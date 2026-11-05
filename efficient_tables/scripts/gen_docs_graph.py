#!/usr/bin/env python3
"""Generate docs/efficient-tables/data/graph.js from the efficient_tables/ package.

Walks both Lake projects of the package -- the layered proof library lean/
(shown as "Library") and the separate hardness project lean_hardness/ (shown as
"Hardness", including its vendored TableGeneration contract) -- parses `import` lines,
module docstrings, and top-level declarations out of every .lean file, converts
every README.md to HTML, and aggregates in-repo import edges (and cross-view
"ghost" edges) for every folder in the tree. Same graph.js schema as ForShor's
scripts/gen_docs_graph.py, which this is ported from; it writes only under
docs/efficient-tables/ and never touches ForShor's own docs/data/graph.js. The
result is a plain `window.GRAPH = {...}` assignment so the viewer keeps working
from `file://`.

Run with --check to additionally validate docs/efficient-tables/data/annotations.js against
the generated graph: every curated bridge must name a real edge and a real
declaration, so a rename or move that forgets to update the annotations
fails loudly instead of leaving a stale arrow on the site.

Usage:
    python3 scripts/gen_docs_graph.py            # write the site's graph.js
    python3 scripts/gen_docs_graph.py --check    # also validate annotations.js
"""
import json
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # .../efficient_tables
FORSHOR_ROOT = os.path.dirname(REPO_ROOT)
SITE_DIR = os.path.join(FORSHOR_ROOT, "docs", "efficient-tables")
GRAPH_JS_PATH = os.path.join(SITE_DIR, "data", "graph.js")
ANNOTATIONS_JS_PATH = os.path.join(SITE_DIR, "data", "annotations.js")
# GitHub links are built as <repo>/blob/<branch>/<META_ROOT>/<fsPath>.
META_ROOT = "efficient_tables"

# The two Lake projects. `top` is the logical name of the project's node,
# `fs` its directory under REPO_ROOT, `order` its immediate sub-folders (each
# paired with the file-system directory it is read from). Module names are
# resolved per project: `Source.Model` is Library/Source/Model.lean, and
# `Mahaney.Core` is Hardness/Mahaney/Core.lean.
PROJECTS = [
    {
        "top": "Library",
        "fs": "lean",
        # Layers in dependency order: a file may only import from its own layer
        # or an earlier one (asserted on every run). Helpers is a standalone library.
        "order": [
            ("Foundations", "lean/Foundations"), ("Source", "lean/Source"),
            ("Model", "lean/Model"), ("Planner", "lean/Planner"),
            ("PhaseProduct", "lean/PhaseProduct"), ("Provider", "lean/Provider"),
            ("ILPEncoding", "lean/ILPEncoding"), ("Alignment", "lean/Alignment"),
            ("Helpers", "lean/Helpers"),
        ],
        # Helpers is built as its own Lake library; it may be imported by anything.
        "readme": "lean/README.md",
    },
    {
        "top": "Hardness",
        "fs": "lean_hardness",
        # TableGeneration is the vendored benchmark contract (byte-identical copies);
        # Mahaney and Points are two developments that sit on top of it
        # (Mahaney builds on TableGeneration; Points imports both).
        "order": [
            ("TableGeneration", "lean_hardness/vendor/ShorTableOptimization/TableGeneration"),
            ("Mahaney", "lean_hardness/Mahaney"), ("Points", "lean_hardness/Points"),
        ],
        "readme": "lean_hardness/README.md",
    },
]
TOPS = [p["top"] for p in PROJECTS]
MODULE_ROOTS = {}  # first segment of a Lean module name -> logical top-level path
for _p in PROJECTS:
    for _d, _ in _p["order"]:
        MODULE_ROOTS[_d] = f"{_p['top']}/{_d}"
RANK = {}  # logical depth-1 folder ("Library/Source") -> (project, rank)
for _p in PROJECTS:
    for _i, (_d, _) in enumerate(_p["order"]):
        RANK[f"{_p['top']}/{_d}"] = (_p["top"], _i)
EXTERNAL_ROOTS = ("Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq", "Complexitylib", "ImportGraph", "Plausible", "LeanSearchClient", "Cli")

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+"
    r"([^\s(:{\[]+)"
)
IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)")
NAMESPACE_OPEN_RE = re.compile(r"^namespace\s+(\S+)")
NAMESPACE_CLOSE_RE = re.compile(r"^end\s+(\S+)\s*$")
DOCSTRING_RE = re.compile(r"/-!(.*?)-/", re.DOTALL)


def depth1_of(logical_path):
    """'Library/Source/Model.lean' -> 'Library/Source'."""
    return "/".join(logical_path.split("/")[:2])


# ---------------------------------------------------------------------------
# Tree walk
# ---------------------------------------------------------------------------

class Node:
    __slots__ = (
        "kind", "path", "fs_path", "name", "children",
        "docstring", "declarations", "imports", "imported_by",
        "lines", "readme_html", "file_count", "decl_count", "_raw_imports",
    )

    def __init__(self, kind, path, fs_path, name):
        self.kind = kind
        self.path = path
        self.fs_path = fs_path
        self.name = name
        self.children = []
        self.docstring = None
        self.declarations = []
        self.imports = []
        self.imported_by = []
        self.lines = None
        self.readme_html = None
        self.file_count = None
        self.decl_count = None


def parse_lean_file(abs_path):
    with open(abs_path, "r", encoding="utf-8") as f:
        text = f.read()
    lines = text.splitlines()

    m = DOCSTRING_RE.search(text)
    docstring = m.group(1).strip() if m else None

    declarations = []
    ns_stack = []
    for i, line in enumerate(lines, start=1):
        nm = NAMESPACE_OPEN_RE.match(line)
        if nm:
            ns_stack.append(nm.group(1))
            continue
        em = NAMESPACE_CLOSE_RE.match(line)
        if em and ns_stack and ns_stack[-1] == em.group(1):
            ns_stack.pop()
            continue
        dm = DECL_RE.match(line)
        if dm:
            kind, name = dm.group(1), dm.group(2)
            qualified = ".".join(ns_stack + [name]) if ns_stack else name
            declarations.append({"kind": kind, "name": qualified, "line": i})

    raw_imports = []
    for line in lines:
        imp = IMPORT_RE.match(line)
        if imp:
            raw_imports.append(imp.group(1))

    return docstring, declarations, raw_imports, len(lines)


def walk():
    """Returns (nodes: dict[path]->Node)."""
    nodes = {}

    for proj in PROJECTS:
        top = proj["top"]
        top_node = Node("folder", top, proj["fs"], top)
        readme_path = os.path.join(REPO_ROOT, proj["readme"])
        if os.path.isfile(readme_path):
            top_node.readme_html = markdown_to_html(read_text(readme_path))
        nodes[top] = top_node

        for d0, fs_dir in proj["order"]:
            base = os.path.join(REPO_ROOT, fs_dir)
            for dirpath, dirnames, filenames in os.walk(base):
                rel = os.path.relpath(dirpath, base).replace(os.sep, "/")
                rel = "" if rel == "." else rel
                dirnames[:] = sorted(d for d in dirnames if d not in (".lake", "design", "build"))
                logical = f"{top}/{d0}" + (f"/{rel}" if rel else "")
                fs_rel = fs_dir + (f"/{rel}" if rel else "")

                node = Node("folder", logical, fs_rel, logical.split("/")[-1])
                readme_path = os.path.join(dirpath, "README.md")
                if os.path.isfile(readme_path):
                    node.readme_html = markdown_to_html(read_text(readme_path))
                nodes[logical] = node
                # os.walk (topdown) visits a directory before its subdirectories,
                # so the parent folder node already exists in `nodes` here.
                nodes[logical.rsplit("/", 1)[0]].children.append(logical)

                for fname in sorted(filenames):
                    if not fname.endswith(".lean"):
                        continue
                    file_logical = f"{logical}/{fname}"
                    fnode = Node("file", file_logical, f"{fs_rel}/{fname}", fname)
                    docstring, declarations, raw_imports, nlines = parse_lean_file(os.path.join(dirpath, fname))
                    fnode.docstring = docstring
                    fnode.declarations = declarations
                    fnode.lines = nlines
                    fnode._raw_imports = raw_imports
                    nodes[file_logical] = fnode
                    node.children.append(file_logical)

    for node in nodes.values():
        node.children.sort()
    for proj in PROJECTS:  # the project's depth-1 folders keep their dependency order
        nodes[proj["top"]].children = [f"{proj['top']}/{d}" for d, _ in proj["order"]]

    return nodes


def read_text(path):
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


# ---------------------------------------------------------------------------
# Resolve imports, compute recursive counts
# ---------------------------------------------------------------------------

def resolve_imports(nodes):
    for node in nodes.values():
        if node.kind != "file":
            continue
        for raw in getattr(node, "_raw_imports", []):
            seg = raw.split(".", 1)
            logical = (MODULE_ROOTS[seg[0]] + "/" + seg[1].replace(".", "/") + ".lean") if seg[0] in MODULE_ROOTS and len(seg) > 1 else None
            if logical in nodes and nodes[logical].kind == "file":
                node.imports.append(logical)
            elif seg[0] not in EXTERNAL_ROOTS:
                print(f"warning: unresolved import {raw!r} in {node.fs_path}", file=sys.stderr)
        del node._raw_imports

    for node in nodes.values():
        if node.kind == "file":
            for dep in node.imports:
                nodes[dep].imported_by.append(node.path)

    for node in nodes.values():
        node.imports.sort()
        node.imported_by.sort()


def subtree_files(nodes, path):
    node = nodes[path]
    if node.kind == "file":
        return {path}
    out = set()
    for c in node.children:
        out |= subtree_files(nodes, c)
    return out


def compute_recursive_counts(nodes):
    memo_files = {}
    memo_decls = {}

    def files_of(path):
        if path in memo_files:
            return memo_files[path]
        node = nodes[path]
        if node.kind == "file":
            memo_files[path] = 1
            return 1
        total = sum(files_of(c) for c in node.children)
        memo_files[path] = total
        return total

    def decls_of(path):
        if path in memo_decls:
            return memo_decls[path]
        node = nodes[path]
        if node.kind == "file":
            memo_decls[path] = len(node.declarations)
            return memo_decls[path]
        total = sum(decls_of(c) for c in node.children)
        memo_decls[path] = total
        return total

    for path, node in nodes.items():
        if node.kind == "folder":
            node.file_count = files_of(path)
            node.decl_count = decls_of(path)


# ---------------------------------------------------------------------------
# View / edge / ghost aggregation
# ---------------------------------------------------------------------------

def edges_for_children(nodes, child_ids):
    subtrees = {c: subtree_files(nodes, c) for c in child_ids}
    edges = []
    for ci in child_ids:
        for cj in child_ids:
            if ci == cj:
                continue
            pairs = []
            for g in subtrees[cj]:  # g imports f -> f provides to g
                for f in nodes[g].imports:
                    if f in subtrees[ci]:
                        pairs.append([f, g])
            if pairs:
                pairs.sort()
                edges.append({"from": ci, "to": cj, "weight": len(pairs), "pairs": pairs})
    return edges


def ghost_target(nodes, view_path, external_path):
    """LCA-based ghost target: the ancestor of external_path one level below
    the longest common path prefix it shares with view_path."""
    view_parts = view_path.split("/") if view_path else []
    ext_parts = external_path.split("/")
    common = 0
    while common < len(view_parts) and common < len(ext_parts) - 1 and view_parts[common] == ext_parts[common]:
        common += 1
    return "/".join(ext_parts[: common + 1])


def ghosts_for_view(nodes, view_path, child_ids):
    if view_path == "":
        return {"providers": [], "consumers": []}
    scope = set()
    for c in child_ids:
        scope |= subtree_files(nodes, c)

    providers = {}
    consumers = {}
    # sorted(), not the set's own order: the dicts below are built in iteration
    # order and ties in the sort key keep it, so an unsorted walk makes the
    # output depend on PYTHONHASHSEED.
    for f in sorted(scope):
        fnode = nodes[f]
        for g in fnode.imports:
            if g not in scope:
                target = ghost_target(nodes, view_path, g)
                providers[target] = providers.get(target, 0) + 1
        for h in fnode.imported_by:
            if h not in scope:
                target = ghost_target(nodes, view_path, h)
                consumers[target] = consumers.get(target, 0) + 1

    return {
        "providers": sorted(({"target": t, "weight": w} for t, w in providers.items()),
                            key=lambda x: (-x["weight"], x["target"])),
        "consumers": sorted(({"target": t, "weight": w} for t, w in consumers.items()),
                            key=lambda x: (-x["weight"], x["target"])),
    }


def build_views(nodes):
    views = {}
    views[""] = {
        "path": "",
        "children": list(TOPS),
        "edges": edges_for_children(nodes, TOPS),
        "ghosts": {"providers": [], "consumers": []},
    }
    for path, node in nodes.items():
        if node.kind != "folder":
            continue
        views[path] = {
            "path": path,
            "children": list(node.children),
            "edges": edges_for_children(nodes, node.children),
            "ghosts": ghosts_for_view(nodes, path, node.children),
        }
    return views


# ---------------------------------------------------------------------------
# Sanity assertions (run every time, not just --check)
# ---------------------------------------------------------------------------

def assert_layer_order(nodes):
    """A file may import only from its own layer or an earlier one of the same
    Lake project; the two projects must not import each other."""
    bad = []
    for path, node in nodes.items():
        if node.kind != "file":
            continue
        proj, rank = RANK[depth1_of(path)]
        for dep in node.imports:
            dproj, drank = RANK[depth1_of(dep)]
            same_layer = depth1_of(dep) == depth1_of(path)
            if dproj != proj or drank > rank or (drank == rank and not same_layer):
                bad.append((path, dep))
    if bad:
        for path, dep in bad:
            print(f"ASSERTION FAILED: {path} imports {dep} across a forbidden layer/project boundary", file=sys.stderr)
        sys.exit(1)


def warn_on_aggregate_cycles(views):
    """The file-level import graph is a DAG (Lean would refuse to build
    otherwise), but aggregating files into folders can create an apparent
    cycle when a folder's own children don't line up with the true
    dependency layering (e.g. an explicitly frozen/unlayered subtree such as
    Math/Table_Generation). That's a real property of the tree, not a bug in
    this script, so it is reported rather than treated as fatal; layout.js's
    rank assignment is written to tolerate it."""
    for view_path, view in views.items():
        adj = {}
        for e in view["edges"]:
            adj.setdefault(e["from"], []).append(e["to"])
        color = {}

        def dfs(u, stack):
            color[u] = 1
            stack.append(u)
            for v in adj.get(u, []):
                if color.get(v) == 1:
                    cyc = stack[stack.index(v):] + [v]
                    print(f"note: view {view_path!r} has an aggregate cycle: {' -> '.join(cyc)}", file=sys.stderr)
                    continue
                if color.get(v) != 2:
                    dfs(v, stack)
            stack.pop()
            color[u] = 2

        for c in view["children"]:
            if color.get(c) is None:
                dfs(c, [])


# ---------------------------------------------------------------------------
# Markdown subset -> HTML
# ---------------------------------------------------------------------------

def esc(s):
    return (s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


def inline_md(s):
    s = esc(s)
    s = re.sub(r"`([^`]+)`", r"<code>\1</code>", s)
    s = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", s)
    s = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"<em>\1</em>", s)
    return s


def markdown_to_html(text):
    lines = text.splitlines()
    out = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]

        if line.strip() == "":
            i += 1
            continue

        if line.startswith("```"):
            i += 1
            code = []
            while i < n and not lines[i].startswith("```"):
                code.append(lines[i])
                i += 1
            i += 1  # skip closing fence
            out.append(f"<pre><code>{esc(chr(10).join(code))}</code></pre>")
            continue

        m = re.match(r"^(#{1,3})\s+(.*)$", line)
        if m:
            level = len(m.group(1))
            out.append(f"<h{level}>{inline_md(m.group(2))}</h{level}>")
            i += 1
            continue

        if line.lstrip().startswith("|") and i + 1 < n and re.match(r"^\s*\|?[\s:|-]+\|?\s*$", lines[i + 1]):
            header = [c.strip() for c in line.strip().strip("|").split("|")]
            i += 2
            rows = []
            while i < n and lines[i].lstrip().startswith("|"):
                rows.append([c.strip() for c in lines[i].strip().strip("|").split("|")])
                i += 1
            thead = "".join(f"<th>{inline_md(c)}</th>" for c in header)
            tbody = "".join(
                "<tr>" + "".join(f"<td>{inline_md(c)}</td>" for c in row) + "</tr>" for row in rows
            )
            out.append(f"<table><thead><tr>{thead}</tr></thead><tbody>{tbody}</tbody></table>")
            continue

        m = re.match(r"^\s*[*-]\s+(.*)$", line)
        if m:
            items = []
            while i < n and re.match(r"^\s*[*-]\s+(.*)$", lines[i]):
                items.append(re.match(r"^\s*[*-]\s+(.*)$", lines[i]).group(1))
                i += 1
            out.append("<ul>" + "".join(f"<li>{inline_md(it)}</li>" for it in items) + "</ul>")
            continue

        m = re.match(r"^\s*\d+\.\s+(.*)$", line)
        if m:
            items = []
            while i < n and re.match(r"^\s*\d+\.\s+(.*)$", lines[i]):
                items.append(re.match(r"^\s*\d+\.\s+(.*)$", lines[i]).group(1))
                i += 1
            out.append("<ol>" + "".join(f"<li>{inline_md(it)}</li>" for it in items) + "</ol>")
            continue

        para = [line]
        i += 1
        while i < n and lines[i].strip() != "" and not lines[i].startswith(("#", "```", "|")) and not re.match(r"^\s*[*-]\s+", lines[i]) and not re.match(r"^\s*\d+\.\s+", lines[i]):
            para.append(lines[i])
            i += 1
        out.append(f"<p>{inline_md(' '.join(p.strip() for p in para))}</p>")

    return "\n".join(out)


# ---------------------------------------------------------------------------
# Emit graph.js
# ---------------------------------------------------------------------------

def node_to_dict(node):
    d = {"kind": node.kind, "path": node.path, "fsPath": node.fs_path, "name": node.name}
    if node.kind == "folder":
        d["children"] = node.children
        d["readmeHtml"] = node.readme_html
        d["fileCount"] = node.file_count
        d["declCount"] = node.decl_count
    else:
        d["docstring"] = node.docstring
        d["declarations"] = node.declarations
        d["imports"] = node.imports
        d["importedBy"] = node.imported_by
        d["lines"] = node.lines
    return d


def build_graph():
    nodes = walk()
    resolve_imports(nodes)
    compute_recursive_counts(nodes)
    assert_layer_order(nodes)
    views = build_views(nodes)
    warn_on_aggregate_cycles(views)

    graph = {
        "meta": {"root": META_ROOT, "order0": list(TOPS), "implementationReadmeHtml": None},
        "nodes": {path: node_to_dict(node) for path, node in nodes.items()},
        "views": views,
    }
    return graph


def write_graph_js(graph):
    os.makedirs(os.path.dirname(GRAPH_JS_PATH), exist_ok=True)
    with open(GRAPH_JS_PATH, "w", encoding="utf-8") as f:
        f.write("// Generated by efficient_tables/scripts/gen_docs_graph.py. Do not edit by hand.\n")
        f.write("window.GRAPH = ")
        json.dump(graph, f, indent=1, sort_keys=True)
        f.write(";\n")


# ---------------------------------------------------------------------------
# --check: validate annotations.js against the generated graph
# ---------------------------------------------------------------------------

def extract_json_object(text, marker):
    idx = text.index(marker)
    start = text.index("{", idx)
    depth = 0
    in_str = False
    esc_next = False
    for i in range(start, len(text)):
        c = text[i]
        if esc_next:
            esc_next = False
            continue
        if c == "\\":
            esc_next = True
            continue
        if c == '"':
            in_str = not in_str
            continue
        if in_str:
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return text[start : i + 1]
    raise ValueError(f"unbalanced braces after {marker!r}")


def load_annotations():
    if not os.path.isfile(ANNOTATIONS_JS_PATH):
        return {"nodes": {}, "views": {}, "roles": {}, "layers": {}}
    text = read_text(ANNOTATIONS_JS_PATH)
    blob = extract_json_object(text, "window.ANNOTATIONS = ")
    return json.loads(blob)


def all_declaration_names(graph):
    """Both fully-qualified and bare (last-segment) declaration names, since
    curated bridges name theorems the way the READMEs do (usually bare)."""
    names = set()
    for node in graph["nodes"].values():
        if node["kind"] == "file":
            for d in node["declarations"]:
                names.add(d["name"])
                names.add(d["name"].rsplit(".", 1)[-1])
    return names


def check_annotations(graph, annotations):
    errors = []
    decl_names = all_declaration_names(graph)

    for path in annotations.get("nodes", {}):
        if path not in graph["nodes"] and path != "":
            errors.append(f"annotations.nodes references unknown path {path!r}")

    for view_path, vdata in annotations.get("views", {}).items():
        view = graph["views"].get(view_path)
        if not view:
            errors.append(f"views entry references unknown view {view_path!r}")
            continue
        children_set = set(view["children"])
        edge_set = {(e["from"], e["to"]) for e in view["edges"]}

        columns = vdata.get("columns")
        if columns is not None:
            seen = []
            for col in columns:
                seen.extend(col)
            if set(seen) != children_set or len(seen) != len(children_set):
                missing = sorted(children_set - set(seen))
                extra = sorted(set(seen) - children_set)
                dup = sorted({x for x in seen if seen.count(x) > 1})
                errors.append(
                    f"view {view_path!r} columns must cover each child exactly once "
                    f"(missing={missing}, extra={extra}, duplicated={dup})"
                )

        for edge in vdata.get("edges", []):
            frm, to = edge.get("from"), edge.get("to")
            if (frm, to) not in edge_set:
                errors.append(f"view {view_path!r} curated edge {frm!r} -> {to!r} is not a real import edge in that view")

            theorem = edge.get("theorem")
            if theorem:
                names = re.split(r"\s*/\s*|\s+and\s+", theorem)
                if not any(n.strip("` ") in decl_names for n in names):
                    errors.append(f"view {view_path!r} edge theorem {theorem!r} (from {frm!r} -> {to!r}) not found among declarations")

            emphasis = edge.get("emphasis")
            if emphasis not in (None, "primary", "secondary", "dim"):
                errors.append(f"view {view_path!r} edge {frm!r} -> {to!r} has invalid emphasis {emphasis!r}")

        drawn = {(e["from"], e["to"]) for e in vdata.get("edges", [])}
        for e in view["edges"]:
            if (e["from"], e["to"]) not in drawn and e["weight"] >= 10:
                print(
                    f"info: view {view_path!r} leaves a weight-{e['weight']} import undrawn: "
                    f"{e['from']} -> {e['to']}",
                    file=sys.stderr,
                )

    return errors


def main():
    check = "--check" in sys.argv
    graph = build_graph()
    write_graph_js(graph)
    print(f"wrote {os.path.relpath(GRAPH_JS_PATH, FORSHOR_ROOT)}: "
          f"{len(graph['nodes'])} nodes, {len(graph['views'])} views")

    if check:
        annotations = load_annotations()
        errors = check_annotations(graph, annotations)
        if errors:
            for e in errors:
                print(f"CHECK FAILED: {e}", file=sys.stderr)
            sys.exit(1)
        edge_count = sum(len(v.get("edges", [])) for v in annotations.get("views", {}).values())
        print(f"--check passed: {edge_count} curated edges validated across {len(annotations.get('views', {}))} views")


if __name__ == "__main__":
    main()
