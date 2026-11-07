#!/usr/bin/env python3
"""Check the layer order of the efficient_tables/ Lean projects.

Walks both Lake projects of the package -- the layered proof library `lean/` ("Library") and the
hardness project `lean_hardness/` ("Hardness", with its vendored TableGeneration contract) --
parses the `import` lines of every .lean file, and fails if a file imports from a later layer of
its own project or from the other project: a file may import only from its own layer or an
earlier one, and the two projects must not import each other. The layers are the `order` lists
in PROJECTS below. Nothing is written.

(This was part of the generator of the package's web page, `gen_docs_graph.py`, which was
removed with the page. The check is kept because it guards the package's structure.)

Usage:
    python3 efficient_tables/scripts/check_layers.py
"""
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # .../efficient_tables

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



def main():
    nodes = walk()
    resolve_imports(nodes)
    assert_layer_order(nodes)
    files = [n for n in nodes.values() if n.kind == "file"]
    edges = sum(len(n.imports) for n in files)
    print(f"layer order ok: {len(files)} Lean files in {len(PROJECTS)} Lake projects, "
          f"{edges} in-package import edges, none crossing a layer or project boundary")


if __name__ == "__main__":
    main()
