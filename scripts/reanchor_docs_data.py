#!/usr/bin/env python3
"""Keep the quoted Lean snippets of the site's data files pointing at the real source.

docs/data/layers.js, docs/data/algorithm.js and docs/data/pp.js quote declarations from the Lean
sources, each with the file, the line and the code. When files move or declarations are
reformatted those quotes go stale; this script finds every declaration again BY NAME and rewrites
file, line and (if the text changed beyond whitespace) the code.

Matching is by the name as written in the declaration, then by namespace-qualified name, restricted
to the same kind (def / theorem / lemma / structure / ...), so `H_reg` is the `def` in
ModularExponentiation/Statement.lean and not the lemma `SFact.H_reg`, and
`lowerSignedPhaseProduct_correct` is not `Policy.lowerSignedPhaseProduct_correct`. A name that still
matches more than one declaration is an error, never a guess.

The inline source links of docs/index.html (`<a href=".../blob/main/<path>#L<n>"><code>name</code></a>`)
are re-anchored the same way, by the declaration name in the link text.

The trimming convention of each existing snippet is kept, detected from its old code:
  * it ends with `:=` or `:= by`           -> the statement only, up to the first top-level `:=`;
  * it carries `-- (field docstrings omitted` -> a structure with its docstrings removed;
  * anything else                          -> the whole declaration.

Usage:
    python3 scripts/reanchor_docs_data.py           # re-anchor (rewrites the three data files)
    python3 scripts/reanchor_docs_data.py --check   # exit 1 if any snippet is stale or unresolved
"""
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "docs", "data")
FILES = ["layers.js", "algorithm.js", "pp.js"]
KINDS = r"(theorem|lemma|def|abbrev|structure|class|inductive|instance)"
DECL = re.compile(
    r"^(?P<ind>[ \t]*)(?:@\[[^\]]*\][ \t]*)?(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+)*"
    + KINDS + r"[ \t]+(?P<name>[^\s(:{\[]+)")
OMITTED = "-- (field docstrings omitted"
TOPLEVEL = re.compile(r"^(?:@\[|/--|/-|--|namespace\b|end\b|open\b|section\b|variable\b|universe\b|set_option\b|"
                      r"private\b|protected\b|noncomputable\b|theorem\b|lemma\b|def\b|abbrev\b|structure\b|"
                      r"class\b|inductive\b|instance\b|deriving\b|attribute\b|local\b|macro\b|notation\b|"
                      r"example\b|mutual\b)")


def load(path):
    s = open(path, encoding="utf-8").read()
    i, j = s.index("{"), s.rindex("}") + 1
    return s, i, j, json.loads(s[i:j])


def entries(d, name):
    if name == "pp.js":
        for k, sn in d["snippets"].items():
            yield f"pp.js:{k}", sn
    else:
        for lid, layer in d["layers"].items():
            for sn in layer["snippets"]:
                yield f"{name}:{lid}", sn


def parse_lean(path):
    """Declarations of one file: (line index, kind, written name, qualified name)."""
    lines = open(path, encoding="utf-8").read().split("\n")
    ns, out = [], []
    for i, ln in enumerate(lines):
        m = re.match(r"^namespace\s+(\S+)", ln)
        if m:
            ns.append(m.group(1)); continue
        m = re.match(r"^end\s+(\S+)\s*$", ln)
        if m and ns and ns[-1] == m.group(1):
            ns.pop(); continue
        d = DECL.match(ln)
        if d:
            out.append((i, d.group(2), d.group("name"), ".".join(ns + [d.group("name")])))
    return lines, out


_cache = {}


def lean_files(root):
    if root not in _cache:
        res = {}
        for dp, dn, fn in os.walk(os.path.join(ROOT, root)):
            for f in fn:
                if f.endswith(".lean"):
                    p = os.path.join(dp, f)
                    res[os.path.relpath(p, os.path.join(ROOT, root))] = parse_lean(p)
        _cache[root] = res
    return _cache[root]


def old_kind(code):
    m = re.match(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*" + KINDS + r"\b", code)
    return m.group(1) if m else None


def is_current(sn, root):
    """The recorded line (give or take two) is a declaration of the recorded name."""
    p = os.path.join(ROOT, root, sn["file"])
    if not os.path.isfile(p):
        return False
    if sn["file"].endswith(".md"):
        lines = open(p, encoding="utf-8").read().split("\n")
        ln = sn.get("line") or 1
        return ln <= len(lines) and sn["code"].strip().split("\n")[0].strip()[:24] in lines[ln - 1]
    short = sn["name"].split(",")[0].strip().split(".")[-1]
    lines, decls = lean_files(root).get(sn["file"], (None, []))
    ln = (sn.get("line") or 1) - 1
    return any(abs(i - ln) <= 2 and (n.split(".")[-1] == short) for i, k, n, q in decls)


def locate(sn, root):
    names = [x.strip() for x in sn["name"].split(",")]
    want = names[0]
    kind = old_kind(sn["code"])
    cands = []
    for f, (lines, decls) in lean_files(root).items():
        for i, k, written, qual in decls:
            if kind and k != kind:
                continue
            if written == want:
                cands.append((0, f, i, lines))
            elif qual == want or qual.endswith("." + want):
                if "." not in written or written.endswith("." + want.split(".")[-1]):
                    cands.append((1, f, i, lines))
    if not cands:
        return None, "no declaration"
    best = min(c[0] for c in cands)
    cands = [c for c in cands if c[0] == best]
    if len(cands) > 1:
        same = [c for c in cands if os.path.dirname(c[1]) == os.path.dirname(sn["file"])]
        if len(same) == 1:
            cands = same
    if len(cands) > 1:
        return None, "ambiguous: " + ", ".join(f"{c[1]}:{c[2]+1}" for c in cands)
    return cands[0], None


def statement(lines, i):
    """From the declaration line to the first `:=` at bracket depth 0 (+ ' by' if it follows)."""
    depth = 0
    out = []
    for k in range(i, min(len(lines), i + 80)):
        ln = lines[k]
        cut = None
        j = 0
        while j < len(ln):
            ch = ln[j]
            if ln.startswith("--", j):
                break
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth -= 1
            elif ln.startswith(":=", j) and depth == 0:
                cut = j
                break
            j += 1
        if cut is not None:
            rest = ln[cut + 2:].strip()
            out.append(ln[:cut + 2] + (" by" if rest.startswith("by") else ""))
            return "\n".join(out)
        out.append(ln)
    return None


def whole(lines, i):
    out = [lines[i]]
    for k in range(i + 1, len(lines)):
        ln = lines[k]
        if ln.strip() == "":
            # a blank line ends the declaration if the next code line starts a new top-level item
            nxt = next((x for x in lines[k + 1:] if x.strip() != ""), "")
            if nxt and not nxt.startswith((" ", "\t", "|")):
                break
            out.append(ln); continue
        if not ln.startswith((" ", "\t", "|")) and TOPLEVEL.match(ln):
            break
        out.append(ln)
    while out and out[-1].strip() == "":
        out.pop()
    return "\n".join(out)


def strip_docstrings(text):
    out, inside = [], False
    for ln in text.split("\n"):
        s = ln.strip()
        if inside:
            if s.endswith("-/"):
                inside = False
            continue
        if s.startswith("/--"):
            if not s.endswith("-/") or s == "/--":
                inside = True
            if out and out[-1] != "":
                out.append("")
            continue
        out.append(ln)
    return "\n".join(out)


def extract(sn, lines, i):
    old = sn["code"]
    if OMITTED in old:
        body = strip_docstrings(whole(lines, i)).split("\n")
        # keep the marker the old snippet had, right after the declaration line
        marker = next(l for l in old.split("\n") if OMITTED in l)
        res = [body[0], marker, ""] + [l for l in body[1:] if True]
        # collapse runs of blank lines
        txt = re.sub(r"\n{3,}", "\n\n", "\n".join(res))
        return txt.rstrip()
    last = old.rstrip().split("\n")[-1].strip()
    if last.endswith(":=") or last.endswith(":= by"):
        return statement(lines, i)
    return whole(lines, i)


def norm(t):
    return [re.sub(r"\s+", " ", x).strip() for x in t.split("\n") if x.strip()]


def locate_many(sn, root):
    """A snippet quoting several adjacent declarations (`name1, name2`): one span, same file."""
    kind = old_kind(sn["code"].lstrip("- ").split("\n", 1)[-1]) if sn["code"].lstrip().startswith("--") else old_kind(sn["code"])
    found = []
    for nm in [x.strip() for x in sn["name"].split(",")]:
        hit = [(f, i, lines) for f, (lines, decls) in lean_files(root).items() for i, k, w, q in decls
               if w == nm and (kind is None or k == kind)]
        if len(hit) != 1:
            return None, f"{nm!r}: {len(hit)} declarations"
        found.append(hit[0])
    if len({f for f, _, _ in found}) != 1:
        return None, "declarations are in different files"
    f, _, lines = found[0]
    first, last = found[0][1], found[-1][1]
    start = first
    if sn["code"].lstrip().startswith("--"):
        while start > 0 and lines[start - 1].lstrip().startswith("--"):
            start -= 1
    end_text = whole(lines, last).split("\n")
    text = "\n".join(lines[start:last] + end_text)
    return (0, f, start, lines, text), None


HTML_FILES = ["docs/index.html"]
LINK = re.compile(r'(<a href=")(https://github\.com/VerifiedQC/ForShor/blob/main/)([^"#]+)(?:#L(\d+))?(")([^>]*>)(.*?)(</a>)', re.S)
LEAN_ROOT = "ForShor/ShorVerification"


def locate_any_kind(name, hint_path, root):
    cands = []
    for f, (lines, decls) in lean_files(root).items():
        for i, k, written, qual in decls:
            if written == name or qual == name:
                cands.append((f, i))
    if len(cands) > 1:
        same = [c for c in cands if os.path.dirname(c[0]) == os.path.dirname(hint_path)]
        if len(same) == 1:
            cands = same
    if len(cands) != 1:
        return None, ("no declaration" if not cands else "ambiguous: " + ", ".join(f"{c[0]}:{c[1]+1}" for c in cands))
    return cands[0], None


def relink_html(check, problems, stale):
    n_links = 0
    for rel in HTML_FILES:
        path = os.path.join(ROOT, rel)
        s = open(path, encoding="utf-8").read()

        def fix(m):
            nonlocal n_links
            full, line = m.group(3), m.group(4)
            if not full.startswith(LEAN_ROOT + "/"):
                return m.group(0)
            n_links += 1
            inner = re.sub(r"<[^>]+>", "", m.group(7)).strip()
            toks = inner.split()
            name = toks[0] if toks else ""
            p = os.path.join(ROOT, full)
            if os.path.exists(p) and not line:
                return m.group(0)
            ok = False
            if os.path.exists(p) and line and full.endswith(".lean") and name:
                L = open(p, encoding="utf-8").read().split("\n")
                k = int(line)
                ok = name.split(".")[-1] in "\n".join(L[max(0, k - 3):k + 2])
            elif os.path.exists(p) and not name:
                ok = True
            if ok:
                return m.group(0)
            stale.append(f"{rel}: {inner[:40]!r} -> {full}#L{line}")
            if not full.endswith(".lean") or not name:
                problems.append(f"{rel}: link {inner[:40]!r} to {full} is gone; edit by hand")
                return m.group(0)
            hit, err = locate_any_kind(name, full[len(LEAN_ROOT) + 1:], LEAN_ROOT)
            if err:
                problems.append(f"{rel}: {name!r}: {err}")
                return m.group(0)
            f, ix = hit
            return (m.group(1) + m.group(2) + LEAN_ROOT + "/" + f + "#L" + str(ix + 1) + m.group(5)
                    + m.group(6) + m.group(7) + m.group(8))
        new = LINK.sub(fix, s)
        if not check and new != s:
            open(path, "w", encoding="utf-8").write(new)
    return n_links


def run(check):
    stale, problems, changed, total = [], [], [], 0
    docs = {}
    for name in FILES:
        path = os.path.join(DATA, name)
        s, i, j, d = load(path)
        docs[name] = (path, s, i, j, d)
        root = d["root"]
        for tag, sn in entries(d, name):
            total += 1
            if is_current(sn, root):
                continue
            stale.append(tag)
            if sn["file"].endswith(".md"):
                problems.append(f"{tag}: {sn['name']!r} quotes {sn['file']}, which is gone; edit by hand")
                continue
            if "," in sn["name"]:
                cand, err = locate_many(sn, root)
            else:
                cand, err = locate(sn, root)
            if err:
                problems.append(f"{tag}: {sn['name']!r}: {err}")
                continue
            if len(cand) == 5:
                _, f, ix, lines, new = cand
            else:
                _, f, ix, lines = cand
                new = extract(sn, lines, ix)
            if new is None:
                problems.append(f"{tag}: {sn['name']!r}: could not extract the statement at {f}:{ix+1}")
                continue
            if not check:
                if norm(new) != norm(sn["code"]):
                    changed.append((tag, sn["name"], sn["code"], new))
                    sn["code"] = new
                sn["file"], sn["line"] = f, ix + 1
    n_links = relink_html(check, problems, stale)
    total += n_links
    if check:
        for t in stale:
            print("STALE", t)
        for p in problems:
            print("PROBLEM", p)
        print(f"{total} snippets and links, {len(stale)} stale, {len(problems)} unresolved")
        return 1 if (stale or problems) else 0
    for name, (path, s, i, j, d) in docs.items():
        open(path, "w", encoding="utf-8").write(s[:i] + json.dumps(d, indent=1, ensure_ascii=False) + s[j:])
    print(f"{total} snippets and links, {len(stale)} re-anchored, {len(changed)} with changed code, {len(problems)} unresolved")
    for t, n, old, new in changed:
        print(f"\n--- CODE CHANGED: {t}  {n}")
        import difflib
        for l in difflib.unified_diff(old.split("\n"), new.split("\n"), "docs (old)", "source (new)", lineterm="", n=1):
            print("   " + l)
    for p in problems:
        print("PROBLEM", p)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(run("--check" in sys.argv[1:]))
