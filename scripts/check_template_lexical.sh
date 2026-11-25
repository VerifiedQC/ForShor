#!/usr/bin/env bash
# The lexical gate from Submission/README.md, step 1 of the submissions-repo CI.
#
# Two tiers read a submitted table and can be made to disagree: the kernel
# reduces C1-C4, while the IR extraction (`Lean.Meta.evalExpr`), the two
# evaluation-tier `example`s and `lake exe forshor_submission` all run compiled
# code. An attribute that changes only the compiled code -- @[implemented_by],
# @[extern], an unsound @[csimp] -- lets a table be kernel-checked as one thing
# and printed into ir.json as another, with no axiom for #assert_axioms to see
# and nothing for lean4checker to replay. This gate is the only cover.
#
# It reads the file as tokens, not as lines. Comments are blanked first (nested
# block comments, doc comments and line comments, with strings respected so that
# `"--"` does not start one), so prose naming the forbidden words, such as the
# paragraph in Template.lean that documents this restriction, does not trip it.
# What is left is searched everywhere, not only at the start of a line: a
# forbidden attribute or command is refused wherever it sits, after another
# attribute, after `open Lean in`, after a doc comment, in a multi-line attribute
# list, or on one line with `namespace`. Strings are scanned as code on purpose:
# an interpolated string holds code, and blanking it would be a hole.
#
# Forbidden: the attributes implemented_by / extern / csimp (and `init`
# attributes), the keywords unsafe, run_cmd, run_meta, run_elab, initialize,
# builtin_initialize, elab, elab_rules, macro, macro_rules, syntax,
# declare_syntax_cat and notation, `import Lean`, and `set_option debug`.
# These are reserved words, so none is a legitimate identifier in a table.
#
# Usage: scripts/check_template_lexical.sh <template.lean>
# Exit: 0 clean, 1 forbidden token found (or unterminated comment/string), 2 usage.
set -euo pipefail

target=${1:-ForShor/ShorVerification/Submission/Template.lean}

if [ ! -f "$target" ]; then
  echo "check_template_lexical: no such file: $target" >&2
  exit 2
fi

python3 - "$target" <<'PY'
import re, sys

path = sys.argv[1]
src = open(path, encoding="utf-8").read()

def blank_comments(s):
    """Replace comments by spaces (newlines kept so line numbers stay right).
    Strings are copied through untouched: they are scanned as code."""
    out, i, n = [], 0, len(s)
    while i < n:
        c = s[i]
        if s.startswith("--", i):
            j = s.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif s.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if s.startswith("/-", j): depth += 1; j += 2
                elif s.startswith("-/", j): depth -= 1; j += 2
                else: j += 1
            if depth:
                return None, "unterminated block comment"
            out.append("".join(ch if ch == "\n" else " " for ch in s[i:j])); i = j
        elif s.startswith('r#', i) or s.startswith('r"', i):
            m = re.match(r'r(#*)"', s[i:])
            if m:
                close = '"' + m.group(1)
                j = s.find(close, i + len(m.group(0)))
                if j < 0: return None, "unterminated raw string"
                j += len(close); out.append(s[i:j]); i = j
            else:
                out.append(c); i += 1
        elif c == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            if j >= n: return None, "unterminated string"
            out.append(s[i:j + 1]); i = j + 1
        elif c == "'" and (i == 0 or not (s[i - 1].isalnum() or s[i - 1] in "_'")):
            m = re.match(r"'(\\.|[^\\'])'", s[i:])   # char literal such as '"'
            if m: out.append(m.group(0)); i += len(m.group(0))
            else: out.append(c); i += 1
        else:
            out.append(c); i += 1
    return "".join(out), None

code, err = blank_comments(src)
if err:
    print(f"check_template_lexical: {path}: {err}", file=sys.stderr)
    sys.exit(1)

W = lambda words: r"(?<![\w'])(?:" + "|".join(words) + r")(?![\w'])"
attrs = r"(?<![\w'])(?:implemented_by|extern|csimp)(?![\w'])"
keywords = W(["unsafe", "run_cmd", "run_meta", "run_elab", "initialize", "builtin_initialize",
              "elab", "elab_rules", "macro", "macro_rules", "syntax", "declare_syntax_cat", "notation"])
others = [r"\bimport\s+Lean\b", r"\bset_option\s+debug\b"]
patterns = [attrs, keywords] + others
# `init` / `builtin_init` run code when the module loads; they are attributes, so look inside [...] groups.
init_attr = re.compile(r"(?<![\w'])(?:builtin_)?init(?![\w'])")

lines = code.split("\n")
orig = src.split("\n")
bad = []
for k, line in enumerate(lines):
    if any(re.search(p, line) for p in patterns):
        bad.append((k + 1, orig[k]))
# multi-line attribute lists: search the joined text for the whole [...] group
for m in re.finditer(r"(?:@|attribute\s*)\[", code):
    j, depth = m.end(), 1
    while j < len(code) and depth:
        depth += {"[": 1, "]": -1}.get(code[j], 0); j += 1
    group = code[m.start():j]
    if re.search(attrs, group) or init_attr.search(group):
        ln = code.count("\n", 0, m.start()) + 1
        if (ln, orig[ln - 1]) not in bad: bad.append((ln, orig[ln - 1]))
if bad:
    for ln, text in sorted(bad):
        print(f"{ln}:{text}")
    print("", file=sys.stderr)
    print(f"check_template_lexical: {path} reaches compiled code or the metaprogramming surface.", file=sys.stderr)
    print("A submitted table needs none of this; see Submission/README.md, 'CI for a submissions repo'.", file=sys.stderr)
    sys.exit(1)
print(f"check_template_lexical: {path} is clean")
PY
