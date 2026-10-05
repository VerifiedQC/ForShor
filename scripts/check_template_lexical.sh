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
# Patterns are anchored at code positions, so prose naming the tokens (such as
# the paragraph in Template.lean that documents this restriction) does not trip
# it.
#
# Usage: scripts/check_template_lexical.sh <template.lean>
set -euo pipefail

target=${1:-FastMultiplication/ShorVerification/Submission/Template.lean}

if [ ! -f "$target" ]; then
  echo "check_template_lexical: no such file: $target" >&2
  exit 2
fi

pattern='^[[:space:]]*(@\[|attribute[[:space:]]*\[)[^]]*(implemented_by|extern|csimp)|^[[:space:]]*((private|protected|noncomputable|scoped|local)[[:space:]]+)*(unsafe|run_cmd|run_meta|initialize|elab|macro|syntax|notation)\b|^import[[:space:]]+Lean\b|^[[:space:]]*set_option[[:space:]]+debug'

if grep -nE "$pattern" "$target"; then
  echo "" >&2
  echo "check_template_lexical: $target reaches compiled code or the metaprogramming surface." >&2
  echo "A submitted table needs none of this; see Submission/README.md, 'CI for a submissions repo'." >&2
  exit 1
fi

echo "check_template_lexical: $target is clean"
