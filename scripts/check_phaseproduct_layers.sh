#!/usr/bin/env bash
# Asserts that every file under Implementation/PhaseProduct imports only from folders at or
# below its own layer. Pure moves must keep this green from the last step on.
set -euo pipefail
root=FastMultiplication/ShorVerification/Implementation/PhaseProduct
prefix=FastMultiplication.ShorVerification.Implementation.PhaseProduct.
layer() { case "$1" in
  Math*) echo 1;; Compiler*) echo 2;; Gates*) echo 3;;
  Lowering*) echo 4;; Spec*) echo 5;; Proofs*) echo 6;; Main) echo 7;; *) echo 9;; esac; }
status=0
while IFS= read -r f; do
  mod=${f#$root/}; mod=${mod%.lean}; mod=${mod//\//.}
  case "$mod" in Math.Table_Generation*) continue;; esac   # frozen subtree, not inspected
  # umbrella detector: a file with imports but no declarations of its own
  if grep -qE '^import ' "$f" && ! grep -qE '^(noncomputable def|def|abbrev|structure|inductive|class|instance|theorem|lemma|@\[|macro|elab|syntax)' "$f"; then
    echo "UMBRELLA FILE: $mod"; status=1
  fi
  me=$(layer "$mod")
  while IFS= read -r imp; do
    dep=${imp#$prefix}; dl=$(layer "$dep")
    if [ "$dl" -gt "$me" ]; then echo "LAYER VIOLATION: $mod imports $dep"; status=1; fi
  done < <(grep -oE "^import ${prefix}[A-Za-z0-9_.]+" "$f" | sed 's/^import //')
done < <(find "$root" -name '*.lean')
exit $status
