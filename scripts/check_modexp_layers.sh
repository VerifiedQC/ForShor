#!/usr/bin/env bash
# Asserts that every file under Implementation/ModularExponentiation imports only from folders at
# or below its own layer. Pure moves must keep this green from the last step on.
set -euo pipefail
root=FastMultiplication/ShorVerification/Implementation/ModularExponentiation
prefix=FastMultiplication.ShorVerification.Implementation.ModularExponentiation.
layer() { case "$1" in
  Math*) echo 1;; Circuit*) echo 2;; Lowering*) echo 3;;
  Spec*) echo 4;; Proofs*) echo 5;; Main) echo 6;; *) echo 9;; esac; }
status=0
while IFS= read -r f; do
  mod=${f#$root/}; mod=${mod%.lean}; mod=${mod//\//.}
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
