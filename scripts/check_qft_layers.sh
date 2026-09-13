#!/usr/bin/env bash
# Asserts that every file under Implementation/QFT imports only from folders at or
# below its own layer. Pure moves must keep this green from the last step on.
set -euo pipefail
root=FastMultiplication/ShorVerification/Implementation/QFT
prefix=FastMultiplication.ShorVerification.Implementation.QFT.
layer() { case "$1" in
  Split) echo 1;; Lowering*) echo 2;;
  Spec*) echo 3;; Proofs*) echo 4;; Main) echo 5;; *) echo 9;; esac; }
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
