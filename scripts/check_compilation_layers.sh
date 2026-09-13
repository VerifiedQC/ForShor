#!/usr/bin/env bash
# Asserts layer discipline for Implementation/Compilation, the generic whole-gate
# Gate -> LowGate compiler: LowerGate < Correctness, and Compilation sits above
# PhaseProduct/QFT/ModularExponentiation but below Shor/GateCount/Reference, so no
# file under Compilation/ may import Shor.*, GateCount.*, or Reference.*.
set -euo pipefail
root=FastMultiplication/ShorVerification/Implementation/Compilation
prefix=FastMultiplication.ShorVerification.Implementation.Compilation.
layer() { case "$1" in
  LowerGate) echo 1;; Correctness) echo 2;; *) echo 9;; esac; }
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
  if grep -oE '^import FastMultiplication\.ShorVerification\.Implementation\.(Shor|GateCount|Reference)\.[A-Za-z0-9_.]+' "$f" >/dev/null; then
    echo "FORBIDDEN UPWARD IMPORT: $mod imports a Shor/GateCount/Reference module"; status=1
  fi
done < <(find "$root" -name '*.lean')
exit $status
