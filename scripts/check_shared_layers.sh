#!/usr/bin/env bash
# Asserts layer discipline for Implementation/Shared: every file imports only
# from Framework/, Mathlib, and Shared/ files at or below its own layer (rule
# (a) of the admission rule in Shared/README.md); reports, as a non-failing
# warning, how many distinct top-level Implementation/ folders import each
# Shared/ file (rule (b) — a file imported from fewer than two is
# shared-in-waiting, not a violation).
#
# Internal layer order: QftPhase, Registers, Measurement < States < Hadamard,
# GateLaws < LowGateEval.
set -euo pipefail
root=FastMultiplication/ShorVerification/Implementation/Shared
prefix=FastMultiplication.ShorVerification.Implementation.Shared.
layer() { case "$1" in
  QftPhase|Registers|Measurement) echo 1;;
  States) echo 2;;
  Hadamard|GateLaws) echo 3;;
  LowGateEval) echo 4;;
  *) echo 99;; esac; }
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
    if [ "$dl" -gt "$me" ]; then
      echo "LAYER VIOLATION: $mod imports $dep"; status=1
    fi
  done < <(grep -oE "^import ${prefix}[A-Za-z0-9_.]+" "$f" | sed 's/^import //')
  if grep -oE '^import FastMultiplication\.ShorVerification\.Implementation\.(PhaseProduct|QFT|ModularExponentiation|Shor|GateCount|Reference)\.[A-Za-z0-9_.]+' "$f" >/dev/null; then
    echo "FORBIDDEN SIDEWAYS IMPORT: $mod imports a subroutine/assembly module"; status=1
  fi
done < <(find "$root" -name '*.lean')

# Rule (b), informational only: count distinct top-level Implementation/
# folders (excluding Shared itself) that import each Shared/ file.
impl_root=FastMultiplication/ShorVerification/Implementation
while IFS= read -r f; do
  mod=${f#$root/}; mod=${mod%.lean}
  n=$(grep -rlE "^import ${prefix}${mod}\$" "$impl_root" --include='*.lean' \
        | sed "s#$impl_root/##" | cut -d/ -f1 | grep -v '^Shared$' | sort -u | wc -l | tr -d ' ')
  if [ "$n" -lt 2 ]; then
    echo "WARNING: Shared.$mod is imported from only $n top-level folder(s) (shared-in-waiting)"
  fi
done < <(find "$root" -name '*.lean')

exit $status
