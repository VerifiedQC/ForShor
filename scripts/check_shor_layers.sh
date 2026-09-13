#!/usr/bin/env bash
# Asserts that every file under Implementation/Shor imports only from folders at or
# below its own layer. Pure moves must keep this green from the last step on.
#
# Layer order: Math < Circuit < Spec < Proofs < Main; inside Proofs, the Readiness/
# chain is Static < Sequencing < Primitives < Init < Step1 < Step2 < Step5 < IQFT <
# ModMul < ModExp < Dynamic, and Budgets, Setup < Readiness/* < NaiveShor/* < Correctness.
set -euo pipefail
root=FastMultiplication/ShorVerification/Implementation/Shor
prefix=FastMultiplication.ShorVerification.Implementation.Shor.
layer() { case "$1" in
  Math*) echo 10;;
  Circuit*) echo 20;;
  Spec.Assertions) echo 31;;
  Spec*) echo 30;;
  Proofs.Budgets|Proofs.Setup) echo 40;;
  Proofs.Readiness.Static) echo 41;;
  Proofs.Readiness.Sequencing) echo 42;;
  Proofs.Readiness.Primitives) echo 43;;
  Proofs.Readiness.Init) echo 44;;
  Proofs.Readiness.Step1) echo 45;;
  Proofs.Readiness.Step2) echo 46;;
  Proofs.Readiness.Step5) echo 47;;
  Proofs.Readiness.IQFT) echo 48;;
  Proofs.Readiness.ModMul) echo 49;;
  Proofs.Readiness.ModExp) echo 50;;
  Proofs.Readiness.Dynamic) echo 51;;
  Proofs.NaiveShor*) echo 52;;
  Proofs.Correctness) echo 53;;
  Main) echo 60;;
  *) echo 99;; esac; }
# allowlisted layer-order exception (see REORG_SHOR.md §4): the assertion file inlines
# a `GateWorkspaceOK` proof term whose meaning is proof-irrelevant, but the file
# dependency on the Static readiness proof is real.
is_allowlisted() {
  [ "$1" = "Spec.Assertions" ] && [ "$2" = "Proofs.Readiness.Static" ]
}
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
      is_allowlisted "$mod" "$dep" && continue
      echo "LAYER VIOLATION: $mod imports $dep"; status=1
    fi
  done < <(grep -oE "^import ${prefix}[A-Za-z0-9_.]+" "$f" | sed 's/^import //')
done < <(find "$root" -name '*.lean')
exit $status
