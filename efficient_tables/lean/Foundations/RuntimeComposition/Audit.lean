import Foundations.RuntimeComposition.Main
import Foundations.RuntimeComposition.Cutoff

/-! Axiom audit for the runtime-composition development. Run with
`lake env lean lean/Foundations/RuntimeComposition/Audit.lean`. Each theorem should depend only on
`propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms RuntimeComposition.S_le_two_pow
#print axioms RuntimeComposition.tt_le_factorial_sq
#print axioms RuntimeComposition.triple_count_le
#print axioms RuntimeComposition.local_factor_bound
#print axioms RuntimeComposition.composition
