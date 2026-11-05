import Foundations.SeparationLemmas.Main

/-! Axiom audit. Run with `lake env lean lean/Foundations/SeparationLemmas/Audit.lean`.
Each theorem should depend only on `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms SeparationLemmas.definitions_unfold
#print axioms SeparationLemmas.peeling
#print axioms SeparationLemmas.zero_criterion
#print axioms SeparationLemmas.integrality_anchored
