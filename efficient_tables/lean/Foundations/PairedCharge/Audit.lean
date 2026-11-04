import Foundations.PairedCharge.Main

/-! Axiom audit. Run with `lake env lean lean/Foundations/PairedCharge/Audit.lean`.
Each theorem should depend only on `propext`, `Classical.choice`, `Quot.sound`
(`charge_classes` only on `propext`). -/

#print axioms PairedCharge.points_def
#print axioms PairedCharge.charge_classes
#print axioms PairedCharge.skeleton_unfold
#print axioms PairedCharge.charge_formula
#print axioms PairedCharge.charge_le
