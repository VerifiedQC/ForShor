import Foundations.SmallPoint.Main

/-! Axiom audit for the small-integer-point development. Run with
`lake env lean lean/Foundations/SmallPoint/Audit.lean`. Each theorem should depend only on
`propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms SmallPoint.cofactor_extreme
#print axioms SmallPoint.extreme_decomposition
#print axioms SmallPoint.conic_caratheodory
#print axioms SmallPoint.small_integer_point
