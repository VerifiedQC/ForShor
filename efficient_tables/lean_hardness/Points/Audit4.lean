import Points.SatRed

/-! Axiom audit for Stage 3 (SAT → table problem; NP-hardness). -/

open Pts Complexity

#check @TS.sat_iff_dhc
#check @sat_iff_table
#check @sat_le_gen
#check @genLang_NPHard
#print axioms TS.sat_iff_dhc
#print axioms sat_iff_table
#print axioms sat_le_gen
#print axioms genLang_NPHard
