import Points.Encode
open Pts Complexity
#check @Pts.reduction_correct
#check @Pts.ehp_le_gen
#check @Pts.genLang_NPHard_of
#print axioms Pts.reduction_correct
#print axioms Pts.ehp_le_gen
#print axioms Pts.genLang_NPHard_of
-- the triangle as an adjacency matrix (n = 3): edges {0,1},{0,2},{1,2}
#eval edgesOf 3 [false, true, true, false, false, true, false, false, false]
