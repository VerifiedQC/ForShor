import FastMultiplication.ShorVerification.Implementation.MathBackbone.Table_Generation.Core.Language

open Operations

namespace Table_Generation.PrecomputedTables

/- Precomputed k=2 and k=3 table-generator artifacts for PhaseProduct and PhaseTripleProduct -/

namespace K2Product

def targetPoints : List Point :=
  [.int 0, .frac 0, .int 1]

def orderedPoints : List Point :=
  targetPoints

def program : Prog 2 :=
  [ valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 true 0
  ]

def layerSizes : List ℕ :=
  [2, 1]

end K2Product

namespace K3Product

def targetPoints : List Point :=
  [.int 0, .frac 0, .int 1, .int (-1), .int 2]

def orderedPoints : List Point :=
  [.int 1, .int 2, .frac 0, .int (-1), .int 0]

def program : Prog 3 :=
  [ valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.addScaled 0 2 false 0
  , valid_ops.addScaled 1 2 false 2
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.addScaled 0 2 false 1
  , valid_ops.addScaled 1 0 false 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 1 2 true 1
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.addScaled 0 2 true 0
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 0 1 false 0
  ]

def layerSizes : List ℕ :=
  [3, 2]

end K3Product

namespace K2TripleProduct

def targetPoints : List Point :=
  [.int 0, .frac 0, .int 1, .int (-1)]

def orderedPoints : List Point :=
  targetPoints

def program : Prog 2 :=
  [ valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.shiftL 1 1
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.negate 1
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.negate 1
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.shiftR 1 1
  , valid_ops.addScaled 0 1 true 0
  ]

def layerSizes : List ℕ :=
  [2, 2]

end K2TripleProduct

namespace K3TripleProduct

def targetPoints : List Point :=
  [.int 0, .frac 0, .int 1, .int (-1), .int 2, .int (-2), .frac 2]

def orderedPoints : List Point :=
  [.int (-2), .int (-1), .frac 0, .int 2, .int 1, .int 0, .frac 2]

def program : Prog 3 :=
  [ valid_ops.addScaled 0 1 true 1
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.addScaled 0 2 false 2
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 0 1 true 1
  , valid_ops.addScaled 1 2 true 2
  , valid_ops.addScaled 2 0 true 0
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 1 true 0
  , valid_ops.addScaled 0 2 false 1
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 0 1 false 1
  , valid_ops.addScaled 1 2 false 1
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.addScaled 2 0 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 2 1 true 1
  , valid_ops.addScaled 1 0 true 1
  ]

def layerSizes : List ℕ :=
  [3, 2, 2]

end K3TripleProduct

end Table_Generation.PrecomputedTables
