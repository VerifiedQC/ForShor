import FastMultiplication.ShorVerification.Implementation.MathBackbone.Table_Generation.Builders.Fragments
import FastMultiplication.ShorVerification.Implementation.MathBackbone.Table_Generation.Generator.Precomputed

open Operations

namespace Table_Generation

inductive ProductMode where
  | PhaseProduct
  | PhaseTripleProduct

/- Number of points required for a given product mode and number of registers -/
def ProductMode.pointCount : ProductMode → ℕ → ℕ
  | .PhaseProduct, k => 2*k-1
  | .PhaseTripleProduct, k => 3*k-2

/-
  Function for generating nth point in the stream (deterministic)
  `0,∞,1,-1,2,-2,1/2,-1/2,...`
-/
def streamPoint : ℕ -> Point
  | 0 => .int 0
  | 1 => .frac 0
  | 2 => .int 1
  | 3 => .int (-1)
  | n + 4 =>
    let e := 1 + (n / 4)
    match n % 4 with
    | 0 => .int (2 ^ e)
    | 1 => .int (- (2 ^ e))
    | 2 => .frac (2 ^ e)
    | _ => .frac (-(2 ^ e))

/- List of points used for provided product mode and k value (number of registers) -/
def generatedPoints (mode : ProductMode) (k : ℕ) : List Point :=
  (List.range (mode.pointCount k)).map streamPoint

/- Parity block helper definitions -/

inductive PointPairType where
  | integer
  | fraction
deriving DecidableEq, Repr

def twoPowInt (e : ℕ) : ℤ := 2 ^ e

def pairKindOfIndex (i : ℕ) : PointPairType :=
  match i % 2 with
  | 0 => .integer
  | _ => .fraction

def pairExponentOfIndex (i : ℕ) : ℕ := 1 + (i / 2)

def parityDegree (type : PointPairType) (k : ℕ) (j : Fin k) : ℕ:=
  match type with
  | .integer => j.val
  | .fraction => k-1-j.val

/- Register indices for even and odd powers -/
def evenCarrier (k : ℕ) (hk : k ≥ 4) : PointPairType → Fin k
  | .integer => ⟨0, by omega⟩
  | .fraction => ⟨k-1, by omega⟩ -- degree 0 at k-1

def oddCarrier (k : ℕ) (hk : k ≥ 4) : PointPairType → Fin k
  | .integer => ⟨1, by omega⟩
  | .fraction => ⟨k-2, by omega⟩ -- degree 1 at k-2

/- Generate sequence of operations for constructing an even or odd carrier register state -/
def carrierAdds (k : ℕ) (type : PointPairType) (e : ℕ) (dst : Fin k) (parity : ℕ) : Prog k :=
  (List.finRange k).foldl (fun acc j =>
    let d := parityDegree type k j
    if d % 2 = parity then
      if j = dst then acc else acc ++ (addConstFrom dst j (twoPowInt (e * d)))
    else acc
  ) []

/-
  Start with Even and Odd carrier registers, E and O. Want E+O and E-O.
  (1) O ← E+O (2) E ← 2E (3) E ← E-O (= 2E-(E+O) = E-O)
-/
def combineParityCarriers {k : ℕ} (even odd : Fin k) : Prog k := [
  valid_ops.addScaled odd even false 0, -- O ← E+O
  valid_ops.shiftL even 1, -- E ← 2E
  valid_ops.addScaled even odd true 0 -- E ← E-O
]

/- Initial dense block covering `0`, `∞`, `1`, and `-1`. -/
def generateParityInitialBlock (k : ℕ) (hk : k ≥ 4) : Prog k :=
  let r0 : Fin k := ⟨0, by omega⟩
  let r1 : Fin k := ⟨1, by omega⟩
  let r2 : Fin k := ⟨2, by omega⟩
  let rlast : Fin k := ⟨k-1, by omega⟩

  let buildEven := carrierAdds k .integer 0 r2 0
  let buildOdd := carrierAdds k .integer 0 r1 1
  let build := buildEven ++ buildOdd ++ combineParityCarriers r2 r1

  build ++ [
    valid_ops.phaseProduct r0, -- 0
    valid_ops.phaseProduct rlast, -- ∞
    valid_ops.phaseProduct r1, -- 1
    valid_ops.phaseProduct r2 -- -1
  ] ++ apply_Op_inverse build

/- One parity-reset symmetric-pair block. -/
def generateParityPairBlock (k : ℕ) (hk : k ≥ 4) (type : PointPairType) (e : ℕ) : Prog k :=
  let reven : Fin k := evenCarrier k hk type
  let rodd : Fin k := oddCarrier k hk type

  let buildEven := carrierAdds k type e reven 0
  let buildOdd := [valid_ops.shiftL rodd e] ++ (carrierAdds k type e rodd 1)
  let build := buildEven ++ buildOdd ++ combineParityCarriers reven rodd

  build ++ [
    valid_ops.phaseProduct rodd, -- +x
    valid_ops.phaseProduct reven -- -x
  ] ++ apply_Op_inverse build

/- Final unpaired parity-reset point block (for k odd) -/
def generateParitySingletonBlock (k : ℕ) (hk : k ≥ 4) (x : Point) : Prog k :=
  opsForPointWithProduct (by omega) x

/- Append the first `pairCount` parity-reset symmetric-pair blocks. -/
def generateParityPairBlocks (k : ℕ) (hk : k ≥ 4) (pairCount : ℕ) : Prog k :=
  (List.range pairCount).foldl (fun acc i =>
    acc ++ generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i)
  ) []

/- Shared general parity-reset generator for any product mode. -/
def generateParityForMode (mode : ProductMode) (k : ℕ) (hk : k ≥ 4) : Prog k :=
  -- Number of points after initial layer
  let rem := mode.pointCount k - 4
  let pairCount := rem / 2
  -- If odd number of points, generate a singleton block for handling the last point
  let singleton :=
    if rem % 2 = 1 then
      generateParitySingletonBlock k hk (streamPoint (4 + 2*pairCount))
    else
      []
  generateParityInitialBlock k hk ++
    generateParityPairBlocks k hk pairCount ++
    singleton

/- General `k ≥ 4` phase-product generator. -/
def generateParityProduct (k : ℕ) (hk : k ≥ 4) : Prog k :=
  generateParityForMode .PhaseProduct k hk

/- General `k ≥ 4` phase-triple-product generator. -/
def generateParityTripleProduct (k : ℕ) (hk : k ≥ 4) : Prog k :=
  generateParityForMode .PhaseTripleProduct k hk

/- Entry point for generating operations for any k ≥ 2 and any product mode -/
def generate (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : Prog k :=
  match mode with
  | .PhaseProduct =>
    if h2 : k=2 then
      by { subst k ; exact PrecomputedTables.K2Product.program }
    else if h3 : k=3 then
      by { subst k ; exact PrecomputedTables.K3Product.program }
    else
      generateParityProduct k (by omega)
  | .PhaseTripleProduct =>
    if h2 : k=2 then
      by { subst k ; exact PrecomputedTables.K2TripleProduct.program }
    else if h3 : k=3 then
      by { subst k ; exact PrecomputedTables.K3TripleProduct.program }
    else
      generateParityTripleProduct k (by omega)

-- Entry point for generating points in order for any k ≥ 2 and any product mode
def generatePointsInOrder (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : List Point :=
  match mode with
  | .PhaseProduct =>
    if h2 : k=2 then
      by { subst k ; exact PrecomputedTables.K2Product.orderedPoints }
    else if h3 : k=3 then
      by { subst k ; exact PrecomputedTables.K3Product.orderedPoints }
    else
      generatedPoints mode k
  | .PhaseTripleProduct =>
    if h2 : k=2 then
      by { subst k ; exact PrecomputedTables.K2TripleProduct.orderedPoints }
    else if h3 : k=3 then
      by { subst k ; exact PrecomputedTables.K3TripleProduct.orderedPoints }
    else
      generatedPoints mode k

/- Helper definitions for generating parallel layer sizes for any k ≥ 2 -/

def generateParityLayerSizesForMode (mode : ProductMode) (k : ℕ) (_hk : k ≥ 4) : List ℕ :=
  let rem := mode.pointCount k - 4
  let pairCount := rem / 2
  ([4] ++ List.replicate pairCount 2) ++
    if rem % 2 = 1 then [1] else []

def generateLayerSizes (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : List ℕ :=
  match mode with
  | .PhaseProduct =>
      if h2 : k = 2 then
        by { subst k; exact PrecomputedTables.K2Product.layerSizes }
      else if h3 : k = 3 then
        by { subst k; exact PrecomputedTables.K3Product.layerSizes }
      else
        generateParityLayerSizesForMode .PhaseProduct k (by omega)
  | .PhaseTripleProduct =>
      if h2 : k = 2 then
        by { subst k; exact PrecomputedTables.K2TripleProduct.layerSizes }
      else if h3 : k = 3 then
        by { subst k; exact PrecomputedTables.K3TripleProduct.layerSizes }
      else
        generateParityLayerSizesForMode .PhaseTripleProduct k (by omega)

end Table_Generation
