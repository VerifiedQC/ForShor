import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.Spec

open Operations

namespace Table_Generation

def generatedPoints (mode : ProductMode) (k : ℕ) : List Point :=
  canonicalPoints mode k

def generatePointsInOrder (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : List Point :=
  match hk with
  | _ => generatedPoints mode k

def targetFirst : Prog 4 :=
  (1 +:= 3 << 0) ;;
  (2 +:= 0 << 0) ;;
  (1 +:= 2 << 0) ;;
  (2 <<s= 1) ;;
  (2 -:= 1 << 0)

def targetAtTwo : Prog 4 :=
  (2 <<s= 2) ;;
  (2 +:= 0 << 0) ;;
  (1 +:= 3 << 2) ;;
  (2 -:= 1 << 1) ;;
  (1 <<s= 2) ;;
  (1 +:= 2 << 0)

def targetAtHalf : Prog 4 :=
  (1 <<s= 2) ;;
  (1 +:= 3 << 0) ;;
  (2 +:= 0 << 2) ;;
  (1 -:= 2 << 1) ;;
  (2 <<s= 2) ;;
  (2 +:= 1 << 0)

def targetAtFour : Prog 4 :=
  (2 <<s= 4) ;;
  (2 +:= 0 << 0) ;;
  (1 +:= 3 << 4) ;;
  (2 -:= 1 << 2) ;;
  (1 <<s= 3) ;;
  (1 +:= 2 << 0)

def targetGenerate : Prog 4 :=
  targetFirst ;;
  [valid_ops.phaseProduct 0, valid_ops.phaseProduct 3,
    valid_ops.phaseProduct 1, valid_ops.phaseProduct 2] ;;
  apply_Op_inverse targetFirst ;;
  targetAtTwo ;;
  [valid_ops.phaseProduct 1, valid_ops.phaseProduct 2] ;;
  apply_Op_inverse targetAtTwo ;;
  targetAtHalf ;;
  [valid_ops.phaseProduct 2, valid_ops.phaseProduct 1] ;;
  apply_Op_inverse targetAtHalf ;;
  targetAtFour ;;
  [valid_ops.phaseProduct 1, valid_ops.phaseProduct 2]

def tableFinOne {k : ℕ} (hk : k ≥ 2) : Fin k :=
  ⟨1, by omega⟩

def tableFinTwo {k : ℕ} (hk : k ≥ 3) : Fin k :=
  ⟨2, by omega⟩

def tableFinBeforeLast {k : ℕ} (hk : k ≥ 2) : Fin k :=
  ⟨k - 2, by omega⟩

def maybeShift {k : ℕ} (i : Fin k) (amount : ℕ) : Prog k :=
  if amount = 0 then [] else [valid_ops.shiftL i amount]

def parityContributions {k : ℕ}
    (dst : Fin k) (exponent : Fin k → ℕ) (wantEven : Bool) (scale : ℕ) : Prog k :=
  (List.finRange k).filterMap fun src =>
    if src = dst then
      none
    else if decide (Even (exponent src)) = wantEven then
      some (valid_ops.addScaled dst src false (scale * exponent src))
    else
      none

def pairButterfly {k : ℕ} (evenDst oddDst : Fin k) : Prog k :=
  [valid_ops.addScaled evenDst oddDst false 0,
    valid_ops.shiftL oddDst 1,
    valid_ops.addScaled oddDst evenDst true 0,
    valid_ops.negate oddDst]

def firstPairBuild {k : ℕ} (hk : k ≥ 4) : Prog k :=
  let evenDst := tableFinTwo (by omega : k ≥ 3)
  let oddDst := tableFinOne (by omega : k ≥ 2)
  parityContributions evenDst (fun j => j.val) true 0 ++
    parityContributions oddDst (fun j => j.val) false 0 ++
    pairButterfly evenDst oddDst

def firstPairPhases {k : ℕ} (hk : k ≥ 4) : Prog k :=
  [valid_ops.phaseProduct (finZero (by omega)),
    valid_ops.phaseProduct (finLast (by omega)),
    valid_ops.phaseProduct (tableFinTwo (by omega : k ≥ 3)),
    valid_ops.phaseProduct (tableFinOne (by omega : k ≥ 2))]

def intPairBuild {k : ℕ} (hk : k ≥ 2) (e : ℕ) : Prog k :=
  let evenDst := finZero (by omega : 0 < k)
  let oddDst := tableFinOne hk
  maybeShift oddDst e ++
    parityContributions evenDst (fun j => j.val) true e ++
    parityContributions oddDst (fun j => j.val) false e ++
    pairButterfly evenDst oddDst

def intPairPhases {k : ℕ} (hk : k ≥ 2) : Prog k :=
  [valid_ops.phaseProduct (finZero (by omega)),
    valid_ops.phaseProduct (tableFinOne hk)]

def fracExponent {k : ℕ} (j : Fin k) : ℕ :=
  k - 1 - j.val

def fracPairBuild {k : ℕ} (hk : k ≥ 2) (e : ℕ) : Prog k :=
  let evenDst := finLast (by omega : 0 < k)
  let oddDst := tableFinBeforeLast hk
  maybeShift oddDst e ++
    parityContributions evenDst fracExponent true e ++
    parityContributions oddDst fracExponent false e ++
    pairButterfly evenDst oddDst

def fracPairPhases {k : ℕ} (hk : k ≥ 2) : Prog k :=
  [valid_ops.phaseProduct (finLast (by omega)),
    valid_ops.phaseProduct (tableFinBeforeLast hk)]

def indexedPairBuild {k : ℕ} (hk : k ≥ 2) (pairIndex : ℕ) : Prog k :=
  let e := pairIndex / 2 + 1
  if pairIndex % 2 = 0 then intPairBuild hk e else fracPairBuild hk e

def indexedPairPhases {k : ℕ} (hk : k ≥ 2) (pairIndex : ℕ) : Prog k :=
  if pairIndex % 2 = 0 then intPairPhases hk else fracPairPhases hk

def opsForFinalPoint {k : ℕ} (hk : k ≥ 2) : Point → Prog k
  | .int z =>
      let build := computeLocal2 (by omega) z
      build ++ [valid_ops.phaseProduct (finZero (by omega))]
  | .frac c =>
      if c = 0 then
        [valid_ops.phaseProduct (finLast (by omega))]
      else
        let build := computeFracLocal2 (by omega) c
        build ++ [valid_ops.phaseProduct (finLast (by omega))]

abbrev GenerationSegment (k : ℕ) := Prog k × List Point

def phaseProductTwoCandidate : Prog 2 :=
  [valid_ops.phaseProduct 0, valid_ops.phaseProduct 1] ;;
  (0 +:= 1 << 0) ;;
  [valid_ops.phaseProduct 0]

def phaseTripleProductTwoCandidate : Prog 2 :=
  [valid_ops.phaseProduct 0, valid_ops.phaseProduct 1] ;;
  (0 +:= 1 << 0) ;;
  [valid_ops.phaseProduct 0] ;;
  (0 -:= 1 << 1) ;;
  [valid_ops.phaseProduct 0]

def firstThreeBuild : Prog 3 :=
  (1 +:= 0 << 0) ;;
  (1 +:= 2 << 0)

def firstThreePhases : Prog 3 :=
  [valid_ops.phaseProduct 0, valid_ops.phaseProduct 2, valid_ops.phaseProduct 1]

def phaseProductThreeSegments : List (GenerationSegment 3) :=
  let first := firstThreeBuild ++ firstThreePhases ++ apply_Op_inverse firstThreeBuild
  let minusOne := opsForPointWithProduct (by decide) (.int (-1))
  let atTwo := opsForFinalPoint (by decide) (.int 2)
  [(first, [.int 0, .frac 0, .int 1]),
    (minusOne, [.int (-1)]),
    (atTwo, [.int 2])]

def strongSegmentTail {k : ℕ} (hk : k ≥ 2) : ℕ → ℕ → List (GenerationSegment k)
  | 0, _ => []
  | 1, pairIndex =>
      let pt := canonicalPoint (4 + 2 * pairIndex)
      [(opsForFinalPoint hk pt, [pt])]
  | remaining + 2, pairIndex =>
      let build := indexedPairBuild hk pairIndex
      let core := build ++ indexedPairPhases hk pairIndex
      let program := if remaining = 0 then core else core ++ apply_Op_inverse build
      let points :=
        [canonicalPoint (4 + 2 * pairIndex), canonicalPoint (5 + 2 * pairIndex)]
      (program, points) :: strongSegmentTail hk remaining (pairIndex + 1)
termination_by remaining _ => remaining

def strongSegments (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) :
    List (GenerationSegment k) :=
  match mode, k with
  | .PhaseProduct, 2 =>
      [(phaseProductTwoCandidate, [.int 0, .frac 0, .int 1])]
  | .PhaseTripleProduct, 2 =>
      [(phaseTripleProductTwoCandidate, [.int 0, .frac 0, .int 1, .int (-1)])]
  | .PhaseProduct, 3 => phaseProductThreeSegments
  | mode, k =>
      if hk4 : k ≥ 4 then
        let build := firstPairBuild hk4
        let firstProgram := build ++ firstPairPhases hk4 ++ apply_Op_inverse build
        let firstPoints := [canonicalPoint 0, canonicalPoint 1,
          canonicalPoint 2, canonicalPoint 3]
        (firstProgram, firstPoints) :: strongSegmentTail hk (mode.pointCount k - 4) 0
      else
        [(genOpsWithProduct (by omega) (generatePointsInOrder mode k hk),
          generatePointsInOrder mode k hk)]

def segmentPrograms {k : ℕ} (segments : List (GenerationSegment k)) : Prog k :=
  segments.flatMap Prod.fst

def segmentPoints {k : ℕ} (segments : List (GenerationSegment k)) : List Point :=
  segments.flatMap Prod.snd

def strongCandidate (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : Prog k :=
  segmentPrograms (strongSegments mode k hk)

def orderedConsumptionCheck {k : ℕ} (hk : k > 0) :
    State k → Prog k → List Point → Bool
  | _, [], pts => pts.isEmpty
  | σ, op :: ops, pts =>
      match op with
      | valid_ops.phaseProduct i =>
          match pts with
          | [] => false
          | pt :: ptsTail =>
              matchesAt_pointRow_state hk σ i pt &&
                orderedConsumptionCheck hk σ ops ptsTail
      | _ =>
          match applyOp? σ op with
          | none => false
          | some σ' => orderedConsumptionCheck hk σ' ops pts

def operationSafe {k : ℕ} : valid_ops k → Bool
  | valid_ops.addScaled dst src _ _ => decide (dst ≠ src)
  | _ => true

def programSafe {k : ℕ} (ops : Prog k) : Bool :=
  ops.all operationSafe

def statesEqual {k : ℕ} (left right : State k) : Bool :=
  (List.finRange k).all fun i =>
    (List.finRange k).all fun j => decide (left i j = right i j)

def returnsToStartCheck {k : ℕ} (program : Prog k) : Bool :=
  match run? program State.start_state with
  | none => false
  | some σ => statesEqual σ State.start_state

def segmentConsumptionCheck {k : ℕ} (hk : k > 0) :
    List (GenerationSegment k) → Bool
  | [] => true
  | [(program, pts)] =>
      orderedConsumptionCheck hk State.start_state program pts
  | (program, pts) :: next :: rest =>
      orderedConsumptionCheck hk State.start_state program pts &&
        returnsToStartCheck program &&
        segmentConsumptionCheck hk (next :: rest)

def strongCandidateValid (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : Bool :=
  let segments := strongSegments mode k hk
  decide (segmentPoints segments = generatePointsInOrder mode k hk) &&
    segmentConsumptionCheck (by omega) segments &&
    programSafe (segmentPrograms segments)

def checkedStrongGenerate (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : Prog k :=
  let candidate := strongCandidate mode k hk
  let pts := generatePointsInOrder mode k hk
  if strongCandidateValid mode k hk then
    candidate
  else
    genOpsWithProduct (by omega) pts

def generate : (mode : ProductMode) → (k : ℕ) → (hk : k ≥ 2) → Prog k
  | .PhaseTripleProduct, 4, _ => targetGenerate
  | mode, k, hk => checkedStrongGenerate mode k hk

end Table_Generation
