import Source.P6Parity

/-!
# Pf4 optimized parity construction

Optimized parity construction for Pf4, reusing the P6 parity machinery. Defines `generateParityPairBlock`, `parityBlocks`, `program` and `generate`, selects the scored `k` values with `scoredK`, and proves `generatedPoints_valid_scored` and `generate_safe_scored`.
-/

namespace TableGeneration.Policies.Accepted.Pf4aff955f16b.OptimizedParity

open Operations
open Policies.Accepted.P6f7d25984ff8.GeneralParity

def carrierAddsOffset
    (k : Nat) (kind : PointPairType) (e : Nat) (dst : Fin k)
    (parity offset : Nat) : Prog k :=
  (List.finRange k).foldl (fun acc j =>
    let d := parityDegree kind k j
    if d % 2 = parity then
      if j = dst then acc else acc ++ addConstFrom dst j (twoPowInt (e * d - offset))
    else
      acc) []

def generateParityPairBlock
    (k : Nat) (hk : k >= 4) (kind : PointPairType) (e : Nat) : Prog k :=
  let even := evenCarrier k hk kind
  let odd := oddCarrier k hk kind
  let buildEven := carrierAdds k kind e even 0
  let buildOddHalf := carrierAddsOffset k kind e odd 1 e
  let build := buildEven ++ buildOddHalf ++
    [.addScaled even odd true e,
     .shiftL odd (e + 1),
     .addScaled odd even false 0]
  build ++ [.phaseProduct odd, .phaseProduct even] ++ apply_Op_inverse build

def parityBlocks
    (mode : ProductMode) (k : Nat) (hk : k >= 4) : List (ResetBlock k) :=
  let remaining := mode.pointCount k - 4
  let pairCount := remaining / 2
  let initial : ResetBlock k :=
    (generateParityInitialBlock k hk,
      [canonicalPoint 0, canonicalPoint 1, canonicalPoint 2, canonicalPoint 3])
  let pairs := (List.range pairCount).map fun i =>
    (generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i),
      [canonicalPoint (4 + 2 * i), canonicalPoint (5 + 2 * i)])
  let singleton :=
    if remaining % 2 = 1 then
      let index := 4 + 2 * pairCount
      [(generateParitySingletonBlock k hk (canonicalPoint index), [canonicalPoint index])]
    else
      []
  initial :: pairs ++ singleton

def program (mode : ProductMode) (k : Nat) (hk : k >= 4) : Prog k :=
  blockPrograms (parityBlocks mode k hk)

def generate (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k :=
  if h4 : k >= 4 then program mode k h4 else baselineGenerate mode k hk

def scoredK (k : Nat) : Bool :=
  decide (k = 4) || (decide (k = 5) || (decide (k = 6) ||
    (decide (k = 7) || (decide (k = 8) || (decide (k = 9) ||
    (decide (k = 10) || (decide (k = 11) || (decide (k = 12) ||
    (decide (k = 13) || (decide (k = 14) ||
    (decide (k = 15) || decide (k = 16))))))))))))

theorem scoredK_cases {k : Nat} (h : scoredK k = true) :
    k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
      k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨
      k = 15 ∨ k = 16 := by
  simpa [scoredK, Bool.or_eq_true, decide_eq_true_eq] using h

theorem generatedPoints_valid_scored
    (mode : ProductMode) (k : Nat) (h : scoredK k = true) :
    ValidPointList mode k (canonicalPoints mode k) := by
  rcases scoredK_cases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst k
  all_goals cases mode <;> unfold ValidPointList canonicalPoints <;> decide

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem generate_safe_scored
    (mode : ProductMode) (k : Nat) (hk : k >= 2) (h : scoredK k = true) :
    ValidPointOrder (canonicalPoints mode k) (canonicalPoints mode k) ∧
      ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
        (generate mode k hk) (canonicalPoints mode k) := by
  rcases scoredK_cases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst k
  all_goals
    have hhk : hk = by decide := Subsingleton.elim _ _
    subst hk
    constructor
    · exact List.Perm.refl _
    · cases mode <;> apply progConsumesPtsSafe_of_checks <;> decide

end TableGeneration.Policies.Accepted.Pf4aff955f16b.OptimizedParity
