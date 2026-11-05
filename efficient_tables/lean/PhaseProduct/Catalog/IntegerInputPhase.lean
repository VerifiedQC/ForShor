import PhaseProduct.Catalog.FinitePhase
import Model.Scanner.LimbReconstruction

/-!
# Phase identity on integer inputs

Connects deterministic signed-magnitude preprocessing of integers to the
best-known words. It evaluates limbs (`evaluate_limbs`) and gives the pair and
triple identities on integer inputs (`bestKnown_pair_integer_inputs`,
`bestKnown_triple_integer_inputs`), each with a single weight vector.
-/

namespace Paper.IntegerInputPhase

theorem evaluate_limbs (W : Nat) {k : Nat} (hk : 0 < k) (n : Int) :
    (∑ j : Fin k, (Paper.SignedLimbs.radix W k : ℚ) ^ j.val *
      (Paper.SignedLimbs.limbs W hk n j : ℚ)) = (n : ℚ) := by
  calc
    _ = ∑ j : Fin k, (Paper.SignedLimbs.limbs W hk n j : ℚ) *
          (Paper.SignedLimbs.radix W k : ℚ) ^ j.val := by
            apply Finset.sum_congr rfl
            intro j hj
            exact mul_comm _ _
    _ = (n : ℚ) := Paper.SignedLimbs.limbs_reconstruct_rat W hk n

/-- Deterministic signed-magnitude preprocessing connects the original flat
BestKnown pair word to the product of the two input integers. -/
theorem bestKnown_pair_integer_inputs (W k : Nat) (hk : 2 ≤ k) :
    let hpos : 0 < k := by omega
    let ops := TableGeneration.bestKnownGenerate .PhaseProduct k hk
    let B := TableGeneration.RecursiveCost.nextBalancedSignedWidth W ops
    ∃ weight : Fin (2*(k-1)+1) → ℚ, ∀ theta : ℝ, ∀ a c : Int,
      a.natAbs < 2 ^ W → c.natAbs < 2 ^ W →
      ∃ mx mz : List (BitVec B),
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) (Paper.SignedLimbs.limbs W hpos a)) =
            some (Paper.BitStep.encode (B := B) (Paper.SignedLimbs.limbs W hpos a), mx) ∧
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) (Paper.SignedLimbs.limbs W hpos c)) =
            some (Paper.BitStep.encode (B := B) (Paper.SignedLimbs.limbs W hpos c), mz) ∧
        mx.length = 2*k-1 ∧ mz.length = 2*k-1 ∧
        (∏ l, Paper.ValuePhase.phaseCharacter theta
          (weight l * ((mx.map BitVec.toInt).getD l.val 0 : ℚ) *
            ((mz.map BitVec.toInt).getD l.val 0 : ℚ))) =
          Paper.ValuePhase.phaseCharacter theta ((a : ℚ) * (c : ℚ)) := by
  dsimp only
  have hpos : 0 < k := by omega
  obtain ⟨weight, hall⟩ :=
    Paper.FinitePhase.bestKnown_pair_finite_phase_product k hk W
      (Paper.SignedLimbs.radix W k : ℚ)
  refine ⟨weight, ?_⟩
  intro theta a c ha hc
  obtain ⟨mx, mz, hx, hz, hxl, hzl, hphase⟩ :=
    hall theta (Paper.SignedLimbs.limbs W hpos a)
      (Paper.SignedLimbs.limbs W hpos c)
      (Paper.SignedLimbs.limbs_fits W hpos a ha)
      (Paper.SignedLimbs.limbs_fits W hpos c hc)
  refine ⟨mx, mz, hx, hz, hxl, hzl, ?_⟩
  simpa only [evaluate_limbs] using hphase

/-- The analogous native triple word has a single weight vector before all
angles and bounded signed integer triples. -/
theorem bestKnown_triple_integer_inputs (W k : Nat) (hk : 2 ≤ k) :
    let hpos : 0 < k := by omega
    let ops := TableGeneration.bestKnownGenerate .PhaseTripleProduct k hk
    let B := TableGeneration.RecursiveCost.nextBalancedSignedWidth W ops
    ∃ weight : Fin (3*(k-1)+1) → ℚ, ∀ theta : ℝ, ∀ a b c : Int,
      a.natAbs < 2 ^ W → b.natAbs < 2 ^ W → c.natAbs < 2 ^ W →
      ∃ mx my mz : List (BitVec B),
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) (Paper.SignedLimbs.limbs W hpos a)) =
            some (Paper.BitStep.encode (B := B) (Paper.SignedLimbs.limbs W hpos a), mx) ∧
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) (Paper.SignedLimbs.limbs W hpos b)) =
            some (Paper.BitStep.encode (B := B) (Paper.SignedLimbs.limbs W hpos b), my) ∧
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) (Paper.SignedLimbs.limbs W hpos c)) =
            some (Paper.BitStep.encode (B := B) (Paper.SignedLimbs.limbs W hpos c), mz) ∧
        mx.length = 3*k-2 ∧ my.length = 3*k-2 ∧ mz.length = 3*k-2 ∧
        (∏ l, Paper.ValuePhase.phaseCharacter theta
          (weight l * ((mx.map BitVec.toInt).getD l.val 0 : ℚ) *
            ((my.map BitVec.toInt).getD l.val 0 : ℚ) *
            ((mz.map BitVec.toInt).getD l.val 0 : ℚ))) =
          Paper.ValuePhase.phaseCharacter theta ((a : ℚ) * (b : ℚ) * (c : ℚ)) := by
  dsimp only
  have hpos : 0 < k := by omega
  obtain ⟨weight, hall⟩ :=
    Paper.FinitePhase.bestKnown_triple_finite_phase_product k hk W
      (Paper.SignedLimbs.radix W k : ℚ)
  refine ⟨weight, ?_⟩
  intro theta a b c ha hb hc
  obtain ⟨mx, my, mz, hx, hy, hz, hxl, hyl, hzl, hphase⟩ :=
    hall theta (Paper.SignedLimbs.limbs W hpos a)
      (Paper.SignedLimbs.limbs W hpos b)
      (Paper.SignedLimbs.limbs W hpos c)
      (Paper.SignedLimbs.limbs_fits W hpos a ha)
      (Paper.SignedLimbs.limbs_fits W hpos b hb)
      (Paper.SignedLimbs.limbs_fits W hpos c hc)
  refine ⟨mx, my, mz, hx, hy, hz, hxl, hyl, hzl, ?_⟩
  simpa only [evaluate_limbs] using hphase

end Paper.IntegerInputPhase
