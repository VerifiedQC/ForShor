import FastMultiplication.ShorVerification.Implementation.Reference.Balanced.Semantics

/-!
# Fault challenge: wrong recombinations for unequal operands fail

1. `commonRadix_recombination_fails` (candidate (a)): if the two operands are
   cut at different radices `2^mx ≠ 2^mz`, recombining the convolution
   coefficients `c_l = Σ_{i+j=l} x_i z_j` with any single radix `2^m` is wrong
   for some limbs (already for `k = 2`). This is the algebraic shape of a
   one-radix recombination such as `cramerCoeffFromPtsWidth k m`; the lemma is
   about the local `recombineAt` and is not formally linked to that definition.
2. `shiftless_split_fails` (a mutated balanced split): dropping the `2^w`
   from the high part's angle gives a circuit that, in *every* model, differs
   from `SignedPhaseProd φ x z` on a clean basis state, for any `φ` in the stated
   (non-degenerate) range.
3. `signedLow_decode_fails`: reading the low block signed instead of
   zero-extending it breaks the recombination identity (concrete values).
-/

namespace Shor
namespace Balanced

open Gate

universe u

/-! ## 1. Candidate (a) with one radix -/

/-- Two-limb operands at radices `2^mx`, `2^mz`; the convolution coefficients
recombined at radix `2^m`. -/
def recombineAt (m : ℕ) (x0 x1 z0 z1 : ℤ) : ℤ :=
  x0 * z0 + 2 ^ m * (x0 * z1 + x1 * z0) + 2 ^ (2 * m) * (x1 * z1)

theorem commonRadix_recombination_fails (mx mz m : ℕ) (hne : mx ≠ mz) :
    ¬ ∀ x0 x1 z0 z1 : ℤ, recombineAt m x0 x1 z0 z1 = (x0 + 2 ^ mx * x1) * (z0 + 2 ^ mz * z1) := by
  intro h
  have h1 := h 0 1 1 0
  have h2 := h 1 0 0 1
  simp [recombineAt] at h1 h2
  have h3 : (2 : ℤ) ^ mx = 2 ^ mz := by rw [← h1, h2]
  have h4 : (2 : ℕ) ^ mx = 2 ^ mz := by exact_mod_cast h3
  exact hne (Nat.pow_right_injective (le_refl 2) h4)

/-- With equal radices the single-radix recombination is right (the sanity side). -/
theorem commonRadix_recombination_ok (m : ℕ) (x0 x1 z0 z1 : ℤ) :
    recombineAt m x0 x1 z0 z1 = (x0 + 2 ^ m * x1) * (z0 + 2 ^ m * z1) := by
  unfold recombineAt; ring

/-! ## 3. A signed low block -/

/-- Reading a low block signed: `x = 01₂` (width 2, `w = 1`) is `1`, but the signed
low bit plus twice the high part is `-1`. -/
theorem signedLow_decode_fails :
    tcDecodeWidth 2 (1 + 2 ^ 1 * 0) ≠ tcDecodeWidth 1 1 + 2 ^ 1 * tcDecodeWidth 1 0 := by
  decide

/-- The shiftless recombination of the integers: `x = 10₂` (width 2) is `-2`,
but low plus high (no `2^w`) is `-1`. -/
theorem shiftless_decode_fails :
    tcDecodeWidth 2 (0 + 2 ^ 1 * 1) ≠ (0 : ℤ) + tcDecodeWidth 1 1 := by
  decide

/-! ## 2. A mutated split circuit -/

/-- The mutant: one low block and the high part, both at angle `φ` (the `2^w`
shift of the recombination is missing). -/
def shiftlessSplit (c : Ctl) (φ : Angle) (x z : ExtReg) (w t t' : ℕ) : Gate :=
  lowGate c φ x z w t ;; topGate c φ (highPart x w) z t'

theorem shiftlessSplit_ket (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (φ : Angle) (x z : ExtReg) (w t t' : ℕ) (b : qs.Basis)
    (hw : w ≤ x.width) (ht : w + 1 ≤ t) (hxcap : t - w ≤ x.capacity) (hzcap : t - z.width ≤ z.capacity)
    (hxcap' : t' - (highPart x w).width ≤ x.capacity) (hzcap' : t' - z.width ≤ z.capacity)
    (hd : ExtReg.OwnedDisjoint x z) (hb : Clean x z b) :
    qs.eval (shiftlessSplit .none φ x z w t t') (qs.ket b) =
      phaseFactor φ ((lowBlock x w).toNat b + extToInt (highPart x w) b) (extToInt z b) • qs.ket b := by
  have hd' : ExtReg.OwnedDisjoint (highPart x w) z :=
    ownedDisjoint_mono hd (highPart_owned_sub x w) (fun _ h => h)
  simp only [shiftlessSplit, QSemantics.eval_seq]
  rw [lowGate_ket qs .none φ x z w t b hw ht hxcap hzcap hd trivial hb, QSemantics.eval_smul,
    topGate_ket qs .none φ (highPart x w) z t' b (by simpa using hxcap') hzcap' hd' trivial hb, smul_smul]
  congr 1
  simp only [Ctl.factor, Ctl.on, ite_true]
  unfold phaseFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Phases at angles `π·θ₁`, `π·θ₂` differ when `0 < |θ₁ - θ₂| < 2`. -/
theorem phaseFactor_ne (φ : Angle) (X Y Z : ℤ)
    (h0 : 0 < |(φ : ℝ) * (((X - Y) * Z : ℤ) : ℝ)|) (h2 : |(φ : ℝ) * (((X - Y) * Z : ℤ) : ℝ)| < 2) :
    phaseFactor φ X Z ≠ phaseFactor φ Y Z := by
  intro h
  unfold phaseFactor at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  set θ : ℝ := (φ : ℝ) * (((X - Y) * Z : ℤ) : ℝ) with hθ
  have key : ((θ : ℝ) : ℂ) * (Real.pi : ℂ) * Complex.I = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hθ]; push_cast
    simp only [Angle.toReal] at hn
    push_cast at hn
    linear_combination hn
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have key2 : ((θ : ℝ) : ℂ) = ((2 * n : ℤ) : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast
    linear_combination key
  have key3 : θ = (2 * n : ℤ) := by exact_mod_cast key2
  rw [key3] at h0 h2
  have : (2 * n : ℤ) ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have h4 : (2 : ℝ) ≤ |((2 * n : ℤ) : ℝ)| := by
    have : (2 : ℤ) ≤ |2 * n| := by
      rcases lt_trichotomy n 0 with hn | hn | hn
      · rw [abs_of_neg (by omega)]; omega
      · subst hn; simp at this
      · rw [abs_of_pos (by omega)]; omega
    exact_mod_cast this
  linarith

/-- **The fault must fail.** In every model, the shiftless mutant differs from the
phase product it replaces on every clean basis state where the dropped term is
non-zero and the angle is in the non-wrapping range. -/
theorem shiftless_split_fails (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (φ : Angle) (x z : ExtReg) (w t t' : ℕ) (b : qs.Basis)
    (hw : w < x.width) (ht : w + 1 ≤ t) (hxcap : t - w ≤ x.capacity) (hzcap : t - z.width ≤ z.capacity)
    (hxcap' : t' - (highPart x w).width ≤ x.capacity) (hzcap' : t' - z.width ≤ z.capacity)
    (hd : ExtReg.OwnedDisjoint x z) (hb : Clean x z b)
    (h0 : 0 < |(φ : ℝ) * ((((2 ^ w - 1) * extToInt (highPart x w) b) * extToInt z b : ℤ) : ℝ)|)
    (h2 : |(φ : ℝ) * ((((2 ^ w - 1) * extToInt (highPart x w) b) * extToInt z b : ℤ) : ℝ)| < 2) :
    qs.eval (shiftlessSplit .none φ x z w t t') (qs.ket b) ≠
      qs.eval (Gate.SignedPhaseProd φ x z) (qs.ket b) := by
  rw [shiftlessSplit_ket qs φ x z w t t' b (by omega) ht hxcap hzcap hxcap' hzcap' hd hb,
    PhaseSemantics.eval_SignedPhaseProd_ket]
  intro h
  have hk := qs.ket_ne_zero b
  have hc := smul_left_injective ℂ hk h
  refine phaseFactor_ne φ (extToInt x b) _ (extToInt z b) ?_ ?_ hc.symm
  · rw [extToInt_split x w hw b]; convert h0 using 4; ring
  · rw [extToInt_split x w hw b]; convert h2 using 4; ring

end Balanced
end Shor
