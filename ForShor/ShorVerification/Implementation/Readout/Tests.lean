import ForShor.ShorVerification.Implementation.Readout.Main

/-!
# Readout: tests of the semiclassical readout statement

* `readoutOfRecord_*`: the little-endian reading on concrete records (slot `0`
  is the least significant bit: `[false, true]` reads `2`, not `1`), and
  `readoutOfRecord_testBit_example` for the general bit law.
* `ffAngle_consistent_*`: `ffAngle` agrees on concrete records with the
  form the equivalence proof derives, `ffAngle j rec = -(readoutOfRecord rec)/2^j`.
* `eq_iqft_m1`, `eq_iqft_m2`: the theorem at exponent widths `m = 1` and
  `m = 2`, record by record: the probability of each record equals the
  coherent probability of the outcome it reads.
* `branch_state_m2_record_10`: the state-level sign pin at `m = 2`: the branch
  at record `[true, false]` has coefficient `-i` on `|a⟩` (a flipped `ffAngle`
  sign would give `+i`).
* `hyps_satisfiable`: the ket hypotheses of `semiclassical_eq_iqft` hold for a
  concrete choice of registers and initial ket (non-vacuity).

The endianness-discrimination check (a reversed reading of the record gives a
different distribution) is a numeric computation and lives outside Lean.
-/

namespace Shor
namespace ReadoutTests

open MeasureClass

theorem readoutOfRecord_nil : readoutOfRecord [] = 0 := rfl
theorem readoutOfRecord_false_true : readoutOfRecord [false, true] = 2 := rfl
theorem readoutOfRecord_true_false : readoutOfRecord [true, false] = 1 := rfl
theorem readoutOfRecord_101 : readoutOfRecord [true, false, true] = 5 := rfl
theorem readoutOfRecord_0011 : readoutOfRecord [false, false, true, true] = 12 := rfl

/-- The bit law on a concrete record: bit `1` of `[false, true, true]` is slot `1`. -/
theorem readoutOfRecord_testBit_example :
    (readoutOfRecord [false, true, true]).testBit 1 = true ∧
    (readoutOfRecord [false, true, true]).testBit 0 = false ∧
    (readoutOfRecord [false, true, true]).testBit 5 = false := by
  simp only [readoutOfRecord_testBit]
  decide

theorem ffAngle_consistent_2 :
    ffAngle 2 [true, false] = -((readoutOfRecord [true, false] : ℚ) / 2 ^ 2) ∧
    ffAngle 2 [true, false] = -1 / 4 :=
  ⟨ffAngle_eq_neg_readout_div 2 _ rfl, by norm_num [ffAngle, Finset.sum_range_succ]⟩

theorem ffAngle_consistent_3 :
    ffAngle 3 [true, true, false] = -((readoutOfRecord [true, true, false] : ℚ) / 2 ^ 3) ∧
    ffAngle 3 [true, true, false] = -3 / 8 :=
  ⟨ffAngle_eq_neg_readout_div 3 _ rfl, by norm_num [ffAngle, Finset.sum_range_succ]⟩

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  [LowerGateClass qs] [MeasureClass qs]

/-- **`m = 1`.** One round (multiplier `a`): outcome `b` has the probability of
reading `o = b` from the one-qubit exponent register after the coherent
readout. -/
theorem eq_iqft_m1
    (a N : ℕ) (x : ExtReg) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hm : regSize x.active = 1)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N)
    (hc : c ∉ data.qubits) (hxdata : Disjoint x.active data)
    (hx0 : RegEncoding.toNat x.active b₀ = 0) (hdata1 : RegEncoding.toNat data b₀ = 1)
    (hc0 : RegEncoding.bit c b₀ = false) (b : Bool) :
    recordProb ((semiclassicalIdeal a N 1 data c).eval (MState.init (qs.ket b₀))) [b]
      = probMeas x.active (if b then 1 else 0)
          (qs.eval (H_reg x.active ;; modExpIdeal' qs a N x.active data ;; IQFT x)
            (qs.ket b₀)) := by
  have h := semiclassical_recordProb_eq a N x data c b₀ hN hNdata ha hc hxdata hx0 hdata1 hc0
    [b] (by simp [hm])
  rw [hm] at h
  rw [h]
  cases b <;> rfl

/-- **`m = 2`.** Two rounds (multipliers `a^2`, then `a`): the record
`[b0, b1]` has the probability of reading `o = b0 + 2·b1` from the two-qubit
exponent register after the coherent readout. -/
theorem eq_iqft_m2
    (a N : ℕ) (x : ExtReg) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hm : regSize x.active = 2)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N)
    (hc : c ∉ data.qubits) (hxdata : Disjoint x.active data)
    (hx0 : RegEncoding.toNat x.active b₀ = 0) (hdata1 : RegEncoding.toNat data b₀ = 1)
    (hc0 : RegEncoding.bit c b₀ = false) (b0 b1 : Bool) :
    recordProb ((semiclassicalIdeal a N 2 data c).eval (MState.init (qs.ket b₀))) [b0, b1]
      = probMeas x.active ((if b0 then 1 else 0) + 2 * (if b1 then 1 else 0))
          (qs.eval (H_reg x.active ;; modExpIdeal' qs a N x.active data ;; IQFT x)
            (qs.ket b₀)) := by
  have h := semiclassical_recordProb_eq a N x data c b₀ hN hNdata ha hc hxdata hx0 hdata1 hc0
    [b0, b1] (by simp [hm])
  rw [hm] at h
  rw [h]
  cases b0 <;> cases b1 <;> rfl

omit [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
/-- Non-vacuity: with exponent register on qubits `[0, 1]`, data on `[2, 3]`
and control `c = 4`, the ket `|data = 1⟩` built from the all-zero ket meets
every register and ket hypothesis of `semiclassical_eq_iqft`. -/
theorem hyps_satisfiable :
    let x : Reg := ⟨[0, 1], by decide⟩
    let data : Reg := ⟨[2, 3], by decide⟩
    let b₀ : qs.Basis := RegEncoding.writeNat data 1 RegEncoding.zero
    (4 : ℕ) ∉ data.qubits ∧ Disjoint x data ∧ 1 < 3 ∧ 3 ≤ ASize data ∧
    RegEncoding.toNat x b₀ = 0 ∧ RegEncoding.toNat data b₀ = 1 ∧
    RegEncoding.bit 4 b₀ = false := by
  intro x data b₀
  have h4 : (4 : ℕ) ∉ data.qubits := by decide
  have hdisj : Disjoint x data := by
    simp [Disjoint, x, data]
  have hsize : 3 ≤ ASize data := by decide
  refine ⟨h4, hdisj, by norm_num, hsize, ?_, ?_, ?_⟩
  · rw [toNat_left_write_right x data hdisj]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < regSize x
    · rw [← RegEncoding.bit_eq_testBit_toNat x _ ⟨i, hi⟩, RegEncoding.bit_zero]
      simp
    · have hlt := RegEncoding.toNat_lt_ASize x (RegEncoding.zero : qs.Basis)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt
        (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi)))]
      simp
  · exact RegEncoding.toNat_writeNat_of_lt _ _ _ (by decide)
  · rw [RegEncoding.bit_writeNat_out _ _ _ _ h4, RegEncoding.bit_zero]

/-- **Sign pin, `m = 2`.** The branch at record `[true, false]` (reading
`o = 1`) is `(1/4)(|1⟩ - i|a⟩ - |a²⟩ + i|a³⟩)` on the data register. The
coefficient of `|a⟩` is `-i = exp(-2πi/4)`; with the feed-forward phase of the
opposite sign it would be `+i`, so this test fails for a flipped `ffAngle`
(unlike the distribution-level statement). -/
theorem branch_state_m2_record_10
    (a N : ℕ) (x : ExtReg) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hm : regSize x.active = 2)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N)
    (hc : c ∉ data.qubits)
    (hdata1 : RegEncoding.toNat data b₀ = 1) (hc0 : RegEncoding.bit c b₀ = false) :
    (semiclassicalIdeal a N 2 data c).eval (MState.init (qs.ket b₀)) [true, false]
      = (1 / 4 : ℂ) • (qs.ket (RegEncoding.writeNat data (a ^ 0 % N) b₀)
          + (-Complex.I) • qs.ket (RegEncoding.writeNat data (a ^ 1 % N) b₀)
          + (-1 : ℂ) • qs.ket (RegEncoding.writeNat data (a ^ 2 % N) b₀)
          + Complex.I • qs.ket (RegEncoding.writeNat data (a ^ 3 % N) b₀)) := by
  have h := semiclassical_branch_state a N x data c b₀ hN hNdata ha hc hdata1 hc0
    [true, false] (by simp [hm])
  rw [hm] at h
  rw [h]
  have e1 : Complex.exp (-(2 * Real.pi * Complex.I * (((readoutOfRecord [true, false] : ℕ) : ℂ)
      * ((1 : ℕ) : ℂ)) / 2 ^ 2)) = -Complex.I := by
    rw [show readoutOfRecord [true, false] = 1 from rfl,
      show -(2 * (Real.pi : ℂ) * Complex.I * (((1 : ℕ) : ℂ) * ((1 : ℕ) : ℂ)) / 2 ^ 2)
        = -((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have e2 : Complex.exp (-(2 * Real.pi * Complex.I * (((readoutOfRecord [true, false] : ℕ) : ℂ)
      * ((2 : ℕ) : ℂ)) / 2 ^ 2)) = -1 := by
    rw [show readoutOfRecord [true, false] = 1 from rfl,
      show -(2 * (Real.pi : ℂ) * Complex.I * (((1 : ℕ) : ℂ) * ((2 : ℕ) : ℂ)) / 2 ^ 2)
        = -((Real.pi : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have e3 : Complex.exp (-(2 * Real.pi * Complex.I * (((readoutOfRecord [true, false] : ℕ) : ℂ)
      * ((3 : ℕ) : ℂ)) / 2 ^ 2)) = Complex.I := by
    rw [show readoutOfRecord [true, false] = 1 from rfl,
      show -(2 * (Real.pi : ℂ) * Complex.I * (((1 : ℕ) : ℂ) * ((3 : ℕ) : ℂ)) / 2 ^ 2)
        = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I + (-1 : ℤ) * (2 * Real.pi * Complex.I) by
        push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have e0 : Complex.exp (-(2 * Real.pi * Complex.I * (((readoutOfRecord [true, false] : ℕ) : ℂ)
      * ((0 : ℕ) : ℂ)) / 2 ^ 2)) = 1 := by simp
  simp only [show (2 : ℕ) ^ 2 = 4 from rfl, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add]
  rw [e0, e1, e2, e3, one_smul]
  norm_num

end ReadoutTests
end Shor
