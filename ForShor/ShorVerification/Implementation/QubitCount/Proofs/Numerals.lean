import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Formula

/-!
# Qubit count: the 2048-bit numerals

The reference widths for every 2048-bit modulus, the budget at those widths
by kernel evaluation, and the claims.
-/

namespace Shor

/-- The standard table for `k = 2`, as a one-band policy. -/
abbrev standardPolicy2 : ShorLoweringPolicy := standardPolicy 2 (by decide)

-- The `2 ^ 2048` literal trips the default `exponentiation.threshold` of 256.
set_option exponentiation.threshold 4100 in
/-- The 2048-bit modulus `2²⁰⁴⁸ − 1` with base 2. -/
def instance2048 : ShorOrderFindingInstance :=
  ⟨2, 2 ^ 2048 - 1, by norm_num, by decide +kernel⟩

namespace QubitCount

/-! ## The budget at the 2048-bit widths -/

theorem orderFindingPeak_2048_4096 :
    Policy.orderFindingPeak standardPolicy2 4096 2048 2347 4398 = 6428 := by
  decide +kernel

theorem orderFindingPeak_2048_4095 :
    Policy.orderFindingPeak standardPolicy2 4095 2048 2347 4398 = 6428 := by
  decide +kernel

theorem orderFindingPeak_2048 {xW : ℕ} (hx : xW = 4095 ∨ xW = 4096) :
    Policy.orderFindingPeak standardPolicy2 xW 2048 2347 4398 = 6428 := by
  rcases hx with rfl | rfl
  · exact orderFindingPeak_2048_4095
  · exact orderFindingPeak_2048_4096

/-! ## The 2048-bit widths -/

section Widths

variable {N : ℕ} (hN : Is2048Bit N)
include hN

-- The `2 ^ 4097` bounds trip the default `exponentiation.threshold` of 256.
set_option exponentiation.threshold 4100 in
lemma log2_two_mul_eq : Nat.log2 (2 * N) = 2048 := by
  rw [Nat.log2_eq_log_two]
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · calc 2 ^ 2048 = 2 * 2 ^ 2047 := by norm_num
      _ ≤ 2 * N := by gcongr; exact hN.1
  · calc 2 * N < 2 * 2 ^ 2048 := by gcongr; exact hN.2
      _ = 2 ^ (2048 + 1) := by norm_num

set_option exponentiation.threshold 4100 in
lemma log2_two_mul_sq_bounds : 4095 ≤ Nat.log2 (2 * N ^ 2) ∧ Nat.log2 (2 * N ^ 2) ≤ 4096 := by
  refine ⟨?_, hN.tbits_le⟩
  rw [Nat.log2_eq_log_two]
  apply Nat.le_log_of_pow_le (by norm_num)
  calc 2 ^ 4095 = 2 * (2 ^ 2047) ^ 2 := by norm_num
    _ ≤ 2 * N ^ 2 := by gcongr; exact hN.1

set_option exponentiation.threshold 4100 in
lemma log2_succ_le : Nat.log2 (N + 1) ≤ 2048 := by
  rw [Nat.log2_eq_log_two]
  have : Nat.log 2 (N + 1) < 2049 := Nat.log_lt_of_lt_pow (by omega)
    (by calc N + 1 ≤ 2 ^ 2048 := hN.2
          _ < 2 ^ 2049 := by norm_num)
  omega

end Widths

set_option exponentiation.threshold 400 in
lemma algorithm1ExtraBitsNat_m2048 : Reference.algorithm1ExtraBitsNat Reference.m2048 = 299 := by
  have hc : Nat.clog 2 ((Reference.m2048 + 7) ^ 2) = 301 := by
    apply le_antisymm
    · rw [Nat.clog_le_iff_le_pow (by norm_num)]
      norm_num [Reference.m2048]
    · rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt (by norm_num)]
      norm_num [Reference.m2048]
  rw [Reference.algorithm1ExtraBitsNat, hc]

lemma reference_widths_2048 {inst : ShorOrderFindingInstance} (hN : Is2048Bit inst.N) :
    Reference.referenceDataWidth inst = 2048 ∧
    Reference.referenceWorkWidth inst Reference.m2048 = 2347 ∧
    Reference.referenceScratchWidth inst Reference.m2048 = 4398 ∧
    (Reference.referenceXWidth inst = 4095 ∨ Reference.referenceXWidth inst = 4096) := by
  have hd : Reference.referenceDataWidth inst = 2048 := log2_two_mul_eq hN
  have hw : Reference.referenceWorkWidth inst Reference.m2048 = 2347 := by
    rw [Reference.referenceWorkWidth, hd, algorithm1ExtraBitsNat_m2048]
  have hx := log2_two_mul_sq_bounds hN
  refine ⟨hd, hw, ?_, by unfold Reference.referenceXWidth; omega⟩
  rw [Reference.referenceScratchWidth, hd, hw]
  have := log2_succ_le hN
  omega

/-! ## The 2048-bit numbers -/

/-- For every 2048-bit modulus, the reference circuit from the standard `k = 2`
table at `m2048` has registers data 2048, work 2347 and scratch 4398, an exponent
register of 4095 or 4096 qubits, and peaks, scratch included, at 19,319 qubits with
4096 exponent qubits and 19,318 with 4095; from an empty start it never exceeds
19,319. -/
theorem reference2048Peak (inst : ShorOrderFindingInstance) (hN : Is2048Bit inst.N) :
    let layout := Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048
    let L0 := orderFindingBaseSet layout.x layout.data layout.work layout.scratch layout.flag
    let g := Reference.referenceShorCircuit standardPolicy2 inst Reference.m2048
    Reference.referenceDataWidth inst = 2048 ∧
    Reference.referenceWorkWidth inst Reference.m2048 = 2347 ∧
    Reference.referenceScratchWidth inst Reference.m2048 = 4398 ∧
    (Reference.referenceXWidth inst = 4095 ∨ Reference.referenceXWidth inst = 4096) ∧
    (Reference.referenceXWidth inst = 4096 → g.peakQubits L0 = 19319) ∧
    (Reference.referenceXWidth inst = 4095 → g.peakQubits L0 = 19318) ∧
    g.peakQubits ∅ ≤ 19319 := by
  dsimp only
  obtain ⟨hd, hw, hs, hx⟩ := reference_widths_2048 hN
  have hp := referencePeakFormula standardPolicy2
    (standardPolicy_admissible 2 (by decide)) inst Reference.m2048
  dsimp only at hp
  rw [Policy.orderFindingQubits, hd, hw, hs, orderFindingPeak_2048 hx] at hp
  have hbase : Reference.referenceXWidth inst + (2048 + 1) + 2347 + 4398 + 1
      = Reference.referenceXWidth inst + 8795 := by
    omega
  rw [hbase] at hp
  have hmono := (mono scratch (Reference.referenceShorCircuit standardPolicy2 inst Reference.m2048)
    true (Finset.empty_subset (orderFindingBaseSet
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).x
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).data
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).work
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).scratch
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).flag))).2
  simp only [LowGate.peakQubits] at hp hmono ⊢
  refine ⟨hd, hw, hs, hx, fun h => by rw [hp, h], fun h => by rw [hp, h], ?_⟩
  omega

-- The `2 ^ 4097` bounds trip the default `exponentiation.threshold` of 256.
set_option exponentiation.threshold 4200 in
/-- For `N = 2²⁰⁴⁸ − 1` the peak, scratch included, is exactly 19,319 qubits. -/
theorem reference2048PeakExample :
    let layout := Reference.allocateReferenceLayout standardPolicy2 instance2048 Reference.m2048
    (Reference.referenceShorCircuit standardPolicy2 instance2048 Reference.m2048).peakQubits
        (orderFindingBaseSet layout.x layout.data layout.work layout.scratch layout.flag)
      = 19319 := by
  have hN : Is2048Bit instance2048.N := by
    show 2 ^ 2047 ≤ 2 ^ 2048 - 1 ∧ 2 ^ 2048 - 1 < 2 ^ 2048
    constructor <;> norm_num
  have hx : Reference.referenceXWidth instance2048 = 4096 := by
    show Nat.log2 (2 * (2 ^ 2048 - 1) ^ 2) = 4096
    rw [Nat.log2_eq_log_two]
    apply Nat.log_eq_of_pow_le_of_lt_pow <;> norm_num
  exact (reference2048Peak instance2048 hN).2.2.2.2.1 hx

end QubitCount
end Shor
