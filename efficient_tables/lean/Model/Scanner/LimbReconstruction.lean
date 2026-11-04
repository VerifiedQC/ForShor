import Model.Scanner.ArrayScanner

/-!
# Signed limb reconstruction

Proves facts about splitting values into limbs of width `W`. Includes `magLimb_reconstruct` for magnitudes, `limbs_fits` for the limb range, and reconstruction of signed integers and rationals (`limbs_reconstruct_int`, `limbs_reconstruct_rat`).
-/

namespace Paper.SignedLimbs

theorem radix_pos (W k : Nat) : 0 < radix W k := by
  simp [radix]

theorem weighted_prefix (B m t : Nat) :
    (∑ i ∈ Finset.range t, ((m / B ^ i) % B) * B ^ i) +
      (m / B ^ t) * B ^ t = m := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ]
      have hdiv : (m / B ^ t) / B = m / B ^ (t + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ]
      have hstep : ((m / B ^ t) % B) * B ^ t +
          (m / B ^ (t + 1)) * B ^ (t + 1) =
          (m / B ^ t) * B ^ t := by
        rw [← hdiv, pow_succ]
        calc
          ((m / B ^ t) % B) * B ^ t + ((m / B ^ t) / B) * (B ^ t * B)
              = ((m / B ^ t) % B + B * ((m / B ^ t) / B)) * B ^ t := by ring
          _ = (m / B ^ t) * B ^ t := by rw [Nat.mod_add_div]
      calc
        (∑ i ∈ Finset.range t, ((m / B ^ i) % B) * B ^ i) +
            ((m / B ^ t) % B) * B ^ t +
            (m / B ^ (t + 1)) * B ^ (t + 1)
            = (∑ i ∈ Finset.range t, ((m / B ^ i) % B) * B ^ i) +
                (m / B ^ t) * B ^ t := by omega
        _ = m := ih

theorem magLimb_reconstruct (W k m : Nat) (hk : 0 < k) :
    (∑ i : Fin k, magLimb W k m i * (radix W k) ^ i.val) = m := by
  cases k with
  | zero => omega
  | succ t =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc]
      have hprefix :
          (∑ i : Fin t,
            magLimb W (t + 1) m i.castSucc *
              (radix W (t + 1)) ^ i.val) =
          ∑ i : Fin t,
            ((m / (radix W (t + 1)) ^ i.val) % (radix W (t + 1))) *
              (radix W (t + 1)) ^ i.val := by
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i.val ≠ t := by omega
        simp [magLimb, hne]
      rw [hprefix]
      rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
        ((m / (radix W (t + 1)) ^ i) % (radix W (t + 1))) *
          (radix W (t + 1)) ^ i)]
      simp only [magLimb, Fin.val_last]
      simpa using weighted_prefix (radix W (t + 1)) m t

theorem top_mag_bound (W k m : Nat) (hk : 0 < k)
    (hm : m < 2 ^ W) :
    m / (radix W k) ^ (k - 1) < 2 ^ (W - (k - 1) * (W / k)) := by
  let q := W / k
  have hkq : k * q ≤ W := by
    simpa [q, Nat.mul_comm] using Nat.div_mul_le_self W k
  have hle : (k - 1) * q ≤ W :=
    le_trans (Nat.mul_le_mul_right q (Nat.sub_le k 1)) hkq
  have hpow : 2 ^ (W - (k - 1) * q) * (radix W k) ^ (k - 1) =
      2 ^ W := by
    rw [radix, ← pow_mul, ← pow_add, Nat.mul_comm (W / k) (k - 1)]
    congr 1
    exact Nat.sub_add_cancel hle
  apply (Nat.div_lt_iff_lt_mul (pow_pos (radix_pos W k) _)).2
  rw [hpow]
  exact hm

theorem limbs_natAbs (W : Nat) {k : Nat} (hk : 0 < k)
    (n : Int) (i : Fin k) :
    (limbs W hk n i).natAbs = magLimb W k n.natAbs i := by
  unfold limbs
  split_ifs <;> simp

theorem limbs_fits (W : Nat) {k : Nat} (hk : 0 < k)
    (n : Int) (hn : n.natAbs < 2 ^ W) :
    Paper.ValueBounds.Fits (Paper.ArrayBridge.literalSourceSplit W k)
      (limbs W hk n) := by
  intro i
  rw [limbs_natAbs, Paper.ArrayBridge.literalSourceSplit_eq_explicit]
  change magLimb W k n.natAbs i <
    2 ^ (TableGeneration.RecursiveCost.phaseSplitLogicalWidth W (W / k) k i)
  unfold TableGeneration.RecursiveCost.phaseSplitLogicalWidth
  by_cases htop : i.val + 1 = k
  · rw [if_pos htop]
    have hi : i.val = k - 1 := by omega
    simp only [magLimb, if_pos htop]
    rw [hi]
    exact top_mag_bound W k n.natAbs hk hn
  · rw [if_neg htop]
    simp only [magLimb, if_neg htop]
    simpa [radix] using
      (Nat.mod_lt (n.natAbs / radix W k ^ i.val) (radix_pos W k))

theorem limbs_reconstruct_int (W : Nat) {k : Nat} (hk : 0 < k)
    (n : Int) :
    (∑ i : Fin k, limbs W hk n i * (radix W k : Int) ^ i.val) = n := by
  have hmag :
      (∑ i : Fin k, (magLimb W k n.natAbs i : Int) *
        (radix W k : Int) ^ i.val) = (n.natAbs : Int) := by
    exact_mod_cast magLimb_reconstruct W k n.natAbs hk
  calc
    (∑ i : Fin k, limbs W hk n i * (radix W k : Int) ^ i.val)
        = (if n < 0 then -1 else 1) *
          (∑ i : Fin k, (magLimb W k n.natAbs i : Int) *
            (radix W k : Int) ^ i.val) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            simp [limbs, mul_assoc]
    _ = (if n < 0 then -1 else 1) * (n.natAbs : Int) := by rw [hmag]
    _ = n := by
      by_cases hn : n < 0
      · simp [hn, Int.natCast_natAbs, abs_of_neg hn]
      · have hnonneg : 0 ≤ n := le_of_not_gt hn
        simp [hn, Int.natCast_natAbs, abs_of_nonneg hnonneg]

theorem limbs_reconstruct_rat (W : Nat) {k : Nat} (hk : 0 < k)
    (n : Int) :
    (∑ i : Fin k, (limbs W hk n i : ℚ) *
      (radix W k : ℚ) ^ i.val) = (n : ℚ) := by
  exact_mod_cast limbs_reconstruct_int W hk n

end Paper.SignedLimbs
