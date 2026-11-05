import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Provider.Weights.Projective

/-!
# Unreduced fraction bounds

Defines `RawBound B q`, recording an unreduced signed fraction for `q` with
bounded numerator and denominator, and proves it is stable under products,
sums, differences, quotients, powers and finite sums and products
(`rawBound_mul`, `rawBound_add`, `rawBound_list_sum`). These feed conditional
bounds for the executable weights (`finiteWeightExec_rawBound`,
`infinityWeightExec_rawBound`).
-/

namespace Paper.A4RationalBounds

/-- `RawBound B q` records an unreduced signed fraction for `q` whose
numerator magnitude and denominator magnitude are both at most `B`. -/
def RawBound (B : Nat) (q : ℚ) : Prop :=
  ∃ a b : ℤ, b ≠ 0 ∧ a.natAbs ≤ B ∧ b.natAbs ≤ B ∧
    q = (a : ℚ) / (b : ℚ)

def listProduct {α : Type} (xs : List α) (f : α → ℚ) : ℚ :=
  (xs.map f).prod

theorem rat_num_den_rawBound (q : ℚ) :
    RawBound (max q.num.natAbs q.den) q := by
  refine ⟨q.num, q.den, ?_, le_max_left _ _, ?_, ?_⟩
  · exact_mod_cast q.den_ne_zero
  · exact le_max_right _ _
  · calc
      q = mkRat q.num q.den := (Rat.mkRat_self q).symm
      _ = (q.num : ℚ) / (q.den : ℚ) := Rat.mkRat_eq_div _ _
      _ = (q.num : ℚ) / ((q.den : ℤ) : ℚ) := by simp

theorem rawBound_mul {B C : Nat} {q r : ℚ}
    (hq : RawBound B q) (hr : RawBound C r) :
    RawBound (B * C) (q * r) := by
  rcases hq with ⟨a, b, hb, haN, hbN, hq⟩
  rcases hr with ⟨c, d, hd, hcN, hdN, hr⟩
  refine ⟨a * c, b * d, mul_ne_zero hb hd, ?_, ?_, ?_⟩
  · rw [Int.natAbs_mul]
    exact Nat.mul_le_mul haN hcN
  · rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hbN hdN
  · rw [hq, hr]
    field_simp [Int.cast_ne_zero.mpr hb, Int.cast_ne_zero.mpr hd] <;> push_cast <;> ring

theorem rawBound_add {B C : Nat} {q r : ℚ}
    (hq : RawBound B q) (hr : RawBound C r) :
    RawBound (2 * (B * C)) (q + r) := by
  rcases hq with ⟨a, b, hb, haN, hbN, hq⟩
  rcases hr with ⟨c, d, hd, hcN, hdN, hr⟩
  refine ⟨a * d + c * b, b * d, mul_ne_zero hb hd, ?_, ?_, ?_⟩
  · calc
      (a * d + c * b).natAbs ≤ (a * d).natAbs + (c * b).natAbs := Int.natAbs_add_le _ _
      _ = a.natAbs * d.natAbs + c.natAbs * b.natAbs := by rw [Int.natAbs_mul, Int.natAbs_mul]
      _ ≤ B * C + C * B := Nat.add_le_add (Nat.mul_le_mul haN hdN) (Nat.mul_le_mul hcN hbN)
      _ = 2 * (B * C) := by ring
  · rw [Int.natAbs_mul]
    calc
      b.natAbs * d.natAbs ≤ B * C := Nat.mul_le_mul hbN hdN
      _ ≤ 2 * (B * C) := Nat.le_mul_of_pos_left _ (by omega)
  · rw [hq, hr]
    field_simp [Int.cast_ne_zero.mpr hb, Int.cast_ne_zero.mpr hd] <;> push_cast <;> ring

theorem rawBound_sub {B C : Nat} {q r : ℚ}
    (hq : RawBound B q) (hr : RawBound C r) :
    RawBound (2 * (B * C)) (q - r) := by
  rw [sub_eq_add_neg]
  apply rawBound_add hq
  rcases hr with ⟨a, b, hb, haN, hbN, hr⟩
  refine ⟨-a, b, hb, ?_, hbN, ?_⟩
  · simpa using haN
  · rw [hr]
    simp [neg_div]

theorem rawBound_div {B C : Nat} {q r : ℚ}
    (hq : RawBound B q) (hr : RawBound C r) (hr0 : r ≠ 0) :
    RawBound (B * C) (q / r) := by
  rcases hq with ⟨a, b, hb, haN, hbN, hq⟩
  rcases hr with ⟨c, d, hd, hcN, hdN, hr⟩
  have hc : c ≠ 0 := by
    intro hcz
    apply hr0
    rw [hr, hcz]
    simp
  refine ⟨a * d, b * c, mul_ne_zero hb hc, ?_, ?_, ?_⟩
  · rw [Int.natAbs_mul]
    exact Nat.mul_le_mul haN hdN
  · rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hbN hcN
  · rw [hq, hr]
    field_simp [Int.cast_ne_zero.mpr hb, Int.cast_ne_zero.mpr hc,
      Int.cast_ne_zero.mpr hd] <;> push_cast <;> ring

/-- A product of `m` rational terms has an unreduced numerator and denominator
bounded by `B^m`, provided each factor has a raw fraction bounded by `B`. -/
theorem rawBound_list_product {α : Type} (xs : List α) (f : α → ℚ) {B : Nat}
    (hf : ∀ x ∈ xs, RawBound B (f x)) :
    RawBound (B ^ xs.length) (listProduct xs f) := by
  induction xs with
  | nil =>
      refine ⟨1, 1, by norm_num, ?_, ?_, ?_⟩
      · simpa using hB
      · simpa using hB
      · simp [listProduct]
  | cons x xs ih =>
      have hx : RawBound B (f x) := hf x (by simp)
      have htail : ∀ y ∈ xs, RawBound B (f y) := by
        intro y hy
        exact hf y (by simp [hy])
      have hprod := rawBound_mul hx (ih htail)
      simpa [listProduct, List.map_cons, List.prod_cons, List.length_cons,
        Nat.pow_succ, Nat.mul_comm] using hprod

/-- An `m`-term rational sum has an unreduced representation bounded by
`(2B)^m`; this deliberately coarse common-denominator bound is linear in `m`
when expressed as a bit length. -/
theorem rawBound_list_sum {α : Type} (xs : List α) (f : α → ℚ) {B : Nat}
    (hf : ∀ x ∈ xs, RawBound B (f x)) :
    RawBound ((2 * B) ^ xs.length) ((xs.map f).sum) := by
  induction xs with
  | nil =>
      refine ⟨0, 1, by norm_num, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · simp
  | cons x xs ih =>
      have hx : RawBound B (f x) := hf x (by simp)
      have htail : ∀ y ∈ xs, RawBound B (f y) := by
        intro y hy
        exact hf y (by simp [hy])
      have hsum := rawBound_add hx (ih htail)
      simpa [List.map_cons, List.sum_cons, List.length_cons,
        Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsum

theorem rawBound_mono {B C : Nat} {q : ℚ} (hBC : B ≤ C)
    (hq : RawBound B q) : RawBound C q := by
  rcases hq with ⟨a, b, hb, haN, hbN, hq⟩
  exact ⟨a, b, hb, haN.trans hBC, hbN.trans hBC, hq⟩

theorem rawBound_pow {B : Nat} {q : ℚ} (hq : RawBound B q) (n : Nat) :
    RawBound (B ^ n) (q ^ n) := by
  induction n with
  | zero =>
      refine ⟨1, 1, by norm_num, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · simp
  | succ n ih =>
      have hp := rawBound_mul ih hq
      simpa [pow_succ, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using hp

theorem rawBound_finset_product {α : Type} (s : Finset α) (f : α → ℚ) {B : Nat}
    (hf : ∀ x ∈ s, RawBound B (f x)) :
    RawBound (B ^ s.card) (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, 1, by norm_num, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · simp
  | @insert x s hxs ih =>
      have hx := hf x (Finset.mem_insert_self ..)
      have htail : ∀ y ∈ s, RawBound B (f y) := by
        intro y hy
        exact hf y (Finset.mem_insert_of_mem hy)
      have hprod := rawBound_mul hx (ih htail)
      simpa [Finset.prod_insert, hxs, Finset.card_insert_of_notMem,
        Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hprod

theorem rawBound_finset_sum {α : Type} (s : Finset α) (f : α → ℚ) {B : Nat}
    (hf : ∀ x ∈ s, RawBound B (f x)) :
    RawBound ((2 * B) ^ s.card) (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, 1, by norm_num, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · simp
  | @insert x s hxs ih =>
      have hx := hf x (Finset.mem_insert_self ..)
      have htail : ∀ y ∈ s, RawBound B (f y) := by
        intro y hy
        exact hf y (Finset.mem_insert_of_mem hy)
      have hsum := rawBound_add hx (ih htail)
      simpa [Finset.sum_insert, hxs, Finset.card_insert_of_notMem,
        Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

/-- Conditional unreduced fraction bound for the executable finite Lagrange
weight. It needs only a common raw bound and the nonzero node gaps. -/
theorem finiteWeightExec_rawBound {d B : Nat} (v : Fin d → ℚ) (b : ℚ) (i : Fin d)
    (hb : RawBound B b) (hv : ∀ j, RawBound B (v j))
    (hgap : ∀ j ∈ (Finset.univ : Finset (Fin d)).erase i, v i ≠ v j) :
    RawBound ((4 * B ^ 4) ^ (d - 1)) (Paper.A4Exec.finiteWeightExec v b i) := by
  have hfactor : ∀ j ∈ (Finset.univ : Finset (Fin d)).erase i,
      RawBound (4 * B ^ 4) ((b - v j) / (v i - v j)) := by
    intro j hj
    have hnum := rawBound_sub hb (hv j)
    have hden := rawBound_sub (hv i) (hv j)
    have hratio := rawBound_div hnum hden (sub_ne_zero.mpr (hgap j hj))
    convert hratio using 1 <;> ring
  have hprod := rawBound_finset_product ((Finset.univ : Finset (Fin d)).erase i)
    (fun j => (b - v j) / (v i - v j)) hfactor
  have hcard : ((Finset.univ : Finset (Fin d)).erase i).card = d - 1 := by simp
  simpa [Paper.A4Exec.finiteWeightExec, hcard] using hprod

/-- Conditional unreduced fraction bound for the executable infinity residual. -/
theorem infinityWeightExec_rawBound {d B : Nat} (v : Fin d → ℚ) (b : ℚ)
    (hb : RawBound B b) (hv : ∀ j, RawBound B (v j))
    (hgap : ∀ i j : Fin d, i ≠ j → v i ≠ v j) :
    RawBound (2 * (B ^ d * ((2 * ((4 * B ^ 4) ^ (d - 1) * B ^ d)) ^ d)))
      (Paper.A4Exec.infinityWeightExec v b) := by
  let F := (4 * B ^ 4) ^ (d - 1)
  let T := F * B ^ d
  have hbpow := rawBound_pow hb d
  have hvpow : ∀ i, RawBound (B ^ d) (v i ^ d) := fun i => rawBound_pow (hv i) d
  have hterm : ∀ i, RawBound T (Paper.A4Exec.finiteWeightExec v b i * v i ^ d) := by
    intro i
    apply rawBound_mul
      (finiteWeightExec_rawBound v b i hb hv (by
        intro j hj
        exact hgap i j (Ne.symm (Finset.mem_erase.mp hj).1)))
      (hvpow i)
  have hsum := rawBound_finset_sum (Finset.univ : Finset (Fin d))
    (fun i => Paper.A4Exec.finiteWeightExec v b i * v i ^ d)
    (by intro i hi; exact hterm i)
  have hsub := rawBound_sub hbpow hsum
  simpa [Paper.A4Exec.infinityWeightExec, T, F, Nat.mul_assoc] using hsub

end Paper.A4RationalBounds
