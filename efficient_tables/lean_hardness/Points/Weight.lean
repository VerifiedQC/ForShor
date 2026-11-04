import Mathlib.Tactic

/-!
# Signed-binary weight: the arithmetic of the reduction

* `W1 x`: `x` is `0` or a signed power of two; `W2 x`: a sum of two `W1` numbers.
* `D1`, `D2`: the same over the dyadic rationals (`ℚ`, integer exponents), and `w_of_dyadic`:
  an integer equal to a `D1`/`D2` number times `2^t` is `W1`/`W2`.
* Non-adjacent forms (`Sparse` lists: signed powers with exponents at least 2 apart) are unique
  (`sparse_unique`); hence `Σ_{Pos} 8^i − Σ_{Neg} 8^i` is `W2` only when `|Pos| + |Neg| ≤ 2`, and
  `W1` only when `|Pos| + |Neg| ≤ 1` (`oct_W2`, `oct_W1`).
-/

namespace Pts

/-- `0` or a signed power of two. -/
def W1 (x : ℤ) : Prop := x = 0 ∨ ∃ (s : ℤ) (p : ℕ), (s = 1 ∨ s = -1) ∧ x = s * 2 ^ p

/-- A sum of two `W1` numbers. -/
def W2 (x : ℤ) : Prop := ∃ a b, W1 a ∧ W1 b ∧ x = a + b

lemma W1.W2 {x : ℤ} (h : W1 x) : W2 x := ⟨x, 0, h, Or.inl rfl, by ring⟩

/-! ### Sparse (non-adjacent) forms -/

/-- A list of signed powers `(s, e)` with `s = ±1` and exponents increasing by at least 2. -/
def Sparse (L : List (ℤ × ℕ)) : Prop :=
  L.Pairwise (fun a b => a.2 + 2 ≤ b.2) ∧ ∀ x ∈ L, x.1 = 1 ∨ x.1 = -1

def value (L : List (ℤ × ℕ)) : ℤ := (L.map fun x => x.1 * 2 ^ x.2).sum

@[simp] lemma value_nil : value [] = 0 := rfl
@[simp] lemma value_cons (x : ℤ × ℕ) (L : List (ℤ × ℕ)) :
    value (x :: L) = x.1 * 2 ^ x.2 + value L := by simp [value]

lemma Sparse.tail {x : ℤ × ℕ} {L : List (ℤ × ℕ)} (h : Sparse (x :: L)) : Sparse L :=
  ⟨(List.pairwise_cons.mp h.1).2, fun y hy => h.2 y (List.mem_cons_of_mem _ hy)⟩

/-- All exponents of the tail of a sparse list are at least `e + 2`. -/
lemma Sparse.tail_ge {x : ℤ × ℕ} {L : List (ℤ × ℕ)} (h : Sparse (x :: L)) :
    ∀ y ∈ L, x.2 + 2 ≤ y.2 :=
  (List.pairwise_cons.mp h.1).1

lemma dvd_value {L : List (ℤ × ℕ)} {N : ℕ} (h : ∀ y ∈ L, N ≤ y.2) : (2 : ℤ) ^ N ∣ value L := by
  induction L with
  | nil => simp
  | cons y L ih =>
    rw [value_cons]
    refine dvd_add (Dvd.dvd.mul_left (pow_dvd_pow 2 (h y (by simp))) _)
      (ih fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- The head of a sparse list is determined modulo `2^(e+2)`. -/
lemma value_cons_mod {x : ℤ × ℕ} {L : List (ℤ × ℕ)} (h : Sparse (x :: L)) :
    ∃ r, value (x :: L) = x.1 * 2 ^ x.2 + 2 ^ (x.2 + 2) * r := by
  obtain ⟨r, hr⟩ := dvd_value h.tail_ge
  exact ⟨r, by rw [value_cons, hr]⟩

lemma sparse_cons_ne_zero {x : ℤ × ℕ} {L : List (ℤ × ℕ)} (h : Sparse (x :: L)) :
    value (x :: L) ≠ 0 := by
  obtain ⟨r, hr⟩ := value_cons_mod h
  rw [hr]
  intro h0
  have hs := h.2 x (by simp)
  have : (2 : ℤ) ^ x.2 * (x.1 + 4 * r) = 0 := by rw [← h0]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 (by positivity)
  · rcases hs with hs | hs <;> rw [hs] at h1 <;> omega

/-- `2^e · s + 2^(e+2) · r = 2^f · t + 2^(f+2) · r'` with `s, t = ±1` forces `e = f`, `s = t`. -/
lemma head_unique {s t : ℤ} {e f : ℕ} {r r' : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (h : s * 2 ^ e + 2 ^ (e + 2) * r = t * 2 ^ f + 2 ^ (f + 2) * r') : e = f ∧ s = t := by
  have key : ∀ {e f : ℕ} {s t r r' : ℤ}, (s = 1 ∨ s = -1) → (t = 1 ∨ t = -1) →
      s * 2 ^ e + 2 ^ (e + 2) * r = t * 2 ^ f + 2 ^ (f + 2) * r' → e < f → False := by
    intro e f s t r r' hs ht h hlt
    obtain ⟨d, rfl⟩ : ∃ d, f = e + 1 + d := ⟨f - e - 1, by omega⟩
    have h2 : (2 : ℤ) ^ e * (s + 4 * r) = 2 ^ e * (2 * (t * 2 ^ d + 4 * 2 ^ d * r')) := by
      rw [show (2 : ℤ) ^ e * (s + 4 * r) = s * 2 ^ e + 2 ^ (e + 2) * r by ring, h]; ring
    have h3 := mul_left_cancel₀ (by positivity : (2 : ℤ) ^ e ≠ 0) h2
    rcases hs with rfl | rfl <;> omega
  rcases lt_trichotomy e f with hlt | rfl | hgt
  · exact (key hs ht h hlt).elim
  · refine ⟨rfl, ?_⟩
    have h2 : (2 : ℤ) ^ e * (s + 4 * r) = 2 ^ e * (t + 4 * r') := by
      rw [show (2 : ℤ) ^ e * (s + 4 * r) = s * 2 ^ e + 2 ^ (e + 2) * r by ring, h]; ring
    have h3 := mul_left_cancel₀ (by positivity : (2 : ℤ) ^ e ≠ 0) h2
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> omega
  · exact (key ht hs h.symm hgt).elim

/-- **Uniqueness of the non-adjacent form.** -/
theorem sparse_unique : ∀ {L M : List (ℤ × ℕ)}, Sparse L → Sparse M → value L = value M → L = M
  | [], [], _, _, _ => rfl
  | [], y :: M, _, hM, h => absurd h.symm (sparse_cons_ne_zero hM)
  | x :: L, [], hL, _, h => absurd h (sparse_cons_ne_zero hL)
  | x :: L, y :: M, hL, hM, h => by
    obtain ⟨r, hr⟩ := value_cons_mod hL
    obtain ⟨r', hr'⟩ := value_cons_mod hM
    have ⟨he, hs⟩ := head_unique (hL.2 x (by simp)) (hM.2 y (by simp)) (hr.symm.trans (h.trans hr'))
    have hxy : x = y := Prod.ext hs he
    subst hxy
    rw [value_cons, value_cons] at h
    rw [sparse_unique hL.tail hM.tail (by linarith)]

lemma sparse_length_eq {L M : List (ℤ × ℕ)} (hL : Sparse L) (hM : Sparse M)
    (h : value L = value M) : L.length = M.length := by rw [sparse_unique hL hM h]

/-! ### `W1`/`W2` numbers have short sparse forms -/

lemma W1_sparse {x : ℤ} (h : W1 x) : ∃ L, Sparse L ∧ value L = x ∧ L.length ≤ 1 := by
  rcases h with rfl | ⟨s, p, hs, rfl⟩
  · exact ⟨[], ⟨List.Pairwise.nil, by simp⟩, rfl, by simp⟩
  · exact ⟨[(s, p)], ⟨List.pairwise_singleton _ _, by simpa using hs⟩, by simp, by simp⟩

lemma W2_sparse {x : ℤ} (h : W2 x) : ∃ L, Sparse L ∧ value L = x ∧ L.length ≤ 2 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  rcases ha with rfl | ⟨s, p, hs, rfl⟩
  · obtain ⟨L, h1, h2, h3⟩ := W1_sparse hb; exact ⟨L, h1, by simp [h2], by omega⟩
  rcases hb with rfl | ⟨t, q, ht, rfl⟩
  · exact ⟨[(s, p)], ⟨List.pairwise_singleton _ _, by simpa using hs⟩, by simp, by simp⟩
  -- two signed powers: order them, then merge if they are adjacent
  wlog hpq : p ≤ q generalizing s t p q
  · obtain ⟨L, h1, h2, h3⟩ := this t q ht s p hs (by omega)
    exact ⟨L, h1, by rw [h2]; ring, h3⟩
  rcases Nat.lt_or_ge (p + 1) q with hgap | hle
  · exact ⟨[(s, p), (t, q)], ⟨by simp [List.pairwise_pair]; omega, by simp [hs, ht]⟩, by simp, by simp⟩
  rcases Nat.eq_or_lt_of_le hpq with rfl | hlt
  · -- p = q
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact ⟨[(1, p + 1)], ⟨List.pairwise_singleton _ _, by simp⟩, by simp [pow_succ]; ring, by simp⟩
    · exact ⟨[], ⟨List.Pairwise.nil, by simp⟩, by simp, by simp⟩
    · exact ⟨[], ⟨List.Pairwise.nil, by simp⟩, by simp, by simp⟩
    · exact ⟨[(-1, p + 1)], ⟨List.pairwise_singleton _ _, by simp⟩, by simp [pow_succ]; ring, by simp⟩
  · -- q = p + 1
    obtain rfl : q = p + 1 := by omega
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact ⟨[(-1, p), (1, p + 2)], ⟨by simp [List.pairwise_pair], by simp⟩, by simp [pow_succ]; ring,
        by simp⟩
    · exact ⟨[(-1, p)], ⟨List.pairwise_singleton _ _, by simp⟩, by simp [pow_succ]; ring, by simp⟩
    · exact ⟨[(1, p)], ⟨List.pairwise_singleton _ _, by simp⟩, by simp [pow_succ]; ring, by simp⟩
    · exact ⟨[(1, p), (-1, p + 2)], ⟨by simp [List.pairwise_pair], by simp⟩, by simp [pow_succ]; ring,
        by simp⟩

/-! ### Signed sums of powers of eight -/

/-- `Σ_{Pos} 8^i − Σ_{Neg} 8^i`. -/
def oct (Pos Neg : Finset ℕ) : ℤ := (∑ i ∈ Pos, (8 : ℤ) ^ i) - ∑ i ∈ Neg, (8 : ℤ) ^ i

/-- The sparse form of `oct Pos Neg` for disjoint `Pos`, `Neg`. -/
def octList (Pos Neg : Finset ℕ) : List (ℤ × ℕ) :=
  ((Pos ∪ Neg).sort).map fun i => (if i ∈ Pos then 1 else -1, 3 * i)

lemma octList_sparse (Pos Neg : Finset ℕ) : Sparse (octList Pos Neg) := by
  refine ⟨?_, fun x hx => ?_⟩
  · unfold octList
    rw [List.pairwise_map]
    have h1 : ((Pos ∪ Neg).sort).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
    have h2 : ((Pos ∪ Neg).sort).Pairwise (· ≠ ·) := List.nodup_iff_pairwise_ne.mp (Finset.sort_nodup (Pos ∪ Neg) (· ≤ ·))
    refine (h1.and h2).imp fun {a b} hab => ?_
    simp only; omega
  · simp only [octList, List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    by_cases h : i ∈ Pos <;> simp [h]

lemma octList_length (Pos Neg : Finset ℕ) : (octList Pos Neg).length = (Pos ∪ Neg).card := by
  simp [octList]

lemma value_octList {Pos Neg : Finset ℕ} (hd : Disjoint Pos Neg) :
    value (octList Pos Neg) = oct Pos Neg := by
  unfold value octList oct
  rw [List.map_map]
  have : (((Pos ∪ Neg).sort (· ≤ ·)).map ((fun x : ℤ × ℕ => x.1 * 2 ^ x.2) ∘
      fun i => (if i ∈ Pos then (1 : ℤ) else -1, 3 * i))).sum =
      ∑ i ∈ Pos ∪ Neg, (if i ∈ Pos then (1 : ℤ) else -1) * 8 ^ i := by
    rw [Finset.sum_eq_multiset_sum, ← Finset.sort_eq (Pos ∪ Neg) (· ≤ ·), Multiset.map_coe,
      Multiset.sum_coe]
    congr 1
    apply List.map_congr_left
    intro i _
    simp [pow_mul]
  rw [this, Finset.sum_union hd]
  have e1 : ∑ i ∈ Pos, (if i ∈ Pos then (1 : ℤ) else -1) * 8 ^ i = ∑ i ∈ Pos, (8 : ℤ) ^ i :=
    Finset.sum_congr rfl fun i hi => by rw [if_pos hi, one_mul]
  have e2 : ∑ i ∈ Neg, (if i ∈ Pos then (1 : ℤ) else -1) * 8 ^ i = ∑ i ∈ Neg, -(8 : ℤ) ^ i :=
    Finset.sum_congr rfl fun i hi => by rw [if_neg (Finset.disjoint_right.mp hd hi), neg_one_mul]
  rw [e1, e2, Finset.sum_neg_distrib]; ring

theorem oct_W2 {Pos Neg : Finset ℕ} (hd : Disjoint Pos Neg) (h : W2 (oct Pos Neg)) :
    (Pos ∪ Neg).card ≤ 2 := by
  obtain ⟨L, hL, hv, hl⟩ := W2_sparse h
  have := sparse_length_eq (octList_sparse Pos Neg) hL (by rw [value_octList hd, hv])
  rw [octList_length] at this; omega

theorem oct_W1 {Pos Neg : Finset ℕ} (hd : Disjoint Pos Neg) (h : W1 (oct Pos Neg)) :
    (Pos ∪ Neg).card ≤ 1 := by
  obtain ⟨L, hL, hv, hl⟩ := W1_sparse h
  have := sparse_length_eq (octList_sparse Pos Neg) hL (by rw [value_octList hd, hv])
  rw [octList_length] at this; omega

/-! ### Dyadic coefficients -/

/-- `0` or a signed power of two with an integer exponent. -/
def D1 (q : ℚ) : Prop := q = 0 ∨ ∃ (s : ℤ) (e : ℤ), (s = 1 ∨ s = -1) ∧ q = s * 2 ^ e

def D2 (q : ℚ) : Prop := ∃ a b, D1 a ∧ D1 b ∧ q = a + b

lemma D1.mul {a b : ℚ} (ha : D1 a) (hb : D1 b) : D1 (a * b) := by
  rcases ha with rfl | ⟨s, e, hs, rfl⟩
  · left; ring
  rcases hb with rfl | ⟨t, f, ht, rfl⟩
  · left; ring
  right
  refine ⟨s * t, e + f, by rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp, ?_⟩
  rw [zpow_add₀ (by norm_num)]; push_cast; ring

lemma D1.D2 {a : ℚ} (h : D1 a) : D2 a := ⟨a, 0, h, Or.inl rfl, by ring⟩

lemma D2.mul_D1 {a b : ℚ} (ha : D2 a) (hb : D1 b) : D2 (a * b) := by
  obtain ⟨x, y, hx, hy, rfl⟩ := ha
  exact ⟨x * b, y * b, hx.mul hb, hy.mul hb, by ring⟩

lemma D1_one : D1 1 := Or.inr ⟨1, 0, Or.inl rfl, by simp⟩
lemma D1_zero : D1 0 := Or.inl rfl
lemma D1_pow (s : ℤ) (hs : s = 1 ∨ s = -1) (e : ℤ) : D1 (s * 2 ^ e) := Or.inr ⟨s, e, hs, rfl⟩

/-- Integer-valued dyadic signed powers are integer signed powers. -/
lemma W1_of_D1_int {x : ℤ} {q : ℚ} (hq : D1 q) (hx : (x : ℚ) = q) : W1 x := by
  rcases hq with rfl | ⟨s, e, hs, rfl⟩
  · left; exact_mod_cast hx
  rcases le_or_gt 0 e with he | he
  · right
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le he
    refine ⟨s, n, hs, ?_⟩
    exact_mod_cast (show (x : ℚ) = (s * 2 ^ n : ℤ) by rw [hx]; push_cast; rfl)
  · exfalso
    have hlt : |(x : ℚ)| < 1 := by
      rw [hx, abs_mul]
      have : |(s : ℚ)| = 1 := by rcases hs with rfl | rfl <;> simp
      rw [this, one_mul, abs_of_pos (by positivity)]
      exact zpow_lt_one_of_neg₀ (by norm_num) he
    have hne : (x : ℚ) ≠ 0 := by
      rw [hx]; rcases hs with rfl | rfl <;> simp <;> exact zpow_ne_zero _ (by norm_num)
    have h1 : |x| < 1 := by exact_mod_cast hlt
    have h2 : x ≠ 0 := by exact_mod_cast hne
    exact h2 (Int.abs_lt_one_iff.mp h1)

lemma le_of_pow_dvd {u : ℤ} (hu : ¬ (2 : ℤ) ∣ u) {p N : ℕ} (h : (2 : ℤ) ^ N ∣ 2 ^ p * u) :
    N ≤ p := by
  by_contra hlt; push Not at hlt
  have h1 : (2 : ℤ) ^ p * 2 ∣ 2 ^ p * u := by
    rw [← pow_succ]; exact (pow_dvd_pow 2 hlt).trans h
  exact hu ((mul_dvd_mul_iff_left (by positivity)).mp h1)

lemma not_two_dvd_sign {s : ℤ} (hs : s = 1 ∨ s = -1) : ¬ (2 : ℤ) ∣ s := by
  rcases hs with rfl | rfl <;> decide

/-- An integer that is a sum of two dyadic signed powers is `W2`. -/
lemma W2_of_D2_int {x : ℤ} {q : ℚ} (hq : D2 q) (hx : (x : ℚ) = q) : W2 x := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hq
  -- clear denominators: find `N` with `a * 2^N`, `b * 2^N` integral
  have hint : ∀ {c : ℚ}, D1 c → ∃ N : ℕ, ∀ M ≥ N, ∃ z : ℤ, W1 z ∧ c * 2 ^ M = z := by
    intro c hc
    rcases hc with rfl | ⟨s, e, hs, rfl⟩
    · exact ⟨0, fun M _ => ⟨0, Or.inl rfl, by simp⟩⟩
    · refine ⟨(-e).toNat, fun M hM => ⟨s * 2 ^ (e + M).toNat, Or.inr ⟨s, _, hs, rfl⟩, ?_⟩⟩
      have := Int.self_le_toNat (-e)
      have hpos : 0 ≤ e + M := by omega
      push_cast
      rw [mul_assoc, ← zpow_natCast (2 : ℚ) M, ← zpow_add₀ (by norm_num), ← zpow_natCast,
        Int.toNat_of_nonneg hpos]
  obtain ⟨N1, h1⟩ := hint ha
  obtain ⟨N2, h2⟩ := hint hb
  set N := max N1 N2
  obtain ⟨za, hza, hza'⟩ := h1 N (le_max_left _ _)
  obtain ⟨zb, hzb, hzb'⟩ := h2 N (le_max_right _ _)
  have hsum : x * 2 ^ N = za + zb := by
    have : (x : ℚ) * 2 ^ N = za + zb := by rw [hx, add_mul, hza', hzb']
    exact_mod_cast this
  -- now `za + zb` is divisible by `2^N`; analyse the two signed powers
  have hdvd : (2 : ℤ) ^ N ∣ za + zb := ⟨x, by rw [← hsum]; ring⟩
  rcases hza with rfl | ⟨s, p, hs, rfl⟩
  · have hw := hzb
    refine W1.W2 ?_
    rcases hw with rfl | ⟨t, q, ht, rfl⟩
    · left; simpa using hsum
    · -- t 2^q = x 2^N
      right
      have hq : N ≤ q := le_of_pow_dvd (not_two_dvd_sign ht)
        (by rw [mul_comm]; simpa using hdvd)
      refine ⟨t, q - N, ht, ?_⟩
      have : x * 2 ^ N = t * 2 ^ (q - N) * 2 ^ N := by
        rw [hsum, mul_assoc, ← pow_add, Nat.sub_add_cancel hq]; ring
      exact mul_right_cancel₀ (by positivity) this
  rcases hzb with rfl | ⟨t, q, ht, rfl⟩
  · refine W1.W2 (Or.inr ?_)
    have hp : N ≤ p := le_of_pow_dvd (not_two_dvd_sign hs)
      (by rw [mul_comm]; simpa using hdvd)
    refine ⟨s, p - N, hs, ?_⟩
    have : x * 2 ^ N = s * 2 ^ (p - N) * 2 ^ N := by
      rw [hsum, add_zero, mul_assoc, ← pow_add, Nat.sub_add_cancel hp]
    exact mul_right_cancel₀ (by positivity) this
  -- both nonzero: use the sparse form of `s 2^p + t 2^q`, all of whose exponents are ≥ N
  obtain ⟨L, hL, hv, hl⟩ := W2_sparse ⟨_, _, Or.inr ⟨s, p, hs, rfl⟩, Or.inr ⟨t, q, ht, rfl⟩, rfl⟩
  -- every exponent in `L` is at least `N`, by repeatedly peeling the lowest term
  have hge : ∀ {L : List (ℤ × ℕ)}, Sparse L → (2 : ℤ) ^ N ∣ value L → ∀ y ∈ L, N ≤ y.2 := by
    intro L
    induction L with
    | nil => simp
    | cons y L ih =>
      intro hS hD z hz
      have hy : N ≤ y.2 := by
        obtain ⟨r, hr⟩ := value_cons_mod hS
        refine le_of_pow_dvd (u := y.1 + 4 * r) ?_ ?_
        · rcases hS.2 y (by simp) with h | h <;> rw [h] <;> omega
        · rw [hr] at hD; convert hD using 1; ring
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hy
      · refine ih hS.tail ?_ z hz
        have := dvd_sub hD (Dvd.dvd.mul_left (pow_dvd_pow 2 hy) y.1)
        rwa [value_cons, add_sub_cancel_left] at this
  have hall := hge hL (hv ▸ hdvd)
  -- divide every exponent by `2^N`
  have hdiv : ∀ {L : List (ℤ × ℕ)}, (∀ y ∈ L, N ≤ y.2) → Sparse L →
      value L = value (L.map fun y => (y.1, y.2 - N)) * 2 ^ N := by
    intro L
    induction L with
    | nil => simp
    | cons y L ih =>
      intro h hS
      rw [List.map_cons, value_cons, value_cons, ih (fun z hz => h z (by simp [hz])) hS.tail]
      have := h y (by simp)
      rw [add_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel this]
  have hx' : x = value (L.map fun y => (y.1, y.2 - N)) := by
    have := hdiv hall hL
    rw [hv, ← hsum] at this
    exact mul_right_cancel₀ (by positivity) this
  -- a list of at most two signed powers is `W2`
  rw [hx']
  have hsg := hL.2
  match L, hl, hsg with
  | [], _, _ => exact W1.W2 (Or.inl rfl)
  | [y], _, hsg => exact W1.W2 (Or.inr ⟨y.1, y.2 - N, hsg y (by simp), by simp⟩)
  | [y, z], _, hsg => exact ⟨y.1 * 2 ^ (y.2 - N), z.1 * 2 ^ (z.2 - N),
      Or.inr ⟨y.1, _, hsg y (by simp), rfl⟩, Or.inr ⟨z.1, _, hsg z (by simp), rfl⟩, by simp⟩

end Pts
