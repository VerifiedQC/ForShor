import Mathlib.Tactic

/-!
# The abstract pruning core of Mahaney's theorem (port of `Workbench/TableOpt/MahaneyCore.lean`)

Assignments are numbers `a < 2^n`; `Left n sat y` says some satisfying `a` has `y ≤ a`.
`level` runs the Ogihara–Watanabe pruning with an arbitrary map `f` of left-set queries;
`accepts_iff` proves it decides satisfiability when `f` reduces the left set into a set
covered by `T` with `T.card ≤ s`. No machine model here.
-/

namespace Mahaney

section Core

variable {σ : Type*} [DecidableEq σ]

/-- The left set: some satisfying assignment `a < 2^n` lies at or above `y`. -/
def Left (n : ℕ) (sat : ℕ → Prop) (y : ℕ) : Prop := ∃ a < 2 ^ n, sat a ∧ y ≤ a

/-- A length-`i` prefix `p`, padded with zeros to `n` bits. -/
def query (n i p : ℕ) : ℕ := p * 2 ^ (n - i)

/-- Extend every prefix by one bit. -/
def expand (C : Finset ℕ) : Finset ℕ := C.biUnion fun p => {2 * p, 2 * p + 1}

/-- Pruning 1: for each `f`-value, keep only the largest prefix with that value. -/
def prune1 (n : ℕ) (f : ℕ → σ) (i : ℕ) (E : Finset ℕ) : Finset ℕ :=
  E.filter fun p => ∀ q ∈ E, f (query n i q) = f (query n i p) → q ≤ p

/-- Number of elements of `D` below `p`. -/
def rank (D : Finset ℕ) (p : ℕ) : ℕ := (D.filter (· < p)).card

/-- Pruning 2: keep only the `s` smallest prefixes. -/
def prune2 (s : ℕ) (D : Finset ℕ) : Finset ℕ := D.filter fun p => rank D p < s

/-- The surviving prefixes of length `i`. -/
def level (n : ℕ) (f : ℕ → σ) (s : ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | i + 1 => prune2 s (prune1 n f (i + 1) (expand (level n f s i)))

/-- The algorithm's answer: some surviving full assignment satisfies the formula. -/
def accepts (n : ℕ) (sat : ℕ → Prop) (f : ℕ → σ) (s : ℕ) : Prop :=
  ∃ a ∈ level n f s n, a < 2 ^ n ∧ sat a

instance (n : ℕ) (sat : ℕ → Prop) [DecidablePred sat] (f : ℕ → σ) (s : ℕ) :
    Decidable (accepts n sat f s) := by
  unfold accepts; infer_instance

/-! ### Structural lemmas -/

lemma expand_lt {C : Finset ℕ} {i : ℕ} (h : ∀ p ∈ C, p < 2 ^ i) :
    ∀ p ∈ expand C, p < 2 ^ (i + 1) := by
  intro p hp
  simp only [expand, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hp
  obtain ⟨q, hq, rfl | rfl⟩ := hp <;> have := h q hq <;> rw [pow_succ] <;> omega

lemma level_lt (n : ℕ) (f : ℕ → σ) (s : ℕ) : ∀ i, ∀ p ∈ level n f s i, p < 2 ^ i
  | 0 => by simp [level]
  | i + 1 => by
    intro p hp
    have h1 : p ∈ prune1 n f (i + 1) (expand (level n f s i)) := (Finset.mem_filter.mp hp).1
    exact expand_lt (level_lt n f s i) p (Finset.mem_filter.mp h1).1

lemma query_lt {n i p : ℕ} (hi : i ≤ n) (hp : p < 2 ^ i) : query n i p < 2 ^ n := by
  unfold query
  calc p * 2 ^ (n - i) < 2 ^ i * 2 ^ (n - i) :=
        Nat.mul_lt_mul_of_pos_right hp (by positivity)
    _ = 2 ^ n := by rw [← pow_add]; congr 1; omega

lemma prune2_card (s : ℕ) (D : Finset ℕ) : (prune2 s D).card ≤ s := by
  by_contra h
  push_neg at h
  have hne : (prune2 s D).Nonempty := Finset.card_pos.mp (by omega)
  have hm : (prune2 s D).max' hne ∈ prune2 s D := Finset.max'_mem _ hne
  have hsub : (prune2 s D).erase ((prune2 s D).max' hne) ⊆
      D.filter (· < (prune2 s D).max' hne) := by
    intro p hp
    have hpF := Finset.mem_of_mem_erase hp
    have hpm := Finset.ne_of_mem_erase hp
    have hle := Finset.le_max' _ p hpF
    simp only [prune2, Finset.mem_filter] at hpF
    exact Finset.mem_filter.mpr ⟨hpF.1, lt_of_le_of_ne hle hpm⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hm] at h1
  have h2 := (Finset.mem_filter.mp hm).2
  unfold rank at h2
  omega

/-! ### The largest satisfying assignment and its prefixes -/

variable (n : ℕ) (sat : ℕ → Prop) [DecidablePred sat]

/-- The largest satisfying assignment below `2^n` (meaningful when one exists). -/
def astar : ℕ := Nat.findGreatest sat (2 ^ n - 1)

/-- Its length-`i` prefix. -/
def pref (i : ℕ) : ℕ := astar n sat / 2 ^ (n - i)

variable {n sat}

lemma astar_spec (h : ∃ a < 2 ^ n, sat a) :
    sat (astar n sat) ∧ astar n sat < 2 ^ n ∧ ∀ a < 2 ^ n, sat a → a ≤ astar n sat := by
  obtain ⟨a, ha, hs⟩ := h
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine ⟨Nat.findGreatest_spec (m := a) (by omega) hs, ?_, fun b hb hsb =>
    Nat.le_findGreatest (by omega) hsb⟩
  have := Nat.findGreatest_le (P := sat) (2 ^ n - 1)
  unfold astar; omega

lemma left_iff (h : ∃ a < 2 ^ n, sat a) (y : ℕ) : Left n sat y ↔ y ≤ astar n sat := by
  obtain ⟨hs, hlt, hmax⟩ := astar_spec h
  constructor
  · rintro ⟨a, ha, hsa, hy⟩; exact hy.trans (hmax a ha hsa)
  · intro hy; exact ⟨_, hlt, hs, hy⟩

lemma left_query (h : ∃ a < 2 ^ n, sat a) (i p : ℕ) :
    Left n sat (query n i p) ↔ p ≤ pref n sat i := by
  rw [left_iff h, query, pref, Nat.le_div_iff_mul_le (by positivity)]

lemma pref_zero (h : ∃ a < 2 ^ n, sat a) : pref n sat 0 = 0 := by
  unfold pref; simpa using Nat.div_eq_of_lt (astar_spec h).2.1

lemma pref_n : pref n sat n = astar n sat := by simp [pref]

lemma pref_succ_div {i : ℕ} (hi : i < n) : pref n sat (i + 1) / 2 = pref n sat i := by
  unfold pref
  rw [Nat.div_div_eq_div_mul, ← pow_succ]
  congr 2; omega

lemma pref_mem_expand {i : ℕ} (hi : i < n) {C : Finset ℕ} (hC : pref n sat i ∈ C) :
    pref n sat (i + 1) ∈ expand C := by
  simp only [expand, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨_, hC, ?_⟩
  have := Nat.div_add_mod (pref n sat (i + 1)) 2
  have h2 := Nat.mod_lt (pref n sat (i + 1)) (by norm_num : 2 > 0)
  rw [pref_succ_div hi] at this
  omega

/-! ### Correctness -/

variable {f : ℕ → σ} {S : Set σ} {T : Finset σ} {s : ℕ}

/-- **Invariant.** If the formula is satisfiable, the length-`i` prefix of the largest
satisfying assignment survives to level `i`. -/
theorem pref_mem_level (hred : ∀ y < 2 ^ n, (Left n sat y ↔ f y ∈ S))
    (hT : ∀ y < 2 ^ n, f y ∈ S → f y ∈ T) (hs : T.card ≤ s)
    (h : ∃ a < 2 ^ n, sat a) : ∀ i ≤ n, pref n sat i ∈ level n f s i
  | 0, _ => by simp [level, pref_zero h]
  | i + 1, hi => by
    have ih := pref_mem_level hred hT hs h i (by omega)
    set E := expand (level n f s i) with hE
    set t := pref n sat (i + 1) with ht
    have hElt : ∀ p ∈ E, query n (i + 1) p < 2 ^ n := fun p hp =>
      query_lt hi (expand_lt (level_lt n f s i) p hp)
    have hleft : ∀ p ∈ E, (p ≤ t ↔ f (query n (i + 1) p) ∈ S) := fun p hp =>
      (left_query h (i + 1) p).symm.trans (hred _ (hElt p hp))
    have htE : t ∈ E := pref_mem_expand (by omega) ih
    -- `t` survives pruning 1
    have htD : t ∈ prune1 n f (i + 1) E := by
      refine Finset.mem_filter.mpr ⟨htE, fun q hq heq => ?_⟩
      have : f (query n (i + 1) t) ∈ S := (hleft t htE).mp le_rfl
      exact (hleft q hq).mpr (heq ▸ this)
    set D := prune1 n f (i + 1) E with hD
    -- `t` survives pruning 2: the prefixes `≤ t` inject into `T`
    have hA : (D.filter (· ≤ t)).card ≤ T.card := by
      apply Finset.card_le_card_of_injOn (fun p => f (query n (i + 1) p))
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hpE := (Finset.mem_filter.mp hp'.1).1
        exact hT _ (hElt p hpE) ((hleft p hpE).mp hp'.2)
      · intro a ha b hb hab
        have ha' := Finset.mem_filter.mp (Finset.mem_filter.mp ha).1
        have hb' := Finset.mem_filter.mp (Finset.mem_filter.mp hb).1
        exact le_antisymm (hb'.2 a ha'.1 hab) (ha'.2 b hb'.1 hab.symm)
    have hlt : rank D t < (D.filter (· ≤ t)).card := by
      unfold rank
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (fun p hp => by
        simp only [Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.le⟩)]
      exact ⟨t, Finset.mem_filter.mpr ⟨htD, le_rfl⟩, by simp⟩
    show t ∈ prune2 s D
    exact Finset.mem_filter.mpr ⟨htD, by omega⟩

/-- **Correctness.** The pruning algorithm decides satisfiability. -/
theorem accepts_iff (hred : ∀ y < 2 ^ n, (Left n sat y ↔ f y ∈ S))
    (hT : ∀ y < 2 ^ n, f y ∈ S → f y ∈ T) (hs : T.card ≤ s) :
    accepts n sat f s ↔ ∃ a < 2 ^ n, sat a := by
  constructor
  · rintro ⟨a, _, ha, hsa⟩; exact ⟨a, ha, hsa⟩
  · intro h
    have hmem := pref_mem_level hred hT hs h n le_rfl
    rw [pref_n] at hmem
    exact ⟨_, hmem, (astar_spec h).2.1, (astar_spec h).1⟩

/-! ### The cost model

Unit cost per call to `f`, per call to `sat` and per comparison. A memoised implementation of
level `i + 1` evaluates `f` once on each element of `expand (level i)`, compares all pairs in
`prune1` and in `prune2`, and calls `sat` once per element of the last level. -/

variable (n f s)

def oracleCalls : ℕ := ∑ i ∈ Finset.range n, (expand (level n f s i)).card

def comparisons : ℕ := ∑ i ∈ Finset.range n,
  ((expand (level n f s i)).card ^ 2 + (prune1 n f (i + 1) (expand (level n f s i))).card ^ 2)

def satCalls : ℕ := (level n f s n).card

variable {n f s}

lemma expand_card (C : Finset ℕ) : (expand C).card ≤ 2 * C.card := by
  unfold expand
  calc (C.biUnion fun p => ({2 * p, 2 * p + 1} : Finset ℕ)).card
      ≤ ∑ p ∈ C, ({2 * p, 2 * p + 1} : Finset ℕ).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ C, 2 := Finset.sum_le_sum fun p _ => Finset.card_le_two
    _ = 2 * C.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma level_card (i : ℕ) : (level n f s i).card ≤ max s 1 := by
  cases i with
  | zero => simp [level]
  | succ i => exact (prune2_card s _).trans (le_max_left _ _)

/-- **Cost.** Polynomially many oracle calls, comparisons and `sat` calls, on `n`-bit
numbers. -/
theorem cost_bounds :
    oracleCalls n f s ≤ n * (2 * max s 1) ∧
    comparisons n f s ≤ n * (2 * (2 * max s 1) ^ 2) ∧
    satCalls n f s ≤ max s 1 ∧
    ∀ i ≤ n, ∀ p ∈ level n f s i, query n i p < 2 ^ n := by
  have hE : ∀ i, (expand (level n f s i)).card ≤ 2 * max s 1 := fun i =>
    (expand_card _).trans (by have := level_card (n := n) (f := f) (s := s) i; omega)
  refine ⟨?_, ?_, level_card n, fun i hi p hp => query_lt hi (level_lt n f s i p hp)⟩
  · calc oracleCalls n f s ≤ ∑ _i ∈ Finset.range n, 2 * max s 1 :=
          Finset.sum_le_sum fun i _ => hE i
      _ = n * (2 * max s 1) := by simp
  · calc comparisons n f s ≤ ∑ _i ∈ Finset.range n, 2 * (2 * max s 1) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have h1 := hE i
          have h2 : (prune1 n f (i + 1) (expand (level n f s i))).card ≤ 2 * max s 1 :=
            (Finset.card_filter_le _ _).trans h1
          have := Nat.pow_le_pow_left h1 2
          have := Nat.pow_le_pow_left h2 2
          omega
      _ = n * (2 * (2 * max s 1) ^ 2) := by simp

end Core

end Mahaney
