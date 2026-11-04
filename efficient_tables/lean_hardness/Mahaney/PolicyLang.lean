import Mahaney.TableLang

/-!
# The sparsity barrier for a unary-parameter optimisation language (T-count, unary `n`)

`TableLang.lean` proves the barrier for the structural score `S`, with the bound `B k = 15k(2k-1)`.
Nothing in that argument uses the table problem except three facts: the optimum is at most a
polynomial `p` of the unary parameter, `p` is monotone, and membership depends on the instance only
through the optimum. This file isolates them.

`PolicyLang opt n0` is the decision language `{(μ, 1^n, B) : n0 ≤ n ∧ opt μ n ≤ B}` (`n` in unary,
`B` in canonical binary), with the encoding `encI` of `TableLang.lean`. Here `opt μ n` is meant to be
`OPT^T_μ(n)`, the least T-count of a recursion policy for modulus size `n`.

`policyOpt_barrier`: if `opt μ n ≤ p.eval n` for all `n ≥ n0` (a fixed policy has polynomial
T-count) and `p.eval` is monotone, then `NPHard (PolicyLang opt n0) → P = NP`.

**Not formalised here:** the T-count itself (the Qualtran / `tcost` model). The hypothesis `hopt` is
exactly the statement "some feasible policy has T-count at most a polynomial in `n`"; it is supplied
by the caller. No hypothesis is made on `opt` otherwise (it may be non-computable).
-/

namespace Mahaney

open Complexity TableGeneration TableGeneration.SparsityBarrier

section Generic

variable (opt : ProductMode → ℕ → ℕ) (n0 : ℕ)

/-- The instances with a feasible budget. -/
def PolicySet : Set Inst := {x | n0 ≤ x.2.1 ∧ opt x.1 x.2.1 ≤ x.2.2}

/-- The language: `(μ, 1^n, B)` with `OPT_μ(n) ≤ B`. -/
def PolicyLang : Language := encI '' PolicySet opt n0

variable (p : Polynomial ℕ)

/-- The hard core: budgets of at most `size (p n)` bits. -/
def PCore : Language :=
  {w | w ∈ PolicyLang opt n0 ∧ (pairSnd w).length ≤ (p.eval ((pairFst w).length - 1)).size}

/-- The trigger for sending an instance to the fixed YES instance. -/
def pBig (w : List Bool) : Prop :=
  WF w ∧ n0 ≤ (pairFst w).length - 1 ∧ (p.eval ((pairFst w).length - 1)).size < (pairSnd w).length

open Classical in
noncomputable def pReduce (w : List Bool) : List Bool :=
  if pBig n0 p w then encI (.PhaseProduct, n0, p.eval n0) else w

lemma mem_policyLang_encI (x : Inst) : encI x ∈ PolicyLang opt n0 ↔ x ∈ PolicySet opt n0 :=
  encI_injective.mem_set_image

variable (hopt : ∀ m n, n0 ≤ n → opt m n ≤ p.eval n)

include hopt in
lemma pYes_mem : encI (.PhaseProduct, n0, p.eval n0) ∈ PCore opt n0 p := by
  refine ⟨(mem_policyLang_encI opt n0 _).mpr ⟨le_refl _, hopt _ _ le_rfl⟩, ?_⟩
  simp only [encI, pairFst_pair, pairSnd_pair, List.length_cons, List.length_replicate,
    Nat.add_sub_cancel, Nat.size_eq_bits_len, le_refl]

lemma pReduce_mem_FP : pReduce n0 p ∈ FP := by
  classical
  have hk : UnaryFn fun w : List Bool => (pairFst w).length - 1 :=
    (UnaryFn.length pairFst_mem_FP).sub (UnaryFn.const 1)
  have hB : UnaryFn fun w : List Bool => p.eval ((pairFst w).length - 1) := UnaryFn.polyEval p hk
  have hp : FPPred (pBig n0 p) :=
    WF_FPPred.and ((FPPred.le (UnaryFn.const n0) hk).and
      (FPPred.lt hB.size (UnaryFn.length pairSnd_mem_FP)))
  exact mem_FP_of_eq (FPPred.ite_mem_FP hp (constFn_mem_FP (encI (.PhaseProduct, n0, p.eval n0)))
    id_mem_FP) fun w => by simp [pReduce]

include hopt in
theorem pReduce_correct (w : List Bool) : w ∈ PolicyLang opt n0 ↔ pReduce n0 p w ∈ PCore opt n0 p := by
  classical
  unfold pReduce
  by_cases hbig : pBig n0 p w
  · rw [if_pos hbig]
    refine ⟨fun _ => pYes_mem opt n0 p hopt, fun _ => ?_⟩
    obtain ⟨hwf, hk, hsz⟩ := hbig
    obtain ⟨⟨m, k, K⟩, rfl⟩ := (WF_iff w).mp hwf
    simp only [encI, pairFst_pair, pairSnd_pair, List.length_cons, List.length_replicate,
      Nat.add_sub_cancel, Nat.size_eq_bits_len] at hk hsz
    rw [mem_policyLang_encI]
    have h1 : 2 ^ (p.eval k).size ≤ K := Nat.lt_size.mp hsz
    have h2 := Nat.lt_size_self (p.eval k)
    exact ⟨hk, show opt m k ≤ K from (hopt m k hk).trans (by omega)⟩
  · rw [if_neg hbig]
    refine ⟨fun hw => ⟨hw, ?_⟩, fun hw => hw.1⟩
    obtain ⟨⟨m, k, K⟩, hx, rfl⟩ := hw
    have hk := hx.1
    by_contra hlt
    push Not at hlt
    exact hbig ⟨(WF_iff _).mpr ⟨_, rfl⟩, by simpa [encI] using hk, hlt⟩

theorem PCore_sparse (hmono : Monotone fun n => p.eval n) : Sparse (PCore opt n0 p) := by
  classical
  refine ⟨Polynomial.C 2 * (Polynomial.X + 1) * (Polynomial.C 2 * p + 1), fun m => ?_⟩
  let modes : Finset ProductMode := {.PhaseProduct, .PhaseTripleProduct}
  let F : Finset Inst := modes ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (2 * p.eval m + 1))
  have hsub : {w | w ∈ PCore opt n0 p ∧ w.length ≤ m} ⊆ encI '' (F : Set Inst) := by
    rintro w ⟨⟨⟨⟨mode, k, K⟩, _, rfl⟩, hb⟩, hlen⟩
    refine ⟨(mode, k, K), ?_, rfl⟩
    simp only [encI, pairFst_pair, pairSnd_pair, List.length_cons, List.length_replicate,
      Nat.add_sub_cancel, Nat.size_eq_bits_len, pair_length] at hb hlen
    have hK : K < 2 * p.eval m + 1 := by
      have h1 := Nat.lt_size_self K
      have h2 : 2 ^ K.size ≤ 2 ^ (p.eval k).size := Nat.pow_le_pow_right (by norm_num) hb
      have h3 := pow_size_le (p.eval k)
      have h4 : p.eval k ≤ p.eval m := hmono (by omega)
      omega
    have hmode : mode ∈ modes := by cases mode <;> simp [modes]
    simp only [F, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    exact ⟨hmode, by omega, hK⟩
  have hcard : F.card = 2 * ((m + 1) * (2 * p.eval m + 1)) := by
    simp only [F, Finset.card_product, Finset.card_range]
    rfl
  calc {w | w ∈ PCore opt n0 p ∧ w.length ≤ m}.ncard ≤ (encI '' (F : Set Inst)).ncard :=
        Set.ncard_le_ncard hsub ((Finset.finite_toSet F).image _)
    _ ≤ (F : Set Inst).ncard := Set.ncard_image_le (Finset.finite_toSet F)
    _ = F.card := Set.ncard_coe_finset F
    _ = _ := by
        rw [hcard]
        simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_one]
        ring

include hopt in
/-- **Barrier for a unary-parameter optimisation language.** If the optimum is bounded by a monotone
polynomial of the unary parameter, many-one NP-hardness of the decision language gives `P = NP`. -/
theorem policyOpt_barrier (hmono : Monotone fun n => p.eval n) :
    NPHard (PolicyLang opt n0) → P = NP := by
  intro h
  have hred : PolicyLang opt n0 ≤ₚ PCore opt n0 p :=
    ⟨pReduce n0 p, pReduce_mem_FP n0 p, pReduce_correct opt n0 p hopt⟩
  exact mahaney (PCore_sparse opt n0 p hmono) fun L' hL' => (h L' hL').trans hred

end Generic

end Mahaney
