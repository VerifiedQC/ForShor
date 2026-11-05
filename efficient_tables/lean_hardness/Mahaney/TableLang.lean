import Mahaney.Theorem
import Mahaney.SparsityBarrier
import Mathlib.Data.Nat.Size

/-!
# The table-schedule problem as a language, and its NP-hardness barrier

An instance `(mode, k, K)` of `SparsityBarrier.TableOpt` is written as the bit string
`encI (mode, k, K) = pair (modeBit :: 1^k) (K.bits)`: the mode as one bit, `k` in unary (the
benchmark's size parameter), and the budget `K` in canonical binary (`Nat.bits`, the convention
complexitylib uses for numbers). `TableOptLang` is the image of `TableOpt`.

`tableOpt_barrier : NPHard TableOptLang → P = NP`, over complexitylib's Turing machines, with no
hypotheses: `reduceS ∈ FP` sends `TableOptLang` to its hard core `CoreL` (budgets of at most
`size (B k)` bits), `CoreL` is sparse, and `mahaney` applies.
-/

namespace Mahaney

open Complexity TableGeneration TableGeneration.SparsityBarrier

/-! ### Encoding -/

def modeBit : ProductMode → Bool
  | .PhaseProduct => false
  | .PhaseTripleProduct => true

def modeOf (b : Bool) : ProductMode := if b then .PhaseTripleProduct else .PhaseProduct

lemma modeOf_modeBit (m : ProductMode) : modeOf (modeBit m) = m := by cases m <;> rfl

lemma modeBit_modeOf (c : Bool) : modeBit (modeOf c) = c := by cases c <;> rfl

/-- The instance encoding. -/
def encI (x : Inst) : List Bool := pair (modeBit x.1 :: un x.2.1) x.2.2.bits

/-- The table-schedule decision problem as a language. -/
def TableOptLang : Language := encI '' TableOpt

/-- LSB-first value. -/
def lsbVal : List Bool → ℕ
  | [] => 0
  | b :: t => Nat.bit b (lsbVal t)

lemma bits_eq_nil_iff (n : ℕ) : n.bits = [] ↔ n = 0 := by
  rw [← List.length_eq_zero_iff, Nat.size_eq_bits_len]
  constructor
  · intro h; by_contra hn; exact absurd h (Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  · rintro rfl; simp

lemma lsbVal_bits (n : ℕ) : lsbVal n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [lsbVal]
  | bit b n h ih => rw [Nat.bits_append_bit n b h, lsbVal, ih]

lemma bits_injective : Function.Injective Nat.bits := fun a b h => by
  rw [← lsbVal_bits a, h, lsbVal_bits]

/-- Canonical binary: empty, or ending in a `1`. -/
def Canon (y : List Bool) : Prop := y = [] ∨ y[y.length - 1]?.getD false = true

lemma canon_bits (n : ℕ) : Canon n.bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [Canon]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    right
    by_cases hn : n = 0
    · subst hn; simp [h rfl]
    · have hne : n.bits ≠ [] := by rw [Ne, bits_eq_nil_iff]; exact hn
      rcases ih with h0 | h1
      · exact absurd h0 hne
      · have hl : 0 < n.bits.length := List.length_pos_iff.mpr hne
        simp only [List.length_cons, Nat.add_sub_cancel]
        rw [show n.bits.length = (n.bits.length - 1) + 1 by omega, List.getElem?_cons_succ]
        exact h1

lemma bits_lsbVal_of_canon {y : List Bool} (hy : Canon y) : (lsbVal y).bits = y := by
  induction y with
  | nil => simp [lsbVal]
  | cons b t ih =>
    have ht : Canon t := by
      rcases hy with h | h
      · simp at h
      · by_cases h0 : t = []
        · left; exact h0
        · right
          have hl : 0 < t.length := List.length_pos_iff.mpr h0
          simp only [List.length_cons, Nat.add_sub_cancel] at h
          rwa [show t.length = (t.length - 1) + 1 by omega, List.getElem?_cons_succ] at h
    have hb : lsbVal t = 0 → b = true := by
      intro h0
      have : t = [] := by rw [← ih ht, h0]; rfl
      subst this
      rcases hy with h | h
      · simp at h
      · simpa using h
    rw [lsbVal, Nat.bits_append_bit _ _ hb, ih ht]

lemma encI_injective : Function.Injective encI := by
  rintro ⟨m, k, K⟩ ⟨m', k', K'⟩ h
  obtain ⟨h1, h2⟩ := pair_inj h
  simp only [List.cons.injEq] at h1
  have hm : m = m' := by rw [← modeOf_modeBit m, h1.1, modeOf_modeBit]
  have hk : k = k' := by have := congrArg List.length h1.2; simpa using this
  subst hm; subst hk
  have hK : K = K' := bits_injective h2
  rw [hK]

lemma mem_lang_encI (x : Inst) : encI x ∈ TableOptLang ↔ x ∈ TableOpt :=
  encI_injective.mem_set_image

/-! ### Well-formedness is polynomial-time -/

/-- The well-formedness test. -/
def WF (w : List Bool) : Prop :=
  w = pair (pairFst w) (pairSnd w) ∧ 1 ≤ (pairFst w).length ∧
    (∀ i < (pairFst w).length - 1, (pairFst w)[i + 1]?.getD false = true) ∧ Canon (pairSnd w)

lemma WF_iff (w : List Bool) : WF w ↔ ∃ x, w = encI x := by
  constructor
  · rintro ⟨hw, h1, hall, hc⟩
    obtain ⟨c, rest, hx⟩ : ∃ c rest, pairFst w = c :: rest := by
      cases h : pairFst w with
      | nil => rw [h] at h1; simp at h1
      | cons c rest => exact ⟨c, rest, rfl⟩
    have hrest : rest = un rest.length := by
      apply List.eq_replicate_iff.mpr ⟨rfl, fun b hb => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have := hall i (by rw [hx]; simp; omega)
      rw [hx] at this
      simpa [List.getElem?_eq_getElem hi] using this
    refine ⟨(modeOf c, rest.length, lsbVal (pairSnd w)), ?_⟩
    calc w = pair (pairFst w) (pairSnd w) := hw
      _ = pair (modeBit (modeOf c) :: un rest.length) (lsbVal (pairSnd w)).bits := by
          rw [bits_lsbVal_of_canon hc, hx, modeBit_modeOf, ← hrest]
      _ = encI (modeOf c, rest.length, lsbVal (pairSnd w)) := rfl
  · rintro ⟨⟨m, k, K⟩, rfl⟩
    refine ⟨by simp [encI], by simp [encI], fun i hi => ?_, by simpa [encI] using canon_bits K⟩
    simp only [encI, pairFst_pair, List.length_cons, List.length_replicate] at hi ⊢
    simp [List.getElem?_replicate, show i < k by omega]

lemma WF_FPPred : FPPred WF := by
  have h1 := FPPred.strEq id_mem_FP (f := id) (g := fun w => pair (pairFst w) (pairSnd w))
    (by polytime)
  have h2 : FPPred fun w : List Bool => 1 ≤ (pairFst w).length :=
    FPPred.le (UnaryFn.const 1) (UnaryFn.length pairFst_mem_FP)
  have h3 : FPPred fun w : List Bool =>
      ∀ i < (pairFst w).length - 1, (pairFst w)[i + 1]?.getD false = true := by
    have hb := FPPred.getBit (bits := fun y : List Bool => pairFst (pairFst y))
      (i := fun y => (pairSnd y).length + 1) (by polytime) (UnaryFn.index.add (UnaryFn.const 1))
    refine (FPPred.forall_lt ((UnaryFn.length pairFst_mem_FP).sub (UnaryFn.const 1)) hb).of_iff
      fun w => ?_
    simp [pairFst_pair, pairSnd_pair]
  have h4 : FPPred fun w : List Bool => Canon (pairSnd w) := by
    have he := FPPred.strEq (f := pairSnd) (g := fun _ => []) pairSnd_mem_FP (constFn_mem_FP [])
    have hl := FPPred.getBit (bits := pairSnd)
      (i := fun w => (pairSnd w).length - 1) pairSnd_mem_FP
      ((UnaryFn.length pairSnd_mem_FP).sub (UnaryFn.const 1))
    exact (he.or hl).of_iff fun w => Iff.rfl
  exact (h1.and (h2.and (h3.and h4))).of_iff fun w => by simp [WF]

/-! ### The reduction to the hard core -/

/-- The hard core: budgets of at most `size (B k)` bits. -/
def CoreL : Language :=
  {w | w ∈ TableOptLang ∧ (pairSnd w).length ≤ (B ((pairFst w).length - 1)).size}

/-- The trigger for sending an instance to the fixed YES instance. -/
def bigBudget (w : List Bool) : Prop :=
  WF w ∧ 2 ≤ (pairFst w).length - 1 ∧ (B ((pairFst w).length - 1)).size < (pairSnd w).length

open Classical in
/-- The reduction on strings. -/
noncomputable def reduceS (w : List Bool) : List Bool := if bigBudget w then encI yesInst else w

lemma reduceS_mem_FP : reduceS ∈ FP := by
  classical
  have hk : UnaryFn fun w : List Bool => (pairFst w).length - 1 :=
    (UnaryFn.length pairFst_mem_FP).sub (UnaryFn.const 1)
  have hB : UnaryFn fun w : List Bool => B ((pairFst w).length - 1) := by
    refine (((UnaryFn.const 15).mul hk).mul (((UnaryFn.const 2).mul hk).sub
      (UnaryFn.const 1))).of_eq fun w => ?_
    rfl
  have hp : FPPred bigBudget :=
    WF_FPPred.and ((FPPred.le (UnaryFn.const 2) hk).and
      (FPPred.lt hB.size (UnaryFn.length pairSnd_mem_FP)))
  exact mem_FP_of_eq (FPPred.ite_mem_FP hp (constFn_mem_FP (encI yesInst)) id_mem_FP)
    fun w => by simp [reduceS]

lemma pow_size_le (n : ℕ) : 2 ^ n.size ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hs := Nat.size_pos.mpr hn
    have : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
    calc 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
          rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * n + 1 := by omega

lemma yes_mem_CoreL : encI yesInst ∈ CoreL := by
  refine ⟨(mem_lang_encI _).mpr yesInst_core.1, ?_⟩
  simp only [encI, yesInst, pairFst_pair, pairSnd_pair, List.length_cons, List.length_replicate,
    Nat.size_eq_bits_len]
  decide

theorem reduceS_correct (w : List Bool) : w ∈ TableOptLang ↔ reduceS w ∈ CoreL := by
  classical
  unfold reduceS
  by_cases hbig : bigBudget w
  · rw [if_pos hbig]
    refine ⟨fun _ => yes_mem_CoreL, fun _ => ?_⟩
    obtain ⟨hwf, hk2, hsz⟩ := hbig
    obtain ⟨⟨m, k, K⟩, rfl⟩ := (WF_iff w).mp hwf
    simp only [encI, pairFst_pair, pairSnd_pair, List.length_cons, List.length_replicate,
      Nat.add_sub_cancel, Nat.size_eq_bits_len] at hk2 hsz
    rw [mem_lang_encI, mem_tableOpt_iff]
    have h1 : 2 ^ (B k).size ≤ K := Nat.lt_size.mp hsz
    have h2 := Nat.lt_size_self (B k)
    exact ⟨hk2, (OPT_le_B m k).trans (by omega)⟩
  · rw [if_neg hbig]
    refine ⟨fun hw => ⟨hw, ?_⟩, fun hw => hw.1⟩
    obtain ⟨⟨m, k, K⟩, hx, rfl⟩ := hw
    have hk2 := ((mem_tableOpt_iff m k K).mp hx).1
    by_contra hlt
    push Not at hlt
    exact hbig ⟨(WF_iff _).mpr ⟨_, rfl⟩, by simpa [encI] using hk2, hlt⟩

/-! ### The hard core is sparse -/

theorem CoreL_sparse : Sparse CoreL := by
  classical
  refine ⟨Polynomial.C 2 * (Polynomial.X + 1) * (Polynomial.C 60 * Polynomial.X ^ 2 + 1),
    fun m => ?_⟩
  let modes : Finset ProductMode := {.PhaseProduct, .PhaseTripleProduct}
  let F : Finset Inst := modes ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (2 * B m + 1))
  have hsub : {w | w ∈ CoreL ∧ w.length ≤ m} ⊆ encI '' (F : Set Inst) := by
    rintro w ⟨⟨⟨⟨mode, k, K⟩, _, rfl⟩, hb⟩, hlen⟩
    refine ⟨(mode, k, K), ?_, rfl⟩
    simp only [encI, pairFst_pair, pairSnd_pair, List.length_cons, List.length_replicate,
      Nat.add_sub_cancel, Nat.size_eq_bits_len, pair_length] at hb hlen
    have hK : K < 2 * B m + 1 := by
      have h1 := Nat.lt_size_self K
      have h2 : 2 ^ K.size ≤ 2 ^ (B k).size := Nat.pow_le_pow_right (by norm_num) hb
      have h3 := pow_size_le (B k)
      have h4 : B k ≤ B m := B_mono (by omega)
      omega
    have hmode : mode ∈ modes := by cases mode <;> simp [modes]
    simp only [F, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    exact ⟨hmode, by omega, hK⟩
  have hcard : F.card = 2 * ((m + 1) * (2 * B m + 1)) := by
    simp only [F, Finset.card_product, Finset.card_range]
    rfl
  have hB : B m ≤ 30 * m ^ 2 := by
    unfold B
    calc 15 * m * (2 * m - 1) ≤ 15 * m * (2 * m) := by gcongr; omega
      _ = 30 * m ^ 2 := by ring
  calc {w | w ∈ CoreL ∧ w.length ≤ m}.ncard ≤ (encI '' (F : Set Inst)).ncard :=
        Set.ncard_le_ncard hsub ((Finset.finite_toSet F).image _)
    _ ≤ (F : Set Inst).ncard := Set.ncard_image_le (Finset.finite_toSet F)
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ _ := by
        rw [hcard]
        simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_pow, Polynomial.eval_one]
        have : 2 * B m + 1 ≤ 60 * m ^ 2 + 1 := by omega
        calc 2 * ((m + 1) * (2 * B m + 1)) ≤ 2 * ((m + 1) * (60 * m ^ 2 + 1)) := by gcongr
          _ = 2 * (m + 1) * (60 * m ^ 2 + 1) := by ring

/-! ### The barrier -/

/-- **The NP-hardness barrier for the table-schedule problem.** If the paper's decision problem
(`TableOptLang`) is NP-hard under polynomial-time many-one reductions, then `P = NP`. Over
complexitylib's multi-tape Turing machines; no hypotheses. -/
theorem tableOpt_barrier : NPHard TableOptLang → P = NP := by
  intro h
  have hred : TableOptLang ≤ₚ CoreL := ⟨reduceS, reduceS_mem_FP, reduceS_correct⟩
  exact mahaney CoreL_sparse fun L' hL' => (h L' hL').trans hred

end Mahaney
