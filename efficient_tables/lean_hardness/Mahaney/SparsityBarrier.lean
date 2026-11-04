import Mathlib.Tactic
import TableGeneration.Spec
import TableGeneration.Metrics
import TableGeneration.ContractSoundness

/-!
# The sparsity barrier for NP-hardness of the table-schedule problem

The problem posed by the paper and by ShorTableOptimization: for a target `(mode, k)`, a policy
chooses a point list, an order and a program. The contract (`ValidPointList`, `ValidPointOrder`,
`ProgConsumesPtsSafe ... State.start_state`) checks them, and the score is
`arithmeticOperationCount + 5 * parallelPhaseProductLayerCount` (`leaderboard/config.json`).

Its decision version is the set `TableOpt` of instances `(mode, k, K)` with a valid schedule of
score `≤ K`. **The instance holds nothing but `(mode, k)` and the budget `K`**: the points are
chosen by the policy, not given.

This file proves, from the contract alone (no extra axioms):

1. `uniform_feasible`: for every `k ≥ 2` and both modes, an explicit schedule passes the contract
   and scores at most `5 · n · (2k − 1)`, where `n = mode.pointCount k`. So `OPT(mode, k) ≤ B k`
   with `B k = 15 k (2k − 1)`, a polynomial.
2. `mem_tableOpt_iff`: `(mode, k, K) ∈ TableOpt ↔ 2 ≤ k ∧ OPT mode k ≤ K`. Membership depends on
   the instance only through one integer per `(mode, k)`.
3. `core_sparse`: the "hard core" `Core = {x ∈ TableOpt : K < B k}` has at most
   `2 (m + 1) B m` elements of size `≤ m`, where size is unary in `k` (as in the paper's
   benchmark), whatever the encoding of `K`. So `Core` is a sparse set.
4. `reduce_correct`: the closed-form map `reduce` (identity if `K < B k`, a fixed YES instance
   otherwise) satisfies `x ∈ TableOpt ↔ reduce x ∈ Core`.
5. `advice_decides`: all instances of size `≤ m` are decided by a table of `2(m + 1)` numbers
   (the values `OPT mode k`, `k ≤ m`), so `TableOpt` has polynomial advice.

## What is cited, not formalised

Mathlib has no polynomial-time computation model, so three facts are stated as hypotheses of
`barrier` rather than proved:
* `reduce` is polynomial-time computable (it compares `K` with the polynomial `B k`);
* Mahaney (1982): a sparse NP-hard set (many-one) implies `P = NP`;
* NP-hardness transfers along polynomial-time many-one reductions (transitivity).

`barrier` then derives: if `TableOpt` is NP-hard under many-one reductions, `P = NP`. Item 5
gives the Turing-reduction version on paper (NP ⊆ P/poly, then Karp–Lipton collapses PH).
-/

namespace TableGeneration
namespace SparsityBarrier

open Operations

/-! ## The problem -/

/-- The paper's score: arithmetic operations plus 5 per marker layer. -/
def score {k : Nat} (ops : Prog k) : Nat :=
  arithmeticOperationCount ops + 5 * parallelPhaseProductLayerCount ops

/-- A schedule for `(mode, k)` that passes the ShorTableOptimization contract. -/
def Valid (mode : ProductMode) (k : Nat) (hk : k > 0) (pts order : List Point)
    (ops : Prog k) : Prop :=
  ValidPointList mode k pts ∧ ValidPointOrder pts order ∧
    ProgConsumesPtsSafe hk State.start_state ops order

/-- The instances: a mode, the size `k` and a budget `K`. -/
abbrev Inst := ProductMode × Nat × Nat

/-- The decision problem: some valid schedule scores at most `K`. -/
def TableOpt : Set Inst :=
  {x | ∃ hk : 2 ≤ x.2.1, ∃ pts order ops,
    Valid x.1 x.2.1 (positive_of_ge_two hk) pts order ops ∧ score ops ≤ x.2.2}

/-! ## Generic run / consumption lemmas -/

lemma run_append {k : Nat} (p q : Prog k) (σ : State k) :
    run? (p ++ q) σ = (run? p σ).bind (run? q) := by
  induction p generalizing σ with
  | nil => rfl
  | cons op p ih =>
    simp only [List.cons_append, run?]
    cases applyOp? σ op with
    | none => rfl
    | some σ' => exact ih σ'

/-- A program with no markers that runs from `σ` to `σ'` can be skipped in a consumption check. -/
lemma consumes_append {k : Nat} (hk : k > 0) (p q : Prog k) (σ σ' : State k) (pts : List Point)
    (hnm : ∀ op ∈ p, ∀ i, op ≠ .phaseProduct i) (hrun : run? p σ = some σ') :
    progConsumesPts? hk σ (p ++ q) pts = progConsumesPts? hk σ' q pts := by
  induction p generalizing σ with
  | nil => simp only [run?, Option.some.injEq] at hrun; subst hrun; rfl
  | cons op p ih =>
    have hop : ∀ i, op ≠ .phaseProduct i := hnm op (by simp)
    have hrest : ∀ o ∈ p, ∀ i, o ≠ .phaseProduct i := fun o ho => hnm o (by simp [ho])
    cases happ : applyOp? σ op with
    | none => simp [run?, happ] at hrun
    | some τ =>
      have hrun' : run? p τ = some σ' := by simpa [run?, happ] using hrun
      rw [← ih τ hrest hrun']
      cases op with
      | phaseProduct i => exact absurd rfl (hop i)
      | _ => simp only [List.cons_append, progConsumesPts?, happ]

/-! ## The uniform schedule

Points: `int (2^e)` for `e < n`. For each point, register 0 (initially `e_0`) gets
`(2^e)^j · e_j` added from every register `j ≠ 0`, the marker fires on register 0, and the
additions are undone. -/

/-- Accumulate into register 0, from each source `s`, `± 2^(e·s) · (register s)`. -/
def addOps {k : Nat} (hk : 0 < k) (b : Bool) (e : Nat) (S : List (Fin k)) : Prog k :=
  S.map fun s => .addScaled (finZero hk) s b (e * s.val)

/-- The sources: every register other than 0. -/
def sources {k : Nat} (hk : 0 < k) : List (Fin k) :=
  (List.finRange k).filter fun j => j ≠ finZero hk

def build {k : Nat} (hk : 0 < k) (e : Nat) : Prog k := addOps hk false e (sources hk)

def block {k : Nat} (hk : 0 < k) (e : Nat) : Prog k :=
  build hk e ++ [.phaseProduct (finZero hk)] ++ apply_Op_inverse (build hk e)

def uniformPts (n : Nat) : List Point := (List.range n).map fun e => .int ((2 : Int) ^ e)

def uniformProg {k : Nat} (hk : 0 < k) (n : Nat) : Prog k :=
  (List.range n).flatMap (block hk)

lemma inverse_build {k : Nat} (hk : 0 < k) (e : Nat) :
    apply_Op_inverse (build hk e) = addOps hk true e (sources hk).reverse := by
  simp [apply_Op_inverse, build, addOps, List.map_reverse, Operations.inv]

/-- The signed contribution of an addition. -/
def sgn (b : Bool) : Int := if b then -1 else 1

lemma run_addOps {k : Nat} (hk : 0 < k) (b : Bool) (e : Nat) (S : List (Fin k))
    (hnd : S.Nodup) (h0 : finZero hk ∉ S) (r : Register k) :
    run? (addOps hk b e S) (State.setReg State.start_state (finZero hk) r) =
      some (State.setReg State.start_state (finZero hk)
        (fun m => r m + if m ∈ S then sgn b * (2 : Int) ^ (e * m.val) else 0)) := by
  induction S generalizing r with
  | nil => simp [addOps, run?]
  | cons s S ih =>
    have hs0 : s ≠ finZero hk := fun h => h0 (h ▸ List.mem_cons_self ..)
    have hsS : s ∉ S := (List.nodup_cons.mp hnd).1
    have h0S : finZero hk ∉ S := fun h => h0 (List.mem_cons_of_mem _ h)
    simp only [addOps, List.map_cons, run?, applyOp?, State.addScaledReg]
    have hstep : State.setReg (State.setReg State.start_state (finZero hk) r) (finZero hk)
        (Register.addScaled (State.setReg State.start_state (finZero hk) r (finZero hk))
          (State.setReg State.start_state (finZero hk) r s) b (e * s.val)) =
        State.setReg State.start_state (finZero hk)
          (fun m => r m + if m = s then sgn b * (2 : Int) ^ (e * m.val) else 0) := by
      funext i j
      by_cases hi : i = finZero hk
      · subst hi
        by_cases hj : j = s
        · subst hj; simp [State.setReg, Register.addScaled, State.start_state, hs0, sgn]
        · simp [State.setReg, Register.addScaled, State.start_state, hs0, hj, Ne.symm hj]
      · simp [State.setReg, hi]
    rw [hstep]
    have := ih (List.nodup_cons.mp hnd).2 h0S
      (fun m => r m + if m = s then sgn b * (2 : Int) ^ (e * m.val) else 0)
    simp only [addOps] at this
    rw [this]
    congr 2
    funext m
    by_cases hm : m = s
    · subst hm; simp [hsS]
    · simp [hm]

lemma sources_nodup {k : Nat} (hk : 0 < k) : (sources hk).Nodup :=
  (List.nodup_finRange k).filter _

lemma zero_not_mem_sources {k : Nat} (hk : 0 < k) : finZero hk ∉ sources hk := by
  simp [sources]

lemma mem_sources {k : Nat} (hk : 0 < k) (m : Fin k) : m ∈ sources hk ↔ m ≠ finZero hk := by
  simp [sources]

lemma setReg_start_self {k : Nat} (i : Fin k) :
    State.setReg State.start_state i (State.start_state i) = State.start_state := by
  funext a b; by_cases h : a = i <;> simp [State.setReg, h]

/-- The register-0 row after `build e`. -/
def row {k : Nat} (e : Nat) : Register k := fun m => ((2 : Int) ^ e) ^ m.val

lemma run_build {k : Nat} (hk : 0 < k) (e : Nat) :
    run? (build hk e) State.start_state =
      some (State.setReg State.start_state (finZero hk) (row e)) := by
  have h := run_addOps hk false e (sources hk) (sources_nodup hk) (zero_not_mem_sources hk)
    (State.start_state (finZero hk))
  rw [setReg_start_self] at h
  rw [build, h]
  congr 2
  funext m
  by_cases hm : m = finZero hk
  · subst hm; simp [row, State.start_state, mem_sources, finZero]
  · have hv : m.val ≠ 0 := fun h => hm (Fin.ext h)
    simp [row, State.start_state, mem_sources, hm, sgn, ← pow_mul]

lemma run_unbuild {k : Nat} (hk : 0 < k) (e : Nat) :
    run? (apply_Op_inverse (build hk e)) (State.setReg State.start_state (finZero hk) (row e)) =
      some State.start_state := by
  rw [inverse_build]
  have hnd := (List.nodup_reverse.mpr (sources_nodup hk))
  have h0 : finZero hk ∉ (sources hk).reverse := by
    simpa using zero_not_mem_sources hk
  rw [run_addOps hk true e _ hnd h0]
  congr 1
  conv_rhs => rw [← setReg_start_self (finZero hk)]
  congr 1
  funext m
  by_cases hm : m = finZero hk
  · subst hm; simp [row, State.start_state, mem_sources, finZero]
  · have hv : m.val ≠ 0 := fun h => hm (Fin.ext h)
    simp [row, State.start_state, mem_sources, hm, sgn, ← pow_mul]

lemma addOps_nm {k : Nat} (hk : 0 < k) (b : Bool) (e : Nat) (S : List (Fin k)) :
    ∀ op ∈ addOps hk b e S, ∀ i, op ≠ .phaseProduct i := by
  intro op hop i h; subst h; simp [addOps] at hop

lemma run_block {k : Nat} (hk : 0 < k) (e : Nat) :
    run? (block hk e) State.start_state = some State.start_state := by
  simp only [block, run_append, run_build, Option.bind_some, run?, applyOp?, run_unbuild]

lemma consumes_uniform {k : Nat} (hk : 0 < k) (L : List Nat) :
    progConsumesPts? hk State.start_state (L.flatMap (block hk))
      (L.map fun e => .int ((2 : Int) ^ e)) = true := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [List.flatMap_cons, List.map_cons, block, List.append_assoc]
    rw [consumes_append hk (build hk e) _ _ _ _ (addOps_nm hk false e _) (run_build hk e)]
    simp only [List.cons_append, List.nil_append, progConsumesPts?, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp [matchesAt_pointRow_state, regEqExpected, State.setReg, expectedRow, row]
    · have hnm : ∀ op ∈ apply_Op_inverse (build hk e), ∀ i, op ≠ .phaseProduct i := by
        rw [inverse_build]; exact addOps_nm hk true e _
      rw [consumes_append hk _ _ _ _ _ hnm (run_unbuild hk e)]
      exact ih

lemma run_uniform {k : Nat} (hk : 0 < k) (L : List Nat) :
    run? (L.flatMap (block hk)) State.start_state = some State.start_state := by
  induction L with
  | nil => rfl
  | cons e L ih => simp only [List.flatMap_cons, run_append, run_block, Option.bind_some, ih]

lemma wellFormed_append {k : Nat} (p q : Prog k) :
    Prog.wellFormed? (p ++ q) = (Prog.wellFormed? p && Prog.wellFormed? q) := by
  induction p with
  | nil => simp [Prog.wellFormed?]
  | cons op p ih => simp [Prog.wellFormed?, ih, Bool.and_assoc]

lemma wellFormed_addOps {k : Nat} (hk : 0 < k) (b : Bool) (e : Nat) (S : List (Fin k))
    (h0 : finZero hk ∉ S) : Prog.wellFormed? (addOps hk b e S) = true := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    have hs : s ≠ finZero hk := fun h => h0 (h ▸ List.mem_cons_self ..)
    simp only [addOps, List.map_cons, Prog.wellFormed?, Prog.OpOK?, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨Ne.symm hs, by simpa [addOps] using ih (fun h => h0 (List.mem_cons_of_mem _ h))⟩

lemma safe_uniform {k : Nat} (hk : 0 < k) (L : List Nat) :
    safeProg? (L.flatMap (block hk)) = true := by
  unfold safeProg?
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [List.flatMap_cons, wellFormed_append, ih, Bool.and_true, block, inverse_build]
    simp only [Prog.wellFormed?, Prog.OpOK?, Bool.and_true, Bool.true_and, Bool.and_eq_true]
    exact ⟨wellFormed_addOps hk false e _ (zero_not_mem_sources hk),
      wellFormed_addOps hk true e _ (by simpa using zero_not_mem_sources hk)⟩

/-! ### Validity of the points -/

lemma natPowerOfTwoFuel_pow (e : Nat) : ∀ fuel, e ≤ fuel → natPowerOfTwoFuel fuel (2 ^ e) = true := by
  induction e with
  | zero => intro fuel _; cases fuel <;> simp [natPowerOfTwoFuel]
  | succ e ih =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have h1 : (2 : Nat) ^ (e + 1) ≠ 1 := by
      have := Nat.one_lt_two_pow (n := e + 1) (by omega); omega
    simp [natPowerOfTwoFuel, h1, pow_succ, ih f (by omega)]

lemma validPoint_pow (e : Nat) : validPoint? (.int ((2 : Int) ^ e)) = true := by
  have : signedPowerOfTwo? ((2 : Int) ^ e) = true := by
    have hne : ((2 : Int) ^ e) ≠ 0 := by positivity
    have habs : Int.natAbs ((2 : Int) ^ e) = 2 ^ e := by simp [Int.natAbs_pow]
    unfold signedPowerOfTwo? natPowerOfTwo?
    rw [if_neg (by simpa using hne), habs]
    exact natPowerOfTwoFuel_pow e _ (Nat.lt_two_pow_self).le
  simp [validPoint?, this]

lemma uniformPts_valid (mode : ProductMode) (k : Nat) :
    ValidPointList mode k (uniformPts (mode.pointCount k)) := by
  refine ⟨by simp [uniformPts], ?_, ?_⟩
  · have hinj : Function.Injective fun e : Nat => normalizePoint (.int ((2 : Int) ^ e)) := by
      intro a b h
      simp only [normalizePoint, Point.int.injEq] at h
      exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h)
    simpa [uniformPts, List.map_map, Function.comp_def] using
      (List.nodup_range (n := mode.pointCount k)).map hinj
  · simp [uniformPts, List.all_eq_true, validPoint_pow]

/-! ### Its score -/

lemma arith_add_count {k : Nat} (p : Prog k) :
    arithmeticOperationCount p + phaseProductCount p = p.length := by
  induction p with
  | nil => rfl
  | cons op p ih =>
    cases op <;> simp [arithmeticOperationCount, phaseProductCount] <;> omega

lemma layers_le_aux {k : Nat} (b : Bool) (p : Prog k) :
    parallelPhaseProductLayerCountAux b p ≤ phaseProductCount p := by
  induction p generalizing b with
  | nil => simp [parallelPhaseProductLayerCountAux]
  | cons op p ih =>
    cases op <;> simp [parallelPhaseProductLayerCountAux, phaseProductCount] <;>
      first | exact ih _ | (have := ih true; split <;> omega)

lemma score_le_length {k : Nat} (p : Prog k) : score p ≤ 5 * p.length := by
  have h1 := arith_add_count p
  have h2 := layers_le_aux false p
  unfold score parallelPhaseProductLayerCount
  omega

lemma sources_length {k : Nat} (hk : 0 < k) : (sources hk).length = k - 1 := by
  classical
  have h1 : (sources hk).length = (sources hk).toFinset.card :=
    (List.toFinset_card_of_nodup (sources_nodup hk)).symm
  have h2 : (sources hk).toFinset = Finset.univ.erase (finZero hk) := by
    ext j; simp [List.mem_toFinset, mem_sources]
  rw [h1, h2, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

lemma uniformProg_length {k : Nat} (hk : 0 < k) (n : Nat) :
    (uniformProg hk n).length = n * (2 * k - 1) := by
  have hb : ∀ e, (block hk e).length = 2 * k - 1 := by
    intro e
    simp [block, apply_Op_inverse, build, addOps, sources_length]
    omega
  unfold uniformProg
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [hb]; ring

/-- **Uniform feasibility.** Every target admits a contract-valid schedule of score
`≤ 5 · pointCount · (2k − 1)`. -/
theorem uniform_feasible (mode : ProductMode) (k : Nat) (hk : 0 < k) :
    Valid mode k hk (uniformPts (mode.pointCount k)) (uniformPts (mode.pointCount k))
        (uniformProg hk (mode.pointCount k)) ∧
      score (uniformProg hk (mode.pointCount k)) ≤ 5 * (mode.pointCount k * (2 * k - 1)) := by
  refine ⟨⟨uniformPts_valid mode k, List.Perm.refl _, ?_⟩, ?_⟩
  · exact progConsumesPtsSafe_of_checks (consumes_uniform hk _) (safe_uniform hk _)
      ((returnsToStartCheck_iff _ _).mpr (run_uniform hk _))
  · exact (score_le_length _).trans (by rw [uniformProg_length])

/-! ## OPT and the threshold form -/

/-- The polynomial upper bound `B k = 15 k (2k − 1)`. -/
def B (k : Nat) : Nat := 15 * k * (2 * k - 1)

lemma pointCount_le (mode : ProductMode) (k : Nat) : mode.pointCount k ≤ 3 * k := by
  cases mode <;> simp [ProductMode.pointCount] <;> omega

lemma exists_le_B (mode : ProductMode) (k : Nat) (hk : 2 ≤ k) :
    ∃ K, ∃ pts order ops, Valid mode k (positive_of_ge_two hk) pts order ops ∧ score ops ≤ K := by
  obtain ⟨hv, _⟩ := uniform_feasible mode k (positive_of_ge_two hk)
  exact ⟨_, _, _, _, hv, le_refl _⟩

/-- The optimum, with the convention `OPT = 0` for `k < 2` (no instance there is in `TableOpt`). -/
noncomputable def OPT (mode : ProductMode) (k : Nat) : Nat :=
  if hk : 2 ≤ k then
    @Nat.find (fun K => ∃ pts order ops,
      Valid mode k (positive_of_ge_two hk) pts order ops ∧ score ops ≤ K)
      (Classical.decPred _) (exists_le_B mode k hk)
  else 0

theorem mem_tableOpt_iff (mode : ProductMode) (k K : Nat) :
    (mode, k, K) ∈ TableOpt ↔ 2 ≤ k ∧ OPT mode k ≤ K := by
  classical
  constructor
  · rintro ⟨hk, pts, order, ops, hv, hs⟩
    refine ⟨hk, ?_⟩
    simp only [OPT, dif_pos hk]
    exact Nat.find_min' _ ⟨pts, order, ops, hv, hs⟩
  · rintro ⟨hk, hle⟩
    simp only [OPT, dif_pos hk] at hle
    obtain ⟨pts, order, ops, hv, hs⟩ := Nat.find_spec (exists_le_B mode k hk)
    exact ⟨hk, pts, order, ops, hv, hs.trans (by convert hle)⟩

theorem OPT_le_B (mode : ProductMode) (k : Nat) : OPT mode k ≤ B k := by
  by_cases hk : 2 ≤ k
  · have h := (mem_tableOpt_iff mode k (B k)).mp ?_
    · exact h.2
    obtain ⟨hv, hs⟩ := uniform_feasible mode k (positive_of_ge_two hk)
    refine ⟨hk, _, _, _, hv, hs.trans ?_⟩
    have := pointCount_le mode k
    unfold B
    calc 5 * (mode.pointCount k * (2 * k - 1)) ≤ 5 * (3 * k * (2 * k - 1)) := by gcongr
      _ = 15 * k * (2 * k - 1) := by ring
  · simp [OPT, hk]

/-! ## Sparsity of the hard core -/

/-- Size of an instance: `k` in unary (as in the benchmark), `K` in binary, plus a mode bit. -/
def size (x : Inst) : Nat := 1 + x.2.1 + Nat.size x.2.2

/-- The hard core: instances whose budget is below the polynomial bound. -/
def Core : Set Inst := {x | x ∈ TableOpt ∧ x.2.2 < B x.2.1}

lemma B_mono : Monotone B := by
  intro a b h; unfold B; gcongr

/-- **Sparsity.** At most `2 (m + 1) B m` core instances have size `≤ m`. -/
theorem core_sparse (m : Nat) :
    {x | x ∈ Core ∧ size x ≤ m}.ncard ≤ 2 * (m + 1) * B m := by
  classical
  let modes : Finset ProductMode := {.PhaseProduct, .PhaseTripleProduct}
  let F : Finset Inst := modes ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (B m))
  have hsub : {x | x ∈ Core ∧ size x ≤ m} ⊆ (F : Set Inst) := by
    rintro ⟨mode, k, K⟩ ⟨⟨_, hK⟩, hs⟩
    simp only [size] at hs hK
    have hk : k ≤ m := by omega
    have hKB : K < B m := lt_of_lt_of_le hK (B_mono hk)
    have hmode : mode ∈ modes := by cases mode <;> simp [modes]
    simp only [F, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    exact ⟨hmode, by omega, hKB⟩
  have hmodes : modes.card = 2 := by decide
  calc {x | x ∈ Core ∧ size x ≤ m}.ncard ≤ (F : Set Inst).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet F)
    _ = F.card := Set.ncard_coe_finset F
    _ = 2 * (m + 1) * B m := by
        simp only [F, Finset.card_product, Finset.card_range, hmodes]; ring

/-! ## The reduction to the core -/

/-- A fixed YES instance of the core: `(PP, 2, 45)`; the uniform schedule at `k = 2` has
3 points and scores at most `5 · 3 · 3 = 45 < B 2 = 90`. -/
def yesInst : Inst := (.PhaseProduct, 2, 45)

lemma yesInst_core : yesInst ∈ Core := by
  obtain ⟨hv, hs⟩ := uniform_feasible .PhaseProduct 2 (by decide)
  exact ⟨⟨le_refl 2, _, _, _, hv, hs.trans (by decide)⟩, by decide⟩

/-- The reduction: keep instances with `k < 2` or budget below `B k`; send the rest
(all YES instances) to `yesInst`. -/
def reduce (x : Inst) : Inst := if x.2.1 < 2 ∨ x.2.2 < B x.2.1 then x else yesInst

theorem reduce_correct (x : Inst) : x ∈ TableOpt ↔ reduce x ∈ Core := by
  obtain ⟨mode, k, K⟩ := x
  unfold reduce
  split_ifs with h
  · refine ⟨fun hx => ⟨hx, ?_⟩, fun hx => hx.1⟩
    rcases h with h | h
    · exact absurd ((mem_tableOpt_iff _ _ _).mp hx).1 (by simp at h ⊢; omega)
    · exact h
  · simp only [not_or, not_lt] at h
    refine ⟨fun _ => yesInst_core, fun _ => ?_⟩
    exact (mem_tableOpt_iff _ _ _).mpr ⟨h.1, (OPT_le_B mode k).trans h.2⟩

/-! ## Polynomial advice -/

/-- The advice for size `m`: the optima for `k ≤ m`, both modes (`2 (m + 1)` numbers,
each `≤ B m`). -/
noncomputable def advice (m : Nat) : List (Nat × Nat) :=
  (List.range (m + 1)).map fun k => (OPT .PhaseProduct k, OPT .PhaseTripleProduct k)

/-- Decide an instance from the advice table by one lookup and one comparison. -/
def decideWith (adv : List (Nat × Nat)) (x : Inst) : Prop :=
  2 ≤ x.2.1 ∧ ∃ p ∈ adv[x.2.1]?,
    (match x.1 with | .PhaseProduct => p.1 | .PhaseTripleProduct => p.2) ≤ x.2.2

theorem advice_length (m : Nat) : (advice m).length = m + 1 := by simp [advice]

theorem advice_bounded (m : Nat) : ∀ p ∈ advice m, p.1 ≤ B m ∧ p.2 ≤ B m := by
  intro p hp
  simp only [advice, List.mem_map, List.mem_range] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  exact ⟨(OPT_le_B _ k).trans (B_mono (by omega)), (OPT_le_B _ k).trans (B_mono (by omega))⟩

/-- **Advice.** Every instance of size `≤ m` is decided correctly from `advice m`. -/
theorem advice_decides (m : Nat) (x : Inst) (hx : size x ≤ m) :
    x ∈ TableOpt ↔ decideWith (advice m) x := by
  obtain ⟨mode, k, K⟩ := x
  have hk : k < m + 1 := by simp only [size] at hx; omega
  rw [mem_tableOpt_iff]
  simp only [decideWith, advice, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.mem_def, Option.some.injEq, exists_eq_left']
  cases mode <;> rfl

/-! ## The barrier, relative to cited complexity theory

Mathlib has no polynomial-time computation model, so the complexity notions are abstract
parameters and the three cited facts are explicit hypotheses. Everything about the table
problem itself is proved above. -/

/-- A set of instances is sparse if, for some polynomial bound, it has at most `c (m+1)^d`
members of size `≤ m`. -/
def Sparse (S : Set Inst) : Prop :=
  ∃ c d : Nat, ∀ m, {x | x ∈ S ∧ size x ≤ m}.ncard ≤ c * (m + 1) ^ d

theorem core_is_sparse : Sparse Core := by
  refine ⟨60, 3, fun m => (core_sparse m).trans ?_⟩
  have hB : B m ≤ 30 * (m + 1) ^ 2 := by
    unfold B
    have : 2 * m - 1 ≤ 2 * (m + 1) := by omega
    calc 15 * m * (2 * m - 1) ≤ 15 * (m + 1) * (2 * (m + 1)) := by gcongr; omega
      _ = 30 * (m + 1) ^ 2 := by ring
  calc 2 * (m + 1) * B m ≤ 2 * (m + 1) * (30 * (m + 1) ^ 2) := by gcongr
    _ = 60 * (m + 1) ^ 3 := by ring

/-- **The sparsity barrier.** Suppose (cited, not formalised here):
* `hred`: `reduce` is a polynomial-time many-one reduction (it is the closed form above);
* `htrans`: NP-hardness transfers along such reductions;
* `hMahaney`: Mahaney (1982), a sparse NP-hard set implies `P = NP`.

Then NP-hardness of `TableOpt` implies `P = NP`. -/
theorem barrier (PolyTime : (Inst → Inst) → Prop) (NPHard : Set Inst → Prop) (PeqNP : Prop)
    (hred : PolyTime reduce)
    (htrans : ∀ (L L' : Set Inst) (f : Inst → Inst), PolyTime f → (∀ x, x ∈ L ↔ f x ∈ L') →
      NPHard L → NPHard L')
    (hMahaney : ∀ S, Sparse S → NPHard S → PeqNP) :
    NPHard TableOpt → PeqNP :=
  fun h => hMahaney Core core_is_sparse (htrans TableOpt Core reduce hred reduce_correct h)

end SparsityBarrier
end TableGeneration
