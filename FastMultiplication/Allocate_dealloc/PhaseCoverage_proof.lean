import FastMultiplication.Allocate_dealloc.Bridge_lemmas
import FastMultiplication.Allocate_dealloc.PhaseCoverage

/-
  This file transfers “phase-product coverage” information from the symbolic world to the
  compiled primitive program.

  Main goal (last theorem):
    compileProg_preserves_phaseCoverage

  Intuition:
  - The symbolic coverage predicate (`PhaseProductCoverage hk ops σ pts`) states that every
    `valid_ops.phaseProduct` step is justified by consuming a matching `Point` from `pts`.
  - The compiled program is a list of primitive ops (`prim_ops`) which contains
    `prim_ops.phaseProduct` at the corresponding moments.
  - The theorem shows that the compiled primitive program satisfies the primitive coverage
    predicate (`PhaseProductCoverage_prim`) with respect to the concrete state produced by
    `stateToSt`.

  Proof structure:
  1) Define a “no phase op occurs in a prefix” predicate (NoPhase) for primitive code.
  2) Show that a NoPhase prefix can be prepended to a coverage proof without consuming points.
  3) Establish list/eraseFirstMatch helper lemmas so that point-consumption transfers across append.
  4) Prove an append theorem for the primitive coverage predicate (PhaseProductCoverageM_prim_append).
  5) Prove the main inductive theorem on symbolic PhaseProductCoverage (compileProg_preserves_phaseCoverage_go),
     threading `ValidFor`, `ValidForStep`, and `PrimOKTrace` just like in `compileProg_simulates`,
     and using bridge lemmas to relate symbolic execution to primitive execution.
  6) Specialize that to start_state in the last theorem.
-/

namespace PhaseProduct_PrimOps

----------------------------------------------------------------------------------------------------
------------------------------- NO-PHASE PREFIX LEMMA ----------------------------------------------
----------------------------------------------------------------------------------------------------

/-
  NoPhase:

  Predicate stating that a primitive-op list contains no `prim_ops.phaseProduct` anywhere.
  This is used to mark prefixes of compiled code that are guaranteed to never consume points.

  It is used in the main proof when the head validated op is not phaseProduct:
  - compile1(op) produces a primitive prefix with NoPhase
  - coverage for that prefix is trivial (consumes [])
  - then append the tail coverage.
-/
def NoPhase {k : ℕ} : List (prim_ops k) → Prop
  | [] => True
  | prim_ops.phaseProduct _ :: _ => False
  | _ :: xs => NoPhase xs

/-
  PhaseProductCoverageM.prepend_noPhase:

  Core lemma: if a primitive suffix `ps` has phase coverage starting from the state obtained
  after evaluating a prefix `opsP`, and that prefix contains no phaseProduct ops, then the
  combined program `opsP ++ ps` has the same phase coverage starting from the original state.

  Key point: NoPhase guarantees the prefix does not consume points, so coverage can be “lifted”
  over the prefix by repeatedly applying the `step_op` constructor.
-/
lemma PhaseProductCoverageM.prepend_noPhase
  {k : ℕ} {M : MatchesAtStateBit k}
  (opsP : List (prim_ops k)) (ps : List (prim_ops k))
  (σ : St k) (pts : List Operations.Point)
  (hNo : NoPhase opsP)
  (hrest : PhaseProductCoverageM_prim (k := k) M ps (eval_prim_ops (k := k) opsP σ) pts) :
  PhaseProductCoverageM_prim (k := k) M (opsP ++ ps) σ pts := by
  induction opsP generalizing σ with
  | nil =>
      simpa [eval_prim_ops] using hrest
  | cons op ops ih =>
      cases op with
      | phaseProduct i =>
          cases hNo
      | Alloc i lsb n =>
          simp [NoPhase] at hNo
          have := ih (σ := eval_prim_op_single (k := k) (prim_ops.Alloc i lsb n) σ) hNo hrest
          simpa [eval_prim_ops] using (PhaseProductCoverageM_prim.step_op (k := k) (M := M) (hrest := this))
      | Free i lsb n =>
          simp [NoPhase] at hNo
          have := ih (σ := eval_prim_op_single (k := k) (prim_ops.Free i lsb n) σ) hNo hrest
          simpa [eval_prim_ops] using (PhaseProductCoverageM_prim.step_op (k := k) (M := M) (hrest := this))
      | negate i =>
          simp [NoPhase] at hNo
          have := ih (σ := eval_prim_op_single (k := k) (prim_ops.negate i) σ) hNo hrest
          simpa [eval_prim_ops] using (PhaseProductCoverageM_prim.step_op (k := k) (M := M) (hrest := this))
      | Add dst src =>
          simp [NoPhase] at hNo
          have := ih (σ := eval_prim_op_single (k := k) (prim_ops.Add dst src) σ) hNo hrest
          simpa [eval_prim_ops] using (PhaseProductCoverageM_prim.step_op (k := k) (M := M) (hrest := this))

end PhaseProduct_PrimOps

open Operations PhaseProduct_PrimOps

----------------------------------------------------------------------------------------------------
------------------------------- LIST / ERASE-FIRSTMATCH HELPERS ------------------------------------
----------------------------------------------------------------------------------------------------

/-
  eraseFirstMatchB_append_hit:

  If eraseFirstMatchB finds a match in a prefix xs and returns some ys,
  then appending an unrelated suffix zs preserves that successful deletion:
    eraseFirstMatchB p (xs ++ zs) = some (ys ++ zs).

  This is used in the primitive append proof when a phaseProduct consumes a point from
  the left list: consuming from (pts ++ b) results in (pts' ++ b).
-/
lemma eraseFirstMatchB_append_hit {α} (p : α → Bool) :
  ∀ {xs ys zs},
    eraseFirstMatchB p xs = some ys →
    eraseFirstMatchB p (xs ++ zs) = some (ys ++ zs)
| [],      ys, zs, h => by
    -- eraseFirstMatchB p [] = none, so impossible
    simp [eraseFirstMatchB] at h
| x :: xs, ys, zs, h => by
    -- unfold one step
    simp [eraseFirstMatchB] at h ⊢
    by_cases hx : p x = true
    · -- match at head: result is some xs
      simp [hx] at h
      cases h
      simp [hx]
    · -- no match at head: recurse on tail
      cases hxs : eraseFirstMatchB p xs with
      | none =>
          simp [hx, hxs] at h
      | some t =>
          have : ys = x :: t := by
            simp[hx, hxs] at h
            rw[h]
          subst this
          have ih := eraseFirstMatchB_append_hit (p := p) (xs := xs) (ys := t) (zs := zs) (by simp [hxs])
          simp [hx,  ih]

namespace PhaseProductCoverage

----------------------------------------------------------------------------------------------------
------------------------------- ERASE-FIRSTMATCH TRANSFER FACTS ------------------------------------
----------------------------------------------------------------------------------------------------

/-
  eraseFirstMatchB_congr:

  If two predicates p and q are pointwise equal, eraseFirstMatchB behaves identically.
  Used to swap predicate presentations when moving between pointRow and interp forms.
-/
lemma eraseFirstMatchB_congr
  {α : Type} (p q : α → Bool) :
  ∀ xs ys,
    (∀ x, p x = q x) →
    eraseFirstMatchB p xs = some ys →
    eraseFirstMatchB q xs = some ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys hp h
      aesop
  | cons x xs ih =>
      intro ys hp h
      simp [eraseFirstMatchB] at h ⊢
      have hx : p x = q x := hp x
      cases hpx : p x <;> cases hqx : q x <;> try cases hx
      · simp [hpx, hqx] at *;aesop
      · simp [hpx, hqx] at *
      · simp [hpx, hqx] at *
      · simp [hpx, hqx] at *;aesop

@[simp] lemma decide_eq_true_bool (b : Bool) : decide (b = true) = b := by
  cases b <;> rfl

/-
  eraseFirstMatchB_of_eraseFirstMatch?_Bool:

  Bridges the List.eraseFirstMatch? version (used in symbolic coverage definitions)
  to the eraseFirstMatchB version (used in primitive coverage definitions).
  This is used in point-consumption transfer lemmas where the symbolic side provides
  eraseFirstMatch? facts but the primitive side needs eraseFirstMatchB facts.
-/
lemma eraseFirstMatchB_of_eraseFirstMatch?_Bool
    {α : Type} (p : α → Bool) :
    ∀ (xs ys : List α),
      List.eraseFirstMatch? (fun x => p x) xs = some ys →
      eraseFirstMatchB p xs = some ys := by
  intro xs ys h
  have h' :=
    eraseFirstMatchB_of_eraseFirstMatch? (p := fun x => p x) xs ys
  aesop

end PhaseProductCoverage

----------------------------------------------------------------------------------------------------
------------------------------- PHASEPRODUCTCOVERAGEM_PRIM APPEND ----------------------------------
----------------------------------------------------------------------------------------------------

/-
  PhaseProductCoverageM_prim_append:

  Append theorem for primitive coverage:
  - If p has coverage consuming points a from σ
  - and q has coverage consuming points b from the state after executing p
  then p ++ q has coverage consuming a ++ b from σ.

  This is the core combinator used repeatedly in the main inductive proof when a NoPhase
  prefix is handled separately from the tail, and when phaseProduct heads are followed by tail code.
-/
theorem PhaseProductCoverageM_prim_append
  {k : ℕ} {M : MatchesAtStateBit k}
  {p q : List (prim_ops k)} {σ : St k} {a b : List Operations.Point}
  (hp : PhaseProductCoverageM_prim (k := k) M p σ a)
  (hq : PhaseProductCoverageM_prim (k := k) M q (eval_prim_ops (k := k) p σ) b) :
  PhaseProductCoverageM_prim (k := k) M (p ++ q) σ (a ++ b) := by
  induction hp generalizing q b with
  | nil =>
      simpa [eval_prim_ops] using hq

  | step_op hop hrest ih =>
      -- p = op :: ps, a unchanged
      rename_i op ps σ pts
      -- align the starting state for q
      have hq' :
          PhaseProductCoverageM_prim (k := k) M q
            (eval_prim_ops (k := k) ps (eval_prim_op_single (k := k) op σ)) b := by
        simpa [eval_prim_ops] using hq
      -- apply IH on tail coverage
      have ht :
          PhaseProductCoverageM_prim (k := k) M (ps ++ q)
            (eval_prim_op_single (k := k) op σ) (pts ++ b) :=
        ih (q := q) (b := b) hq'
      -- rebuild with step_op
      simpa [List.cons_append] using
        PhaseProductCoverageM_prim.step_op (k := k) (M := M)
          (op := op) (ps := ps ++ q) (σ := σ) (pts := pts ++ b)
          hop ht

  | step_phase hconsume hrest ih =>
      -- p = phaseProduct i :: ps
      rename_i i ps σ pts pts'
      -- phaseProduct does not change σ in eval_prim_ops
      have hq' :
          PhaseProductCoverageM_prim (k := k) M q (eval_prim_ops (k := k) ps σ) b := by
        simpa [eval_prim_ops, eval_prim_op_single] using hq
      -- apply IH to tail with pts' and b
      have ht :
          PhaseProductCoverageM_prim (k := k) M (ps ++ q) σ (pts' ++ b) :=
        ih (q := q) (b := b) hq'
      -- lift the consume fact to pts ++ b
      have hconsume' :
          eraseFirstMatchB (fun pt => M σ i pt) (pts ++ b) = some (pts' ++ b) :=
        eraseFirstMatchB_append_hit (p := fun pt => M σ i pt)
          (xs := pts) (ys := pts') (zs := b) hconsume
      -- rebuild with step_phase
      simpa [List.cons_append] using
        PhaseProductCoverageM_prim.step_phase (k := k) (M := M)
          (i := i) (ps := ps ++ q) (σ := σ)
          (pts := pts ++ b) (pts' := pts' ++ b)
          hconsume' ht

/-
  phaseProduct_coverage_prim_check_append:

  Specialization of the append theorem for the case where the prefix p returns to σ
  (i.e. eval_prim_ops p σ = σ). This allows composing two coverages both starting
  from σ without rewriting the intermediate state.
-/
/- “Returns to σ” -/
lemma phaseProduct_coverage_prim_check_append
  {k : ℕ} {M : MatchesAtStateBit k}
  {p q : List (prim_ops k)} {σ : St k} {a b : List Operations.Point}
  (hret : eval_prim_ops (k := k) p σ = σ)
  (hp : PhaseProductCoverageM_prim (k := k) M p σ a)
  (hq : PhaseProductCoverageM_prim (k := k) M q σ b) :
  PhaseProductCoverageM_prim (k := k) M (p ++ q) σ (a ++ b) := by
  have hq' :
      PhaseProductCoverageM_prim (k := k) M q (eval_prim_ops (k := k) p σ) b := by
    simpa [hret] using hq
  exact PhaseProductCoverageM_prim_append (hp := hp) (hq := hq')

----------------------------------------------------------------------------------------------------
------------------------------- COVERAGE WRAPPER ---------------------------------------------------
----------------------------------------------------------------------------------------------------

/-
  PhaseProductCoverage_prim:

  Wrapper that fixes the matching predicate M to the “interp matcher” based on σ0.
  This is the exact coverage predicate used as the target statement in the main theorems.
-/
def PhaseProductCoverage_prim {k : ℕ}
    (prog : List (prim_ops k)) (σ0 : St k) (pts : List Operations.Point) : Prop :=
  PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σ0) prog σ0 pts

----------------------------------------------------------------------------------------------------
------------------------------- COMPILER SIMP LEMMAS ------------------------------------------------
----------------------------------------------------------------------------------------------------

/-
  compile1_phaseProduct:

  Normal form for compilation of phaseProduct: compile1 emits exactly one prim phaseProduct
  and does not change curLen. Used to simplify the compiled program shape in proofs that split
  on whether the head op is phaseProduct.
-/
@[simp] lemma compile1_phaseProduct
  {k : ℕ} (i : Fin k) (curLen : List Nat) :
  compile1 (k := k) (valid_ops.phaseProduct i) curLen
    = ([prim_ops.phaseProduct i], curLen) := by
  simp [compile1, compile_op_to_prim_single]

----------------------------------------------------------------------------------------------------
------------------------------- POINT-ROW MATCHER FACTS --------------------------------------------
----------------------------------------------------------------------------------------------------

/-
  The next block relates the different matching predicates:
  - matchesAt_pointRow_state: symbolic/table-level matching against a Point row
  - regEqExpected: equivalent “all coefficients equal expectedRow” formulation
  - matchesAt_interp: the compiled/primitive-level matcher used in coverage proofs

  These are used to transfer “the head Point matches” facts from the symbolic side
  to the primitive side (where eraseFirstMatchB consumes based on matchesAt_interp).
-/
@[simp] lemma matchesAt_pointRow_state_apply
  {k : Nat} (hk : k > 0) (σ : State k) (i : Fin k) (pt : Point) :
  matchesAt_pointRow_state (k := k) hk σ i pt
    =
  regEqExpected (k := k) (σ i) pt := by
  rfl

lemma matchesAt_pointRow_state_eq_ofRegister
  {k : Nat} (hk : k > 0) :
  matchesAt_pointRow_state (k := k) hk
    =
  MatchesAtState.ofRegister (k := k) (matchesAt_pointRow (k := k)) := by
  funext σ i pt
  simp [matchesAt_pointRow_state, MatchesAtState.ofRegister, matchesAt_pointRow]

lemma matchesAt_pointRow_state_irrel
  {k : Nat} (hk₁ hk₂ : k > 0) :
  matchesAt_pointRow_state (k := k) hk₁
    =
  matchesAt_pointRow_state (k := k) hk₂ := by
  funext σ i pt
  rfl

----------------------------------------------------------------------------------------------------
------------------------------- regEqExpected CHARACTERIZATION --------------------------------------
----------------------------------------------------------------------------------------------------

/-
  regEqExpected_eq_true_iff:

  Characterizes regEqExpected = true as pointwise equality with expectedRow.
  Used when converting a boolean match fact into equalities needed for evalRegister proofs
  (especially the `pt.inf` case which isolates a single coefficient).
-/
lemma regEqExpected_eq_true_iff {k : Nat} (r : Register k) (pt : Point) :
    regEqExpected (k := k) r pt = true ↔ ∀ j : Fin k, r j = expectedRow (k := k) pt j := by
  classical
  unfold regEqExpected
  constructor
  · intro h
    have hall := List.all_eq_true.mp h
    intro j
    have hj : j ∈ List.finRange k := by
      aesop
    have : decide (r j = expectedRow (k := k) pt j) = true := hall j hj
    aesop
  · intro h
    apply List.all_eq_true.mpr
    intro j hj
    have : r j = expectedRow (k := k) pt j := h j
    simp [this]

----------------------------------------------------------------------------------------------------
------------------------------- FIN HELPERS ---------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-
  lastFin_eq_some_of_pos:

  For k>0, lastFin k exists. This is used in the `pt.inf` case to pick out the last basis vector.
-/
lemma lastFin_eq_some_of_pos {k : Nat} (hk : k > 0) :
    ∃ last : Fin k, lastFin k = some last := by
  cases k with
  | zero =>
      cases hk
  | succ k' =>
      refine ⟨⟨k', by simp⟩, rfl⟩

/-
  finSum_unitSelector:

  Standard “delta selector” sum lemma:
    ∑ (if j=last then 1 else 0) * x j = x last
  Used in the `pt.inf` case when expectedRow is a unit vector at the last index.
-/
lemma finSum_unitSelector {k : Nat} (last : Fin k) (x : Fin k → Int) :
    (∑ j : Fin k, (if j = last then (1 : Int) else 0) * x j) = x last := by
  classical
  have hz : ∀ j : Fin k, j ≠ last → (if j = last then (1 : Int) else 0) * x j = 0 := by
    intro j hj
    simp [hj]
  aesop

----------------------------------------------------------------------------------------------------
------------------------------- stateToSt / regToInt FACTS ------------------------------------------
----------------------------------------------------------------------------------------------------

/-
  regToInt_stateToSt_eq_bmod:

  Expands regToInt(stateToSt σ ctx i) into a bmod form:
    evalRegister (σ i) ρ, reduced mod 2^w.

  This is the algebraic interface used to compare symbolic evaluation to the concrete
  integer stored in the bitvector, and it is used later to prove that interp matching
  corresponds to pointRow matching when FitsSignedAt holds.
-/
@[simp] lemma regToInt_stateToSt_eq_bmod
  {k : ℕ} (σ : Fin k → (Fin k → Int)) (ctx : StCtx k) (i : Fin k) :
  let w : Nat := ctx.baseW i + ctx.curLen.getD i.1 0
  regToInt (stateToSt (k := k) σ ctx i)
    =
  (evalRegister (σ i) ctx.ρ).bmod ((2 : Nat) ^ w) := by
  classical
  cases ctx with
  | mk ρ baseW curLen =>
    dsimp [stateToSt, regToInt]
    simp
    rw [BitVec.toInt_ofNat']
    simp
    have := Int.emod_nonneg (evalRegister (σ i) ρ)
      (b := 2 ^ (baseW i + curLen[i.val]?.getD 0)) (by simp)
    have :
        max ((evalRegister (σ i) ρ).emod (2 ^ (baseW i + curLen[i.val]?.getD 0))) 0
          =
        ((evalRegister (σ i) ρ).emod (2 ^ (baseW i + curLen[↑i]?.getD 0))) := by
      aesop

    simp_all
    set d := (evalRegister (σ i) ρ)
    set c := (baseW i + curLen[i]?.getD 0)
    have hc : (baseW i + curLen[i.val]?.getD 0) = c := by aesop
    rw [hc]
    change Int.bmod (d % (2 ^ c)) (2 ^ c) = d.bmod (2 ^ c)
    have := Int.emod_bmod d (2 ^ c)
    rw [← this]
    norm_cast

/-
  Int.bmod_eq_self_of_FitsSigned:

  If z fits in signed width w, then reducing z modulo 2^w (as Nat) returns z itself.
  This is the key step that lets the proof replace “stored bmod form” with the true
  integer value, whenever FitsSignedAt is available.
-/
lemma Int.bmod_eq_self_of_FitsSigned (w : Nat) (z : ℤ) (h : FitsSigned w z) :
    z.bmod ((2 : Nat) ^ w) = z := by
  rcases h with ⟨hwpos, hzlo, hzhi⟩
  cases w with
  | zero =>
      cases hwpos
  | succ w' =>
      have hzlo' : -( (2 : ℤ) ^ w') ≤ z := by simpa using hzlo
      have hzhi' : z < (2 : ℤ) ^ w' := by simpa using hzhi
      set a:=w'+1
      have hbmod_a : z.bmod (2^a) = z := by
        have h1 : (BitVec.ofInt a z).toInt = z := BitVec.toInt_ofInt_eq_self (w:=a) (by aesop) (by aesop) (by aesop)
        have h2 : (BitVec.ofInt a z).toInt = z.bmod (2^a) := by aesop
        exact by aesop
      assumption

/-
  regToInt_stateToSt_eq_eval_of_FitsSignedAt:

  Specialization: when FitsSignedAt holds at i, the bmod term collapses and
  regToInt(stateToSt ...) equals evalRegister exactly.

  This is used when converting row-matching hypotheses into interp-matching
  conclusions in the “pointRow ⇒ interp” lemma below.
-/
lemma regToInt_stateToSt_eq_eval_of_FitsSignedAt
  {k : ℕ} (σ : State k) (ctx : StCtx k) (i : Fin k)
  (hfit : FitsSignedAt (σ := σ) (ctx := ctx) i) :
  regToInt (stateToSt (k := k) σ ctx i) = evalRegister (σ i) ctx.ρ := by
  classical
  cases ctx with
  | mk ρ baseW curLen =>
    set w : Nat := stWidth (ctx := ⟨ρ, baseW, curLen⟩) i
    set z : ℤ := evalRegister (σ i) ρ
    have hbmod :
        regToInt (stateToSt (k := k) σ ⟨ρ, baseW, curLen⟩ i)
          =
        z.bmod ((2 : Nat) ^ w) := by
      aesop
    have hid : z.bmod ((2 : Nat) ^ w) = z := by
      have : FitsSigned w z := by
        simpa [FitsSignedAt, stWidth, w, z] using hfit
      exact Int.bmod_eq_self_of_FitsSigned w z this
    simpa [z] using hbmod.trans hid


lemma matchesAt_pointRow_state_implies_matchesAt_interp
  {k : Nat}
  (hk : k > 0)
  (σ : State k) (i : Fin k) (pt : Point)
  (σ0St : St k)
  (baseW : Fin k → Nat) (curLen : List Nat)
  (hfit :
    FitsSignedAt (σ := σ)
      (ctx := ⟨(fun j => regToInt (σ0St j)), baseW, curLen⟩) i)
  (hrow : matchesAt_pointRow_state (k := k) hk σ i pt = true) :
  matchesAt_interp (k := k) σ0St
    (stateToSt (k := k) σ ⟨(fun j => regToInt (σ0St j)), baseW, curLen⟩) i pt
    = true := by
  classical
  let ρinit : Fin k → ℤ := fun j => regToInt (σ0St j)

  have hcur :
      regToInt (stateToSt (k := k) σ ⟨ρinit, baseW, curLen⟩ i)
        =
      evalRegister (σ i) ρinit := by
    -- identical, just ctx-ified
    simpa [ρinit] using
      (regToInt_stateToSt_eq_eval_of_FitsSignedAt (k := k)
        (σ := σ) (ctx := ⟨ρinit, baseW, curLen⟩) (i := i) hfit)

  have hrow' : ∀ j : Fin k, σ i j = expectedRow (k := k) pt j := by
    have : regEqExpected (k := k) (σ i) pt = true := by
      simpa [matchesAt_pointRow_state] using hrow
    exact (regEqExpected_eq_true_iff (k := k) (r := σ i) (pt := pt)).1 this

  cases pt with
  | int z =>
      have ht :
          evalRegister (σ i) ρinit = polyEvalFromInit (k := k) σ0St z := by
        simp [evalRegister, polyEvalFromInit, expectedRow, ρinit, hrow']
      simp [matchesAt_interp, interpTarget]
      aesop

  | inf =>
      cases k with
      | zero =>
          cases hk
      | succ k' =>
          let last : Fin (Nat.succ k') := ⟨k', by simp⟩
          have ht :
              evalRegister (σ i) ρinit = regToInt (σ0St last) := by
            have hrowInf :
                ∀ j : Fin (Nat.succ k'), σ i j = (if j = last then (1 : ℤ) else 0) := by
              intro j
              aesop
            have hsum :
              (∑ j : Fin (Nat.succ k'), (if j = last then (1 : ℤ) else 0) * ρinit j) = ρinit last := by
              rw [Finset.sum_eq_single last]
              simp [expectedRow] at *
              intro b _ hb
              simp [hb]; aesop

            simp [evalRegister, ρinit, hrowInf, last]

          simp [matchesAt_interp, interpTarget, lastFin, ht, hcur, last, ρinit]



----------------------------------------------------------------------------------------------------
------------------------------- COVERAGE TRANSFER / AUX LEMMAS --------------------------------------
----------------------------------------------------------------------------------------------------

namespace PhaseProductCoverage

open Operations
open PhaseProduct_PrimOps

/-
  compile1_*_ops / compile1_*_noPhase:

  These are small “shape” lemmas about the compiler output for specific ops.
  They are used to prove `NoPhase` for prefixes generated by compile1 when the
  source op is *not* a phaseProduct, so that these prefixes can be prepended to
  a coverage proof without consuming points.

  In the main induction (compileProg_preserves_phaseCoverage_go):
  - if the head op is not phaseProduct, its compiled fragment has NoPhase
  - coverage for that fragment is trivial (consumes [])
  - then append tail coverage.
-/
lemma compile1_phaseProduct_ops
  {k : ℕ} (i : Fin k) (curLen : List Nat) :
  (compile1 (k := k) (.phaseProduct i) curLen).1 = [prim_ops.phaseProduct i] := by
  simp [compile1, compile_op_to_prim_single]

lemma compile1_shiftL_noPhase
  {k : ℕ} (i : Fin k) (n : Nat) (curLen : List Nat) :
  (compile1 (k := k) (.shiftL i n) curLen).1 = [prim_ops.Alloc i true n] := by
  simp [compile1, compile_op_to_prim_single]

lemma compile1_shiftR_noPhase
  {k : ℕ} (i : Fin k) (n : Nat) (curLen : List Nat) :
  (compile1 (k := k) (.shiftR i n) curLen).1 = [prim_ops.Free i true n] := by
  simp [compile1, compile_op_to_prim_single]

lemma compile1_negate_noPhase
  {k : ℕ} (i : Fin k) (curLen : List Nat) :
  (compile1 (k := k) (.negate i) curLen).1 = [prim_ops.negate i] := by
  simp [compile1, compile_op_to_prim_single]

/-
  ValidForStep.withCurLen:

  The phase-coverage proof threads contexts exactly like compileProg_simulates:
  after compiling/executing one op, the tail is proven under `{ctx0 with curLen := curLen1}`.

  This lemma transports the one-step invariant `ValidForStep ctx0` to the updated
  context with a different curLen field, so the induction can reuse the same step rule.
-/
lemma ValidForStep.withCurLen
  {k : ℕ} (ctx : StCtx k) (L : List Nat) :
  ValidForStep (k := k) ctx → ValidForStep (k := k) { ctx with curLen := L } := by
  intro h
  cases ctx with
  | mk ρ baseW curLen =>
    unfold ValidForStep at h ⊢
    intro σ σ1 op curLenNow
    simpa using (h (σ := σ) (σ1 := σ1) (op := op) (curLenNow := curLenNow))

/-
  interp_true_of_row_true:

  Converts a symbolic head match (regEqExpected / pointRow) into an interp match.

  This is needed to transfer the point consumption step from symbolic coverage:
    eraseFirstMatch? (matchesAt_pointRow_state ...) pts = some pts'
  into the primitive coverage form:
    eraseFirstMatchB (matchesAt_interp ...) pts = some pts'

  FitsSignedAt is required to ensure regToInt(stateToSt σ ...) equals evalRegister,
  so interpTarget computes the same value the pointRow matcher expects.
-/
lemma interp_true_of_row_true
  {k : ℕ} (hk : k > 0)
  (σinit : St k)
  (ctxNow : StCtx k)
  (σ : State k) (i : Fin k) (pt : Point)
  (hfit :
    FitsSignedAt (σ := σ)
      (ctx := ⟨(fun j => regToInt (σinit j)), ctxNow.baseW, ctxNow.curLen⟩) i)
  (hrow : regEqExpected (k := k) (σ i) pt = true) :
  matchesAt_interp (k := k) σinit
    (stateToSt (k := k) σ ⟨(fun j => regToInt (σinit j)), ctxNow.baseW, ctxNow.curLen⟩)
    i pt = true := by

  have hrow' :
    matchesAt_pointRow_state (k := k) hk σ i pt = true := by
    simpa [matchesAt_pointRow_state] using hrow
  simpa using
    (matchesAt_pointRow_state_implies_matchesAt_interp (k := k) (hk := hk)
      (σ := σ) (i := i) (pt := pt)
      (σ0St := σinit) (baseW := ctxNow.baseW) (curLen := ctxNow.curLen)
      (hfit := hfit) (hrow := hrow'))

/-
  eraseFirstMatchB_head_true:

  Small list lemma: if the predicate holds at the head element, eraseFirstMatchB
  removes that head and returns the tail.

  This is used for phaseProduct coverage steps that consume the first point of the list.
-/
@[simp] lemma eraseFirstMatchB_head_true {α} (p : α → Bool) (x : α) (xs : List α)
  (hx : p x = true) :
  eraseFirstMatchB p (x :: xs) = some xs := by
  simp [eraseFirstMatchB, hx]

/-
  eraseFirstMatchB_interp_head:

  Specializes eraseFirstMatchB_head_true to the interp predicate.
  This is the exact consumption statement needed by the primitive coverage constructor
  PhaseProductCoverageM_prim.step_phase, in the situation where the matching point is the head.
-/
lemma eraseFirstMatchB_interp_head
  {k : ℕ} (hk : k > 0)
  (σinit : St k)
  (ctxNow : StCtx k)
  (σ : State k) (i : Fin k)
  (pt : Point) (ptsTail : List Point)
  (hfit :
    FitsSignedAt (σ := σ)
      (ctx := ⟨(fun j => regToInt (σinit j)), ctxNow.baseW, ctxNow.curLen⟩) i)
  (hrow : regEqExpected (k := k) (σ i) pt = true) :
  eraseFirstMatchB
      (fun q =>
        matchesAt_interp (k := k) σinit
          (stateToSt (k := k) σ ⟨(fun j => regToInt (σinit j)), ctxNow.baseW, ctxNow.curLen⟩)
          i q)
      (pt :: ptsTail)
    = some ptsTail := by
  have hinterp :
    matchesAt_interp (k := k) σinit
      (stateToSt (k := k) σ ⟨(fun j => regToInt (σinit j)), ctxNow.baseW, ctxNow.curLen⟩)
      i pt = true :=
    interp_true_of_row_true (k := k) hk σinit ctxNow σ i pt hfit hrow
  simp [eraseFirstMatchB, hinterp]

/-
  PhaseConsumeOK:

  Bundles the “consumption transfer” property into a reusable statement.
  It says: whenever the symbolic side consumes a point under matchesAt_pointRow_state,
  the primitive side consumes the same point under matchesAt_interp.

  This is exactly what is needed in step_phase cases of the main induction.
-/
def PhaseConsumeOK {k : ℕ}
  (hk : k > 0) (σinit : St k) (ctx0 : StCtx k) : Prop :=
  ∀ (σ : State k) (i : Fin k) (curLenNow : List Nat)
    (pts pts' : List Operations.Point),
    ValidFor (k := k) σ { ctx0 with curLen := curLenNow } →
    List.eraseFirstMatch?
        (fun pt => matchesAt_pointRow_state (k := k) hk σ i pt) pts = some pts' →
    eraseFirstMatchB
        (fun pt =>
          matchesAt_interp (k := k) σinit
            (stateToSt (k := k) σ { ctx0 with curLen := curLenNow }) i pt)
        pts = some pts'

/-
  consume_transfer_pointRow_to_interp:

  Concrete version of PhaseConsumeOK for the “head point matches” case (pts = pt :: pts').
  It uses FitsSignedAt and the ρ-alignment hypothesis to replace ctx.ρ with regToInt σinit,
  then applies matchesAt_pointRow_state_implies_matchesAt_interp and eraseFirstMatchB_head_true.
-/
lemma consume_transfer_pointRow_to_interp
  {k : ℕ} (hk : k > 0)
  (σinit : St k)
  (ctx:StCtx k)
  (σ : State k) (i : Fin k)
  (pt: Operations.Point)
  (pts pts' : List Operations.Point)
  (hpt: pts=pt::pts')
  (hmatch: matchesAt_pointRow_state (k := k) hk σ i pt)
  (hfit : FitsSignedAt (σ := σ)
          (ctx := ⟨(fun j => regToInt (σinit j)), ctx.baseW, ctx.curLen⟩) i)
  (hρ : ctx.ρ = fun j ↦ regToInt (σinit j))
      :
  eraseFirstMatchB (fun pt => matchesAt_interp (k := k) σinit (stateToSt σ ctx) i pt) pts
    = some pts' := by
  subst hpt
  have hinterp :
      matchesAt_interp (k := k) σinit (stateToSt (k := k) σ ctx) i pt = true := by
    have:= (matchesAt_pointRow_state_implies_matchesAt_interp
        (k := k) hk
        (σ := σ) (i := i) (pt := pt)
        (σ0St := σinit)
        (baseW := ctx.baseW) (curLen := ctx.curLen)
        (hfit := hfit)
        (hrow := hmatch))
    have : stateToSt σ ctx =
      stateToSt σ { ρ := fun j ↦ regToInt (σinit j), baseW := ctx.baseW, curLen := ctx.curLen } := by
      cases ctx ; simp_all
    simp_all
  simpa using
    (eraseFirstMatchB_head_true
      (p := fun pt => matchesAt_interp (k := k) σinit (stateToSt (k := k) σ ctx) i pt)
      (x := pt) (xs := pts') hinterp)

/-
  MatchFirstPhase / ProgConsumesPts:

  These predicates describe how the symbolic program consumes points:
  - MatchFirstPhase checks that the first phaseProduct encountered matches the head point.
  - ProgConsumesPts is the full consumption trace: every phaseProduct consumes one point.

  compileProg_preserves_phaseCoverage_go assumes ProgConsumesPts to drive the phase-product
  consumption part of the primitive coverage proof.
-/
def MatchFirstPhase {k : ℕ} (hk : k > 0) : State k → Prog k → List Point → Prop
| _σ, [], _pts => True
| σ, op :: ops, pts =>
  match op with
  | valid_ops.phaseProduct i =>
      match pts with
      | [] => False
      | pt :: _ => matchesAt_pointRow_state (k := k) hk σ i pt = true
  | _ =>
      ∃ σ', applyOp? (k := k) σ op = some σ' ∧
            MatchFirstPhase hk σ' ops pts

def ProgConsumesPts {k : ℕ} (hk : k > 0) : State k → Prog k → List Point → Prop
| _σ, [], pts => pts = []
| σ, op :: ops, pts =>
  match op with
  | valid_ops.phaseProduct i =>
      ∃ pt ptsTail,
        pts = pt :: ptsTail ∧
        matchesAt_pointRow_state (k := k) hk σ i pt = true ∧
        ProgConsumesPts hk σ ops ptsTail
  | _ =>
      ∃ σ', applyOp? (k := k) σ op = some σ' ∧
            ProgConsumesPts hk σ' ops pts

/-
  NoPhase_compile1_of_not_phaseProduct:

  If the validated op is not a phaseProduct, then compile1 emits a primitive fragment
  with NoPhase. This is used in the step_op case of the main induction to build trivial
  prefix coverage consuming [].
-/
lemma NoPhase_compile1_of_not_phaseProduct
  {k : ℕ} (op : valid_ops k) (curLen : List Nat)
  (hne : (∀ i, op ≠ valid_ops.phaseProduct i)) :
  NoPhase (k := k) (compile1 (k := k) op curLen).1 := by
  cases op <;> simp [compile1, compile_op_to_prim_single, PhaseProduct_PrimOps.NoPhase]
  ·  split_ifs<;>simp [PhaseProduct_PrimOps.NoPhase]
  · simp_all

/-
  compileProg_cons_phaseProduct:

  Shape lemma: if the head validated op is phaseProduct, compileProg emits a primitive
  phaseProduct at the front and threads the same curLen into the tail compilation.
  Used to split PrimOKTrace and to structure the step_phase proof cases.
-/
@[simp] lemma compileProg_cons_phaseProduct
  {k : ℕ} (i : Fin k) (ps : Prog k) (curLen : List Nat) :
  compileProg (k := k) (valid_ops.phaseProduct i :: ps) curLen
    =
  let cp := compileProg (k := k) ps curLen
  ([prim_ops.phaseProduct i] ++ cp.1, cp.2) := by
  simp [compileProg, compile1_phaseProduct]

/-
  PrimOKTrace_tail_of_cons_phaseProduct:

  When compileProg emits a leading [phaseProduct i] ++ tail, PrimOKTrace on the full program
  implies PrimOKTrace on the tail (since phaseProduct does not change bookkeeping context).
  This is used in the step_phase case to recover the safety hypothesis needed for the IH.
-/
lemma PrimOKTrace_tail_of_cons_phaseProduct
  {k : ℕ} (i : Fin k) (ps : Prog k) (curLen : List Nat) (ctx : StCtx k)
  (hPrim : PrimOKTrace (k := k)
      (compileProg (k := k) (valid_ops.phaseProduct i :: ps) curLen).1
      { ctx with curLen := curLen }) :
  PrimOKTrace (k := k)
    (compileProg (k := k) ps curLen).1
    { ctx with curLen := curLen } := by
  -- rewrite the compiled program as ([phaseProduct] ++ tail)
  simp at hPrim
  -- now split trace
  have hs :=
    PrimOKTrace.append_inv (k := k) [prim_ops.phaseProduct i]
      (compileProg (k := k) ps curLen).1
      ({ ctx with curLen := curLen }) hPrim
  -- hs.2 is a trace starting in runCtxPrim ctx [phaseProduct i], but phaseProduct leaves ctx unchanged
  have hctx :
      runCtxPrim (k := k) ({ ctx with curLen := curLen }) [prim_ops.phaseProduct i]
        = { ctx with curLen := curLen } := by
    simp [runCtxPrim, stepCtxPrim]
  simpa [hctx] using hs.2

/-
  eraseFirstMatchB_of_phaseConsume:

  Transfers the consumption result for a phaseProduct op from the symbolic matcher
  (eraseFirstMatch? over matchesAt_pointRow_state) to the primitive matcher
  (eraseFirstMatchB over matchesAt_interp), in the specific situation where
  ProgConsumesPts guarantees the head point matches.

  This lemma is used in step_phase cases of the main induction when constructing the
  PhaseProductCoverageM_prim.step_phase constructor.
-/
lemma eraseFirstMatchB_of_phaseConsume
  {k : ℕ} (hk : k > 0)
  (σinit : St k)
  (ctx0 : StCtx k) (curLenNow : List Nat)
  (σ1 : State k) (i : Fin k)
  (pts1 pts2 : List Point)
  (hV : ValidFor (k := k) σ1 { ctx0 with curLen := curLenNow })
  (hρ : ctx0.ρ = fun j => regToInt (σinit j))
  (hConsume : ProgConsumesPts hk σ1 (valid_ops.phaseProduct i :: ([] : Prog k)) pts1)
  (hconsume : List.eraseFirstMatch?
      (fun pt => matchesAt_pointRow_state (k := k) hk σ1 i pt) pts1 = some pts2) :
  eraseFirstMatchB
      (fun pt =>
        matchesAt_interp (k := k) σinit
          (stateToSt (k := k) σ1 { ctx0 with curLen := curLenNow }) i pt)
      pts1
    = some pts2 := by
  -- unpack ProgConsumesPts for a phaseProduct head: pts1 = pt :: ptsTail and head matches
  simp [ProgConsumesPts] at hConsume
  rcases hConsume with ⟨pt,hConsume⟩
  rcases hConsume with ⟨hpts1, hrow⟩
  subst hpts1
   -- turn hrow into the pointRow boolean
  have hrowPR :
      matchesAt_pointRow_state (k := k) hk σ1 i pt = true := by
    simpa [matchesAt_pointRow_state_apply] using hrow

  -- compute pts2 from the eraseFirstMatch? fact on a singleton list
  have hpts2 : pts2 = [] := by
    have : List.eraseFirstMatch?
        (fun q ↦ matchesAt_pointRow_state (k := k) hk σ1 i q) [pt]
        = some ([] : List Point) := by
      simp [List.eraseFirstMatch?, hrow]
    exact Option.some.inj (by simp at hconsume; aesop)
  subst hpts2

  -- get FitsSignedAt from ValidFor, rewriting ρ using hρ
  have hfit :
      FitsSignedAt (σ := σ1)
        (ctx := ⟨(fun j => regToInt (σinit j)), ctx0.baseW, curLenNow⟩) i := by
    simpa [hρ] using (hV.fits_all i)

  -- apply interp-head eraser lemma
  have : eraseFirstMatchB
      (fun q =>
        matchesAt_interp (k := k) σinit
          (stateToSt (k := k) σ1 ⟨(fun j => regToInt (σinit j)), ctx0.baseW, curLenNow⟩) i q)
      (pt :: [])
    = some [] := by
    simpa using
      eraseFirstMatchB_interp_head
        (k := k) (hk := hk)
        (σinit := σinit)
        (ctxNow := ⟨(fun j => regToInt (σinit j)), ctx0.baseW, curLenNow⟩)
        (σ := σ1) (i := i) (pt := pt) (ptsTail := [])
        (hfit := hfit) (hrow := hrow)

  -- rewrite ctx back to ctx0 using hρ and finish
  simpa [hρ, stateToSt] using this

/-
  PhaseProductCoverageM_prim_of_NoPhase:

  If a primitive program contains no phaseProduct ops, then it has primitive coverage
  consuming the empty point list. This is the “trivial prefix coverage” lemma used in
  step_op cases of the main induction.
-/
lemma PhaseProductCoverageM_prim_of_NoPhase
  {k : ℕ} {M : MatchesAtStateBit k}
  (opsP : List (prim_ops k)) (σ : St k)
  (hNo : PhaseProduct_PrimOps.NoPhase (k := k) opsP) :
  PhaseProductCoverageM_prim (k := k) M opsP σ [] := by
  have hrest : PhaseProductCoverageM_prim (k := k) M ([] : List (prim_ops k))
                (eval_prim_ops (k := k) opsP σ) [] := by
    simpa using (PhaseProductCoverageM_prim.nil (k := k) (M := M) (σ := eval_prim_ops (k := k) opsP σ))
  have := PhaseProduct_PrimOps.PhaseProductCoverageM.prepend_noPhase
      (k := k) (M := M) (opsP := opsP) (ps := []) (σ := σ) (pts := [])
      hNo hrest
  simpa using this

end PhaseProductCoverage

----------------------------------------------------------------------------------------------------
------------------------------- MAIN THEOREMS -------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace PhaseProductCoverage

open Operations
open PhaseProduct_PrimOps

/-
  compileProg_preserves_phaseCoverage_go:

  Main induction that builds primitive phase coverage for the compiled program.

  Inputs:
  - symbolic phase coverage (PhaseProductCoverage hk ops σ pts)
  - ValidFor + ValidForStep: numeric invariant and its one-step preservation
  - PrimOKTrace: primitive safety needed to justify bridge steps
  - ProgConsumesPts: explicit witness that the symbolic program consumes pts in order
  - ρ alignment: ctx0.ρ matches the initial concrete state σinit via regToInt

  Output:
  - primitive coverage for the compiled primitive program opsP starting from stateToSt σ ctxNow.
-/
theorem compileProg_preserves_phaseCoverage_go
  {k : ℕ}
  (hk : k > 0)
  (σinit : St k)
  (ops : List (valid_ops k))
  (σ : State k)
  (ctx0 : StCtx k)
  (curLenNow : List Nat)
  (hWF : Prog.WellFormed ops)
  (pts : List Operations.Point)
  (hcov : PhaseProductCoverage (k := k) hk ops σ pts)
  (hV : ValidFor (k := k) σ { ctx0 with curLen := curLenNow })
  (hStep : ValidForStep (k := k) ctx0)
  (hPrim : PrimOKTrace (compileProg (k := k) ops curLenNow).1 { ctx0 with curLen := curLenNow })
  (hConsume : ProgConsumesPts hk σ ops pts)
  (hρ : ctx0.ρ = fun j => regToInt (σinit j))
  :
  let ctxNow : StCtx k := { ctx0 with curLen := curLenNow }
  let (opsP, _) := compileProg (k := k) ops curLenNow
  PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
    σinit opsP (stateToSt (k := k) σ ctxNow) pts := by
  classical

  unfold PhaseProductCoverage at hcov
  induction hcov generalizing curLenNow ctx0 with
  | nil =>
      simp [compileProg, PhaseProduct_PrimOps.PhaseProductCoverage_prim,
            PhaseProduct_PrimOps.PhaseProductCoverageM_prim.nil]

  | step_op hstep hrest ih =>
    simp_all
    rename_i op ops2 σ0 σ1 pts2 ih'
    set ctxNow : StCtx k := { ρ := ctx0.ρ, baseW := ctx0.baseW, curLen := curLenNow }

    -- Name the compiled pieces for the head op and the tail program.
    set ops1 : List (prim_ops k) := (compile1 (k := k) op curLenNow).1
    set curLen1 : List Nat := (compile1 (k := k) op curLenNow).2
    set cp2 : (List (prim_ops k) × List Nat) := compileProg (k := k) ops2 curLen1
    set opsP2 : List (prim_ops k) := cp2.1

    -- Tail consumption witness extracted from ProgConsumesPts.
    have hConsumeTail : ProgConsumesPts hk σ1 ops2 pts2 := by
      cases op with
      | phaseProduct i =>
          exfalso
          exact hstep i rfl
      | shiftL i n =>
          simp [ProgConsumesPts] at hConsume
          rcases hConsume with ⟨σ', hσ', ht⟩
          have : σ' = σ1 := Option.some.inj (by simpa [hσ'] using hrest)
          simpa [this] using ht
      | shiftR i n =>
          simp [ProgConsumesPts] at hConsume
          rcases hConsume with ⟨σ', hσ', ht⟩
          have : σ' = σ1 := Option.some.inj (by simpa [hσ'] using hrest)
          simpa [this] using ht
      | negate i =>
          simp [ProgConsumesPts] at hConsume
          rcases hConsume with ⟨σ', hσ', ht⟩
          have : σ' = σ1 := Option.some.inj (by simpa [hσ'] using hrest)
          simpa [this] using ht
      | addScaled dst src negSrc sh =>
          simp [ProgConsumesPts] at hConsume
          unfold applyOp? at hrest; simp at hrest
          rw [hrest] at hConsume
          apply hConsume

    -- WellFormed splits into head-op OK and tail program WellFormed.
    have hopOK : Prog.OpOK (k := k) op := by
      simp [Prog.WellFormed] at hWF; apply hWF.left
    have hWF_tail : Prog.WellFormed (k := k) ops2 := by
      simp [Prog.WellFormed] at hWF; apply hWF.right

    -- ValidFor after stepping the symbolic state (and updating curLen to curLen1).
    have hV1 : ValidFor (k := k) σ1 { ctx0 with curLen := curLen1 } := by
      apply hStep σ0 σ1 op curLenNow hrest hopOK
      aesop

    -- Split PrimOKTrace for ops1 ++ opsP2 into head and tail traces.
    have hPrim_all :
        PrimOKTrace (k := k) (ops1 ++ opsP2) { ctx0 with curLen := curLenNow } := by
      simp [ops1, opsP2, cp2, curLen1] at hPrim
      aesop

    have hPrim_split :
        PrimOKTrace (k := k) ops1 { ctx0 with curLen := curLenNow } ∧
        PrimOKTrace (k := k) opsP2
          (runCtxPrim (k := k) ({ ctx0 with curLen := curLenNow }) ops1) := by
      exact PrimOKTrace.append_inv (k := k) ops1 opsP2 ({ ctx0 with curLen := curLenNow }) hPrim_all

    have hPrim1 : PrimOKTrace (k := k) ops1 { ctx0 with curLen := curLenNow } := hPrim_split.1
    have hPrim2_raw :
        PrimOKTrace (k := k) opsP2
          (runCtxPrim (k := k) ({ ctx0 with curLen := curLenNow }) ops1) := hPrim_split.2

    -- Identify the threaded context after ops1 with `{ctx0 with curLen := curLen1}`.
    have hCtx1 :
        runCtxPrim (k := k) ({ ctx0 with curLen := curLenNow }) ops1
          = { ctx0 with curLen := curLen1 } := by
      have := runCtxPrim_compile1 (k := k) op ({ ctx0 with curLen := curLenNow })
      simpa [ops1, curLen1] using this

    have hPrim2 : PrimOKTrace (k := k) opsP2 { ctx0 with curLen := curLen1 } := by
      simpa [hCtx1] using hPrim2_raw

    -- Transport ValidForStep to the context whose curLen field matches curLenNow.
    have hStepNow : ValidForStep (k := k) ({ ctx0 with curLen := curLenNow }) :=
      PhaseProductCoverage.ValidForStep.withCurLen (k := k) ctx0 curLenNow hStep

    -- Head simulation: compiled ops1 evaluates to the same stateToSt of the stepped symbolic state.
    have hsim :
        eval_prim_ops (k := k) ops1
            (stateToSt (k := k) σ0 { ctx0 with curLen := curLenNow })
          =
        stateToSt (k := k) σ1 { ctx0 with curLen := curLen1 } := by
      have := compile1_simulates (k := k)
        (op := op)
        (σ := σ0) (ctx := { ctx0 with curLen := curLenNow })
        (hV := by aesop) (hV_step := hStepNow)
        (hPrim := by simpa [ops1] using hPrim1)
        (σ2 := σ1) (hstep := hrest) (hOK := hopOK)
      simpa [ops1, curLen1] using this

    -- Tail coverage from IH (starting at the stepped symbolic state and updated curLen).
    have htail :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit opsP2
          (stateToSt (k := k) σ1 { ctx0 with curLen := curLen1 }) pts2 := by
      have := ih' (ctx0 := ctx0) (curLenNow := curLen1) (hρ:=hρ)
        hWF_tail hV1 hStep
        (by simpa [opsP2, cp2] using hPrim2)
        hConsumeTail
      aesop

    -- Rewrite tail start state to eval_prim_ops ops1 ... using hsim.
    have htail' :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit opsP2
          (eval_prim_ops (k := k) ops1
            (stateToSt (k := k) σ0 { ctx0 with curLen := curLenNow })) pts2 := by
      simpa [hsim] using htail

    -- Align the ρ field in stateToSt using hρ (needed so matchesAt_interp uses σinit).
    have hstart :
        stateToSt (k := k) σ0
          { ρ := fun j ↦ regToInt (σinit j),
            baseW := ctx0.baseW, curLen := curLenNow }
        =
        stateToSt (k := k) σ0
          { ρ := ctx0.ρ,
            baseW := ctx0.baseW, curLen := curLenNow } := by
      simp [hρ]

    -- NoPhase for the compiled head fragment ops1 (since the head validated op is not phaseProduct).
    have hNo : PhaseProduct_PrimOps.NoPhase (k := k) ops1 := by
      have hne : ∀ i, op ≠ valid_ops.phaseProduct i := by
        intro i hi; exact hstep i (by simp[hi])
      simpa [ops1] using
        NoPhase_compile1_of_not_phaseProduct (k := k) (op := op) (curLen := curLenNow) hne

    -- Trivial coverage for a NoPhase prefix consumes no points.
    have hpref :
        PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σinit)
          ops1
          (stateToSt (k := k) σ0 { ρ := ctx0.ρ, baseW := ctx0.baseW, curLen := curLenNow })
          [] := by
      exact PhaseProductCoverageM_prim_of_NoPhase (k := k)
        (M := matchesAt_interp (k := k) σinit)
        ops1
        (stateToSt (k := k) σ0 { ρ := ctx0.ρ, baseW := ctx0.baseW, curLen := curLenNow })
        hNo

    -- Unwrap the tail coverage into the monadic form needed for append.
    have htailM :
        PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σinit)
          opsP2
          (eval_prim_ops (k := k) ops1
            (stateToSt (k := k) σ0 { ρ := ctx0.ρ, baseW := ctx0.baseW, curLen := curLenNow }))
          pts2 := by
      simpa [PhaseProduct_PrimOps.PhaseProductCoverage_prim] using htail'

    -- Append prefix and tail coverages: ops1 consumes [], opsP2 consumes pts2.
    have happ :
        PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σinit)
          (ops1 ++ opsP2)
          (stateToSt (k := k) σ0 { ρ := ctx0.ρ, baseW := ctx0.baseW, curLen := curLenNow })
          ([] ++ pts2) := by
      exact PhaseProductCoverageM_prim_append (k := k)
        (M := matchesAt_interp (k := k) σinit)
        (hp := hpref)
        (hq := htailM)

    -- Rewrap and clean up [] ++ pts2, then rewrite start state via hstart.
    have happ' :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit (ops1 ++ opsP2)
          (stateToSt (k := k) σ0 { ρ := ctx0.ρ, baseW := ctx0.baseW, curLen := curLenNow })
          pts2 := by
      simpa [PhaseProduct_PrimOps.PhaseProductCoverage_prim] using (by simpa using happ)

    simpa [hstart] using happ'

  | step_phase hconsume hrest ih =>
      -- Head validated op is phaseProduct: primitive compilation emits a leading prim phaseProduct.
      rename_i i ops2 σ1 pts1 pts2

      -- Extract the tail consumption witness from ProgConsumesPts.
      have hConsTail : ProgConsumesPts hk σ1 ops2 pts2 := by
        simp [ProgConsumesPts] at hConsume
        rcases hConsume with ⟨pt, ptsTail, hpts1, hrow, hCtail⟩

        have hconsume_head :
            List.eraseFirstMatch?
              (fun q => matchesAt_pointRow_state (k := k) hk σ1 i q) (pt :: ptsTail)
            = some ptsTail := by
          simp [List.eraseFirstMatch?, hrow]

        have : pts2 = ptsTail := by
          subst hpts1
          exact Option.some.inj (by simp at hconsume; aesop)

        subst this
        exact hCtail

      -- Tail WellFormed for IH.
      have hWF_tail : Prog.WellFormed (k := k) ops2 := by
        simp [Prog.WellFormed] at hWF; apply hWF.right

      -- Remove the leading phaseProduct from PrimOKTrace to obtain tail safety.
      simp [PhaseProduct_PrimOps.PhaseProductCoverage_prim]
      have hPrimTail :
          PrimOKTrace (k := k) (compileProg (k := k) ops2 curLenNow).1
            { ctx0 with curLen := curLenNow } := by
        simpa using
          PrimOKTrace_tail_of_cons_phaseProduct (k := k) i ops2 curLenNow ctx0
            (by simpa using hPrim)

      -- Unpack the head point match and identify pts2 after consumption.
      simp [ProgConsumesPts] at hConsume
      rcases hConsume with ⟨pt, ptsTail, hpts1, hrow, hConsumeTail⟩
      subst hpts1

      have hconsume_head :
          List.eraseFirstMatch?
            (fun q => matchesAt_pointRow_state (k := k) hk σ1 i q) (pt :: ptsTail)
          = some ptsTail := by
        simp [List.eraseFirstMatch?, hrow]
      have hpts2 : pts2 = ptsTail := by
        exact Option.some.inj (by aesop)
      subst hpts2

      -- Tail coverage from IH.
      have htail :
          PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
            σinit (compileProg (k := k) ops2 curLenNow).1
            (stateToSt (k := k) σ1 { ctx0 with curLen := curLenNow }) pts2 := by
        simpa using
          ih (ctx0 := ctx0) (curLenNow := curLenNow)
            hWF_tail hV hStep hPrimTail hConsumeTail hρ

      -- Build eraseFirstMatchB fact for the head phaseProduct using FitsSignedAt and matcher transfer.
      have hfit :
          FitsSignedAt (σ := σ1)
            (ctx := ⟨(fun j => regToInt (σinit j)), ctx0.baseW, curLenNow⟩) i := by
        simpa [hρ] using (hV.fits_all i)

      have hrow' : regEqExpected (k := k) (σ1 i) pt = true := by
        simpa using hrow

      have hb :
          eraseFirstMatchB
            (fun q =>
              matchesAt_interp (k := k) σinit
                (stateToSt (k := k) σ1
                  { ctx0 with curLen := curLenNow }) i q)
            (pt :: pts2)
          = some pts2 := by
        have := PhaseProductCoverage.eraseFirstMatchB_interp_head
            (k := k) (hk := hk)
            (σinit := σinit)
            (ctxNow := { ctx0 with curLen := curLenNow })
            (σ := σ1) (i := i) (pt := pt) (ptsTail := pts2)
            (hfit := hfit) (hrow := hrow')
        aesop

      -- Convert into PhaseProductCoverageM_prim: head consumes pt, tail consumes pts2.
      simp_all [PhaseProduct_PrimOps.PhaseProductCoverage_prim]
      change PhaseProductCoverageM_prim (matchesAt_interp σinit)
        ([prim_ops.phaseProduct i] ++ (compileProg ops2 curLenNow).1)
        (stateToSt σ1 { ρ := fun j ↦ regToInt (σinit j), baseW := ctx0.baseW, curLen := curLenNow })
        ([pt] ++ pts2)

      set σ0 : St k :=
        stateToSt (k := k) σ1
          { ρ := fun j ↦ regToInt (σinit j), baseW := ctx0.baseW, curLen := curLenNow }

      -- Tail coverage as a monadic coverage statement.
      have htail :
          PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σinit)
            (compileProg (k := k) ops2 curLenNow).1
            σ0 pts2 := by
        simpa [σ0] using
          ih (ctx0 := ctx0) (curLenNow := curLenNow) (by aesop) hStep (by aesop) hρ

      -- Coverage for the singleton prefix [phaseProduct i] consuming [pt].
      have hpref :
      PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σinit)
        [prim_ops.phaseProduct i] σ0 [pt] := by
        have hb1 :
            eraseFirstMatchB (fun q => matchesAt_interp (k := k) σinit σ0 i q) [pt]
              = some ([] : List Point) := by
          have hinterp :
              matchesAt_interp (k := k) σinit σ0 i pt = true := by
            have : matchesAt_interp (k := k) σinit
                (stateToSt (k := k) σ1
                  { ρ := fun j ↦ regToInt (σinit j), baseW := ctx0.baseW, curLen := curLenNow })
                i pt = true := by
              exact PhaseProductCoverage.interp_true_of_row_true
                (k := k) (hk := hk) (σinit := σinit)
                (ctxNow := { ρ := fun j ↦ regToInt (σinit j), baseW := ctx0.baseW, curLen := curLenNow })
                (σ := σ1) (i := i) (pt := pt) (hfit := hfit) (hrow := hrow')
            simpa [σ0] using this
          simpa using
            (PhaseProductCoverage.eraseFirstMatchB_head_true
              (p := fun q => matchesAt_interp (k := k) σinit σ0 i q)
              (x := pt) (xs := ([] : List Point)) hinterp)

        refine PhaseProductCoverageM_prim.step_phase (k := k)
          (M := matchesAt_interp (k := k) σinit) (i := i)
          (pts := [pt]) (pts' := []) ?_ ?_
        · exact hb1
        · simpa using (PhaseProductCoverageM_prim.nil (k := k) (M := matchesAt_interp (k := k) σinit) (σ := σ0))

      -- Append prefix and tail coverages (phaseProduct does not change σ0).
      have happend :
          PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σinit)
            ([prim_ops.phaseProduct i] ++ (compileProg (k := k) ops2 curLenNow).1)
            σ0 ([pt] ++ pts2) := by
        exact PhaseProductCoverageM_prim_append (k := k)
          (M := matchesAt_interp (k := k) σinit)
          (hp := hpref)
          (hq := by
            simpa [eval_prim_ops, eval_prim_op_single, σ0] using htail)

      simpa [σ0] using happend

/-
  compileProg_preserves_phaseCoverage:

  Final specialization of the “go” theorem to start_state.

  Inputs match the typical pipeline assumptions:
  - ops well-formed
  - symbolic coverage for State.start_state
  - ValidFor at start_state
  - one-step validity preservation (ValidForStep)
  - primitive safety trace for compileProg output (PrimOKTrace)
  - explicit point consumption witness (ProgConsumesPts)
  - alignment of ctx0.ρ with regToInt of the initial concrete state (stateToSt start_state ctx0)

  Output:
  - phase coverage for the compiled program starting from the initial concrete state.
-/
theorem compileProg_preserves_phaseCoverage
  {k : ℕ}
  (hk : k > 0)
  (ops : List (valid_ops k))
  (ctx0 : StCtx k)
  (hOK : Prog.WellFormed ops)
  (pts : List Operations.Point)
  (hcov : PhaseProductCoverage (k := k) hk ops State.start_state pts)
  (hV0 : ValidFor (k := k) State.start_state ctx0)
  (hStep : ValidForStep (k := k) ctx0)
  (hPrim : PrimOKTrace (compileProg (k := k) ops ctx0.curLen).1 ctx0)
  (hConsume : ProgConsumesPts hk State.start_state ops pts)
  (hρ : ctx0.ρ = fun j ↦ regToInt (stateToSt State.start_state ctx0 j))
  :
  PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
    (stateToSt (k := k) State.start_state ctx0)
    (compileProg (k := k) ops ctx0.curLen).1
    (stateToSt (k := k) State.start_state ctx0)
    pts := by
    apply compileProg_preserves_phaseCoverage_go
    apply hOK; apply hcov; apply hV0; apply hStep; apply hPrim; apply hConsume; apply hρ

end PhaseProductCoverage
