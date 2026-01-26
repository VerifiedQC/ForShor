import FastMultiplication.Allocate_dealloc.Bridge_lemmas
import FastMultiplication.Allocate_dealloc.PhaseCoverage


namespace PhaseProduct_PrimOps

----------------------------------------------------------------------------------------------------
------------------------------- NO-PHASE PREFIX LEMMA ----------------------------------------------
----------------------------------------------------------------------------------------------------

def NoPhase {k : ℕ} : List (prim_ops k) → Prop
  | [] => True
  | prim_ops.phaseProduct _ :: _ => False
  | _ :: xs => NoPhase xs

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
      -- `eraseFirstMatchB p xs = some t` and ys = x :: t
      cases hxs : eraseFirstMatchB p xs with
      | none =>
          simp [hx, hxs] at h
      | some t =>
          -- from h, we learn ys = x :: t
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

/-- “Returns to σ” -/
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

def PhaseProductCoverage_prim {k : ℕ}
    (prog : List (prim_ops k)) (σ0 : St k) (pts : List Operations.Point) : Prop :=
  PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σ0) prog σ0 pts

----------------------------------------------------------------------------------------------------
------------------------------- COMPILER SIMP LEMMAS ------------------------------------------------
----------------------------------------------------------------------------------------------------

@[simp] lemma compile1_phaseProduct
  {k : ℕ} (i : Fin k) (curLen : List Nat) :
  compile1 (k := k) (valid_ops.phaseProduct i) curLen
    = ([prim_ops.phaseProduct i], curLen) := by
  simp [compile1, compile_op_to_prim_single]

----------------------------------------------------------------------------------------------------
------------------------------- POINT-ROW MATCHER FACTS --------------------------------------------
----------------------------------------------------------------------------------------------------

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

lemma lastFin_eq_some_of_pos {k : Nat} (hk : k > 0) :
    ∃ last : Fin k, lastFin k = some last := by
  cases k with
  | zero =>
      cases hk
  | succ k' =>
      refine ⟨⟨k', by simp⟩, rfl⟩

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

----------------------------------------------------------------------------------------------------
------------------------------- pointRow ⇒ interp (WITH FITS) ---------------------------------------
----------------------------------------------------------------------------------------------------

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

lemma ValidForStep.withCurLen
  {k : ℕ} (ctx : StCtx k) (L : List Nat) :
  ValidForStep (k := k) ctx → ValidForStep (k := k) { ctx with curLen := L } := by
  intro h
  cases ctx with
  | mk ρ baseW curLen =>
    unfold ValidForStep at h ⊢
    intro σ σ1 op curLenNow
    simpa using (h (σ := σ) (σ1 := σ1) (op := op) (curLenNow := curLenNow))

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

@[simp] lemma eraseFirstMatchB_head_true {α} (p : α → Bool) (x : α) (xs : List α)
  (hx : p x = true) :
  eraseFirstMatchB p (x :: xs) = some xs := by
  simp [eraseFirstMatchB, hx]

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
| _σ, [], pts => pts = []   -- or `True` if you allow leftover points
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

lemma NoPhase_compile1_of_not_phaseProduct
  {k : ℕ} (op : valid_ops k) (curLen : List Nat)
  (hne : (∀ i, op ≠ valid_ops.phaseProduct i)) :
  NoPhase (k := k) (compile1 (k := k) op curLen).1 := by
  cases op <;> simp [compile1, compile_op_to_prim_single, PhaseProduct_PrimOps.NoPhase]
  ·  split_ifs<;>simp [PhaseProduct_PrimOps.NoPhase]
  · simp_all

@[simp] lemma compileProg_cons_phaseProduct
  {k : ℕ} (i : Fin k) (ps : Prog k) (curLen : List Nat) :
  compileProg (k := k) (valid_ops.phaseProduct i :: ps) curLen
    =
  let cp := compileProg (k := k) ps curLen
  ([prim_ops.phaseProduct i] ++ cp.1, cp.2) := by
  simp [compileProg, compile1_phaseProduct]

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
    -- eraseFirstMatch? on [pt] either yields some [] if head matches, else none
    -- and we know it yields some pts2 and head matches.
    have : List.eraseFirstMatch?
        (fun q ↦ matchesAt_pointRow_state (k := k) hk σ1 i q) [pt]
        = some ([] : List Point) := by
      simp [List.eraseFirstMatch?, hrow]
    -- compare with given hconsume
    exact Option.some.inj (by simp at hconsume; aesop)
  subst hpts2

  -- get FitsSignedAt from ValidFor, rewriting ρ using hρ
  have hfit :
      FitsSignedAt (σ := σ1)
        (ctx := ⟨(fun j => regToInt (σinit j)), ctx0.baseW, curLenNow⟩) i := by
    simpa [hρ] using (hV.fits_all i)

  -- apply interp-head eraser lemma
  -- need the regEqExpected form, which we already have as hrow
  have : eraseFirstMatchB
      (fun q =>
        matchesAt_interp (k := k) σinit
          (stateToSt (k := k) σ1 ⟨(fun j => regToInt (σinit j)), ctx0.baseW, curLenNow⟩) i q)
      (pt :: [])
    = some [] := by
    -- eraseFirstMatchB_interp_head expects ptsTail, so here ptsTail = []
    simpa using
      eraseFirstMatchB_interp_head
        (k := k) (hk := hk)
        (σinit := σinit)
        (ctxNow := ⟨(fun j => regToInt (σinit j)), ctx0.baseW, curLenNow⟩)
        (σ := σ1) (i := i) (pt := pt) (ptsTail := [])
        (hfit := hfit) (hrow := hrow)

  -- rewrite ctx back to ctx0 using hρ and finish
  simpa [hρ, stateToSt] using this
  -- have:=eraseFirstMatchB_of_eraseFirstMatch? (fun pt ↦ matchesAt_pointRow_state hk σ1 i pt) [pt] pts2 (by simp_all)
  -- rw[← this]

lemma PhaseProductCoverageM_prim_of_NoPhase
  {k : ℕ} {M : MatchesAtStateBit k}
  (opsP : List (prim_ops k)) (σ : St k)
  (hNo : PhaseProduct_PrimOps.NoPhase (k := k) opsP) :
  PhaseProductCoverageM_prim (k := k) M opsP σ [] := by
  have hrest : PhaseProductCoverageM_prim (k := k) M ([] : List (prim_ops k))
                (eval_prim_ops (k := k) opsP σ) [] := by
    -- nil constructor
    simpa using (PhaseProductCoverageM_prim.nil (k := k) (M := M) (σ := eval_prim_ops (k := k) opsP σ))
  -- prepend_noPhase builds coverage for opsP ++ [] i.e. opsP
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

    -- We'll name the compiled pieces
    set ops1 : List (prim_ops k) := (compile1 (k := k) op curLenNow).1
    set curLen1 : List Nat := (compile1 (k := k) op curLenNow).2
    set cp2 : (List (prim_ops k) × List Nat) := compileProg (k := k) ops2 curLen1
    set opsP2 : List (prim_ops k) := cp2.1

    -- Goal is coverage for ops1 ++ opsP2 from stateToSt σ0 ctxNow
    -- 1) Extract tail consume predicate from hConsume (this is where rcases failed before)
    have hConsumeTail : ProgConsumesPts hk σ1 ops2 pts2 := by
      cases op with
      | phaseProduct i =>
          -- impossible in step_op case
          exfalso
          exact hstep i rfl
      | shiftL i n =>
          -- unfold and extract ∃ σ', applyOp? σ0 op = some σ' ∧ ...
          -- (simp will reduce applyOp? too)
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
          unfold applyOp? at hrest;simp at hrest
          rw[hrest] at hConsume
          apply hConsume

    -- 2) WellFormed splits
    have hopOK : Prog.OpOK (k := k) op := by
      simp [Prog.WellFormed] at hWF; apply hWF.left
    have hWF_tail : Prog.WellFormed (k := k) ops2 := by
      simp [Prog.WellFormed] at hWF; apply hWF.right

    -- 3) ValidFor after stepping the source op, with curLen updated to curLen1
    have hV1 : ValidFor (k := k) σ1 { ctx0 with curLen := curLen1 } := by
      apply hStep σ0 σ1 op curLenNow hrest hopOK
      aesop
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

    have hCtx1 :
        runCtxPrim (k := k) ({ ctx0 with curLen := curLenNow }) ops1
          = { ctx0 with curLen := curLen1 } := by
      have := runCtxPrim_compile1 (k := k) op ({ ctx0 with curLen := curLenNow })
      simpa [ops1, curLen1] using this

    have hPrim2 : PrimOKTrace (k := k) opsP2 { ctx0 with curLen := curLen1 } := by
      simpa [hCtx1] using hPrim2_raw
    have hStepNow : ValidForStep (k := k) ({ ctx0 with curLen := curLenNow }) :=
      PhaseProductCoverage.ValidForStep.withCurLen (k := k) ctx0 curLenNow hStep

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
    have htail :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit opsP2
          (stateToSt (k := k) σ1 { ctx0 with curLen := curLen1 }) pts2 := by
      have := ih' (ctx0 := ctx0) (curLenNow := curLen1) (hρ:=hρ)
        hWF_tail hV1 hStep
        (by simpa [opsP2, cp2] using hPrim2)
        hConsumeTail
      aesop
    have htail' :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit opsP2
          (eval_prim_ops (k := k) ops1
            (stateToSt (k := k) σ0 { ctx0 with curLen := curLenNow })) pts2 := by
      simpa [hsim] using htail
    have hstart :
        stateToSt (k := k) σ0
          { ρ := fun j ↦ regToInt (σinit j),
            baseW := ctx0.baseW, curLen := curLenNow }
        =
        stateToSt (k := k) σ0
          { ρ := ctx0.ρ,
            baseW := ctx0.baseW, curLen := curLenNow } := by
      simp[hρ]

    -- NoPhase for ops1 (compiled from a non-phaseProduct op)
    have hNo : PhaseProduct_PrimOps.NoPhase (k := k) ops1 := by
      -- hstep : ∀ i, ¬ op = phaseProduct i  (same as ∀ i, op ≠ ...)
      have hne : ∀ i, op ≠ valid_ops.phaseProduct i := by
        intro i hi; exact hstep i (by simp[hi])
      simpa [ops1] using
        NoPhase_compile1_of_not_phaseProduct (k := k) (op := op) (curLen := curLenNow) hne

    -- Prefix coverage consumes no points
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

    -- Tail coverage (already have htail' but unwrap wrapper)
    have htailM :
        PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σinit)
          opsP2
          (eval_prim_ops (k := k) ops1
            (stateToSt (k := k) σ0 { ρ := ctx0.ρ, baseW := ctx0.baseW, curLen := curLenNow }))
          pts2 := by
      -- htail' is the wrapper version
      simpa [PhaseProduct_PrimOps.PhaseProductCoverage_prim] using htail'

    -- Append lemma: ops1 then opsP2 consumes [] then pts2
    have happ :
        PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σinit)
          (ops1 ++ opsP2)
          (stateToSt (k := k) σ0 { ρ := ctx0.ρ, baseW := ctx0.baseW, curLen := curLenNow })
          ([] ++ pts2) := by
      exact PhaseProductCoverageM_prim_append (k := k)
        (M := matchesAt_interp (k := k) σinit)
        (hp := hpref)
        (hq := htailM)

    -- back to wrapper + clean up [] ++ pts2, then rewrite start state to the goal’s form
    have happ' :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit (ops1 ++ opsP2)
          (stateToSt (k := k) σ0 { ρ := ctx0.ρ, baseW := ctx0.baseW, curLen := curLenNow })
          pts2 := by
      simpa [PhaseProduct_PrimOps.PhaseProductCoverage_prim] using (by simpa using happ)

    simpa [hstart] using happ'

  | step_phase hconsume hrest ih =>
      rename_i i ops2 σ1 pts1 pts2
      have hConsTail : ProgConsumesPts hk σ1 ops2 pts2 := by
        simp [ProgConsumesPts] at hConsume
        rcases hConsume with ⟨pt, ptsTail, hpts1, hrow, hCtail⟩

        -- 2) show pts2 = ptsTail by comparing hconsume with “eraseFirstMatch? hits head”
        have hconsume_head :
            List.eraseFirstMatch?
              (fun q => matchesAt_pointRow_state (k := k) hk σ1 i q) (pt :: ptsTail)
            = some ptsTail := by
          simp[List.eraseFirstMatch?, hrow]
        -- rewrite pts1 and conclude pts2 = ptsTail
        have : pts2 = ptsTail := by
          subst hpts1
          -- now both sides are `some ...`
          exact Option.some.inj (by simp at hconsume; aesop)

        subst this
        exact hCtail

      -- 3) Get tail prim-coverage from IH at same curLenNow
      have hWF_tail : Prog.WellFormed (k := k) ops2 := by
        simp [Prog.WellFormed] at hWF; apply hWF.right

        -- Unfold the let/match and rewrite compileProg on the cons
      simp [PhaseProduct_PrimOps.PhaseProductCoverage_prim]
      have hPrimTail :
          PrimOKTrace (k := k) (compileProg (k := k) ops2 curLenNow).1
            { ctx0 with curLen := curLenNow } := by
        simpa using
          PrimOKTrace_tail_of_cons_phaseProduct (k := k) i ops2 curLenNow ctx0
            (by simpa using hPrim)

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

      -- 3) Use IH on the tail to get prim coverage for compiled ops2 at pts2
      have htail :
          PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
            σinit (compileProg (k := k) ops2 curLenNow).1
            (stateToSt (k := k) σ1 { ctx0 with curLen := curLenNow }) pts2 := by
        simpa using
          ih (ctx0 := ctx0) (curLenNow := curLenNow)
            hWF_tail hV hStep hPrimTail hConsumeTail hρ

      -- 4) Build the interp-consumption fact for the head phase
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
        have:=PhaseProductCoverage.eraseFirstMatchB_interp_head
            (k := k) (hk := hk)
            (σinit := σinit)
            (ctxNow := { ctx0 with curLen := curLenNow })
            (σ := σ1) (i := i) (pt := pt) (ptsTail := pts2)
            (hfit := hfit) (hrow := hrow')
        aesop

      simp_all[PhaseProduct_PrimOps.PhaseProductCoverage_prim]
      change PhaseProductCoverageM_prim (matchesAt_interp σinit) ([prim_ops.phaseProduct i] ++ (compileProg ops2 curLenNow).1) (stateToSt σ1 { ρ := fun j ↦ regToInt (σinit j), baseW := ctx0.baseW, curLen := curLenNow }) ([pt] ++ pts2)
      set σ0 : St k :=
        stateToSt (k := k) σ1
          { ρ := fun j ↦ regToInt (σinit j), baseW := ctx0.baseW, curLen := curLenNow }

      -- 1) Tail coverage from IH
      have htail :
          PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σinit)
            (compileProg (k := k) ops2 curLenNow).1
            σ0 pts2 := by
        simpa [σ0] using
          ih (ctx0 := ctx0) (curLenNow := curLenNow) (by aesop) hStep (by aesop) hρ

      have hpref :
      PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σinit)
        [prim_ops.phaseProduct i] σ0 [pt] := by
        have hb1 :
            eraseFirstMatchB (fun q => matchesAt_interp (k := k) σinit σ0 i q) [pt]
              = some ([] : List Point) := by
          have := eraseFirstMatchB_append_hit
            (p := fun q => matchesAt_interp (k := k) σinit σ0 i q)
            (xs := [pt]) (ys := ([] : List Point)) (zs := pts2)
            ?_
          · -- now specialize it: eraseFirstMatchB ... ([pt] ++ pts2) = some ([] ++ pts2)
            -- and compare with hb
            -- ([] ++ pts2) is pts2, ([pt] ++ pts2) is (pt :: pts2)
            have : eraseFirstMatchB (fun q => matchesAt_interp (k := k) σinit σ0 i q) ([pt] ++ pts2)
                    = some (([] : List Point) ++ pts2) := this
            have hinterp : matchesAt_interp (k := k) σinit σ0 i pt = true := by
              -- use the lemma that turns row truth into interp truth
              -- note: `hrow' : regEqExpected (σ1 i) pt = true`
              -- and `hfit` is FitsSignedAt for the ctx with ρ = regToInt σinit.
              -- `σ0` is definitional equal to the stateToSt with that ctx.
              have :=
                PhaseProductCoverage.interp_true_of_row_true
                  (k := k) (hk := hk)
                  (σinit := σinit)
                  (ctxNow := { ρ := fun j ↦ regToInt (σinit j), baseW := ctx0.baseW, curLen := curLenNow })
                  (σ := σ1) (i := i) (pt := pt)
                  (hfit := hfit) (hrow := hrow')
              -- this lemma’s conclusion matchesAt_interp uses the explicit `stateToSt ...` term,
              -- rewrite it to σ0
              simpa [σ0] using this
            simpa using (PhaseProductCoverage.eraseFirstMatchB_head_true (p := fun q => matchesAt_interp (k := k) σinit σ0 i q) (x := pt) (xs := ([] : List Point)) hinterp)
          · -- need eraseFirstMatchB ... [pt] = some []
            -- this follows from the fact the head matches: matchesAt_interp ... pt = true
            have hinterp :
                matchesAt_interp (k := k) σinit σ0 i pt = true := by
              have : matchesAt_interp (k := k) σinit
                  (stateToSt (k := k) σ1
                    { ρ := fun j ↦ regToInt (σinit j), baseW := ctx0.baseW, curLen := curLenNow })
                  i pt = true := by
                -- use the lemma directly
                exact PhaseProductCoverage.interp_true_of_row_true
                  (k := k) (hk := hk) (σinit := σinit)
                  (ctxNow := { ρ := fun j ↦ regToInt (σinit j), baseW := ctx0.baseW, curLen := curLenNow })
                  (σ := σ1) (i := i) (pt := pt) (hfit := hfit) (hrow := hrow')
              simpa [σ0] using this
            -- now `eraseFirstMatchB` consumes the head of a singleton list
            -- You already have `eraseFirstMatchB_head_true`
            simpa using
              (PhaseProductCoverage.eraseFirstMatchB_head_true
                (p := fun q => matchesAt_interp (k := k) σinit σ0 i q)
                (x := pt) (xs := ([] : List Point)) hinterp)
        refine PhaseProductCoverageM_prim.step_phase (k := k)
          (M := matchesAt_interp (k := k) σinit) (i := i)
          (pts := [pt]) (pts' := []) ?_ ?_
        · exact hb1
        · simpa using (PhaseProductCoverageM_prim.nil (k := k) (M := matchesAt_interp (k := k) σinit) (σ := σ0))

      have happend :
          PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σinit)
            ([prim_ops.phaseProduct i] ++ (compileProg (k := k) ops2 curLenNow).1)
            σ0 ([pt] ++ pts2) := by
        exact PhaseProductCoverageM_prim_append (k := k)
          (M := matchesAt_interp (k := k) σinit)
          (hp := hpref)
          (hq := by
            -- hq must start from eval_prim_ops of the prefix; prefix is phaseProduct so state unchanged
            simpa [eval_prim_ops, eval_prim_op_single, σ0] using htail)

      -- Finish by unfolding σ0
      simpa [σ0] using happend

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
    -- proof goes here
    apply compileProg_preserves_phaseCoverage_go
    apply hOK; apply hcov; apply hV0; apply hStep; apply hPrim; apply hConsume; apply hρ

end PhaseProductCoverage
