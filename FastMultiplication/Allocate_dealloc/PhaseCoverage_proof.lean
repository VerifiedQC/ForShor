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
------------------------------- GENERIC PREPEND LEMMA ----------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Prepend lemma: execute a prefix of prim-ops using only `step_op` steps. -/
lemma prepend
  {k : ℕ} {M : MatchesAtStateBit k}
  (pref rest : List (prim_ops k)) (σ : St k) (pts : List Operations.Point) :
  PhaseProductCoverageM_prim (k := k) M rest (eval_prim_ops (k := k) pref σ) pts →
  PhaseProductCoverageM_prim (k := k) M (pref ++ rest) σ pts := by
  intro h
  induction pref generalizing σ with
  | nil =>
      simpa [eval_prim_ops] using h
  | cons op pref ih =>
      -- rewrite the tail state to match the IH shape
      have h' :
        PhaseProductCoverageM_prim (k := k) M rest
          (eval_prim_ops (k := k) pref (eval_prim_op_single (k := k) op σ)) pts := by
        simpa [eval_prim_ops] using h
      -- apply IH at the updated σ
      have h'' :
        PhaseProductCoverageM_prim (k := k) M (pref ++ rest)
          (eval_prim_op_single (k := k) op σ) pts := by
        exact ih (σ := eval_prim_op_single (k := k) op σ) h'
      -- add one `step_op` in front
      have : PhaseProductCoverageM_prim (k := k) M (op :: (pref ++ rest)) σ pts :=
        PhaseProductCoverageM_prim.step_op (k := k) (M := M) (hrest := h'')
      simpa [List.cons_append] using this


----------------------------------------------------------------------------------------------------
------------------------------- COVERAGE (PRIM / INTERP WRAPPER) -----------------------------------
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
------------------------------- COVERAGE TRANSFER + MAIN THEOREMS -----------------------------------
----------------------------------------------------------------------------------------------------

namespace PhaseProductCoverage

open Operations
open PhaseProduct_PrimOps

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



lemma consume_transfer_pointRow_to_interp
  {k : ℕ} (hk : k > 0)
  (σinit : St k)
  (ctxNow : StCtx k)
  (σ : State k) (i : Fin k)
  (pts pts' : List Operations.Point)
  (hconsume :
    List.eraseFirstMatch? (fun pt => matchesAt_pointRow_state (k := k) hk σ i pt) pts
      = some pts') :
  eraseFirstMatchB
      (fun pt => matchesAt_interp (k := k) σinit (stateToSt (k := k) σ ctxNow) i pt) pts
    = some pts' := by
  have hb_row :
    eraseFirstMatchB (fun pt => matchesAt_pointRow_state (k := k) hk σ i pt) pts = some pts' := by
    apply eraseFirstMatchB_of_eraseFirstMatch?_Bool
      (p := fun pt => matchesAt_pointRow_state (k := k) hk σ i pt) pts pts'
    aesop
  clear hconsume
  induction pts with
  | nil =>
      simp_all [eraseFirstMatchB]
  | cons head tail ih =>
      simp_all [eraseFirstMatchB]
      sorry


theorem compileProg_preserves_phaseCoverage_go
  {k : ℕ}
  (hk : k > 0)
  (σinit : St k)
  (ops : List (valid_ops k))
  (σ0 : State k)
  (ctx0 : StCtx k)
  (curLenNow : List Nat)
  (hWF : Prog.WellFormed ops)
  (pts : List Operations.Point)
  (hcov : PhaseProductCoverage (k := k) hk ops σ0 pts)
  (hV : ValidFor (k := k) σ0 { ctx0 with curLen := curLenNow })
  (hStep : ValidForStep (k := k) ctx0) :
  let ctxNow : StCtx k := { ctx0 with curLen := curLenNow }
  let (opsP, _curLen') := compileProg (k := k) ops curLenNow
  PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
    σinit opsP (stateToSt (k := k) σ0 ctxNow) pts := by
  classical
  unfold PhaseProductCoverage at hcov
  induction hcov generalizing curLenNow with
  | nil =>
      simp [compileProg, PhaseProduct_PrimOps.PhaseProductCoverage_prim,
            PhaseProduct_PrimOps.PhaseProductCoverageM_prim.nil]
  | step_op hstep hrest ih =>
      rename_i op ps σ τ pts
      have hopOK : Prog.OpOK op := by
        simp [Prog.WellFormed] at hWF; aesop
      have hWF_tail : Prog.WellFormed ps := by
        simp [Prog.WellFormed] at hWF; aesop

      have hVτ :
          let curLen1 := (compile1 (k := k) op curLenNow).2
          ValidFor (k := k) τ { ctx0 with curLen := curLen1 } := by
        exact hStep σ τ op curLenNow hstep hopOK hV

      rcases hC1 : compile1 (k := k) op curLenNow with ⟨ops1, curLen1⟩
      rcases hCP : compileProg (k := k) ps curLen1 with ⟨ops2, curLen2⟩

      have hVτ' : ValidFor (k := k) τ { ctx0 with curLen := curLen1 } := by
        simpa [hC1] using hVτ

      have hsim :
        eval_prim_ops (k := k) ops1 (stateToSt (k := k) σ { ctx0 with curLen := curLenNow })
          =
        stateToSt (k := k) τ { ctx0 with curLen := curLen1 } := by

        have:= (compile1_simulates (k := k) (op := op) (σ := σ) { ctx0 with curLen := curLenNow } hV hStep )
        sorry
      have htail :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit ops2 (stateToSt (k := k) τ { ctx0 with curLen := curLen1 }) pts := by
        have := ih (curLenNow := curLen1) (hWF := hWF_tail) (hV := hVτ')
        simpa [hCP] using this

      have htail' :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit ops2
          (eval_prim_ops (k := k) ops1 (stateToSt (k := k) σ { ctx0 with curLen := curLenNow })) pts := by
        simpa [hsim] using htail

      have hwhole :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit (ops1 ++ ops2) (stateToSt (k := k) σ { ctx0 with curLen := curLenNow }) pts := by
        apply prepend
        aesop
      simpa [compileProg, hC1, hCP] using hwhole

  | step_phase hconsume hrest ih =>
      rename_i i ps σ pts pts'
      have hWF_tail : Prog.WellFormed ps := by
        simp [Prog.WellFormed] at hWF; aesop

      rcases hC1 : compile1 (k := k) (valid_ops.phaseProduct i) curLenNow with ⟨ops1, curLen1⟩
      rcases hCP : compileProg (k := k) ps curLen1 with ⟨ops2, curLen2⟩

      have hCphase : ops1 = [prim_ops.phaseProduct i] ∧ curLen1 = curLenNow := by
        simpa [hC1] using (compile1_phaseProduct (k := k) i curLenNow)
      rcases hCphase with ⟨hops1, hcur1⟩
      subst hops1; subst hcur1

      have hb_interp :
        eraseFirstMatchB
          (fun pt =>
            matchesAt_interp (k := k) σinit
              (stateToSt (k := k) σ { ctx0 with curLen := curLen1 }) i pt) pts
          = some pts' := by
        apply consume_transfer_pointRow_to_interp (k := k) hk σinit
          ({ ctx0 with curLen := curLen1 }) σ i pts pts'
        aesop

      have htail :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit ops2 (stateToSt (k := k) σ { ctx0 with curLen := curLen1 }) pts' := by
        have := ih (curLenNow := curLen1) (hWF := hWF_tail) (hV := hV)
        simpa [hCP] using this

      have hphase :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit (prim_ops.phaseProduct i :: ops2)
          (stateToSt (k := k) σ { ctx0 with curLen := curLen1 }) pts := by
        dsimp [PhaseProduct_PrimOps.PhaseProductCoverage_prim] at htail ⊢
        refine PhaseProduct_PrimOps.PhaseProductCoverageM_prim.step_phase (k := k)
          (M := matchesAt_interp (k := k) σinit) (i := i) (hconsume := hb_interp) ?_
        exact htail

      simpa [compileProg, hC1, hCP] using hphase


theorem compileProg_preserves_phaseCoverage
  {k : ℕ}
  (hk : k > 0)
  (ops : List (valid_ops k))
  (σ0 : State k)
  (ctx0 : StCtx k)
  (hOK : Prog.WellFormed ops)
  (pts : List Operations.Point)
  (hcov : PhaseProductCoverage (k := k) hk ops σ0 pts)
  (hV0 : ValidFor (k := k) σ0 ctx0)
  (hStep : ValidForStep (k := k) ctx0) :
  PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
    (stateToSt (k := k) σ0 ctx0) (compileProg (k := k) ops ctx0.curLen).1
    (stateToSt (k := k) σ0 ctx0) pts := by
  classical
  let σinit : St k := stateToSt (k := k) σ0 ctx0
  have := compileProg_preserves_phaseCoverage_go (k := k)
    (hk := hk) (σinit := σinit)
    (ops := ops) (σ0 := σ0) (ctx0 := ctx0)
    (curLenNow := ctx0.curLen)
    (hWF := hOK) (pts := pts) (hcov := hcov)
    (hV := by simpa using hV0) (hStep := hStep)
  simpa [σinit] using this

end PhaseProductCoverage
