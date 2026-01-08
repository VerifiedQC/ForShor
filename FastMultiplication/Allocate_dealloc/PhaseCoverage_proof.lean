import FastMultiplication.Allocate_dealloc.Compiler_correctness
import FastMultiplication.Allocate_dealloc.PhaseCoverage

namespace PhaseProduct_PrimOps

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
          cases hNo  -- contradiction
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






/-- Prepend lemma: execute a prefix of prim-ops using only `step_op` steps. -/
lemma prepend
  {k : ℕ} {M : PhaseProduct_PrimOps.MatchesAtStateBit k}
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

/-- Your wrapper (as you were using it): initial state is fixed in the matcher. -/
def PhaseProductCoverage_prim {k : ℕ}
    (prog : List (prim_ops k)) (σ0 : St k) (pts : List Operations.Point) : Prop :=
  PhaseProductCoverageM_prim (k := k) (matchesAt_interp (k := k) σ0) prog σ0 pts


@[simp] lemma compile1_phaseProduct
  {k : ℕ} (i : Fin k) (curLen : List Nat) :
  compile1 (k := k) (valid_ops.phaseProduct i) curLen
    = ([prim_ops.phaseProduct i], curLen) := by
  -- this is definitional from your compiler
  simp [compile1, compile_op_to_prim_single]


/-- Unfold `matchesAt_pointRow_state`. -/
@[simp] lemma matchesAt_pointRow_state_apply
  {k : Nat} (hk : k > 0) (σ : State k) (i : Fin k) (pt : Point) :
  matchesAt_pointRow_state (k := k) hk σ i pt
    =
  regEqExpected (k := k) (σ i) pt := by
  rfl

/-- `matchesAt_pointRow_state` is exactly the register-only matcher
    `matchesAt_pointRow` lifted to states via `MatchesAtState.ofRegister`. -/
lemma matchesAt_pointRow_state_eq_ofRegister
  {k : Nat} (hk : k > 0) :
  matchesAt_pointRow_state (k := k) hk
    =
  MatchesAtState.ofRegister (k := k) (matchesAt_pointRow (k := k)) := by
  -- extensionality over σ i pt
  funext σ i pt
  -- unfold everything
  simp [matchesAt_pointRow_state, MatchesAtState.ofRegister, matchesAt_pointRow]

/-- The `hk : k>0` argument is irrelevant (the definition ignores it). -/
lemma matchesAt_pointRow_state_irrel
  {k : Nat} (hk₁ hk₂ : k > 0) :
  matchesAt_pointRow_state (k := k) hk₁
    =
  matchesAt_pointRow_state (k := k) hk₂ := by
  -- same proof: ext and rfl after unfolding
  funext σ i pt
  rfl

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

/-- `lastFin` is defined and returns a last index when `k>0`. -/
lemma lastFin_eq_some_of_pos {k : Nat} (hk : k > 0) :
    ∃ last : Fin k, lastFin k = some last := by
  cases k with
  | zero =>
      cases hk
  | succ k' =>
      refine ⟨⟨k', by simp⟩, rfl⟩

/-- Sum of a “unit vector” selector. -/
lemma finSum_unitSelector {k : Nat} (last : Fin k) (x : Fin k → Int) :
    (∑ j : Fin k, (if j = last then (1 : Int) else 0) * x j) = x last := by
  classical
  have hz : ∀ j : Fin k, j ≠ last → (if j = last then (1 : Int) else 0) * x j = 0 := by
    intro j hj
    simp [hj]
  aesop

@[simp] lemma regToInt_stateToSt_eq_bmod
  {k : ℕ} (σ : Fin k → (Fin k → Int)) (ρ : Fin k → Int)
  (baseW : Fin k → Nat) (curLen : List Nat) (i : Fin k) :
  let w : Nat := baseW i + curLen.getD i.1 0
  regToInt (stateToSt (k := k) σ ρ baseW curLen i)
    =
  (evalRegister (σ i) ρ).bmod ((2 : Nat) ^ w) := by
  classical
  dsimp [stateToSt, regToInt]
  simp
  rw[BitVec.toInt_ofNat']
  simp
  have:=Int.emod_nonneg (evalRegister (σ i) ρ) (b:=2 ^ (baseW i + curLen[i.val]?.getD 0)) (by simp)
  have:max ((evalRegister (σ i) ρ).emod (2 ^ (baseW i + curLen[i.val]?.getD 0))) 0=((evalRegister (σ i) ρ).emod (2 ^ (baseW i + curLen[↑i]?.getD 0))):=by aesop
  rw[this]
  set d:=(evalRegister (σ i) ρ)
  set c:=((baseW i + curLen[i]?.getD 0))
  have hc:(baseW i + curLen[i.val]?.getD 0)=c:= by aesop
  rw[hc]
  change Int.bmod (d % (2 ^ c)) (2 ^ c) = d.bmod (2 ^ c)
  have:=Int.emod_bmod d (2^c)
  rw[← this]
  norm_cast

lemma Int.bmod_eq_self_of_FitsSigned (w : Nat) (z : ℤ) (h : FitsSigned w z) :
    z.bmod ((2 : Nat) ^ w) = z := by
  rcases h with ⟨hwpos, hzlo, hzhi⟩
  -- For w>0, let H = 2^(w-1). Then modulus is m = 2^w = 2*H.
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
  {k : ℕ} (σ : State k) (ρ : Fin k → ℤ) (baseW : Fin k → Nat)
  (curLen : List Nat) (i : Fin k)
  (hfit : FitsSignedAt (σ := σ) (ρ := ρ) (baseW := baseW) (curLen := curLen) i) :
  regToInt (stateToSt (k := k) σ ρ baseW curLen i) = evalRegister (σ i) ρ := by
  classical
  set w : Nat := stWidth baseW curLen i
  set z : ℤ := evalRegister (σ i) ρ
  have hbmod :
      regToInt (stateToSt (k := k) σ ρ baseW curLen i)
        =
      z.bmod ((2 : Nat) ^ w) := by
    aesop
  have hid : z.bmod ((2 : Nat) ^ w) = z := by
    have : FitsSigned w z := by simpa [FitsSignedAt, stWidth, w, z] using hfit
    exact Int.bmod_eq_self_of_FitsSigned w z this
  simpa [z] using hbmod.trans hid


/-- The “one-way” bridge: row-match ⇒ interp-match, assuming `FitsSignedAt` so `stateToSt` has no wrap. -/
lemma matchesAt_pointRow_state_implies_matchesAt_interp
  {k : Nat}
  (hk : k > 0)
  (σ : State k) (i : Fin k) (pt : Point)
  (σ0St : St k)
  (baseW : Fin k → Nat) (curLen : List Nat)
  (hfit :
    FitsSignedAt (σ := σ)
      (ρ := (fun j => regToInt (σ0St j)))
      (baseW := baseW) (curLen := curLen) i)
  (hrow : matchesAt_pointRow_state (k := k) hk σ i pt = true) :
  matchesAt_interp (k := k) σ0St
    (stateToSt (k := k) σ (fun j => regToInt (σ0St j)) baseW curLen) i pt
    = true := by
  classical
  let ρinit : Fin k → ℤ := fun j => regToInt (σ0St j)

  -- `stateToSt` readback is exact evalRegister when `FitsSignedAt` holds
  have hcur :
      regToInt (stateToSt (k := k) σ ρinit baseW curLen i)
        =
      evalRegister (σ i) ρinit := by
    simpa [ρinit] using
      (regToInt_stateToSt_eq_eval_of_FitsSignedAt (k := k)
        (σ := σ) (ρ := ρinit) (baseW := baseW) (curLen := curLen) (i := i) hfit)

  -- turn `hrow` into pointwise equality `σ i j = expectedRow pt j`
  have hrow' : ∀ j : Fin k, σ i j = expectedRow (k := k) pt j := by
    have : regEqExpected (k := k) (σ i) pt = true := by
      simpa [matchesAt_pointRow_state] using hrow
    exact (regEqExpected_eq_true_iff (k := k) (r := σ i) (pt := pt)).1 this

  -- now split on pt
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
            have hrowInf : ∀ j : Fin (Nat.succ k'), σ i j = (if j = last then (1 : ℤ) else 0) := by
              intro j
              aesop
            have hsum :
              (∑ j : Fin (Nat.succ k'), (if j = last then (1 : ℤ) else 0) * ρinit j) = ρinit last := by
              rw[Finset.sum_eq_single last]
              simp[expectedRow] at *
              intro b _ hb
              simp[hb];aesop

            simp[evalRegister, ρinit, hrowInf, last]

          simp [matchesAt_interp, interpTarget, lastFin, ht, hcur, last, ρinit]






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

/-- `decide (b = true)` simplifies back to `b`. -/
@[simp] lemma decide_eq_true_bool (b : Bool) : decide (b = true) = b := by
  cases b <;> rfl

-- lemma matchers_agree_on_points
--   {k : ℕ} (hk : k > 0)
--   (σinit : St k)
--   (ρ : Fin k → ℤ) (baseW : Fin k → Nat) :
--   ∀ (curLenNow : List Nat) (σ : State k) (i : Fin k) (pt : Operations.Point),
--     matchesAt_pointRow_state (k := k) hk σ i pt
--       =
--     matchesAt_interp (k := k) σinit (stateToSt σ ρ baseW curLenNow) i pt := by
--   sorry


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
  (ρ : Fin k → ℤ) (baseW : Fin k → Nat)
  (curLenNow : List Nat)
  (σ : State k) (i : Fin k)
  (pts pts' : List Operations.Point)
  (hconsume :
    List.eraseFirstMatch? (fun pt => matchesAt_pointRow_state (k := k) hk σ i pt) pts
      = some pts') :
  eraseFirstMatchB (fun pt => matchesAt_interp (k := k) σinit (stateToSt σ ρ baseW curLenNow) i pt) pts
    = some pts' := by
  -- (1) convert Prop eraseFirstMatch? to Bool eraseFirstMatchB on pointRow
  have hb_row :
    eraseFirstMatchB (fun pt => matchesAt_pointRow_state (k := k) hk σ i pt) pts = some pts' := by
    apply eraseFirstMatchB_of_eraseFirstMatch?_Bool
      (p := fun pt => matchesAt_pointRow_state (k := k) hk σ i pt) pts pts'
    aesop
  -- (2) swap the predicate pointwise using the bridge lemma
  clear hconsume
  induction pts with
  |nil=>{
    simp_all[eraseFirstMatchB]
  }
  |cons head tail ih=>{
    simp_all[eraseFirstMatchB]
    sorry
  }
  -- refine eraseFirstMatchB_congr
  --   (p := fun pt => matchesAt_pointRow_state (k := k) hk σ i pt)
  --   (q := fun pt => matchesAt_interp (k := k) σinit (stateToSt σ ρ baseW curLenNow) i pt)
  --   (xs := pts) (ys := pts') ?_ hb_row
  -- intro pt
  -- simpa using (matchers_agree_on_points (k := k) hk σinit ρ baseW curLenNow σ i pt)


theorem compileProg_preserves_phaseCoverage_go
  {k : ℕ}
  (hk : k > 0)
  (σinit : St k)
  (ops : List (valid_ops k))
  (σ0 : State k)
  (ρ : Fin k → ℤ) (baseW : Fin k → Nat)
  (curLenNow : List Nat)
  (hlen : curLenNow.length = k)
  (hWF : Prog.WellFormed ops)
  (pts : List Operations.Point)
  (hcov : PhaseProductCoverage (k := k) hk ops σ0 pts) :
  let (opsP, _curLen') := compileProg (k := k) ops curLenNow
  PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
    σinit opsP (stateToSt σ0 ρ baseW curLenNow) pts := by
  classical
  -- unpack valid coverage
  unfold PhaseProductCoverage at hcov
  induction hcov generalizing curLenNow with
  | nil =>
      simp [compileProg, PhaseProduct_PrimOps.PhaseProductCoverage_prim,
            PhaseProduct_PrimOps.PhaseProductCoverageM_prim.nil]
  | step_op hstep hrest ih =>
      rename_i op ps σ τ pts
      have hopOK : Prog.OpOK op := by
        simp[Prog.WellFormed] at hWF;aesop
      have hWF_tail : Prog.WellFormed ps := by
        simp[Prog.WellFormed] at hWF;aesop

      rcases hC1 : compile1 (k := k) op curLenNow with ⟨ops1, curLen1⟩
      rcases hCP : compileProg (k := k) ps curLen1 with ⟨ops2, curLen2⟩

      have hsim :
        eval_prim_ops (k := k) ops1 (stateToSt σ ρ baseW curLenNow)
          =
        stateToSt τ ρ baseW curLen1 := by
        simpa [hC1] using
          (compile1_simulates (k := k)
            (op := op) (σ := σ) (ρ := ρ) (baseW := baseW)
            (curLen := curLenNow) (hcurLen := hlen)
            (σ2 := τ) (hstep := hstep) (hOK := hopOK))

      have hlen1 : curLen1.length = k := by
        -- use your lemma name here
        have hlen' := compile1_pres_len (k := k) (op := op) (curLen := curLenNow)
        simpa [hC1, hlen] using hlen'

      have htail :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit ops2 (stateToSt τ ρ baseW curLen1) pts := by
        have := ih (curLenNow := curLen1) hlen1 hWF_tail
        simpa [hCP] using this

      have htail' :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit ops2
          (eval_prim_ops (k := k) ops1 (stateToSt σ ρ baseW curLenNow)) pts := by
        simpa [hsim] using htail

      have hwhole :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit (ops1 ++ ops2) (stateToSt σ ρ baseW curLenNow) pts := by
        apply prepend
        aesop
      simpa [compileProg, hC1, hCP] using hwhole

  | step_phase hconsume hrest ih =>
      rename_i i ps σ pts pts'
      have hWF_tail : Prog.WellFormed ps := by
        simp[Prog.WellFormed] at hWF;aesop

      rcases hC1 : compile1 (k := k) (valid_ops.phaseProduct i) curLenNow with ⟨ops1, curLen1⟩
      rcases hCP : compileProg (k := k) ps curLen1 with ⟨ops2, curLen2⟩

      have hCphase : ops1 = [prim_ops.phaseProduct i] ∧ curLen1 = curLenNow := by
        simpa [hC1] using (compile1_phaseProduct (k := k) i curLenNow)
      rcases hCphase with ⟨hops1, hcur1⟩
      subst hops1; subst hcur1

      -- consume-transfer (Prop eraseFirstMatch? -> Bool eraseFirstMatchB, then swap matcher)
      have hb_interp :
        eraseFirstMatchB
          (fun pt => matchesAt_interp (k := k) σinit (stateToSt σ ρ baseW curLen1) i pt) pts
          = some pts' := by
        apply consume_transfer_pointRow_to_interp (k := k) hk σinit ρ baseW curLen1 σ i pts pts'
        aesop

      have htail :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit ops2 (stateToSt σ ρ baseW curLen1) pts' := by
        have := ih (curLenNow := curLen1) hlen hWF_tail
        simpa [hCP] using this

      have hphase :
        PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
          σinit (prim_ops.phaseProduct i :: ops2) (stateToSt σ ρ baseW curLen1) pts := by
        dsimp [PhaseProduct_PrimOps.PhaseProductCoverage_prim] at htail ⊢
        refine PhaseProduct_PrimOps.PhaseProductCoverageM_prim.step_phase (k := k)
          (M := matchesAt_interp (k := k) σinit) (i := i) (hconsume := hb_interp) ?_
        exact htail

      simpa [compileProg, hC1, hCP] using hphase


/-
## 3) Final theorem: no matcher hypothesis, just call `go`
-/
theorem compileProg_preserves_phaseCoverage
  {k : ℕ}
  (hk : k > 0)
  (ops : List (valid_ops k))
  (σ0 : State k)
  (ρ : Fin k → ℤ) (baseW : Fin k → Nat)
  (curLen : List Nat)
  (hcurLen : curLen.length = k)
  (hOK : Prog.WellFormed ops)
  (pts : List Operations.Point)
  (hcov : PhaseProductCoverage (k := k) hk ops σ0 pts) :
  PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
    (stateToSt σ0 ρ baseW curLen) (compileProg (k := k) ops curLen).1 (stateToSt σ0 ρ baseW curLen) pts := by
  classical
  let σinit : St k := stateToSt σ0 ρ baseW curLen
  simpa [σinit] using
    (compileProg_preserves_phaseCoverage_go (k := k)
      (hk := hk) (σinit := σinit)
      (ops := ops) (σ0 := σ0) (ρ := ρ) (baseW := baseW)
      (curLenNow := curLen) (hlen := hcurLen)
      (hWF := hOK) (pts := pts) (hcov := hcov))
