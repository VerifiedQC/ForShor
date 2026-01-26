import FastMultiplication.Allocate_dealloc.PhaseCoverage_proof
open Operations PhaseProductCoverage List

----------------------------------------------------------------------------------------------------
------------------------------- SHIFT-FREE PREDICATES ----------------------------------------------
----------------------------------------------------------------------------------------------------

def NoShiftR {k : ℕ} : Prog k → Prop
  | [] => True
  | valid_ops.shiftR _ _ :: _ => False
  | _ :: xs => NoShiftR xs

/-- No left-shifts occur in the program. (Helper predicate.) -/
def NoShiftL {k : ℕ} : Prog k → Prop
  | [] => True
  | valid_ops.shiftL _ _ :: _ => False
  | _ :: xs => NoShiftL xs

----------------------------------------------------------------------------------------------------
------------------------------- BASIC SIMPS --------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[simp] lemma NoShiftR_nil {k : ℕ} : NoShiftR (k := k) ([] : Prog k) := by
  simp [NoShiftR]

@[simp] lemma NoShiftR_cons_addScaled {k : ℕ} (dst src : Fin k) (negSrc : Bool) (sh : Nat) (xs : Prog k) :
    NoShiftR (k := k) (valid_ops.addScaled dst src (negSrc := negSrc) sh :: xs) = NoShiftR (k := k) xs := by
  simp [NoShiftR]

@[simp] lemma NoShiftL_nil {k : ℕ} : NoShiftL (k := k) ([] : Prog k) := by
  simp [NoShiftL]

@[simp] lemma NoShiftL_cons_addScaled {k : ℕ} (dst src : Fin k) (negSrc : Bool) (sh : Nat) (xs : Prog k) :
    NoShiftL (k := k) (valid_ops.addScaled dst src (negSrc := negSrc) sh :: xs) = NoShiftL (k := k) xs := by
  simp [NoShiftL]

----------------------------------------------------------------------------------------------------
------------------------------- APPEND PRESERVATION ------------------------------------------------
----------------------------------------------------------------------------------------------------

-- “append preserves NoShiftR”
lemma NoShiftR_append {k : ℕ} :
    ∀ (xs ys : Prog k), NoShiftR (k := k) xs → NoShiftR (k := k) ys → NoShiftR (k := k) (xs ++ ys)
  | [], ys, hx, hy => by simpa using hy
  | (x :: xs), ys, hx, hy => by
      cases x <;> simp [NoShiftR] at * <;> exact NoShiftR_append xs ys hx hy

-- “append preserves NoShiftL”
lemma NoShiftL_append {k : ℕ} :
    ∀ (xs ys : Prog k), NoShiftL (k := k) xs → NoShiftL (k := k) ys → NoShiftL (k := k) (xs ++ ys)
  | [], ys, hx, hy => by simpa using hy
  | (x :: xs), ys, hx, hy => by
      -- if x is shiftR, hx is impossible; otherwise reduce to tail
      cases x <;> simp [NoShiftL] at * <;> exact NoShiftL_append xs ys hx hy

----------------------------------------------------------------------------------------------------
------------------------------- addConst* HAS NO SHIFTS --------------------------------------------
----------------------------------------------------------------------------------------------------

-- Main structural lemma: addConstAux never introduces shiftR
lemma NoShiftR_addConstAux {k : Nat} (dst src : Fin k) (neg' : Bool) :
    ∀ (n sh : Nat), NoShiftR (k := k) (addConstAux (k := k) dst src neg' n sh)
  | 0, sh => by
      simp [addConstAux]
  | (n+1), sh => by
      by_cases hOdd : Odd (n+1)
      ·
        simp [addConstAux, hOdd, NoShiftR_addConstAux (n := (n+1)/2) (sh := sh+1)]
      ·
        simp [addConstAux, hOdd, NoShiftR_addConstAux (n := (n+1)/2) (sh := sh+1)]

lemma NoShiftR_addConstFrom {k : Nat} (dst src : Fin k) (c : Int) :
    NoShiftR (k := k) (addConstFrom (k := k) dst src c) := by
  by_cases hc : c = 0
  · simp [addConstFrom, hc]
  · -- reduces to addConstAux
    simp [addConstFrom, hc, NoShiftR_addConstAux]

/-- Mapping shifts to `addScaled` never introduces `shiftR`. -/
lemma NoShiftR_map_addScaled {k : ℕ} (dst src : Fin k) (neg' : Bool) :
    ∀ ss : List Nat,
      NoShiftR (k := k) (ss.map (fun s => valid_ops.addScaled dst src (negSrc := neg') s))
  | [] => by simp
  | _ :: ss => by
      simpa [NoShiftR] using NoShiftR_map_addScaled (k := k) dst src neg' ss

-- Main structural lemma: addConstAux never introduces shiftR
lemma NoShiftL_addConstAux {k : Nat} (dst src : Fin k) (neg' : Bool) :
    ∀ (n sh : Nat), NoShiftL (k := k) (addConstAux (k := k) dst src neg' n sh)
  | 0, sh => by
      simp [addConstAux]
  | (n+1), sh => by
      by_cases hOdd : Odd (n+1)
      ·
        simp [addConstAux, hOdd, NoShiftL_addConstAux (n := (n+1)/2) (sh := sh+1)]
      ·
        simp [addConstAux, hOdd, NoShiftL_addConstAux (n := (n+1)/2) (sh := sh+1)]

lemma NoShiftL_addConstFrom {k : Nat} (dst src : Fin k) (c : Int) :
    NoShiftL (k := k) (addConstFrom (k := k) dst src c) := by
  by_cases hc : c = 0
  · simp [addConstFrom, hc]
  · -- reduces to addConstAux
    simp [addConstFrom, hc, NoShiftL_addConstAux]

/-- Mapping shifts to `addScaled` never introduces `shiftR`. -/
lemma NoShiftL_map_addScaled {k : ℕ} (dst src : Fin k) (neg' : Bool) :
    ∀ ss : List Nat,
      NoShiftL (k := k) (ss.map (fun s => valid_ops.addScaled dst src (negSrc := neg') s))
  | [] => by simp
  | _ :: ss => by
      simpa [NoShiftL] using NoShiftL_map_addScaled (k := k) dst src neg' ss

----------------------------------------------------------------------------------------------------
------------------------------- computeLocalAux HAS NO SHIFTS --------------------------------------
----------------------------------------------------------------------------------------------------

/-- Correct proof: `computeLocalAux` has no `shiftR` by induction on `js`. -/
lemma NoShiftR_computeLocalAux {k : Nat} (hk : 0 < k) (z : Int) :
    ∀ js : List (Fin k),
      NoShiftR (k := k) (computeLocalAux (k := k) hk z js) := by
  intro js
  induction js with
  | nil =>
      simp [computeLocalAux]
  | cons j js ih =>
      -- computeLocalAux = head ++ tail
      have hhead :
          NoShiftR (k := k)
            (addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat))) :=
        NoShiftR_addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat))
      -- tail uses IH (NOT the lemma itself)
      have htail :
          NoShiftR (k := k) (computeLocalAux (k := k) hk z js) := ih
      -- append preserves
      simpa [computeLocalAux] using
        NoShiftR_append (k := k)
          (addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat)))
          (computeLocalAux (k := k) hk z js)
          hhead htail

/-- Correct proof: `computeLocalAux` has no `shiftR` by induction on `js`. -/
lemma NoShiftL_computeLocalAux {k : Nat} (hk : 0 < k) (z : Int) :
    ∀ js : List (Fin k),
      NoShiftL (k := k) (computeLocalAux (k := k) hk z js) := by
  intro js
  induction js with
  | nil =>
      simp [computeLocalAux]
  | cons j js ih =>
      -- computeLocalAux = head ++ tail
      have hhead :
          NoShiftL (k := k)
            (addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat))) :=
        NoShiftL_addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat))
      -- tail uses IH (NOT the lemma itself)
      have htail :
          NoShiftL (k := k) (computeLocalAux (k := k) hk z js) := ih
      -- append preserves
      simpa [computeLocalAux] using
        NoShiftL_append (k := k)
          (addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat)))
          (computeLocalAux (k := k) hk z js)
          hhead htail

lemma NoShiftR_computeLocal2 {k : ℕ} (hk : 0 < k) (z : Int) :
  NoShiftR (k := k) (computeLocal2 (k := k) hk z) := by
  simpa [computeLocal2] using
    (NoShiftR_computeLocalAux (k := k) hk z (nonzeroFins (k := k) hk))

lemma NoShiftL_computeLocal2 {k : ℕ} (hk : 0 < k) (z : Int) :
  NoShiftL (k := k) (computeLocal2 (k := k) hk z) := by
  simpa [computeLocal2] using
    (NoShiftL_computeLocalAux (k := k) hk z (nonzeroFins (k := k) hk))

----------------------------------------------------------------------------------------------------
------------------------------- NO-SHIFT HELPERS: HEAD/TAIL/REVERSE/INV -----------------------------
----------------------------------------------------------------------------------------------------

-- helper: pull NoShiftR tail out of NoShiftR (op :: ops)
lemma NoShiftR_tail {k : ℕ} {op : valid_ops k} {ops : List (valid_ops k)} :
  NoShiftR (k := k) (op :: ops) → NoShiftR (k := k) ops := by
  intro h
  cases op <;> simp [NoShiftR] at h <;> simp_all

-- helper: pull NoShiftR tail out of NoShiftR (op :: ops)
lemma NoShiftR_head {k : ℕ} {op : valid_ops k} {ops : List (valid_ops k)} :
  NoShiftR (k := k) (op :: ops) → NoShiftR (k := k) [op] := by
  intro h
  cases op <;> simp [NoShiftR] at h <;> simp_all[NoShiftR]

-- helper: pull NoShiftR tail out of NoShiftR (op :: ops)
lemma NoShiftL_tail {k : ℕ} {op : valid_ops k} {ops : List (valid_ops k)} :
  NoShiftL (k := k) (op :: ops) → NoShiftL (k := k) ops := by
  intro h
  cases op <;> simp [NoShiftL] at h <;> simp_all

-- helper: pull NoShiftR tail out of NoShiftR (op :: ops)
lemma NoShiftL_head {k : ℕ} {op : valid_ops k} {ops : List (valid_ops k)} :
  NoShiftL (k := k) (op :: ops) → NoShiftL (k := k) [op] := by
  intro h
  cases op <;> simp [NoShiftL] at h <;> simp_all[NoShiftL]

/-- If `op` is not a shiftL or shiftR, then `inv op` is not a shiftR.
    (This is the only place that needs `simp [Operations.inv]` to work.) -/
lemma NoShiftR_single_inv_of_noShiftsHead {k : ℕ} :
    ∀ op : valid_ops k,
      (∀ i n, op ≠ valid_ops.shiftL i n) →
      (∀ i n, op ≠ valid_ops.shiftR i n) →
      NoShiftR (k := k) ([Operations.inv op] : Prog k)
  | op, hL, hR => by
      cases op <;> simp [NoShiftR, Operations.inv] at hL hR ⊢

/-- Reverse preserves NoShiftR. -/
lemma NoShiftR_reverse {k : ℕ} :
    ∀ p : Prog k, NoShiftR (k := k) p → NoShiftR (k := k) p.reverse
  | [], hp => by simp
  | (op :: ps), hp => by
      have hp_tail : NoShiftR (k := k) ps := NoShiftR_tail (k := k) hp
      have ih : NoShiftR (k := k) ps.reverse := NoShiftR_reverse ps hp_tail
      have hop : NoShiftR (k := k) ([op] : Prog k) := by
        cases op <;> simp [NoShiftR] at hp ⊢
      simpa [List.reverse_cons] using NoShiftR_append (k := k) ps.reverse [op] ih hop

/-- Reverse preserves NoShiftL. -/
lemma NoShiftL_reverse {k : ℕ} :
    ∀ p : Prog k, NoShiftL (k := k) p → NoShiftL (k := k) p.reverse
  | [], hp => by simp
  | (op :: ps), hp => by
      have hp_tail : NoShiftL (k := k) ps := NoShiftL_tail (k := k) hp
      have ih : NoShiftL (k := k) ps.reverse := NoShiftL_reverse ps hp_tail
      have hop : NoShiftL (k := k) ([op] : Prog k) := by
        cases op <;> simp [NoShiftL] at hp ⊢
      simpa [List.reverse_cons] using NoShiftL_append (k := k) ps.reverse [op] ih hop

/-- Map `inv` preserves NoShiftR provided the list has no shiftL and no shiftR. -/
lemma NoShiftR_map_inv_of_NoShiftL_NoShiftR {k : ℕ} :
    ∀ p : Prog k,
      NoShiftL (k := k) p → NoShiftR (k := k) p → NoShiftR (k := k) (p.map Operations.inv)
  | [], hL, hR => by simp
  | (op :: ps), hL, hR => by
      have hLps : NoShiftL (k := k) ps := NoShiftL_tail (k := k) hL
      have hRps : NoShiftR (k := k) ps := NoShiftR_tail (k := k) hR
      have ih : NoShiftR (k := k) (ps.map Operations.inv) :=
        NoShiftR_map_inv_of_NoShiftL_NoShiftR ps hLps hRps
      -- show head inv op is not shiftR using the fact op is neither shiftL nor shiftR
      have hHead : NoShiftR (k := k) ([Operations.inv op] : Prog k) := by
        refine NoShiftR_single_inv_of_noShiftsHead (k := k) op ?_ ?_
        · intro i n hEq
          subst hEq
          simp[NoShiftL] at hL
        · intro i n hEq
          subst hEq
          simp [NoShiftR] at hR
      cases h : Operations.inv op <;> simp_all [NoShiftR]

/-- If p has no shifts, then apply_Op_inverse p has no shiftR. -/
lemma NoShiftR_apply_Op_inverse_of_NoShiftL_NoShiftR {k : ℕ} (p : Prog k) :
    NoShiftL (k := k) p → NoShiftR (k := k) p → NoShiftR (k := k) (apply_Op_inverse p) := by
  intro hL hR
  have hLr : NoShiftL (k := k) p.reverse := NoShiftL_reverse (k := k) p hL
  have hRr : NoShiftR (k := k) p.reverse := NoShiftR_reverse (k := k) p hR
  simpa [apply_Op_inverse] using
    NoShiftR_map_inv_of_NoShiftL_NoShiftR (k := k) p.reverse hLr hRr

----------------------------------------------------------------------------------------------------
------------------------------- opsForPoint/genOps NO SHIFT-R ---------------------------------------
----------------------------------------------------------------------------------------------------

lemma NoShiftR_opsForPointWithProduct {k : ℕ} (hk : 0 < k) :
  ∀ pt, NoShiftR (k := k) (opsForPointWithProduct (k := k) hk pt)
| .inf => by
    simp [opsForPointWithProduct, NoShiftR]
| .int z => by
    let dst := finZero hk
    let l   := computeLocal2 (k := k) hk z
    have hR_l : NoShiftR (k := k) l := by
      simpa [l] using NoShiftR_computeLocal2 (k := k) hk z
    have hL_l : NoShiftL (k := k) l := by
      simpa [l] using NoShiftL_computeLocal2 (k := k) hk z
    have hR_inv : NoShiftR (k := k) (apply_Op_inverse l) :=
      NoShiftR_apply_Op_inverse_of_NoShiftL_NoShiftR (k := k) l hL_l hR_l
    have hR_mid : NoShiftR (k := k) (l ++ [valid_ops.phaseProduct dst]) :=
      NoShiftR_append (k := k) l [valid_ops.phaseProduct dst] hR_l (by simp [NoShiftR])
    simpa [opsForPointWithProduct, dst, l, List.append_assoc] using
      NoShiftR_append (k := k) (l ++ [valid_ops.phaseProduct dst]) (apply_Op_inverse l) hR_mid hR_inv

lemma NoShiftR_genOpsWithProduct {k : ℕ} (hk : 0 < k) :
  ∀ pts, NoShiftR (k := k) (genOpsWithProduct (k := k) hk pts)
| [] => by
    simp [genOpsWithProduct]
| p :: ps => by
    have hp : NoShiftR (k := k) (opsForPointWithProduct (k := k) hk p) :=
      NoShiftR_opsForPointWithProduct (k := k) hk p
    have ih : NoShiftR (k := k) (genOpsWithProduct (k := k) hk ps) :=
      NoShiftR_genOpsWithProduct hk ps
    -- genOpsWithProduct hk (p::ps) = opsForPointWithProduct hk p ++ genOpsWithProduct hk ps
    simpa [genOpsWithProduct] using
      NoShiftR_append (k := k)
        (opsForPointWithProduct (k := k) hk p)
        (genOpsWithProduct (k := k) hk ps)
        hp ih

----------------------------------------------------------------------------------------------------
------------------------------- CTX BOOKKEEPING -----------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Bookkeeping: running ctx updates for the compiled output matches the returned curLen. -/
lemma runCtxPrim_compileProg
  {k : ℕ} (ops : Prog k) (curLen : List Nat) (ctx0 : StCtx k) :
  runCtxPrim (k := k) ({ ctx0 with curLen := curLen }) (compileProg (k := k) ops curLen).1
    = { ctx0 with curLen := (compileProg (k := k) ops curLen).2 } := by
  classical
  induction ops generalizing curLen with
  | nil =>
      simp [compileProg, runCtxPrim]
  | cons op ops ih =>
      simp [compileProg]
      rcases hC1 : compile1 (k := k) op curLen with ⟨ops1, curLen1⟩
      rcases hCP : compileProg (k := k) ops curLen1 with ⟨ops2, curLen2⟩
      simp [runCtxPrim_append]
      have h1 :
        runCtxPrim (k := k) ({ ctx0 with curLen := curLen }) ops1
          = { ctx0 with curLen := curLen1 } := by
        simpa [hC1] using (runCtxPrim_compile1 (k := k) op ({ ctx0 with curLen := curLen }))
      have:= (ih (curLen := curLen1))
      simp_all only

----------------------------------------------------------------------------------------------------
------------------------------- PRIMOKTRACE: LOCAL FACTS -------------------------------------------
----------------------------------------------------------------------------------------------------

open Operations

lemma FitsSigned_zero_of_pos (w : Nat) (hw : 0 < w) : FitsSigned w (0 : ℤ) := by
  refine ⟨hw, ?_, ?_⟩<;>simp

lemma PrimOKTrace_compile1
  {k : ℕ}
  (ctx : StCtx k)
  (hbase : ∀ i j : Fin k, ctx.baseW i = ctx.baseW j)
  (hcurLen:ctx.curLen.length = k)
  (op: valid_ops k)
  (hn: NoShiftR [op])
  :
  PrimOKTrace (k := k)
    (compile1 (k := k) (op) ctx.curLen).1 ctx := by
    cases op with
    |shiftR i sh=>{
      unfold NoShiftR at hn
      contradiction
    }
    |addScaled=>{
      apply PrimOKTrace_compile1_addScaled (hbase:=hbase) (hcurLen:=hcurLen)
    }
    |negate=>{
      simp[compile1,compile_op_to_prim_single,PrimOKTrace,PrimOKForCtx]
    }
    |shiftL=>{
      simp[compile1,compile_op_to_prim_single,PrimOKTrace,PrimOKForCtx]
    }
    |phaseProduct=>{
      simp[compile1,compile_op_to_prim_single,PrimOKTrace,PrimOKForCtx]
    }

lemma compile1_preserves_curLen_len {k} (op : valid_ops k) (curLen : List ℕ)
  (h : curLen.length = k) : (compile1 (k := k) op curLen).2.length = k := by
  cases op with
  |shiftL i sh=>{
    simp[compile1,compile_op_to_prim_single]
    rw[incLen_pres_len]
    apply h
  }
  |shiftR=>{
    simp[compile1,compile_op_to_prim_single]
    rw[decLen_pres_len]
    apply h
  }
  |negate=>{
    simp[compile1,compile_op_to_prim_single]
    apply h
  }
  |phaseProduct=>{
    simp[compile1,compile_op_to_prim_single]
    apply h
  }
  |addScaled dst src hneg sh=>{
    simp[compile1,compile_op_to_prim_single]
    by_cases hds:dst≠src
    {
      by_cases hn:hneg
      {
        simp[hds,hn]
        rw[decLen_pres_len];rw[incLen_pres_len];rw[incLen_pres_len]
        apply h
      }
      {
        simp[hds,hn]
        rw[decLen_pres_len];rw[incLen_pres_len];rw[incLen_pres_len]
        apply h
      }
    }
    {
      simp at hds
      simp[hds]
      apply h
    }
  }


def BaseWConst {k : ℕ} (ctx : StCtx k) : Prop :=
  ∀ i j : Fin k, ctx.baseW i = ctx.baseW j


lemma tail_PrimOKTrace_after_compile1
  {k : ℕ}
  (ctx : StCtx k)
  (ops : Prog k)
  (op : valid_ops k)
  (curLen : List ℕ)
  (hbase : BaseWConst (k := k) ctx)
  (hcurLen : curLen.length = k)
  (hc : ctx.curLen = curLen)
  (hNoTail : NoShiftR (k := k) ops)
  (ih :
    ∀ (curLen' : List ℕ) (ctx' : StCtx k),
      BaseWConst (k := k) ctx' →
      ctx'.curLen = curLen' →
      curLen'.length = k →
      NoShiftR (k := k) ops →
      PrimOKTrace (k := k) (compileProg (k := k) ops curLen').1 ctx')
  :
  let curLen1 := (compile1 (k := k) op ctx.curLen).2
  PrimOKTrace (k := k) (compileProg (k := k) ops curLen1).1 { ctx with curLen := curLen1 } := by
  classical
  intro curLen1
  -- baseW const survives curLen update
  have hbase1 : BaseWConst (k := k) ({ ctx with curLen := curLen1 }) := by
    intro i j
    simpa [BaseWConst] using hbase i j

  -- length of curLen1
  have hlen1 : curLen1.length = k := by
    have:=(compile1_preserves_curLen_len (k := k) (op := op) (curLen := curLen) hcurLen)
    unfold curLen1;simp[hc,this]

  simpa using
    (ih (curLen' := curLen1) (ctx' := { ctx with curLen := curLen1 })
      hbase1 rfl hlen1 hNoTail)

lemma PrimOKTrace_compile1_of_NoShiftR_head
  {k : ℕ} (ctx0 : StCtx k) (curLen : List ℕ)
  (op : valid_ops k)
  (hbase : BaseWConst (k := k) ctx0)
  (hNoHead : NoShiftR (k := k) [op])
  (hlen : curLen.length = k)
  :
  PrimOKTrace (k := k)
    (compile1 (k := k) op curLen).1 { ctx0 with curLen := curLen } := by
  classical
  -- `NoShiftR [op]` rules out the shiftR constructor
  cases op with
  | shiftR i n =>
      cases hNoHead
  | shiftL i n =>
      -- compile1 emits [Alloc ...]; always OK
      simp [compile1, compile_op_to_prim_single, PrimOKTrace, PrimOKForCtx]
  | negate i =>
      simp [compile1, compile_op_to_prim_single, PrimOKTrace, PrimOKForCtx]
  | phaseProduct i =>
      simp [compile1, compile_op_to_prim_single, PrimOKTrace, PrimOKForCtx]
  | addScaled dst src negSrc sh =>
      have:=(PrimOKTrace_compile1_addScaled (k := k) (ctx := { ctx0 with curLen := curLen })
          (dst := dst) (src := src) (negSrc := negSrc) (sh := sh)
          (hbase := by
            intro i j
            simpa using hbase i j))
      simp[BaseWConst] at hbase
      simp_all

theorem PrimOKTrace_compileProg_of_NoShiftR_general
  {k : ℕ} :
  ∀ (ops : Prog k) (curLen : List ℕ) (ctx : StCtx k),
    BaseWConst (k := k) ctx →
    ctx.curLen = curLen →
    curLen.length = k →
    NoShiftR (k := k) ops →
    PrimOKTrace (k := k) (compileProg (k := k) ops curLen).1 ctx := by
  intro ops
  induction ops with
  | nil =>
      intro curLen ctx hbase hctx hlen hNo
      simp [compileProg, PrimOKTrace]
  | cons op ops ih =>
      intro curLen ctx hbase hctx hlen hNo
      simp [compileProg]
      rcases hC1 : compile1 (k := k) op curLen with ⟨ops1, curLen1⟩
      rcases hCP : compileProg (k := k) ops curLen1 with ⟨ops2, curLen2⟩

      have hNoHead : NoShiftR (k := k) [op] := by
        cases op <;> simp [NoShiftR] at hNo ⊢

      have hNoTail : NoShiftR (k := k) ops := NoShiftR_tail (k := k) (op := op) (ops := ops) hNo

      have hCtx1 :
        runCtxPrim (k := k) ctx ops1 = { ctx with curLen := curLen1 } := by
        have := runCtxPrim_compile1 (k := k) op ({ ctx with curLen := curLen })
        have hctx' : { ctx with curLen := curLen } = ctx := by
          cases ctx
          simp at hctx
          subst hctx
          rfl
        simpa [hC1, hctx'] using this
      have h1 :
        PrimOKTrace (k := k) ops1 ctx := by
        have : PrimOKTrace (k := k) (compile1 (k := k) op curLen).1 { ctx with curLen := curLen } := by
          exact PrimOKTrace_compile1_of_NoShiftR_head (k := k) ctx curLen op hbase hNoHead (hlen:=hlen)
        simp [hC1] at this
        rw[← hctx] at this
        apply this
      have hlen1 : curLen1.length = k := by
        have : (compile1 (k := k) op curLen).2.length = k :=
          compile1_preserves_curLen_len (k := k) op curLen hlen
        simpa [hC1] using this
      have h2 :
        PrimOKTrace (k := k) ops2 (runCtxPrim (k := k) ctx ops1) := by
        have : PrimOKTrace (k := k)
            (compileProg (k := k) ops curLen1).1 { ctx with curLen := curLen1 } := by
          have hbase1 : BaseWConst (k := k) ({ ctx with curLen := curLen1 }) := by
            intro i j; simpa using hbase i j
          exact ih (curLen := curLen1) (ctx := { ctx with curLen := curLen1 })
            hbase1 rfl hlen1 hNoTail
        simpa [hCP, hCtx1] using this
      have hall :
        PrimOKTrace (k := k) (ops1 ++ ops2) ctx := by
        apply PrimOKTrace_append_fwd (k := k) ops1 ops2 ctx h1 h2
      simpa [compileProg, hC1, hCP] using hall

lemma PrimOKTrace_compileProg_NoShiftR
  {k : ℕ}
  (ctx : StCtx k)
  (hbase : ∀ i j : Fin k, ctx.baseW i = ctx.baseW j)
  (curLen: List ℕ)
  (hc_eq: curLen = ctx.curLen)
  (hcurLen:ctx.curLen.length = k)
  (p: Prog k)
  (hn: NoShiftR p)
  :
  PrimOKTrace (k := k)
    (compileProg (k := k) p curLen).1 ctx := by

  have hlen : curLen.length = k := by
    simpa [hc_eq] using hcurLen

  exact PrimOKTrace_compileProg_of_NoShiftR_general (k := k) (ops := p) (curLen := curLen) (ctx := ctx) (by intro i j; exact hbase i j) (by simp[hc_eq] ) hlen hn

----------------------------------------------------------------------------------------------------
------------------------------- genOpsWithProduct: PrimOKTrace -------------------------------------
----------------------------------------------------------------------------------------------------

theorem genOpsWithProduct_PrimOKTrace
  {k : Nat} (hk : 0 < k) (pts : List Point) (ctx0 : StCtx k) (hV0 : ValidFor (k := k) State.start_state ctx0):
  PrimOKTrace (k := k)
    (compileProg (k := k) (genOpsWithProduct hk pts) ctx0.curLen).1 ctx0 := by
  have hNo : NoShiftR (k := k) (genOpsWithProduct (k := k) hk pts) :=
    NoShiftR_genOpsWithProduct (k := k) hk pts
  apply PrimOKTrace_compileProg_NoShiftR ctx0 (hV0.baseW_eq) (ctx0.curLen) rfl (hV0.curLen_len) ((genOpsWithProduct hk pts)) hNo

----------------------------------------------------------------------------------------------------
------------------------------- CONSUMPTION PREDICATES & LEMMAS ------------------------------------
----------------------------------------------------------------------------------------------------

/-- When `eraseFirstMatch?` succeeds during a phaseProduct check,
    it must be because the *head* matches. -/
def ConsumeHeadOK {k : ℕ} (hk : k > 0) : Prop :=
  ∀ (σ : State k) (i : Fin k) (pts pts' : List Point),
    List.eraseFirstMatch? (fun pt => matchesAt_pointRow_state (k := k) hk σ i pt) pts = some pts' →
      ∃ pt ptsTail,
        pts = pt :: ptsTail ∧
        pts' = ptsTail ∧
        matchesAt_pointRow_state (k := k) hk σ i pt = true

/-- If `p` consumes exactly `a` starting from `σ` and ends in `σ'`,
    and `q` consumes `b` starting from `σ'`,
    then `p ++ q` consumes `a ++ b` starting from `σ`. -/
theorem ProgConsumesPts_append
  {k : ℕ} (hk : k > 0)
  (σ σ' : State k) (p q : Prog k) (a b : List Point)
  (hp : ProgConsumesPts (k := k) hk σ p a)
  (hret : run? (k := k) p σ = some σ')
  (hq : ProgConsumesPts (k := k) hk σ' q b) :
  ProgConsumesPts (k := k) hk σ (p ++ q) (a ++ b) := by
  -- We prove a slightly more general statement by induction on `p`.
  revert σ a hp hret
  induction p with
  | nil =>
      intro σ a hp hret
      have ha : a = [] := by simpa [ProgConsumesPts] using hp
      subst ha
      -- σ' = σ from hret
      simp [run?] at hret
      cases hret
      simpa [ProgConsumesPts]
        using hq

  | cons op ps ih =>
      intro σ a hp hret
      -- unfold run? on op :: ps
      simp [run?] at hret
      -- split applyOp? σ op
      cases hstep : applyOp? (k := k) σ op with
      | none =>
          -- then run? fails, contradict hret
          simp [hstep] at hret
      | some σ1 =>
          -- hret tells us run? ps σ1 = some σ'
          have hret_ps : run? (k := k) ps σ1 = some σ' := by
            simpa [hstep] using hret

          -- Now analyze hp by cases on op
          cases op with
          | phaseProduct i =>
              have hσ1 : σ1 = σ := by
                simp [applyOp?] at hstep; simp[hstep]
              subst hσ1
              simp [ProgConsumesPts] at hp
              rcases hp with ⟨pt, aTail, ha, hmatch, hpTail⟩
              subst ha
              refine ⟨pt, aTail ++ b, ?_, ?_, ?_⟩
              · simp
              · exact hmatch
              -- remaining: ps ++ q consumes aTail ++ b starting from σ
              -- use IH on ps with hpTail and hret_ps, then append q
              have hps : ProgConsumesPts (k := k) hk σ1 ps aTail := hpTail
              have := ih (σ := σ1) (a := aTail) hps hret_ps
              simpa [List.append_assoc] using this

          | shiftL i n =>
              -- non-phase case: hp is ∃ σ', applyOp? σ op = some σ' ∧ ...
              simp [ProgConsumesPts] at hp
              rcases hp with ⟨σ2, hσ2, hpTail⟩
              -- applyOp? σ op = some σ1 also; hence σ2 = σ1
              have hσ2' : σ2 = σ1 := Option.some.inj (by simpa [hσ2] using hstep)
              subst hσ2'
              -- now use IH on ps with same a
              have := ih (σ := σ2) (a := a) hpTail hret_ps
              -- and rebuild the existential for op at front
              refine ⟨σ2, ?_, ?_⟩
              · exact hstep
              · simpa [List.cons_append] using this

          | shiftR i n =>
              simp [ProgConsumesPts] at hp
              rcases hp with ⟨σ2, hσ2, hpTail⟩
              have hσ2' : σ2 = σ1 := Option.some.inj (by simpa [hσ2] using hstep)
              subst hσ2'
              have := ih (σ := σ2) (a := a) hpTail hret_ps
              refine ⟨σ2, hstep, ?_⟩
              simpa [List.cons_append] using this

          | negate i =>
              simp [ProgConsumesPts] at hp
              rcases hp with ⟨σ2, hσ2, hpTail⟩
              have hσ2' : σ2 = σ1 := Option.some.inj (by simpa [hσ2] using hstep)
              subst hσ2'
              have := ih (σ := σ2) (a := a) hpTail hret_ps
              refine ⟨σ2, hstep, ?_⟩
              simpa [List.cons_append] using this

          | addScaled dst src negSrc sh =>
              simp [ProgConsumesPts] at hp
              simp [ProgConsumesPts]
              have hp' : ProgConsumesPts hk σ1 ps a := by
                have : σ1 = σ.addScaledReg dst src negSrc sh := by
                  exact Option.some.inj (by simp [applyOp?] at hstep;simp_all)
                simpa [this] using hp

              aesop

----------------------------------------------------------------------------------------------------
------------------------------- NO-PHASE ⇒ CONSUMES [] ---------------------------------------------
----------------------------------------------------------------------------------------------------

lemma ProgConsumesPts_of_run?_NoPhase
  {k : ℕ} (hk : k > 0) :
  ∀ (p : Prog k) (_hNo : NoPhase (k := k) p)
    (σ τ : State k),
    run? (k := k) p σ = some τ →
    ProgConsumesPts (k := k) hk σ p [] := by
  intro p
  induction p with
  | nil =>
      intro hNo σ τ hrun
      simp [run?, ProgConsumesPts] at hrun ⊢
  | cons op ps ih =>
      intro hNo σ τ hrun
      -- op can't be phaseProduct
      cases op with
      | phaseProduct i =>
          simp[NoPhase] at hNo
          have := hNo i
          simp at this
      | shiftL i n =>
          simp [run?, applyOp?, ProgConsumesPts] at hrun ⊢
          exact ih (by simp[NoPhase] at *; simp_all) (σ.shiftLReg i n) τ (by simpa [run?, applyOp?] using hrun)

      | shiftR i n =>
          simp [run?, applyOp?, ProgConsumesPts] at hrun ⊢
          cases h : State.shiftRReg? σ i n <;> simp [h] at hrun
          rename_i σ1
          refine ⟨σ1, by simp, ?_⟩
          exact ih (by simp[NoPhase] at *; simp_all) σ1 τ (by simpa [run?, applyOp?, h] using hrun)
      | negate i =>
          simp [run?, applyOp?, ProgConsumesPts] at hrun ⊢
          exact ih (by simp[NoPhase] at *; simp_all) (σ.negateReg i) τ (by simpa [run?, applyOp?] using hrun)

      | addScaled dst src negSrc sh =>
          simp [run?, applyOp?, ProgConsumesPts] at hrun ⊢
          exact ih (by simp[NoPhase] at *; simp_all) (σ.addScaledReg dst src negSrc sh) τ (by simpa [run?, applyOp?] using hrun)

----------------------------------------------------------------------------------------------------
------------------------------- NO-PHASE LEMMAS FOR computeLocal / inverse --------------------------
----------------------------------------------------------------------------------------------------

lemma NoPhase_computeLocal2 {k : ℕ} (hk : 0 < k) (z : Int) :
  NoPhase (k := k) (computeLocal2 (k := k) hk z) := by
  rw[← computeLocal_eq_computeLocal2]
  apply computeLocal_NoPhase

lemma NoPhaseV_apply_Op_inverse_of_NoPhaseV {k : ℕ} :
  ∀ (p : Prog k), NoPhase (k := k) p → NoPhase (k := k) (apply_Op_inverse (k := k) p) := by
  intro p hp
  apply NoPhase_map_inv_of_NoPhase
  apply NoPhase_reverse
  apply hp

----------------------------------------------------------------------------------------------------
------------------------------- BLOCK CONSUMES INT/INF AT START -------------------------------------
----------------------------------------------------------------------------------------------------

theorem block_consumes_int_start
  {k : ℕ} (hk : 0 < k) (z : Int)
  (WF : Prog.WellFormed (k := k) (computeLocal2 (k := k) hk z)) :
  ProgConsumesPts (k := k) hk (State.start_state (k := k))
    (computeLocal2 (k := k) hk z
      ++ [valid_ops.phaseProduct (finZero hk)]
      ++ apply_Op_inverse (k := k) (computeLocal2 (k := k) hk z))
    [Point.int z] := by
  classical
  -- Step 1: computeLocal2 reaches σ₁ and matches row at finZero
  rcases computeLocal2_matches_row_start (k := k) hk z with ⟨σ₁, hrun, hmatch⟩

  let p : Prog k := computeLocal2 (k := k) hk z
  have hNo : NoPhase (k := k) p := by
    simpa [p] using NoPhase_computeLocal2 (k := k) hk z

  -- Step 2: p consumes [] (no phaseProduct) and run? p start = some σ₁
  have hp : ProgConsumesPts (k := k) hk (State.start_state (k := k)) p [] :=
    ProgConsumesPts_of_run?_NoPhase (k := k) hk p hNo _ _ hrun

  -- Step 3: the single phaseProduct consumes [Point.int z] at σ₁
  have hphase : ProgConsumesPts (k := k) hk σ₁ [valid_ops.phaseProduct (finZero hk)] [Point.int z] := by
    -- ProgConsumesPts for a phaseProduct op:
    -- ∃ pt ptsTail, pts = pt::ptsTail ∧ match=true ∧ ProgConsumesPts σ [] ptsTail
    refine ⟨Point.int z, [], by simp, ?_, by simp [ProgConsumesPts]⟩
    simpa using hmatch

  -- Step 4: inverse run? succeeds back to start
  have hrun_inv :
      run? (k := k) (apply_Op_inverse (k := k) p) σ₁ = some (State.start_state (k := k)) := by
    exact State.run?_inverse_undoes_WF (k := k) p WF _ _ hrun

  have hNoInv : NoPhase (k := k) (apply_Op_inverse (k := k) p) :=
    NoPhaseV_apply_Op_inverse_of_NoPhaseV (k := k) p hNo

  have hinv : ProgConsumesPts (k := k) hk σ₁ (apply_Op_inverse (k := k) p) [] :=
    ProgConsumesPts_of_run?_NoPhase (k := k) hk _ hNoInv _ _ hrun_inv

  -- Step 5: glue with append lemma twice
  have h12 :
      ProgConsumesPts (k := k) hk (State.start_state (k := k))
        (p ++ [valid_ops.phaseProduct (finZero hk)]) ([] ++ [Point.int z]) := by
    -- run? (p ++ [phase]) start = some σ₁ because phaseProduct doesn’t change state
    have hrun2 : run? (k := k) (p ++ [valid_ops.phaseProduct (finZero hk)])
        (State.start_state (k := k)) = some σ₁ := by
      rw[run?_append]
      simp[p,hrun,applyOp?]

    exact ProgConsumesPts_append (k := k) hk (State.start_state (k := k)) σ₁ p [valid_ops.phaseProduct (finZero hk)] [] [Point.int z] hp
      (
        by
          have:=State.run?_inverse_undoes_WF (computeLocal2 hk z) WF State.start_state σ₁
          aesop
      )
      (hphase)

  have h123 :
      ProgConsumesPts (k := k) hk (State.start_state (k := k))
        ((p ++ [valid_ops.phaseProduct (finZero hk)]) ++ apply_Op_inverse p)
        (([] ++ [Point.int z]) ++ []) := by
    -- run? of (p ++ [phase]) already computed as some σ₁ above; use hrun2 again
    have hrun2 : run? (k := k) (p ++ [valid_ops.phaseProduct (finZero hk)])
        (State.start_state (k := k)) = some σ₁ := by
      simp [p]
      rw[run?_append]
      simp[hrun,applyOp?]
    exact ProgConsumesPts_append (k := k) hk (State.start_state (k := k)) σ₁ (p ++ [valid_ops.phaseProduct (finZero hk)]) (apply_Op_inverse p) ([] ++ [Point.int z]) [] h12 hrun2 hinv

  simpa [p, List.append_assoc, List.nil_append, List.append_nil] using h123

open Operations

lemma ProgConsumesPts_single_phaseProduct
  {k : ℕ} (hk : k > 0)
  (σ : State k) (i : Fin k) (pt : Point)
  (hmatch : matchesAt_pointRow_state (k := k) hk σ i pt = true) :
  ProgConsumesPts (k := k) hk σ [valid_ops.phaseProduct i] [pt] := by
  -- unfold ProgConsumesPts at the singleton program
  -- phaseProduct case requires an existential witness for head/tail
  refine ⟨pt, ([] : List Point), ?_, ?_, ?_⟩
  · simp
  · exact hmatch
  · -- remaining program is [], remaining points is []
    simp [ProgConsumesPts]

lemma ProgConsumesPts_phaseProduct_inf_start
  {k : ℕ} (hk : k > 0)
  (i : Fin k)
  (hmatch : matchesAt_pointRow_state (k := k) hk (State.start_state (k := k)) i Point.inf = true) :
  ProgConsumesPts (k := k) hk (State.start_state (k := k))
    [valid_ops.phaseProduct i] [Point.inf] := by
  exact ProgConsumesPts_single_phaseProduct (k := k) hk (σ := State.start_state (k := k)) i Point.inf hmatch

open Operations

/-- `start_state` at the last index matches `Point.inf`. -/
lemma matchesAt_pointRow_state_start_inf
  {k : ℕ} (hk : k > 0) :
  let last : Fin k := ⟨k - 1, by
    have hk' : 0 < k := hk
    exact Nat.sub_lt (Nat.succ_le_of_lt hk') (by decide)⟩
  matchesAt_pointRow_state (k := k) hk (State.start_state (k := k)) last Point.inf = true := by
  classical
  cases k with
  | zero =>
      cases hk
  | succ k' =>
      -- In `Fin (k'+1)`, the last index is `k'`.
      let last : Fin (Nat.succ k') := ⟨k', by simp⟩

      -- Prove regEqExpected for the unit vector at `last` against expectedRow .inf
      have hreg :
          regEqExpected (k := Nat.succ k') ((State.start_state (k := Nat.succ k')) last) Point.inf = true := by
        --   regEqExpected_eq_true_iff : regEqExpected r pt = true ↔ ∀ j, r j = expectedRow pt j
        apply (regEqExpected_eq_true_iff (k := Nat.succ k')
          (r := (State.start_state (k := Nat.succ k') last)) (pt := Point.inf)).2
        intro j
        -- both sides are the same “unit vector at last”
        simp [State.start_state, expectedRow, last]

      -- matchesAt_pointRow_state is regEqExpected on σ i
      simpa [matchesAt_pointRow_state_apply, last] using hreg

/-- singleton phaseProduct consumes `[Point.inf]` at start_state. -/
lemma ProgConsumesPts_start_single_inf
  {k : ℕ} (hk : k > 0) :
  ProgConsumesPts (k := k) hk (State.start_state (k := k))
    [valid_ops.phaseProduct ⟨k - 1, by
      have hk' : 0 < k := hk
      exact Nat.sub_lt (Nat.succ_le_of_lt hk') (by decide)⟩]
    [Point.inf] := by
  -- hcov is unused; the statement is purely about the matcher at start_state.
  have hmatch :
      matchesAt_pointRow_state (k := k) hk (State.start_state (k := k))
        ⟨k - 1, by
          have hk' : 0 < k := hk
          exact Nat.sub_lt (Nat.succ_le_of_lt hk') (by decide)⟩
        Point.inf = true := by
    simpa using (matchesAt_pointRow_state_start_inf (k := k) hk)

  exact ProgConsumesPts_single_phaseProduct (k := k) hk
    (σ := State.start_state (k := k))
    (i := ⟨k - 1, by
      have hk' : 0 < k := hk
      exact Nat.sub_lt (Nat.succ_le_of_lt hk') (by decide)⟩)
    (pt := Point.inf)
    hmatch

----------------------------------------------------------------------------------------------------
------------------------------- COVERAGE ⇒ CONSUMPTION (genOps) -------------------------------------
----------------------------------------------------------------------------------------------------

/-- Cancel a covered prefix from a covered append. -/
theorem PhaseProductCoverageM_cancel_prefix
  {k : ℕ}  :
  ∀ {M : MatchesAtState k} {p q : Prog k} {σ σ' : State k} {a b : List Point},
    run? (k := k) p σ = some σ' →
    PhaseProductCoverageM (k := k) M p σ a →
    PhaseProductCoverageM (k := k) M (p ++ q) σ (a ++ b) →
    PhaseProductCoverageM (k := k) M q σ' b := by
  intro M p q σ σ' a b hrun hp hall
  -- Induct on hp (the prefix coverage)
  induction hp generalizing q b σ' with
  | nil =>
      -- p = [], a = []
      simp [run?] at hrun
      cases hrun
      simpa using hall

  | step_op hop hstep hp_rest ih =>
      simp [run?] at hrun
      rename_i op ops σ1 σ2 pts
      -- applyOp? σ op must be some τ
      cases happ : applyOp? (k := k) σ1 op with
      | none =>
          simp [happ] at hrun
      | some τ =>
          have hτ : τ = _ := Option.some.inj (by simpa [happ] using hstep)
          subst hτ
          -- Now peel the same op from hall
          -- (hall must be a step_op with same head op)
          cases hall with
          | step_op hop2 hall_rest =>
              -- hall_rest : coverage of (ps ++ q) at the stepped state
              have := ih (σ' := σ') (q := q) (b := b)
              aesop
          | step_phase hcons _ =>
              -- impossible: head op is not phaseProduct
              exfalso
              rcases hcons with _
              simp_all only [valid_ops.phaseProduct.injEq, forall_eq']

  | step_phase hconsume hp_rest ih =>
      simp [run?, applyOp?] at hrun
      rename_i i ops σ1 pts1 pts2
      cases hall with
      | step_op hop hrest =>
          exfalso
          exact hop i rfl
      | step_phase hconsume_all hrest_all =>
          have hhit :
              List.eraseFirstMatch? (fun pt => M σ1 i pt) (pts1 ++ b)
                = some (pts2 ++ b) :=
            List.eraseFirstMatch?_append_hit (p := fun pt => M σ1 i pt)
              (xs := pts1) (ys := pts2) (zs := b) hconsume
          have hrest' :
              PhaseProductCoverageM M (ops ++ q) σ1 (pts2 ++ b) := by
            aesop
          exact ih (q := q) (σ' := σ') (b := b) hrun hrest'

theorem PhaseProductCoverage_consumesPts
  {k : ℕ} (hk : k > 0) (pts : List Point)
  (hcov : PhaseProductCoverage (k := k) hk (genOpsWithProduct hk pts) State.start_state pts)
  :
  ProgConsumesPts (k := k) hk State.start_state (genOpsWithProduct hk pts) pts := by
  induction pts with
  |nil=>{
    simp[genOpsWithProduct,ProgConsumesPts]
  }
  |cons head tail ih=>{
    simp[genOpsWithProduct]
    have:=ProgConsumesPts_append hk (State.start_state) (State.start_state) (opsForPointWithProduct hk head) (genOpsWithProduct hk tail) [head] tail
    simp[opsForPointWithProduct_returns_to_original hk head] at this
    apply this
    {
      clear this ih
      unfold opsForPointWithProduct
      cases head with
      | int z=>{
        simp
        have:= block_consumes_int_start hk z (by apply computeLocal2_Valid)
        simp_all only [append_assoc, cons_append, nil_append]
      }
      | inf=>{
        simp
        apply ProgConsumesPts_start_single_inf hk
      }
    }
    {
      apply ih
      have hall :
        PhaseProductCoverage hk (opsForPointWithProduct hk head ++ genOpsWithProduct hk tail)
          State.start_state ([head] ++ tail) := by
        simpa [genOpsWithProduct] using hcov

      -- unwrap, cancel prefix, rewrap:
      unfold PhaseProductCoverage at *
      have hrunP : run? (k := k) (opsForPointWithProduct (k := k) hk head)
              (State.start_state (k := k)) = some (State.start_state (k := k)) := by
        apply opsForPointWithProduct_returns_to_original
      have hpref : PhaseProductCoverageM (k := k) (matchesAt_pointRow_state (k := k) hk)
                    (opsForPointWithProduct (k := k) hk head)
                    (State.start_state (k := k)) [head] := by
        have:= genOpsWithProduct_PhaseProductCoverage hk [head]
        simp[genOpsWithProduct] at this
        apply this

      have htailM :=
        PhaseProductCoverageM_cancel_prefix (k := k)
          (M := matchesAt_pointRow_state hk)
          (p := opsForPointWithProduct hk head)
          (q := genOpsWithProduct hk tail)
          (σ := State.start_state) (σ' := State.start_state)
          (a := [head]) (b := tail)
          hrunP hpref hall
      apply htailM
    }
  }

----------------------------------------------------------------------------------------------------
------------------------------- FINAL COMPILED COVERAGE THEOREM ------------------------------------
----------------------------------------------------------------------------------------------------

theorem genOpsWithProduct_compiled_PhaseProductCoverage
  {k : Nat} (hk : 0 < k) (pts : List Point)
  (ctx0 : StCtx k)
  (hV0 : ValidFor (k := k) State.start_state ctx0)
  (hStep : ValidForStep (k := k) ctx0)
  (hρ : ctx0.ρ = fun j ↦ regToInt (stateToSt State.start_state ctx0 j))
  (hWF : Prog.WellFormed (k := k) (genOpsWithProduct hk pts)) :
  PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
    (stateToSt (k := k) State.start_state ctx0)
    (compileProg (k := k) (genOpsWithProduct hk pts) ctx0.curLen).1
    (stateToSt (k := k) State.start_state ctx0) pts := by
  have hcov :
    PhaseProductCoverage (k := k) hk (genOpsWithProduct hk pts) State.start_state pts :=
      genOpsWithProduct_PhaseProductCoverage (k := k) hk pts
  apply PhaseProductCoverage.compileProg_preserves_phaseCoverage
    (k := k) (hk := hk)
    (ops := genOpsWithProduct hk pts)
    (ctx0 := ctx0)
    (hOK := hWF)
    (pts := pts)
    (hcov := hcov)
    (hV0 := hV0)
    (hStep := hStep)
  apply genOpsWithProduct_PrimOKTrace
  apply hV0
  apply PhaseProductCoverage_consumesPts hk
  apply hcov; apply hρ
