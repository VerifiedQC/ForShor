import FastMultiplication.Allocate_dealloc.PhaseCoverage_proof
open Operations PhaseProductCoverage List

/-
  This file supplies two big ingredients needed to prove the *compiled* phase-product
  coverage theorem for `genOpsWithProduct`:

  (1) Safety: `PrimOKTrace` for the compiled primitive program, derived from the fact that
      the source program contains no `shiftR` (NoShiftR).

  (2) Consumption: `ProgConsumesPts` for the source program, derived from the symbolic
      phase coverage theorem plus a prefix-cancellation argument.

  These are combined at the end to prove:
    genOpsWithProduct_compiled_PhaseProductCoverage
-/

----------------------------------------------------------------------------------------------------
------------------------------- SHIFT-FREE PREDICATES ----------------------------------------------
----------------------------------------------------------------------------------------------------

/-
  NoShiftR / NoShiftL are syntactic predicates stating a validated-op program contains
  no `shiftR` / no `shiftL`. They are used to build a “no shiftR” pipeline:

    NoShiftR (source) → PrimOKTrace (compiled)

  because shiftR is the only source op that introduces the tricky “free from LSB”
  safety obligations and divisibility constraints.
-/
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

/-
  S simp lemmas to make `simp [NoShiftR]` / `simp [NoShiftL]` peel the list structure.
  The addScaled simp lemmas are especially useful because many generator programs are
  built from addScaled-only fragments.
-/
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

/-
  NoShiftR_append / NoShiftL_append:
  Both predicates are preserved by append, which is used constantly because most of the
  programs here are concatenations of blocks.
-/
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

/-
  addConstAux/addConstFrom programs are built out of addScaled operations and recursion on n.
  The next lemmas show these helpers introduce no shifts, which feeds into the later
  computeLocal2 “no shifts” proofs.
-/
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

/-
  computeLocalAux is built by concatenating addConstFrom blocks across a list of indices.
  Since addConstFrom has no shifts and append preserves NoShift*, computeLocalAux has no shifts.
-/
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

/-
  computeLocal2 is the “canonical” computeLocalAux call with the standard index list.
  These two lemmas package the no-shift results for the concrete computeLocal2 definition.
-/
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

/-
  These helper lemmas support the fact that apply_Op_inverse preserves NoShiftR
  when the original program has neither shiftL nor shiftR:

    - NoShiftR_tail / NoShiftL_tail extract the tail property from a cons
    - NoShiftR_reverse / NoShiftL_reverse show reverse preserves NoShift*
    - NoShiftR_single_inv_of_noShiftsHead shows inv(op) cannot introduce shiftR
      when op is neither shiftL nor shiftR
    - NoShiftR_map_inv_of_NoShiftL_NoShiftR combines these to handle map inv
    - NoShiftR_apply_Op_inverse_of_NoShiftL_NoShiftR packages the final result
-/
-- helper: pull NoShiftR tail out of NoShiftR (op :: ops)
lemma NoShiftR_tail {k : ℕ} {op : valid_ops k} {ops : List (valid_ops k)} :
  NoShiftR (k := k) (op :: ops) → NoShiftR (k := k) ops := by
  intro h
  cases op <;> simp [NoShiftR] at h <;> simp_all

-- helper: pull NoShiftR head out of NoShiftR (op :: ops)
lemma NoShiftR_head {k : ℕ} {op : valid_ops k} {ops : List (valid_ops k)} :
  NoShiftR (k := k) (op :: ops) → NoShiftR (k := k) [op] := by
  intro h
  cases op <;> simp [NoShiftR] at h <;> simp_all[NoShiftR]

-- helper: pull NoShiftL tail out of NoShiftL (op :: ops)
lemma NoShiftL_tail {k : ℕ} {op : valid_ops k} {ops : List (valid_ops k)} :
  NoShiftL (k := k) (op :: ops) → NoShiftL (k := k) ops := by
  intro h
  cases op <;> simp [NoShiftL] at h <;> simp_all

-- helper: pull NoShiftL head out of NoShiftL (op :: ops)
lemma NoShiftL_head {k : ℕ} {op : valid_ops k} {ops : List (valid_ops k)} :
  NoShiftL (k := k) (op :: ops) → NoShiftL (k := k) [op] := by
  intro h
  cases op <;> simp [NoShiftL] at h <;> simp_all[NoShiftL]

/-- If `op` is not a shiftL or shiftR, then `inv op` is not a shiftR. -/
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

/-
  opsForPointWithProduct produces a block per point:
  - for inf: just a phaseProduct
  - for int z: computeLocal2 z ++ [phaseProduct dst] ++ inverse(computeLocal2 z)

  The next lemmas show these blocks contain no shiftR, and then the concatenation over pts
  contains no shiftR. This is the key prerequisite for the PrimOKTrace pipeline.
-/
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

/-
  runCtxPrim_compileProg:
  Bookkeeping alignment lemma for compileProg. It states that running the bookkeeping
  interpreter runCtxPrim on the compiled primitive ops yields exactly the curLen list
  returned by compileProg.

  This is used whenever proofs need to identify the “post-state context” for the tail
  in append splits (analogous to runCtxPrim_compile1).
-/
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

/-
  This section builds a chain:
    NoShiftR (source program) → PrimOKTrace (compiled program)

  The core reason is that shiftR is ruled out, so compile1 outputs are composed of
  safe primitive fragments (Alloc, negate, Add, phaseProduct) plus the addScaled
  compilation pipeline which is already proven safe.
-/
lemma FitsSigned_zero_of_pos (w : Nat) (hw : 0 < w) : FitsSigned w (0 : ℤ) := by
  refine ⟨hw, ?_, ?_⟩<;>simp

/-
  PrimOKTrace_compile1:
  Local safety for compile1 on a single op, given:
  - base widths are constant across registers
  - curLen has correct length
  - the op is not shiftR (encoded as NoShiftR [op])
-/
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

/-
  compile1_preserves_curLen_len:
  compile1 does not change the length of curLen. This is needed to keep the “Fin index in range”
  invariant when iterating compileProg and applying induction hypotheses.
-/
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

/-
  BaseWConst:
  Convenience predicate: baseW constant across registers. This is a common hypothesis
  for PrimOKTrace proofs because Add safety wants width equalities, and constant baseW
  lets those reduce to curLen equalities.
-/
def BaseWConst {k : ℕ} (ctx : StCtx k) : Prop :=
  ∀ i j : Fin k, ctx.baseW i = ctx.baseW j

/-
  tail_PrimOKTrace_after_compile1:
  Helper for the cons case of compileProg safety induction: after compiling the head op,
  re-run the IH on the tail under the updated context `{ctx with curLen := curLen1}`.
-/
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

/-
  PrimOKTrace_compile1_of_NoShiftR_head:
  Specializes PrimOKTrace_compile1 to a context `{ctx0 with curLen := curLen}`, taking
  NoShiftR [op] as the condition excluding shiftR.
-/
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

/-
  PrimOKTrace_compileProg_of_NoShiftR_general:
  Main structural theorem: if a program has NoShiftR and base widths are constant and curLen length is k,
  then the compiled primitive program has PrimOKTrace.

  This is the engine used later to derive genOpsWithProduct_PrimOKTrace.
-/
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

/-
  PrimOKTrace_compileProg_NoShiftR:
  Friendly wrapper around the general theorem when the inputs are already in the shape
  used throughout (ctx, baseW equality, curLen = ctx.curLen, etc.).
-/
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

/-
  genOpsWithProduct_PrimOKTrace:
  Apply the NoShiftR → PrimOKTrace pipeline to `genOpsWithProduct`:
  - NoShiftR_genOpsWithProduct gives NoShiftR
  - ValidFor start_state supplies baseW const and curLen length
  - PrimOKTrace_compileProg_NoShiftR yields PrimOKTrace for the compiled program
-/
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

/-
  This section proves that the generated symbolic program consumes exactly the input
  point list `pts` in order. This is later used as a hypothesis in the phase coverage
  transfer theorem to the compiled primitive program.
-/

/-- When `eraseFirstMatch?` succeeds during a phaseProduct check,
    it must be because the *head* matches. -/
def ConsumeHeadOK {k : ℕ} (hk : k > 0) : Prop :=
  ∀ (σ : State k) (i : Fin k) (pts pts' : List Point),
    List.eraseFirstMatch? (fun pt => matchesAt_pointRow_state (k := k) hk σ i pt) pts = some pts' →
      ∃ pt ptsTail,
        pts = pt :: ptsTail ∧
        pts' = ptsTail ∧
        matchesAt_pointRow_state (k := k) hk σ i pt = true

/-
  ProgConsumesPts_append:
  Concatenation rule for the consumption predicate: if p consumes a and reaches σ',
  and q consumes b from σ', then p++q consumes a++b from σ.
-/
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

/-
  ProgConsumesPts_of_run?_NoPhase:
  If a program has no phaseProduct ops (NoPhase), then it consumes [].
  This is used for computeLocal blocks and inverse blocks (both NoPhase).
-/
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

/-
  NoPhase_computeLocal2 / NoPhaseV_apply_Op_inverse_of_NoPhaseV:
  computeLocal2 and its inverse block contain no phaseProduct ops, so they consume [].
  These facts feed into the “block consumes exactly one point” theorem for int points.
-/
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

/-
  block_consumes_int_start:
  For an int point z, the “block”
    computeLocal2 z ++ [phaseProduct dst] ++ inverse(computeLocal2 z)
  consumes exactly [Point.int z] starting from start_state.

  Proof pattern:
  - computeLocal2 reaches σ₁ and matches row at dst
  - computeLocal2 consumes [] because it has NoPhase
  - singleton phaseProduct consumes [Point.int z]
  - inverse consumes [] and returns to start_state
  - glue with ProgConsumesPts_append twice.
-/
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
    have hrun2 : run? (k := k) (p ++ [valid_ops.phaseProduct (finZero hk)])
        (State.start_state (k := k)) = some σ₁ := by
      simp [p]
      rw[run?_append]
      simp[hrun,applyOp?]
    exact ProgConsumesPts_append (k := k) hk (State.start_state (k := k)) σ₁ (p ++ [valid_ops.phaseProduct (finZero hk)]) (apply_Op_inverse p) ([] ++ [Point.int z]) [] h12 hrun2 hinv

  simpa [p, List.append_assoc, List.nil_append, List.append_nil] using h123

open Operations

/-
  ProgConsumesPts_single_phaseProduct:
  Convenience lemma: a singleton phaseProduct consumes a singleton point list if the head matches.
-/
lemma ProgConsumesPts_single_phaseProduct
  {k : ℕ} (hk : k > 0)
  (σ : State k) (i : Fin k) (pt : Point)
  (hmatch : matchesAt_pointRow_state (k := k) hk σ i pt = true) :
  ProgConsumesPts (k := k) hk σ [valid_ops.phaseProduct i] [pt] := by
  refine ⟨pt, ([] : List Point), ?_, ?_, ?_⟩
  · simp
  · exact hmatch
  · simp [ProgConsumesPts]

lemma ProgConsumesPts_phaseProduct_inf_start
  {k : ℕ} (hk : k > 0)
  (i : Fin k)
  (hmatch : matchesAt_pointRow_state (k := k) hk (State.start_state (k := k)) i Point.inf = true) :
  ProgConsumesPts (k := k) hk (State.start_state (k := k))
    [valid_ops.phaseProduct i] [Point.inf] := by
  exact ProgConsumesPts_single_phaseProduct (k := k) hk (σ := State.start_state (k := k)) i Point.inf hmatch

open Operations

/-
  matchesAt_pointRow_state_start_inf:
  Establishes that start_state matches the .inf point at the last index.
  This provides the “inf block consumes Point.inf” base fact.
-/
/- `start_state` at the last index matches `Point.inf`. -/
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
      let last : Fin (Nat.succ k') := ⟨k', by simp⟩

      have hreg :
          regEqExpected (k := Nat.succ k') ((State.start_state (k := Nat.succ k')) last) Point.inf = true := by
        apply (regEqExpected_eq_true_iff (k := Nat.succ k')
          (r := (State.start_state (k := Nat.succ k') last)) (pt := Point.inf)).2
        intro j
        simp [State.start_state, expectedRow, last]

      simpa [matchesAt_pointRow_state_apply, last] using hreg

/-
  ProgConsumesPts_start_single_inf:
  Packs the “start_state matches inf at last index” into a ProgConsumesPts statement
  for a singleton phaseProduct program.
-/
/- singleton phaseProduct consumes `[Point.inf]` at start_state. -/
lemma ProgConsumesPts_start_single_inf
  {k : ℕ} (hk : k > 0) :
  ProgConsumesPts (k := k) hk (State.start_state (k := k))
    [valid_ops.phaseProduct ⟨k - 1, by
      have hk' : 0 < k := hk
      exact Nat.sub_lt (Nat.succ_le_of_lt hk') (by decide)⟩]
    [Point.inf] := by
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

/-
  PhaseProductCoverageM_cancel_prefix:
  Cancellation lemma for symbolic coverage: if p has coverage consuming a and run? p σ = some σ',
  and p++q has coverage consuming a++b from σ, then q has coverage consuming b from σ'.
  This is the key tool used to extract tail coverage in the induction for consumesPts.
-/
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
          cases hall with
          | step_op hop2 hall_rest =>
              have := ih (σ' := σ') (q := q) (b := b)
              aesop
          | step_phase hcons _ =>
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

/-
  PhaseProductCoverage_consumesPts:
  Main consumption theorem for genOpsWithProduct. It derives ProgConsumesPts from the known
  symbolic coverage theorem by induction on the point list. The critical step is:
  - build consumption for the head block (int or inf)
  - cancel the head coverage from the full coverage to obtain tail coverage (using the cancel lemma)
  - apply IH to tail, then append consumptions.
-/
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
------------------------------- GEN_OPS WF Lemmas ------------------------------------
----------------------------------------------------------------------------------------------------

open Operations

namespace Prog

/-- `WellFormed` is closed under cons. -/
lemma WF_cons_intro {k : ℕ} {op : valid_ops k} {p : Prog k} :
    OpOK (k := k) op → WellFormed (k := k) p → WellFormed (k := k) (op :: p) := by
  intro hopOK hWF
  unfold WellFormed at *
  intro op' hop'
  simp at hop'
  rcases hop' with rfl | hop'
  · exact hopOK
  · exact hWF op' hop'

/-- `WellFormed` is closed under append. -/
lemma WF_append {k : ℕ} {p q : Prog k} :
    WellFormed (k := k) p → WellFormed (k := k) q → WellFormed (k := k) (p ++ q) := by
  intro hp hq
  unfold WellFormed at *
  intro op hop
  simp at hop
  rcases hop with hop | hop
  · exact hp op hop
  · exact hq op hop

@[simp] lemma WF_nil {k : ℕ} : WellFormed (k := k) ([] : Prog k) := by
  unfold WellFormed
  intro op hop
  cases hop

@[simp] lemma OpOK_phaseProduct {k : ℕ} (i : Fin k) :
    OpOK (k := k) (valid_ops.phaseProduct i) := by
  simp [OpOK]

@[simp] lemma OpOK_shiftL {k : ℕ} (i : Fin k) (n : Nat) :
    OpOK (k := k) (valid_ops.shiftL i n) := by
  simp [OpOK]

@[simp] lemma OpOK_shiftR {k : ℕ} (i : Fin k) (n : Nat) :
    OpOK (k := k) (valid_ops.shiftR i n) := by
  simp [OpOK]

@[simp] lemma OpOK_negate {k : ℕ} (i : Fin k) :
    OpOK (k := k) (valid_ops.negate i) := by
  simp [OpOK]

/-- The only nontrivial OpOK case is `addScaled`: it requires `dst ≠ src`. -/
@[simp] lemma OpOK_addScaled {k : ℕ} (dst src : Fin k) (b : Bool) (sh : Nat) :
    OpOK (k := k) (valid_ops.addScaled dst src (negSrc := b) sh) ↔ dst ≠ src := by
  simp [OpOK]

end Prog

open Prog

/-
  Now prove WF for your synthesis pieces.

  Assumes your current definitions exist in scope:
  - addConstAux
  - addConstFrom
  - computeLocalAux
  - computeLocal2
  - nonzeroFins
  - opsForPointWithProduct
  - genOpsWithProduct
-/

section WF_Synthesis

/-- `addConstAux` emits only `addScaled dst src ...`, so WF holds if `dst ≠ src`. -/
lemma WF_addConstAux {k : ℕ} (dst src : Fin k) (neg' : Bool) (hds : dst ≠ src) :
    ∀ (n sh : Nat), Prog.WellFormed (k := k) (addConstAux (k := k) dst src neg' n sh) := by
  -- strong induction because the recursive call is on (n/2)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro sh
      cases n with
      | zero =>
          simp [addConstAux, Prog.WellFormed]
      | succ n =>
          -- Let N = n+1 for readability
          set N : Nat := Nat.succ n
          -- the recursive argument is N/2, and it is strictly smaller than N
          have hlt : (N / 2) < N := by
            simpa [N] using Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 2)

          have hrest :
              Prog.WellFormed (k := k)
                (addConstAux (k := k) dst src neg' (N / 2) (sh + 1)) :=
            ih (N / 2) hlt (sh + 1)

          by_cases hOdd : Odd N
          · -- odd case: head is addScaled :: rest
            have hopOK : Prog.OpOK (k := k) (valid_ops.addScaled dst src (negSrc := neg') sh) := by
              -- OpOK for addScaled is dst ≠ src
              simpa [Prog.OpOK] using hds
            have hcons :
                Prog.WellFormed (k := k)
                  (valid_ops.addScaled dst src (negSrc := neg') sh
                    :: addConstAux (k := k) dst src neg' (N / 2) (sh + 1)) :=
              Prog.WF_cons_intro (k := k) (op := valid_ops.addScaled dst src (negSrc := neg') sh)
                hopOK hrest
            simpa [addConstAux, N, hOdd] using hcons

          ·
            simpa [addConstAux, N, hOdd] using hrest

/-- `addConstFrom` is WF if `dst ≠ src`. -/
lemma WF_addConstFrom {k : ℕ} (dst src : Fin k) (c : Int) (hds : dst ≠ src) :
    Prog.WellFormed (k := k) (addConstFrom (k := k) dst src c) := by
  classical
  by_cases hc : c = 0
  · simp [addConstFrom, hc, Prog.WellFormed]
  ·
    -- unfold to addConstAux
    simp [addConstFrom, hc]
    exact WF_addConstAux (k := k) (dst := dst) (src := src) (neg' := (c < 0)) (hds := hds) (n := Int.natAbs c) (sh := 0)

lemma WF_computeLocalAux_finZero {k : ℕ} (hk : 0 < k) (z : Int) :
  ∀ (js : List (Fin k)),
    (∀ j, j ∈ js → finZero hk ≠ j) →
    (computeLocalAux (k := k) hk z js).WellFormed := by
  intro js
  induction js with
  | nil =>
      intro _; simp [computeLocalAux, Prog.WellFormed]
  | cons j js ih =>
      intro h
      have hdstj : finZero hk ≠ j := h j (by simp)
      have hhead :
          (addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat))).WellFormed :=
        WF_addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat)) hdstj
      have htail :
          (computeLocalAux (k := k) hk z js).WellFormed :=
        ih (by
          intro j' hj'
          exact h j' (by simp [hj']))
      simpa [computeLocalAux] using Prog.WF_append (k := k) hhead htail



/-- Every element of `nonzeroFins hk` is not `finZero hk`. -/
lemma mem_nonzeroFins_ne_zero {k : ℕ} (hk : 0 < k) :
    ∀ j : Fin k, j ∈ nonzeroFins (k := k) hk → j ≠ finZero hk := by
  classical
  intro j hj
  unfold nonzeroFins at hj
  have : decide (j ≠ finZero hk) = true := by
    have := List.mem_filter.1 hj
    exact this.2
  exact by aesop

/-- `computeLocal2` is WF. -/
lemma WF_computeLocal2 {k : ℕ} (hk : 0 < k) (z : Int) :
    Prog.WellFormed (k := k) (computeLocal2 (k := k) hk z) := by
  unfold computeLocal2
  refine WF_computeLocalAux_finZero (k := k) hk z (js := nonzeroFins (k := k) hk) ?_
  intro j hj
  have : j ≠ finZero hk := mem_nonzeroFins_ne_zero (k := k) hk j hj
  exact Ne.symm this

/-- `opsForPointWithProduct` is WF (using your `apply_Op_inverse_preserves_WF`). -/
lemma WF_opsForPointWithProduct {k : ℕ} (hk : 0 < k) :
    ∀ pt, Prog.WellFormed (k := k) (opsForPointWithProduct (k := k) hk pt)
  | .inf => by
      simp [opsForPointWithProduct, Prog.WellFormed, Prog.OpOK]
  | .int z => by
      let dst : Fin k := finZero hk
      let l : Prog k := computeLocal2 (k := k) hk z
      have hL : Prog.WellFormed (k := k) l := by
        simpa [l] using WF_computeLocal2 (k := k) hk z
      have hP : Prog.WellFormed (k := k) ([valid_ops.phaseProduct dst] : Prog k) := by
        simp [Prog.WellFormed, Prog.OpOK]
      have hInv : Prog.WellFormed (k := k) (apply_Op_inverse (k := k) l) := by
        exact apply_Op_inverse_preserves_WF (k := k) (p := l) hL
      have hLP : Prog.WellFormed (k := k) (l ++ [valid_ops.phaseProduct dst]) :=
        Prog.WF_append (k := k) hL hP
      have hAll : Prog.WellFormed (k := k) ((l ++ [valid_ops.phaseProduct dst]) ++ apply_Op_inverse l) :=
        Prog.WF_append (k := k) hLP hInv
      simpa [opsForPointWithProduct, l, dst, List.append_assoc] using hAll

/-- Finally, `genOpsWithProduct` is WF for any point list. -/
theorem WF_genOpsWithProduct {k : ℕ} (hk : 0 < k) :
    ∀ (pts : List Point),
      Prog.WellFormed (k := k) (genOpsWithProduct (k := k) hk pts) := by
  intro pts
  induction pts with
  | nil =>
      simp [genOpsWithProduct, Prog.WellFormed]
  | cons pt pts ih =>
      have hHead : Prog.WellFormed (k := k) (opsForPointWithProduct (k := k) hk pt) :=
        WF_opsForPointWithProduct (k := k) hk pt
      have hTail : Prog.WellFormed (k := k) (genOpsWithProduct (k := k) hk pts) :=
        ih
      simpa [genOpsWithProduct] using Prog.WF_append (k := k) hHead hTail

end WF_Synthesis


----------------------------------------------------------------------------------------------------
------------------------------- FINAL COMPILED COVERAGE THEOREM ------------------------------------
----------------------------------------------------------------------------------------------------

/-
  genOpsWithProduct_compiled_PhaseProductCoverage:
  Final assembly theorem.

  Inputs provide:
  - ValidFor/ValidForStep for start_state in the concrete ctx0
  - ρ alignment between ctx0.ρ and the initial concrete state
  - WellFormed for the generated source program

  The proof supplies:
  - symbolic coverage (genOpsWithProduct_PhaseProductCoverage)
  - PrimOKTrace for compiled program (genOpsWithProduct_PrimOKTrace)
  - ProgConsumesPts for source program (PhaseProductCoverage_consumesPts)

  Then it invokes PhaseProductCoverage.compileProg_preserves_phaseCoverage to transfer
  coverage to the compiled primitive program.
-/
theorem genOpsWithProduct_compiled_PhaseProductCoverage
  {k : Nat} (hk : 0 < k) (pts : List Point)
  (ctx0 : StCtx k)
  (hV0 : ValidFor (k := k) State.start_state ctx0)
  (hStep : ValidForStep (k := k) ctx0)
  (hρ : ctx0.ρ = fun j ↦ regToInt (stateToSt State.start_state ctx0 j)) :
  PhaseProduct_PrimOps.PhaseProductCoverage_prim (k := k)
    (stateToSt (k := k) State.start_state ctx0)
    (compileProg (k := k) (genOpsWithProduct hk pts) ctx0.curLen).1
    (stateToSt (k := k) State.start_state ctx0) pts := by
  have hcov :
    PhaseProductCoverage (k := k) hk (genOpsWithProduct hk pts) State.start_state pts :=
      genOpsWithProduct_PhaseProductCoverage (k := k) hk pts
  have hWF : Prog.WellFormed (k := k) (genOpsWithProduct hk pts):= by {
    apply WF_genOpsWithProduct
  }
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
