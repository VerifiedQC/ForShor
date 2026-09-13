import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Layout
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Widths

/-!
# Phase-Product Compiler: Compilation

The annotated-operation compiler: annotating phase-product leaves with
interpolation terms (`AnnotatedOp`, `annotatePhaseTermsAux`), the per-chunk
allocation/deallocation gates, and the full signed/controlled-signed
compilers (`compileOpsToSignedGate`, `compileOpsToCSignedGate`,
`controlPhaseLeaves`).
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Annotated operations and phase-product counting
========================================================= -/

/-- A source operation plus the interpolation term assigned to a phase-product leaf, if any. -/
structure AnnotatedOp (k : ℕ) where
  op : valid_ops k
  phaseTerm? : Option (Fin (q k))

/-- Attach interpolation-term indices to phase-product operations in source order. -/
def annotatePhaseTermsAux (k n : ℕ) (ops : List (valid_ops k)) : List (AnnotatedOp k) :=
  match ops with
  | [] => []
  | op :: rest =>
      match op with
      | .phaseProduct _i =>
          let ann : Option (Fin (q k)) :=
            if h : n < q k then some ⟨n, h⟩ else none
          ⟨op, ann⟩ :: annotatePhaseTermsAux k (n+1) rest
      | _ =>
          ⟨op, none⟩ :: annotatePhaseTermsAux k n rest

/-- Number of recursive phase-product leaves in a source program. -/
def phaseProductCount {k : ℕ} : List (valid_ops k) → ℕ
  | [] => 0
  | op :: ops =>
      match op with
      | .phaseProduct _ => phaseProductCount ops + 1
      | _               => phaseProductCount ops

/-- Allocation gate for a single chunk. Lower chunks are zero-extended;
    the top chunk is sign-extended. -/

def allocChunkGate {k : ℕ} (i : Fin k) (src dst : ExtReg) : Gate :=
  let n := extraDelta src dst
  if _h0 : n = 0 then
    Gate.id
  else if _htop : isTopChunk i then
    Gate.signExtend src n
  else
    Gate.zeroExtend src n

/-- Matching deallocation gate for a single chunk. -/
def deallocChunkGate {k : ℕ} (i : Fin k) (src dst : ExtReg) : Gate :=
  let n := extraDelta src dst
  if _h0 : n = 0 then
    Gate.id
  else if _htop : isTopChunk i then
    Gate.signDealloc src n
  else
    Gate.zeroDealloc src n

/-- Allocation program for the first `n` chunks, in increasing order `0,1,...,n-1`. -/
def compileSignedAllocationsAux {k : ℕ} (src dst : LayoutState k) :
    ∀ (n : ℕ), n ≤ k → Gate
  | 0, _ => Gate.id
  | n + 1, hn =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      compileSignedAllocationsAux src dst n hk' ;;
      allocChunkGate i (src.xslot i) (dst.xslot i) ;;
      allocChunkGate i (src.zslot i) (dst.zslot i)

/-- Emit all chunk allocations before the signed arithmetic body. -/
def compileSignedAllocations (k : ℕ) (src dst : LayoutState k) : Gate :=
  compileSignedAllocationsAux src dst k (le_rfl)

/-- Deallocation program for the first `n` chunks, in decreasing order `n-1,...,1,0`. -/
def compileSignedDeallocationsAux {k : ℕ} (src dst : LayoutState k) :
    ∀ (n : ℕ), n ≤ k → Gate
  | 0, _ => Gate.id
  | n + 1, hn =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
      deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
      compileSignedDeallocationsAux src dst n hk'

/-- Emit all chunk deallocations after the signed arithmetic body. -/
def compileSignedDeallocations (k : ℕ) (src dst : LayoutState k) : Gate :=
  compileSignedDeallocationsAux src dst k (le_rfl)

/-! =========================================================
    Compilation from `valid_ops` to `Gate`
========================================================= -/

/-- Signed compiler for annotated ops.  The layout state already contains
    enough extra width in each slot, so compilation only emits gates and does
    not resize the state further. -/

def compileAnnotatedOpsToSignedGateAux
  (k : ℕ) (hk : 1 < k)
  (phi : Angle)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (ops : List (AnnotatedOp k)) : Gate :=
  match ops with
  | [] => Gate.id
  | ⟨op, term?⟩ :: rest =>
      let tail := compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st rest
      match op with
      | .shiftL i n =>
          Gate.ShiftL (st.xslot i) n ;;
          Gate.ShiftL (st.zslot i) n ;; tail
      | .shiftR i n =>
          Gate.ShiftR (st.xslot i) n ;;
          Gate.ShiftR (st.zslot i) n ;; tail
      | .negate i =>
          Gate.Negate (st.xslot i) ;;
          Gate.Negate (st.zslot i) ;; tail
      | .addScaled dst src negsrc sh =>
          Gate.AddScaled (st.xslot dst) (st.xslot src) negsrc sh ;;
          Gate.AddScaled (st.zslot dst) (st.zslot src) negsrc sh ;; tail
      | .phaseProduct i =>
          match term? with
          | some l =>
              Gate.SignedPhaseProd
                (phi * phaseCoeff l)
                (st.xslot i)
                (st.zslot i) ;; tail
          | none =>
              tail

/-- Full signed phase-product lowering: allocate widths, compile the annotated body, then deallocate. -/
def compileOpsToSignedGate
  (k : ℕ) (hk : 1 < k) (phi : Angle) (x z : ExtReg) (layout : Gate.PhaseProductLayout x z k)
  (phaseCoeff : Fin (q k) → ℚ) (ops : List (valid_ops k)) : Gate :=
  let annOps : List (AnnotatedOp k) :=
    annotatePhaseTermsAux k 0 ops
  let need : NeededWidths k :=
    scanNeededWidths x z ops
  let stInit : LayoutState k :=
    initSignedLayoutState layout
  let stFinal : LayoutState k :=
    targetSignedLayoutState stInit need
  let allocs : Gate :=
    compileSignedAllocations k stInit stFinal
  let body : Gate :=
    compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff stFinal annOps
  let deallocs : Gate :=
    compileSignedDeallocations k stInit stFinal
  allocs ;; body ;; deallocs

/-- Add a shared control to phase-product leaves while leaving structural and arithmetic gates unchanged. -/
def controlPhaseLeaves (ctrl : ℕ) : Gate → Gate
  | .id => .id
  | .seq U V => controlPhaseLeaves ctrl U ;; controlPhaseLeaves ctrl V
  | .SignedPhaseProd phi x z => .CSignedPhaseProd ctrl phi x z
  | .ShiftL r n => .ShiftL r n
  | .ShiftR r n => .ShiftR r n
  | .Negate r => .Negate r
  | .AddScaled dst src negSrc sh => .AddScaled dst src negSrc sh
  | .zeroExtend r n => .zeroExtend r n
  | .signExtend r n => .signExtend r n
  | .zeroDealloc r n => .zeroDealloc r n
  | .signDealloc r n => .signDealloc r n
  | U => U

/-- Controlled signed lowering obtained by compiling first and controlling phase leaves. -/
def compileOpsToCSignedGate
    (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k) (coeff : Fin (q k) → ℚ) (ops : Prog k) : Gate :=
  controlPhaseLeaves ctrl (compileOpsToSignedGate k hk phi x z layout coeff ops)

/-- The control qubit is outside every child register touched by a phase-product layout. -/
def Gate.PhaseProductLayout.ControlDisjoint {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (ctrl : ℕ) : Prop :=
  (∀ i, ctrl ∉ (layout.xSplit.child i).ownedQubits) ∧ (∀ i, ctrl ∉ (layout.zSplit.child i).ownedQubits)

/-! =========================================================
    Annotation and phase-product counting
    These lemmas are pure program-bookkeeping facts. They keep phase-product
    term indices stable under append and prove that local arithmetic helper
    programs do not introduce recursive phase-product leaves.
========================================================= -/

/-- Compatibility alias for older files: every concrete `Reg` already carries `Nodup`. -/

@[simp] lemma compileSignedAllocationsAux_zero {k : ℕ} (src dst : LayoutState k) (h : 0 ≤ k) :
  compileSignedAllocationsAux src dst 0 h = Gate.id := rfl

@[simp] lemma compileSignedAllocationsAux_succ {k : ℕ} (src dst : LayoutState k)
  (n : ℕ) (hn : n + 1 ≤ k) :
  compileSignedAllocationsAux src dst (n + 1) hn
    =
  let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
  let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
  compileSignedAllocationsAux src dst n hk' ;;
  allocChunkGate i (src.xslot i) (dst.xslot i) ;;
  allocChunkGate i (src.zslot i) (dst.zslot i) := rfl

@[simp] lemma compileSignedDeallocationsAux_zero {k : ℕ} (src dst : LayoutState k) (h : 0 ≤ k) :
  compileSignedDeallocationsAux src dst 0 h = Gate.id := rfl

@[simp] lemma compileSignedDeallocationsAux_succ {k : ℕ} (src dst : LayoutState k)
  (n : ℕ) (hn : n + 1 ≤ k) :
  compileSignedDeallocationsAux src dst (n + 1) hn
    =
  let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
  let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
  deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
  deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
  compileSignedDeallocationsAux src dst n hk' := rfl

/-! =========================================================
    Control wrappers for allocation and deallocation

    These structural lemmas are needed to define the controlled recursive
    lowering plan without importing proof modules.
========================================================= -/

/-- Control-phase wrapping leaves allocation gates unchanged. -/
lemma controlPhaseLeaves_allocChunkGate
  {k : ℕ} (ctrl : ℕ) (i : Fin k) (src dst : ExtReg) :
  controlPhaseLeaves ctrl (allocChunkGate i src dst) = allocChunkGate i src dst := by
  unfold allocChunkGate
  by_cases htop : isTopChunk i <;>
    by_cases hδ : extraDelta src dst = 0 <;>
    simp [htop, hδ, controlPhaseLeaves]

/-- Control-phase wrapping leaves deallocation gates unchanged. -/
lemma controlPhaseLeaves_deallocChunkGate
  {k : ℕ} (ctrl : ℕ) (i : Fin k) (src dst : ExtReg) :
  controlPhaseLeaves ctrl (deallocChunkGate i src dst) = deallocChunkGate i src dst := by
  unfold deallocChunkGate
  by_cases htop : isTopChunk i <;>
    by_cases hδ : extraDelta src dst = 0 <;>
    simp [htop, hδ, controlPhaseLeaves]

/-- Control-phase wrapping leaves allocation prefixes unchanged. -/
lemma controlPhaseLeaves_compileSignedAllocationsAux
  {k : ℕ} (ctrl : ℕ) (src dst : LayoutState k) :
  ∀ (n : ℕ) (hn : n ≤ k),
    controlPhaseLeaves ctrl (compileSignedAllocationsAux src dst n hn) =
      compileSignedAllocationsAux src dst n hn := by
  intro n hn
  induction n with
  | zero =>
      simp [compileSignedAllocationsAux_zero, controlPhaseLeaves]
  | succ n ih =>
      rw [compileSignedAllocationsAux_succ (src := src) (dst := dst) (n := n) (hn := hn)]
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      simp [controlPhaseLeaves, ih hk',
        controlPhaseLeaves_allocChunkGate]

/-- Control-phase wrapping leaves full allocation unchanged. -/
lemma controlPhaseLeaves_compileSignedAllocations
  {k : ℕ} (ctrl : ℕ) (src dst : LayoutState k) :
  controlPhaseLeaves ctrl (compileSignedAllocations k src dst) =
    compileSignedAllocations k src dst := by
  exact controlPhaseLeaves_compileSignedAllocationsAux ctrl src dst k le_rfl

/-- Control-phase wrapping leaves deallocation prefixes unchanged. -/
lemma controlPhaseLeaves_compileSignedDeallocationsAux
  {k : ℕ} (ctrl : ℕ) (src dst : LayoutState k) :
  ∀ (n : ℕ) (hn : n ≤ k),
    controlPhaseLeaves ctrl (compileSignedDeallocationsAux src dst n hn) =
      compileSignedDeallocationsAux src dst n hn := by
  intro n hn
  induction n with
  | zero =>
      simp [compileSignedDeallocationsAux_zero, controlPhaseLeaves]
  | succ n ih =>
      rw [compileSignedDeallocationsAux_succ (src := src) (dst := dst) (n := n) (hn := hn)]
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      simp [controlPhaseLeaves, ih hk',
        controlPhaseLeaves_deallocChunkGate]

/-- Control-phase wrapping leaves full deallocation unchanged. -/
lemma controlPhaseLeaves_compileSignedDeallocations
  {k : ℕ} (ctrl : ℕ) (src dst : LayoutState k) :
  controlPhaseLeaves ctrl (compileSignedDeallocations k src dst) =
    compileSignedDeallocations k src dst := by
  exact controlPhaseLeaves_compileSignedDeallocationsAux ctrl src dst k le_rfl


end Shor
