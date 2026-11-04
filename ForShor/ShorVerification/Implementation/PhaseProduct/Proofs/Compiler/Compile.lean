import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Coefficients
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Layout

/-!
# Phase-Product Compiler: Compilation

The annotated-operation compiler: annotating phase-product leaves with
interpolation terms (`AnnotatedOp`, `annotatePhaseTermsAux`), the per-chunk
allocation/deallocation gates, and the full signed/controlled-signed
compilers (`compileOpsToSignedGate` and its width-rule form `compileOpsToSignedGateBy`,
`controlPhaseLeaves`).
-/

/-! ---------------------------------------------------------
    Unfolding equations for the allocation and deallocation prefixes
--------------------------------------------------------- -/

namespace Shor

theorem compileOpsToSignedGateBy_scan
    (k : ℕ) (hk : 1 < k) (phi : Angle) (x z : ExtReg) (layout : Gate.PhaseProductLayout x z k)
    (phaseCoeff : Fin (q k) → ℚ) (ops : List (Operations.valid_ops k)) :
    compileOpsToSignedGateBy .scan k hk phi x z layout phaseCoeff ops
      = compileOpsToSignedGate k hk phi x z layout phaseCoeff ops := rfl

theorem compileOpsToCSignedGateBy_scan
    (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k) (coeff : Fin (q k) → ℚ) (ops : Prog k) :
    compileOpsToCSignedGateBy .scan k hk ctrl phi x z layout coeff ops
      = controlPhaseLeaves ctrl (compileOpsToSignedGate k hk phi x z layout coeff ops) := rfl

@[simp] lemma compileSignedAllocationsAux_zero {k : ℕ} (src dst : LayoutState k) (h : 0 ≤ k) :
    compileSignedAllocationsAux src dst 0 h = Gate.id := rfl

@[simp] lemma compileSignedAllocationsAux_succ
    {k : ℕ} (src dst : LayoutState k) (n : ℕ) (hn : n + 1 ≤ k) :
    compileSignedAllocationsAux src dst (n + 1) hn
      =
    let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
    let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
    compileSignedAllocationsAux src dst n hk' ;;
    allocChunkGate i (src.xslot i) (dst.xslot i) ;;
    allocChunkGate i (src.zslot i) (dst.zslot i) := rfl

@[simp] lemma compileSignedDeallocationsAux_zero {k : ℕ} (src dst : LayoutState k) (h : 0 ≤ k) :
    compileSignedDeallocationsAux src dst 0 h = Gate.id := rfl

@[simp] lemma compileSignedDeallocationsAux_succ
    {k : ℕ} (src dst : LayoutState k) (n : ℕ) (hn : n + 1 ≤ k) :
    compileSignedDeallocationsAux src dst (n + 1) hn
      =
    let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
    let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
    deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
    deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
    compileSignedDeallocationsAux src dst n hk' := rfl

end Shor

/-! ---------------------------------------------------------
    Phase-Product Compiler: Compilation (moved from `Statement.lean`)
--------------------------------------------------------- -/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Compilation from `valid_ops` to `Gate`
========================================================= -/

/-- The control qubit is outside every child register touched by a phase-product layout. -/
def Gate.PhaseProductLayout.ControlDisjoint {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (ctrl : ℕ) : Prop :=
  (∀ i, ctrl ∉ (layout.xSplit.child i).ownedQubits) ∧ (∀ i, ctrl ∉ (layout.zSplit.child i).ownedQubits)

end Shor

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Annotated operations and phase-product counting
========================================================= -/

/-- Number of recursive phase-product leaves in a source program. -/
def phaseProductCount {k : ℕ} : List (valid_ops k) → ℕ
  | [] => 0
  | op :: ops =>
      match op with
      | .phaseProduct _ => phaseProductCount ops + 1
      | _               => phaseProductCount ops

end Shor
