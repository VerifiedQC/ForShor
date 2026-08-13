import FastMultiplication.ShorVerification.Implementation.QFT.Lowering

namespace Shor

/-!
# Shor workspace budgets and clean-state predicates

This file is the layer for the workspace directory. It names the static reserve
budgets and the dynamic clean-state invariants used by
`Workspace.ShorReadiness`.

Main declarations:

* `shorWorkspaceNeed` computes the reserve budget for exponent, data, and
  auxiliary registers.
* `ShorWorkspaceLargeEnough` is the public static capacity assumption.
* `ShorLoweringCleanState` is the clean-state invariant preserved by lowered
  Shor stages after the data carry bit is allowed to be live.
* `shorLoweringCleanState_ket` is the entry lemma that turns an initially clean
  basis state into the lowered clean invariant.
-/

/-! =========================================================
    Section 1: Static reserve budgets
========================================================= -/

/-- Workspace required on each register by lowered Shor order finding. -/
structure ShorWorkspaceNeed where
  exponent : ℕ
  data : ℕ
  auxiliary : ℕ

/-- Total reserve required for lowering a QFT of width `n`. -/
def qftReserveNeed
    {k : ℕ}
    (ops : Prog k)
    (n : ℕ) : ℕ :=
  (qftWorkspaceNeed ops n).1 +
  (qftWorkspaceNeed ops n).2

/--
Compute the reserve required from the exponent, data, and auxiliary registers
when lowering the approximate Shor order-finding circuit.
-/
def shorWorkspaceNeed
    {k : ℕ}
    (ops : Prog k)
    (x data work : ExtReg) :
    ShorWorkspaceNeed :=

  let step1Need :=
    RecursivePhaseWorkspace.reserveNeed ops (data.width + 1) (work.width + 1)

  let step2Need :=
    RecursivePhaseWorkspace.reserveNeed ops (work.width + 1) (data.width + 2)

  let step5Need :=
    RecursivePhaseWorkspace.reserveNeed ops (data.width + 2) (work.width + 1)

  {
    exponent := qftReserveNeed ops x.width

    data :=
      (max (2 + step1Need.1)
        (max (1 + qftReserveNeed ops (data.width + 1))
          (max (2 + step2Need.2) (2 + step5Need.1))))

    auxiliary :=
      (max (qftReserveNeed ops work.width)
        (max (1 + step1Need.2) (max (1 + step2Need.1) (1 + step5Need.2))))
  }


/--
The exponent, data, and auxiliary registers contain enough inactive reserve
for lowering the complete approximate Shor order-finding circuit.
-/
structure ShorWorkspaceLargeEnough
    {k : ℕ}
    (ops : Prog k)
    (x data work : ExtReg) :
    Prop where

  exponent_large_enough :
    (shorWorkspaceNeed ops x data work).exponent
      ≤ x.capacity

  data_large_enough :
    (shorWorkspaceNeed ops x data work).data
      ≤ data.capacity

  auxiliary_large_enough :
    (shorWorkspaceNeed ops x data work).auxiliary
      ≤ work.capacity

/-! =========================================================
    Section 2: Public workspace preconditions
========================================================= -/

/--
Every reserve register that may be used during Shor lowering is initially zero.
-/
def ShorWorkspaceCleanInput
    {Basis : Type u}
    [RegEncoding Basis]
    (x y work : ExtReg)
    (b0 : Basis) :
    Prop :=
  FreshZero x.reserve b0 ∧
  FreshZero y.reserve b0 ∧
  FreshZero work.reserve b0

/--
The reserve belonging to the exponent register is not reused by the
auxiliary register or comparator flag.
-/
structure ShorWorkspaceIsolation
    (x work : ExtReg)
    (flag : ℕ) :
    Prop where

  exponent_work_disjoint :
    ExtReg.OwnedDisjoint x work

  flag_outside_exponent :
    flag ∉ x.ownedQubits

/-! =========================================================
    Section 3: Dynamic clean-state invariants

    The main invariant for lowered readiness is `ShorLoweringCleanState`.
    The older full/carry predicates are kept as small bridge names because
    several imported correctness statements still expose them.
========================================================= -/

/--
A state supported on basis states in which three specified registers are zero.
-/
abbrev ThreeRegsCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] (r₁ r₂ r₃ : Reg) :
    qs.State → Prop :=
  CleanClosure (fun b => FreshZero r₁ b ∧ FreshZero r₂ b ∧ FreshZero r₃ b)

namespace ThreeRegsCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {r₁ r₂ r₃ : Reg}
/-- Smart constructors delegating to `CleanClosure`, preserving call sites. -/
theorem zero : ThreeRegsCleanState qs r₁ r₂ r₃ 0 := CleanClosure.zero
theorem ket (b : qs.Basis) (h₁ : FreshZero r₁ b) (h₂ : FreshZero r₂ b)
    (h₃ : FreshZero r₃ b) : ThreeRegsCleanState qs r₁ r₂ r₃ (qs.ket b) :=
  CleanClosure.ket b ⟨h₁, h₂, h₃⟩
theorem add {ψ φ : qs.State} (hψ : ThreeRegsCleanState qs r₁ r₂ r₃ ψ)
    (hφ : ThreeRegsCleanState qs r₁ r₂ r₃ φ) :
    ThreeRegsCleanState qs r₁ r₂ r₃ (ψ + φ) := CleanClosure.add hψ hφ
theorem smul (a : ℂ) {ψ : qs.State} (hψ : ThreeRegsCleanState qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState qs r₁ r₂ r₃ (a • ψ) := CleanClosure.smul a hψ
/-- Custom eliminator preserving the original 3-hypothesis `ket` shape
(`| ket b h₁ h₂ h₃`) despite the generic single-predicate closure. -/
@[induction_eliminator, cases_eliminator]
def rec' {motive : (ψ : qs.State) → ThreeRegsCleanState qs r₁ r₂ r₃ ψ → Prop}
    (zero : motive 0 ThreeRegsCleanState.zero)
    (ket : ∀ (b : qs.Basis) (h₁ : FreshZero r₁ b) (h₂ : FreshZero r₂ b)
        (h₃ : FreshZero r₃ b),
        motive (qs.ket b) (ThreeRegsCleanState.ket b h₁ h₂ h₃))
    (add : ∀ {ψ φ : qs.State} (hψ : ThreeRegsCleanState qs r₁ r₂ r₃ ψ)
        (hφ : ThreeRegsCleanState qs r₁ r₂ r₃ φ),
        motive ψ hψ → motive φ hφ → motive (ψ + φ) (ThreeRegsCleanState.add hψ hφ))
    (smul : ∀ (a : ℂ) {ψ : qs.State} (hψ : ThreeRegsCleanState qs r₁ r₂ r₃ ψ),
        motive ψ hψ → motive (a • ψ) (ThreeRegsCleanState.smul a hψ))
    {ψ : qs.State} (h : ThreeRegsCleanState qs r₁ r₂ r₃ ψ) : motive ψ h := by
  induction h with
  | zero => exact zero
  | ket b hconj => exact ket b hconj.1 hconj.2.1 hconj.2.2
  | add hψ hφ ihψ ihφ => exact add hψ hφ ihψ ihφ
  | smul a hψ ih => exact smul a hψ ih
end ThreeRegsCleanState

/--
The invariant at entry to and exit from each modular-multiplication core.
-/
abbrev FullShorWorkspaceCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x data work : ExtReg) :
    qs.State → Prop :=
  ThreeRegsCleanState
    qs
    x.reserve
    data.reserve
    work.reserve

namespace FullShorWorkspaceCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {x data work : ExtReg}
@[induction_eliminator, cases_eliminator]
def rec' {motive : (ψ : qs.State) → FullShorWorkspaceCleanState qs x data work ψ → Prop}
    (zero : motive 0 ThreeRegsCleanState.zero)
    (ket : ∀ (b : qs.Basis) (h₁ : FreshZero x.reserve b) (h₂ : FreshZero data.reserve b)
        (h₃ : FreshZero work.reserve b),
        motive (qs.ket b) (ThreeRegsCleanState.ket b h₁ h₂ h₃))
    (add : ∀ {ψ φ : qs.State} (hψ : FullShorWorkspaceCleanState qs x data work ψ)
        (hφ : FullShorWorkspaceCleanState qs x data work φ),
        motive ψ hψ → motive φ hφ → motive (ψ + φ) (ThreeRegsCleanState.add hψ hφ))
    (smul : ∀ (a : ℂ) {ψ : qs.State} (hψ : FullShorWorkspaceCleanState qs x data work ψ),
        motive ψ hψ → motive (a • ψ) (ThreeRegsCleanState.smul a hψ))
    {ψ : qs.State} (h : FullShorWorkspaceCleanState qs x data work ψ) : motive ψ h :=
  ThreeRegsCleanState.rec' zero ket add smul h
end FullShorWorkspaceCleanState

/--
The lowering-clean invariant used throughout lowered Shor readiness.

The first bit of `data.reserve` is the algorithmic carry bit, so it is not part
of the lowering workspace that must remain clean between modular-multiplication
stages.
-/
abbrev ShorLoweringCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x data work : ExtReg) :
    qs.State → Prop :=
  ThreeRegsCleanState
    qs
    x.reserve
    (data.reserve.drop 1)
    work.reserve

namespace ShorLoweringCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {x data work : ExtReg}
@[induction_eliminator, cases_eliminator]
def rec' {motive : (ψ : qs.State) → ShorLoweringCleanState qs x data work ψ → Prop}
    (zero : motive 0 ThreeRegsCleanState.zero)
    (ket : ∀ (b : qs.Basis) (h₁ : FreshZero x.reserve b)
        (h₂ : FreshZero (data.reserve.drop 1) b) (h₃ : FreshZero work.reserve b),
        motive (qs.ket b) (ThreeRegsCleanState.ket b h₁ h₂ h₃))
    (add : ∀ {ψ φ : qs.State} (hψ : ShorLoweringCleanState qs x data work ψ)
        (hφ : ShorLoweringCleanState qs x data work φ),
        motive ψ hψ → motive φ hφ → motive (ψ + φ) (ThreeRegsCleanState.add hψ hφ))
    (smul : ∀ (a : ℂ) {ψ : qs.State} (hψ : ShorLoweringCleanState qs x data work ψ),
        motive ψ hψ → motive (a • ψ) (ThreeRegsCleanState.smul a hψ))
    {ψ : qs.State} (h : ShorLoweringCleanState qs x data work ψ) : motive ψ h :=
  ThreeRegsCleanState.rec' zero ket add smul h
end ShorLoweringCleanState

lemma fullShorWorkspaceCleanState_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {x data work : ExtReg}
    {b : qs.Basis}
    (hzero :
      ShorWorkspaceCleanInput x data work b) :
    FullShorWorkspaceCleanState
      qs x data work
      (qs.ket b) := by
  exact
    ThreeRegsCleanState.ket
      b
      hzero.1
      hzero.2.1
      hzero.2.2

lemma fullShorWorkspaceCleanState_to_carry
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {x data work : ExtReg}
    {ψ : qs.State}
    (hclean :
      FullShorWorkspaceCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work ψ := by
  induction hclean with
  | zero =>
      exact ThreeRegsCleanState.zero

  | ket b hx hdata hwork =>
      apply ThreeRegsCleanState.ket b hx
      · apply FreshZero.of_subset
          (data.reserve.drop 1)
          data.reserve
          b
        · intro q hq
          exact List.mem_of_mem_drop hq
        · exact hdata
      · exact hwork

  | add hψ hφ ihψ ihφ =>
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      exact ThreeRegsCleanState.smul a ihψ

/--
Main clean-state entry lemma for this file.

It packages the initial reserve-zero assumption into the invariant used by all
lowered Shor readiness theorems. The first data reserve bit is deliberately
dropped because it is the modular-multiplication carry bit, not compiler
workspace.
-/
lemma shorLoweringCleanState_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {x data work : ExtReg}
    {b : qs.Basis}
    (hzero :
      ShorWorkspaceCleanInput
        x data work b) :
    ShorLoweringCleanState
      qs x data work
      (qs.ket b) := by
  exact
    fullShorWorkspaceCleanState_to_carry
      (fullShorWorkspaceCleanState_ket hzero)

end Shor
