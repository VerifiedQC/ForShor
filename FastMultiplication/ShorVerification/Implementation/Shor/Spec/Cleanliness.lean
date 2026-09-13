import FastMultiplication.ShorVerification.Implementation.Semantics.CleanClosure
import FastMultiplication.ShorVerification.Implementation.RegisterLemmas

namespace Shor

universe u

/-!
# Shor Clean-State Predicates

The static clean-input predicates and dynamic clean-state invariants used by
Shor's workspace readiness proofs and the final correctness statements.
-/

/-! =========================================================
    Static Clean Workspace Inputs
========================================================= -/

/--
Every reserve register that may be used during Shor lowering is initially zero.
-/
def ShorWorkspaceCleanInput
    {Basis : Type u}
    [RegEncoding Basis]
    (x y work scratch : ExtReg)
    (b0 : Basis) :
    Prop :=
  FreshZero x.reserve b0 ∧
  FreshZero y.reserve b0 ∧
  FreshZero work.reserve b0 ∧
  FreshZero scratch.reserve b0

/-- The input basis state is clean on every register used by Shor. -/
def ShorCleanInput
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧
  RegEncoding.toNat y.active b0 = 0 ∧
  y.FreshFor 2 b0 ∧
  RegEncoding.toNat work.active b0 = 0 ∧
  work.FreshFor 1 b0 ∧
  RegEncoding.toNat scratch.active b0 = 0 ∧
  scratch.FreshFor 1 b0 ∧
  RegEncoding.toNat (qubitReg flag) b0 = 0

/-- Ideal clean input predicate used by correctness proofs: both public
registers start at zero and own disjoint qubits. -/
def IdealOrderFindingInput
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x y : ExtReg)
    (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧
  RegEncoding.toNat y.active b0 = 0 ∧
  ExtReg.OwnedDisjoint x y

/-! =========================================================
    Dynamic Clean-State Invariants
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

/-- The exponent reserve together with all Step-3/4 scratch storage.  Keeping
the ordinary auxiliary reserve as the third clean register lets the existing
phase-product readiness lemmas retain their exact workspace boundary. -/
def exponentScratchCleanReg
    (x scratch : ExtReg)
    (hdisjoint : x.OwnedDisjoint scratch) : Reg :=
  Reg.append x.reserve scratch.ownedReg (by
    rw [Disjoint, List.disjoint_left]
    intro q hqExponent hqScratch
    rw [ExtReg.OwnedDisjoint, List.disjoint_left] at hdisjoint
    apply hdisjoint
    · rw [ExtReg.ownedQubits, List.mem_append]
      exact Or.inr hqExponent
    · simpa only [
        ExtReg.ownedReg,
        Reg.append,
        ExtReg.ownedQubits
      ] using hqScratch)

/-- The compiler-clean invariant strengthened with the complete comparator
scratch register.  It remains a single basis-span predicate, so Step 3 can
soundly combine data-carry freshness with scratch cleanliness. -/
abbrev ShorConcreteCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x data work scratch : ExtReg)
    (hdisjoint : x.OwnedDisjoint scratch) :
    qs.State → Prop :=
  ThreeRegsCleanState
    qs
    (exponentScratchCleanReg x scratch hdisjoint)
    (data.reserve.drop 1)
    work.reserve

end Shor
