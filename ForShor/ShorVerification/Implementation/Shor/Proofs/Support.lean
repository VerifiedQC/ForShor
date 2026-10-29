import ForShor.ShorVerification.Implementation.Shor.Statement
import ForShor.ShorVerification.Implementation.Compiler.Main

/-!
# Shor proofs: supporting definitions and bridges

The clean-state invariants the readiness proofs carry through the circuit, the
bridges between the single-table and policy forms of the workspace budget, the
lowered order-finding circuit `orderFindingApproxLow`, the single-table
workspace spellings, and the full approximate setup `ShorApproxSetup`. Other
folders reach these through `Main.lean`.
-/

namespace Shor

/-! =========================================================
    Clean-state invariants
========================================================= -/

section

universe u

/-! =========================================================
    Static Clean Workspace Inputs
========================================================= -/

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
theorem rec' {motive : (ψ : qs.State) → ThreeRegsCleanState qs r₁ r₂ r₃ ψ → Prop}
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
theorem rec' {motive : (ψ : qs.State) → FullShorWorkspaceCleanState qs x data work ψ → Prop}
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
theorem rec' {motive : (ψ : qs.State) → ShorLoweringCleanState qs x data work ψ → Prop}
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

end

/-! =========================================================
    The lowered order-finding circuit and workspace spellings
========================================================= -/

section

/-- The lowered approximate order-finding circuit. -/
def orderFindingApproxLow (P : ShorLoweringPolicy) (a N : ℕ) (x y work scratch : ExtReg)
    (flag : ℕ) (hmodWorkspace : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hLowerWorkspace : Policy.GateWorkspaceOK P
      (orderFindingApprox a N x y work scratch flag hmodWorkspace hstep4)) :=
  Policy.lowerGate P (orderFindingApprox a N x y work scratch flag hmodWorkspace hstep4)
    hLowerWorkspace

/-- Spare qubits needed to lower a QFT of width `n`, for a single table. -/
abbrev qftReserveNeed {k : ℕ} (ops : Prog k) (n : ℕ) : ℕ :=
  qftReserveNeedOf (qftWorkspaceNeed ops) n

/-- Spare qubits needed to lower a QFT of width `n`, under a policy. -/
abbrev Policy.qftReserveNeed (P : ShorLoweringPolicy) (n : ℕ) : ℕ :=
  qftReserveNeedOf (Policy.qftWorkspaceNeed P) n

/-- `shorWorkspaceNeedOf` for a single table. -/
abbrev shorWorkspaceNeed {k : ℕ} (ops : Prog k) (x data work scratch : ExtReg) :
    ShorWorkspaceNeed :=
  shorWorkspaceNeedOf (qftWorkspaceNeed ops) (RecursivePhaseWorkspace.reserveNeed ops)
    x data work scratch

/-- `ShorWorkspaceLargeEnoughOf` for a single table. -/
abbrev ShorWorkspaceLargeEnough {k : ℕ} (ops : Prog k) (x data work scratch : ExtReg) : Prop :=
  ShorWorkspaceLargeEnoughOf (shorWorkspaceNeed ops x data work scratch) x data work scratch

end

/-! =========================================================
    The approximate setup
========================================================= -/

section
open Operations

/-- The input basis state is clean on every register used by Shor. -/
def ShorCleanInput (qs : QSemantics) [RegEncoding qs.Basis] (x y work scratch : ExtReg)
    (flag : ℕ) (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧
  RegEncoding.toNat y.active b0 = 0 ∧
  y.FreshFor 2 b0 ∧
  RegEncoding.toNat work.active b0 = 0 ∧
  work.FreshFor 1 b0 ∧
  RegEncoding.toNat scratch.active b0 = 0 ∧
  scratch.FreshFor 1 b0 ∧
  RegEncoding.toNat (qubitReg flag) b0 = 0

/-- Public assumptions for the approximate implementation of Shor. -/
structure ShorApproxSetup
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (η : ℝ)
    (N : ℕ)
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) : Type where
  /-- The exponent, data, work, carry, and flag qubits do not overlap. -/
  register_layout :
    ModExpLayout x.active y work flag

  /-- The modular-exponentiation subcircuit has enough local workspace. -/
  circuit_workspace :
    ModMulCircuitWorkspaceOK y work

  /-- The concrete Step-4 comparator and its Step-3 scratch are well laid out. -/
  step4_workspace :
    CmpLtNWWorkspace N (y.grow 1) work scratch flag

  /-- The exponent register is owned separately from the modular data register. -/
  exponent_data_disjoint :
    ExtReg.OwnedDisjoint x y

  /-- The exponent register is owned separately from comparator scratch. -/
  exponent_scratch_disjoint :
    ExtReg.OwnedDisjoint x scratch

  /-- The work register has enough extra bits for precision `η`. -/
  work_precision :
    Algorithm1Precision η y.active work.active

  /-- Shor begins in `|0⋯0⟩` on all registers it uses. -/
  clean_input :
    ShorCleanInput qs x y work scratch flag b0

end

/-! =========================================================
    Workspace budget bridges
========================================================= -/

section

/-- Bridge. -/
@[simp] theorem Policy.qftReserveNeed_const (T : ToomCookTable) (n : ℕ) :
    Policy.qftReserveNeed (ShorLoweringPolicy.constPolicy T) n
      = _root_.Shor.qftReserveNeed T.ops n := by
  unfold Policy.qftReserveNeed _root_.Shor.qftReserveNeed
  rw [Policy.qftWorkspaceNeed_const]

/-- Bridge. -/
theorem Policy.shorWorkspaceNeed_const (T : ToomCookTable) (x data work scratch : ExtReg) :
    Policy.shorWorkspaceNeed (ShorLoweringPolicy.constPolicy T) x data work scratch
      = _root_.Shor.shorWorkspaceNeed T.ops x data work scratch := by
  unfold Policy.shorWorkspaceNeed _root_.Shor.shorWorkspaceNeed
  rw [Policy.qftWorkspaceNeed_const,
    show Policy.reserveNeed (ShorLoweringPolicy.constPolicy T)
        = RecursivePhaseWorkspace.reserveNeed T.ops from
      funext fun wx => funext fun wz => Policy.reserveNeed_const T wx wz]

/-- Bridge: at the constant policy the two coincide. -/
theorem Policy.shorWorkspaceLargeEnough_const_iff {T : ToomCookTable}
    {x data work scratch : ExtReg} :
    Policy.ShorWorkspaceLargeEnough (ShorLoweringPolicy.constPolicy T) x data work scratch
      ↔ _root_.Shor.ShorWorkspaceLargeEnough T.ops x data work scratch := by
  unfold Policy.ShorWorkspaceLargeEnough _root_.Shor.ShorWorkspaceLargeEnough
  rw [Policy.shorWorkspaceNeed_const]

end

/-! =========================================================
    The factoring instance
========================================================= -/

/-- A modulus to factor: odd, greater than two, and not a prime power. -/
structure ShorFactoringInstance where
  /-- The modulus to factor. -/
  N : ℕ
  /-- The modulus is odd. -/
  odd : Odd N
  /-- The modulus is nontrivial. -/
  gt_two : N > 2
  /-- The modulus is not a prime power. -/
  not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k

/-! =========================================================
    The ideal order-finding circuit
========================================================= -/

section
open Operations

/-- Order finding with exact modular exponentiation. -/
noncomputable def orderFindingIdeal (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs]
    (a N : ℕ) (x y : ExtReg) : Gate :=
  (H_reg x.active) ;; (initY1 y.active) ;; (modExpIdeal' qs a N x.active y.active) ;; (IQFT x)

/-- Input to the ideal circuit: both registers start at zero and own disjoint
qubits. -/
def IdealOrderFindingInput (qs : QSemantics) [RegEncoding qs.Basis] (x y : ExtReg)
    (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧
  RegEncoding.toNat y.active b0 = 0 ∧
  ExtReg.OwnedDisjoint x y

end

end Shor
