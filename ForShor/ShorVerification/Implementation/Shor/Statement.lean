import ForShor.ShorVerification.Framework.Gatecount.ResourceModel
import ForShor.ShorVerification.Framework.Quantum.Measurement
import ForShor.ShorVerification.Framework.Semantics.LowGateSemantics
import ForShor.ShorVerification.Framework.ToomCookTable
import ForShor.ShorVerification.Implementation.ModularExponentiation.Circuit.CmpLtNW
import ForShor.ShorVerification.Implementation.ModularExponentiation.Circuit.ModExp
import ForShor.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import ForShor.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import ForShor.ShorVerification.Implementation.ModularExponentiation.Lowering.ConstArithmetic
import ForShor.ShorVerification.Implementation.ModularExponentiation.Spec.Config
import ForShor.ShorVerification.Implementation.ModularExponentiation.Spec.Precision
import ForShor.ShorVerification.Implementation.ModularExponentiation.Spec.Validity
import ForShor.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import ForShor.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import ForShor.ShorVerification.Implementation.PhaseProduct.Lowering.Lower
import ForShor.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness
import ForShor.ShorVerification.Implementation.QFT.Statement
import ForShor.ShorVerification.Implementation.Compiler.Statement
import ForShor.ShorVerification.Implementation.Shared.Registers
import ForShor.ShorVerification.Implementation.Shared.States
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions

/-!
# Shor: the lowered circuit and its correctness statement

Everything needed to state the propositions proved in `Main.lean`, and nothing
else. It imports nothing from `Shor/`.
-/

namespace Shor

/-! =========================================================
    Problem instance
========================================================= -/

/-- One order-finding problem: a base `a` coprime to the modulus `N`. -/
structure ShorOrderFindingInstance where
  /-- The base whose order is being found. -/
  a : ℕ
  /-- The modulus. -/
  N : ℕ
  /-- The base lies in the valid range. -/
  range : 0 < a ∧ a < N
  /-- The base is coprime to the modulus. -/
  coprime : Nat.gcd a N = 1

/-! =========================================================
    The order and continued-fraction post-processing
========================================================= -/

/-- The multiplicative order of `a` modulo `N`. -/
noncomputable def ord (a N : ℕ) (hgcd : Nat.gcd a N = 1) : ℕ :=
  orderOf (ZMod.unitOfCoprime a ((Nat.coprime_iff_gcd_eq_one).2 hgcd))

/-- The candidate orders for an outcome `o`: the denominators of the first `T Q`
continued-fraction convergents of `o / Q` that are positive and pass `verify`. -/
noncomputable def orderCandidates (T : ℕ → ℕ) (verify : ℕ → Bool) (o Q : ℕ) : Finset ℕ :=
  ((Finset.range (T Q)).image fun t => (Real.convergent ((o : ℝ) / (Q : ℝ)) t).den).filter
    fun d => 0 < d ∧ verify d = true

/-- Classical post-processing of an outcome `o`: the least candidate, or `0` if there is none. -/
noncomputable def OF_post (T : ℕ → ℕ) (verify : ℕ → Bool) (o Q : ℕ) : ℕ :=
  if h : (orderCandidates T verify o Q).Nonempty then (orderCandidates T verify o Q).min' h else 0

/-- `T Q` convergents are enough: for every `o < Q`, the continued fraction of `o / Q`
terminates before step `T Q`. -/
def ContinuedFractionSearchComplete (T : ℕ → ℕ) : Prop :=
  ∀ Q o : ℕ, o < Q → ∃ n < T Q, (GenContFract.of ((o : ℝ) / (Q : ℝ))).TerminatedAt n

/-- `1` if post-processing the outcome `o` returns `r`, else `0`. -/
noncomputable def r_found (T : ℕ → ℕ) (verify : ℕ → Bool) (o Q r : ℕ) : ℝ :=
  if OF_post (T := T) verify o Q = r then (1 : ℝ) else 0

/-! =========================================================
    Workspace budget
========================================================= -/

/-- Spare qubits needed on each register family by the lowered circuit. -/
structure ShorWorkspaceNeed where
  /-- On the exponent register, for the QFT. -/
  exponent : ℕ
  /-- On the modular data register. -/
  data : ℕ
  /-- On the work register. -/
  auxiliary : ℕ
  /-- On the comparator scratch register. -/
  scratch : ℕ

/-- Spare qubits needed to lower a QFT of width `n`. -/
def qftReserveNeedOf (need : ℕ → ℕ × ℕ) (n : ℕ) : ℕ :=
  (need n).1 + (need n).2

/-- Spare qubits needed by the lowered order-finding circuit, given the QFT
need `need` and the phase-product need `res`. -/
def shorWorkspaceNeedOf (need : ℕ → ℕ × ℕ) (res : ℕ → ℕ → ℕ × ℕ)
    (x data work scratch : ExtReg) : ShorWorkspaceNeed :=
  let step1Need := res (data.width + 1) (work.width + 1)
  let step2Need := res (work.width + 1) (data.width + 2)
  let step5Need := res (data.width + 2) (work.width + 1)
  let step4Need := res (work.width + 1) (scratch.width + 1)
  { exponent := qftReserveNeedOf need x.width
    data :=
      max (2 + step1Need.1)
        (max (1 + qftReserveNeedOf need (data.width + 1))
          (max (2 + step2Need.2) (2 + step5Need.1)))
    auxiliary :=
      max (qftReserveNeedOf need work.width)
        (max (1 + step1Need.2)
          (max (1 + step2Need.1) (max (1 + step4Need.1) (1 + step5Need.2))))
    scratch := max (qftReserveNeedOf need scratch.width) (1 + step4Need.2) }

/-- `shorWorkspaceNeedOf` under the policy `P`. -/
abbrev Policy.shorWorkspaceNeed (P : ShorLoweringPolicy) (x data work scratch : ExtReg) :
    ShorWorkspaceNeed :=
  shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (Policy.reserveNeed P) x data work scratch

/-- Each register has at least the spare qubits `needs` asks of it. -/
structure ShorWorkspaceLargeEnoughOf (needs : ShorWorkspaceNeed) (x data work scratch : ExtReg) :
    Prop where
  exponent_large_enough : needs.exponent ≤ x.capacity
  data_large_enough : needs.data ≤ data.capacity
  auxiliary_large_enough : needs.auxiliary ≤ work.capacity
  scratch_large_enough : needs.scratch ≤ scratch.capacity

/-- `ShorWorkspaceLargeEnoughOf` under the policy `P`. -/
abbrev Policy.ShorWorkspaceLargeEnough (P : ShorLoweringPolicy) (x data work scratch : ExtReg) :
    Prop :=
  ShorWorkspaceLargeEnoughOf (Policy.shorWorkspaceNeed P x data work scratch) x data work scratch

/-- The exponent register's qubits are not reused by the work register, the
comparator scratch, or the flag. -/
structure ShorWorkspaceIsolation (x work scratch : ExtReg) (flag : ℕ) : Prop where
  exponent_work_disjoint : ExtReg.OwnedDisjoint x work
  exponent_scratch_disjoint : ExtReg.OwnedDisjoint x scratch
  flag_outside_exponent : flag ∉ x.ownedQubits

/-! =========================================================
    Hypotheses
========================================================= -/

section
open Operations
universe u

/-- Register layout, precision and clean-input assumptions of the approximate
circuit. The rest of the layout and the remaining clean-input facts follow from
the workspace budget, the comparator layout and `ShorWorkspaceIsolation`. -/
structure ShorApproxSetupMinimal (qs : QSemantics) [RegEncoding qs.Basis] (η : ℝ) (N : ℕ)
    (x data work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis) : Type where
  /-- The comparator's register layout. -/
  step4_workspace : CmpLtNWWorkspace N (data.grow 1) work scratch flag
  exponent_data_disjoint : ExtReg.OwnedDisjoint x data
  /-- The work register is wide enough for precision `η`. -/
  algorithm1_precision : Algorithm1Precision η data.active work.active
  exponent_zero : RegEncoding.toNat x.active b0 = 0
  data_zero : RegEncoding.toNat data.active b0 = 0
  work_zero : RegEncoding.toNat work.active b0 = 0
  scratch_zero : RegEncoding.toNat scratch.active b0 = 0
  flag_zero : RegEncoding.toNat (qubitReg flag) b0 = 0

/-- Every spare qubit the lowering may use starts at zero. -/
def ShorWorkspaceCleanInput {Basis : Type u} [RegEncoding Basis] (x y work scratch : ExtReg)
    (b0 : Basis) : Prop :=
  FreshZero x.reserve b0 ∧ FreshZero y.reserve b0 ∧
  FreshZero work.reserve b0 ∧ FreshZero scratch.reserve b0

/-- The hypotheses of the lowered-circuit claims: the approximate setup, the
workspace budget, and clean spare qubits. -/
structure LoweredShorReady (qs : QSemantics) [RegEncoding qs.Basis] (P : ShorLoweringPolicy)
    (η : ℝ) (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis) : Type where
  approx : ShorApproxSetupMinimal qs η N x y work scratch flag b0
  workspace_large_enough : Policy.ShorWorkspaceLargeEnough P x y work scratch
  workspace_isolated : ShorWorkspaceIsolation x work scratch flag
  workspace_initially_zero : ShorWorkspaceCleanInput x y work scratch b0

end

/-! =========================================================
    Success probability
========================================================= -/

section
open Classical

/-- The probability that measuring the exponent register and post-processing
with continued fractions returns the order `r`. -/
noncomputable def probability_of_success {qs : QSemantics} [RegEncoding qs.Basis]
    [MeasureClass qs] {Circuit : Type} (evalC : Circuit → qs.State → qs.State) (T : ℕ → ℕ)
    (verify : ℕ → Bool) (x : Reg) (r Q : ℕ) (C : Circuit) (ψ : qs.State) : ℝ :=
  ∑ o : Fin Q, (r_found (T := T) verify o.1 Q r) *
    MeasureClass.probMeas (qs := qs) x o.1 (evalC C ψ)

end

noncomputable def κ : ℝ := 1 / (Real.pi ^ 2)

/-- The per-step precision at which the lowering loss is at most half of the
ideal success bound `κ / log(log₂ N + 1)`: the solution of
`2 · regSize x · √(2 · 1600 · η) ≤ κ / (2 · log(log₂ N + 1))`, with
`51200 = 32 · 1600`. -/
noncomputable def shorPrecision (N : ℕ) (x : Reg) : ℝ :=
  κ ^ 2 / (51200 * (regSize x : ℝ) ^ 2 * (Real.log ((Nat.log2 N : ℝ) + 1)) ^ 2)

/-! =========================================================
    The order-finding circuit
========================================================= -/

section
open Operations

/-- Initialize the data register to the computational basis value `1`. -/
def initY1 (y : Reg) : Gate :=
  match y.qubits with
  | [] => Gate.id
  | q :: _ => Gate.X q

/-- Order finding with the approximate modular exponentiation of
`ModularExponentiation/`. -/
def orderFindingApprox (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) : Gate :=
  (H_reg x.active) ;;
  (initY1 y.active) ;;
  (modExpApproxValid a N x.active y work scratch flag hworkspace hstep4) ;;
  (IQFT x)

variable {qs : QSemantics} [RegEncoding qs.Basis] {P : ShorLoweringPolicy} {η : ℝ} {a N : ℕ}
  {x y work scratch : ExtReg} {flag : ℕ} {b0 : qs.Basis}

/-- The workspace the modular multiplications need, from the budget and the
comparator layout. -/
theorem LoweredShorReady.modMulWorkspace
    (h : LoweredShorReady qs P η a N x y work scratch flag b0) : ModMulCircuitWorkspaceOK y work := by
  have hd := h.workspace_large_enough.data_large_enough
  have hw := h.workspace_large_enough.auxiliary_large_enough
  simp only [Policy.shorWorkspaceNeed, shorWorkspaceNeedOf] at hd hw
  refine ⟨by unfold ExtReg.CanGrow; omega, by unfold ExtReg.CanGrow; omega, ?_⟩
  simpa [ExtReg.OwnedDisjoint, ExtReg.ownedQubits_grow] using
    h.approx.step4_workspace.data_work_disjoint

/-- The approximate order-finding circuit on a readiness package's registers. -/
def LoweredShorReady.circuit (h : LoweredShorReady qs P η a N x y work scratch flag b0) : Gate :=
  orderFindingApprox a N x y work scratch flag h.modMulWorkspace h.approx.step4_workspace

end

/-! =========================================================
    Correctness
========================================================= -/

section
variable {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]

/-- The lowered approximate circuit at any precision `η`, with loss
`2 · regSize x · √(2Kη)` for some constant `K ≤ 1600`. -/
def ShorCorrectApproxLoweredUniform [GateSemanticsFacts qs] [LowerGateClass qs] (T : ℕ → ℕ)
    (_hT : ContinuedFractionSearchComplete T) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ K ≤ 1600 ∧
    ∀ (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (_hP : P.Admissible)
      (x y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
      (_hm : regSize x.active = Nat.log2 (2 * inst.N^2))
      (_hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
      (hready : LoweredShorReady qs P η inst.a inst.N x y work scratch flag b0)
      (hws : Policy.GateWorkspaceOK P hready.circuit),
      probability_of_success (qs := qs) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active) (r := ord inst.a inst.N inst.coprime) (Q := ASize x.active)
        (evalC := LowerGateClass.evalL (qs := qs)) (C := Policy.lowerGate P hready.circuit hws)
        (ψ := qs.ket b0)
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * (regSize x.active : ℝ) * Real.sqrt (2 * (K * η))

/-- The lowered approximate circuit at any precision `η ≤ shorPrecision N x`
keeps at least half of the ideal success bound. -/
def ShorCorrectApproxLowered [GateSemanticsFacts qs] [LowerGateClass qs] (T : ℕ → ℕ)
    (_hT : ContinuedFractionSearchComplete T) : Prop :=
  ∀ (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (_hP : P.Admissible)
    (x y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
    (_hm : regSize x.active = Nat.log2 (2 * inst.N^2))
    (_hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (_hη : η ≤ shorPrecision inst.N x.active)
    (hready : LoweredShorReady qs P η inst.a inst.N x y work scratch flag b0)
    (hws : Policy.GateWorkspaceOK P hready.circuit),
    probability_of_success (qs := qs) (T := T)
      (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
      (x := x.active) (r := ord inst.a inst.N inst.coprime) (Q := ASize x.active)
      (evalC := LowerGateClass.evalL (qs := qs)) (C := Policy.lowerGate P hready.circuit hws)
      (ψ := qs.ket b0)
    ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))

end
end Shor
