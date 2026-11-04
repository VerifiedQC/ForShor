import ForShor.ShorVerification.Framework.Semantics.GateSemantics
import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.QFT.Statement
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Modular exponentiation: the circuit and its correctness statement

Everything needed to state the propositions proved in `Main.lean`, and nothing
else. It imports nothing from `ModularExponentiation/`.
-/

namespace Shor

/-! =========================================================
    Precision
========================================================= -/

/-- The error scale of one modular multiplication at precision `η`: `√(2Kη)`. -/
noncomputable def stepErr (K η : ℝ) : ℝ :=
  Real.sqrt (2 * (K * η))

/-- The number of extra work-register qubits for precision `η`. -/
noncomputable def algorithm1ExtraBits (η : ℝ) : ℕ :=
  ⌈2 * Real.logb 2 (2 + 1 / (2 * η))⌉₊

/-- `0 < η < 1/2`, and the work register has exactly `algorithm1ExtraBits η` more
qubits than the data register. The width is fixed, not just bounded below,
because the Shor gate count (`Shor/Proofs/GateCount.lean`) needs the upper bound too. -/
def Algorithm1Precision (η : ℝ) (data work : Reg) : Prop :=
  0 < η ∧ η < (1 / 2 : ℝ) ∧ regSize work = regSize data + algorithm1ExtraBits η

/-! =========================================================
    Spare qubits of the phase-product workspaces
========================================================= -/

namespace ExtReg

/-- Room for `n` spare qubits gives room for any `m ≤ n`. -/
theorem CanGrow.mono {e : ExtReg} {m n : ℕ} (h : e.CanGrow n) (hmn : m ≤ n) : e.CanGrow m :=
  le_trans hmn h

/-- After growing by `n`, a register with room for `n + k` spare qubits has room for `k`. -/
theorem canGrow_grow {e : ExtReg} {n k : ℕ} (h : e.CanGrow (n + k)) : (e.grow n).CanGrow k := by
  unfold CanGrow at h ⊢
  simp [capacity, grow, remainingReserve, Reg.drop, regSize, Reg.width] at h ⊢
  omega

theorem OwnedDisjoint.symm {d w : ExtReg} (h : OwnedDisjoint d w) : OwnedDisjoint w d :=
  List.Disjoint.symm h

/-- Growing a register does not change the qubits it owns, so it stays disjoint. -/
theorem OwnedDisjoint.grow_left {d w : ExtReg} (n : ℕ) (h : OwnedDisjoint d w) :
    OwnedDisjoint (d.grow n) w := by
  have hown : (d.grow n).ownedQubits = d.ownedQubits := by
    simp [ownedQubits, grow, Reg.append, newBits, remainingReserve, Reg.take, Reg.drop,
      List.append_assoc]
  unfold OwnedDisjoint
  rw [hown]
  exact h

/-- The active qubits are disjoint from the reserve with its first `n` qubits dropped. -/
theorem active_disjoint_reserve_drop (e : ExtReg) (n : ℕ) :
    Disjoint e.active (e.reserve.drop n) := by
  rw [Disjoint, List.disjoint_left]
  intro q hqActive hqReserve
  have hdisj := e.active_reserve_disjoint
  rw [Disjoint, List.disjoint_left] at hdisj
  exact hdisj hqActive (List.mem_of_mem_drop hqReserve)

/-- Dropping the first `n` reserve qubits leaves room for `k` if there was room for `n + k`. -/
theorem canGrow_dropReserve {e : ExtReg} {n k : ℕ} (h : e.CanGrow (n + k)) :
    (withReserve e.active (e.reserve.drop n) (e.active_disjoint_reserve_drop n)).CanGrow k := by
  unfold CanGrow capacity at *
  change k ≤ regSize (e.reserve.drop n)
  simp [Reg.drop, regSize, Reg.width] at *
  omega

/-- Dropping reserve qubits keeps a register disjoint from another. -/
theorem OwnedDisjoint.dropReserve {e w : ExtReg} (n : ℕ) (h : OwnedDisjoint e w) :
    OwnedDisjoint (withReserve e.active (e.reserve.drop n) (e.active_disjoint_reserve_drop n)) w := by
  unfold OwnedDisjoint
  rw [List.disjoint_left]
  intro q hq hqw
  apply h _ hqw
  rw [ownedQubits, List.mem_append] at hq ⊢
  rcases hq with hqActive | hqReserve
  · exact Or.inl hqActive
  · exact Or.inr (List.mem_of_mem_drop hqReserve)

end ExtReg


/-! =========================================================
    Workspace
========================================================= -/

section
open Gate

/-- The registers of one modular multiplication do not overlap: data and work
are disjoint, and the flag and control qubit are outside both. -/
def ModMulCoreLayout (data work : ExtReg) (flag ctrl : ℕ) : Prop :=
  ExtReg.OwnedDisjoint data work ∧
  flag ∉ data.ownedQubits ∧ flag ∉ work.ownedQubits ∧
  ctrl ∉ data.ownedQubits ∧ ctrl ∉ work.ownedQubits ∧
  ctrl ≠ flag

/-- The spare qubits one modular multiplication needs: two on the data register
(a carry bit, and one for the phase products), one on the work register. -/
def ModMulCircuitWorkspaceOK (data work : ExtReg) : Prop :=
  data.CanGrow 2 ∧ work.CanGrow 1 ∧ ExtReg.OwnedDisjoint data work

/-- The phase-product workspace of Step 1: the data register without its carry
bit, and the work register. -/
def ModMulCircuitWorkspaceOK.step1Workspace {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) : Gate.PhaseProdWorkspace data.active work.active :=
  let dataNoCarry : ExtReg :=
    ExtReg.withReserve data.active (data.reserve.drop 1) (data.active_disjoint_reserve_drop 1)
  Gate.PhaseProdWorkspace.ofExtRegs dataNoCarry work
    (ExtReg.canGrow_dropReserve (n := 1) (k := 1) h.1) h.2.1 (h.2.2.dropReserve 1)

/-- The phase-product workspace of Step 2: the work register, and the data
register with its carry bit. -/
def ModMulCircuitWorkspaceOK.step2Workspace {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) :
    Gate.PhaseProdWorkspace work.active (data.grow 1).active :=
  Gate.PhaseProdWorkspace.ofExtRegs work (data.grow 1)
    h.2.1 (ExtReg.canGrow_grow (n := 1) (k := 1) h.1) (h.2.2.grow_left 1).symm

/-- The phase-product workspace of Step 5: the data register with its carry
bit, and the work register. -/
def ModMulCircuitWorkspaceOK.step5Workspace {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) :
    Gate.PhaseProdWorkspace (data.grow 1).active work.active :=
  Gate.PhaseProdWorkspace.ofExtRegs (data.grow 1) work
    (ExtReg.canGrow_grow (n := 1) (k := 1) h.1) h.2.1 (h.2.2.grow_left 1)

/-- The width of the Step-4 comparator's scratch register. -/
def cmpLtNWWidth (N : ℕ) (data work : Reg) : ℕ :=
  2 + max (regSize data + regSize work) (Nat.log2 (N + 1) + 1 + regSize work)

/-- The registers and spare qubits the Step-4 comparator needs. -/
structure CmpLtNWWorkspace (N : ℕ) (data work scratch : ExtReg) (flag : ℕ) where
  data_can_grow : data.CanGrow 1
  mulWorkspace : Gate.PhaseProdWorkspace work.active scratch.active
  mul_xReserve_eq : mulWorkspace.xReserve = work.reserve
  mul_zReserve_eq : mulWorkspace.zReserve = scratch.reserve
  data_work_disjoint : ExtReg.OwnedDisjoint data work
  data_scratch_disjoint : ExtReg.OwnedDisjoint data scratch
  work_scratch_disjoint : ExtReg.OwnedDisjoint work scratch
  flag_not_data : flag ∉ data.ownedQubits
  flag_not_work : flag ∉ work.ownedQubits
  flag_not_scratch : flag ∉ scratch.ownedQubits
  scratch_width : regSize scratch.active = cmpLtNWWidth N data.active work.active

end

/-! =========================================================
    The Step-4 comparator
========================================================= -/

section
open Gate

/-- The top qubit of the scratch register: the sign of the difference. -/
def cmpLtNWSignQubit (scratch : ExtReg) (h : 0 < regSize scratch.active) : ℕ :=
  scratch.active.get ⟨regSize scratch.active - 1, by simpa [regSize] using Nat.sub_lt h one_pos⟩

/-- Add `N · work` into the scratch register, in Fourier space. -/
def fastConstMulInto (N : ℕ) (work scratch : ExtReg)
    (hworkspace : Gate.PhaseProdWorkspace work.active scratch.active) : Gate :=
  let phi : Angle := (2 * (N : ℚ)) / (ASize hworkspace.zExt.active : ℚ)
  Gate.QFT hworkspace.zExt ;;
  Gate.PhaseProdUsing phi work.active scratch.active hworkspace ;;
  †(Gate.QFT hworkspace.zExt)

/-- Turn the scratch register into `data · 2^|work| − N · work`. -/
def cmpLtNWDifference (data work scratch : ExtReg) (_hdata : data.CanGrow 1) : Gate :=
  Gate.zeroExtend data 1 ;;
  Gate.Negate scratch ;;
  Gate.AddScaled scratch (data.grow 1) false (regSize work.active) ;;
  Gate.zeroDealloc data 1

/-- Flip `flag` iff `data · 2^|work| < N · work`, and restore the scratch register. -/
def cmpLtNW (N : ℕ) (data work scratch : ExtReg) (flag : ℕ)
    (hworkspace : CmpLtNWWorkspace N data work scratch flag) : Gate :=
  let mul := fastConstMulInto N work scratch hworkspace.mulWorkspace
  let diff := cmpLtNWDifference data work scratch hworkspace.data_can_grow
  let sign := cmpLtNWSignQubit scratch
    (hworkspace.scratch_width ▸ Nat.lt_of_lt_of_le two_pos (Nat.le_add_right 2 _))
  mul ;; diff ;; Gate.CNOT sign flag ;; †diff ;; †mul

end

/-! =========================================================
    Algorithm 1
========================================================= -/

section
open Gate

/-- Inverse QFT. -/
def IQFT (r : ExtReg) : Gate :=
  †(Gate.QFT r)

/-- Apply Hadamards across all qubits of a register. -/
def H_reg (r : Reg) : Gate :=
  (regQubits r).foldl (fun acc q => (Gate.H q) ;; acc) Gate.id

/-- Algorithm 1 Step 1: prepare the work Fourier packet and apply the first controlled phase load. -/
def step1
    (c N ctrl : ℕ) (data work : ExtReg) (hworkspace : ModMulCircuitWorkspaceOK data work) : Gate :=
  let phi : Angle := (2 * (((c + N - 1) % N : ℕ) : ℚ)) / (N : ℚ)
  H_reg work.active ;;
  Gate.CPhaseProdUsing ctrl phi data.active work.active hworkspace.step1Workspace ;;
  IQFT hworkspace.step1Workspace.zExt

/-- Algorithm 1 Step 2: use a PhaseProduct to transfer the work-label phase into the data-carry register. -/
def step2 (N : ℕ) (data work : ExtReg) (hworkspace : ModMulCircuitWorkspaceOK data work) : Gate :=
  let dataCarry : ExtReg := data.grow 1
  let phi : Angle := (2 * (N : ℚ)) / (2 : ℚ) ^ (regSize work.active + regSize dataCarry.active)
  Gate.QFT hworkspace.step2Workspace.zExt ;;
  Gate.PhaseProdUsing phi work.active dataCarry.active hworkspace.step2Workspace ;;
  IQFT hworkspace.step2Workspace.zExt

/-- Algorithm 1 Step 3: compare against `N` and conditionally subtract it from the data-carry register. -/
def step3 (N : ℕ) (dataCarry scratch : ExtReg) (flag : ℕ) : Gate :=
  Gate.CmpGeConst N dataCarry scratch flag ;;
  Gate.CSubConst N dataCarry scratch flag

/-- Algorithm 1 Step 4: clear the comparator flag using the data-carry/work relation. -/
def step4 (N : ℕ) (dataCarry work scratch : ExtReg) (flag : ℕ)
    (hworkspace : CmpLtNWWorkspace N dataCarry work scratch flag) :
    Gate :=
  cmpLtNW N dataCarry work scratch flag hworkspace

/-- Algorithm 1 Step 5: adjoint cleanup for the forward fractional load using the inverse constant. -/
def step5
    (k5val N : ℕ) (ctrl : ℕ) (data work : ExtReg) (hworkspace : ModMulCircuitWorkspaceOK data work) :
    Gate :=
  let phi : Angle := (2 * ((k5val % N : ℕ) : ℚ)) / (N : ℚ)
  †((H_reg work.active) ;;
    (Gate.CPhaseProdUsing ctrl phi (data.grow 1).active work.active hworkspace.step5Workspace) ;;
    (IQFT hworkspace.step5Workspace.zExt))

/--
The Step-5 cleanup constant `1 - c⁻¹ mod N`, with the inverse chosen from
the finite modular-inverse existence theorem when it applies.
-/
def step5Constant (c N : ℕ) : ℕ :=
  if h : ∃ cinv : ℕ, cinv < N ∧ (c * cinv) % N = 1 then
    (1 + N - Nat.find h) % N
  else
    0

/-- The five-step controlled in-place modular-multiplication core. -/
def CmodMulInPlaceCore (c N : ℕ) (ctrl : ℕ) (data work scratch : ExtReg) (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) : Gate :=
  let U1 : Gate := step1 c N ctrl data work hworkspace
  let U2 : Gate := step2 N data work hworkspace
  let U3 : Gate := step3 N (data.grow 1) scratch flag
  let U4 : Gate := step4 N (data.grow 1) work scratch flag hstep4
  let U5 : Gate := step5 (step5Constant c N) N ctrl data work hworkspace
  U1 ;; U2 ;; U3 ;; U4 ;; U5

end

/-! =========================================================
    Modular exponentiation
========================================================= -/

section
open Gate

/-- Exact modular exponentiation from the `e`-th exponent bit on: the control
`ctrls[i]` multiplies by `a^(2^(e+i)) mod N`. -/
def modExpIdealSteps (qs : QSemantics) [RegEncoding qs.Basis] (a N : ℕ) (data : Reg) :
    ℕ → List ℕ → Gate
  | _, [] => Gate.id
  | e, ctrl :: ctrls =>
      Gate.idealCtrlModMul ((a ^ (2 ^ e)) % N) N data ctrl ;; modExpIdealSteps qs a N data (e + 1) ctrls

/-- Exact modular exponentiation, controlled by the exponent register `x`. -/
def modExpIdeal' (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs] (a N : ℕ)
    (x data : Reg) : Gate :=
  modExpIdealSteps qs a N data 0 x.qubits

/-- Every exponent qubit, as a control, fits the layout of one modular multiplication. -/
def ModExpLayout (x : Reg) (data work : ExtReg) (flag : ℕ) : Prop :=
  ∀ i : Fin (regSize x), ModMulCoreLayout data work flag (x.get i)

/-- Every multiplier `a^(2^i) mod N` is coprime to `N`. -/
def ModExpArithmeticOK (a N : ℕ) (x : Reg) : Prop :=
  ∀ i : Fin (regSize x), Nat.Coprime ((a ^ (2 ^ i.1)) % N) N

/-- Approximate modular exponentiation from the `e`-th exponent bit on, one
`CmodMulInPlaceCore` per control. -/
def modExpApproxStepsValid (a N : ℕ) (data work scratch : ExtReg) (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) :
    ℕ → List ℕ → Gate
  | _, [] => Gate.id
  | e, ctrl :: ctrls =>
      let c := (a ^ (2 ^ e)) % N
      CmodMulInPlaceCore c N ctrl data work scratch flag hworkspace hstep4 ;;
      modExpApproxStepsValid a N data work scratch flag hworkspace hstep4 (e + 1) ctrls

/-- Approximate modular exponentiation, controlled by the exponent register `x`. -/
def modExpApproxValid (a N : ℕ) (x : Reg) (data work scratch : ExtReg) (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) : Gate :=
  modExpApproxStepsValid a N data work scratch flag hworkspace hstep4 0 x.qubits

end

/-! =========================================================
    Valid inputs
========================================================= -/

/-- A basis input to one modular multiplication: the data register holds a value
below `N`, and its two spare qubits, the work register with its spare qubit, and
the flag are zero. Every other qubit is arbitrary. -/
def GoodModMulBasisInput (qs : QSemantics) [RegEncoding qs.Basis] (N : ℕ) (data work : ExtReg)
    (flag : ℕ) (b : qs.Basis) : Prop :=
  RegEncoding.toNat data.active b < N ∧ data.FreshFor 2 b ∧
  RegEncoding.toNat work.active b = 0 ∧ work.FreshFor 1 b ∧
  RegEncoding.toNat (qubitReg flag) b = 0

/-- `GoodModMulBasisInput`, with the comparator's scratch register and its spare
qubit also zero. -/
def GoodAlgorithm1BasisInput (qs : QSemantics) [RegEncoding qs.Basis] (N : ℕ)
    (data work scratch : ExtReg) (flag : ℕ) (b : qs.Basis) : Prop :=
  GoodModMulBasisInput qs N data work flag b ∧
  RegEncoding.toNat scratch.active b = 0 ∧ scratch.FreshFor 1 b

/-- The valid states: the span of the valid basis inputs. -/
def ValidAlgorithm1State (qs : QSemantics) [RegEncoding qs.Basis] (N : ℕ)
    (data work scratch : ExtReg) (flag : ℕ) : Submodule ℂ qs.State :=
  Submodule.span ℂ
    { ψ | ∃ b : qs.Basis, GoodAlgorithm1BasisInput qs N data work scratch flag b ∧ ψ = qs.ket b }

/-! =========================================================
    Configuration
========================================================= -/

/-- The modulus and registers of one modular multiplication, with its precision
and workspace conditions. -/
structure Algorithm1Env (η : ℝ) where
  N : ℕ
  data : ExtReg
  work : ExtReg
  scratch : ExtReg
  modulus_gt_one : 1 < N
  data_capacity : N ≤ ASize data.active
  precision : Algorithm1Precision η data.active work.active
  circuit_workspace : ModMulCircuitWorkspaceOK data work

/-- One modular exponentiation: an environment, the base `a`, the exponent
register `x`, the comparator flag, and the layout and coprimality conditions. -/
structure ModExpConfig (η : ℝ) where
  env : Algorithm1Env η
  a : ℕ
  x : Reg
  flag : ℕ
  layout : ModExpLayout x env.data env.work flag
  arithmetic : ModExpArithmeticOK a env.N x
  step4_workspace : CmpLtNWWorkspace env.N (env.data.grow 1) env.work env.scratch flag

namespace ModExpConfig

/-- The approximate modular-exponentiation circuit of a configuration. -/
def approxGate {η : ℝ} (cfg : ModExpConfig η) : Gate :=
  modExpApproxValid cfg.a cfg.env.N cfg.x cfg.env.data cfg.env.work cfg.env.scratch cfg.flag
    cfg.env.circuit_workspace cfg.step4_workspace

/-- The exact modular-exponentiation gate of a configuration. -/
def idealGate (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs] {η : ℝ}
    (cfg : ModExpConfig η) : Gate :=
  modExpIdeal' qs cfg.a cfg.env.N cfg.x cfg.env.data.active

/-- A valid state of unit norm. -/
def ValidUnitState (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModExpConfig η)
    (ψ : qs.State) : Prop :=
  ψ ∈ ValidAlgorithm1State qs cfg.env.N cfg.env.data cfg.env.work cfg.env.scratch cfg.flag ∧
    ‖ψ‖ = 1

end ModExpConfig

/-! =========================================================
    Correctness
========================================================= -/

/-- For some constant `K ≤ 1600`, on every valid unit state, the approximate and
exact modular exponentiation differ by at most `regSize x · stepErr K η`. -/
def ModExpApproxValidDistUniform (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] :
    Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ K ≤ 1600 ∧
    ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State), cfg.ValidUnitState qs ψ →
      ‖qs.eval cfg.approxGate ψ - qs.eval (cfg.idealGate qs) ψ‖ ≤ (regSize cfg.x : ℝ) * stepErr K η

/-- `ModExpApproxValidDistUniform` at the constant `K = 1600`. -/
def ModExpApproxValidDist1600 (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] :
    Prop :=
  ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State), cfg.ValidUnitState qs ψ →
    ‖qs.eval cfg.approxGate ψ - qs.eval (cfg.idealGate qs) ψ‖ ≤ (regSize cfg.x : ℝ) * stepErr 1600 η

end Shor
