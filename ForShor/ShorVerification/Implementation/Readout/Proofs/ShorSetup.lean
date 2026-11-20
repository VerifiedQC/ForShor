import ForShor.ShorVerification.Implementation.Readout.ShorStatement
import ForShor.ShorVerification.Implementation.Readout.Main
import ForShor.ShorVerification.Implementation.Readout.Proofs.Approx
import ForShor.ShorVerification.Implementation.Shor.Proofs.Correctness

/-!
# Readout: discharging the approximate-gate hypotheses for the real circuit

`semiclassical_dist_le_sum_errors` (`Proofs/Approx.lean`) has four kinds of
hypothesis. For `orderFindingSemiclassical` under a `SemiclassicalShorSetup`
they are discharged here:

* the side condition `P` is `semiclassicalSide y work scratch flag`: the data
  register's two spare qubits, the work register and its spare qubit, the flag,
  the scratch register and its spare qubit are all `0`. With it,
  `ValidSpan y.active N P` lies inside `ValidAlgorithm1State N y work scratch flag`,
  the span on which the existing per-step bound `modMul_approx_valid_dist_uniform`
  holds (`validSpan_le_validAlgorithm1State`); `P` is unchanged by writing the
  control `c` (`semiclassicalSide_writeNat_ctrl`, from the layout) or the data
  register (`semiclassicalSide_writeNat_data`, from the workspaces);
* the multiplier hypothesis `hU` (`semiclassicalMultiplier_dist_le`): the
  per-step lemma applies with `ctrl := c` through the configuration
  `semiclassicalModMulConfig` (the lemma is stated for an arbitrary control
  qubit satisfying `ModMulCoreLayout`, which the layout gives), and
  `gate_dist_le_of_unit` turns its unit-vector form into `ε · ‖φ‖`;
* the start state (`semiclassical_start`): the data = 1 ket of `semiclassical_branch_state` is
  `b1 = writeNat y.active 1 b0`, and `qs.eval (initY1 y.active) (qs.ket b0) = qs.ket b1`
  (`eval_initY1_start`; `y = 0` in `b0`). `qs.ket b1` is a unit vector in
  `InRangeOn c y.active N P` (control `0`, data `1 < N`, `P`), and `b1` has
  `x = 0`, `y = 1`, `c = 0` (the hypotheses of `semiclassical_eq_iqft`);
* the circuit (`orderFindingSemiclassical_eval`): the `MGate` run from `|b0⟩`
  is `semiclassicalImpl` with the real multipliers and the exact phases, from
  `|b1⟩`; and the textbook ideal circuit `orderFindingIdeal` from `|b0⟩` is the
  coherent circuit of `semiclassical_eq_iqft` from `|b1⟩`
  (`orderFindingIdeal_eval_start`).

`ShorApproxSetup.toSemiclassicalShorSetup` builds a `SemiclassicalShorSetup`
from the existing coherent setup, with the first exponent qubit as the control.
-/

namespace Shor
namespace Readout

open MeasureClass

section Side

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis]

/-- The side condition `P` for the real multiplier: the data register's two
spare qubits, the work register and its spare qubit, the flag, the scratch
register and its spare qubit are all `0` (the non-data part of
`GoodAlgorithm1BasisInput`). -/
def semiclassicalSide (y work scratch : ExtReg) (flag : ℕ) (b : qs.Basis) : Prop :=
  y.FreshFor 2 b ∧ RegEncoding.toNat work.active b = 0 ∧ work.FreshFor 1 b ∧
    RegEncoding.toNat (qubitReg flag) b = 0 ∧ RegEncoding.toNat scratch.active b = 0 ∧
    scratch.FreshFor 1 b

/-- With `P = semiclassicalSide`, `ValidSpan` is inside `ValidAlgorithm1State`
(the span of `GoodAlgorithm1BasisInput` kets). -/
theorem validSpan_le_validAlgorithm1State (N : ℕ) (y work scratch : ExtReg) (flag : ℕ) :
    ValidSpan (qs := qs) y.active N (semiclassicalSide y work scratch flag)
      ≤ ValidAlgorithm1State qs N y work scratch flag := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, ⟨h1, h2, h3, h4, h5, h6, h7⟩, rfl⟩
  exact Submodule.subset_span ⟨b, ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩, rfl⟩

/-- A spare qubit is an owned qubit. -/
theorem mem_owned_of_mem_newBits (e : ExtReg) (n q : ℕ) (h : q ∈ (e.newBits n).qubits) :
    q ∈ e.ownedQubits :=
  List.mem_append_right _ (List.mem_of_mem_take h)

/-- An active qubit is an owned qubit. -/
theorem mem_owned_of_mem_active (e : ExtReg) (q : ℕ) (h : q ∈ e.active.qubits) :
    q ∈ e.ownedQubits :=
  List.mem_append_left _ h

/-- Writing a register `W` does not change the value of a register `R` that
shares no qubit with it. -/
theorem toNat_writeNat_of_not_mem (R W : Reg) (h : ∀ q ∈ R.qubits, q ∉ W.qubits) (v : ℕ)
    (b : qs.Basis) : RegEncoding.toNat R (RegEncoding.writeNat W v b) = RegEncoding.toNat R b :=
  toNat_left_write_right R W (List.disjoint_left.2 fun _ hq hw => h _ hq hw) b v

/-- `P` is unchanged by writing the control `c` (outside every register `P`
reads). -/
theorem semiclassicalSide_writeNat_ctrl {c : ℕ} {y work scratch : ExtReg} {flag : ℕ}
    (hl : SemiclassicalLayout c y work scratch flag) (b : qs.Basis) (v : ℕ)
    (h : semiclassicalSide y work scratch flag b) :
    semiclassicalSide y work scratch flag (RegEncoding.writeNat (qubitReg c) v b) := by
  have key : ∀ R : Reg, (∀ q ∈ R.qubits, q ≠ c) →
      RegEncoding.toNat R (RegEncoding.writeNat (qubitReg c) v b) = RegEncoding.toNat R b :=
    fun R hR => toNat_writeNat_of_not_mem R _ (fun q hq hc =>
      hR q hq ((mem_qubitReg c q).1 hc)) v b
  have ne_of : ∀ e : ExtReg, c ∉ e.ownedQubits → ∀ q ∈ e.ownedQubits, q ≠ c :=
    fun e he q hq hqc => he (hqc ▸ hq)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold ExtReg.FreshFor FreshZero at h1 h3 h6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ExtReg.FreshFor FreshZero
    rw [key _ fun q hq => ne_of y hl.c_not_mem_data q (mem_owned_of_mem_newBits y 2 q hq), h1]
  · rw [key _ fun q hq => ne_of work hl.c_not_mem_work q (mem_owned_of_mem_active work q hq), h2]
  · unfold ExtReg.FreshFor FreshZero
    rw [key _ fun q hq => ne_of work hl.c_not_mem_work q (mem_owned_of_mem_newBits work 1 q hq), h3]
  · rw [key _ fun q hq => by rw [(mem_qubitReg flag q).1 hq]; exact fun e => hl.c_ne_flag e.symm, h4]
  · rw [key _ fun q hq =>
      ne_of scratch hl.c_not_mem_scratch q (mem_owned_of_mem_active scratch q hq), h5]
  · unfold ExtReg.FreshFor FreshZero
    rw [key _ fun q hq =>
      ne_of scratch hl.c_not_mem_scratch q (mem_owned_of_mem_newBits scratch 1 q hq), h6]

/-- `P` is unchanged by writing the data register `y.active` (the registers `P`
reads are disjoint from it by the multiplier's workspaces). -/
theorem semiclassicalSide_writeNat_data {N : ℕ} {y work scratch : ExtReg} {flag : ℕ}
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b : qs.Basis) (v : ℕ)
    (h : semiclassicalSide y work scratch flag b) :
    semiclassicalSide y work scratch flag (RegEncoding.writeNat y.active v b) := by
  have hyw : ExtReg.OwnedDisjoint y work := hw.2.2
  have hys : ExtReg.OwnedDisjoint y scratch := by
    simpa [ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow] using hs4.data_scratch_disjoint
  have hfy : flag ∉ y.ownedQubits := by
    simpa [Gate.ExtReg.ownedQubits_grow] using hs4.flag_not_data
  have key : ∀ R : Reg, (∀ q ∈ R.qubits, q ∉ y.ownedQubits) →
      RegEncoding.toNat R (RegEncoding.writeNat y.active v b) = RegEncoding.toNat R b :=
    fun R hR => toNat_writeNat_of_not_mem R _ (fun q hq hy =>
      hR q hq (mem_owned_of_mem_active y q hy)) v b
  have off : ∀ e : ExtReg, ExtReg.OwnedDisjoint y e → ∀ q ∈ e.ownedQubits, q ∉ y.ownedQubits :=
    fun e he q hq hy => he hy hq
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold ExtReg.FreshFor FreshZero at h3 h6
  refine ⟨ExtReg.freshFor_write_active y 2 v b h1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [key _ fun q hq => off work hyw q (mem_owned_of_mem_active work q hq), h2]
  · unfold ExtReg.FreshFor FreshZero
    rw [key _ fun q hq => off work hyw q (mem_owned_of_mem_newBits work 1 q hq), h3]
  · rw [key _ fun q hq => by rw [(mem_qubitReg flag q).1 hq]; exact hfy, h4]
  · rw [key _ fun q hq => off scratch hys q (mem_owned_of_mem_active scratch q hq), h5]
  · unfold ExtReg.FreshFor FreshZero
    rw [key _ fun q hq => off scratch hys q (mem_owned_of_mem_newBits scratch 1 q hq), h6]

end Side

/-! ## The start state -/

section Start

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis]

/-- `y` has at least one qubit when `regSize y = log₂(2N)` and `N ≥ 2`. -/
theorem regSize_pos_of_log2 (N : ℕ) (hN : 2 ≤ N) (y : Reg) (hn : regSize y = Nat.log2 (2 * N)) :
    0 < regSize y := by
  rw [hn, Nat.log2_eq_log_two]
  exact Nat.log_pos Nat.one_lt_two (by omega)

/-- The data = 1 start ket of the semiclassical readout: `b0` with the data
register written to `1`. -/
def semiclassicalStartKet (y : ExtReg) (b0 : qs.Basis) : qs.Basis :=
  RegEncoding.writeNat y.active 1 b0

variable [GateSemanticsFacts qs]

/-- `initY1` turns the data = 0 ket `b0` into the data = 1 ket
`semiclassicalStartKet y b0` (an `X` on the lowest data qubit). -/
theorem eval_initY1_start (y : ExtReg) (b0 : qs.Basis) (hy : 0 < regSize y.active)
    (hy0 : RegEncoding.toNat y.active b0 = 0) :
    qs.eval (initY1 y.active) (qs.ket b0) = qs.ket (semiclassicalStartKet y b0) := by
  rw [initY1_eq_X_lowQubit y.active hy]
  exact PauliXSemantics.eval_X_low_zero_reg_ket (qs := qs) y.active b0 hy hy0

omit [GateSemanticsFacts qs] in
/-- **The start ket.** Under a `SemiclassicalShorSetup` with `1 < N ≤ 2^|y|`,
the ket `b1 = semiclassicalStartKet y b0` has exponent register `x = 0`, data
`= 1`, control `c = 0`, satisfies the side condition `P`, and `|b1⟩` is a unit
vector in `InRangeOn c y.active N P`. -/
theorem semiclassical_start {η : ℝ} {N c : ℕ} {x y work scratch : ExtReg} {flag : ℕ}
    {b0 : qs.Basis} (h : SemiclassicalShorSetup qs η N c x y work scratch flag b0)
    (hN : 1 < N) (hNy : N ≤ ASize y.active) :
    RegEncoding.toNat x.active (semiclassicalStartKet y b0) = 0 ∧
    RegEncoding.toNat y.active (semiclassicalStartKet y b0) = 1 ∧
    RegEncoding.bit c (semiclassicalStartKet y b0) = false ∧
    semiclassicalSide y work scratch flag (semiclassicalStartKet y b0) ∧
    InRangeOn c y.active N (semiclassicalSide y work scratch flag)
      (qs.ket (semiclassicalStartKet y b0)) ∧
    ‖qs.ket (semiclassicalStartKet (qs := qs) y b0)‖ = 1 := by
  obtain ⟨hx0, hy0, hyF, hw0, hwF, hs0, hsF, hf0⟩ := h.clean_input
  have hxy : Disjoint x.active y.active := ExtReg.activeDisjoint_of_ownedDisjoint h.reference_data_disjoint
  have hx1 : RegEncoding.toNat x.active (semiclassicalStartKet y b0) = 0 := by
    rw [semiclassicalStartKet, toNat_left_write_right x.active y.active hxy, hx0]
  have hy1 : RegEncoding.toNat y.active (semiclassicalStartKet y b0) = 1 :=
    RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le hN hNy)
  have hc1 : RegEncoding.bit c (semiclassicalStartKet y b0) = false := by
    rw [semiclassicalStartKet, RegEncoding.bit_writeNat_out _ _ _ _
      (fun hc => h.layout.c_not_mem_data (mem_owned_of_mem_active y c hc)), h.control_zero]
  have hP0 : semiclassicalSide y work scratch flag b0 := ⟨hyF, hw0, hwF, hf0, hs0, hsF⟩
  have hP1 : semiclassicalSide y work scratch flag (semiclassicalStartKet y b0) :=
    semiclassicalSide_writeNat_data h.circuit_workspace h.step4_workspace b0 1 hP0
  refine ⟨hx1, hy1, hc1, hP1, ?_, ket_norm_one qs _⟩
  exact Submodule.subset_span ⟨_, ⟨hc1, by rw [hy1]; exact hN, hP1⟩, rfl⟩

end Start

/-! ## The multiplier hypothesis -/

section Multiplier

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis]

/-- The configuration of the existing per-step bound for one round of the
semiclassical circuit: multiplier `cm` (coprime to `N`), control `ctrl := c`,
the setup's registers and workspaces. The layout `ModMulCoreLayout y work flag c`
comes from `SemiclassicalLayout` and the workspaces. -/
def semiclassicalModMulConfig {η : ℝ} {N c : ℕ} {x y work scratch : ExtReg} {flag : ℕ}
    {b0 : qs.Basis} (h : SemiclassicalShorSetup qs η N c x y work scratch flag b0)
    (hN : 1 < N) (hNy : N ≤ ASize y.active) (cm : ℕ) (hcm : Nat.Coprime cm N) :
    ModMulConfig η where
  env :=
    { N := N
      data := y
      work := work
      scratch := scratch
      modulus_gt_one := hN
      data_capacity := hNy
      precision := h.work_precision
      circuit_workspace := h.circuit_workspace }
  c := cm
  flag := flag
  ctrl := c
  coprime := hcm
  layout := ⟨h.circuit_workspace.2.2,
    by simpa [Gate.ExtReg.ownedQubits_grow] using h.step4_workspace.flag_not_data,
    h.step4_workspace.flag_not_work, h.layout.c_not_mem_data, h.layout.c_not_mem_work,
    h.layout.c_ne_flag⟩
  step4_workspace := h.step4_workspace

/-- **`hU` for the real multiplier.** If every `CmodMulInPlaceCore` is
`stepErr K η`-close to the ideal controlled multiplier on unit vectors of
`ValidAlgorithm1State` (the form of `modMul_approx_valid_dist_uniform`), then in
every round `j` the semiclassical circuit's multiplier is
`stepErr K η · ‖φ‖`-close to the ideal one on `ValidSpan y.active N P`. -/
theorem semiclassicalMultiplier_dist_le [GateSemanticsFacts qs] (K : ℝ)
    (hmodMul : ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
      ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η)
    {η : ℝ} {a N c : ℕ} {x y work scratch : ExtReg} {flag : ℕ} {b0 : qs.Basis}
    (h : SemiclassicalShorSetup qs η N c x y work scratch flag b0)
    (hN : 1 < N) (hNy : N ≤ ASize y.active) (ha : Nat.Coprime a N) (m j : ℕ) :
    ∀ φ ∈ ValidSpan y.active N (semiclassicalSide y work scratch flag),
      ‖qs.eval (semiclassicalMultipliers a N c m y work scratch flag h.circuit_workspace
            h.step4_workspace j) φ
          - qs.eval (Gate.idealCtrlModMul ((a ^ (2 ^ (m - 1 - j))) % N) N y.active c) φ‖
        ≤ stepErr K η * ‖φ‖ := by
  refine gate_dist_le_of_unit _ _ _ _ fun φ hφ h1 => ?_
  exact hmodMul η (semiclassicalModMulConfig h hN hNy _ (coprime_pow_mod a N ha _)) φ
    ⟨validSpan_le_validAlgorithm1State N y work scratch flag hφ, h1⟩

end Multiplier

/-! ## The circuits as runs from the start ket -/

section Circuits

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  [LowerGateClass qs] [MeasureClass qs]

/-- A gate applied branchwise to `MState.init ψ` is `MState.init` of its image. -/
theorem unitary_eval_init (g : Gate) (ψ : qs.State) :
    (MGate.unitary g).eval (MState.init ψ) = MState.init (qs.eval g ψ) := by
  funext r
  simp only [MGate.eval_unitary, MState.init]
  split_ifs
  · rfl
  · exact MGate.gate_eval_zero_state g

/-- **The `MGate` as an implemented readout.** Run from `|b0⟩` (data `0`),
`orderFindingSemiclassical` is `semiclassicalImpl` with the real multipliers
and the exact feed-forward phases, run from `|b1⟩ = initY1 |b0⟩` (data `1`). -/
theorem orderFindingSemiclassical_eval (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 : qs.Basis)
    (hy : 0 < regSize y.active) (hy0 : RegEncoding.toNat y.active b0 = 0) :
    (orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval (MState.init (qs.ket b0))
      = semiclassicalImpl c (semiclassicalMultipliers a N c m y work scratch flag hw hs4)
          (fun j => exactPhase c j) m (MState.init (qs.ket (semiclassicalStartKet y b0))) := by
  rw [orderFindingSemiclassical, MGate.eval_seq, unitary_eval_init,
    eval_initY1_start y b0 hy hy0, semiclassicalImpl_exact]

omit [LowerGateClass qs] [MeasureClass qs] in
/-- **The textbook ideal circuit from `|b0⟩` is the coherent readout of
`semiclassical_eq_iqft` from `|b1⟩`.** `H_reg x ;; initY1 y ;; modExpIdeal' ;; IQFT x`
on `|b0⟩` (`x = 0`, `y = 0`, `x` and `y` disjoint) equals
`H_reg x ;; modExpIdeal' ;; IQFT x` on `|b1⟩ = |b0 with y := 1⟩`. -/
theorem orderFindingIdeal_eval_start (a N : ℕ) (x y : ExtReg) (b0 : qs.Basis)
    (hxy : Disjoint x.active y.active) (hy : 0 < regSize y.active)
    (hx0 : RegEncoding.toNat x.active b0 = 0) (hy0 : RegEncoding.toNat y.active b0 = 0) :
    qs.eval (orderFindingIdeal qs a N x y) (qs.ket b0)
      = qs.eval (H_reg x.active ;; modExpIdeal' qs a N x.active y.active ;; IQFT x)
          (qs.ket (semiclassicalStartKet y b0)) := by
  have hx1 : RegEncoding.toNat x.active (semiclassicalStartKet y b0) = 0 := by
    rw [semiclassicalStartKet, toNat_left_write_right x.active y.active hxy, hx0]
  have hyx : Disjoint y.active x.active := List.disjoint_left.2 fun _ h1 h2 => hxy h2 h1
  have hH : qs.eval (initY1 y.active) (qs.eval (H_reg x.active) (qs.ket b0))
      = qs.eval (H_reg x.active) (qs.ket (semiclassicalStartKet y b0)) := by
    rw [eval_Hreg_zero_uniform_sum x b0 hx0, eval_Hreg_zero_uniform_sum x _ hx1,
      ← gateL_apply (qs := qs), map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [gateL_apply]
    have hyt : RegEncoding.toNat y.active (RegEncoding.writeNat x.active t.1 b0) = 0 := by
      rw [toNat_left_write_right y.active x.active hyx, hy0]
    rw [eval_initY1_start y _ hy hyt, semiclassicalStartKet, semiclassicalStartKet,
      writeNat_comm_of_disjoint y.active x.active hyx]
  simp only [orderFindingIdeal, qs.eval_seq]
  rw [hH]

end Circuits

end Readout

/-! ## From the coherent setup -/

section Bridge

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis]

/-- **The coherent setup gives a semiclassical one.** From a `ShorApproxSetup`
(the hypotheses of the existing approximate theorems) with a nonempty exponent
register, the semiclassical hypotheses hold with the control `c` the first
exponent qubit `x.active[0]` (which the coherent layout already keeps outside
the data, work and scratch registers and the flag, and which is `0` in `b0`).
So the semiclassical theorems apply wherever the coherent ones do. -/
def ShorApproxSetup.toSemiclassicalShorSetup {η : ℝ} {N : ℕ} {x y work scratch : ExtReg}
    {flag : ℕ} {b0 : qs.Basis} (h : ShorApproxSetup qs η N x y work scratch flag b0)
    (hx : 0 < regSize x.active) :
    SemiclassicalShorSetup qs η N (x.active.get ⟨0, hx⟩) x y work scratch flag b0 where
  layout :=
    have hc := h.register_layout ⟨0, hx⟩
    { c_not_mem_data := hc.2.2.2.1
      c_not_mem_work := hc.2.2.2.2.1
      c_not_mem_scratch := fun hs =>
        h.exponent_scratch_disjoint (List.mem_append_left _ (List.get_mem _ _)) hs
      c_ne_flag := hc.2.2.2.2.2 }
  circuit_workspace := h.circuit_workspace
  step4_workspace := h.step4_workspace
  work_precision := h.work_precision
  reference_data_disjoint := h.exponent_data_disjoint
  clean_input := h.clean_input
  control_zero := by
    have hb := RegEncoding.bit_eq_testBit_toNat x.active b0 ⟨0, hx⟩
    rw [h.clean_input.1, Nat.zero_testBit] at hb
    exact hb

end Bridge

end Shor
