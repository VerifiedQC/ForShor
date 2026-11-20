import ForShor.ShorVerification.Implementation.Readout.Proofs.GhostFreeMass

/-!
# Readout: the hypotheses of the success theorems WITHOUT an exponent register

`SemiclassicalGhostFreeSetup qs η N c y work scratch flag b0` is
`SemiclassicalShorSetup` with the reference exponent register `x` removed: no
`x`, no `Disjoint x y`, no "`x = 0` in `b0`". Its fields are only about the
registers the circuit uses: the control `c` (outside the data, work and scratch
registers, reserves included, and not the flag), the multiplier workspaces, the
precision `η` of the work register, and a start ket `b0` that is zero on the data,
work and scratch registers, their spare qubits, the flag and `c`
(`SemiclassicalCleanInput`).

`SemiclassicalGhostFreeSetup.of_ghost` drops `x` from a ghost setup (so every
place the ghost theorems apply, these do).

Also here, the per-step lemmas of `Proofs/ShorSetup.lean` restated for the
ghost-free setup (the start ket, the multiplier configuration and its bound),
and `shorPrecisionRounds N m`, the precision `shorPrecision N x` written with
the NUMBER of rounds `m` in place of the register `x`
(`shorPrecision_eq_rounds`: equal when `regSize x = m`).
-/

namespace Shor

/-- The clean start ket without an exponent register: `b0` is zero on the data
register `y`, its two spare qubits, the work register and its spare qubit, the
scratch register and its spare qubit, and the flag (`ShorCleanInput` minus `x`). -/
def SemiclassicalCleanInput (qs : QSemantics) [RegEncoding qs.Basis] (y work scratch : ExtReg)
    (flag : ℕ) (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat y.active b0 = 0 ∧ y.FreshFor 2 b0 ∧
  RegEncoding.toNat work.active b0 = 0 ∧ work.FreshFor 1 b0 ∧
  RegEncoding.toNat scratch.active b0 = 0 ∧ scratch.FreshFor 1 b0 ∧
  RegEncoding.toNat (qubitReg flag) b0 = 0

/-- **Hypotheses of the ghost-free semiclassical success theorems.** On the
registers the circuit uses (data `y`, `work`, `scratch`, the flag qubit, the
control qubit `c`) and nothing else.

Fields: the control `c` lies outside `y`, `work`, `scratch` (reserves included)
and is not the flag (`layout`); the modular-multiplier workspaces (exactly those
of `ShorApproxSetup`); the precision `η` of the work register; the start ket
`b0` is zero on `y`, `work`, `scratch`, their spare qubits and the flag
(`clean_input`), and on `c` (`control_zero`). There is NO exponent register. -/
structure SemiclassicalGhostFreeSetup (qs : QSemantics) [RegEncoding qs.Basis] (η : ℝ)
    (N c : ℕ) (y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis) : Type where
  layout : SemiclassicalLayout c y work scratch flag
  circuit_workspace : ModMulCircuitWorkspaceOK y work
  step4_workspace : CmpLtNWWorkspace N (y.grow 1) work scratch flag
  work_precision : Algorithm1Precision η y.active work.active
  clean_input : SemiclassicalCleanInput qs y work scratch flag b0
  control_zero : RegEncoding.bit c b0 = false

/-- A ghost setup gives a ghost-free one (drop `x`). -/
def SemiclassicalGhostFreeSetup.of_ghost {qs : QSemantics} [RegEncoding qs.Basis] {η : ℝ}
    {N c : ℕ} {x y work scratch : ExtReg} {flag : ℕ} {b0 : qs.Basis}
    (h : SemiclassicalShorSetup qs η N c x y work scratch flag b0) :
    SemiclassicalGhostFreeSetup qs η N c y work scratch flag b0 where
  layout := h.layout
  circuit_workspace := h.circuit_workspace
  step4_workspace := h.step4_workspace
  work_precision := h.work_precision
  clean_input := h.clean_input.2
  control_zero := h.control_zero

/-- `shorPrecision` with the number of rounds `m` in place of the exponent
register: `κ² / (51200 · m² · log²(log₂ N + 1))`. -/
noncomputable def shorPrecisionRounds (N m : ℕ) : ℝ :=
  κ ^ 2 / (51200 * (m : ℝ) ^ 2 * (Real.log ((Nat.log2 N : ℝ) + 1)) ^ 2)

/-- `shorPrecision N x` depends on `x` only through `regSize x`. -/
theorem shorPrecision_eq_rounds (N : ℕ) (x : Reg) :
    shorPrecision N x = shorPrecisionRounds N (regSize x) := rfl

theorem regSize_interval (lo s : ℕ) : regSize (Reg.interval lo s) = s := by
  simp [regSize, Reg.width, Reg.interval]

namespace Readout

section Start
variable {qs : QSemantics.{0}} [RegEncoding qs.Basis]

/-- **The start ket, ghost-free.** Under a `SemiclassicalGhostFreeSetup` with
`1 < N ≤ 2^|y|`, `b1 = semiclassicalStartKet y b0` has data `= 1`, control
`c = 0`, satisfies the side condition `P`, and `|b1⟩` is a unit vector in
`InRangeOn c y.active N P`. -/
theorem semiclassical_start_ghostfree {η : ℝ} {N c : ℕ} {y work scratch : ExtReg} {flag : ℕ}
    {b0 : qs.Basis} (h : SemiclassicalGhostFreeSetup qs η N c y work scratch flag b0)
    (hN : 1 < N) (hNy : N ≤ ASize y.active) :
    RegEncoding.toNat y.active (semiclassicalStartKet y b0) = 1 ∧
    RegEncoding.bit c (semiclassicalStartKet y b0) = false ∧
    semiclassicalSide y work scratch flag (semiclassicalStartKet y b0) ∧
    InRangeOn c y.active N (semiclassicalSide y work scratch flag)
      (qs.ket (semiclassicalStartKet y b0)) ∧
    ‖qs.ket (semiclassicalStartKet (qs := qs) y b0)‖ = 1 := by
  obtain ⟨_, hyF, hw0, hwF, hs0, hsF, hf0⟩ := h.clean_input
  have hy1 : RegEncoding.toNat y.active (semiclassicalStartKet y b0) = 1 :=
    RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le hN hNy)
  have hc1 : RegEncoding.bit c (semiclassicalStartKet y b0) = false := by
    rw [semiclassicalStartKet, RegEncoding.bit_writeNat_out _ _ _ _
      (fun hc => h.layout.c_not_mem_data (mem_owned_of_mem_active y c hc)), h.control_zero]
  have hP0 : semiclassicalSide y work scratch flag b0 := ⟨hyF, hw0, hwF, hf0, hs0, hsF⟩
  have hP1 : semiclassicalSide y work scratch flag (semiclassicalStartKet y b0) :=
    semiclassicalSide_writeNat_data h.circuit_workspace h.step4_workspace b0 1 hP0
  refine ⟨hy1, hc1, hP1, ?_, ket_norm_one qs _⟩
  exact Submodule.subset_span ⟨_, ⟨hc1, by rw [hy1]; exact hN, hP1⟩, rfl⟩

end Start

section Multiplier
variable {qs : QSemantics.{0}} [RegEncoding qs.Basis]

/-- The per-step configuration `semiclassicalModMulConfig`, from the ghost-free setup. -/
def semiclassicalModMulConfigGhostFree {η : ℝ} {N c : ℕ} {y work scratch : ExtReg} {flag : ℕ}
    {b0 : qs.Basis} (h : SemiclassicalGhostFreeSetup qs η N c y work scratch flag b0)
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

/-- `semiclassicalMultiplier_dist_le` for the ghost-free setup. -/
theorem semiclassicalMultiplier_dist_le_ghostfree [GateSemanticsFacts qs] (K : ℝ)
    (hmodMul : ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
      ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η)
    {η : ℝ} {a N c : ℕ} {y work scratch : ExtReg} {flag : ℕ} {b0 : qs.Basis}
    (h : SemiclassicalGhostFreeSetup qs η N c y work scratch flag b0)
    (hN : 1 < N) (hNy : N ≤ ASize y.active) (ha : Nat.Coprime a N) (m j : ℕ) :
    ∀ φ ∈ ValidSpan y.active N (semiclassicalSide y work scratch flag),
      ‖qs.eval (semiclassicalMultipliers a N c m y work scratch flag h.circuit_workspace
            h.step4_workspace j) φ
          - qs.eval (Gate.idealCtrlModMul ((a ^ (2 ^ (m - 1 - j))) % N) N y.active c) φ‖
        ≤ stepErr K η * ‖φ‖ := by
  refine gate_dist_le_of_unit _ _ _ _ fun φ hφ h1 => ?_
  exact hmodMul η (semiclassicalModMulConfigGhostFree h hN hNy _ (coprime_pow_mod a N ha _)) φ
    ⟨validSpan_le_validAlgorithm1State N y work scratch flag hφ, h1⟩

end Multiplier

end Readout
end Shor
