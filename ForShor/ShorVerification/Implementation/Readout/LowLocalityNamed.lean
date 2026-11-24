import ForShor.ShorVerification.Implementation.Readout.Proofs.LowFootprintNamed

/-!
# Readout: low-gate locality of the lowered semiclassical circuit, named

With the footprint of the lowered QFT and phase-product blocks bounded by names
(`Proofs/LowFootprintNamed.lean`), the lowered semiclassical circuit names only the qubits of
the semiclassical registers:

* `semiclassical_lowSupport_named`: `(orderFindingSemiclassicalLow …).lowSupport ⊆
  semiclassicalQubits c y work scratch flag` (the control, the owned qubits of `y`, `work`,
  `scratch`, reserves included, and the flag), for EVERY policy and lowering workspace `hws`.
* `not_mem_qftPhaseFoot_of_not_mem_semiclassicalQubits`: the extra hypothesis of the B3 (ii)
  theorems follows from `q ∉ semiclassicalQubits`.
* `orderFindingSemiclassicalLow_recordProb_init_X_named`, `…_decomp_named`,
  `…_superpose_named`, `…_of_agree_named`: the B3 (ii) theorems with the single hypothesis
  `q ∉ semiclassicalQubits …` (or agreement on that set): any policy (no admissibility), any
  registers, any lowering workspace, ANY start state, no clean-workspace hypothesis.

Not covered: qubits in `semiclassicalQubits` (in particular reserve qubits of `y`, `work`,
`scratch`, which the lowering may use, and the control); the flip forms use the low-level
`LowGate.X q`; the agreement form needs finitely many differing qubits.
-/

namespace Shor
namespace Readout

/-- **The lowered semiclassical circuit names only the semiclassical registers.** -/
theorem semiclassical_lowSupport_named (P : ShorLoweringPolicy) (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)) :
    (↑(orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).lowSupport : Set ℕ)
      ⊆ semiclassicalQubits c y work scratch flag := fun _ hp =>
  orderFindingSemiclassical_support a N m hw hs4 (lowerM_lowSupport_named P _ hws hp)

/-- The residual hypothesis of B3 (ii) is implied by `q ∉ semiclassicalQubits`. -/
theorem not_mem_qftPhaseFoot_of_not_mem_semiclassicalQubits {P : ShorLoweringPolicy}
    {a N c m : ℕ} {y work scratch : ExtReg} {flag : ℕ} {hw : ModMulCircuitWorkspaceOK y work}
    {hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag}
    {hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)}
    {q : ℕ} (hq : q ∉ semiclassicalQubits c y work scratch flag) :
    q ∉ MGate.qftPhaseFoot P (orderFindingSemiclassical a N c m y work scratch flag hw hs4) hws :=
  fun h => hq (orderFindingSemiclassical_support a N m hw hs4
    (mgate_qftPhaseFoot_subset P _ hws h))

section Specialise
variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs] [MeasureClass qs]
variable {P : ShorLoweringPolicy} {a N c m : ℕ} {y work scratch : ExtReg} {flag : ℕ}
  {hw : ModMulCircuitWorkspaceOK y work} {hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag}
  {hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)}

/-- **Lowered circuit, flip form, any start state, named.** For ANY policy, registers,
lowering workspace and start state `ψ₀`, and `q ∉ semiclassicalQubits`: applying the
low-level `X q` to the start state changes no record probability of the lowered circuit. -/
theorem orderFindingSemiclassicalLow_recordProb_init_X_named {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (LowerGateClass.evalL (LowGate.X q) ψ₀))) r
      = recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
          (MState.init ψ₀)) r :=
  orderFindingSemiclassicalLow_recordProb_init_X hq
    (not_mem_qftPhaseFoot_of_not_mem_semiclassicalQubits hq) ψ₀ r

/-- **Lowered circuit, decomposition, any start state, named.** -/
theorem orderFindingSemiclassicalLow_recordProb_decomp_named {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch
          flag hw hs4 hws).eval (MState.init (MeasureClass.measProj (qubitReg q) o ψ₀))) r :=
  orderFindingSemiclassicalLow_recordProb_decomp hq
    (not_mem_qftPhaseFoot_of_not_mem_semiclassicalQubits hq) ψ₀ r

/-- **Lowered circuit, superposed spectator, any start ket, named.** -/
theorem orderFindingSemiclassicalLow_recordProb_superpose_named {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (b0 : qs.Basis) (α β : ℂ)
    (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch
          flag hw hs4 hws).eval (MState.init (qs.ket b0))) r :=
  orderFindingSemiclassicalLow_recordProb_superpose_direct hq
    (not_mem_qftPhaseFoot_of_not_mem_semiclassicalQubits hq) b0 α β r

/-- **Lowered circuit, agreement form, any start kets, named.** Two start kets that agree on
`semiclassicalQubits` and differ at finitely many qubits give every record the same
probability. -/
theorem orderFindingSemiclassicalLow_recordProb_of_agree_named (b0 b0' : qs.Basis)
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (hfin : {p | RegEncoding.bit p b0' ≠ RegEncoding.bit p b0}.Finite) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (qs.ket b0'))) r
      = recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
          (MState.init (qs.ket b0))) r :=
  MLowGate.recordProb_of_agree _ b0 b0'
    (fun p hp => hagree p (semiclassical_lowSupport_named P a N c m y work scratch flag hw hs4
      hws hp)) hfin r

end Specialise

end Readout
end Shor
