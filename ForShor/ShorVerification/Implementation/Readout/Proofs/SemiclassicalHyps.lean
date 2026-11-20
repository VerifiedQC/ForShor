import ForShor.ShorVerification.Implementation.Readout.Lowering

/-!
# Readout: the semiclassical lowering hypotheses from the coherent ones

* `rounds_workspaceOK`: the semiclassical rounds have the lowering workspace when every
  multiplier has.
* `semiclassical_hyps_of_coherent`: on the registers of the coherent circuit, with the
  control `c` its first exponent qubit, the coherent lowering hypotheses give the
  semiclassical ones (`MGate.WorkspaceOK` for every number of rounds, `SemiclassicalLayout`).

Moved unchanged from `Readout/LoweringTests.lean` so that non-test code (the
`forshor_emit readout` entry point, `Emit/Lower/Readout.lean`) can use them without
importing a test module.
-/

namespace Shor
namespace Readout

open QubitCount

/-- The semiclassical rounds have the lowering workspace when every multiplier has. -/
theorem rounds_workspaceOK (P : ShorLoweringPolicy) (U : ℕ → Gate) (c : ℕ)
    (hU : ∀ j, Policy.GateWorkspaceOK P (U j)) :
    ∀ m, MGate.WorkspaceOK P (readoutRounds U c m) := by
  intro m
  induction m with
  | zero => exact trivial
  | succ k ih => exact ⟨ih, trivial, hU k, trivial, trivial, trivial⟩

/-- **The coherent circuit's hypotheses give the semiclassical ones** with the control
its first exponent qubit `c`: the lowering workspace for every number of rounds, and
the layout. -/
theorem semiclassical_hyps_of_coherent {P : ShorLoweringPolicy} {a N : ℕ}
    {x y work scratch : ExtReg} {flag : ℕ} {hw : ModMulCircuitWorkspaceOK y work}
    {hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag} {c : ℕ} {rest : List ℕ}
    (hc : x.active.qubits = c :: rest)
    (hws : Policy.GateWorkspaceOK P (orderFindingApprox a N x y work scratch flag hw hs4))
    (hlay : OrderFindingSpaceLayout x y work scratch flag) :
    (∀ m, MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)) ∧
      SemiclassicalLayout c y work scratch flag := by
  have hcx : c ∈ x.ownedQubits := List.mem_append_left _ (by rw [hc]; exact List.mem_cons_self)
  have hcore : Policy.GateWorkspaceOK P
      (CmodMulInPlaceCore ((a ^ (2 ^ 0)) % N) N c y work scratch flag hw hs4) := by
    have h3 := hws.2.2.1
    unfold modExpApproxValid at h3
    rw [hc] at h3
    exact h3.1
  refine ⟨fun m => ⟨hws.2.1, rounds_workspaceOK P
    (semiclassicalMultipliers a N c m y work scratch flag hw hs4) c (fun _ => hcore) m⟩, ?_⟩
  exact
    { c_not_mem_data := fun h => hlay.exponent_data_disjoint hcx h
      c_not_mem_work := fun h => hlay.exponent_work_disjoint hcx h
      c_not_mem_scratch := fun h => hlay.exponent_scratch_disjoint hcx h
      c_ne_flag := fun h => hlay.flag_outside_exponent (h ▸ hcx) }

end Readout
end Shor
