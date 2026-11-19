import ForShor.ShorVerification.Submission.CorrectSemiclassical
import ForShor.Emit.Lower.Readout

/-!
# The `readout` emitter prints the certified semiclassical program

`forshor_emit readout <k> <a> <N> <level> <rounds>` (`Emit/Lower/Readout.lean`) prints
`Readout.EmitRef.referenceSemiclassicalLow (standardPolicy k hk) ⟨a, N, …⟩ level rounds` as a
`forshor.mlowgate/v1` document. `Submission/CorrectSemiclassical.lean` certifies
`(Readout.referenceSemiclassicalProgramAt P hP submissionPrecision inst).circuit`. This file
proves they are the same `MLowGate` when the two CLI inputs are pinned:

* `level = submissionPrecision` (the CLI takes the level as a free input; any other level is a
  different circuit, certified only by `referenceSemiclassicalProgramAt_success` at that level);
* `rounds = referenceXWidth inst = log₂(2N²)` (the CLI takes the number of rounds as a free
  input and reports `full_rounds = referenceXWidth inst` in its metadata; any other value is a
  different circuit that no theorem here certifies);
* the control: the emitter computes it as `qubits.headD 0` of the reference exponent register,
  the certificate as `get ⟨0, _⟩`; they agree because that register is non-empty
  (`emitRef_referenceControl_eq`). The control is not a CLI input.

The policy is not a CLI input either: the emitter only builds the one-band standard policy
`standardPolicy k hk`, which is the policy of the submission
`ShorPolicySubmission.ofSetup (standardLoweringSetup k hk)`. Other submissions' policies are
not reachable from the `readout` subcommand; for them the equation
`emitRef_referenceSemiclassicalLow_eq` (any policy, any level) still identifies the Lean term
`EmitRef.referenceSemiclassicalLow` with the certified circuit, but no CLI prints it.

Also here: the lowered program performs exactly `rounds` measurements
(`referenceSemiclassicalProgramAt_measureCount`): the lowering adds no `measureReset`, so the
feed-forward phase of round `j` reads the record of the same `j` earlier outcomes as in the
high-level program.

Not claimed: anything about the JSON serialisation (`emitMLowGateDoc`) itself, or about the
coherent IR printed by the other subcommands.
-/

namespace Shor

open Reference Readout

/-! ## Number of measurements -/

/-- The number of `measureReset` steps of a lowered measured program (the length of the record
it appends), the `MLowGate` counterpart of `MGate.numMeas`. -/
def MLowGate.measureCount : MLowGate → ℕ
  | .unitary _ => 0
  | .seq a b => a.measureCount + b.measureCount
  | .measureReset _ => 1
  | .ffPhase _ _ => 0

namespace Readout

/-- Lowering by any gate lowering keeps the number of measurements. -/
theorem measureCount_lowerMWith (P : ShorLoweringPolicy)
    (f : (u : Gate) → Policy.GateWorkspaceOK P u → LowGate) :
    ∀ (g : MGate) (h : MGate.WorkspaceOK P g),
      (Policy.lowerMWith P f g h).measureCount = g.numMeas := by
  intro g
  induction g with
  | unitary u => intro _; rfl
  | seq a b iha ihb =>
      intro h
      simp only [Policy.lowerMWith, MLowGate.measureCount, MGate.numMeas, iha h.1, ihb h.2]
  | measureReset q => intro _; rfl
  | ffPhase q j => intro _; rfl

/-- The semiclassical circuit with `m` rounds performs `m` measurements. -/
theorem numMeas_orderFindingSemiclassical (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    (orderFindingSemiclassical a N c m y work scratch flag hw hs4).numMeas = m := by
  have hr : ∀ (U : ℕ → Gate) (k : ℕ), (readoutRounds U c k).numMeas = k := by
    intro U k
    induction k with
    | zero => rfl
    | succ k ih => simp [readoutRounds, MGate.numMeas, ih]
  simp [orderFindingSemiclassical, MGate.numMeas, hr]

/-- **The certified semiclassical program performs exactly `rounds` measurements.** -/
theorem referenceSemiclassicalProgramAt_measureCount (P : ShorLoweringPolicy)
    (hP : P.Admissible) (m : ℕ) (inst : ShorOrderFindingInstance) :
    (referenceSemiclassicalProgramAt P hP m inst).circuit.measureCount
      = (referenceSemiclassicalProgramAt P hP m inst).rounds := by
  simp only [referenceSemiclassicalProgramAt, orderFindingSemiclassicalLow, Policy.lowerM]
  rw [measureCount_lowerMWith, numMeas_orderFindingSemiclassical]

/-- The guarded-balanced program performs exactly `rounds` measurements. -/
theorem balancedSemiclassicalProgramAt_measureCount (P : ShorLoweringPolicy)
    (R : Balanced.Rule) (m : ℕ) (inst : ShorOrderFindingInstance) :
    (balancedSemiclassicalProgramAt P R m inst).circuit.measureCount
      = (balancedSemiclassicalProgramAt P R m inst).rounds := by
  simp only [balancedSemiclassicalProgramAt, orderFindingSemiclassicalLowBalanced,
    Policy.lowerMBalanced]
  rw [measureCount_lowerMWith, numMeas_orderFindingSemiclassical]

/-- The every-site-split program performs exactly `rounds` measurements. -/
theorem balancedUSemiclassicalProgramAt_measureCount (P : ShorLoweringPolicy)
    (R : Balanced.Rule) (hfits : Balanced.ReferenceFits P R) (m : ℕ)
    (inst : ShorOrderFindingInstance) :
    (balancedUSemiclassicalProgramAt P R hfits m inst).circuit.measureCount
      = (balancedUSemiclassicalProgramAt P R hfits m inst).rounds := by
  simp only [balancedUSemiclassicalProgramAt, orderFindingSemiclassicalLowBalancedU]
  rw [lowerMBalancedU_eq, Policy.lowerMBalanced, measureCount_lowerMWith,
    numMeas_orderFindingSemiclassical]

/-! ## The emitter's term is the certified circuit -/

/-- The emitter's control (`headD 0` of the reference exponent register) is the certificate's
(`get ⟨0, _⟩`): the register is non-empty. -/
theorem emitRef_referenceControl_eq (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : EmitRef.referenceControl P inst ℓ = referenceControl P inst ℓ := by
  unfold EmitRef.referenceControl
  rw [referenceX_qubits_eq]
  rfl

/-- The lowered semiclassical circuit depends on the control and the number of rounds only
through their values (the workspace proofs are irrelevant). -/
theorem orderFindingSemiclassicalLow_congr (P : ShorLoweringPolicy) (a N : ℕ) {c c' m m' : ℕ}
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hws' : MGate.WorkspaceOK P (orderFindingSemiclassical a N c' m' y work scratch flag hw hs4))
    (hc : c = c') (hm : m = m') :
    orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws
      = orderFindingSemiclassicalLow P a N c' m' y work scratch flag hw hs4 hws' := by
  subst hc hm
  rfl

/-- **The emitter's Lean term is the certified circuit**, for every policy and level, at
`rounds = referenceXWidth inst`: `EmitRef.referenceSemiclassicalLow P inst ℓ (referenceXWidth inst)`
equals `(referenceSemiclassicalProgramAt P hP ℓ inst).circuit`. -/
theorem emitRef_referenceSemiclassicalLow_eq (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    EmitRef.referenceSemiclassicalLow P inst ℓ (referenceXWidth inst)
      = (referenceSemiclassicalProgramAt P hP ℓ inst).circuit :=
  orderFindingSemiclassicalLow_congr P inst.a inst.N _ _ _ _ _ _ _
    (referenceSemiclassicalWorkspaceOK P inst ℓ _)
    (emitRef_referenceControl_eq P inst ℓ)
    (allocateReferenceLayout_x_width P inst ℓ).symm

end Readout

/-- **What `forshor_emit readout k a N submissionPrecision (referenceXWidth inst)` prints is
the certified semiclassical program.** For every arity `k > 1` and instance `inst = (a, N)`,
the circuit `runReadout` serialises with `level = submissionPrecision` and
`rounds = referenceXWidth inst = log₂(2N²)` — namely
`EmitRef.referenceSemiclassicalLow (standardPolicy k hk) inst submissionPrecision (referenceXWidth inst)`
— is the circuit that `policy_submission_correct_semiclassical` certifies for the submission
`ShorPolicySubmission.ofSetup (standardLoweringSetup k hk)`, and it performs exactly
`referenceXWidth inst` measurements. Not claimed: other `level` / `rounds` CLI inputs, other
policies (the CLI builds only `standardPolicy`), or the JSON serialisation. -/
theorem emit_readout_is_certified (k : ℕ) (hk : 1 < k) (inst : ShorOrderFindingInstance) :
    EmitRef.referenceSemiclassicalLow (standardPolicy k hk) inst submissionPrecision
        (referenceXWidth inst)
      = (referenceSemiclassicalProgramAt
          (ShorPolicySubmission.ofSetup (standardLoweringSetup k hk)).policy
          (ShorPolicySubmission.ofSetup (standardLoweringSetup k hk)).policy_admissible
          submissionPrecision inst).circuit ∧
    (referenceSemiclassicalProgramAt
        (ShorPolicySubmission.ofSetup (standardLoweringSetup k hk)).policy
        (ShorPolicySubmission.ofSetup (standardLoweringSetup k hk)).policy_admissible
        submissionPrecision inst).rounds = referenceXWidth inst ∧
    (referenceSemiclassicalProgramAt
        (ShorPolicySubmission.ofSetup (standardLoweringSetup k hk)).policy
        (ShorPolicySubmission.ofSetup (standardLoweringSetup k hk)).policy_admissible
        submissionPrecision inst).circuit.measureCount = referenceXWidth inst :=
  ⟨emitRef_referenceSemiclassicalLow_eq _ _ inst submissionPrecision,
   allocateReferenceLayout_x_width _ inst submissionPrecision,
   (referenceSemiclassicalProgramAt_measureCount _ _ _ inst).trans
     (allocateReferenceLayout_x_width _ inst submissionPrecision)⟩

end Shor

/-! ## Checks -/

-- The CLI's policy is the standard submission's policy, definitionally.
example (k : ℕ) (hk : 1 < k) :
    (Shor.ShorPolicySubmission.ofSetup (Shor.standardLoweringSetup k hk)).policy
      = Shor.standardPolicy k hk := rfl

#print axioms Shor.emit_readout_is_certified
#print axioms Shor.Readout.emitRef_referenceSemiclassicalLow_eq
#print axioms Shor.Readout.referenceSemiclassicalProgramAt_measureCount
#print axioms Shor.Readout.balancedSemiclassicalProgramAt_measureCount
#print axioms Shor.Readout.balancedUSemiclassicalProgramAt_measureCount
