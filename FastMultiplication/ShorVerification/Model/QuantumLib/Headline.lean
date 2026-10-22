import FastMultiplication.ShorVerification.Model.QuantumLib.Measure
import FastMultiplication.ShorVerification.Model.QuantumLib.Native
import FastMultiplication.ShorVerification.Implementation.Shor.Main
import FastMultiplication.ShorVerification.Submission.Correct

/-!
# The headline theorems in the matrix model

The point of the folder.

Every term below is a QuantumLib matrix or vector: the circuit is a
`CSquare (2 ^ dim)`, the input is the all-zeros `CVector (2 ^ dim)`, and the
success probability is a weighted sum of squared ℓ² norms of projected vectors.
Nothing in `Framework/`, `Implementation/` or `Submission/` is re-proved — each
statement is `rw`-transported from its abstract original through
`Measure.probability_of_success_eq`.

The dimension is left free, subject only to `maxQubit C ≤ dim`. That is strictly
more general than fixing `shorDim` to a closed form read off
`Implementation/Reference/ReferenceLayout.lean`, and it lets a reader plug in
any qubit ceiling they can prove — including `maxQubit C` itself, which is the
`shorDim` corollary at the end.
-/

namespace Shor
namespace Model
namespace QuantumLib

open Reference

/-- The reference program a table submission compiles to, at the fixed
scoring precision. -/
noncomputable def refProg (s : ShorSubmission) (inst : ShorOrderFindingInstance) :
    ShorOrderFindingProgram :=
  referenceProgramAt (ShorLoweringPolicy.constPolicy s.table)
    (ShorLoweringPolicy.constPolicy_admissible s.table_admissible) submissionPrecision inst

/-- The same for a policy submission. -/
noncomputable def refPolicyProg (s : ShorPolicySubmission) (inst : ShorOrderFindingInstance) :
    ShorOrderFindingProgram :=
  referenceProgramAt s.policy s.policy_admissible submissionPrecision inst

/-! ## The certificate, over matrices -/

/-- **`submission_correct`, in QuantumLib's types.** Any table passing C1–C4
yields a circuit matrix `denote dim C : CSquare (2 ^ dim)` which, applied to the
all-zeros column vector and measured on the output register, meets the declared
success bound. -/
theorem ql_submission_correct (s : ShorSubmission) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) (inst : ShorOrderFindingInstance)
    (dim : ℕ) (hdim : maxQubit (refProg s inst).circuit ≤ dim) :
    referenceSuccessProbabilityAt submissionPrecision inst.N
      ≤ qlSuccess dim (refProg s inst).circuit (refProg s inst).output T
          (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (ord inst.a inst.N inst.coprime) (ASize (refProg s inst).output) := by
  simp only [refProg] at hdim ⊢
  have h := submission_correct (qs := qs) s T hT inst
  rwa [probability_of_success_eq _ hdim] at h

/-- **`policy_submission_correct`, in QuantumLib's types.** -/
theorem ql_policy_submission_correct (s : ShorPolicySubmission) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) (inst : ShorOrderFindingInstance)
    (dim : ℕ) (hdim : maxQubit (refPolicyProg s inst).circuit ≤ dim) :
    referenceSuccessProbabilityAt submissionPrecision inst.N
      ≤ qlSuccess dim (refPolicyProg s inst).circuit (refPolicyProg s inst).output T
          (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (ord inst.a inst.N inst.coprime) (ASize (refPolicyProg s inst).output) := by
  simp only [refPolicyProg] at hdim ⊢
  have h := policy_submission_correct (qs := qs) s T hT inst
  rwa [probability_of_success_eq _ hdim] at h

/-! ## The fully lowered approximate circuit, over matrices -/

/-- **`Shor_correct_approx_lowered`, in QuantumLib's types.** The hypotheses are
carried verbatim from the abstract statement; the only addition is that the
input basis state and the circuit live on the `dim` qubits being modelled. -/
theorem ql_Shor_correct_approx_lowered
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    (P : ShorLoweringPolicy) (hP : P.Admissible)
    (x y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N))
    (η : ℝ) (hη : η ≤ shorPrecision inst.N x.active)
    (hready : LoweredShorReady qs P η inst.a inst.N x y work scratch flag b0)
    (dim : ℕ)
    (hdim : maxQubit (orderFindingApproxLow P inst.a inst.N x y work scratch flag
        (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
        (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace
        hready.workspace) ≤ dim)
    (hb0 : Below dim b0) :
    qlSuccessOn dim
        (orderFindingApproxLow P inst.a inst.N x y work scratch flag
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace
          hready.workspace)
        x.active T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (ord inst.a inst.N inst.coprime) (ASize x.active)
        (e dim (basisIdx dim b0))
      ≥ κ / (2 * (Nat.log2 inst.N : ℝ) ^ 4) := by
  have h := Shor_correct_approx_lowered (qs := qs) T hT inst P hP x y work scratch flag b0
    hm hn η hη hready
  rwa [probability_of_success_ket _ hdim _ _ _ _ _ hb0] at h

/-! ## At the circuit's own qubit count

`shorDim` is the qubit ceiling of the reference circuit. A closed form read
off the reference layout would also do; this is the one that needs no layout
lemma, and the theorems above are stated at an arbitrary `dim` so a closed
form can be substituted later without restating anything.
-/

/-- The number of qubits the reference circuit for a submission touches. -/
noncomputable def shorDim (s : ShorSubmission) (inst : ShorOrderFindingInstance) : ℕ :=
  maxQubit (refProg s inst).circuit

theorem maxQubit_le_shorDim (s : ShorSubmission) (inst : ShorOrderFindingInstance) :
    maxQubit (refProg s inst).circuit ≤ shorDim s inst := le_rfl

/-- The certificate at the circuit's own qubit count: no free `dim`, no
side condition. -/
theorem ql_submission_correct_shorDim (s : ShorSubmission) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) (inst : ShorOrderFindingInstance) :
    referenceSuccessProbabilityAt submissionPrecision inst.N
      ≤ qlSuccess (shorDim s inst) (refProg s inst).circuit (refProg s inst).output T
          (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (ord inst.a inst.N inst.coprime) (ASize (refProg s inst).output) :=
  ql_submission_correct s T hT inst _ (maxQubit_le_shorDim s inst)

/-!
## Axioms

```
#print axioms ql_submission_correct
-- 'Shor.Model.QuantumLib.ql_submission_correct' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```
-/

end QuantumLib
end Model
end Shor
