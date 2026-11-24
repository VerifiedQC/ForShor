import ForShor.ShorVerification.Model.Standard.SemiclassicalLocalityModel
import ForShor.ShorVerification.Implementation.Readout.LocalityTight

/-!
# Reserve-qubit reads and the scratch over-count in the standard model

Instances of `Implementation/Readout/LocalityTight.lean` and its proofs file at `Model.qs`, showing
that their hypotheses are satisfiable (the theorems are not vacuous):

* `model_reference_reserve_slots_ne_nil`: at the reference layout `allocateReferenceLayout P inst ℓ`
  (every policy, instance, level) the four reserve slots in question exist: `data.newBits 1`,
  `(data.grow 1).newBits 1`, `work.newBits 1`, `scratch.newBits 1` are nonempty.
* `model_reference_N_bounds`: `1 ≤ N ≤ 2^|data|` at the reference layout.
* `model_reference_step3_read`, `model_reference_step4_read`: at the reference layout the whole
  Step 3 reads the first data reserve slot and the whole Step 4 reads the second (non-commutation
  with `X q`).
* `model_reference_carry_read`, `model_reference_ySign_read`, `model_reference_workSign_read`:
  the named sub-gate forms (for `work.newBits 1` only the sub-gate form exists).
* `model_reference_scratchSign_overcount`: the scratch slot is in `semiclassicalExactQubits` but
  flipping it leaves every record probability of the real circuit unchanged, for every number
  of rounds and every start ket (high-level circuit only).
* `reserveReadLeafPolicy`, `reserveReadSmallInst`, `model_reference_nonvacuous`: the quantifiers over policies and
  instances are not empty (the all-leaf policy, the instance `a = 2`, `N = 15`), and the
  four slots exist there.
* `model_toyPhaseKick`: the toy stand-in (one-qubit operands, angle `1/2`, `H · phase · H`
  shape; NOT the real circuit) at `Model.qs` with concrete qubits `x = [0]`, `x` reserve `[1]`,
  `z = [2]`, `z` reserve `[3]`, from the all-zero ket.

NOT claimed: anything about record probabilities of the real order-finding circuit under a flip
of a read reserve qubit (open).
-/

namespace Shor
namespace Model

open Reference Readout

set_option hygiene false in
local notation "RL" => allocateReferenceLayout P inst ℓ

theorem take_one_ne_nil_of_drop_ne_nil {l : List ℕ} {k : ℕ} (h : l.drop k ≠ []) :
    l.take 1 ≠ [] := by
  intro h1
  rw [List.take_eq_nil_iff] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (by norm_num)
  · subst h1; simp at h

/-- **The four reserve slots exist at the reference layout** (every policy, instance, level). -/
theorem model_reference_reserve_slots_ne_nil (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    ((RL).data.newBits 1).qubits ≠ [] ∧ (((RL).data.grow 1).newBits 1).qubits ≠ [] ∧
      ((RL).work.newBits 1).qubits ≠ [] ∧ ((RL).scratch.newBits 1).qubits ≠ [] := by
  obtain ⟨hd, hw, hs⟩ := reference_unusedReserve_ne_nil P inst ℓ
  refine ⟨take_one_ne_nil_of_drop_ne_nil hd, ?_, take_one_ne_nil_of_drop_ne_nil hw,
    take_one_ne_nil_of_drop_ne_nil hs⟩
  have hlen : 2 < (RL).data.reserve.qubits.length := by
    simpa [Reg.drop, List.drop_eq_nil_iff] using hd
  simp only [ExtReg.newBits, ExtReg.grow, ExtReg.remainingReserve, Reg.take, Reg.drop]
  rcases h : (RL).data.reserve.qubits with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp

/-- `1 ≤ N ≤ 2^|data|` at the reference layout. -/
theorem model_reference_N_bounds (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : 1 ≤ inst.N ∧ inst.N ≤ 2 ^ regSize (RL).data.active := by
  have hr := inst.range
  have hw : regSize (RL).data.active = Nat.log2 (2 * inst.N) :=
    referenceLayout_data_width' P inst ℓ
  have hl := Nat.lt_log2_self (n := 2 * inst.N)
  rw [pow_succ] at hl
  refine ⟨by omega, ?_⟩
  rw [hw]; omega

/-- **Reference layout: the carry slot is read by Step 3's comparator.** -/
theorem model_reference_carry_read (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : ∀ q ∈ ((RL).data.newBits 1).qubits,
      ¬ CommX qs (Gate.CmpGeConst inst.N ((RL).data.grow 1) (RL).scratch (RL).flag) q :=
  fun _ hq => step3Cmp_not_commX_carry (referenceStep4Workspace P inst ℓ)
    (model_reference_N_bounds P inst ℓ).1 (model_reference_N_bounds P inst ℓ).2 hq

/-- **Reference layout: the second data reserve slot is read by Step 4's difference block.** -/
theorem model_reference_ySign_read (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : ∀ q ∈ (((RL).data.grow 1).newBits 1).qubits,
      ¬ CommX qs (cmpLtNWDifference ((RL).data.grow 1) (RL).work (RL).scratch
        (referenceStep4Workspace P inst ℓ).data_can_grow) q :=
  fun _ hq => cmpLtNWDifference_not_commX_ySign (referenceStep4Workspace P inst ℓ) hq

/-- **Reference layout: the work reserve slot is read by Step 4's constant multiplier.** -/
theorem model_reference_workSign_read (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : ∀ q ∈ ((RL).work.newBits 1).qubits,
      ¬ CommX qs (fastConstMulInto inst.N (RL).work (RL).scratch
        (referenceStep4Workspace P inst ℓ).mulWorkspace) q :=
  fun _ hq => fastConstMulInto_not_commX_workSign (referenceStep4Workspace P inst ℓ)
    (model_reference_N_bounds P inst ℓ).1 hq

/-- **Reference layout: the whole Step 3 reads the carry slot.** -/
theorem model_reference_step3_read (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : ∀ q ∈ ((RL).data.newBits 1).qubits,
      ¬ CommX qs (step3 inst.N ((RL).data.grow 1) (RL).scratch (RL).flag) q :=
  fun _ hq => step3_not_commX_carry (referenceStep4Workspace P inst ℓ)
    (model_reference_N_bounds P inst ℓ).1 (model_reference_N_bounds P inst ℓ).2 hq

/-- **Reference layout: the whole Step 4 reads the second data reserve slot.** -/
theorem model_reference_step4_read (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : ∀ q ∈ (((RL).data.grow 1).newBits 1).qubits,
      ¬ CommX qs (step4 inst.N ((RL).data.grow 1) (RL).work (RL).scratch (RL).flag
        (referenceStep4Workspace P inst ℓ)) q :=
  fun _ hq => step4_not_commX_ySign (referenceStep4Workspace P inst ℓ) hq

/-- The all-leaf policy (no bands). -/
def reserveReadLeafPolicy : ShorLoweringPolicy where
  bands := []
  sorted := by simp

/-- A small order-finding instance: `a = 2`, `N = 15`. -/
def reserveReadSmallInst : ShorOrderFindingInstance := ⟨2, 15, by decide, by decide⟩

/-- **The model statements are not vacuous:** a policy and an instance exist, and at them (level
`0`) the four reserve slots are nonempty. -/
theorem model_reference_nonvacuous :
    Nonempty ShorLoweringPolicy ∧ Nonempty ShorOrderFindingInstance ∧
    ((allocateReferenceLayout reserveReadLeafPolicy reserveReadSmallInst 0).data.newBits 1).qubits ≠ [] ∧
    (((allocateReferenceLayout reserveReadLeafPolicy reserveReadSmallInst 0).data.grow 1).newBits 1).qubits ≠ [] ∧
    ((allocateReferenceLayout reserveReadLeafPolicy reserveReadSmallInst 0).work.newBits 1).qubits ≠ [] ∧
    ((allocateReferenceLayout reserveReadLeafPolicy reserveReadSmallInst 0).scratch.newBits 1).qubits ≠ [] :=
  ⟨⟨reserveReadLeafPolicy⟩, ⟨reserveReadSmallInst⟩, model_reference_reserve_slots_ne_nil reserveReadLeafPolicy reserveReadSmallInst 0⟩

/-- **Reference layout: the scratch slot is over-counted.** Every qubit `q` of
`scratch.newBits 1` is in `semiclassicalExactQubits`, yet for every number of rounds `m`, every
start ket `b0` and every record `r`, flipping `q` leaves the record probability of the real
circuit unchanged (high-level circuit only). -/
theorem model_reference_scratchSign_overcount (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) : ∀ q ∈ ((RL).scratch.newBits 1).qubits,
      q ∈ semiclassicalExactQubits (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
        (RL).flag ∧
      ∀ (m : ℕ) (b0 : qs.Basis) (r : Record),
        recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
            (RL).data (RL).work (RL).scratch (RL).flag (referenceCircuitWorkspace P inst ℓ)
            (referenceStep4Workspace P inst ℓ)).eval (MState.init (qs.ket (flipBit q b0)))) r
          = recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
            (RL).data (RL).work (RL).scratch (RL).flag (referenceCircuitWorkspace P inst ℓ)
            (referenceStep4Workspace P inst ℓ)).eval (MState.init (qs.ket b0))) r := by
  intro q hq
  refine ⟨(scratchSign_mem_exact_not_mem_refined inst.N (referenceStep4Workspace P inst ℓ)
    (referenceSemiclassicalLayout P inst ℓ).c_not_mem_scratch hq).1, fun m b0 r => ?_⟩
  exact orderFindingSemiclassical_recordProb_flip_scratchSign inst.a inst.N m
    (referenceCircuitWorkspace P inst ℓ) (referenceStep4Workspace P inst ℓ)
    (referenceSemiclassicalLayout P inst ℓ) b0 hq r

/-- The toy workspace: `x = [0]` with reserve `[1]`, `z = [2]` with reserve `[3]`. -/
def toyWs : Gate.PhaseProdWorkspace (qubitReg 0) (qubitReg 2) where
  xReserve := qubitReg 1
  zReserve := qubitReg 3
  x_can_grow := by decide
  z_can_grow := by decide
  xz_disjoint := by simp [Disjoint, qubitReg, Reg.singleton]
  x_reserve_disjoint := by simp [Disjoint, qubitReg, Reg.singleton]
  z_reserve_disjoint := by simp [Disjoint, qubitReg, Reg.singleton]
  xReserve_not_z := by simp [Disjoint, qubitReg, Reg.singleton]
  zReserve_not_x := by simp [Disjoint, qubitReg, Reg.singleton]
  reserve_disjoint := by simp [Disjoint, qubitReg, Reg.singleton]

/-- **Toy stand-in at `Model.qs`** (one-qubit operands, angle `1/2`; not the real circuit). From the all-zero ket, record `[false]` of
`toyPhaseKick 0 2 toyWs` has probability `1`; after flipping qubit `1` (the `x` sign-extension
bit), probability `0`. -/
theorem model_toyPhaseKick :
    recordProb ((toyPhaseKick 0 2 toyWs).eval
        (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) [false] = 1 ∧
    recordProb ((toyPhaseKick 0 2 toyWs).eval
        (MState.init (qs.ket (flipBit 1 (RegEncoding.zero (Basis := qs.Basis)))))) [false] = 0 :=
  toyPhaseKick_recordProb 0 2 toyWs (q := 1) (zr := 3)
    (by simp [Gate.PhaseProdWorkspace.xExt, toyWs, ExtReg.newBits, qubitReg, Reg.singleton,
      Reg.take])
    (by simp [Gate.PhaseProdWorkspace.zExt, toyWs, ExtReg.newBits, qubitReg, Reg.singleton,
      Reg.take])
    _ (RegEncoding.bit_zero _) (RegEncoding.bit_zero _) (RegEncoding.bit_zero _)
    (RegEncoding.bit_zero _)

end Model
end Shor

-- Axioms (expected: propext, Classical.choice, Quot.sound).
#print axioms Shor.Model.model_reference_reserve_slots_ne_nil
#print axioms Shor.Model.model_reference_N_bounds
#print axioms Shor.Model.model_reference_carry_read
#print axioms Shor.Model.model_reference_ySign_read
#print axioms Shor.Model.model_reference_workSign_read
#print axioms Shor.Model.model_reference_scratchSign_overcount
#print axioms Shor.Model.model_toyPhaseKick
#print axioms Shor.Model.model_reference_step3_read
#print axioms Shor.Model.model_reference_step4_read
#print axioms Shor.Model.model_reference_nonvacuous
