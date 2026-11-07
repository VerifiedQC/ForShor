import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Recursion.Recursion
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Recursion.CensusFull
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Witness.FaultChallenge

/-!
# Non-vacuity of O2: a concrete gate-level recursion

The accepted k = 2 FaultChallenge policy `fixed` (one band at 20, child width 14) on three
20-qubit registers `X s = [20s, 20s + 20)`: a concrete split layout (reserve qubits
60..83, four extension qubits per child slot), sandwich leaves at width 14 with ancillas
84, 85, assembled as a `PolicyImpl`, so `evalL_policyImpl_ket` applies to an actual circuit.
Every structural hypothesis is discharged by `decide`.
-/

namespace Shor.PTP.Witness

open Shor Shor.PTP Shor.PTP.Instances.FaultChallenge

theorem disj_of_check {l1 l2 : List ℕ} (h : (l1.all fun a => !l2.contains a) = true) :
    l1.Disjoint l2 := by
  intro a h1 h2
  have := List.all_eq_true.mp h a h1
  exact (by simpa using this : a ∉ l2) h2

/-- Parent register `s`: qubits `[20s, 20s + 20)`. -/
def X (s : Fin 3) : ExtReg := ExtReg.ofReg (Reg.interval (20 * s) 20)

/-- Chunk register of child slot `(s, j)`, with a 4-qubit reserve at `60 + 8s + 4j`. -/
def pre (s : Fin 3) (j : Fin 2) : ExtReg :=
  ExtReg.withReserve (chunkReg (X s).active 2 ((X s).width / 2) j) (Reg.interval (60 + 8 * s + 4 * j) 4)
    (disj_of_check (by revert s j; decide +kernel))

theorem childWidth_20 : childWidth 20 fixedTable.ops = 14 := fixed_childWidth

def SL : SplitLayout X fixedTable.k (childWidth 20 fixedTable.ops) where
  pre := pre
  ext := fun _ _ => 4
  two_le := by decide +kernel
  pre_active := fun s j => rfl
  can_grow := by intro s j; show 4 ≤ (pre s j).capacity; revert s j; decide +kernel
  ext_width := by rw [childWidth_20]; decide +kernel
  ext_pos := by decide +kernel
  disjoint := by
    intro s j s' j' h
    apply disj_of_check
    revert h
    revert s j s' j'
    decide +kernel

/-- Child slot triple `j` (width 14). -/
def Y (j : Fin 2) : Fin 3 → ExtReg := fun s => SL.lay.slot s j

/-- The leaf of child triple `j`, ancillas 84 and 85. -/
theorem leafImpl (j : Fin 2) :
    PolicyImpl fixed (Y j) (childWidth 20 fixedTable.ops) [84, 85]
      (fun θ => ptpLeafSandwich θ (Y j 0) (Y j 1) (Y j 2) 84 85) := by
  refine PolicyImpl.leaf (Y j) _ 84 85 ?_ ?_ ?_ ?_
  · intro s; show (SL.lay.slot s j).width = _; exact SL.lay.slot_width s j
  · intro T hT
    rw [childWidth_20] at hT
    have h14 : fixed.choose 14 = none := rfl
    rw [h14] at hT
    cases hT
  · refine ⟨disj_of_check ?_, disj_of_check ?_, disj_of_check ?_⟩ <;> revert j <;> decide +kernel
  · unfold SandwichAnc; revert j; decide +kernel

/-- **The witness**: a depth-one gate-level PTP recursion following `fixed` at width 20. -/
theorem impl :
    PolicyImpl fixed X 20 (SL.R ++ [84, 85])
      (fun θ => ptpSubNode fixedTable SL (fun t j => ptpLeafSandwich (θ * coeffN fixedTable 20 t)
        (Y j 0) (Y j 1) (Y j 2) 84 85)) :=
  PolicyImpl.node X 20 fixedTable (by decide +kernel) (by decide +kernel) rfl
    (by rw [childWidth_20]; decide +kernel) SL (fun j θ => ptpLeafSandwich θ (Y j 0) (Y j 1) (Y j 2) 84 85)
    [84, 85] (fun _ => [84, 85]) (fun _ _ h => h) (by unfold SplitLayout.lay; decide +kernel) leafImpl

/-- The concrete circuit is gate-correct (O2 instantiated). -/
theorem impl_correct {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs] (φ : Angle)
    (b : qs.Basis) (hfit : ∀ s, FitsSignedWidth 20 (extToInt (X s) b))
    (hclean : ∀ q ∈ SL.R ++ [84, 85], RegEncoding.bit q b = false) :
    LowerGateClass.evalL (qs := qs) (ptpSubNode fixedTable SL (fun t j =>
        ptpLeafSandwich (φ * coeffN fixedTable 20 t) (Y j 0) (Y j 1) (Y j 2) 84 85)) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((extToInt (X 0) b : ℤ) : ℂ) * ((extToInt (X 1) b : ℤ) : ℂ) *
          ((extToInt (X 2) b : ℤ) : ℂ))) • qs.ket b :=
  evalL_policyImpl_ket fixed_accepted impl φ b hfit hclean

/-- The hypotheses are satisfiable: the all-zero basis state is clean and fits. -/
theorem impl_hyps_sat {Basis : Type*} [RegEncoding Basis] :
    (∀ q ∈ SL.R ++ [84, 85], RegEncoding.bit q (RegEncoding.zero : Basis) = false) :=
  fun q _ => RegEncoding.bit_zero q

/-- Its Rz / Toffoli census is the policy formula: `ptpResources fixed 20`
(4 children of width 14: Rz = 4 · 14³ = 10976). -/
theorem impl_resources (θ : Angle) :
    let R := LowGate.resources fixed.resourceModel (ptpSubNode fixedTable SL (fun t j =>
      ptpLeafSandwich (θ * coeffN fixedTable 20 t) (Y j 0) (Y j 1) (Y j 2) 84 85))
    R.rz = (ptpResources fixed 20).rz ∧ R.toffoli = (ptpResources fixed 20).toffoli :=
  ⟨(impl.resources θ).1, (impl.resources θ).2.1⟩

theorem ptpResources_fixed_20 : (ptpResources fixed 20).rz = 10976 := by decide +kernel

/-! ## Both negation methods on one concrete policy

`negFixed` is `fixed` with a pair of negations of the second operand appended to the table program
(`negate x₁; negate x₁` is the identity, so the point order, the returns-to-start check and the child width
are unchanged). It has `A = 3` additions, `N = 2` negations and `P = 4` checkpoints; at the child width
`C = 14` the node census is evaluated by the kernel under each method, and compared with the closed forms:

* `scratch` (the pre-swap negation, `X = C + (2C - 6) + 2`, `CNOT = 5C - 7`, `Toffoli = 2C - 3`):
  `CNOT = 3 (A + N)(5C - 7) = 945`, `Toffoli = 3 (A + N)(2C - 3) + P · 2 (C² + C³) = 23895`,
  `X = 3 (A (2C - 6) + N (C + (2C - 6) + 2)) = 426`, and `C + 1 = 15` clean qubits;
* `oneQubit` (`X = 67`, `CNOT = 216`, `Toffoli = 140` per negation at `C = 14`):
  `CNOT = 1863`, `Toffoli = 24585`, `X = 600`, and `1` clean qubit.

Rz (`P C³ = 10976`) and H (`0`) are the same under both. -/

/-- `fixed`'s table with `negate x₁` twice appended. -/
def negTable : PTPTable :=
  ⟨2, fixedTable.pts, ops ++ [.negate ⟨1, by decide⟩, .negate ⟨1, by decide⟩]⟩

/-- `fixed` with the negating table. -/
def negFixed : PTPPolicy := { bands := [⟨20, negTable⟩] }

theorem negFixed_accepted : negFixed.check = true := by decide +kernel

theorem negFixed_childWidth : childWidth 20 negTable.ops = 14 := by decide +kernel

theorem negFixed_counts : addCount negTable.ops = 3 ∧ negCount negTable.ops = 2 ∧
    cpCount negTable.ops = 4 := by decide +kernel

/-- Pre-swap anchor: under `scratch` the census is the closed form of the version before the one-qubit
negation. -/
theorem negFixed_scratch_census :
    ptpResources (negFixed.withNegation .scratch) 20 =
      ⟨0, 426, 945, 23895, 10976⟩ := by decide +kernel

/-- Under `oneQubit` (the default) the census is the one of the one-qubit negation. -/
theorem negFixed_oneQubit_census :
    ptpResources negFixed 20 = ⟨0, 600, 1863, 24585, 10976⟩ := by decide +kernel

theorem negFixed_scratch_cnotFull :
    ptpCnotFull (negFixed.withNegation .scratch) 20 = 945 + 6 * (14 - topLimbWidth 20 2) := by
  decide +kernel

theorem negFixed_cleanAnc :
    ptpCleanAnc negFixed 20 = 1 ∧ ptpCleanAnc (negFixed.withNegation .scratch) 20 = 15 := by
  decide +kernel

/-- The same table, `fixed`, has no negation: both methods price it alike. -/
theorem fixed_methods_agree :
    ptpResources (fixed.withNegation .scratch) 20 = ptpResources fixed 20 := by decide +kernel

end Shor.PTP.Witness
