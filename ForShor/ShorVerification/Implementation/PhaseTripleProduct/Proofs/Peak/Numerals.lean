import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Peak.Peak
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Witness.RecursionWitness

/-!
# Kernel-checked single-product peaks, both negation methods

Two concrete policies, each costed under `oneQubit` (the default) and under `scratch`:

* `Witness.negFixed` (`Witness/RecursionWitness.lean`): `k = 2`, one band at width 20, child width 14, three
  additions and two negations in the table program;
* `Ref2048.policy`: the golden reference phase-triple-product policy for 2048 bits, four bands (thresholds
  2048, 398, 122, 66; `k = 6, 4, 2, 2`), whose exact-width ladder from 2048 is
  `2048, 375, 189, 96, 50` with a schoolbook leaf at 50. The tables are copied here (from
  `policies/ref_ptp_2048.json`, as generated for `Submission/Policies/RefPtp2048.lean`), so this file does not
  depend on the submission files; they are data, and any slip in the copy would make `check` fail, not the numerals.

For each, `ptpPeakQubits = 3 n + ptpWsTD + ptpCleanAncD` (`Statement.lean`) is evaluated by the kernel
(`decide +kernel`) at both width rules, next to `ptpQubits` (the formula the optimisation board reports as
`qubits`), so the claims `PTPPeakQubits*` have concrete content for both methods.
-/

namespace Shor.PTP.Peak

open Shor Operations

namespace Ref2048

/-- Table 0: k = 6, 16 points, 109 operations. -/
abbrev t0K : ℕ := 6

def t0Pts : List Point :=
  [Point.int 0, Point.frac 0, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2), Point.int 4, Point.int (-4), Point.int 8, Point.int (-8), Point.int 16, Point.int (-16), Point.int 32, Point.int (-32), Point.int 64, Point.int (-64)]

def t0Ops : Prog t0K :=
  [ valid_ops.addScaled 2 0 false 0
  , valid_ops.addScaled 2 4 false 0
  , valid_ops.addScaled 1 3 false 0
  , valid_ops.addScaled 1 5 false 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 1 true 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 5
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 2
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 1
  , valid_ops.addScaled 2 3 true 2
  , valid_ops.addScaled 2 5 true 5
  , valid_ops.addScaled 2 5 false 1
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 3
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 6
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 4
  , valid_ops.addScaled 2 3 true 5
  , valid_ops.addScaled 2 5 true 10
  , valid_ops.addScaled 2 5 false 6
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 7
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 10
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 7
  , valid_ops.addScaled 2 3 true 8
  , valid_ops.addScaled 2 5 true 15
  , valid_ops.addScaled 2 5 false 11
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 11
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 14
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 10
  , valid_ops.addScaled 2 3 true 11
  , valid_ops.addScaled 2 5 true 20
  , valid_ops.addScaled 2 5 false 16
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 15
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 18
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 13
  , valid_ops.addScaled 2 3 true 14
  , valid_ops.addScaled 2 5 true 25
  , valid_ops.addScaled 2 5 false 21
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 19
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 22
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 16
  , valid_ops.addScaled 2 3 true 17
  , valid_ops.addScaled 2 5 true 30
  , valid_ops.addScaled 2 5 false 26
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 23
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.shiftR 1 7
  , valid_ops.addScaled 2 4 true 24
  , valid_ops.addScaled 2 0 true 0
  , valid_ops.addScaled 2 1 false 6
  , valid_ops.shiftR 2 12
  , valid_ops.addScaled 1 5 true 24
  , valid_ops.addScaled 1 3 true 12 ]

theorem t0Hpts : t0Pts.length = pointCount t0K := by decide

/-- Table 1: k = 4, 10 points, 48 operations. -/
abbrev t1K : ℕ := 4

def t1Pts : List Point :=
  [Point.int 0, Point.frac 0, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2), Point.int 4, Point.int (-4), Point.int 8, Point.int (-8)]

def t1Ops : Prog t1K :=
  [ valid_ops.addScaled 1 3 false 0
  , valid_ops.addScaled 2 0 false 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 1 true 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 3
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 1
  , valid_ops.addScaled 2 3 true 2
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 4
  , valid_ops.addScaled 2 3 true 5
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 7
  , valid_ops.addScaled 2 3 true 8
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 0
  , valid_ops.shiftR 1 4
  , valid_ops.addScaled 2 1 false 3
  , valid_ops.shiftR 2 6
  , valid_ops.addScaled 1 3 true 6 ]

theorem t1Hpts : t1Pts.length = pointCount t1K := by decide

/-- Table 2: k = 2, 4 points, 8 operations. -/
abbrev t2K : ℕ := 2

def t2Pts : List Point :=
  [Point.int 1, Point.int 0, Point.int (-1), Point.frac 0]

def t2Ops : Prog t2K :=
  [ valid_ops.addScaled 1 0 false 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.addScaled 0 1 false 0 ]

theorem t2Hpts : t2Pts.length = pointCount t2K := by decide

/-- Table 0 as a `PTPTable` (contract checked below). -/
def tbl0 : PTPTable := ⟨t0K, t0Pts, t0Ops⟩

/-- Table 1 as a `PTPTable` (contract checked below). -/
def tbl1 : PTPTable := ⟨t1K, t1Pts, t1Ops⟩

/-- Table 2 as a `PTPTable` (contract checked below). -/
def tbl2 : PTPTable := ⟨t2K, t2Pts, t2Ops⟩

/-- The policy: bands widest first. -/
def policy : PTPPolicy where
  bands := [⟨2048, tbl0⟩, ⟨398, tbl1⟩, ⟨122, tbl2⟩, ⟨66, tbl2⟩]

theorem check : policy.check = true := by decide +kernel

/-- The reference policy has no `negate` operation, so the negation method does not enter its census:
the two methods price it alike. (`negCount` is the number of negations in a program.) -/
theorem no_negate : negCount tbl0.ops = 0 ∧ negCount tbl1.ops = 0 ∧ negCount tbl2.ops = 0 := by
  decide +kernel

/-- The reference shape with `negate x₁; negate x₁` appended to the top table's program (the identity, as in
`Witness.negFixed`, so the point order and the table contract are unchanged): a 2048-bit policy in which the
negation method matters. -/
def tblNeg : PTPTable := ⟨t0K, t0Pts, t0Ops ++ [.negate ⟨1, by decide⟩, .negate ⟨1, by decide⟩]⟩

def policyNeg : PTPPolicy where
  bands := [⟨2048, tblNeg⟩, ⟨398, tbl1⟩, ⟨122, tbl2⟩, ⟨66, tbl2⟩]

theorem checkNeg : policyNeg.check = true := by decide +kernel

end Ref2048

/-! ## Peaks, `Witness.negFixed` (`n = 20`)

Three additions and two negations, child width 14 at the scan rule, 12 at the exact rule. Named qubits at most
`3 n + ptpWsTD = 60 + 26` (scan) or `60 + 14` (exact), method independent; the scratch is the method's:
`1` under `oneQubit`, `C' + 1` at the negating node under `scratch` (`C' = 14`, resp. `12`). -/

section NegFixed

open Shor.PTP.Witness

theorem negFixed_ws :
    ptpWsTD negFixed scanRule 20 = 26 ∧ ptpWsTD (negFixed.withNegation .scratch) scanRule 20 = 26 ∧
    ptpWsTD negFixed exactRule 20 = 14 ∧ ptpWsTD (negFixed.withNegation .scratch) exactRule 20 = 14 := by
  decide +kernel

theorem negFixed_peak_oneQubit :
    ptpCleanAncD negFixed scanRule 20 = 1 ∧ ptpPeakQubits negFixed scanRule 20 = 87 ∧
    ptpCleanAncD negFixed exactRule 20 = 1 ∧ ptpPeakQubits negFixed exactRule 20 = 75 := by
  decide +kernel

theorem negFixed_peak_scratch :
    ptpCleanAncD (negFixed.withNegation .scratch) scanRule 20 = 15 ∧
    ptpPeakQubits (negFixed.withNegation .scratch) scanRule 20 = 101 ∧
    ptpCleanAncD (negFixed.withNegation .scratch) exactRule 20 = 13 ∧
    ptpPeakQubits (negFixed.withNegation .scratch) exactRule 20 = 87 := by
  decide +kernel

/-- The `ptpQubits` formula at the scan rule, next to the peaks above: `86` (`oneQubit`), `99` (`scratch`). -/
theorem negFixed_ptpQubits :
    ptpQubits negFixed 20 = 86 ∧ ptpQubits (negFixed.withNegation .scratch) 20 = 99 := by
  decide +kernel

end NegFixed

/-! ## Peaks, the 2048-bit reference policy and its negating variant

`Ref2048.policy` has no negation, so both methods give the same numbers: at the scan rule
`ptpWsTD = 1352`, `ptpCleanAncD = 1`, peak `6144 + 1352 + 1 = 7497`, where the `ptpQubits` formula says `10946`;
at the exact rule (ladder `2048, 375, 189, 96, 50`) `ptpWsTD = 638`, `ptpCleanAncD = 1`, peak `6783`.
In `Ref2048.policyNeg`, the negation pair at the top table makes the method matter: scratch `C' + 1` at the
top node (`C' = 398` scan, `375` exact) instead of `1`. -/

section Ref

open Ref2048

theorem ref_methods_agree :
    ptpPeakQubits (policy.withNegation .scratch) scanRule 2048 = ptpPeakQubits policy scanRule 2048 ∧
    ptpPeakQubits (policy.withNegation .scratch) exactRule 2048 = ptpPeakQubits policy exactRule 2048 ∧
    ptpQubits (policy.withNegation .scratch) 2048 = ptpQubits policy 2048 := by
  decide +kernel

theorem ref_peak_scan :
    ptpWsTD policy scanRule 2048 = 1352 ∧ ptpCleanAncD policy scanRule 2048 = 1 ∧
    ptpPeakQubits policy scanRule 2048 = 7497 ∧ ptpQubits policy 2048 = 10946 := by
  decide +kernel

theorem ref_peak_exact :
    ptpWsTD policy exactRule 2048 = 638 ∧ ptpCleanAncD policy exactRule 2048 = 1 ∧
    ptpPeakQubits policy exactRule 2048 = 6783 := by
  decide +kernel

theorem refNeg_peak_oneQubit :
    ptpCleanAncD policyNeg scanRule 2048 = 1 ∧ ptpPeakQubits policyNeg scanRule 2048 = 7497 ∧
    ptpCleanAncD policyNeg exactRule 2048 = 1 ∧ ptpPeakQubits policyNeg exactRule 2048 = 6783 := by
  decide +kernel

theorem refNeg_peak_scratch :
    ptpCleanAncD (policyNeg.withNegation .scratch) scanRule 2048 = 399 ∧
    ptpPeakQubits (policyNeg.withNegation .scratch) scanRule 2048 = 7895 ∧
    ptpCleanAncD (policyNeg.withNegation .scratch) exactRule 2048 = 376 ∧
    ptpPeakQubits (policyNeg.withNegation .scratch) exactRule 2048 = 7158 := by
  decide +kernel

end Ref

/-! ## The bound is attained on a concrete circuit, and `ptpQubits` is not a bound on `qubitCount`

`Witness.impl` is a concrete gate-level recursion following `fixed` (`k = 2`, one band at width 20, three
additions, no negation, so both methods price it alike). Its framework qubit count is computed by the kernel:
the gates name exactly `86 = 60 + 26 = 3 n + ptpWsTD` qubits and the model holds `1 = ptpCleanAncD` clean qubit,
so `qubitCount = 87 = ptpPeakQubits fixed scanRule 20`: on this circuit the bound of `PTPPeakQubitsScan` is an
equality. The `ptpQubits` formula says `86`, one less: it counts the sandwich leaves' two ancillas and the scratch
as one `max`, but the circuit holds them at once (they are named qubits, and the scratch is extra). -/

section Attained

open Shor.PTP.Witness Shor.PTP.Instances.FaultChallenge

/-- The circuit of `Witness.impl`, at angle `0` (the qubit count does not depend on the angle). -/
noncomputable def fixedCircuit : LowGate :=
  ptpSubNode fixedTable SL (fun t j =>
    ptpLeafSandwich ((0 : Angle) * coeffN fixedTable 20 t) (Y j 0) (Y j 1) (Y j 2) 84 85)

set_option maxRecDepth 1000000 in
theorem fixedCircuit_used : (LowGate.usedQubits fixedCircuit).card = 86 := by decide +kernel

theorem fixedCircuit_cleanAnc :
    (LowGate.resources fixed.resourceModel fixedCircuit).cleanAnc = 1 ∧
    (LowGate.resources (fixed.withNegation .scratch).resourceModel fixedCircuit).cleanAnc = 1 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Peak of the concrete circuit: exactly `ptpPeakQubits`. -/
theorem fixedCircuit_qubitCount :
    LowGate.qubitCount fixed.resourceModel fixedCircuit = 87 ∧
    ptpPeakQubits fixed ptpScanWidth 20 = 87 := by
  constructor
  · have h : LowGate.qubitCount fixed.resourceModel fixedCircuit =
        (LowGate.usedQubits fixedCircuit).card +
          (LowGate.resources fixed.resourceModel fixedCircuit).cleanAnc := rfl
    rw [h, fixedCircuit_used, fixedCircuit_cleanAnc.1]
  · decide +kernel

/-- The `ptpQubits` formula says `86`: one below the circuit's `qubitCount`. -/
theorem fixed_ptpQubits : ptpQubits fixed 20 = 86 := by decide +kernel

end Attained

end Shor.PTP.Peak
