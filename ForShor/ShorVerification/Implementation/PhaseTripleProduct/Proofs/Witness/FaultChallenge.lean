import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Support.Mirror
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Table.Contract
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Table.Width
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Values.Semantics
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Values.Exact

/-!
# PTP fault challenge: the contract and the width are load-bearing

Tautology checks for the PTP theorems (reference `φ·x₀·x₁·x₂` held fixed,
system altered).

**Point-order fault.** A valid `k = 2` PTP program consumes its four
checkpoints in the order `0, ∞, 1, -1`. The faulty table declares
`0, ∞, -1, 1`. The PTP contract rejects it (`faulty_rejected`); the corrected
order passes (`fixed_accepted`). Evaluated anyway, at width `20` with
`x₀ = x₁ = x₂ = 1025 = 2^10 + 1` and `φ = 1`, the faulty policy applies
`B³ + 3B² - 5B + 1` (`B = 2^10`), not `1025³ = (B+1)³` (`faulty_wrong`).

**Width fault.** For the corrected table the PTP child width at `20` is `14`
(`fixed_childWidth`). On `x = 2^19 - 1 = 511·2^10 + 1023` (fits 20 signed
bits) the intermediate `x₀ + x₁ = 1534` needs 12 signed bits: wrapping the
registers at 11 bits turns the third child operand into `-514`
(`wrapped11_children`), so the node's weighted sum is wrong
(`width_fault_wrong`), while wrapping at the PTP width changes nothing
(`wrapped14_children`, an instance of `node_width_sound`).
-/

namespace Shor.PTP.Instances.FaultChallenge

open Operations Shor.PTP

/-- Consumes `0` (`x₀`), `∞` (`x₁`), `1` (`x₀ + x₁`), `-1` (`x₀ - x₁`), then restores. -/
def ops : Prog 2 :=
  [ .phaseProduct ⟨0, by decide⟩
  , .phaseProduct ⟨1, by decide⟩
  , .addScaled ⟨0, by decide⟩ ⟨1, by decide⟩ false 0
  , .phaseProduct ⟨0, by decide⟩
  , .addScaled ⟨0, by decide⟩ ⟨1, by decide⟩ true 1
  , .phaseProduct ⟨0, by decide⟩
  , .addScaled ⟨0, by decide⟩ ⟨1, by decide⟩ false 0 ]

def faultyTable : PTPTable := ⟨2, [Point.int 0, Point.frac 0, Point.int (-1), Point.int 1], ops⟩
def fixedTable : PTPTable := ⟨2, [Point.int 0, Point.frac 0, Point.int 1, Point.int (-1)], ops⟩

def faulty : PTPPolicy := { bands := [⟨20, faultyTable⟩] }
def fixed : PTPPolicy := { bands := [⟨20, fixedTable⟩] }

theorem faulty_rejected : faulty.check = false := by decide +kernel
theorem fixed_accepted : fixed.check = true := by decide +kernel

theorem fixed_childWidth : childWidth 20 ops = 14 := by decide +kernel
theorem limbWidth_20 : limbWidth 20 2 = 10 := by decide +kernel

/-- Interpolation matrix of `0, ∞, -1, 1` and its inverse. -/
theorem inv_faulty :
    (ToomCookMath.interpMatrix (pointRowQ 4) (fun i : Fin 4 => faultyTable.pts.get i))⁻¹ =
      !![1, 0, 0, 0; 0, -1, -1/2, 1/2; -1, 0, 1/2, 1/2; 0, 1, 0, 0] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ToomCookMath.interpMatrix, pointRowQ, faultyTable, Matrix.mul_apply,
      Fin.sum_univ_four] <;> norm_num

/-- Interpolation matrix of `0, ∞, 1, -1` and its inverse. -/
theorem inv_fixed :
    (ToomCookMath.interpMatrix (pointRowQ 4) (fun i : Fin 4 => fixedTable.pts.get i))⁻¹ =
      !![1, 0, 0, 0; 0, -1, 1/2, -1/2; -1, 0, 1/2, 1/2; 0, 1, 0, 0] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ToomCookMath.interpMatrix, pointRowQ, fixedTable, Matrix.mul_apply,
      Fin.sum_univ_four] <;> norm_num

def B : ℚ := 2 ^ 10

theorem faulty_coeff (t : Fin 4) :
    faultyTable.coeff 20 t = ![1 - B ^ 2, B ^ 3 - B, (B ^ 2 - B) / 2, (B ^ 2 + B) / 2] t := by
  unfold PTPTable.coeff
  have hw : limbWidth 20 faultyTable.k = 10 := by decide +kernel
  simp only [hw]
  change Matrix.vecMul (fun j : Fin 4 => ((2 : ℚ) ^ 10) ^ (j : ℕ))
      (ToomCookMath.interpMatrix (pointRowQ 4) (fun i : Fin 4 => faultyTable.pts.get i))⁻¹ t = _
  rw [inv_faulty]
  fin_cases t <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_four, B] <;> ring

theorem fixed_coeff (t : Fin 4) :
    fixedTable.coeff 20 t = ![1 - B ^ 2, B ^ 3 - B, (B ^ 2 + B) / 2, (B ^ 2 - B) / 2] t := by
  unfold PTPTable.coeff
  have hw : limbWidth 20 fixedTable.k = 10 := by decide +kernel
  simp only [hw]
  change Matrix.vecMul (fun j : Fin 4 => ((2 : ℚ) ^ 10) ^ (j : ℕ))
      (ToomCookMath.interpMatrix (pointRowQ 4) (fun i : Fin 4 => fixedTable.pts.get i))⁻¹ t = _
  rw [inv_fixed]
  fin_cases t <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_four, B] <;> ring

/-- The children the program actually produces from `1025` (limbs `1, 1`). -/
theorem children_1025 : faultyTable.children id 20 1025 = [1, 1, 2, 0] := by decide +kernel

/-! ## Point-order fault -/

theorem faulty_value : faulty.evalPhase 20 1 (fun _ => 1025) = B ^ 3 + 3 * B ^ 2 - 5 * B + 1 := by
  have hc : faulty.choose 20 = some faultyTable := rfl
  have hlt : childWidth 20 faultyTable.ops < 20 := by
    show childWidth 20 ops < 20; rw [fixed_childWidth]; decide
  have hleaf : faulty.choose (childWidth 20 faultyTable.ops) = none := by
    show faulty.choose (childWidth 20 ops) = none; rw [fixed_childWidth]; rfl
  rw [PTPPolicy.evalPhase, hc]
  simp only [hlt, ↓reduceDIte]
  simp only [PTPPolicy.evalPhase.eq_1, hleaf]
  show ∑ t : Fin 4, _ = _
  rw [Fin.sum_univ_four]
  simp only [faulty_coeff, children_1025]
  simp [B]
  norm_num

/-- **The contract is load-bearing**: the faulty policy computes the wrong phase. -/
theorem faulty_wrong : faulty.evalPhase 20 1 (fun _ => 1025) ≠ 1 * 1025 * 1025 * 1025 := by
  rw [faulty_value]; norm_num [B]

/-! ## Width fault -/

/-- `2^19 - 1`, fits 20 signed bits. -/
def big : ℤ := 524287

theorem big_fits : Shor.FitsSignedWidth 20 big := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> simp [Shor.signedMin, Shor.signedMax, big]

theorem exact_children : fixedTable.children id 20 big = [1023, 511, 1534, 512] := by decide +kernel

/-- Wrapping at 11 bits corrupts the third child operand. -/
theorem wrapped11_children :
    fixedTable.children (Shor.tcWrapInt 11) 20 big = [1023, 511, -514, 512] := by decide +kernel

/-- Wrapping at the PTP child width changes nothing. -/
theorem wrapped14_children :
    fixedTable.children (Shor.tcWrapInt 14) 20 big = [1023, 511, 1534, 512] := by decide +kernel

/-- The node's weighted sum of child products with child operands `v`. -/
noncomputable def nodeSum (v : List ℤ) : ℚ :=
  ∑ t : Fin 4, fixedTable.coeff 20 t * ((v.getD t 0 : ℚ) ^ 3)

theorem nodeSum_exact : nodeSum (fixedTable.children id 20 big) = (big : ℚ) ^ 3 := by
  rw [exact_children, nodeSum, Fin.sum_univ_four]
  simp only [fixed_coeff]
  simp [B, big]
  norm_num

/-- **The width is load-bearing**: wrapping one bit too narrow (11 < 12 needed)
makes the node apply the wrong phase on an operand that fits 20 bits. -/
theorem width_fault_wrong : nodeSum (fixedTable.children (Shor.tcWrapInt 11) 20 big) ≠ (big : ℚ) ^ 3 := by
  rw [wrapped11_children, nodeSum, Fin.sum_univ_four]
  simp only [fixed_coeff]
  simp [B, big]
  norm_num

/-! ## Exact-width fault: one bit below `ptpTightWidth` -/

/-- The exact PTP width of the corrected table at `20` is `12` (the scan says `14`). -/
theorem fixed_tight : ptpTightWidth fixedTable 20 = 12 := by decide +kernel

/-- The exact board ladder from `20`. -/
theorem fixed_ladderX : fixed.ladderX 20 = [(20, some 2), (12, none)] := by decide +kernel

/-- Minimality witness at `12 - 1 = 11`: operand `big` reaches `1534`, which does not
fit signed 11 bits. -/
theorem big_trace_has_1534 : (1534 : ℤ) ∈ opTrace fixedTable 20 big := by decide +kernel

theorem not_fits_11 : ¬ Shor.FitsSignedWidth 11 1534 := by
  intro h; obtain ⟨-, -, h2⟩ := h; simp [Shor.signedMax] at h2

/-- At the exact width the wrapped children are the exact ones. -/
theorem wrapped12_children :
    fixedTable.children (Shor.tcWrapInt 12) 20 big = [1023, 511, 1534, 512] := by decide +kernel

/-- **The exact-width fault gives a wrong result**: the board with the node one bit
below exact (width 11) applies the wrong phase to `big³`. -/
theorem exact_fault_wrong :
    fixed.evalPhaseD (fun _ _ => 11) 20 1 (fun _ => big) ≠ 1 * big * big * big := by
  have hc : fixed.choose 20 = some fixedTable := rfl
  have hleaf : fixed.choose 11 = none := rfl
  rw [PTPPolicy.evalPhaseD, hc]
  simp only [show (11 : ℕ) < 20 by decide, ↓reduceDIte]
  simp only [PTPPolicy.evalPhaseD.eq_1, hleaf]
  have := width_fault_wrong
  unfold nodeSum at this
  intro h; apply this
  rw [show (big : ℚ) ^ 3 = 1 * (big : ℚ) * big * big by ring, ← h]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- The same board at the exact width is correct for every operand triple fitting 20 bits. -/
theorem exact_board_correct (φ : ℚ) (x : Fin 3 → ℤ) (hx : ∀ s, Shor.FitsSignedWidth 20 (x s)) :
    fixed.evalPhaseTight 20 φ x = φ * x 0 * x 1 * x 2 :=
  evalPhaseTight_correct fixed fixed_accepted 20 φ x hx

end Shor.PTP.Instances.FaultChallenge
