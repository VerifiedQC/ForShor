import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Workspace
import FastMultiplication.ShorVerification.Framework.AbstractMachine.Gates

/-!
# E4: QFT plan

For `w = 2..wMax`: the `left`/`right` split widths (`splitM`'s convention:
`left := w / 2`, `right := w - w / 2`, matching both `QFT/Split.lean`'s
`leftReg`/`rightReg` and `qftWorkspaceNeed`'s own local `leftWidth`/
`rightWidth`), `qftPhi w` as an exact angle, the radix-reverse cost
`3 · (w/2)`, and `qftWorkspaceNeed`. This is the rule
`QFT(w) = QFT(right) ; PhaseProd(qftPhi w, left, right) ; QFT(left) ;
RadixReverse` from `standardQFTLoweringPlan`.
-/

namespace Shor

/-- One row of the QFT plan: `(w, leftWidth, rightWidth, qftPhi w,
radixReverseCost, xWorkspaceNeed, zWorkspaceNeed)`. -/
def qftPlanTable {k : ℕ} (ops : Prog k) (wMax : ℕ) :
    List (ℕ × ℕ × ℕ × Angle × ℕ × ℕ × ℕ) :=
  (List.range (wMax + 1)).filterMap fun w =>
    if w < 2 then
      none
    else
      let left := w / 2
      let right := w - left
      let need := qftWorkspaceNeed ops w
      some (w, left, right, qftPhi w, 3 * (w / 2), need.1, need.2)

end Shor
