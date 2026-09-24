import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Workspace

/-!
# E4: QFT workspace table

For `w = 1..wMax`: `qftWorkspaceNeed`, the one D4-opaque function the
extracted `qft` template calls by name (`left`/`right` split widths,
`qftPhi`, and the radix-reverse cost are all printed directly by the
template itself now, since R3/R4).
-/

namespace Shor

/-- `(w, xWorkspaceNeed, zWorkspaceNeed)` for `w = 1..wMax`. -/
def qftPlanTable {k : ℕ} (ops : Prog k) (wMax : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range wMax).map fun i =>
    let w := i + 1
    let need := qftWorkspaceNeed ops w
    (w, need.1, need.2)

end Shor
