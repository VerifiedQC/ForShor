import Model.Scanner.Scanner

/-!
# Quotient/remainder split helper

A single helper lemma. `literalSourceSplit_eq_balanced` states that the literal quotient/remainder source-width vector equals the scanner's balanced vector when `top` is the last row.
-/

namespace Paper.RowMass

/-- The literal quotient/remainder source-width vector is exactly the
scanner's balanced vector when `top` is the last row. -/
theorem literalSourceSplit_eq_balanced {k : Nat}
    (top : Fin k) (htop : top.val + 1 = k) (w : Nat) :
    (fun i : Fin k => if i.val + 1 = k then w - i.val * (w / k) else w / k) =
      Paper.Scanner.balanced top (w / k) (w % k) := by
  funext i
  by_cases hi : i = top
  · subst i
    simp only [htop, ↓reduceIte, Paper.Scanner.balanced]
    have hdiv : w % k + (top.val + 1) * (w / k) = w := by
      simpa only [htop] using Nat.mod_add_div w k
    rw [Nat.add_mul] at hdiv
    omega
  · have hlast : i.val + 1 ≠ k := by
      intro heq
      apply hi
      apply Fin.ext
      omega
    simp [Paper.Scanner.balanced, hi, hlast]

end Paper.RowMass
