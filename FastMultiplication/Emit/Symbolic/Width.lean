import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace

/-!
# E3: width table

Over `w = 1..wMax`: `RecursivePhaseWorkspace.nextWidth` and `reserveNeed`,
read directly off the compiler's own definitions — no recomputation. These
are the D4-opaque functions the extracted `phase_product`/`qft` templates
call by name; this table is where their values live. Only the symbolic
policy is emitted; the older tooling's exact reachable-value ("tight") width
scan is not carried over (nothing on this repository's data path uses it).
-/

namespace Shor

/-- `(w, nextWidth w w, reserveNeed.1, reserveNeed.2)` for `w = 1..wMax`. -/
def widthTable {k : ℕ} (ops : Prog k) (wMax : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range wMax).map fun i =>
    let w := i + 1
    let need := RecursivePhaseWorkspace.reserveNeed ops w w
    (w, RecursivePhaseWorkspace.nextWidth ops w w, need.1, need.2)

end Shor
