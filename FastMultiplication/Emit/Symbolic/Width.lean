import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace

/-!
# E3: width tables

Over `m = 1..mMax` (uniform limbs, `w = k·m`) and over general `w = k..wMax`:
`RecursivePhaseWorkspace.nextWidth`, `RecursivePhaseWorkspace.limbWidth`, and
`reserveNeed`, read directly off the compiler's own definitions — no
recomputation. Only the symbolic policy is emitted; the older tooling's exact
reachable-value ("tight") width scan is not carried over (nothing on this
repository's data path uses it).
-/

namespace Shor

/-- `(m, nextWidth (k·m) (k·m), limbWidth k (k·m) (k·m))` for `m = 1..mMax`. -/
def widthTableByM {k : ℕ} (ops : Prog k) (mMax : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range mMax).map fun m' =>
    let m := m' + 1
    let w := k * m
    (m, RecursivePhaseWorkspace.nextWidth ops w w, RecursivePhaseWorkspace.limbWidth k w w)

/-- `(w, nextWidth w w, reserveNeed.1, reserveNeed.2)` for `w = k..wMax`. -/
def widthTableByW {k : ℕ} (ops : Prog k) (wMax : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  if wMax < k then
    []
  else
    (List.range (wMax - k + 1)).map fun i =>
      let w := k + i
      let need := RecursivePhaseWorkspace.reserveNeed ops w w
      (w, RecursivePhaseWorkspace.nextWidth ops w w, need.1, need.2)

/-- Least `(m₀, β)`, among a contiguous `(m, W m)` table given oldest-`m`-last
(as `widthTableByM`'s `.map (fun (m,W,_) => (m,W))` produces after `.reverse`,
or any list where the *last* entry is the largest `m` scanned), such that
`W(m) = m + β` for every `m ≥ m₀` in the table — equivalently
`W(m+1) = W(m) + 1` for consecutive scanned `m`. `none` if the table is empty
or `W` decreases below `m` (no affine tail found in the scanned range). -/
def affineTail (widths : List (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  match widths.reverse with
  | [] => none
  | (mLast, wLast) :: rest =>
      let β : ℤ := (wLast : ℤ) - (mLast : ℤ)
      let rec walk : List (ℕ × ℕ) → ℕ → ℕ
        | [], m0 => m0
        | (m, w) :: rest', m0 =>
            if (w : ℤ) - (m : ℤ) = β then walk rest' m else m0
      let m0 := walk rest mLast
      if 0 ≤ β then some (m0, β.toNat) else none

end Shor
