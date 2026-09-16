import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceLayout

/-!
# E5: Shor register plan

For a ladder of modulus bit-lengths `n` and precision levels `m`, using
synthetic instances `N = 2^n − 1, a = 2` (`N` is always odd, so
`gcd a N = 1` always holds; `a < N` holds for `n ≥ 2`): `referenceXWidth`,
`referenceDataWidth`, `referenceWorkWidth` (through `algorithm1ExtraBitsNat
m`), `referenceScratchWidth`, and the four reserve sizes from
`referenceWorkspaceNeed`. Affine tails are detected per column the same way
as E3 (`Symbolic/Width.lean`'s `affineTail`, applied by the caller to the
extracted `(m, width)` columns below).
-/

namespace Shor

open Reference

/-- Widths and reserves at one precision level `m`, for a fixed modulus
bit-length. -/
structure ShorPlanPerM where
  m : ℕ
  workWidth : ℕ
  scratchWidth : ℕ
  exponentReserve : ℕ
  dataReserve : ℕ
  auxiliaryReserve : ℕ
  scratchReserve : ℕ
deriving Repr

/-- One row of the Shor register plan: a modulus bit-length `n`, its
(`m`-independent) `x`/data widths, and the per-`m` table. -/
structure ShorPlanRow where
  n : ℕ
  xWidth : ℕ
  dataWidth : ℕ
  perM : List ShorPlanPerM
deriving Repr

/-- Build one `ShorPlanRow` at bit-length `n`, precision levels `0..mMax`,
using the synthetic instance `N := 2^n - 1, a := 2`. `none` if that instance
is invalid (defensively checked the same way `Main.lean`'s `runEmit` checks a
real instance; cannot happen for `n ≥ 2`, since `N` is odd and `2 < N`). -/
def shorPlanRow {k : ℕ} (ops : Prog k) (n mMax : ℕ) : Option ShorPlanRow :=
  let N := 2 ^ n - 1
  let a := 2
  if hrange : 0 < a ∧ a < N then
    if hcop : Nat.gcd a N = 1 then
      let inst : ShorOrderFindingInstance := ⟨a, N, hrange, hcop⟩
      some
        { n := n
          xWidth := referenceXWidth inst
          dataWidth := referenceDataWidth inst
          perM :=
            (List.range (mMax + 1)).map fun m =>
              let need := referenceWorkspaceNeed ops inst m
              { m := m
                workWidth := referenceWorkWidth inst m
                scratchWidth := referenceScratchWidth inst m
                exponentReserve := need.exponent
                dataReserve := need.data
                auxiliaryReserve := need.auxiliary
                scratchReserve := need.scratch } }
    else none
  else none

/-- The Shor register plan for `n = nMin..nMax`, dropping any bit-length whose
synthetic instance is invalid. -/
def shorPlanTable {k : ℕ} (ops : Prog k) (nMin nMax mMax : ℕ) : List ShorPlanRow :=
  ((List.range (nMax + 1 - nMin)).map (fun i => nMin + i)).filterMap fun n =>
    shorPlanRow ops n mMax

end Shor
