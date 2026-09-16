import FastMultiplication.Emit.Table.Census
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace

/-!
# E6: recursion skeleton

The ladder `W₀ = w, W_{i+1} = nextWidth W_i` while `W_{i+1} < W_i`, exactly the
`by_cases hrec : nextSignedWidth x z ops < phaseInputSize x z` recursion in
`standardSignedPhaseLoweringPlan` (`RecursivePhaseWorkspace.nextWidth` wraps
`nextSignedWidth` at `wx = wz`). Per level: leaf multiplicity `q^i`,
adder-class cost `A_k · addScaledResources(W_{i+1})`, base cost from the E1
leaf census at the final width, summed under `shorGateCostModel`
(`.totalGates`, since `shorGateCostModel = shorGateResourceModel.toCostModel`
maps each resource field through `.totalGates`). This is the cost model
evaluated on the ladder, not a theorem — the asymptotic statement it
evaluates is `Shor.phaseProductGateCountBound_of_programOK` /
`Shor.exists_shorGateCountBound`.
-/

namespace Shor

/-- The width ladder `[W₀, W₁, …, W_d]` starting from `w`, stopping at the
first width the recursion no longer shrinks (the leaf/base width). Mirrors
`RecursivePhaseWorkspace.reserveNeed`'s own well-founded recursion. -/
def widthLadder {k : ℕ} (ops : Prog k) (w : ℕ) : List ℕ :=
  let next := RecursivePhaseWorkspace.nextWidth ops w w
  if _h : next < w then w :: widthLadder ops next else [w]
termination_by w
decreasing_by simpa using _h

/-- Per-level cost breakdown along a width ladder. -/
structure RecursionLevel where
  depth : ℕ
  width : ℕ
  leafMultiplicity : ℕ
  adderCost : ℕ
  baseCost : ℕ
deriving Repr

/-- Structural recursion mirroring `widthLadder`; `partial` since this is
output-only tooling with no proof obligations (as `LowGateJson.lean`'s
`flattenSeq`/`lowGateJson` already are). -/
partial def recursionLevelsAux
    {k : ℕ} (ops : Prog k) (census : OpCensus) (depth width : ℕ) : List RecursionLevel :=
  let next := RecursivePhaseWorkspace.nextWidth ops width width
  if next < width then
    { depth := depth
      width := width
      leafMultiplicity := q k ^ depth
      adderCost := census.adderClassTotal * (addScaledResourcesAt next).totalGates
      baseCost := 0 } ::
      recursionLevelsAux ops census (depth + 1) next
  else
    [{ depth := depth
       width := width
       leafMultiplicity := q k ^ depth
       adderCost := 0
       baseCost := (naiveLeafResourcesAt width width).totalGates }]

/-- Per-level cost breakdown along the width ladder starting from `w`. -/
def recursionLevels {k : ℕ} (ops : Prog k) (w : ℕ) : List RecursionLevel :=
  recursionLevelsAux ops (opCensus ops) 0 w

/-- Total cost summed across levels, weighted by leaf multiplicity. -/
def recursionTotalCost (levels : List RecursionLevel) : ℕ :=
  levels.foldl (fun acc l => acc + l.leafMultiplicity * (l.adderCost + l.baseCost)) 0

end Shor
