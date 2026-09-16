import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Compile
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Plan
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Builders.Fragments
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.Correctness

/-!
# Toom-Cook table sources

Two table sources exist in the repository and they are **not** the same
object (see `Emit/README.md`): `standard` (`genOpsWithProduct` fed
`genInterpolationPoints`, via `Shor.standardLoweringSetup`) is what the
lowering theorems (`ShorLoweringSetup.consumes`/`.returns`) are about;
`generate` (`Table_Generation.generate`) is the older table-generation
tooling, kept for comparison, with no such theorem. `standard` is the
default the rest of the emitter uses.
-/

namespace Shor

open Operations

/-- Which Toom-Cook table a `TableInstance` was built from. -/
inductive TableSource where
  | standard
  | generate
deriving Repr, DecidableEq

/-- A concrete `Prog k` / interpolation-point-list pair, plus provenance.
`hlen` lets downstream interpolation code (`Symbolic/CoeffPoly.lean`) consume
`points` without re-deriving its length. -/
structure TableInstance (k : ℕ) where
  ops : Prog k
  points : List Point
  hlen : points.length = q k
  decl : String
  srcFile : String

/-- Resolve a `TableSource` at arity `k`. -/
def tableInstance (src : TableSource) (k : ℕ) (hk : 1 < k) : TableInstance k :=
  match src with
  | .standard =>
      { ops := genOpsWithProduct (k := k) (by omega) (genInterpolationPoints k)
        points := genInterpolationPoints k
        hlen := generatedInterpolationPoints_length k
        decl := "Shor.standardLoweringSetup"
        srcFile :=
          "FastMultiplication/ShorVerification/Implementation/Reference/StandardLoweringSetup.lean" }
  | .generate =>
      -- `generatePointsInOrder`, not a plain `streamPoint` enumeration: for
      -- `k = 2, 3` the precomputed tables consume the canonical points in
      -- their own order (a permutation of `streamPoint`'s enumeration,
      -- `ValidPointOrder`/`generatePointsInOrder_valid`), which is what the
      -- program's `phaseProduct` checkpoints actually see.
      { ops := Table_Generation.generate .PhaseProduct k (by omega)
        points := Table_Generation.generatePointsInOrder .PhaseProduct k (by omega)
        hlen := by
          have hperm := Table_Generation.generatePointsInOrder_valid .PhaseProduct k (by omega)
          simpa [Table_Generation.canonicalPoints, Table_Generation.ProductMode.pointCount, q]
            using hperm.length_eq
        decl := "Table_Generation.generate"
        srcFile :=
          "FastMultiplication/ShorVerification/Implementation/PhaseProduct/Math/" ++
          "Table_Generation/Generator/Defs.lean" }

/-- Computable, ordered mirror of `ProgConsumesPts`: walk `ops` left to right,
consuming `pts` from the front at each `phaseProduct` checkpoint. Unlike the
existing `phaseCoverageFrom?`/`List.eraseFirstMatch?` checker (which accepts a
match anywhere in the remaining point list), this requires each
`phaseProduct i` to match exactly the *next* point, matching
`ProgConsumesPts`'s own `pts = pt :: ptsTail` structure. -/
def progConsumesPtsCheck {k : ℕ} (hk : k > 0) : State k → Prog k → List Point → Bool
  | _σ, [], pts => pts.isEmpty
  | σ, op :: ops, pts =>
      match op with
      | .phaseProduct i =>
          match pts with
          | [] => false
          | pt :: ptsTail =>
              matchesAt_pointRow_state hk σ i pt && progConsumesPtsCheck hk σ ops ptsTail
      | _ =>
          match applyOp? σ op with
          | none => false
          | some σ' => progConsumesPtsCheck hk σ' ops pts

/-- Blocking checks on a table instance. `standard` is backed by the
compile-time theorems `genOpsWithProduct_ProgConsumesPtsSafe`/
`genOpsWithProduct_returns_to_original` bundled into `ShorLoweringSetup`, so it
always succeeds without recomputation. `generate` has no such theorem, so this
runs the checks at run time and refuses (`Except.error`) on any mismatch. -/
def checkTable (src : TableSource) (k : ℕ) (hk : 1 < k) (inst : TableInstance k) :
    Except String Unit :=
  match src with
  | .standard => .ok ()
  | .generate =>
      if phaseProductCount inst.ops ≠ q k then
        .error
          s!"generate k={k}: phaseProduct count {phaseProductCount inst.ops} ≠ q k = {q k}"
      else if run? inst.ops State.start_state ≠ some State.start_state then
        .error s!"generate k={k}: program does not return to the start state"
      else if ¬ progConsumesPtsCheck (by omega) State.start_state inst.ops inst.points then
        .error s!"generate k={k}: ordered point-coverage check failed"
      else
        .ok ()

end Shor
