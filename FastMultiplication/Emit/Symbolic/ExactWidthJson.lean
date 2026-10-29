import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.PolicyWorkspace
import FastMultiplication.Emit.Json.Common
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.ExactWidthBoxes

/-!
# E3: the width rule an exact-width policy document carries

A policy document's IR calls `nextWidth(xw, zw)` (band body `i`: band `i`'s
table) and `reserveNeed_x/z` (policy level) as opaque functions; a consumer
supplies them. On the scan rule (the default) a consumer re-implements the
scan, as before. On the exact rule (`WidthRule.exact`) the width is no longer a
fold over the ops, so the document carries the rule itself, under
`ir.width_rule`:

* per band, the **rows**: every coefficient row the table's program holds in
  some register of some visited state (`exactReachRows`, duplicates removed).
  With them `nextWidth(xw, zw)` at any pair is a closed formula
  (`Compiler/ExactWidth.lean`, transcribed in `formula`);
* per band, `diag`: `[w, nextWidth(w, w)]` for `w = 1..wMax`, read off the
  compiler's own `RecursivePhaseWorkspace.nextWidthBy` (a consumer checks its
  evaluation of the formula against these);
* `reserve_diag`: `[w, reserveNeed_x(w, w), reserveNeed_z(w, w)]` for the policy
  (`Policy.reserveNeed`), same range.

All of it is computed by the same definitions the compiler and its proofs use;
none of it is re-derived.
-/

namespace Shor

open Lean (Json)

/-- The reachable rows of a program, as integer lists, duplicates removed. -/
def exactRowsList {k : ℕ} (ops : Prog k) : List (List ℤ) :=
  ((exactReachRows ops).map fun r => (List.finRange k).map r).eraseDups

def exactWidthFormula : String :=
  "W = min(xw div k, zw div k); chunk j < k-1 has width W, the top chunk xw - (k-1)W \
   (resp. zw); box: lower chunks [0, 2^W - 1], top chunk [-2^(t-1), 2^(t-1) - 1] ([0,0] if t = 0); \
   demand(r) = max(-rowLo, rowHi + 1, 0) with rowLo/rowHi the coordinatewise min/max of \
   sum_j r_j L_j over the box; D = max over rows and both operands; \
   tight = 1 + (least e >= 0 with D <= 2^e); floor = 1 + max chunk width over both operands; \
   nextWidth = max(tight, floor). Shor.exactSignedWidthOfWidths (Compiler/ExactWidth.lean)."

def bandWidthRuleJson (R : WidthRule) (wMax : ℕ) (i : ℕ) (b : ℕ × ShorLoweringSetup) : Json :=
  Json.mkObj [
    ("index", (i : Json)),
    ("k", (b.2.k : Json)),
    ("rows", Json.arr ((exactRowsList b.2.ops).map fun r =>
      Json.arr (r.map fun c => Lean.toJson c).toArray).toArray),
    ("diag", Json.arr ((List.range wMax).map fun j =>
      Json.arr #[((j + 1 : ℕ) : Json),
        (RecursivePhaseWorkspace.nextWidthBy R b.2.ops (j + 1) (j + 1) : Json)]).toArray)
  ]

/-- `ir.width_rule` for a policy submission on the exact rule
(`ShorPolicySubmission.widthRule = .exact`); `forshor_policy_submission` adds it
only then. On the scan rule the document is upstream's, without it. -/
def policyWidthRuleJson (s : ShorPolicySubmission) (wMax : ℕ) : Json :=
  Json.mkObj [
    ("rule", Json.str "forshor.exact-width/v1"),
    ("formula", Json.str exactWidthFormula),
    ("wMax", (wMax : Json)),
    ("bands", Json.arr (s.bands.zipIdx.map (fun p => bandWidthRuleJson s.widthRule wMax p.2 p.1)).toArray),
    ("reserve_diag", Json.arr ((List.range wMax).map fun j =>
      let need := Policy.reserveNeed s.policy (j + 1) (j + 1)
      Json.arr #[((j + 1 : ℕ) : Json), (need.1 : Json), (need.2 : Json)]).toArray)
  ]

end Shor
