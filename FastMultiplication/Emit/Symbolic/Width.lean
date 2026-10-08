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

/-- `(v, xw, zw, nextWidth xw zw, reserveNeed.1, reserveNeed.2)` for the
*unequal* operand pair `qft` hands `phase_product` at register width `v`.

`widthTable` is the diagonal and nothing else, which is enough for
`phase_product`'s own recursion — a recursive call grows both children to
`nextWidth`, so once the chain starts it stays symmetric. It is not enough
for `qft`, which splits its register at `splitM r = regSize r / 2` and calls
`phase_product` on `(v / 2, v - v / 2)`: unequal at every odd `v`. Without
this table a consumer holding only the bundle cannot instantiate `qft` at an
odd width at all, because the one `nextWidth` value it needs is the one
value not published.

One row per `v`, not per reachable `(xw, zw)` pair, because that is exactly
the set: the only asymmetric query any template makes is `qft`'s split, and
every width the recursion reaches is some `v ≤ wMax`. -/
def splitWidthTable {k : ℕ} (ops : Prog k) (wMax : ℕ) :
    List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (List.range wMax).map fun i =>
    let v := i + 1
    let xw := v / 2
    let zw := v - xw
    let need := RecursivePhaseWorkspace.reserveNeed ops xw zw
    (v, xw, zw, RecursivePhaseWorkspace.nextWidth ops xw zw, need.1, need.2)

/-- The `opaqueW` oracle a *consumer* can build from the published tables
alone — no call into this repository's `nextWidth`/`reserveNeed`/
`qftWorkspaceNeed`.

This is the contract `instantiate` is held to from outside: the three
tabulated functions are resolved by lookup in `width` (diagonal),
`split_width` (`qft`'s unequal pair) and `qft_plan`; the rest (`log2`,
`mod`, `pow`) are ordinary arithmetic any consumer implements. A miss
returns `none`, which `instantiate` reports as an error rather than
silently papering over — so a width outside the published range fails
loudly.

`modpow` and `step5Const` are deliberately absent: they are `shor`'s, not
`phase_product`/`qft`'s, and they depend on the modulus rather than on the
table. A consumer instantiating `shor` implements them directly (see
`IR/README.md`). -/
def tableOpaqueW (wrows : List (ℕ × ℕ × ℕ × ℕ))
    (srows : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (qrows : List (ℕ × ℕ × ℕ)) :
    String → List ℕ → Option ℕ :=
  let diag : ℕ → Option (ℕ × ℕ × ℕ × ℕ) :=
    fun w => wrows.find? (fun row => row.1 == w)
  let split : ℕ → ℕ → Option (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
    fun xw zw => srows.find? (fun row => row.2.1 == xw && row.2.2.1 == zw)
  fun name args =>
    match name, args with
    | "nextWidth", [xw, zw] =>
        if xw == zw then (diag xw).map (fun row => row.2.1)
        else (split xw zw).map (fun row => row.2.2.2.1)
    | "reserveNeed_x", [xw, zw] =>
        if xw == zw then (diag xw).map (fun row => row.2.2.1)
        else (split xw zw).map (fun row => row.2.2.2.2.1)
    | "reserveNeed_z", [xw, zw] =>
        if xw == zw then (diag xw).map (fun row => row.2.2.2)
        else (split xw zw).map (fun row => row.2.2.2.2.2)
    | "qftXWork", [w] => (qrows.find? (fun row => row.1 == w)).map (fun row => row.2.1)
    | "qftZWork", [w] => (qrows.find? (fun row => row.1 == w)).map (fun row => row.2.2)
    | "log2", [n] => some (Nat.log2 n)
    | "mod", [m, n] => some (m % n)
    | "pow", [b, e] => some (b ^ e)
    | _, _ => none

end Shor
