import FastMultiplication.Emit.Lower.Decide
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Workspace

/-!
# Concrete register construction for a chosen `Prog k` and width

Shared by `Lower/PhaseProduct.lean`, `Lower/Qft.lean` (the `pp`/`cpp`/`qft`
CLI commands), and `Reflect/Verify.lean` (the R3 instance-check canary) —
split out on its own so `Reflect/Verify.lean` can build the same concrete
registers those commands do without importing them back (`Verify.lean`
itself is what those files need for their own `instantiate_eq_real` check,
so the dependency has to run this way to avoid a cycle).
-/

namespace Shor

/-- Concrete registers for a (controlled) signed phase product at width `n`.
The controlled variant additionally allocates a control qubit past both
registers' full extent (so it is disjoint from both by construction, still
checked decidably by the caller since that's what
`CSignedRecursiveWorkspaceOK` itself demands). -/
def ppRegisters {k : ℕ} (ops : Prog k) (n : ℕ) : Except String (ExtReg × ExtReg × ℕ) :=
  let need := RecursivePhaseWorkspace.reserveNeed ops n n
  let xActive := Reg.interval 0 n
  let xReserve := Reg.interval n (need.1 + 1)
  if hx : Disjoint xActive xReserve then
    let zStart := n + (need.1 + 1)
    let zActive := Reg.interval zStart n
    let zReserve := Reg.interval (zStart + n) (need.2 + 1)
    if hz : Disjoint zActive zReserve then
      let ctrl := zStart + n + (need.2 + 1)
      .ok (ExtReg.withReserve xActive xReserve hx, ExtReg.withReserve zActive zReserve hz, ctrl)
    else
      .error "internal: z active/reserve overlap"
  else
    .error "internal: x active/reserve overlap"

/-- One register of width `w` with reserve sized by `qftWorkspaceNeed`. -/
def qftRegister {k : ℕ} (ops : Prog k) (w : ℕ) : Except String ExtReg :=
  let need := qftWorkspaceNeed ops w
  let active := Reg.interval 0 w
  let reserve := Reg.interval w (need.1 + need.2)
  if h : Disjoint active reserve then
    .ok (ExtReg.withReserve active reserve h)
  else
    .error "internal: active/reserve overlap"

end Shor
