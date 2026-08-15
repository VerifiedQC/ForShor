import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs

/-!
# Phase-product gate macros (implementation)

The unsigned/controlled phase-product macros (`PhaseProdWorkspace`,
`PhaseProdUsing`, `CPhaseProdUsing`) — specific circuit constructions used only
by the lowering and correctness proofs.  The general register-algebra lemmas
they build on stay in Framework/AbstractMachine/Gates.
-/

namespace Shor
namespace Gate

/-! =========================================================
    Unsigned Phase-Product Workspace

    The unsigned macros reserve one clean bit next to each operand so they can
    reuse the signed phase-product semantics without changing the public gate.
========================================================= -/

/--
Workspace needed to implement an unsigned phase product via the signed phase-product gate.
The one-bit reserves hold the sign-extension bit for each operand, and the disjointness
fields make the generated macro local to `x`, `z`, and those reserves.
-/
structure PhaseProdWorkspace (x z : Reg) where
  xReserve : Reg
  zReserve : Reg

  x_can_grow : 1 ≤ Reg.width xReserve
  z_can_grow : 1 ≤ Reg.width zReserve

  xz_disjoint : Disjoint x z
  x_reserve_disjoint : Disjoint x xReserve
  z_reserve_disjoint : Disjoint z zReserve

  xReserve_not_z : Disjoint xReserve z
  zReserve_not_x : Disjoint zReserve x
  reserve_disjoint : Disjoint xReserve zReserve

namespace PhaseProdWorkspace

/-! =========================================================
    Workspace Views And Cleanliness
========================================================= -/

def xExt {x z : Reg} (ws : PhaseProdWorkspace x z) : ExtReg :=
  ExtReg.withReserve x ws.xReserve ws.x_reserve_disjoint

def zExt {x z : Reg} (ws : PhaseProdWorkspace x z) : ExtReg :=
  ExtReg.withReserve z ws.zReserve ws.z_reserve_disjoint

/-- The reserve bits used by the unsigned-to-signed bridge are initially zero. -/
def Clean
    {Basis : Type u}
    [RegEncoding Basis]
    {x z : Reg}
    (ws : PhaseProdWorkspace x z)
    (b : Basis) : Prop :=
  ws.xExt.FreshFor 1 b ∧
  ws.zExt.FreshFor 1 b

@[simp] theorem xExt_canGrow
    {x z : Reg}
    (ws : PhaseProdWorkspace x z) :
    ws.xExt.CanGrow 1 := by
  simpa [
    PhaseProdWorkspace.xExt,
    ExtReg.CanGrow,
    ExtReg.capacity
  ] using ws.x_can_grow

@[simp] theorem zExt_canGrow
    {x z : Reg}
    (ws : PhaseProdWorkspace x z) :
    ws.zExt.CanGrow 1 := by
  simpa [
    PhaseProdWorkspace.zExt,
    ExtReg.CanGrow,
    ExtReg.capacity
  ] using ws.z_can_grow

@[simp] theorem toNat_xExt
    {Basis : Type u}
    [RegEncoding Basis]
    {x z : Reg}
    (ws : PhaseProdWorkspace x z)
    (b : Basis) :
    ExtReg.toNat ws.xExt b =
      RegEncoding.toNat x b := by
  rfl

@[simp] theorem toNat_zExt
    {Basis : Type u}
    [RegEncoding Basis]
    {x z : Reg}
    (ws : PhaseProdWorkspace x z)
    (b : Basis) :
    ExtReg.toNat ws.zExt b =
      RegEncoding.toNat z b := by
  rfl



/-- The controlled bridge may read `ctrl`; this predicate keeps it outside all touched qubits. -/
def ControlDisjoint
    {x z : Reg}
    (ws : PhaseProdWorkspace x z)
    (ctrl : ℕ) : Prop :=
  ctrl ∉ x.qubits ∧
  ctrl ∉ z.qubits ∧
  ctrl ∉ ws.xReserve.qubits ∧
  ctrl ∉ ws.zReserve.qubits
end PhaseProdWorkspace

/-! =========================================================
    Macro Gate Definitions

    These are implementation-only circuit macros; the public lowering theorems
    later prove that they realize the asserted phase-product behavior.
========================================================= -/

/--
Unsigned phase product macro: allocate one clean high bit on each operand, run the signed
phase product on the grown registers, and then deallocate the temporary bits.
-/
def PhaseProdUsing
    (phi : ℝ)
    (x z : Reg)
    (ws : PhaseProdWorkspace x z) : Gate :=
  let xext := ws.xExt
  let zext := ws.zExt

  Gate.zeroExtend xext 1 ;;
  Gate.zeroExtend zext 1 ;;
  Gate.SignedPhaseProd phi
    (xext.grow 1)
    (zext.grow 1) ;;
  Gate.zeroDealloc zext 1 ;;
  Gate.zeroDealloc xext 1

/-- Controlled unsigned phase-product macro with the same workspace discipline as `PhaseProdUsing`. -/
def CPhaseProdUsing
    (ctrl : ℕ) (phi : ℝ)
    (x z : Reg)
    (ws : PhaseProdWorkspace x z) :
    Gate :=
  let xext := ws.xExt
  let zext := ws.zExt

  Gate.zeroExtend xext 1 ;;
  Gate.zeroExtend zext 1 ;;
  Gate.CSignedPhaseProd
    ctrl
    phi
    (xext.grow 1)
    (zext.grow 1) ;;
  Gate.zeroDealloc zext 1 ;;
  Gate.zeroDealloc xext 1


end Gate
end Shor
