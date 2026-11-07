import ForShor.ShorVerification.Framework.Gatecount.CostModel

namespace Shor
/-! =========================================================
    Concrete Shor cost model

This section gives the numerical costs assigned to arithmetic primitives and
packages them into the concrete model used throughout the gate-count proofs.
The arithmetic primitives are charged under stated conventions, not proved
decompositions: adders and negation follow published circuits, shifts and
sign handling are charged as wiring, and radix reversal as `m/2` swaps. The
asymptotic results only need linear arithmetic costs and quadratic direct
PhaseProduct base cases.
========================================================= -/

section ConcreteCostModel

/-- Conservative linear bound for one ripple-adder on `w` qubits. -/
def rippleAdderGateBound (w : ℕ) : ℕ := 9 * w + 2

/-- Negation is bounded by the complement plus the one-ancilla increment: at most `34 w + 1`
gates in all (swap 001; see `negateResources`). -/
def negateGateBound (r : ExtReg) : ℕ := 34 * ExtReg.width r + 1

/-- Direct signed PhaseProduct base-case cost, quadratic in the operand widths. -/
def directSignedPhaseProductGateCount (x z : ExtReg) : ℕ := 5 * ExtReg.width x * ExtReg.width z

/-- Cost assigned to the final radix-reversal swaps for a register split. -/
def radixReverseGateCount (_r : Reg) (m : ℕ) : ℕ := 3 * (m / 2)

end ConcreteCostModel

/-- Concrete logical resources used by a lowered circuit.

`cleanAnc` is a peak-space quantity rather than a gate count, so sequential
composition takes the maximum rather than the sum. -/
structure GateResources where
  h : ℕ := 0
  x : ℕ := 0
  cnot : ℕ := 0
  toffoli : ℕ := 0
  rz : ℕ := 0
  cleanAnc : ℕ := 0
deriving Repr, DecidableEq

namespace GateResources

def zero : GateResources := {}

def seq (a b : GateResources) : GateResources where
  h := a.h + b.h
  x := a.x + b.x
  cnot := a.cnot + b.cnot
  toffoli := a.toffoli + b.toffoli
  rz := a.rz + b.rz
  cleanAnc := max a.cleanAnc b.cleanAnc

/-- Total number of logical unitary gates when every elementary gate has
unit cost.  Ancilla usage is intentionally not included. -/
def totalGates (r : GateResources) : ℕ :=
  r.h + r.x + r.cnot + r.toffoli + r.rz

end GateResources

/-- Structural resource model for low-level gates.

Unlike `LowGateCostModel`, this records the decomposition into logical
elementary resources instead of immediately collapsing everything to a Nat. -/
structure LowGateResourceModel where
  shiftL : ExtReg → ℕ → GateResources
  shiftR : ExtReg → ℕ → GateResources
  negate : ExtReg → GateResources
  addScaled : ExtReg → ExtReg → Bool → ℕ → GateResources
  zeroExtend : ExtReg → ℕ → GateResources
  signExtend : ExtReg → ℕ → GateResources
  zeroDealloc : ExtReg → ℕ → GateResources
  signDealloc : ExtReg → ℕ → GateResources
  radixReverse : Reg → ℕ → GateResources

namespace LowGate

def resources (M : LowGateResourceModel) : LowGate → GateResources
  | .id => {}
  | .seq U V => GateResources.seq (resources M U) (resources M V)
  | .adj U => resources M U
  | .H _ => { h := 1 }
  | .X _ => { x := 1 }
  | .ShiftL r n => M.shiftL r n
  | .ShiftR r n => M.shiftR r n
  | .Negate r => M.negate r
  | .AddScaled dst src negSrc shift =>
      M.addScaled dst src negSrc shift
  | .Phase _ _ => { rz := 1 }
  | .CNOT _ _ => { cnot := 1 }
  | .Toffoli _ _ _ => { toffoli := 1 }
  | .zeroExtend r n => M.zeroExtend r n
  | .signExtend r n => M.signExtend r n
  | .zeroDealloc r n => M.zeroDealloc r n
  | .signDealloc r n => M.signDealloc r n
  | .RadixReverse r m => M.radixReverse r m

end LowGate

namespace LowGateResourceModel

def toCostModel (M : LowGateResourceModel) : LowGateCostModel where

  shiftL := fun r n =>
    (M.shiftL r n).totalGates

  shiftR := fun r n =>
    (M.shiftR r n).totalGates

  negate := fun r =>
    (M.negate r).totalGates

  addScaled := fun dst src negSrc shift =>
    (M.addScaled dst src negSrc shift).totalGates

  zeroExtend := fun r n =>
    (M.zeroExtend r n).totalGates

  signExtend := fun r n =>
    (M.signExtend r n).totalGates

  zeroDealloc := fun r n =>
    (M.zeroDealloc r n).totalGates

  signDealloc := fun r n =>
    (M.signDealloc r n).totalGates

  radixReverse := fun r m =>
    (M.radixReverse r m).totalGates

end LowGateResourceModel

/-! =========================================================
    Concrete structural resource model

The model below counts logical unitary resources in the basis

    H, X, CNOT, Toffoli, Rz

plus peak clean scratch ancillas.

Important convention:
`cleanAnc` counts temporary scratch qubits required by the implementation,
not qubits already owned by an `ExtReg` reserve.

The adder and negation formulas follow published circuits; shifts are
charged as wiring and radix reversal as `m/2` swaps, by convention rather than
by a proved decomposition. None is a free constant chosen only to obtain the
desired asymptotics.
========================================================= -/

section ConcreteResourceModel

/-! ---------------------------------------------------------
    Cuccaro ripple-carry arithmetic

Primary source:
  Steven A. Cuccaro, Thomas G. Draper, Samuel A. Kutin,
  David Petrie Moulton,
  "A new quantum ripple-carry addition circuit"
  https://arxiv.org/abs/quant-ph/0410184

Section 4.1, "Addition Modulo 2^n", states that for n ≥ 3
the circuit contains exactly:

  Toffoli   = 2n - 3
  CNOT      = 5n - 7
  negations = 2n - 6
  ancillas  = 1

The paper constructs the circuit entirely from negations, CNOTs,
and Toffoli gates, so the H and Rz counts are zero.

Here each negation is counted as one X gate.

Reference:
  https://arxiv.org/html/quant-ph/0410184v1#S4.SS1
--------------------------------------------------------- -/

/-- Exact resource count of the Cuccaro modulo-`2^w` ripple-carry
adder, as stated in Sec. 4.1 of Cuccaro et al.

This published formula applies for `w ≥ 3`. -/
def cuccaroModAddResources (w : ℕ) : GateResources where
  h := 0
  x := 2 * w - 6
  cnot := 5 * w - 7
  toffoli := 2 * w - 3
  rz := 0
  cleanAnc := 1

/-! ---------------------------------------------------------
    Negation

Two's-complement negation is

    -x = (~x) + 1  (mod 2^w).

We therefore apply X to all `w` data qubits and then increment the register
in place, with a single ancilla and no scratch register.

MODULAR SWAP 001 (2026-11-05, counts corrected 2026-11-06). This replaces the
earlier construction (a clean `w`-bit constant-one register plus a Cuccaro
modulo adder: `2w - 3` Toffolis, `w + 1` clean qubits). The increment is
Gidney's single-ancilla increment gate:
  Craig Gidney, "Constructing Large Increment Gates", 2015,
  https://algassert.com/circuits/2015/06/12/Constructing-Large-Increment-Gates.html
It needs ONE extra qubit, which may be in any state (it is borrowed and returned),
and borrows everything else from the register's own bits. We charge it as one
clean qubit, which is valid and conservative.

The gate counts are those of an explicit NOT/CNOT/Toffoli circuit built from
the post's construction and simulated classically (every input and both ancilla
values for `w <= 12`; random and long-carry inputs up to `w = 4398`; the ancilla
is always returned), then counted. They are exact for every `w >= 7` (checked
for each `w` from 7 to 1600 and at 2048, 2049, 4096 and 4398):

                      w even          w odd
    Toffoli           12 w - 28       10 w - 18
    CNOT              17 w - 22       17 w - 5
    X (with the       5 w - 3         5 w + 1
       complement)

and valid upper bounds below `w = 7`. (The post's "32 n" is the total of
Toffoli, CNOT and NOT gates, not of Toffolis: a negation here has `34 w`.)
That circuit is not built in Lean. Like every primitive here, the counts are a
stated convention, not a proved decomposition: they say that a circuit of this
shape exists, which a Python/Qualtran build (outside this repository) checks.
Alternatives recorded in `ForShor_modular_swaps/swap-001_negation_incrementer`.
--------------------------------------------------------- -/

/-- X gates of a `w`-bit negation: the `w` complement NOTs plus the increment's. -/
def negateXGates (w : ℕ) : ℕ := if w % 2 = 0 then 5 * w - 3 else 5 * w + 1

/-- CNOT gates of a `w`-bit negation. -/
def negateCnotGates (w : ℕ) : ℕ := if w % 2 = 0 then 17 * w - 22 else 17 * w - 5

/-- Toffoli gates of a `w`-bit negation. -/
def negateToffoliGates (w : ℕ) : ℕ := if w % 2 = 0 then 12 * w - 28 else 10 * w - 18

def negateResources (r : ExtReg) : GateResources :=
  let w := ExtReg.width r
  { x := negateXGates w
    cnot := negateCnotGates w
    toffoli := negateToffoliGates w
    cleanAnc := 1 }

theorem negateXGates_le (w : ℕ) : negateXGates w ≤ 5 * w + 1 := by
  unfold negateXGates; split_ifs <;> omega

theorem negateCnotGates_le (w : ℕ) : negateCnotGates w ≤ 17 * w := by
  unfold negateCnotGates; split_ifs <;> omega

theorem negateToffoliGates_le (w : ℕ) : negateToffoliGates w ≤ 12 * w := by
  unfold negateToffoliGates; split_ifs <;> omega

/-! ---------------------------------------------------------
    AddScaled

The multiplication paper forms Toom-Cook linear combinations using
ordinary in-place additions/subtractions and treats powers-of-two
coefficients as logical shifts.

Gregory Kahanamoku-Meyer, Norman Yao,
"Fast quantum integer multiplication with zero ancillas"
  https://arxiv.org/abs/2403.18006

For the concrete adder implementation we use the Cuccaro modulo adder:
  https://arxiv.org/abs/quant-ph/0410184

`negSrc = true` does not need a different gate count: subtraction is
the inverse of the corresponding reversible addition circuit.

The `shift` is treated as a logical wiring offset, following the
multiplication paper's convention.
--------------------------------------------------------- -/

def addScaledResources
    (dst _src : ExtReg) (_negSrc : Bool) (_shift : ℕ) :
    GateResources :=
  cuccaroModAddResources (ExtReg.width dst)

/-! ---------------------------------------------------------
    Radix reversal

Charged as `floor(m/2)` pairwise SWAPs, by convention:
`floor(m/2)` SWAP = `3 * floor(m/2)` CNOT.
--------------------------------------------------------- -/

def radixReverseResources (_r : Reg) (m : ℕ) : GateResources :=
  {
    cnot := 3 * (m / 2)
  }

/-! ---------------------------------------------------------
    Concrete Shor resource model
--------------------------------------------------------- -/

/-- Concrete structural resource model used for the Shor lowering.

Each field is backed either by an explicit published circuit or by the
logical-wiring convention of the multiplication construction.
-/
def shorGateResourceModel : LowGateResourceModel where
  shiftL := fun _ _ => {}

  shiftR := fun _ _ => {}

  negate := negateResources

  addScaled := addScaledResources

  zeroExtend := fun _ _ => {}

  signExtend := fun _ n => {
    cnot := n
  }

  zeroDealloc := fun _ _ => {}

  signDealloc := fun _ n => {
    cnot := n
  }

  radixReverse := radixReverseResources

/-- Concrete scalar gate-count model obtained by forgetting the
    resource decomposition of `shorGateResourceModel`. -/
def shorGateCostModel : LowGateCostModel :=
  shorGateResourceModel.toCostModel

end ConcreteResourceModel

/-! =========================================================
    Qubit count
========================================================= -/

/-- Physical qubits owned by an ordinary register. -/
def regQubitSet (r : Reg) : Finset ℕ :=
  r.qubits.toFinset

def extRegActiveQubits (r : ExtReg) : Finset ℕ :=
  r.active.qubits.toFinset

def extRegGrowQubits (r : ExtReg) (n : ℕ) : Finset ℕ :=
  (r.grow n).active.qubits.toFinset

def LowGate.usedQubits : LowGate → Finset ℕ
  | .id => ∅
  | .seq U V =>
      usedQubits U ∪ usedQubits V
  | .adj U =>
      usedQubits U
  | .H q => {q}
  | .X q => {q}
  | .ShiftL r _ =>
      extRegActiveQubits r
  | .ShiftR r _ =>
      extRegActiveQubits r
  | .Negate r =>
      extRegActiveQubits r
  | .AddScaled dst src _ _ =>
      extRegActiveQubits dst ∪ extRegActiveQubits src
  | .Phase q _ => {q}
  | .CNOT ctrl target =>
      {ctrl, target}
  | .Toffoli c₁ c₂ target =>
      {c₁, c₂, target}
  | .zeroExtend r n =>
      extRegGrowQubits r n
  | .signExtend r n =>
      extRegGrowQubits r n
  | .zeroDealloc _ _ =>
      ∅
  | .signDealloc r _ =>
      r.active.qubits.toFinset
  | .RadixReverse r _ =>
      r.qubits.toFinset

/--
Total physical qubit requirement of a lowered circuit:

* all distinct qubits explicitly owned/referenced by the circuit;
* peak additional clean scratch ancillas required by its implementation.
-/
def LowGate.qubitCount
    (M : LowGateResourceModel)
    (g : LowGate) : ℕ :=
  (usedQubits g).card + (resources M g).cleanAnc

/-! ## Counting lemmas for `LowGate.gateCount` -/

namespace LowGate

/-- The identity gate contributes no cost. -/
@[simp]
theorem gateCount_id_eq (M : LowGateCostModel) :
    gateCount M .id = 0 := rfl

/-- Sequential composition contributes the sum of the component costs. -/
@[simp]
theorem gateCount_seq_eq (M : LowGateCostModel) (U V : LowGate) :
    gateCount M (U ;; V) = gateCount M U + gateCount M V := rfl

/-- Taking adjoints preserves the gate count. -/
@[simp]
theorem gateCount_adj_eq (M : LowGateCostModel) (U : LowGate) :
    gateCount M (†U) = gateCount M U := rfl

/-- A Hadamard is counted as one primitive low-level gate. -/
@[simp]
theorem gateCount_H_eq (M : LowGateCostModel) (q : ℕ) :
    gateCount M (.H q) = 1 := rfl

/-- An `X` gate is counted as one primitive low-level gate. -/
@[simp]
theorem gateCount_X_eq (M : LowGateCostModel) (q : ℕ) :
    gateCount M (.X q) = 1 := rfl

end LowGate

end Shor
