import FastMultiplication.ShorVerification.Framework.AbstractMachine.LowGate

/-!
# Framework — LowGate cost model

The abstract cost model for lowered circuits, the `LowGate → ℕ` evaluator,
and the concrete Shor cost instance. Program-independent: it depends only on
the `LowGate` language, not on any lowering or construction.
-/

namespace Shor

/-! =========================================================
    Low-gate cost interface

This section defines the abstract cost model for lowered circuits and the
single evaluator that interprets a `LowGate` syntax tree as a natural-number
cost.  Later sections instantiate the model with the concrete Shor costs used
in the asymptotic bounds.
========================================================= -/

section LowGateCostModel

/-- A table of costs for each primitive low-level gate family.  Sequencing,
adjoint, and elementary one-qubit gates are handled uniformly by `gateCount`; the
fields here are exactly the operations whose costs depend on registers, payloads,
or the concrete arithmetic model. -/
structure LowGateCostModel where
  prim : String → List ℕ → ℕ
  shiftL : ExtReg → ℕ → ℕ
  shiftR : ExtReg → ℕ → ℕ
  negate : ExtReg → ℕ
  addScaled : ExtReg → ExtReg → Bool → ℕ → ℕ
  zeroExtend : ExtReg → ℕ → ℕ
  signExtend : ExtReg → ℕ → ℕ
  zeroDealloc : ExtReg → ℕ → ℕ
  signDealloc : ExtReg → ℕ → ℕ
  radixReverse : Reg → ℕ → ℕ

namespace LowGate

/-- Evaluate a lowered gate tree against a cost model.  Structural gates add or
preserve cost, elementary `H`/`X` gates cost one, and model-dependent operations
are delegated to `LowGateCostModel`. -/
def gateCount (M : LowGateCostModel) : LowGate → ℕ
  | .id => 0
  | .seq U V => gateCount M U + gateCount M V
  | .adj U => gateCount M U
  | .H _ => 1
  | .X _ => 1
  | .Prim tag qs => M.prim tag qs
  | .ShiftL r n => M.shiftL r n
  | .ShiftR r n => M.shiftR r n
  | .Negate r => M.negate r
  | .AddScaled dst src negSrc shift => M.addScaled dst src negSrc shift
  | .Phase _ _ => 1
  | .CNOT _ _ => 1
  | .Toffoli _ _ _ => 1
  | .zeroExtend r n => M.zeroExtend r n
  | .signExtend r n => M.signExtend r n
  | .zeroDealloc r n => M.zeroDealloc r n
  | .signDealloc r n => M.signDealloc r n
  | .RadixReverse r m => M.radixReverse r m

end LowGate
end LowGateCostModel

/-! =========================================================
    Concrete Shor cost model

This section gives the numerical costs assigned to arithmetic primitives and
packages them into the concrete model used throughout the gate-count proofs.
The constants are intentionally conservative; the later asymptotic results only
need linear arithmetic costs and quadratic direct PhaseProduct base cases.
========================================================= -/

section ConcreteCostModel

/-- Conservative linear bound for one ripple-adder on `w` qubits. -/
def rippleAdderGateBound (w : ℕ) : ℕ := 9 * w + 2

/-- Negation is bounded by sign-width handling plus one ripple-adder. -/
def negateGateBound (r : ExtReg) : ℕ := ExtReg.width r + rippleAdderGateBound (ExtReg.width r)

/-- Direct signed PhaseProduct base-case cost, quadratic in the operand widths. -/
def directSignedPhaseProductGateCount (x z : ExtReg) : ℕ := ExtReg.width x * ExtReg.width z

/-- Direct controlled signed PhaseProduct base-case cost, with a constant-factor
controlled overhead over the signed direct implementation. -/
def directCSignedPhaseProductGateCount (x z : ExtReg) : ℕ := 5 * ExtReg.width x * ExtReg.width z

/-- Cost assigned to the final radix-reversal swaps for a register split. -/
def radixReverseGateCount (_r : Reg) (m : ℕ) : ℕ := 3 * (m / 2)

/-- Build a PhaseProduct-oriented cost model from a primitive-cost table.  Shifts
and allocation bookkeeping default to zero cost, arithmetic operations are
linear, and direct signed PhaseProduct gates are quadratic base cases. -/
def phaseProductCostModel
    (primCost : String → List ℕ → ℕ)
    (shiftLCost : ExtReg → ℕ → ℕ := fun _ _ => 0)
    (shiftRCost : ExtReg → ℕ → ℕ := fun _ _ => 0) : LowGateCostModel where
  prim := primCost
  shiftL := shiftLCost
  shiftR := shiftRCost
  negate := negateGateBound
  addScaled := fun dst _src _negSrc _shift => rippleAdderGateBound (ExtReg.width dst)
  zeroExtend := fun _r _n => 0
  signExtend := fun _r _n => 0
  zeroDealloc := fun _r _n => 0
  signDealloc := fun _r _n => 0
  radixReverse := radixReverseGateCount

/-- Conservative linear elementary-gate bound for an opaque reversible arithmetic
primitive acting on `w` qubits. -/
def linearPrimitiveGateBound (w : ℕ) : ℕ := 20 * w + 10

/-- Concrete costs for the opaque arithmetic primitives used by the Shor circuit.
Recognized payloads use their register widths; malformed or unknown payloads are
assigned cost one as a defensive fallback. -/
def shorPrimCost (tag : String) (args : List ℕ) : ℕ :=
  if tag = "CMP_GE_CONST" ∨
      tag = "CSUB_CONST" ∨
      tag = "CMP_LT_NW" then
    linearPrimitiveGateBound (args.length - 2)
  else
    1

/-- Concrete gate-cost model used by all Shor gate-count developments. -/
def shorGateCostModel : LowGateCostModel := phaseProductCostModel shorPrimCost

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
  prim : String → List ℕ → GateResources
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
  | .Prim tag qs => M.prim tag qs
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
  prim := fun tag qs =>
    (M.prim tag qs).totalGates

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

The numerical formulas are concrete circuit upper bounds, rather than
free constants chosen only to obtain the desired asymptotics.
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
    Ordinary comparator

Sources:

Cuccaro et al.:
  https://arxiv.org/abs/quant-ph/0410184

Table 1 gives for the high-bit/comparator construction:
  Toffoli = 2n - 1
  CNOT    = 4n - 3

Cuccaro explicitly notes that negations are omitted from the table's
size metric.

Remaud gives the comparator circuit with an X layer on every bit of
one operand before the comparison and the inverse X layer afterwards:
  Maxime Remaud,
  "Optimizing T and CNOT Gates in Quantum Ripple-Carry
   Adders and Comparators"
  https://arxiv.org/abs/2401.17921

Thus we count:
  X       = 2n
  CNOT    = 4n - 3
  Toffoli = 2n - 1
--------------------------------------------------------- -/

/-- Cuccaro ripple-carry comparison of two `w`-bit quantum integers. -/
def comparatorResources (w : ℕ) : GateResources :=
  if 3 ≤ w then
    {
      h := 0
      x := 2 * w
      cnot := 4 * w - 3
      toffoli := 2 * w - 1
      rz := 0
      cleanAnc := 1
    }
  else
    {
      h := 0
      x := 2 * w
      cnot := 4 * w
      toffoli := 2 * w
      rz := 0
      cleanAnc := 1
    }


/-! ---------------------------------------------------------
    Comparison against a classical constant

Concrete construction used here:

  1. Allocate a clean `w`-qubit register.
  2. Write the classical constant into it with X gates.
  3. Run `comparatorResources`.
  4. Erase the classical constant.

At most `w` X gates are needed to write the constant, and at most
`w` to erase it.

The comparator itself is the Cuccaro construction:
  https://arxiv.org/abs/quant-ph/0410184

A lower-ancilla alternative is given by Khattar--Gidney, who obtain
a linear 3n-Toffoli quantum/classical comparator:
  https://arxiv.org/abs/2407.17966

We use the Cuccaro-derived version because it gives explicit counts in
our X/CNOT/Toffoli basis instead of only a Toffoli metric.
--------------------------------------------------------- -/

def cmpGeConstResources (w : ℕ) : GateResources :=
  let c := comparatorResources w
  {
    h := c.h
    x := c.x + 2 * w
    cnot := c.cnot
    toffoli := c.toffoli
    rz := c.rz
    cleanAnc := w + c.cleanAnc
  }


/-! ---------------------------------------------------------
    Controlled subtraction of a classical constant

Concrete construction:

  1. Allocate a clean `w`-bit temporary register.
  2. Controlled on `flag`, write the classical constant N into it.
     This needs at most `w` CNOTs.
  3. Run the inverse Cuccaro modulo adder.
  4. Erase the temporary constant using at most `w` CNOTs.

The inverse of a reversible adder has exactly the same resource count.

Adder source:
  https://arxiv.org/abs/quant-ph/0410184
--------------------------------------------------------- -/

def csubConstResources (w : ℕ) : GateResources :=
  let a := cuccaroModAddResources w
  {
    h := a.h
    x := a.x
    cnot := a.cnot + 2 * w
    toffoli := a.toffoli
    rz := a.rz
    cleanAnc := w + a.cleanAnc
  }


/-! ---------------------------------------------------------
    CMP_LT_NW

The current `Prim` encoding erases the boundary between the `data`
and `work` registers:

    [N, flag] ++ data.qubits ++ work.qubits

so this function only knows their combined width `w`.

Until `Prim` is made typed, use a conservative explicit schoolbook
upper bound:

  * allocate a `w`-bit product accumulator;
  * for at most `w` work bits, controlled-add a shifted N;
  * compare against the shifted data value;
  * uncompute the product.

Each controlled constant add is implemented by controlled-loading a
temporary constant followed by a Cuccaro modulo adder.

Adder/comparator source:
  https://arxiv.org/abs/quant-ph/0410184

The standard schoolbook multiply-as-controlled-additions construction
is also discussed in:
  Daniel Litinski,
  "Quantum schoolbook multiplication with fewer Toffoli gates"
  https://arxiv.org/abs/2410.00899

This is deliberately conservative and quadratic.  It should eventually
be replaced by a typed primitive carrying separate `data` and `work`
register widths.
--------------------------------------------------------- -/

def cmpLtNWResources (w : ℕ) : GateResources :=
  {
    h := 0

    /-
    Compute + uncompute at most `w` controlled additions:
      ≤ 2w * (2w X)
    plus one `w`-bit comparator:
      ≤ 2w X.
    -/
    x := 4 * w * w + 2 * w

    /-
    Controlled addition:
      ≤ 2w CNOT to materialize/unmaterialize the constant
      + 5w CNOT for Cuccaro
      = 7w.

    Compute + uncompute:
      ≤ 14w².

    Materialize/unmaterialize shifted data + comparator:
      ≤ 2w + 4w = 6w.
    -/
    cnot := 14 * w * w + 6 * w

    /-
    Compute + uncompute:
      ≤ 2w * (2w Toffoli) = 4w²
    comparator:
      ≤ 2w.
    -/
    toffoli := 4 * w * w + 2 * w

    rz := 0

    /-
    Product accumulator + reusable temporary operand + ripple carry.
    -/
    cleanAnc := 2 * w + 1
  }


/-! ---------------------------------------------------------
    Primitive resources
--------------------------------------------------------- -/

def shorPrimResources (tag : String) (args : List ℕ) : GateResources :=
  let w := args.length - 2
  if tag = "CMP_GE_CONST" then
    cmpGeConstResources w
  else if tag = "CSUB_CONST" then
    csubConstResources w
  else if tag = "CMP_LT_NW" then
    cmpLtNWResources w
  else
    /-
    This is a sentinel, NOT a claimed resource upper bound for an
    arbitrary unknown primitive.

    The Shor development should separately prove that every reachable
    `Prim` tag is one of the three cases above.  Long term, `Prim`
    should be replaced by a typed inductive datatype.
    -/
    { toffoli := 1 }


/-! ---------------------------------------------------------
    Negation

Two's-complement negation is

    -x = (~x) + 1  (mod 2^w).

We therefore:
  * apply X to all `w` data qubits;
  * prepare a clean `w`-bit register containing 1;
  * apply a Cuccaro modulo adder;
  * erase the constant-one register.

Cuccaro adder:
  https://arxiv.org/abs/quant-ph/0410184

Khattar--Gidney independently give a linear-size dedicated incrementer:
  https://arxiv.org/abs/2407.17966

The version below is intentionally the simpler directly-auditable
Cuccaro construction.
--------------------------------------------------------- -/

def negateResources (r : ExtReg) : GateResources :=
  let w := ExtReg.width r
  let a := cuccaroModAddResources w
  {
    h := a.h
    -- `w` X gates for bitwise complement; 2 more to prepare/erase |1⟩.
    x := w + a.x + 2
    cnot := a.cnot
    toffoli := a.toffoli
    rz := a.rz

    -- `w` clean bits for the constant-one register + Cuccaro carry.
    cleanAnc := w + a.cleanAnc
  }


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
    Direct signed PhaseProduct

Kahanamoku-Meyer--Yao use the schoolbook base case with one singly
controlled phase rotation for each input-bit pair:
  https://arxiv.org/abs/2403.18006

Therefore, for operand widths a,b there are a*b controlled phases.

A controlled one-qubit unitary can be decomposed using two CNOTs and
single-qubit gates; see Barenco et al.:
  https://arxiv.org/abs/quant-ph/9503016

Specializing to a diagonal controlled phase gives, up to global phase:

    CP(θ) =
      Rz(...) -- CNOT -- Rz(...) -- CNOT -- Rz(...)

so we count each bit pair as:
    2 CNOT + 3 Rz.

Signed two's-complement coefficients only change rotation angles,
not the number of gates.
--------------------------------------------------------- -/

def directSignedPhaseProductResources
    (x z : ExtReg) : GateResources :=
  let pairs := ExtReg.width x * ExtReg.width z
  {
    cnot := 2 * pairs
    rz := 3 * pairs
  }


/-! ---------------------------------------------------------
    Direct controlled signed PhaseProduct

For each bit pair we need a phase conditioned on

    ctrl ∧ xᵢ ∧ zⱼ.

Use one reusable clean ancilla:

    Toffoli(xᵢ,zⱼ -> anc)
    ControlledPhase(ctrl,anc,θ)
    Toffoli(xᵢ,zⱼ -> anc)

The middle controlled phase is decomposed as above into
2 CNOT + 3 Rz.

Thus every bit pair contributes:
    2 Toffoli + 2 CNOT + 3 Rz.

--------------------------------------------------------- -/

def directCSignedPhaseProductResources
    (x z : ExtReg) : GateResources :=
  let pairs := ExtReg.width x * ExtReg.width z
  {
    h := 0
    x := 0
    cnot := 2 * pairs
    toffoli := 2 * pairs
    rz := 5 * pairs
    cleanAnc := 0
  }

/-! ---------------------------------------------------------
    Radix reversal

We retain the existing implementation as `floor(m/2)` pairwise SWAPs.

 floor(m/2) SWAP = 3 * floor(m/2) CNOT.
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
  prim := shorPrimResources

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

def LowGate.usedQubits
    (primQubits : String → List ℕ → Finset ℕ) :
    LowGate → Finset ℕ
  | .id => ∅
  | .seq U V =>
      usedQubits primQubits U ∪ usedQubits primQubits V
  | .adj U =>
      usedQubits primQubits U

  | .H q => {q}
  | .X q => {q}

  | .Prim tag qs =>
      primQubits tag qs

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
    (primQubits : String → List ℕ → Finset ℕ)
    (g : LowGate) : ℕ :=
  (usedQubits primQubits g).card + (resources M g).cleanAnc


end Shor
