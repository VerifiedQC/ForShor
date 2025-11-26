import FastMultiplication.one_reg_synth_proof_2

/-
############################################################
## Qubit-level model and state-level operations
############################################################
-/

namespace Qubits

/-- Abstract type of a single qubit. -/
axiom Qubit : Type

/-- An arbitrarily large qubit reg indexed by ℕ. -/
abbrev QReg := ℕ → Qubit

/-- A logical register: a QReg + a shift + a used range. -/
structure Register where
  qreg  : QReg
  shift : ℕ
  used  : ℕ

/-- A state of `k` qubit-registers. -/
def State (k : ℕ) := Fin k → Register

/-- Abstract qubit-level addition on QRegs. -/
axiom addQReg : QReg → QReg → QReg   --QReg → ℕ → QReg → ℕ → QReg

/-- Abstract qubit-level negation on tapes. -/
axiom negateQReg : QReg → QReg

/-- Low-level adder on *windows* of the destination and source registers. -/
noncomputable def add (dst : Register) (dst_ran : ℕ × ℕ)
    (src : Register) (src_ran : ℕ × ℕ) : Register :=
  let (d1, d2) := dst_ran  -- range of destination qubits used
  let (s1, s2) := src_ran  -- range of source qubits used
  { qreg  := addQReg dst.qreg src.qreg
  , shift := dst.shift
  , used  := (Nat.max d2 s2 + 1) - (Nat.min d1 s1) -- d1 + Nat.max dlen slen + 1
  }

/-- Logical range of the *used* bits of a register:
    indices `[shift, shift + used)`. -/
def logicalRange (r : Register) : ℕ × ℕ :=
  (r.shift, r.shift + r.used)

/-- Logical range of the used bits if the register were additionally shifted left
    by `sh` bits: indices `[shift + sh, shift + sh + used)`. -/
def shiftedRange (r : Register) (sh : ℕ) : ℕ × ℕ :=
  (r.shift + sh, r.shift + sh + r.used)

/-- Scaled addition on single registers: conceptually `dst ← dst + (src << sh)`. -/
noncomputable def add_Scaled (dst src : Register) (sh : ℕ) : Register :=
  add dst (logicalRange dst) src (shiftedRange src sh)

/-- Logical left shift by `n` bits: multiply by `2^n`. -/
def shiftL (r : Register) (n : ℕ) : Register :=
  { r with shift := r.shift + n }

/-- Logical right shift by `n` bits: divide by `2^n` (truncating). -/
def shiftR (r : Register) (n : ℕ) : Register :=
  { r with shift := r.shift - n }

/-- Logical negation of a register: conceptually multiply by `-1`. -/
noncomputable def negate (r : Register) : Register :=
  { r with qreg := negateQReg r.qreg }

@[simp] lemma shiftL_qreg (r : Register) (n : ℕ) :
    (shiftL r n).qreg = r.qreg := rfl

@[simp] lemma shiftL_used (r : Register) (n : ℕ) :
    (shiftL r n).used = r.used := rfl

@[simp] lemma shiftL_shift (r : Register) (n : ℕ) :
    (shiftL r n).shift = r.shift + n := rfl

@[simp] lemma shiftR_qreg (r : Register) (n : ℕ) :
    (shiftR r n).qreg = r.qreg := rfl

@[simp] lemma shiftR_used (r : Register) (n : ℕ) :
    (shiftR r n).used = r.used := rfl

@[simp] lemma shiftR_shift (r : Register) (n : ℕ) :
    (shiftR r n).shift = r.shift - n := rfl


/-! ## State-level operations -/

namespace StateOps

/-- Overwrite register `i` in the state. -/
def setReg {k : ℕ} (σ : State k) (i : Fin k) (r : Register) : State k :=
  fun j => if h : j = i then (Eq.rec r h.symm) else σ j

@[simp] lemma setReg_self {k : ℕ} (σ : State k) (i : Fin k) (r : Register) :
    setReg σ i r i = r := by
  simp [setReg]

@[simp] lemma setReg_other {k : ℕ} (σ : State k) (i j : Fin k) (r : Register)
    (h : j ≠ i) :
    setReg σ i r j = σ j := by
  simp [setReg, h]

/-- Logical left shift of register `i` in the state by `n` bits. -/
def shiftLReg {k : ℕ} (σ : State k) (i : Fin k) (n : ℕ) : State k :=
  setReg σ i (shiftL (σ i) n)

/-- Logical right shift of register `i` in the state by `n` bits. -/
def shiftRReg {k : ℕ} (σ : State k) (i : Fin k) (n : ℕ) : State k :=
  setReg σ i (shiftR (σ i) n)

/-- Negate register `i` in the state. -/
noncomputable def negateReg {k : ℕ} (σ : State k) (i : Fin k) : State k :=
  setReg σ i (negate (σ i))

/-- **State-level windowed add**:
    apply the low-level `add` to registers `dst` and `src` using
    explicit ranges, and update only `dst` in the state. -/
noncomputable def addReg {k : ℕ} (σ : State k)
    (dst src : Fin k) (dst_ran src_ran : ℕ × ℕ) : State k :=
  setReg σ dst (add (σ dst) dst_ran (σ src) src_ran)

/-- Convenience: state-level scaled add defined via windowed add. -/
noncomputable def addScaledReg {k : ℕ} (σ : State k)
    (dst src : Fin k) (sh : ℕ) : State k :=
  let dst_ran := logicalRange (σ dst)
  let src_ran := shiftedRange (σ src) sh
  addReg σ dst src dst_ran src_ran

end StateOps


/-! ## Inductive valid operations and programs -/

open StateOps

/-- Valid qubit-level operations on a `State k`.

We now base `add` directly on the low-level windowed `add`:
it carries explicit destination and source ranges. -/
inductive valid_operation (k : ℕ) where
  | shiftL    (i : Fin k) (n : ℕ)
  | shiftR    (i : Fin k) (n : ℕ)
  | negate    (i : Fin k)
  | add       (dst src : Fin k) (dst_ran src_ran : ℕ × ℕ)
  | phaseProduct (i : Fin k)
deriving Repr

/-- Semantics of a single `valid_operation` on a state. -/
noncomputable def apply {k : ℕ} (op : valid_operation k) (σ : State k) : State k :=
  match op with
  | valid_operation.shiftL i n            => shiftLReg σ i n
  | valid_operation.shiftR i n            => shiftRReg σ i n
  | valid_operation.negate i              => negateReg σ i
  | valid_operation.add dst src dr sr     => addReg σ dst src dr sr
  | valid_operation.phaseProduct _        => σ  -- no-op for now

/-- A program is a list of qubit-level operations. -/
abbrev QProg (k : ℕ) := List (valid_operation k)

/-- Apply a program (list of operations) to a state, left-to-right. -/
noncomputable def applyProg {k : ℕ} : QProg k → State k → State k
  | [],      σ => σ
  | op :: p, σ => applyProg p (apply op σ)

@[simp] lemma applyProg_nil {k : ℕ} (σ : State k) :
    applyProg ([] : QProg k) σ = σ := rfl

@[simp] lemma applyProg_cons {k : ℕ}
    (op : valid_operation k) (p : QProg k) (σ : State k) :
    applyProg (op :: p) σ = applyProg p (apply op σ) := rfl

end Qubits


/-
############################################################
## Compiler from integer-level ops to qubit-level ops
############################################################
-/

open Qubits

namespace Compile


abbrev Layout (k : ℕ) := Qubits.State k

/-- Axiomatic compilation of `addScaled` with `negSrc = true`.

We don't specify *how* this is implemented; we only assume there is
*some* list of qubit ops and resulting state. -/
axiom compileOp_addScaled_neg
  {k : ℕ} (σ : Qubits.State k) (dst src : Fin k) (sh : ℕ) :
  Qubits.QProg k × Qubits.State k

/-- Axiom: the compiled negative `addScaled` is the inverse of the
    positive (sign = false) `addScaled` at the qubit level. -/
axiom compileOp_addScaled_neg_inverse
  {k : ℕ} (σ : Qubits.State k) (dst src : Fin k) (sh : ℕ) :
  let (progNeg, _σNeg) := compileOp_addScaled_neg σ dst src sh
  let dst_ran : ℕ × ℕ := Qubits.logicalRange (σ dst)
  let src_ran : ℕ × ℕ := Qubits.shiftedRange (σ src) sh
  let opPos : Qubits.valid_operation k :=
    Qubits.valid_operation.add dst src dst_ran src_ran
  Qubits.applyProg (opPos :: progNeg) σ = σ

/-- Compile *one* integer-level op, threading the current qubit layout.

Returns:
* a `QProg k` (list of qubit `valid_operation`s),
* the **updated** qubit state after those ops. -/
noncomputable def compileOp {k : ℕ}
    (σ : Qubits.State k) (op : Operations.valid_ops k) :
    Qubits.QProg k × Qubits.State k :=
  match op with
  | Operations.valid_ops.shiftL i n =>
      let opQ : Qubits.valid_operation k :=
        Qubits.valid_operation.shiftL i n
      let σ' : Qubits.State k := Qubits.apply opQ σ
      ([opQ], σ')

  | Operations.valid_ops.shiftR i n =>
      let opQ : Qubits.valid_operation k :=
        Qubits.valid_operation.shiftR i n
      let σ' : Qubits.State k := Qubits.apply opQ σ
      ([opQ], σ')

  | Operations.valid_ops.negate i =>
      let opQ : Qubits.valid_operation k :=
        Qubits.valid_operation.negate i
      let σ' : Qubits.State k := Qubits.apply opQ σ
      ([opQ], σ')

  | Operations.valid_ops.addScaled dst src false sh =>
      -- dst ← dst + (src << sh)
      let dst_ran : ℕ × ℕ := Qubits.logicalRange (σ dst)
      let src_ran : ℕ × ℕ := Qubits.shiftedRange (σ src) sh
      let opQ : Qubits.valid_operation k :=
        Qubits.valid_operation.add dst src dst_ran src_ran
      let σ' : Qubits.State k := Qubits.apply opQ σ
      ([opQ], σ')

  | Operations.valid_ops.addScaled dst src true sh =>
      -- Axiomatic: compiled as the inverse of the positive addScaled.
      compileOp_addScaled_neg σ dst src sh

  | Operations.valid_ops.phaseProduct i =>
      let opQ : Qubits.valid_operation k :=
        Qubits.valid_operation.phaseProduct i
      let σ' : Qubits.State k := Qubits.apply opQ σ
      ([opQ], σ')

/-- Compile a whole list of integer-level ops, threading the qubit layout. -/
noncomputable def compileProgram {k : ℕ}
    (σ0 : Qubits.State k) (ops : Prog k) :
    Qubits.QProg k × Qubits.State k :=
  match ops with
  | [] =>
      ([], σ0)
  | op :: ops' =>
      let (prog1, σ1) := compileOp σ0 op
      let (prog2, σ2) := compileProgram σ1 ops'
      (prog1 ++ prog2, σ2)


/-
############################################################
## PhaseProduct-style layout and concrete program example
############################################################
-/

namespace Qubits

/-!
Concrete "PhaseProduct-style" architecture state:

  x0 : n/2 bits
  x1 : n/2 bits
  z0 : n/2 bits
  z1 : n/2 bits
-/

/-- Number of registers in the PhaseProduct layout. -/
def PP_k : ℕ := 4

/-- Indices of the logical registers. -/
def idx_x0 : Fin PP_k := ⟨0, by decide⟩
def idx_x1 : Fin PP_k := ⟨1, by decide⟩
def idx_z0 : Fin PP_k := ⟨2, by decide⟩
def idx_z1 : Fin PP_k := ⟨3, by decide⟩

/-- A canonical state for an `n`-bit multiplier.-/
def PP_initState (n : ℕ)
    (qx0 qx1 qz0 qz1: QReg) : Qubits.State PP_k :=
  let m := n / 2
  fun i =>
    if _h0 : i = idx_x0 then
      { qreg := qx0, shift := 0, used := m }
    else if _h1 : i = idx_x1 then
      { qreg := qx1, shift := 0, used := m }
    else if _h3 : i = idx_z0 then
      { qreg := qz0, shift := 0, used := m }
    else
      { qreg := qz1, shift := 0, used := m }

/-- A small integer-level program in the PhaseProduct layout:

    1. shiftL x0 by 1
    2. z0 ← z0 + x0 (no extra shift, sign = +1)
-/
def PP_ops : List (Operations.valid_ops PP_k) :=
  [ Operations.valid_ops.shiftL idx_x0 1,
    Operations.valid_ops.addScaled idx_z0 idx_x0 false 0 ]

def PP_ops_2 : List (Operations.valid_ops PP_k) :=
  [ Operations.valid_ops.phaseProduct idx_x0,
    Operations.valid_ops.phaseProduct idx_z0,
    Operations.valid_ops.phaseProduct idx_x1,
    Operations.valid_ops.phaseProduct idx_z1,

    Operations.valid_ops.addScaled idx_x1 idx_x0 false 0,
    Operations.valid_ops.addScaled idx_z1 idx_z0 false 0,
    Operations.valid_ops.phaseProduct idx_x1,
    Operations.valid_ops.phaseProduct idx_z1,
    Operations.valid_ops.addScaled idx_x1 idx_x0 true 0,
    Operations.valid_ops.addScaled idx_z1 idx_z0 true 0
    ]



/-- Concrete description of how `PP_ops` compiles to a qubit program
    and final state, starting from `PP_initState`. -/
theorem compile_PP_ops
    (n : ℕ) (qx0 qx1 qz0 qz1 : QReg) :
  let σ0  : Qubits.State PP_k := PP_initState n qx0 qx1 qz0 qz1
  let σ1  : Qubits.State PP_k :=
    Qubits.apply (Qubits.valid_operation.shiftL idx_x0 1) σ0
  let dst_ran : ℕ × ℕ := Qubits.logicalRange (σ1 idx_z0)
  let src_ran : ℕ × ℕ := Qubits.shiftedRange (σ1 idx_x0) 0
  let op2 : Qubits.valid_operation PP_k :=
    Qubits.valid_operation.add idx_z0 idx_x0 dst_ran src_ran
  compileProgram σ0 PP_ops
      =
      ( [ Qubits.valid_operation.shiftL idx_x0 1, op2 ],
        Qubits.apply op2 σ1 ) := by
  simp [PP_ops, compileProgram, compileOp]

/-- Concrete, range-resolved description of `PP_ops` compilation. -/
theorem compile_PP_ops_concrete
    (n : ℕ) (qx0 qx1 qz0 qz1 : QReg) :
  let m   := n / 2
  let σ0  : Qubits.State PP_k := PP_initState n qx0 qx1 qz0 qz1
  let op1 : Qubits.valid_operation PP_k :=
    Qubits.valid_operation.shiftL idx_x0 1
  let op2 : Qubits.valid_operation PP_k :=
    Qubits.valid_operation.add idx_z0 idx_x0 (0, m) (1, 1 + m)
  compileProgram σ0 PP_ops
      =
      ( [op1, op2],
        Qubits.apply op2 (Qubits.apply op1 σ0) ) := by
  intro m σ0 op1 op2
  simp [m, σ0, op1, op2,
        PP_ops,
        compileProgram, compileOp,
        PP_initState,
        Qubits.apply,
        Qubits.logicalRange, Qubits.shiftedRange,
        Qubits.StateOps.shiftLReg, Qubits.StateOps.setReg,
        Qubits.shiftL, idx_x0, idx_z0, idx_x1]


/-- Prefix of the qubit-level program corresponding to the *positive*
    part of `PP_ops_2`:

    φ(x0), φ(z0), φ(x1), φ(z1),
    ADD x1 += x0, ADD z1 += z0,
    φ(x1), φ(z1).

The ADDs use windows `(0,m)` on both destination and source, which is
exactly what `compileOp` produces when starting from `PP_initState`
(where all four registers have `shift = 0`, `used = m`). -/
def PP_ops_2_prefix (m : ℕ) : QProg PP_k :=
  [ valid_operation.phaseProduct idx_x0,
    valid_operation.phaseProduct idx_z0,
    valid_operation.phaseProduct idx_x1,
    valid_operation.phaseProduct idx_z1,
    valid_operation.add idx_x1 idx_x0 (0, m) (0, m),
    valid_operation.add idx_z1 idx_z0 (0, m) (0, m),
    valid_operation.phaseProduct idx_x1,
    valid_operation.phaseProduct idx_z1 ]

/-- Concrete translation theorem for `PP_ops_2`.

Starting from the PhaseProduct-style initial state `PP_initState`, the
compiler produces:

  • the explicit prefix `PP_ops_2_prefix m` (where `m = n/2`), and then
  • two axiomatic negative blocks (from `compileOp_addScaled_neg`)
    for `addScaled idx_x1 idx_x0 true 0` and
    `addScaled idx_z1 idx_z0 true 0`.

The final state is exactly what you get by running that combined
qubit-level program. -/
theorem compile_PP_ops_2
    (n : ℕ) (qx0 qx1 qz0 qz1 : QReg) :
  let m   := n / 2
  let σ0  : Qubits.State PP_k := PP_initState n qx0 qx1 qz0 qz1
  let σ8  : Qubits.State PP_k := Qubits.applyProg (PP_ops_2_prefix m) σ0
  let res1 := compileOp_addScaled_neg σ8 idx_x1 idx_x0 0
  let res2 := compileOp_addScaled_neg res1.snd idx_z1 idx_z0 0
  compileProgram σ0 PP_ops_2
    =
    ( PP_ops_2_prefix m ++ res1.fst ++ res2.fst,
      res2.snd ) := by
  intro m σ0 σ8 res1 res2
  sorry

end Qubits


/-
############################################################
## Basic compileOp lemmas (single-op translations)
############################################################
-/

open Qubits
open Compile

/-- For any state, compiling `shiftL i n` produces exactly one
    qubit op `shiftL i n`, and the resulting qubit state is
    `shiftLReg` on that register. -/
theorem compileOp_shiftL_sound
    {k : ℕ} (σ : Qubits.State k) (i : Fin k) (n : ℕ) :
  compileOp σ (Operations.valid_ops.shiftL i n)
    = ([Qubits.valid_operation.shiftL i n],
       Qubits.StateOps.shiftLReg σ i n) := by
  simp [compileOp, Qubits.StateOps.shiftLReg, apply]

/-- Similarly, compiling `shiftR i n` produces one qubit `shiftR i n`
    and the state-level effect is `shiftRReg` on that register. -/
theorem compileOp_shiftR_sound
    {k : ℕ} (σ : Qubits.State k) (i : Fin k) (n : ℕ) :
  compileOp σ (Operations.valid_ops.shiftR i n)
    = ([Qubits.valid_operation.shiftR i n],
       Qubits.StateOps.shiftRReg σ i n) := by
  simp [compileOp, Qubits.StateOps.shiftRReg, apply]

/-- For the positive case `addScaled dst src false sh`, the compiler
    produces one windowed `add` whose ranges are exactly
    `logicalRange (σ dst)` and `shiftedRange (σ src) sh`, and the new
    qubit state is `apply`ing that `add` to `σ`. -/
theorem compileOp_addScaled_pos_sound
    {k : ℕ} (σ : Qubits.State k)
    (dst src : Fin k) (sh : ℕ) :
  compileOp σ (Operations.valid_ops.addScaled dst src false sh)
    =
    ( [Qubits.valid_operation.add dst src
         (Qubits.logicalRange (σ dst))
         (Qubits.shiftedRange (σ src) sh)],
      Qubits.apply
        (Qubits.valid_operation.add dst src
           (Qubits.logicalRange (σ dst))
           (Qubits.shiftedRange (σ src) sh))
        σ ) := by
  simp [compileOp]

/-- In the PhaseProduct layout, compiling `shiftL idx_x0 n` from the
    initial `PP_initState` produces exactly one qubit op
    `shiftL idx_x0 n`, and the resulting state is
    `shiftLReg` applied to `x0` in that layout. -/
theorem compileOp_shiftL_x0_PP
    (n : ℕ) (qx0 qx1 qz0 qz1 : QReg) (sh : ℕ) :
  let σ0 : Qubits.State PP_k := PP_initState n qx0 qx1 qz0 qz1
  compileOp σ0 (Operations.valid_ops.shiftL idx_x0 sh)
      =
      ( [Qubits.valid_operation.shiftL idx_x0 sh],
        Qubits.StateOps.shiftLReg σ0 idx_x0 sh ) := by
  intro σ0
  simpa [σ0] using
    (compileOp_shiftL_sound σ0 idx_x0 sh)


/-
############################################################
## Semantic axioms and correctness of the compiler
############################################################
-/

open Qubits
open Compile


axiom compileOp_addScaled_neg_semantic
  {k : ℕ} (σ : Qubits.State k) (dst src : Fin k) (sh : ℕ) :
  let (progNeg, σNeg) := compileOp_addScaled_neg σ dst src sh
  Qubits.applyProg progNeg σ = σNeg

/-- Helpful lemma: executing `p₁ ++ p₂` is the same as executing `p₁`
    then `p₂`. -/
lemma Qubits.applyProg_append {k : ℕ}
    (p₁ p₂ : Qubits.QProg k) (σ : Qubits.State k) :
  Qubits.applyProg (p₁ ++ p₂) σ
    = Qubits.applyProg p₂ (Qubits.applyProg p₁ σ) := by
  induction p₁ generalizing σ with
  | nil =>
      simp [Qubits.applyProg]
  | cons op p₁ ih =>
      simp [Qubits.applyProg, ih, List.cons_append]

/-- **Single-step correctness** of `compileOp`: -/
theorem compileOp_sound {k : ℕ}
    (σ : Qubits.State k) (op : Operations.valid_ops k) :
  let res := compileOp σ op
  Qubits.applyProg res.1 σ = res.2 := by
  cases op with
  | shiftL i n =>
      simp [compileOp, Qubits.applyProg]
  | shiftR i n =>
      simp [compileOp, Qubits.applyProg]
  | negate i =>
      simp [compileOp, Qubits.applyProg]
  | addScaled dst src ng sh =>
      cases ng with
      | false =>
          simp [compileOp, Qubits.applyProg]
      | true =>
          -- delegate to the axiomatic negative case
          have h := compileOp_addScaled_neg_semantic σ dst src sh
          simpa [compileOp] using h
  | phaseProduct i =>
      simp [compileOp, Qubits.applyProg]


theorem compileProgram_sound {k : ℕ}
    (σ₀ : Qubits.State k) (ops : List (Operations.valid_ops k)) :
  let res := compileProgram σ₀ ops
  Qubits.applyProg res.1 σ₀ = res.2 := by
  simp
  induction ops generalizing σ₀ with
  | nil =>
      simp [compileProgram]
  | cons op ops ih =>
      -- Expand the definition of compileProgram for (op :: ops)
      simp [compileProgram] at ih ⊢
      cases h1 : compileOp σ₀ op with
      | mk prog1 σ1 =>
        have hstep : Qubits.applyProg prog1 σ₀ = σ1 := by
          -- single-step correctness for this op
          have := compileOp_sound σ₀ op
          simpa [h1] using this
        cases h2 : compileProgram σ1 ops with
        | mk prog2 σ2 =>
          have htail : Qubits.applyProg prog2 σ1 = σ2 := by
            have := ih σ1
            simpa [h2] using this
          have := Qubits.applyProg_append prog1 prog2 σ₀
          aesop
