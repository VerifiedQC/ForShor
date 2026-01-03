import FastMultiplication.one_reg_synth_proof_2

open Classical

/-
############################################################
## Qubit-level primitives as a typeclass
############################################################
-/

/-- Primitive qubit-level operations that we assume exist. -/
class QubitPrimitives where
  /-- Abstract type of a single qubit. -/
  Qubit : Type
  addQReg :
    (ℕ → Qubit) → ℕ → (ℕ → Qubit) → ℕ → (ℕ → Qubit)
  negateQReg :
    (ℕ → Qubit) → (ℕ → Qubit)


/-
############################################################
## Qubit-level model and state-level operations
############################################################
-/

namespace Qubits

variable [QubitPrimitives]

/-- An arbitrarily large qubit reg indexed by ℕ. -/
abbrev Qubit  := QubitPrimitives.Qubit
abbrev QReg  := ℕ → Qubit

/-- A logical register: a QReg + a shift + a used range. -/
structure Register_w where
  qreg  : QReg
  shift : ℕ
  used  : ℕ

/-- A state of `k` qubit-Register_ws. -/
def State (k : ℕ) := Fin k → Register_w

/-- Low-level adder on *windows* of the destination and source Register_ws. -/
noncomputable def add (dst : Register_w) (dst_ran : ℕ × ℕ)
    (src : Register_w) (src_ran : ℕ × ℕ) : Register_w :=
  let (d1, d2) := dst_ran  -- range of destination qubits used
  let (s1, s2) := src_ran  -- range of source qubits used
  { qreg  := QubitPrimitives.addQReg dst.qreg dst.shift src.qreg s1
  , shift := dst.shift
  , used  := (Nat.max d2 s2 + 1) - (Nat.min d1 s1) -- d1 + Nat.max dlen slen + 1
  }

/-- Logical range of the *used* bits of a Register_w:
    indices `[shift, shift + used)`. -/
def logicalRange (r : Register_w) : ℕ × ℕ :=
  (r.shift, r.shift + r.used)

/-- Logical range of the used bits if the Register_w were additionally shifted left
    by `sh` bits: indices `[shift + sh, shift + sh + used)`. -/
def shiftedRange (r : Register_w) (sh : ℕ) : ℕ × ℕ :=
  (r.shift + sh, r.shift + sh + r.used)

/-- Logical left shift by `n` bits: multiply by `2^n`. -/
def shiftL (r : Register_w) (n : ℕ) : Register_w :=
  { r with shift := r.shift + n }

/-- Logical right shift by `n` bits: divide by `2^n` (truncating). -/
def shiftR (r : Register_w) (n : ℕ) : Register_w :=
  { r with shift := r.shift - n }

/-- Logical negation of a Register_w: conceptually multiply by `-1`. -/
noncomputable def negate (r : Register_w) : Register_w :=
  { r with qreg := QubitPrimitives.negateQReg r.qreg }

@[simp] lemma shiftL_qreg (r : Register_w) (n : ℕ) :
    (shiftL r n).qreg = r.qreg := rfl

@[simp] lemma shiftL_used (r : Register_w) (n : ℕ) :
    (shiftL r n).used = r.used := rfl

@[simp] lemma shiftL_shift (r : Register_w) (n : ℕ) :
    (shiftL r n).shift = r.shift + n := rfl

@[simp] lemma shiftR_qreg (r : Register_w) (n : ℕ) :
    (shiftR r n).qreg = r.qreg := rfl

@[simp] lemma shiftR_used (r : Register_w) (n : ℕ) :
    (shiftR r n).used = r.used := rfl

@[simp] lemma shiftR_shift (r : Register_w) (n : ℕ) :
    (shiftR r n).shift = r.shift - n := rfl


/-! ## State-level operations -/

namespace StateOps


/-- Overwrite Register_w `i` in the state. -/
def setReg {k : ℕ} (σ : State k) (i : Fin k) (r : Register_w) : State k :=
  fun j => if h : j = i then (Eq.rec r h.symm) else σ j

@[simp] lemma setReg_self {k : ℕ} (σ : State k) (i : Fin k) (r : Register_w) :
    setReg σ i r i = r := by
  simp [setReg]

@[simp] lemma setReg_other {k : ℕ} (σ : State k) (i j : Fin k) (r : Register_w)
    (h : j ≠ i) :
    setReg σ i r j = σ j := by
  simp [setReg, h]

/-- Logical left shift of Register_w `i` in the state by `n` bits. -/
def shiftLReg {k : ℕ} (σ : State k) (i : Fin k) (n : ℕ) : State k :=
  setReg σ i (shiftL (σ i) n)

/-- Logical right shift of Register_w `i` in the state by `n` bits. -/
def shiftRReg {k : ℕ} (σ : State k) (i : Fin k) (n : ℕ) : State k :=
  setReg σ i (shiftR (σ i) n)

/-- Negate Register_w `i` in the state. -/
noncomputable def negateReg {k : ℕ} (σ : State k) (i : Fin k) : State k :=
  setReg σ i (negate (σ i))

/-- **State-level windowed add**:
    apply the low-level `add` to Register_ws `dst` and `src` using
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

We no longer have `shiftL` and `shiftR` here-/
inductive valid_operation (k : ℕ) where
  | negate      (i : Fin k)
  | add         (dst src : Fin k) (dst_ran src_ran : ℕ × ℕ)
  | phaseProduct (i : Fin k)
deriving Repr

/-- Semantics of a single `valid_operation` on a state. -/
noncomputable def apply {k : ℕ} (op : valid_operation k) (σ : State k) : State k :=
  match op with
  | valid_operation.negate i               => StateOps.negateReg σ i
  | valid_operation.add dst src dr sr      => StateOps.addReg σ dst src dr sr
  | valid_operation.phaseProduct _         => σ  -- phaseProduct is a no-op here

abbrev QProg (k : ℕ) := List (valid_operation k)

noncomputable def applyProg {k : ℕ} : QProg k → State k → State k
  | [],      σ => σ
  | op :: p, σ => applyProg p (apply op σ)

@[simp] lemma applyProg_nil {k : ℕ} (σ : State k) :
    applyProg ([] : QProg k) σ = σ := rfl

@[simp] lemma applyProg_cons {k : ℕ}
    (op : valid_operation k) (p : QProg k) (σ : State k) :
    applyProg (op :: p) σ = applyProg p (apply op σ) := rfl

/-- Helpful lemma: executing `p₁ ++ p₂` is the same as executing `p₁`
    then `p₂`. -/
lemma applyProg_append {k : ℕ}
    (p₁ p₂ : QProg k) (σ : State k) :
  applyProg (p₁ ++ p₂) σ
    = applyProg p₂ (applyProg p₁ σ) := by
  induction p₁ generalizing σ with
  | nil =>
      simp [applyProg]
  | cons op p₁ ih =>
      simp [applyProg, ih, List.cons_append]

/-!
Concrete "PhaseProduct-style" architecture state:

  x0 : n/2 bits
  x1 : n/2 bits
  z0 : n/2 bits
  z1 : n/2 bits
-/

/-- Number of Register_ws in the PhaseProduct layout. -/
def PP_k : ℕ := 4

/-- Indices of the logical Register_ws. -/
def idx_x0 : Fin PP_k := ⟨0, by decide⟩
def idx_x1 : Fin PP_k := ⟨1, by decide⟩
def idx_z0 : Fin PP_k := ⟨2, by decide⟩
def idx_z1 : Fin PP_k := ⟨3, by decide⟩

/-- A canonical state for an `n`-bit multiplier.-/
def PP_initState (n : ℕ)
    (qx0 qx1 qz0 qz1: QReg) : State PP_k :=
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

def PP_ops_2_prefix (m : ℕ) : QProg PP_k :=
  [ valid_operation.phaseProduct idx_x0,
    valid_operation.phaseProduct idx_z0,
    valid_operation.phaseProduct idx_x1,
    valid_operation.phaseProduct idx_z1,
    valid_operation.add idx_x1 idx_x0 (0, m) (0, m),
    valid_operation.add idx_z1 idx_z0 (0, m) (0, m),
    valid_operation.phaseProduct idx_x1,
    valid_operation.phaseProduct idx_z1 ]

end Qubits


/-
############################################################
## Backend for negative addScaled compilation as a class
############################################################
-/

open Qubits

/-- Backend specification for compiling the negative `addScaled`. -/
class AddScaledNegBackend (k : ℕ) [QubitPrimitives] where
  /-- Axiomatic compilation of `addScaled` with `negSrc = true`. -/
  compileOp_addScaled_neg :
    Qubits.State k → Fin k → Fin k → ℕ →
    Qubits.QProg k × Qubits.State k

  /-- Left inverse law at the qubit level. -/
  compileOp_addScaled_neg_left_inverse :
    ∀ (σ : Qubits.State k) (dst src : Fin k) (sh : ℕ),
      let (progNeg, _σNeg) := compileOp_addScaled_neg σ dst src sh
      let dst_ran : ℕ × ℕ := Qubits.logicalRange (σ dst)
      let src_ran : ℕ × ℕ := Qubits.shiftedRange (σ src) sh
      let opPos : Qubits.valid_operation k :=
        Qubits.valid_operation.add dst src dst_ran src_ran
      Qubits.applyProg (opPos :: progNeg) σ = σ

  /-- Right inverse law at the qubit level. -/
  compileOp_addScaled_neg_right_inverse :
    ∀ (σ : Qubits.State k) (dst src : Fin k) (sh : ℕ),
      let (progNeg, _σNeg) := compileOp_addScaled_neg σ dst src sh
      let dst_ran : ℕ × ℕ := Qubits.logicalRange (σ dst)
      let src_ran : ℕ × ℕ := Qubits.shiftedRange (σ src) sh
      let opPos : Qubits.valid_operation k :=
        Qubits.valid_operation.add dst src dst_ran src_ran
      Qubits.applyProg (progNeg ++ [opPos]) σ = σ

  /-- Semantic law: running the compiled negative program yields
      exactly the second component of the pair. -/
  compileOp_addScaled_neg_semantic :
    ∀ (σ : Qubits.State k) (dst src : Fin k) (sh : ℕ),
      let (progNeg, σNeg) := compileOp_addScaled_neg σ dst src sh
      Qubits.applyProg progNeg σ = σNeg


/-
############################################################
## Compiler from integer-level ops to qubit-level ops
############################################################
-/

namespace Compile

open Qubits

variable [QubitPrimitives]

abbrev Layout (k : ℕ) := Qubits.State k

/-- Compile *one* integer-level op, threading the current qubit layout. -/
noncomputable def compileOp {k : ℕ}
    [AddScaledNegBackend k]
    (σ : Qubits.State k) (op : Operations.valid_ops k) :
    Qubits.QProg k × Qubits.State k :=
  match op with
  | Operations.valid_ops.shiftL i n =>
      -- no qubit gates, just update layout
      let σ' : Qubits.State k := Qubits.StateOps.shiftLReg σ i n
      ([], σ')

  | Operations.valid_ops.shiftR i n =>
      -- no qubit gates, just update layout
      let σ' : Qubits.State k := Qubits.StateOps.shiftRReg σ i n
      ([], σ')

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
      -- compiled as the inverse of the positive addScaled.
      AddScaledNegBackend.compileOp_addScaled_neg (k := k) σ dst src sh

  | Operations.valid_ops.phaseProduct i =>
      let opQ : Qubits.valid_operation k :=
        Qubits.valid_operation.phaseProduct i
      let σ' : Qubits.State k := Qubits.apply opQ σ
      ([opQ], σ')

/-- For any state, compiling `shiftL i n` produces **no** qubit ops
    and updates the wiring-level state via `shiftLReg`. -/
theorem compileOp_shiftL_meta
    {k : ℕ} [AddScaledNegBackend k]
    (σ : Qubits.State k) (i : Fin k) (n : ℕ) :
  compileOp σ (Operations.valid_ops.shiftL i n)
    = ([], Qubits.StateOps.shiftLReg σ i n) := by
  simp [compileOp, Qubits.StateOps.shiftLReg]

/-- Similarly, compiling `shiftR i n` produces no qubit ops and the
    state-level effect is `shiftRReg` on that register. -/
theorem compileOp_shiftR_meta
    {k : ℕ} [AddScaledNegBackend k]
    (σ : Qubits.State k) (i : Fin k) (n : ℕ) :
  compileOp σ (Operations.valid_ops.shiftR i n)
    = ([], Qubits.StateOps.shiftRReg σ i n) := by
  simp [compileOp, Qubits.StateOps.shiftRReg]

/-- For the positive case `addScaled dst src false sh`, the compiler
    produces one windowed `add` whose ranges are exactly
    `logicalRange (σ dst)` and `shiftedRange (σ src) sh`, and the new
    qubit state is `apply`ing that `add` to `σ`. -/
theorem compileOp_addScaled_pos_sound
    {k : ℕ} [AddScaledNegBackend k]
    (σ : Qubits.State k)
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

/-- Compile a whole list of integer-level ops, threading the qubit layout. -/
noncomputable def compileProgramAux {k : ℕ}
    [AddScaledNegBackend k]
    (σ0 : Qubits.State k) (ops : Prog k) :
    Qubits.QProg k × Qubits.State k :=
  match ops with
  | [] =>
      ([], σ0)
  | op :: ops' =>
      let (prog1, σ1) := compileOp σ0 op
      let (prog2, σ2) := compileProgramAux σ1 ops'
      (prog1 ++ prog2, σ2)

noncomputable def compile_Prog {k}
  [AddScaledNegBackend k]
  (σ0 : Qubits.State k) (ops : Prog k) :
    Qubits.QProg k := (compileProgramAux σ0 ops).1

@[simp] lemma compile_Prog_nil (σQ : Qubits.State k) [AddScaledNegBackend k]:
    compile_Prog σQ ([] : Prog k) = ([] : Qubits.QProg k) := by
  simp [Compile.compile_Prog, Compile.compileProgramAux]

lemma compile_Prog_cons (σQ : Qubits.State k) [AddScaledNegBackend k]
    (op : Operations.valid_ops k) (ps : Prog k) :
    compile_Prog σQ (op :: ps)
      = (compileOp σQ op).1 ++ compile_Prog (compileOp σQ op).2 ps := by
  -- Unfold the definition through `compileProgramAux`
  cases h : compileOp σQ op with
  | mk prog1 σQ₁ =>
    simp [Compile.compile_Prog, Compile.compileProgramAux, h]


end Compile


/-
############################################################
## Decode backend as a class
############################################################
-/

open Qubits Compile

/-- Decoding qubit-level states into the classical `Register k` world,
    together with the semantic laws we assume. -/
class DecodeBackend (k : ℕ) [QubitPrimitives] [AddScaledNegBackend k] where
  decodeRegister : Qubits.Register_w → Register k

  decode_shiftLReg_ax :
    ∀ (σQ : Qubits.State k) (i : Fin k) (n : ℕ),
      (fun j => decodeRegister ((Qubits.StateOps.shiftLReg σQ i n) j))
        = State.shiftLReg (fun j => decodeRegister (σQ j)) i n

  decode_shiftRReg_ax :
    ∀ (σQ : Qubits.State k) (i : Fin k) (n : ℕ),
      State.shiftRReg?
        (fun j => decodeRegister (σQ j)) i n
        = some (fun j => decodeRegister ((Qubits.StateOps.shiftRReg σQ i n) j))

  decode_negateReg_ax :
    ∀ (σQ : Qubits.State k) (i : Fin k),
      (fun j => decodeRegister ((Qubits.StateOps.negateReg σQ i) j))
        = State.negateReg (fun j => decodeRegister (σQ j)) i

  decode_addScaledReg_pos_ax :
    ∀ (σQ : Qubits.State k) (dst src : Fin k) (sh : ℕ),
      let dst_ran : ℕ × ℕ := Qubits.logicalRange (σQ dst)
      let src_ran : ℕ × ℕ := Qubits.shiftedRange (σQ src) sh
      (fun j => decodeRegister ((Qubits.StateOps.addReg σQ dst src dst_ran src_ran) j))
        = State.addScaledReg (fun j => decodeRegister (σQ j)) dst src false sh

  decode_compileOp_addScaled_neg_ax :
    ∀ (σQ : Qubits.State k) (dst src : Fin k) (sh : ℕ),
      let σC := fun j => decodeRegister (σQ j)
      let res := AddScaledNegBackend.compileOp_addScaled_neg (k := k) σQ dst src sh
      (fun j => decodeRegister (res.2 j))
        = State.addScaledReg σC dst src true sh


/-- Interpret a wiring-level state as a classical integer-coefficient state. -/
def decodeState {k : ℕ}
    [QubitPrimitives] [AddScaledNegBackend k] [DecodeBackend k]
    (σ : Qubits.State k) : _root_.State k :=
  fun i => DecodeBackend.decodeRegister (k := k) (σ i)

/-!
  Now we re-expose the original decode lemmas (with the same names as
  in your code) as thin wrappers around the class axioms.
-/

theorem decode_shiftLReg
  {k : ℕ} [QubitPrimitives] [AddScaledNegBackend k] [DecodeBackend k]
  (σQ : Qubits.State k) (i : Fin k) (n : ℕ) :
  decodeState (Qubits.StateOps.shiftLReg σQ i n)
    = State.shiftLReg (decodeState σQ) i n := by
  --funext j
  have := DecodeBackend.decode_shiftLReg_ax σQ i n
  unfold decodeState State.shiftLReg State.setReg at *
  simp at *
  aesop


theorem decode_shiftRReg
  {k : ℕ} [QubitPrimitives] [AddScaledNegBackend k] [DecodeBackend k]
  (σQ : Qubits.State k) (i : Fin k) (n : ℕ) :
  State.shiftRReg? (decodeState σQ) i n
    = some (decodeState (Qubits.StateOps.shiftRReg σQ i n)) := by
  have := DecodeBackend.decode_shiftRReg_ax σQ i n
  unfold decodeState State.shiftRReg? State.setReg at *
  simp at *
  aesop

theorem decode_negateReg
  {k : ℕ} [QubitPrimitives] [AddScaledNegBackend k] [DecodeBackend k]
  (σQ : Qubits.State k) (i : Fin k) :
  decodeState (Qubits.StateOps.negateReg σQ i)
    = State.negateReg (decodeState σQ) i := by
  have := DecodeBackend.decode_negateReg_ax σQ i
  unfold decodeState State.negateReg State.setReg at *
  simp at *
  aesop

theorem decode_addScaledReg_pos
  {k : ℕ} [QubitPrimitives] [AddScaledNegBackend k] [DecodeBackend k]
  (σQ : Qubits.State k) (dst src : Fin k) (sh : ℕ) :
  let dst_ran : ℕ × ℕ := Qubits.logicalRange (σQ dst)
  let src_ran : ℕ × ℕ := Qubits.shiftedRange (σQ src) sh
  decodeState (Qubits.StateOps.addReg σQ dst src dst_ran src_ran)
    = State.addScaledReg (decodeState σQ) dst src false sh := by
  have := DecodeBackend.decode_addScaledReg_pos_ax σQ dst src sh
  simp at this
  unfold decodeState StateOps.addReg StateOps.setReg at *
  simp at *
  aesop
theorem decode_compileOp_addScaled_neg
  {k : ℕ} [QubitPrimitives] [AddScaledNegBackend k] [DecodeBackend k]
  (σQ : Qubits.State k) (dst src : Fin k) (sh : ℕ) :
  let σC := decodeState σQ
  let res := AddScaledNegBackend.compileOp_addScaled_neg (k := k) σQ dst src sh
  decodeState res.2
    = State.addScaledReg σC dst src true sh := by
  have := DecodeBackend.decode_compileOp_addScaled_neg_ax σQ dst src sh
  simp at this
  unfold decodeState at *
  simp at *
  aesop

/-
############################################################
## Single-step and multi-step decode-level correctness
############################################################
-/

open Qubits Compile

/-- Single-step refinement: one integer op vs its compiled qubit program,
    at the decoded (classical) level. -/
theorem compileOp_respects_decode
    {k : ℕ}
    [QubitPrimitives] [AddScaledNegBackend k] [DecodeBackend k]
    (σQ : Qubits.State k) (op : Operations.valid_ops k) :
  let σC    := decodeState σQ
  let res   := Compile.compileOp σQ op
  let σQ'   := res.2
  some (decodeState σQ')
    = run? [op] σC := by
  simp only at *
  cases op with
  | shiftL i sh =>
      simp [Compile.compileOp, decode_shiftLReg, run?, applyOp?]
  | shiftR i sh =>
      have h := decode_shiftRReg (σQ := σQ) i sh
      -- rewrite using the helper lemma
      simp [Compile.compileOp, run?, applyOp?] at *
      aesop
  | negate i =>
      have:=decode_negateReg σQ i
      simp [Compile.compileOp, run?, applyOp?, State.negateReg, decodeState]
      aesop
  | addScaled dst src sign sh =>
      cases sign with
      | false =>
          simp [Compile.compileOp,run?,decode_addScaledReg_pos,Qubits.apply]
      | true =>
          have h := decode_compileOp_addScaled_neg (σQ := σQ) dst src sh
          aesop
  | phaseProduct i =>
      simp [Compile.compileOp, run?, applyOp?, Qubits.apply]

theorem compileProg_respects_decode
    {k : ℕ}
    [QubitPrimitives] [AddScaledNegBackend k] [DecodeBackend k]
    (σQ : Qubits.State k) (ops : Prog k) :
  let σC    := decodeState σQ
  let res   := Compile.compileProgramAux σQ ops
  let σQ'   := res.2
  some (decodeState σQ')
    = run? ops σC := by
  intro σC res σQ'
  induction ops generalizing σQ with
  | nil =>
      aesop
  | cons op ops ih =>
      simp at ih ⊢
      cases h1 : Compile.compileOp σQ op with
      | mk prog1 σQ₁ =>
        have hstep : some (decodeState σQ₁)
            = run? [op] (decodeState σQ) := by
          have := compileOp_respects_decode (σQ := σQ) (op := op)
          simpa [h1] using this

        cases h2 : Compile.compileProgramAux σQ₁ ops with
        | mk prog2 σQ₂ =>
          have htail : some (decodeState σQ₂)
              = run? ops (decodeState σQ₁) := by
            have := ih σQ₁
            simpa [Compile.compileProgramAux, h2] using this

          have hApply : applyOp? (decodeState σQ) op
                           = some (decodeState σQ₁) := by
            have := hstep
            simp [run?] at this
            aesop
          have hres : σQ' = σQ₂ := by
            unfold σQ' res
            simp [Compile.compileProgramAux, h1, h2]
          rw [hres, htail, hApply]


def zeroShiftState {k : ℕ} [ QubitPrimitives] (σQ : Qubits.State k): Prop :=
  ∀ i : Fin k, (σQ i).shift = 0

lemma zeroShift_apply
    {k : ℕ} [QubitPrimitives]
    (op : Qubits.valid_operation k) (σ : Qubits.State k)
    (h : zeroShiftState σ) :
    zeroShiftState (Qubits.apply op σ) := by
  intro i
  cases op with
  | negate j =>
      unfold Qubits.apply StateOps.negateReg StateOps.setReg zeroShiftState at *
      by_cases hji : i = j
      · subst hji ; unfold negate; simp[h]
      · simp [hji, h]
  | add dst src dr sr =>
      unfold Qubits.apply StateOps.addReg StateOps.setReg zeroShiftState at *
      by_cases hdi : i = dst
      · subst hdi
        simp [h, Qubits.add]
      · simp [hdi, h]
  | phaseProduct _ =>
      unfold zeroShiftState at h
      simp [Qubits.apply,h]

lemma zeroShift_applyProg
    {k : ℕ} [QubitPrimitives]
    (p : Qubits.QProg k) (σ : Qubits.State k)
    (h : zeroShiftState σ) :
    zeroShiftState (Qubits.applyProg p σ) := by
  induction p generalizing σ with
  | nil =>
      simpa [Qubits.applyProg] using h
  | cons op ps ih =>
      simp [Qubits.applyProg] at ih ⊢
      -- first apply op, then ps
      exact ih _ (zeroShift_apply op σ h)
