import FastMultiplication.QuantumCircuit.circ_model_list

namespace Qubit_level

--------------------------------------------------------------------------------
-- State and state-level operations
--------------------------------------------------------------------------------

abbrev State (k : ℕ) := Fin k → Register

/-- Nicely render a single register as "bits (value)". -/
def prettyRegister (r : Register) : String :=
  let bits := regToString r
  let n    := regToNat r
  s!"{bits} ({n})"

/-- Lines of a pretty-printed state: ["R0 = ...", "R1 = ...", ...]. -/
def prettyStateLines {k : ℕ} (σ : State k) : List String :=
  (List.finRange k).map fun i =>
    s!"R{i.val} = {regToString (σ i)} ({regToNat (σ i)})"

/-- IO printer that actually prints each register on its own line. -/
def printState {k : ℕ} (σ : State k) : IO Unit := do
  for line in prettyStateLines σ do
    IO.println line

-- Example state:
def exampleState : State 2 :=
  fun
  | ⟨0, _⟩ => [false, true, false]  -- 010₂ = 2
  | ⟨1, _⟩ => [true,  true, false]  -- 011₂ = 3

-- State-level operations
def State.add_with_carry {k : ℕ} (s : State k) (dst src : Fin k) : State k :=
  let rdst    := s dst
  let rsrc    := s src
  let new_dst := add_reg rdst rsrc
  fun j => if j = dst then new_dst else s j

def State.add_no_carry {k : ℕ} (s : State k) (dst src : Fin k) : State k :=
  let rdst    := s dst
  let rsrc    := s src
  let new_dst := add_reg_no_carry rdst rsrc
  fun j => if j = dst then new_dst else s j

def State.shiftL {k : ℕ} (s : State k) (dst : Fin k) : State k :=
  let rdst    := s dst
  let new_dst := left_shift rdst
  fun j => if j = dst then new_dst else s j

def State.shiftR {k : ℕ} (s : State k) (dst : Fin k) : State k :=
  let rdst    := s dst
  let new_dst := right_shift rdst
  fun j => if j = dst then new_dst else s j

def State.negate {k : ℕ} (s : State k) (w : ℕ) (dst : Fin k) : State k :=
  let rdst    := s dst
  let new_dst := negateFixed w rdst
  fun j => if j = dst then new_dst else s j




--------------------------------------------------------------------------------
-- Inductive description of valid operations + sequencing
--------------------------------------------------------------------------------

/--
`valid_operations k` is the syntax of allowed state-level operations
on a `State k`:

* `addWithCarry dst src`     : `dst ← dst + src` with carry bit
* `addNoCarry dst src`       : `dst ← dst + src` dropping final carry
* `shiftL dst`               : logical left shift of `dst`
* `shiftR dst`               : logical right shift of `dst`
* `negate w dst`             : two's-complement negate `dst` at width `w`
* `phaseProduct`             : no-op on the state
-/
inductive valid_operations (k : ℕ) : Type where
  | addWithCarry (dst src : Fin k) : valid_operations k
  | addNoCarry  (dst src : Fin k)  : valid_operations k
  | shiftL      (dst : Fin k)      : valid_operations k
  | shiftR      (dst : Fin k)      : valid_operations k
  | negate      (w : ℕ) (dst : Fin k) : valid_operations k
  | phaseProduct : valid_operations k
deriving Repr

namespace valid_operations

/-- Semantics of a single `valid_operations` on a state. -/
def apply {k : ℕ} (op : valid_operations k) (σ : State k) : State k :=
  match op with
  | valid_operations.addWithCarry dst src =>
      State.add_with_carry σ dst src
  | valid_operations.addNoCarry dst src   =>
      State.add_no_carry σ dst src
  | valid_operations.shiftL dst           =>
      State.shiftL σ dst
  | valid_operations.shiftR dst           =>
      State.shiftR σ dst
  | valid_operations.negate w dst         =>
      State.negate σ w dst
  | valid_operations.phaseProduct         =>
      σ

/--
Semantics of a **sequence** of operations.

`applySeq σ ops` applies each operation in `ops` from left to right.
-/
def applySeq {k : ℕ} (σ : State k) (ops : List (valid_operations k)) : State k :=
  ops.foldl (fun σ op => apply op σ) σ

end valid_operations


--------------------------------------------------------------------------------
-- Small example: sequence of operations
--------------------------------------------------------------------------------

open valid_operations

/--
Example program on `exampleState`:

1. addWithCarry R0 R1
2. shiftL R0
3. phaseProduct (no-op)
4. negate width 4 on R0
-/
def exampleProg : List (valid_operations 2) :=
  [ valid_operations.addWithCarry 0 1,
    valid_operations.shiftL 0,
    valid_operations.phaseProduct,
    valid_operations.negate 4 0 ]

def exampleAfterProg : State 2 :=
  valid_operations.applySeq exampleState exampleProg

#eval printState exampleState
#eval printState exampleAfterProg




inductive Program (k : ℕ) : Type where
  | skip : Program k
  | op   : valid_operations k → Program k
  | seq  : Program k → Program k → Program k
deriving Repr

namespace Program

open valid_operations

/-- Big-step semantics for programs. -/
def eval {k : ℕ} (p : Program k) (σ : State k) : State k :=
  match p with
  | Program.skip      => σ
  | Program.op o      => valid_operations.apply o σ
  | Program.seq p q   => eval q (eval p σ)

/-- Notation for sequencing: `p ;; q`. -/
infixr:60 " ;; " => Program.seq

/-- Build a Program from a list of operations (run left-to-right). -/
def fromOps {k : ℕ} (ops : List (valid_operations k)) : Program k :=
  ops.foldr (fun o acc => Program.seq (Program.op o) acc) Program.skip

end Program

open valid_operations Program

/--
Example "program":

1. R0 ← R0 + R1  (with carry)
2. shiftL R0
3. phaseProduct (no-op)
4. negate width 4 on R0
-/
def progExample : Program 2 :=
  Program.op (addWithCarry 0 1) ;;
  Program.op (shiftL 0) ;;
  Program.op phaseProduct;;
  Program.op (negate 5 1);;
  Program.op (addNoCarry 0 1) ;;
  Program.op (negate 5 1)

/-- Run `progExample` on `exampleState`. -/
def exampleAfterProg2 : State 2 :=
  Program.eval progExample exampleState

#eval printState exampleState
#eval printState exampleAfterProg2

end Qubit_level
