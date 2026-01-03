import FastMultiplication.one_reg_synth_proof_2
import Mathlib.Data.Bitvec
import Mathlib.Data.Fin.Basic

inductive prim_ops (k : ℕ) where
  | Alloc         (i : Fin k) (lsb: Bool) (n : ℕ)
  | Free          (i : Fin k) (lsb: Bool) (n : ℕ)
  | negate        (i : Fin k)
  | Add           (dst src : Fin k)
  | phaseProduct  (i : Fin k)

/-- A single register with an arbitrary (stored) bitwidth. -/
abbrev Reg := Σ w : ℕ, BitVec w

/-- A `k`-register state with potentially different widths per register. -/
abbrev St (k : ℕ) := Fin k → Reg


----------------------------------------------------------------------------------------------------
------------------------------- FORMATTED PRINTER --------------------------------------------------
----------------------------------------------------------------------------------------------------
/-- Convenience constructor: make a `Reg` of width `w` storing `x` mod `2^w`. -/
def mkReg (w : Nat) (x : Nat) : Reg :=
  ⟨w, BitVec.ofNat w x⟩

/-- Render a Bool as `'0'`/`'1'`. -/
def bitChar (b : Bool) : Char := if b then '1' else '0'
def getLsb {w : ℕ} (bv : BitVec w) (i : Fin w) : Bool :=
  Nat.testBit bv.toNat i.val
/-- MSB-left binary string for a `BitVec w`. -/
def bitVecToBin {w : ℕ} (bv : BitVec w) : String :=
  let chars : List Char :=
    ((List.finRange w).reverse).map (fun i => bitChar (getLsb bv i))
  String.mk chars

/-- Format one variable-width register. -/
def formatReg (idx : Nat) (r : Reg) : String :=
  match r with
  | ⟨w, bv⟩ =>
      let signed : Int := BitVec.toInt bv
      let signedBits : Nat := w.succ.pred  -- = w-1 when w>0, else 0
      s!"{idx}: {bitVecToBin bv}  (signed={signed}, storedBits={w}, signedBits={signedBits})"

/-- Pretty-print a whole state. -/
def formatState {k : ℕ} (σ : St k) : String :=
  let lines : List String :=
    (List.finRange k).map (fun i => formatReg i.val (σ i))
  String.intercalate "\n" lines

def printState {k : ℕ} (σ : St k) : IO Unit :=
  IO.println (formatState σ)

def demo : St 3 :=
  fun i =>
    match i.val with
    | 0 => mkReg 5 15  -- 01111 = +15
    | 1 => mkReg 5  6  -- 00110 = +6
    | _ => mkReg 5 24  -- 11000 = -8 (24 - 32)

#eval printState demo


----------------------------------------------------------------------------------------------------
------------------------------- ARITHEMTIC OPERATORS -----------------------------------------------
----------------------------------------------------------------------------------------------------







open Operations

-- def compile_op_to_prim {k : ℕ} (op: valid_ops k):=
-- match op with
--   | .shiftL i n =>
--       [prim_ops.Alloc i false n]

--   | .shiftR i n =>
--       [prim_ops.Free i false n]

--   | .negate i =>
--       [prim_ops.negate i]

--   | .phaseProduct i =>
--       [prim_ops.phaseProduct i]

--   | .addScaled dst src negSrc sh =>
--       if dst = src then
--         []
--       else
--         let negops:=
--           if negSrc then [prim_ops.negate src] else []
--         let shiftOps:=
--           [prim_ops.Alloc src true sh]

--         let adder:=
--           [prim_ops.Add dst src]
--         let inv:=
--           [prim_ops.Alloc src true sh]++negops
--         negops++shiftOps++adder++inv
