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



/-- Pretty label for the Bool flag: `true` = LSB, `false` = MSB. -/
def endLabel (lsb : Bool) : String :=
  if lsb then "LSB" else "MSB"

/-- Pretty-print a single primitive op. -/
def formatPrimOp {k : ℕ} : prim_ops k → String
  | prim_ops.Alloc i lsb n =>
      s!"Alloc(reg={i.val}, end={endLabel lsb}, n={n})"
  | prim_ops.Free i lsb n  =>
      s!"Free(reg={i.val}, end={endLabel lsb}, n={n})"
  | prim_ops.negate i      =>
      s!"Negate(reg={i.val})"
  | prim_ops.Add dst src   =>
      s!"Add(dst={dst.val}, src={src.val})"
  | prim_ops.phaseProduct i =>
      s!"PhaseProduct(reg={i.val})"

/-- Format ops with line numbers (no `List.enum` needed). -/
def formatPrimOps {k : ℕ} (ops : List (prim_ops k)) : String :=
  let rec go (idx : Nat) (xs : List (prim_ops k)) : List String :=
    match xs with
    | [] => []
    | op :: tail => s!"{idx}: {formatPrimOp op}" :: go (idx + 1) tail
  String.intercalate "\n" (go 0 ops)

def printPrimOps {k : ℕ} (ops : List (prim_ops k)) : IO Unit :=
  IO.println (formatPrimOps ops)

----------------------------------------------------------------------------------------------------
------------------------------- ARITHEMTIC OPERATORS -----------------------------------------------
----------------------------------------------------------------------------------------------------

def AllocLSB (σ : St k) (reg: Fin k) (n:ℕ): St k:=
  fun (i:Fin k)=>
  if i=reg then
    ⟨(σ reg).1+n,BitVec.append (σ reg).2 (BitVec.zero n)⟩
  else
    σ i

def AllocMSB (σ : St k) (reg : Fin k) (n : ℕ) : St k :=
  fun i =>
  if i = reg then
    let val := σ reg
    ⟨n + val.1, val.2.signExtend (n + val.1)⟩
  else
    σ i

def Adder {k:ℕ} (σ : St k) (dst src: Fin k) :=
  fun (i:Fin k) =>
    if i=dst then
      ⟨(σ dst).1,BitVec.add (σ dst).2 (BitVec.truncate ((σ dst).1) (σ src).2)⟩
    else
      σ i

def Negation {k:ℕ} (σ : St k) (dst: Fin k) :=
  fun (i:Fin k) =>
    if i=dst then
      ⟨(σ dst).1,BitVec.neg (σ dst).2⟩
    else
      σ i

def FreeLSB (σ : St k) (reg : Fin k) (n : ℕ) : St k :=
  fun i =>
    if i = reg then
      let w  := (σ reg).fst
      let bv := (σ reg).snd
      let w' := w - n
      ⟨w', BitVec.ofNat w' (bv.toNat / (2 ^ n))⟩
    else
      σ i


def FreeMSB  (σ : St k) (reg: Fin k) (n:ℕ): St k:=
  fun (i:Fin k)=>
  if i=reg then
    ⟨(σ reg).1-n,(BitVec.truncate ((σ reg).1-n) (σ reg).2)⟩
  else
    σ i


#eval printState (AllocLSB demo 1 3)
#eval printState (AllocMSB demo 2 4)

#eval printState demo
#eval printState (Adder (Adder (Negation demo 1) 1 2) 0 1)
#eval printState (Adder demo 1 2)

#eval printState (FreeMSB demo 1 1)

#eval printState (FreeLSB demo 2 1)


----------------------------------------------------------------------------------------------------
------------------------------- Evaluation of PrimOps -----------------------------------------------
----------------------------------------------------------------------------------------------------

def eval_prim_op_single (op:prim_ops k) (σ: St k):=
match op with
  | prim_ops.Alloc i lsb n =>  if lsb then AllocLSB σ i n else AllocMSB σ i n
  | prim_ops.Free i lsb n  =>  if lsb then FreeLSB σ i n else FreeMSB σ i n
  | prim_ops.negate i      =>  Negation σ i
  | prim_ops.Add dst src   =>  Adder σ dst src
  | prim_ops.phaseProduct _ => σ


def eval_prim_ops (ops:List (prim_ops k)) (σ: St k):=
match ops with
|List.nil => σ
|List.cons head tail =>  eval_prim_ops tail (eval_prim_op_single head σ)

open Operations

/-- Set the `idx`-th entry of a list (if in range). Otherwise leave the list unchanged. -/
def setAt {α : Type} : List α → Nat → α → List α
  | [],      _,      _ => []
  | _ :: xs, 0,      a => a :: xs
  | x :: xs, idx+1,  a => x :: setAt xs idx a
/-- Get `lens[idx]` with a default if out of range. -/
def getLen (curLen : List Nat) (idx : Nat) : Nat :=
  curLen.getD idx 1

def setLen {k : ℕ} (curLen : List Nat) (i : Fin k) (v : Nat) : List Nat :=
  setAt curLen i.val v

def incLen {k : ℕ} (curLen : List Nat) (i : Fin k) (n : Nat) : List Nat :=
  setLen curLen i (getLen curLen i.val + n)

def decLen {k : ℕ} (curLen : List Nat) (i : Fin k) (n : Nat) : List Nat :=
  setLen curLen i (getLen curLen i.val - n)

def compile_op_to_prim_single {k : ℕ} (op : valid_ops k) (curLen : List Nat) :
    (List (prim_ops k)) × (List Nat) × (List (Fin k × Nat)) :=
match op with
  | .shiftL i n =>
      -- LSB shift scaffolding => lsb = true in your evaluator
      ([prim_ops.Alloc i true n], incLen curLen i n, [])

  | .shiftR i n =>
      ([prim_ops.Free i true n], decLen curLen i n, [])

  | .negate i =>
      ([prim_ops.negate i], curLen, [])

  | .phaseProduct i =>
      ([prim_ops.phaseProduct i], curLen, [])

  | .addScaled dst src negSrc sh =>
      if dst = src then
        ([], curLen, [])
      else
        let negops : List (prim_ops k) :=
          if negSrc then [prim_ops.negate src] else []

        -- (1) optional negate(src)
        let curLen1 := curLen

        -- (2) src <<= sh  (LSB alloc)
        let shiftOps : List (prim_ops k) :=
          if sh = 0 then [] else [prim_ops.Alloc src true sh]
        let curLen2 := incLen curLen1 src sh

        -- lengths after negate (no change) + shift
        let lenDst := getLen curLen2 dst.val
        let lenSrc := getLen curLen2 src.val

        -- (3) choose safe width for ONE signed add
        let target := 1 + Nat.max lenDst lenSrc

        -- (4a) widen dst at MSB to target (remember to free at end)
        let deltaDst := target - lenDst
        let widenDstOps : List (prim_ops k) :=
          if deltaDst = 0 then [] else [prim_ops.Alloc dst false deltaDst]
        let curLen3 := incLen curLen2 dst deltaDst
        let msbAdds : List (Fin k × Nat) :=
          if deltaDst = 0 then [] else [(dst, deltaDst)]

        -- (4b) widen src at MSB to target (temporary; free right after Add)
        let deltaSrc := target - lenSrc
        let widenSrcOps : List (prim_ops k) :=
          if deltaSrc = 0 then [] else [prim_ops.Alloc src false deltaSrc]
        let curLen4 := incLen curLen3 src deltaSrc

        -- (5) dst += src
        let adder : List (prim_ops k) := [prim_ops.Add dst src]

        -- (6) undo src MSB widen
        let freeSrcOps : List (prim_ops k) :=
          if deltaSrc = 0 then [] else [prim_ops.Free src false deltaSrc]
        let curLen5 := decLen curLen4 src deltaSrc

        -- (7) undo shift (LSB free)
        let unShiftOps : List (prim_ops k) :=
          if sh = 0 then [] else [prim_ops.Free src true sh]
        let curLen6 := decLen curLen5 src sh

        -- (8) undo negate(src)
        let unNegOps : List (prim_ops k) := negops
        let curLen7 := curLen6

        (negops ++ shiftOps ++ widenDstOps ++ widenSrcOps ++ adder ++ freeSrcOps ++ unShiftOps ++ unNegOps,
         curLen7,
         msbAdds)

def compile_valid_ops {k : ℕ} (ops : List (valid_ops k)) :
    List (prim_ops k) :=
  let initLen : Nat := 0
  let initCurLen : List Nat := List.replicate k initLen

  -- main loop: build primOps in forward order (we'll accumulate with ++ for clarity)
  let rec go (ops : List (valid_ops k))
             (curLen : List Nat)
             (msbStack : List (Fin k × Nat))
             (out : List (prim_ops k)) : List (prim_ops k) :=
    match ops with
    | [] =>
        let frees : List (prim_ops k) :=
          msbStack.map (fun p => prim_ops.Free p.1 false p.2)
        out ++ frees
    | op :: ops' =>
        let (ops1, curLen1, msbAdds) := compile_op_to_prim_single (k := k) op curLen
        let msbStack1 := msbAdds ++ msbStack
        go ops' curLen1 msbStack1 (out ++ ops1)

  go ops initCurLen [] []


def compile1 {k : ℕ} (op : valid_ops k) (curLen : List Nat) :
    List (prim_ops k) × List Nat :=
  let (ops, curLen', _msbAdds) := compile_op_to_prim_single (k := k) op curLen
  (ops, curLen')


namespace DemoValidOps
-- handy Fin indices for k = 3
def r0 : Fin 3 := ⟨0, by decide⟩
def r1 : Fin 3 := ⟨1, by decide⟩
def r2 : Fin 3 := ⟨2, by decide⟩

/--
A small program:
1) r0 += r1
2) r0 += (r2 << 1)
3) PhaseProduct on r0 (no classical effect in your eval)
4) r0 -= r1   (negSrc=true)
5) r2 <<= 2
6) r2 >>= 1
7) negate r1
-/
def prog : List (valid_ops 3) :=
[
  valid_ops.addScaled r0 r1 false 0,
  valid_ops.addScaled r0 r2 false 1,
  valid_ops.phaseProduct r0,
  valid_ops.addScaled r0 r1 true  0,
  valid_ops.shiftL r2 2,
  valid_ops.shiftR r2 1,
  valid_ops.negate r1
]

lemma h3:0<3:=by simp
def vop1:=(genOpsWithProduct h3 [Point.int 0, Point.inf, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2)])
def pop1:=compile_valid_ops vop1

#eval printPrimOps pop1
#eval printState (eval_prim_ops (pop1.take 9) demo)
-- def demo : St 3 :=
--   fun i =>
--     match i.val with
--     | 0 => mkReg 5 15  -- 01111 = +15
--     | 1 => mkReg 5  6  -- 00110 = +6
--     | _ => mkReg 5 24  -- 11000 = -8 (24 - 32)

def compiled_prog:=compile_valid_ops prog

#eval printPrimOps compiled_prog
#eval printState (eval_prim_ops (compiled_prog) demo)



-- def bitsFreedAllEq {w : Nat} (bv : BitVec w) (lsb : Bool) (n : Nat) (target : Bool) : Bool :=
--   if _h : n ≤ w then
--     let base : Nat := if lsb then 0 else (w - n)
--     (List.range n).all (fun j => (Nat.testBit bv.toNat (base + j)) == target)
--   else
--     false


-- def validFreeStep {w : Nat} (bv : BitVec w) (lsb : Bool) (n : Nat) : Bool :=
--   if lsb then
--     bitsFreedAllEq bv true n false
--   else
--     bitsFreedAllEq bv false n bv.msb


-- def validFree {k : Nat} (ops : List (prim_ops k)) (σ0 : St k) : Bool :=
--   let rec go (ops : List (prim_ops k)) (σ : St k) : Bool :=
--     match ops with
--     | [] => true
--     | op :: tail =>
--         match op with
--         | prim_ops.Free i lsb n =>
--             let ⟨_, bv⟩ := σ i
--             if validFreeStep bv lsb n then
--               go tail (eval_prim_op_single (k := k) op σ)
--             else
--               false
--         | _ =>
--             go tail (eval_prim_op_single (k := k) op σ)
--   go ops σ0


-- #eval validFree pop1 demo
