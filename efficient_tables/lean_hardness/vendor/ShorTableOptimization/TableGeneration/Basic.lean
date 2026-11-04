namespace TableGeneration

abbrev Register (k : Nat) := Fin k -> Int

abbrev State (k : Nat) := Fin k -> Register k

namespace Register

def zero (k : Nat) : Register k := fun _ => 0

def negate {k : Nat} (r : Register k) : Register k :=
  fun j => -r j

def shiftL {k : Nat} (r : Register k) (n : Nat) : Register k :=
  fun j => r j * (2 : Int) ^ n

def shiftR? {k : Nat} (r : Register k) (n : Nat) : Option (Register k) :=
  let m : Int := (2 : Int) ^ n
  if (List.finRange k).all (fun j => decide (r j % m = 0)) then
    some (fun j => r j / m)
  else
    none

def addScaled {k : Nat} (dst src : Register k) (negSrc : Bool) (shift : Nat) :
    Register k :=
  let sign : Int := if negSrc then -1 else 1
  fun j => dst j + sign * src j * (2 : Int) ^ shift

end Register

namespace State

def start_state {k : Nat} : State k :=
  fun i j => if j = i then 1 else 0

def setReg {k : Nat} (sigma : State k) (i : Fin k) (r : Register k) : State k :=
  fun j => if j = i then r else sigma j

def negateReg {k : Nat} (sigma : State k) (i : Fin k) : State k :=
  setReg sigma i (Register.negate (sigma i))

def shiftLReg {k : Nat} (sigma : State k) (i : Fin k) (n : Nat) : State k :=
  setReg sigma i (Register.shiftL (sigma i) n)

def shiftRReg? {k : Nat} (sigma : State k) (i : Fin k) (n : Nat) : Option (State k) := do
  let r <- Register.shiftR? (sigma i) n
  pure (setReg sigma i r)

def addScaledReg {k : Nat} (sigma : State k)
    (dst src : Fin k) (negSrc : Bool) (shift : Nat) : State k :=
  setReg sigma dst (Register.addScaled (sigma dst) (sigma src) negSrc shift)

end State

namespace Operations

inductive Point where
  | int (z : Int)
  | frac (m : Int)
deriving DecidableEq, Repr

inductive valid_ops (k : Nat) where
  | shiftL (i : Fin k) (n : Nat)
  | shiftR (i : Fin k) (n : Nat)
  | negate (i : Fin k)
  | addScaled (dst src : Fin k) (negSrc : Bool) (shift : Nat)
  | phaseProduct (i : Fin k)
deriving DecidableEq, Repr

def inv {k : Nat} : valid_ops k -> valid_ops k
  | .shiftL i n => .shiftR i n
  | .shiftR i n => .shiftL i n
  | .negate i => .negate i
  | .addScaled dst src negSrc shift => .addScaled dst src (!negSrc) shift
  | .phaseProduct i => .phaseProduct i

end Operations

end TableGeneration
