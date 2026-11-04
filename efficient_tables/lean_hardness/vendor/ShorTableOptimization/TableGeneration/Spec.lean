import TableGeneration.Language

namespace TableGeneration

open Operations

inductive ProductMode where
  | PhaseProduct
  | PhaseTripleProduct
deriving DecidableEq, Repr

def ProductMode.pointCount : ProductMode -> Nat -> Nat
  | .PhaseProduct, k => 2 * k - 1
  | .PhaseTripleProduct, k => 3 * k - 2

def canonicalPoint : Nat -> Point
  | 0 => .int 0
  | 1 => .frac 0
  | 2 => .int 1
  | 3 => .int (-1)
  | n + 4 =>
      let e := 1 + n / 4
      match n % 4 with
      | 0 => .int ((2 : Int) ^ e)
      | 1 => .int (-((2 : Int) ^ e))
      | 2 => .frac ((2 : Int) ^ e)
      | _ => .frac (-((2 : Int) ^ e))

def canonicalPoints (mode : ProductMode) (k : Nat) : List Point :=
  (List.range (mode.pointCount k)).map canonicalPoint

def natPowerOfTwoFuel : Nat -> Nat -> Bool
  | 0, n => n == 1
  | fuel + 1, n =>
      if n == 0 then
        false
      else if n == 1 then
        true
      else if n % 2 == 0 then
        natPowerOfTwoFuel fuel (n / 2)
      else
        false

def natPowerOfTwo? (n : Nat) : Bool :=
  natPowerOfTwoFuel n n

def signedPowerOfTwo? (z : Int) : Bool :=
  if z == 0 then false else natPowerOfTwo? (Int.natAbs z)

def validPoint? : Point -> Bool
  | .int z => z == 0 || signedPowerOfTwo? z
  | .frac m => m == 0 || signedPowerOfTwo? m

def normalizePoint : Point -> Point
  | .frac m =>
      if m = 1 then
        .int 1
      else if m = -1 then
        .int (-1)
      else
        .frac m
  | pt => pt

def ValidPointList (mode : ProductMode) (k : Nat) (pts : List Point) : Prop :=
  pts.length = mode.pointCount k /\
    (pts.map normalizePoint).Nodup /\
    pts.all validPoint? = true

def ValidPointOrder (generated pts : List Point) : Prop :=
  pts.Perm generated

end TableGeneration
