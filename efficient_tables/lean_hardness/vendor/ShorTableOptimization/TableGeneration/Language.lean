import TableGeneration.Basic

namespace TableGeneration

open Operations

abbrev Prog (k : Nat) := List (valid_ops k)

def applyOp? {k : Nat} (sigma : State k) : valid_ops k -> Option (State k)
  | .shiftL i n => some (State.shiftLReg sigma i n)
  | .shiftR i n => State.shiftRReg? sigma i n
  | .negate i => some (State.negateReg sigma i)
  | .addScaled dst src negSrc shift => some (State.addScaledReg sigma dst src negSrc shift)
  | .phaseProduct _ => some sigma

def apply_Op_inverse {k : Nat} (p : Prog k) : Prog k :=
  p.reverse.map Operations.inv

def run? {k : Nat} : Prog k -> State k -> Option (State k)
  | [], sigma => some sigma
  | op :: ops, sigma =>
      match applyOp? sigma op with
      | none => none
      | some sigma' => run? ops sigma'

namespace Prog

def OpOK {k : Nat} : valid_ops k -> Prop
  | .addScaled dst src _ _ => Not (dst = src)
  | _ => True

def OpOK? {k : Nat} : valid_ops k -> Bool
  | .addScaled dst src _ _ => decide (Not (dst = src))
  | _ => true

def wellFormed? {k : Nat} : Prog k -> Bool
  | [] => true
  | op :: ops => OpOK? op && wellFormed? ops

def SHL {k : Nat} (i : Fin k) (n : Nat) : Prog k := [.shiftL i n]

def SHR {k : Nat} (i : Fin k) (n : Nat) : Prog k := [.shiftR i n]

def NEG {k : Nat} (i : Fin k) : Prog k := [.negate i]

def ADD {k : Nat} (dst src : Fin k) (shift : Nat) : Prog k :=
  [.addScaled dst src false shift]

def SUB {k : Nat} (dst src : Fin k) (shift : Nat) : Prog k :=
  [.addScaled dst src true shift]

end Prog

def safeProg? {k : Nat} (ops : Prog k) : Bool :=
  Prog.wellFormed? ops

def expectedRow {k : Nat} : Point -> Register k
  | .int z => fun j => z ^ j.val
  | .frac m => fun j => m ^ (k - 1 - j.val)

def regEqExpected {k : Nat} (r : Register k) (pt : Point) : Bool :=
  (List.finRange k).all (fun j => decide (r j = expectedRow (k := k) pt j))

def matchesAt_pointRow_state {k : Nat} (_hk : k > 0) : State k -> Fin k -> Point -> Bool :=
  fun sigma i pt => regEqExpected (k := k) (sigma i) pt

def progConsumesPts? {k : Nat} (hk : k > 0) : State k -> Prog k -> List Point -> Bool
  | _sigma, [], [] => true
  | _sigma, [], _ :: _ => false
  | sigma, op :: ops, pts =>
      match op with
      | .phaseProduct i =>
          match pts with
          | [] => false
          | pt :: rest =>
              matchesAt_pointRow_state (k := k) hk sigma i pt &&
                progConsumesPts? hk sigma ops rest
      | _ =>
          match applyOp? sigma op with
          | none => false
          | some sigma' => progConsumesPts? hk sigma' ops pts

def statesEqual {k : Nat} (left right : State k) : Bool :=
  (List.finRange k).all fun i =>
    (List.finRange k).all fun j => decide (left i j = right i j)

def returnsToStartCheck {k : Nat} (ops : Prog k) (sigma : State k) : Bool :=
  match run? ops sigma with
  | none => false
  | some sigma' => statesEqual sigma' sigma

structure ProgConsumesPtsSafe {k : Nat} (hk : k > 0)
    (sigma : State k) (ops : Prog k) (pts : List Point) : Prop where
  consumes : progConsumesPts? hk sigma ops pts = true
  safe_add : safeProg? ops = true
  returns_start : returnsToStartCheck ops sigma = true

theorem progConsumesPtsSafe_of_checks {k : Nat} {hk : k > 0}
    {sigma : State k} {ops : Prog k} {pts : List Point}
    (hconsumes : progConsumesPts? hk sigma ops pts = true)
    (hsafe : safeProg? ops = true)
    (hreturns : returnsToStartCheck ops sigma = true) :
    ProgConsumesPtsSafe hk sigma ops pts where
  consumes := hconsumes
  safe_add := hsafe
  returns_start := hreturns

def finZero {k : Nat} (hk : 0 < k) : Fin k :=
  { val := 0, isLt := hk }

theorem last_lt {k : Nat} (hk : 0 < k) : k - 1 < k := by
  cases k with
  | zero => cases hk
  | succ n => simp

theorem positive_of_ge_two {k : Nat} (hk : k >= 2) : k > 0 :=
  Nat.lt_of_lt_of_le (by decide : 0 < 2) hk

def finLast {k : Nat} (hk : 0 < k) : Fin k :=
  { val := k - 1, isLt := last_lt hk }

def pointDst {k : Nat} (hk : 0 < k) : Point -> Fin k
  | .int _ => finZero hk
  | .frac _ => finLast hk

def showFin {k : Nat} (i : Fin k) : String :=
  toString i.val

def opToString {k : Nat} : valid_ops k -> String
  | .shiftL i n => s!"(shiftL, reg={showFin i}, by={n})"
  | .shiftR i n => s!"(shiftR, reg={showFin i}, by={n})"
  | .negate i => s!"(negate, reg={showFin i})"
  | .addScaled dst src negSrc shift =>
      let sign := if negSrc then "-" else "+"
      s!"(addScaled, dst={showFin dst}, src={showFin src}, sign={sign}1, shift={shift})"
  | .phaseProduct i => s!"(phaseProduct, reg={showFin i})"

def joinComma : List String -> String
  | [] => "[]"
  | x :: xs => "[" ++ xs.foldl (fun acc s => acc ++ ", " ++ s) x ++ "]"

def progToString {k : Nat} (p : Prog k) : String :=
  joinComma (p.map opToString)

def pointToString : Point -> String
  | .int z => toString z
  | .frac m =>
      if m = 0 then "inf"
      else if m < 0 then "-1/" ++ toString (-m)
      else "1/" ++ toString m

end TableGeneration
