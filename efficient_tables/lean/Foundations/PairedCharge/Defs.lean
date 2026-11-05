import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Field.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace PairedCharge

/-- Projective point of the line: a rational or infinity. -/
inductive Pt where
  | fin : ℚ → Pt
  | inf : Pt

/-- The infinite list `0, ∞, -1, 1, -2^{-1}, 2^{-1}, -2^1, 2^1, ...`. -/
noncomputable def pointAt (i : ℕ) : Pt :=
  if i = 0 then Pt.fin 0
  else if i = 1 then Pt.inf
  else if i = 2 then Pt.fin (-1)
  else if i = 3 then Pt.fin 1
  else
    match i % 4 with
    | 0 => Pt.fin (-(2 : ℚ) ^ (-((i / 4 : ℕ) : ℤ)))
    | 1 => Pt.fin ((2 : ℚ) ^ (-((i / 4 : ℕ) : ℤ)))
    | 2 => Pt.fin (-(2 : ℚ) ^ ((i / 4 : ℕ) : ℤ))
    | _ => Pt.fin ((2 : ℚ) ^ ((i / 4 : ℕ) : ℤ))

/-- Negative fractional: `-2^{-j}` with `j ≥ 1`. -/
def IsNegFrac (x : Pt) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ x = Pt.fin (-(2 : ℚ) ^ (-(j : ℤ)))

open Classical in
/-- Number of negative fractional points among `p_0,…,p_{2k-2}`. -/
noncomputable def fMinus (k : ℕ) : ℕ :=
  ((Finset.range (2 * k - 1)).filter (fun i => IsNegFrac (pointAt i))).card

inductive Instr where
  | posAdd | negAdd | negation | shift | checkpoint

def Instr.charge : Instr → ℕ
  | .posAdd => 1
  | .negAdd => 3
  | .negation => 1
  | .shift => 0
  | .checkpoint => 0

def listCharge (l : List Instr) : ℕ := (l.map Instr.charge).sum

def pairBlock (k : ℕ) : List Instr :=
  List.replicate (k - 2) Instr.posAdd ++ [Instr.posAdd, Instr.negAdd, Instr.posAdd] ++
    List.replicate (k - 2) Instr.negAdd

def singletonBlock (k : ℕ) : List Instr :=
  List.replicate (k - 1) Instr.posAdd ++ List.replicate (k - 1) Instr.negAdd

open Classical in
/-- Skeleton list for arity `k`. -/
noncomputable def skeleton (k : ℕ) : List Instr :=
  [Instr.checkpoint, Instr.checkpoint] ++
  (List.replicate (k - 2) (pairBlock k)).flatten ++
  singletonBlock k ++
  List.replicate
    (if Even k then
      2 * ((Finset.Ico 2 (2 * k - 1)).filter (fun i => IsNegFrac (pointAt i))).card
     else 0) Instr.negation

noncomputable def cPair (k : ℕ) : ℕ := listCharge (skeleton k)

noncomputable def nu (k : ℕ) : ℕ :=
  if Even k then 2 * fMinus k else 0

end PairedCharge
