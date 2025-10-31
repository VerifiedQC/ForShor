import FastMultiplication.Lemmas_and_Theorems



-- /******************************************************************************/
-- /*                DEFINING BASIC SYNTHESIS PROGRAM                            */
-- /******************************************************************************/
open Operations



def shiftsOfAux : Nat → Nat → List Nat
| 0,      _  => []
| n+1,    sh =>
  let rest := shiftsOfAux ((n+1) / 2) (sh+1)
  if Nat.bodd (n+1) then sh :: rest else rest
-- termination_by n _ => n
-- decreasing_by
--   -- simplify the well-founded goal then show (n+1)/2 < (n+1)
--   exact Nat.div_lt_self (Nat.succ_pos _) (by decide)


def shiftsOf (n : Nat) : List Nat := shiftsOfAux n 0
--#eval shiftsOf 24  -- expects [3, 4]

/-- Signed power-of-two decomposition.
    Returns a list of `(neg, shift)` so that
    `c = ∑ (if neg then -1 else +1) * 2^shift`. -/
def signedPow2Decomp (c : Int) : List (Bool × Nat) :=
  if c = 0 then
    []
  else
    let neg'  : Bool := c < 0
    let mag  : Nat  := Int.natAbs c
    (shiftsOf mag).map (fun sh => (neg', sh))

/-- Finite index `0 : Fin k` when `k > 0`. -/
def finZero {k : Nat} (hk : 0 < k) : Fin k := ⟨0, hk⟩

/-- All source registers `j = 1..k-1` (i.e. finRange minus `0`). -/
def nonzeroFins {k : Nat} (hk : 0 < k) : List (Fin k) :=
  (List.finRange k).filter (fun j => decide (j ≠ finZero hk))

/-- Turn a `(neg, shift)` pair into one `addScaled` op: `dst += ± (src << shift)`. -/
def pairToOp {k : Nat} (dst src : Fin k) : (Bool × Nat) → valid_ops k
| (neg', sh) => valid_ops.addScaled dst src (negSrc := neg') sh


/-- Tiny helper: if `p head` is true, the eraser drops the head. -/
@[simp] lemma eraseFirstMatch?_head_true {α} (p : α → Bool) (x : α) (xs : List α)
  (hx : p x = true) :
  List.eraseFirstMatch? p (x :: xs) = some xs := by
  simp [List.eraseFirstMatch?, hx]



/-- Accumulate all contributions for `.int z` into `dst = 0`, **no uncompute yet**. -/
def computeLocal {k : Nat} (hk : 0 < k) (z : Int) : Prog k :=
  let dst := finZero hk
  (nonzeroFins hk).foldl
    (fun acc (j:Fin k) =>
      let c : Int := z ^ (j : Nat)
      if c = 0 then acc
      else acc ++ (signedPow2Decomp c).map (pairToOp dst j))
    ([] : Prog k)

/-- One block per point: build row in reg 0, mark it, then uncompute. -/
def opsForPointWithProduct {k : Nat} (hk : 0 < k) : Point → Prog k
| .inf   =>
    let last : Fin k := ⟨k-1, by have : 0 < k := hk; exact Nat.sub_lt (Nat.succ_le_of_lt this) (by decide)⟩
    [valid_ops.phaseProduct last]
| .int z =>
  let dst   := finZero hk
  let l := computeLocal hk z
  l ++ [valid_ops.phaseProduct dst] ++ apply_Op_inverse l

/-- Generator that **does** include the `phaseProduct` checkpoints. -/
def genOpsWithProduct {k : Nat} (hk : 0 < k) (points : List Point) : Prog k :=
  points.foldl (fun acc pt => acc ++ opsForPointWithProduct hk pt) ([] : Prog k)
