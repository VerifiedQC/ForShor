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

-- /-- One block per point: build row in reg 0, mark it, then uncompute. -/
-- def opsForPointWithProduct {k : Nat} (hk : 0 < k) : Point → Prog k
-- | .inf   =>
--     let last : Fin k := ⟨k-1, by have : 0 < k := hk; exact Nat.sub_lt (Nat.succ_le_of_lt this) (by decide)⟩
--     [valid_ops.phaseProduct last]
-- | .int z =>
--   let dst   := finZero hk
--   let l := computeLocal hk z
--   l ++ [valid_ops.phaseProduct dst] ++ apply_Op_inverse l

-- /-- Generator that **does** include the `phaseProduct` checkpoints. -/
-- def genOpsWithProduct {k : Nat} (hk : 0 < k) (points : List Point) : Prog k :=
--   points.foldl (fun acc pt => acc ++ opsForPointWithProduct hk pt) ([] : Prog k)

--New synthesis program (no folds)

open Operations

/-- Internal block: add `dst += (± 2^sh) * n • src`, compiled structurally by halving `n`. -/
def addConstAux {k : Nat} (dst src : Fin k) (neg' : Bool) :
    (n sh : Nat) → Prog k
| 0,      _  => []
| n+1,    sh =>
  let rest := addConstAux dst src neg' ((n+1)/2) (sh+1)
  if Nat.bodd (n+1) then
    valid_ops.addScaled dst src (negSrc := neg') sh :: rest
  else
    rest
termination_by n _ => n
decreasing_by
  simp_wf
  exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

/-- Top-level constant adder: emit ops for `dst := dst + c • src`. -/
def addConstFrom {k : Nat} (dst src : Fin k) (c : Int) : Prog k :=
  if c = 0 then []
  else
    let neg' := c < 0
    let n   := Int.natAbs c
    addConstAux dst src neg' n 0

/-- Compute local Vandermonde row into `dst = finZero hk` by explicit recursion on sources. -/
def computeLocalAux {k : Nat} (hk : 0 < k) (z : Int) :
    List (Fin k) → Prog k
| []       => []
| j :: js  =>
  let c := z ^ (j : Nat)
  let head := addConstFrom (finZero hk) j c
  head ++ computeLocalAux hk z js

/-- Public wrapper (no folds). -/
def computeLocal2 {k : Nat} (hk : 0 < k) (z : Int) : Prog k :=
  computeLocalAux hk z (nonzeroFins hk)

/-- Push an `if` guarding a tail list out through append. -/
lemma append_ite_nil_eq {β} (acc : List β) (P : Prop) [Decidable P] (L : List β) :
  acc ++ (if P then [] else L) = (if P then acc else acc ++ L) := by
  by_cases h : P <;> simp [h]

/-- helper: `pairToOp` with fixed sign equals the direct constructor on shifts. -/
@[simp] lemma pairToOp_fixed {k} (dst src : Fin k) (neg' : Bool) :
  (fun s : Nat => pairToOp (k := k) dst src (neg', s))
  = (fun s : Nat => valid_ops.addScaled dst src (negSrc := neg') s) := by
  funext s; simp [pairToOp]


/-- Structural equality: `addConstAux` enumerates exactly the shifts that
    `shiftsOfAux` does, mapping each shift `s` to `addScaled … s`. -/
lemma addConstAux_eq_shifts {k}
    (dst src : Fin k) (neg' : Bool) :
  ∀ n sh,
    addConstAux (k := k) dst src neg' n sh
      =
    (shiftsOfAux n sh).map (fun s => valid_ops.addScaled dst src (negSrc := neg') s)
| 0,      sh => by
  simp [addConstAux, shiftsOfAux]
| (n+1),  sh => by
  -- IH on the structurally smaller arguments ((n+1)/2, sh+1)
  have ih :
      addConstAux (k := k) dst src neg' ((n+1)/2) (sh+1)
        =
      (shiftsOfAux ((n+1)/2) (sh+1)).map
        (fun s => valid_ops.addScaled dst src (negSrc := neg') s) :=
    addConstAux_eq_shifts (k := k) (dst := dst) (src := src) (neg' := neg') ((n+1)/2) (sh+1)

  by_cases hb : Nat.bodd (n+1)
  · -- odd case: emit a head at `sh`, then the tail
    simp [addConstAux, shiftsOfAux, ih]
    aesop
  · -- even case: just the tail
    simp [addConstAux, shiftsOfAux, ih]
    aesop


lemma addConstFrom_eq_signedPow2Map {k}
    (dst src : Fin k) (c : Int) :
  addConstFrom (k := k) dst src c
    =
  (if c = 0 then [] else (signedPow2Decomp c).map (pairToOp (k := k) dst src)) := by
  classical
  by_cases hc : c = 0
  · simp [addConstFrom, hc]
  ·
    have : addConstFrom (k := k) dst src c
            = addConstAux (k := k) dst src (c < 0) (Int.natAbs c) 0 := by
      simp [addConstFrom, hc]
    have haux :
      addConstAux (k := k) dst src (c < 0) (Int.natAbs c) 0
        = (shiftsOf (Int.natAbs c)).map
            (fun s => valid_ops.addScaled dst src (negSrc := (c < 0)) s) := by
      simpa [shiftsOf] using addConstAux_eq_shifts (k := k) dst src (c < 0) (Int.natAbs c) 0
    simp [this, haux, signedPow2Decomp, hc, List.map_map, pairToOp]

lemma computeLocalAux_eq_fold {k} (hk : 0 < k) (z : Int) :
  ∀ (js : List (Fin k)),
    computeLocalAux (k := k) hk z js
      =
    js.foldl
      (fun acc j => acc ++ addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat))) []
| []      => by simp [computeLocalAux]
| j :: js => by
  simp [computeLocalAux, computeLocalAux_eq_fold (k := k) hk z js, List.foldl]

/-- Fold helper: if the step functions are pointwise equal, the folds are equal. -/
lemma foldl_congr_step {α β} :
  ∀ (xs : List α) (f g : β → α → β) (acc : β),
    (∀ acc a, f acc a = g acc a) →
    List.foldl f acc xs = List.foldl g acc xs
| [],      f, g, acc, h => by simp
| a :: xs, f, g, acc, h => by
  simp [List.foldl, h, foldl_congr_step xs f g _ h]

/-- Normalize the guard: `z ^ (j:ℕ) = 0` iff `z = 0 ∧ j ≠ 0` (where zero means `finZero`). -/
lemma pow_guard_iff {k} (hk : 0 < k) (z : ℤ) (j : Fin k) :
  (z ^ (j : Nat) = 0) ↔ (z = 0 ∧ j ≠ finZero hk) := by
  classical
  by_cases h0 : j = finZero hk
  · subst h0; simp [finZero, pow_zero]
  · -- j ≠ 0 ⇒ (j : ℕ) > 0
    have hjpos : 0 < (j : Nat) := by
      have : (j : Nat) ≠ 0 := by
        intro h; apply h0; apply Fin.ext; simpa [finZero] using h
      exact Nat.pos_of_ne_zero this
    constructor
    · intro h; aesop
    · intro hzj; have hz : z = 0 := hzj.left; aesop


theorem computeLocal_eq(hk: 0 < k):
computeLocal2 hk z = computeLocal hk z:= by {
  have rec_as_fold :
    computeLocal2 (k := k) hk z
      =
    (nonzeroFins (k := k) hk).foldl
      (fun acc j => acc ++ addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat))) [] := by
    revert z; intro z
    -- simple induction on the list hidden inside computeLocal2
    unfold computeLocal2
    -- prove the generic list lemma: `computeLocalAux` equals that fold
    have : ∀ (js : List (Fin k)) (z : ℤ),
        computeLocalAux (k := k) hk z js
          =
        js.foldl (fun acc j => acc ++ addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat))) [] := by
      intro js; induction js with
      | nil => intro z; simp [computeLocalAux]
      | cons j js ih =>
          intro z; simp [computeLocalAux, ih, List.foldl]
    -- apply the lemma to `nonzeroFins hk`
    simpa using this (nonzeroFins (k := k) hk) z
  have step_eq :
    ∀ (acc : Prog k) (j : Fin k),
      acc ++ addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat))
      =
      if z = 0 ∧ j ≠ finZero hk then acc
      else acc ++ (signedPow2Decomp (z ^ (j : Nat))).map (pairToOp (k := k) (finZero hk) j) := by
    intro acc j
    have E := addConstFrom_eq_signedPow2Map (k := k) (finZero hk) j (z ^ (j : Nat))
    -- pull the `if` out across the append
    -- and rewrite the guard using the power-0 characterization
    by_cases hzj : z ^ (j : Nat) = 0
    · aesop
    · have hz' : ¬ (z = 0 ∧ j ≠ finZero hk) := by
        intro h; exact hzj ((pow_guard_iff (k := k) hk z j).2 h)
      simp [E, hzj, hz']
  -- Conclude by foldl congruence.
  have := foldl_congr_step (xs := nonzeroFins (k := k) hk)
          (f := fun acc j => acc ++ addConstFrom (k := k) (finZero hk) j (z ^ (j : Nat)))
          (g := fun acc j =>
            if z = 0 ∧ j ≠ finZero hk then acc
            else acc ++ (signedPow2Decomp (z ^ (j : Nat))).map (pairToOp (k := k) (finZero hk) j))
          (acc := ([] : Prog k))
          (step_eq)
  unfold computeLocal2 computeLocal computeLocalAux at *
  simp [rec_as_fold,this]
  unfold finZero
  have h:(fun acc (j:Fin k) ↦ if z = 0 ∧ ¬j = ⟨0, hk⟩ then acc else acc ++ List.map (pairToOp ⟨0, hk⟩ j) (signedPow2Decomp (z ^ j.val)))
          = (fun acc (j:Fin k) ↦ if z = 0 ∧ ¬j.val = 0 then acc else acc ++ List.map (pairToOp ⟨0, hk⟩ j) (signedPow2Decomp (z ^ j.val))):=by
          funext acc j
          split_ifs with h1 h2 h3
          all_goals try rfl
          cases h1 with
          |intro l h => {
            simp[l] at h2
            simp_all
            have hj0 : j = ⟨0, hk⟩ := by
              apply Fin.ext
              -- goal is j.val = 0, which is exactly h2
              simpa using h2
            contradiction
          }
          cases h3 with
          |intro l h => {
            simp[l] at h1
            simp_all
          }
  simp[h]

}
/-- One block per point: build row in `dst`, mark it, then uncompute. -/
def opsForPointWithProduct {k : Nat} (hk : 0 < k) : Point → Prog k
| .inf   =>
  let last : Fin k := ⟨k-1, by
    have hk' : 0 < k := hk
    exact Nat.sub_lt (Nat.succ_le_of_lt hk') (by decide)⟩
  [valid_ops.phaseProduct last]
| .int z =>
  let dst := finZero hk
  let l   := computeLocal2 hk z
  l ++ [valid_ops.phaseProduct dst] ++ apply_Op_inverse l

/-- Generator that includes `phaseProduct` checkpoints (no folds). -/
def genOpsWithProduct {k : Nat} (hk : 0 < k) : List Point → Prog k
| []       => []
| p :: ps  => opsForPointWithProduct hk p ++ genOpsWithProduct hk ps


lemma computeLocal2_Valid{k:ℕ}{z:ℤ}(hk:0<k):
  Prog.WellFormed (computeLocal2 hk z):= by sorry
