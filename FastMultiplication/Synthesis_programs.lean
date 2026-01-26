import FastMultiplication.Lemmas_and_Theorems



-- /******************************************************************************/
-- /*                DEFINING BASIC SYNTHESIS PROGRAM                            */
-- /******************************************************************************/
open Operations



def shiftsOfAux : Nat → Nat → List Nat
| 0,      _  => []
| n+1,    sh =>
  let rest := shiftsOfAux ((n+1) / 2) (sh+1)
  if Odd (n+1) then sh :: rest else rest
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
  if Odd (n+1) then
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

open Operations


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

  by_cases hb : Odd (n+1)
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




lemma computeLocal_eq_computeLocal2 {k : Nat} (hk : 0 < k) (z : Int) :
  computeLocal hk z = computeLocal2 hk z := by
  classical
  let dst : Fin k := finZero hk

  -- Rewrite computeLocal2 as a fold.
  have h2 :
      computeLocal2 (k := k) hk z
        =
      (nonzeroFins (k := k) hk).foldl
        (fun acc j => acc ++ addConstFrom (k := k) dst j (z ^ (j : Nat))) [] := by
    unfold computeLocal2
    simpa using (computeLocalAux_eq_fold (k := k) hk z (nonzeroFins (k := k) hk))

  -- Compare the fold steps.
  have step_eq :
      ∀ (acc : Prog k) (j : Fin k),
        (fun acc (j:Fin k) =>
          let c : Int := z ^ (j : Nat)
          if c = 0 then acc
          else acc ++ (signedPow2Decomp c).map (pairToOp (k := k) dst j)) acc j
        =
        (fun acc j => acc ++ addConstFrom (k := k) dst j (z ^ (j : Nat))) acc j := by
    intro acc j
    set c : Int := z ^ (j : Nat)
    -- rewrite addConstFrom into signedPow2Decomp form
    have E :
        addConstFrom (k := k) dst j c
          =
        (if c = 0 then [] else (signedPow2Decomp c).map (pairToOp (k := k) dst j)) := by
      -- this is your previously proved bridge lemma
      simpa [c] using (addConstFrom_eq_signedPow2Map (k := k) (dst := dst) (src := j) c)
    -- now simplify both sides by cases on c=0
    by_cases hc : c = 0
    · aesop
    · simp [c, E, hc]

  -- Now finish: both sides are the same fold over nonzeroFins.
  unfold computeLocal
  -- use fold congruence
  have := foldl_congr_step
    (xs := nonzeroFins (k := k) hk)
    (f := fun acc (j:Fin k) =>
      let c : Int := z ^ (j : Nat)
      if c = 0 then acc
      else acc ++ (signedPow2Decomp c).map (pairToOp (k := k) dst j))
    (g := fun acc j => acc ++ addConstFrom (k := k) dst j (z ^ (j : Nat)))
    (acc := ([] : Prog k))
    step_eq
  aesop


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

/-- Prop version: the whole row equals the expected row, pointwise. -/
def rowMatchesProp {k : Nat} (σ : State k) (i : Fin k) (pt : Point) : Prop :=
  ∀ j : Fin k, σ i j = expectedRow (k := k) pt j

/-- Provide a decidable instance for `rowMatchesProp`. -/
instance instDecidable_rowMatchesProp
  {k : Nat} (σ : State k) (i : Fin k) (pt : Point) :
  Decidable (rowMatchesProp (k := k) σ i pt) := by
  classical
  -- This reduces to decidability of ∀ over a finite type with decidable equality
  -- (`Int` has `DecidableEq`, and equality is decidable).
  unfold rowMatchesProp
  infer_instance













/-- Render a `Fin k` as a plain natural number. -/
def showFin {k} (i : Fin k) : String :=
  toString i.val

/-- Pretty printer for a single operation. -/
def opToString {k} : valid_ops k → String
| .shiftL i n        => s!"(shiftL,  reg={showFin i}, by={n})"
| .shiftR i n        => s!"(shiftR,  reg={showFin i}, by={n})"
| .negate i          => s!"(negate,  reg={showFin i})"
| .addScaled i j b sh =>
    let sgn := if b then "-" else "+"
    s!"(add,     dst={showFin i}, src={showFin j}, sign={sgn}1, shift={sh})"
| .phaseProduct i    => s!"(phaseProduct, reg={showFin i})"

/-- Join a list of strings with ", " and bracket it like a list. -/
def joinComma : List String → String
| []      => "[]"
| xs      =>
  let body := xs.foldl (fun acc s => if acc = "" then s else acc ++ ", " ++ s) ""
  "[" ++ body ++ "]"

/-- Pretty print a whole program. -/
def progToString {k} (p : Prog k) : String :=
  joinComma (p.map opToString)

/-- String form for a single point. -/
def pointToString : Point → String
| .inf    => "inf"
| .int z  => toString z

/-- Ops for a single point, as a one-line string. -/
def opsForPointString {k} (hk : 0 < k) (p : Point) : String :=
  progToString (opsForPointWithProduct (k := k) hk p)

/-- Ops for a whole list of points, as one flat list string. -/
def genOpsString {k} (hk : 0 < k) (ps : List Point) : String :=
  progToString (genOpsWithProduct (k := k) hk ps)



/-- Example: change `k` and `pts` to whatever you want. -/
def pts : List Point :=
  [Point.inf, Point.int (-3), Point.int (-2)]

#eval IO.println (genOpsString (k := 3) (by decide) pts)


def AllNe {k} (dst : Fin k) : List (Fin k) → Prop
| []      => True
| j :: js => j ≠ dst ∧ AllNe dst js

lemma nonzeroFins_allNe {k} (hk : 0 < k) :
  AllNe (finZero (k := k) hk) (nonzeroFins (k := k) hk) := by
  classical
  unfold nonzeroFins
  let dst := finZero (k := k) hk
  have h_aux :
      ∀ (L : List (Fin k)),
        AllNe dst (L.filter (fun j => j ≠ dst)) := by
    intro L
    induction L with
    | nil =>
        simp [AllNe]
    | cons j js ih =>
        by_cases h : j = dst
        ·
          unfold AllNe
          simp [h]
          aesop
        ·
          simp [AllNe, h]
          aesop
  simpa using h_aux (List.finRange k)

lemma WellFormed_append {k} {p q : Prog k} :
    Prog.WellFormed p → Prog.WellFormed q → Prog.WellFormed (p ++ q) := by
  intro hp hq op hop
  -- membership in p ++ q splits
  have := List.mem_append.mp hop
  rcases this with hmem | hmem
  · exact hp op hmem
  · exact hq op hmem


open Prog

lemma addConstAux_WellFormed
    {k : ℕ} {dst src : Fin k} (hsd : dst ≠ src) (neg' : Bool) :
    ∀ n sh, (addConstAux (k := k) dst src neg' n sh).WellFormed := by
  classical
  -- Strong induction on n
  have main :
      ∀ n, ∀ sh, (addConstAux (k := k) dst src neg' n sh).WellFormed :=
    fun n =>
      Nat.strongRecOn n
        (motive :=
          fun n => ∀ sh, (addConstAux (k := k) dst src neg' n sh).WellFormed)
        (fun n ih sh op hop => by
          cases n with
          | zero =>
              simp [addConstAux] at hop
          | succ n' =>
              have hlt : (n' + 1) / 2 < n'.succ := by
                exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

              have wf_tail :
                  (addConstAux (k := k) dst src neg' ((n' + 1) / 2) (sh + 1)).WellFormed :=
                ih ((n' + 1) / 2) hlt (sh + 1)
              dsimp [Prog.WellFormed] at wf_tail

              unfold addConstAux at hop
              set rest :=
                addConstAux (k := k) dst src neg' ((n' + 1) / 2) (sh + 1)
                with hrest

              by_cases hodd : Odd (n' + 1)
              · -- Odd case: head :: rest
                simp [hodd, hrest] at hop
                rcases hop with hhead | hmem
                · -- op is the head
                  subst hhead
                  simp [Prog.OpOK, hsd]
                · -- op from the tail: use wf_tail
                  exact wf_tail op (by simpa [hrest] using hmem)
              · -- Even case: only rest
                simp [hodd, hrest] at hop
                exact wf_tail op (by simpa [hrest] using hop)
        )
  intro n sh
  exact main n sh


/-- `addConstFrom` is well-formed whenever `dst ≠ src`. -/
lemma addConstFrom_WellFormed
    {k : ℕ} {dst src : Fin k} (hsd : dst ≠ src) (c : Int) :
    Prog.WellFormed (addConstFrom (k := k) dst src c) := by
  classical
  by_cases hc : c = 0
  · -- no ops
    simp [addConstFrom, hc, Prog.WellFormed]
  · -- expands to addConstAux dst src (c<0) (|c|) 0
    have h :=
      addConstAux_WellFormed (k := k) (dst := dst) (src := src)
        hsd (neg' := c < 0) (Int.natAbs c) 0
    simpa [addConstFrom, hc] using h
/-- `computeLocalAux` is well-formed when all sources in the list are
    different from `dst = finZero hk`. -/
lemma computeLocalAux_WellFormed
    {k : ℕ} (hk : 0 < k) (z : ℤ) :
    ∀ (js : List (Fin k)),
      AllNe (finZero (k := k) hk) js →
      Prog.WellFormed (computeLocalAux (k := k) hk z js)
  | [], _ => by
      -- no ops
      intro op hop
      simp [computeLocalAux] at hop
  | j :: js, hAll => by
      -- AllNe dst (j :: js) gives j ≠ dst and AllNe dst js
      rcases hAll with ⟨hj_ne, hAll_js⟩
      -- set names
      let dst := finZero (k := k) hk
      let c   := z ^ (j : ℕ)
      -- head block: addConstFrom dst j c, with dst ≠ j
      have hheadWF :
          Prog.WellFormed (addConstFrom (k := k) dst j c) :=
        addConstFrom_WellFormed
          (k := k) (dst := dst) (src := j)
          (by
            -- hj_ne : j ≠ dst, but lemma expects dst ≠ j
            intro h; exact hj_ne (by simp [h] : j = dst))
          c
      -- tail block: by IH on js
      have htailWF :
          Prog.WellFormed (computeLocalAux (k := k) hk z js) := by
        have :=computeLocalAux_WellFormed hk z js hAll_js
        simp[this]
      -- whole list is head ++ tail
      intro op hop
      -- expand definition and use append lemma
      have := WellFormed_append (k := k) hheadWF htailWF op
      simpa [computeLocalAux] using this hop

lemma computeLocal2_Valid{k:ℕ}{z:ℤ}(hk:0<k):
  Prog.WellFormed (computeLocal2 hk z):= by
    unfold computeLocal2
    have hAll : AllNe (finZero (k := k) hk) (nonzeroFins (k := k) hk) :=
      nonzeroFins_allNe (k := k) hk
    exact computeLocalAux_WellFormed (k := k) hk z (nonzeroFins hk) hAll










/-- Numeric sum of powers-of-two specified by a list of shifts. -/
private def sumPow2 (ls : List Nat) : Int :=
  ls.foldl (fun acc s => acc + (2 : Int) ^ s) 0

lemma tail_all_nonzero
  {k : ℕ} (hk : 0 < k)
  {j : Fin k} {js : List (Fin k)}
  (heq :
    List.filter (fun u : Fin k => ! decide (u = finZero (k := k) hk))
                (List.ofFn (fun i : Fin k => i))
    = j :: js) :
  ∀ t ∈ js, t ≠ finZero (k := k) hk :=
by
  intro t ht
  -- t ∈ js ⇒ t ∈ j :: js ⇒ t ∈ that filter (by `heq`)
  have hmemFilt :
    t ∈ List.filter (fun u : Fin k => ! decide (u = finZero (k := k) hk))
                    (List.ofFn (fun i : Fin k => i)) := by
    have : t ∈ (j :: js) := by simp [ht]
    simpa [heq] using this
  -- membership in a boolean `filter` gives the predicate is true
  have hpred : (! decide (t = finZero (k := k) hk)) = true := by
    -- `mem_filter` ↔ (mem ∧ p=tt); `simp` picks out the boolean guard
    simpa [List.mem_filter] using hmemFilt
  -- so `decide (t = 0) = false` ⇒ indeed `t ≠ 0`
  have hdec : decide (t = finZero (k := k) hk) = false := by simpa using hpred
  intro hEq;
  subst hEq
  simp_all only [List.mem_cons, or_true, decide_true, Bool.not_true, Bool.false_eq_true]

lemma computeLocalAux_zero_nil_of_nonzero
  {k : ℕ} (hk : 0 < k) :
  ∀ (js : List (Fin k)), (∀ t ∈ js, t ≠ finZero (k := k) hk) →
    computeLocalAux (k := k) hk 0 js = []
| [], _ => by simp [computeLocalAux]
| (t :: ts), hnon => by
  have ht_ne0 : t ≠ finZero (k := k) hk := hnon t (by simp)
  have ht_pos : 0 < (t : ℕ) := by
    have hval_ne : (t : ℕ) ≠ 0 := by
      intro h0; apply ht_ne0; apply Fin.ext; simpa [finZero] using h0
    exact Nat.pos_of_ne_zero hval_ne
  -- 0^(t:ℕ) = 0 because t>0
  have hpow : (0 : ℤ) ^ (t : ℕ) = 0 := by
    rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt ht_pos) with ⟨m, hm⟩
    -- 0^(m+1) = (0^m) * 0 = 0
    simp [hm, pow_succ]  -- uses *_*0 = 0
  -- tail still has only nonzero indices
  have htail : ∀ u ∈ ts, u ≠ finZero (k := k) hk := by
    intro u hu; exact hnon u (by simp [hu])
  -- unfold once: head ++ tail, but head = []
  simp [computeLocalAux, addConstFrom, hpow, computeLocalAux_zero_nil_of_nonzero hk ts htail]


lemma exists_mid_of_run_append {k}
  {p q : Prog k} {σ σ₁ : State k}
  (hr : run? (p ++ q) σ = some σ₁) :
  ∃ τ, run? p σ = some τ ∧ run? q τ = some σ₁ := by
  revert q σ σ₁ hr
  induction p with
  | nil =>
      intro q σ σ₁ hr
      exact ⟨σ, by simp[run?], by simpa[List.nil_append] using hr⟩
  | cons op ps ih =>
      intro q σ σ₁ hr
      -- p ++ q = (op :: ps) ++ q = op :: (ps ++ q)
      simp [List.cons_append] at hr
      rcases (show ∃ τ, applyOp? (k := k) σ op = some τ from by
                cases h:applyOp? (k := k) σ op <;> simp[h] at hr ; aesop) with ⟨τ,hτ⟩
      have : run? (ps ++ q) τ = some σ₁ := by simpa [hτ] using hr
      rcases ih this with ⟨μ, hps, hq⟩
      exact ⟨μ, by simpa [run?, hτ] using hps, hq⟩

/-- From `heq : filter(≠0) (finRange k) = j::js` we get `j ≠ 0` and all `t∈js` are ≠0. -/
lemma head_and_tail_nonzero
  {k} (hk:0<k) {j:Fin k} {js:List (Fin k)}
  (heq : List.filter (fun u : Fin k => !decide (u = finZero (k:=k) hk))
                     (List.finRange k) = j :: js) :
  (j ≠ finZero (k:=k) hk) ∧ (∀ t∈js, t ≠ finZero (k:=k) hk) := by
  have hjmem : j ∈ List.filter (fun u : Fin k => !decide (u = finZero (k:=k) hk))
                               (List.finRange k) := by simp [heq]
  have : (!decide (j = finZero (k:=k) hk)) = true := by
    -- mem of boolean filter implies predicate holds
    simpa [List.mem_filter] using hjmem
  have hj0 : j ≠ finZero (k:=k) hk := by
    intro h; have : decide (j = finZero (k:=k) hk) = true := by simp [h]
    simp_all
  refine ⟨hj0, ?_⟩
  intro t ht
  have tmem : t ∈ List.filter (fun u : Fin k => !decide (u = finZero (k:=k) hk))
                              (List.finRange k) := by
    have : t ∈ (j::js) := by simp_all
    simpa [heq] using this
  have : (!decide (t = finZero (k:=k) hk)) = true := by
    simpa [List.mem_filter] using tmem
  intro h; have : decide (t = finZero (k:=k) hk) = true := by simp [h]
  simp_all


/-- Pointwise equality of registers as a `Bool`. -/
def regEqReg {k : Nat} (r s : Register k) : Bool :=
  (List.finRange k).all (fun u => decide (r u = s u))

def matchesAt_pointRow_state3 {k : Nat} (hk : 0 < k) : MatchesAtState k :=
  fun σ i pt =>
    match pt with
    | .int z =>
        match run? (computeLocal2 (k := k) hk z) (State.start_state (k := k)) with
        | some σ' => regEqReg (k := k) (σ i) (σ' (finZero (k := k) hk))
        | none    => false
    | .inf =>
        let last : Fin k := ⟨k-1, by
          have hk' : 0 < k := hk
          exact Nat.sub_lt (Nat.succ_le_of_lt hk') (by decide)⟩
        let target : Register k := fun u => if u = last then (1 : Int) else 0
        regEqReg (k := k) (σ i) target



/-- Comparing a register with a concrete row via `regEqReg` is the same as
    `regEqExpected` when the concrete row *is* that expected row. -/
lemma regEqReg_to_regEqExpected_int
  {k : ℕ} (r : Register k) (z : ℤ) :
  regEqReg (k := k) r (expectedRow (k := k) (.int z))
  =
  regEqExpected (k := k) r (.int z) := by
  classical
  simp [regEqReg, regEqExpected]

/-- For `.inf`, your state3/2 target register *is* `expectedRow .inf`. -/
lemma regEqReg_to_regEqExpected_inf
  {k : ℕ} (hk : 0 < k) (r : Register k) :
  (let last : Fin k := ⟨k-1, by
     have hk' : 0 < k := hk
     exact Nat.sub_lt (Nat.succ_le_of_lt hk') (by decide)⟩
   let target : Register k := fun u => if u = last then (1 : Int) else 0;
   regEqReg (k := k) r target)
  =
  regEqExpected (k := k) r (.inf) := by
  classical
  -- `expectedRow .inf` is exactly that `target`
  simp [regEqReg, regEqExpected, expectedRow]
  split
  next k => simp_all only [List.finRange_zero, zero_tsub, List.all_nil]
  next k k_1 => simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right]

open Operations

lemma run_some_addConstAux
    {k : ℕ} (dst src : Fin k) (neg' : Bool) :
    ∀ (n sh : ℕ) (σ : State k),
      ∃ τ, run? (addConstAux (k := k) dst src neg' n sh) σ = some τ := by
  classical
  -- strong induction on n
  intro n
  refine Nat.strongRecOn n ?step
  -- step : ∀ n, (∀ m < n, ...) → ∀ sh σ, ∃ τ, ...
  intro n ih sh σ
  cases n with
  | zero =>
      -- n = 0: addConstAux 0 sh = []
      refine ⟨σ, ?_⟩
      simp [addConstAux]
  | succ n' =>
      set rest :=
        addConstAux (k := k) dst src neg' ((n' + 1) / 2) (sh + 1)
        with hrest

      have hlt : (n' + 1) / 2 < n'.succ :=
        Nat.div_lt_self (Nat.succ_pos _) (by decide)

      have ih_tail :
          ∀ (sh₁ : ℕ) (σ₁ : State k),
            ∃ τ, run? rest σ₁ = some τ := by
        intro sh₁ σ₁
        have := ih ((n' + 1) / 2) hlt sh₁ σ₁
        aesop

      by_cases hodd : Odd (n' + 1)
      · -- odd case: head addScaled then rest
        let σ₁ := State.addScaledReg σ dst src (negSrc := neg') sh
        have hstep :
            applyOp? (k := k) σ
              (valid_ops.addScaled dst src (negSrc := neg') sh)
          = some σ₁ := rfl

        -- run the tail starting from σ₁ at shift (sh+1)
        rcases ih_tail (sh + 1) σ₁ with ⟨τ, hτ⟩

        refine ⟨τ, ?_⟩
        simp [addConstAux, hodd,  hstep]
        aesop
      · -- even case: no head, just rest
        rcases ih_tail (sh + 1) σ with ⟨τ, hτ⟩
        refine ⟨τ, ?_⟩
        simp [addConstAux, hodd]
        aesop

lemma run_some_addConstFrom
    {k : ℕ} (dst src : Fin k) (c : ℤ) (σ : State k) :
    ∃ τ, run? (addConstFrom (k := k) dst src c) σ = some τ := by
  classical
  by_cases hc : c = 0
  · -- empty program
    subst hc
    refine ⟨σ, ?_⟩
    simp [addConstFrom]
  · -- nonzero: delegates to addConstAux
    unfold addConstFrom
    simp[hc]
    have h := run_some_addConstAux (k := k)
              dst src (decide (c < 0)) c.natAbs 0 σ
    rcases h with ⟨τ, hτ⟩
    simp[hτ]



lemma run_some_computeLocalAux
    {k : ℕ} (hk : 0 < k) (z : ℤ) :
    ∀ (js : List (Fin k)) (σ : State k),
      ∃ τ, run? (computeLocalAux (k := k) hk z js) σ = some τ := by
  classical
  intro js
  -- IMPORTANT: generalize over σ in the induction
  induction js with
  | nil =>
      simp [computeLocalAux]
  | cons j js ih =>
      intro σ
      -- head: addConstFrom (finZero hk) j (z^j)
      obtain ⟨σ₁, h₁⟩ :
          ∃ σ₁, run? (addConstFrom (k := k) (finZero hk) j (z ^ (j : ℕ))) σ = some σ₁ :=
        run_some_addConstFrom (k := k) (dst := finZero hk) (src := j)
                              (c := z ^ (j : ℕ)) σ
      obtain ⟨τ, h₂⟩ := ih σ₁
      refine ⟨τ, ?_⟩
      simp [computeLocalAux,run?_append,h₁,h₂]


lemma computeLocal2_some_state
(k : ℕ)
(hk : 0 < k)
(z : ℤ)
(σ : State k):
 ∃ σ₁, run? (computeLocal2 hk z) σ = some σ₁:=by
  unfold computeLocal2
  exact run_some_computeLocalAux (k := k) hk z (nonzeroFins hk) σ
