import FastMultiplication.ShorVerification.Basic
import FastMultiplication.Table_Blocks
import Mathlib.Data.Finset.Basic

namespace Shor
open Gate
open Operations


/-! =========================================================
    Section 2: Finite reindexing equivalence
========================================================= -/

/-- Equivalence between `Fin A × Fin B` and `Fin (A * B)`. -/
noncomputable def finMulAddEquiv (A B : ℕ) :
    (Fin A × Fin B) ≃ Fin (A * B) where
  toFun p :=
    let i : Fin A := p.1
    let j : Fin B := p.2
    ⟨i.1 + A * j.1, by
      rcases i with ⟨i, hi⟩
      rcases j with ⟨j, hj⟩
      calc
        i + A * j < A + A * j := Nat.add_lt_add_right hi _
        _ = A * (j + 1)       := by
              simp [Nat.mul_add, Nat.add_comm]
        _ ≤ A * B             := by
              exact Nat.mul_le_mul_left A (Nat.succ_le_of_lt hj)
    ⟩

  invFun n :=
    if hA : 0 < A then
      (⟨n.1 % A, Nat.mod_lt _ hA⟩,
       ⟨n.1 / A, by
          exact Nat.div_lt_of_lt_mul (by
            simp)⟩)
    else
      by
        have : False := by
          have hA0 : A = 0 := Nat.eq_zero_of_not_pos hA
          subst hA0
          simp_all
          simp at n
          simpa using n.elim0
        exact False.elim this

  left_inv := by
    intro p
    rcases p with ⟨i, j⟩
    cases A with
    | zero =>
        exact i.elim0
    | succ A =>
        have hA : 0 < A.succ := Nat.succ_pos _
        simp
        constructor
        · apply Fin.ext
          have hi_lt : (i.1) < (A + 1) := i.2
          simp [Nat.mod_eq_of_lt hi_lt]
        · apply Fin.ext
          have hi_lt : (i.1) < (A + 1) := i.2
          have hi_div : (i.1 / (A + 1)) = 0 := by
            exact Nat.div_eq_of_lt hi_lt
          calc
            (i.1 + (A + 1) * j.1) / (A + 1)
                = j.1 + (i.1 / (A + 1)) := by
                    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                      using (Nat.add_mul_div_right i.1 j.1 (Nat.succ_pos A))
            _   = j.1 := by simp [hi_div]

  right_inv := by
    intro n
    cases A with
    | zero =>
        simp at n
        exact n.elim0
    | succ A =>
        have hA : 0 < A.succ := Nat.succ_pos _
        ext
        simp
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.mod_add_div (n.1) (A + 1))

/-! =========================================================
    Section 3: Low-level gate language
========================================================= -/

/-- Low-level target gate language for lowering. -/
inductive LowGate : Type
  | id : LowGate
  | seq : LowGate → LowGate → LowGate
  | adj : LowGate → LowGate
  | H : ℕ → LowGate
  | X : ℕ → LowGate
  | Prim : String → List ℕ → LowGate
  | ShiftL    : (r : ExtReg) → (n : ℕ) → LowGate
  | ShiftR    : (r : ExtReg) → (n : ℕ) → LowGate
  | Negate    : (r : ExtReg) → LowGate
  | AddScaled : (dst src : ExtReg) → (negSrc : Bool) → (shift : ℕ) → LowGate
  | Naive_SignedPhaseProd : (phi : Real) → (x z : ExtReg) → LowGate
  | Naive_CSignedPhaseProd : (ctrl : ℕ) → (phi : Real) → (x z : ExtReg) → LowGate
  | zeroExtend : (r : ExtReg) → (n : ℕ) → LowGate
  | signExtend : (r : ExtReg) → (n : ℕ) → LowGate
  | zeroDealloc : (r : ExtReg) → (n : ℕ) → LowGate
  | signDealloc : (r : ExtReg) → (n : ℕ) → LowGate
  | RadixReverse : (r : Reg) → (m : ℕ) → LowGate
deriving Inhabited

namespace LowGate

/-- Sequential composition notation for low gates. -/
infixr:80 " ;; " => LowGate.seq

/-- Adjoint notation for low gates. -/
prefix:90 "†" => LowGate.adj

end LowGate

/-! =========================================================
    Section 4: Register layouts and slot geometry
========================================================= -/

/-- A `k`-slot register layout with pairwise disjoint slots. -/
structure Layout (k : ℕ) where
  slot : Fin k → Reg
  disjoint : ∀ i j, i ≠ j → Disjoint (slot i) (slot j)

/-- Size of chunk `i` when splitting a register into `k` parts. -/
def chunkSize (n k : ℕ) (i : Fin k) : ℕ :=
  let q := n / k
  let rem := n % k
  q + if i.1 < rem then 1 else 0

/-- Starting offset of chunk `i` in an even split into `k` parts. -/
def chunkStart (n k : ℕ) (i : Fin k) : ℕ :=
  let q := n / k
  let rem := n % k
  i.1 * q + Nat.min i.1 rem

/-- Helper: in a near-even chunk split, the end of an earlier chunk is before
    the start of a later chunk. -/
lemma chunkStart_mono (n k : ℕ) {i j : Fin k} (hij : i.1 ≤ j.1) :
    chunkStart n k i ≤ chunkStart n k j := by
  unfold chunkStart
  exact Nat.add_le_add
    (Nat.mul_le_mul_right _ hij)
    (min_le_min_right _ hij)

lemma chunkStart_succ_eq_add_chunkSize
  (n k : ℕ) {i : Fin k} (hnext : i.1 + 1 < k) :
  chunkStart n k ⟨i.1 + 1, hnext⟩ = chunkStart n k i + chunkSize n k i := by
  by_cases hi : i.1 < n % k
  · have hmin_i : Nat.min i.1 (n % k) = i.1 :=
      Nat.min_eq_left (Nat.le_of_lt hi)
    have hmin_succ : Nat.min (i.1 + 1) (n % k) = i.1 + 1 :=
      Nat.min_eq_left (Nat.succ_le_of_lt hi)
    simp [chunkStart, chunkSize, hi, hmin_i]
    ring
  · have hge : n % k ≤ i.1 := Nat.le_of_not_gt hi
    have hmin_i : Nat.min i.1 (n % k) = n % k :=
      Nat.min_eq_right hge
    have hmin_succ : Nat.min (i.1 + 1) (n % k) = n % k :=
      Nat.min_eq_right (le_trans hge (Nat.le_succ _))
    simp [chunkStart, chunkSize, hi, hmin_i, hmin_succ]
    ring

lemma chunkStart_add_chunkSize_le_chunkStart_of_lt
  (n k : ℕ) {i j : Fin k}
  (hlt : i.1 < j.1) :
  chunkStart n k i + chunkSize n k i ≤ chunkStart n k j := by
  have hsucc : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hlt
  have hnext : i.1 + 1 < k := lt_of_le_of_lt hsucc j.is_lt
  calc
    chunkStart n k i + chunkSize n k i
        = chunkStart n k ⟨i.1 + 1, hnext⟩ := by
            symm
            exact chunkStart_succ_eq_add_chunkSize n k hnext
    _ ≤ chunkStart n k j :=
      chunkStart_mono n k hsucc

/-- Contiguous near-even splitting of a register into `k` chunks. -/
def layoutOfReg (r : Reg) (k : ℕ) : Layout k where
  slot := fun i =>
    let n := regSize r
    let s := chunkStart n k i
    let m := chunkSize n k i
    { lo := r.lo + s, size := m }
  disjoint := by
    intro i j hij

    have hij_val : i.1 ≠ j.1 := by
      intro h
      apply hij
      exact Fin.ext h

    rcases lt_or_gt_of_ne hij_val with hlt | hgt
    · left
      dsimp
      have hmain :
          chunkStart (regSize r) k i + chunkSize (regSize r) k i
            ≤ chunkStart (regSize r) k j :=
        chunkStart_add_chunkSize_le_chunkStart_of_lt
          (regSize r) k hlt
      simp[add_assoc]
      set a:=chunkStart (regSize r) k i + chunkSize (regSize r) k i
      omega

    · right
      dsimp
      have hmain :
          chunkStart (regSize r) k j + chunkSize (regSize r) k j
            ≤ chunkStart (regSize r) k i :=
        chunkStart_add_chunkSize_le_chunkStart_of_lt
          (regSize r) k hgt
      omega

/-- Each slot in a split layout has size at most the original register. -/
lemma slot_size_le (x : Reg) (k : ℕ) (hk : 1 ≤ k) (i : Fin k) :
  regSize ((layoutOfReg x k).slot i) ≤ regSize x := by
  dsimp [layoutOfReg]
  let n := regSize x
  change chunkSize n k i ≤ n
  unfold chunkSize
  have hk0 : 0 < k := by omega
  have hdiv : n / k * k + n % k = n := by
    rw [mul_comm]
    exact Nat.div_add_mod n k
  simp
  split_ifs with h
  · have hrem_lt : n % k < k := Nat.mod_lt _ hk0
    have hrem_pos : 1 ≤ n % k := by
      omega
    have hmul : n / k ≤ n / k * k := by
      calc
        n / k = n / k * 1 := by rw [Nat.mul_one]
        _ ≤ n / k * k := Nat.mul_le_mul_left _ hk
    omega
  · have hmul : n / k ≤ n / k * k := by
      calc
        n / k = n / k * 1 := by rw [Nat.mul_one]
        _ ≤ n / k * k := Nat.mul_le_mul_left _ hk
    omega

/-- If `k > 1` and the register is nontrivial, each slot is strictly smaller. -/
lemma slot_size_lt (x : Reg) {k : ℕ} (hk : 1 < k) (hx : 1 < regSize x) (i : Fin k) :
  regSize ((layoutOfReg x k).slot i) < regSize x := by
  dsimp [layoutOfReg]
  let n := regSize x
  change chunkSize n k i < n
  unfold chunkSize
  have hk0 : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  have hdiv : n / k * k + n % k = n := by
    rw [mul_comm]
    exact Nat.div_add_mod n k
  simp
  split_ifs with h
  · by_cases hq : n / k = 0
    · have hrem_lt : n % k < k := Nat.mod_lt _ hk0
      have hrem_pos : 1 ≤ n % k := by
        omega
      omega
    · have hq_pos : 1 ≤ n / k := by
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq)
      have hmul : n / k * 2 ≤ n / k * k :=
        Nat.mul_le_mul_left (n / k) hk2
      have hrem_lt : n % k < k := Nat.mod_lt _ hk0
      have hrem_pos : 1 ≤ n % k := by
        omega
      omega
  · by_cases hq : n / k = 0
    · omega
    · have hq_pos : 1 ≤ n / k := by
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq)
      have hmul : n / k * 2 ≤ n / k * k :=
        Nat.mul_le_mul_left (n / k) hk2
      omega

/-! =========================================================
    Section 5: Layout-state evolution under valid ops
========================================================= -/
/-- Mutable slot assignment state for both `x` and `z` blocks. -/
structure LayoutState (k : ℕ) where
  xslot : Fin k → ExtReg
  zslot : Fin k → ExtReg

/-- Width bookkeeping only: current logical widths of each chunk. -/
structure WidthState (k : ℕ) where
  xw : Fin k → ℕ
  zw : Fin k → ℕ

/-- Logical chunk width when splitting a logical width across `k` slots. -/
def splitLogicalWidth (w k : ℕ) (i : Fin k) : ℕ :=
  chunkSize w k i

-- /-- Initial logical widths come from the current semantic widths of `x` and `z`,
--     not just from the raw physical register sizes. -/
-- def initWidthState (x z : ExtReg) (k : ℕ) : WidthState k where
--   xw := fun i => splitLogicalWidth (ExtReg.width x) k i
--   zw := fun i => splitLogicalWidth (ExtReg.width z) k i

def updateWidthState {k : ℕ} (st : WidthState k) : valid_ops k → WidthState k
  | .shiftL i n =>
      { xw := Function.update st.xw i (st.xw i + n)
        zw := Function.update st.zw i (st.zw i + n) }
  | .shiftR i n =>
      { xw := Function.update st.xw i (st.xw i - n)
        zw := Function.update st.zw i (st.zw i - n) }
  | .negate i =>
      { xw := Function.update st.xw i (st.xw i + 1)
        zw := Function.update st.zw i (st.zw i + 1) }
  | .addScaled dst src _negsrc sh =>
      let newX := 1 + max (st.xw dst) (st.xw src + sh)
      let newZ := 1 + max (st.zw dst) (st.zw src + sh)
      { xw := Function.update st.xw dst newX
        zw := Function.update st.zw dst newZ }
  | .phaseProduct _ =>
      st

structure NeededWidths (k : ℕ) where
  xneed : Fin k → ℕ
  zneed : Fin k → ℕ

def mergeNeededWidths {k : ℕ} (a b : NeededWidths k) : NeededWidths k where
  xneed := fun i => max (a.xneed i) (b.xneed i)
  zneed := fun i => max (a.zneed i) (b.zneed i)

def widthsOfState {k : ℕ} (st : WidthState k) : NeededWidths k where
  xneed := st.xw
  zneed := st.zw
/-- Ceiling division. Kept because other code may still use it. -/
def ceilDiv (n k : ℕ) : ℕ :=
  (n + k - 1) / k

/--
Lower-limb width for the top-heavy phase layout.

This deliberately uses floor division. The lower `k - 1` limbs have width `w / k`,
and the most significant limb absorbs all remaining bits.
For example, `w = 5`, `k = 4` gives widths `1, 1, 1, 2`.
-/
def phaseLimbWidthOfWidth (w k : ℕ) : ℕ :=
  w / k

/--
Common radix width for decomposing both operands.

Use `min`, not `max`: the lower limbs must fit inside both operands.
The larger operand simply gets a larger top chunk.
-/
def phaseLimbWidth (x z : ExtReg) (k : ℕ) : ℕ :=
  min (phaseLimbWidthOfWidth (ExtReg.width x) k)
      (phaseLimbWidthOfWidth (ExtReg.width z) k)

/-! =========================================================
    Top-heavy uniform lower-limb layout for PhaseProduct decomposition
========================================================= -/

/-- The most significant chunk is the last chunk. -/
def isTopChunk {k : ℕ} (i : Fin k) : Prop :=
  i.1 + 1 = k

instance {k : ℕ} (i : Fin k) : Decidable (isTopChunk i) := by
  unfold isTopChunk
  infer_instance

/-- Start offset of chunk `i` in the uniform-radix phase layout. -/
def phaseChunkStart (W : ℕ) (i : ℕ) : ℕ :=
  i * W

/--
End offset of a non-top chunk.

For the new top-heavy layout, this is only used for non-top chunks.
The top chunk ends at the full physical register size.
-/
def phaseChunkEnd (W : ℕ) (i : ℕ) : ℕ :=
  (i + 1) * W

/--
Physical slot for chunk `i` using the top-heavy uniform-radix layout.

Non-top chunks are `[i * W, (i + 1) * W)`.
The top chunk is `[(k - 1) * W, regSize r)`, so all leftover MSB bits go into
the top chunk.
-/
def phaseSlot (r : Reg) (k W : ℕ) (i : Fin k) : Reg :=
  let n := regSize r
  let loOff := Nat.min n (phaseChunkStart W i.1)
  let hiOff :=
    if isTopChunk i then
      n
    else
      Nat.min n (phaseChunkEnd W i.1)
  { lo := r.lo + loOff, size := hiOff - loOff }

lemma phaseSlot_loOff_le_hiOff (r : Reg) (k W : ℕ) (i : Fin k) :
    Nat.min (regSize r) (phaseChunkStart W i.1) ≤
      if isTopChunk i then
        regSize r
      else
        Nat.min (regSize r) (phaseChunkEnd W i.1) := by
  by_cases htop : isTopChunk i
  · simp [htop]
  · simpa [htop, phaseChunkStart, phaseChunkEnd] using
      (min_le_min_left (regSize r) (Nat.mul_le_mul_right W (Nat.le_succ i.1)))

lemma phaseSlot_hi_eq (r : Reg) (k W : ℕ) (i : Fin k) :
    (phaseSlot r k W i).hi =
      r.lo +
        (if isTopChunk i then
          regSize r
        else
          Nat.min (regSize r) (phaseChunkEnd W i.1)) := by
  let n := regSize r
  let loOff := Nat.min n (phaseChunkStart W i.1)
  let hiOff := if isTopChunk i then n else Nat.min n (phaseChunkEnd W i.1)
  have hle : loOff ≤ hiOff := by
    dsimp [loOff, hiOff, n]
    exact phaseSlot_loOff_le_hiOff r k W i
  unfold phaseSlot Reg.hi
  simp [loOff, hiOff, n, hle]

/--
Uniform lower-limb layout with all excess placed in the most significant chunk.

This is the layout wanted for radix reconstruction:
`x = x₀ + x₁ B + ... + x_{k-1} B^{k-1}`,
where `B = 2^W`.
-/
def phaseLayoutOfReg (r : Reg) (k W : ℕ) : Layout k where
  slot := fun i => phaseSlot r k W i
  disjoint := by
    intro i j hij
    have hij_val : i.1 ≠ j.1 := by
      intro hEq
      apply hij
      exact Fin.ext hEq
    rcases lt_or_gt_of_ne hij_val with hlt | hgt
    · left
      have hi_not_top : ¬ isTopChunk i := by
        intro htop
        unfold isTopChunk at htop
        omega
      have hsucc : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hlt
      have hmul : (i.1 + 1) * W ≤ j.1 * W :=
        Nat.mul_le_mul_right W hsucc
      have hmin :
          Nat.min (regSize r) (phaseChunkEnd W i.1)
            ≤ Nat.min (regSize r) (phaseChunkStart W j.1) := by
        unfold phaseChunkEnd phaseChunkStart
        exact min_le_min_left _ hmul
      rw [phaseSlot_hi_eq (r := r) (k := k) (W := W) (i := i)]
      simpa [phaseSlot, hi_not_top, phaseChunkStart] using
        Nat.add_le_add_left hmin r.lo
    · right
      have hj_not_top : ¬ isTopChunk j := by
        intro htop
        unfold isTopChunk at htop
        omega
      have hsucc : j.1 + 1 ≤ i.1 := Nat.succ_le_of_lt hgt
      have hmul : (j.1 + 1) * W ≤ i.1 * W :=
        Nat.mul_le_mul_right W hsucc
      have hmin :
          Nat.min (regSize r) (phaseChunkEnd W j.1)
            ≤ Nat.min (regSize r) (phaseChunkStart W i.1) := by
        unfold phaseChunkEnd phaseChunkStart
        exact min_le_min_left _ hmul
      rw [phaseSlot_hi_eq (r := r) (k := k) (W := W) (i := j)]
      simpa [phaseSlot, hj_not_top, phaseChunkStart] using
        Nat.add_le_add_left hmin r.lo

/--
Logical width of chunk `i`.

All non-top chunks have width `W`. The top chunk has the remaining width.
With the new top-heavy physical layout, this now matches the physical split.
-/
def phaseSplitLogicalWidth (w W k : ℕ) (i : Fin k) : ℕ :=
  if isTopChunk i then
    w - i.1 * W
  else
    W

/--
This compatibility predicate is now optional.

For the new floor/min top-heavy layout, the relevant compatibility condition is
true by construction for the lower chunks. I am leaving the definition in place
so older lemmas depending on the name do not immediately break.
-/
def PhaseLayoutCompatibleWidth (w W k : ℕ) : Prop :=
  ∀ i : Fin k, ¬ isTopChunk i → (i.1 + 1) * W ≤ w

/-- Compatibility for both operands. Kept for backward compatibility. -/
def PhaseLayoutCompatible (x z : ExtReg) (k : ℕ) : Prop :=
  let W := phaseLimbWidth x z k
  PhaseLayoutCompatibleWidth (ExtReg.width x) W k ∧
  PhaseLayoutCompatibleWidth (ExtReg.width z) W k

/-- Initial width bookkeeping now uses the uniform lower-limb phase layout. -/
def initWidthState (x z : ExtReg) (k : ℕ) : WidthState k :=
  let W := phaseLimbWidth x z k
  { xw := fun i => phaseSplitLogicalWidth (ExtReg.width x) W k i
    zw := fun i => phaseSplitLogicalWidth (ExtReg.width z) W k i }

/-- Pull the recursion in `scanNeededWidths` out to a top-level helper. -/
def scanNeededWidthsAux {k : ℕ} (cur : WidthState k) (mx : NeededWidths k) :
    List (valid_ops k) → NeededWidths k
  | [] => mx
  | op :: rest =>
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      scanNeededWidthsAux cur' mx' rest

/-- Scan needed widths using the new initial width state. -/
def scanNeededWidths {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
    NeededWidths k :=
  scanNeededWidthsAux
    (initWidthState x z k)
    (widthsOfState (initWidthState x z k))
    ops
/-- Build an `ExtReg` over a physical slot with the requested logical width. -/
def withLogicalWidth (r : Reg) (w : ℕ) : ExtReg :=
  { base := r, extra := w - regSize r }

/-- Common target width so that all chunks are widened to the same size. -/
def commonNeededWidth {k : ℕ} (need : NeededWidths k) : ℕ :=
  1 + Finset.univ.sup (fun i : Fin k => max (need.xneed i) (need.zneed i))



/-! =========================================================
    Replacement definitions for Section 5
========================================================= -/



/-- Initial chunk views for the uniform-radix phase decomposition. -/
def initSignedLayoutState (x z : ExtReg) (k : ℕ) : LayoutState k :=
  let W := phaseLimbWidth x z k
  { xslot := fun i =>
      let r := (phaseLayoutOfReg x.base k W).slot i
      withLogicalWidth r (phaseSplitLogicalWidth (ExtReg.width x) W k i)
    zslot := fun i =>
      let r := (phaseLayoutOfReg z.base k W).slot i
      withLogicalWidth r (phaseSplitLogicalWidth (ExtReg.width z) W k i) }

/--
Final widened chunk views for the compiled signed body.

The physical slots are still the uniform-radix slots from `phaseLayoutOfReg`.
Only the logical storage width is widened to the work width `commonNeededWidth need`.
-/
def targetSignedLayoutState
    (x z : ExtReg) (k : ℕ) (need : NeededWidths k) : LayoutState k :=
  let Wphase := phaseLimbWidth x z k
  let Wwork := commonNeededWidth need
  { xslot := fun i =>
      let r := (phaseLayoutOfReg x.base k Wphase).slot i
      withLogicalWidth r Wwork
    zslot := fun i =>
      let r := (phaseLayoutOfReg z.base k Wphase).slot i
      withLogicalWidth r Wwork }



/-! =========================================================
    Section 6: Interpolation and phase coefficients
========================================================= -/

/-- Number of interpolation points used for radix-`k` phase decomposition. -/
def q (k : ℕ) : ℕ := 2 * k - 1

/-- One entry of the interpolation matrix. -/
def interpEntry (k : ℕ) (p : Point) (j : Fin (q k)) : ℚ :=
  match p with
  | .int z => (z : ℚ) ^ (j : ℕ)
  | .inf   => if (j : ℕ) = q k - 1 then 1 else 0

/-- Interpolation matrix built from the chosen point set. -/
def interpMatrix
  (k : ℕ)
  (pts : Fin (q k) → Point) :
  Matrix (Fin (q k)) (Fin (q k)) ℚ :=
  fun i j => interpEntry k (pts i) j

/-- Row vector `[1, b, b^2, ...]` used for interpolation evaluation. -/
def radixRow (k : ℕ) (b : ℚ) :
  Matrix (Fin 1) (Fin (q k)) ℚ :=
  fun _ j => b ^ (j : ℕ)

/-- Interpolated phase coefficients evaluated at radix `b`. -/
noncomputable def phaseCoeffFromPts
  (k : ℕ)
  (pts : Fin (q k) → Point)
  (b : ℚ) :
  Fin (q k) → ℚ :=
  let B : Matrix (Fin (q k)) (Fin (q k)) ℚ := interpMatrix k pts
  let v : Matrix (Fin 1) (Fin (q k)) ℚ := radixRow k b * B⁻¹
  fun i => v 0 i


/-- Convert a point list of the right length into a `Fin`-indexed family. -/
def ptsToFin
  (k : ℕ)
  (pts : List Point)
  (hpts : pts.length = q k) :
  Fin (q k) → Point :=
  fun i =>
    pts.get
      ⟨
        i.val,
        by
          have hi : i.val < q k := i.is_lt
          simp [hpts]
      ⟩

/-- Radix used for chunked phase decomposition. -/
def phaseRadix (x : Reg) (k : ℕ) : ℚ :=
  (2 : ℚ) ^ ((regSize x) / k)

def phaseRadixWidth (w k : ℕ) : ℚ :=
  (2 : ℚ) ^ (w / k)

def chunkRadix (W : ℕ) : ℚ :=
  (2 : ℚ) ^ W

noncomputable def phaseCoeffFromPtsWidth
  (k : ℕ) (W : ℕ)
  (pts : List Point) (hpts : pts.length = q k) :
  Fin (q k) → ℚ :=
  phaseCoeffFromPts k (ptsToFin k pts hpts) ((2 : ℚ) ^ W)

noncomputable def phaseCoeffFromPtsForRegs
  (k : ℕ) (x z : ExtReg)
  (pts : List Point) (hpts : pts.length = q k) :
  Fin (q k) → ℚ :=
  phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts


/-- The size parameter used when deciding whether a signed phase product
    should recurse again. -/
def phaseInputSize (x z : ExtReg) : ℕ :=
  max (ExtReg.width x) (ExtReg.width z)

/-- The actual width of the recursively compiled chunk phase products. -/
def nextSignedWidth {k : ℕ} (x z : ExtReg) (ops : Prog k) : ℕ :=
  commonNeededWidth (scanNeededWidths x z ops)


structure AnnotatedOp (k : ℕ) where
  op : valid_ops k
  phaseTerm? : Option (Fin (q k))

def annotatePhaseTermsAux
  (k : ℕ)
  (n : ℕ)
  (ops : List (valid_ops k)) :
  List (AnnotatedOp k) :=
  match ops with
  | [] => []
  | op :: rest =>
      match op with
      | .phaseProduct _i =>
          let ann : Option (Fin (q k)) :=
            if h : n < q k then some ⟨n, h⟩ else none
          ⟨op, ann⟩ :: annotatePhaseTermsAux k (n+1) rest
      | _ =>
          ⟨op, none⟩ :: annotatePhaseTermsAux k n rest

def phaseProductCount {k : ℕ} : List (valid_ops k) → ℕ
  | [] => 0
  | op :: ops =>
      match op with
      | .phaseProduct _ => phaseProductCount ops + 1
      | _               => phaseProductCount ops

lemma annotatePhaseTermsAux_append
  (k : ℕ) (n : ℕ)
  (ops₁ ops₂ : List (valid_ops k)) :
  annotatePhaseTermsAux k n (ops₁ ++ ops₂) =
    annotatePhaseTermsAux k n ops₁ ++
      annotatePhaseTermsAux k (n + phaseProductCount ops₁) ops₂ := by
  induction ops₁ generalizing n with
  | nil =>
      simp [annotatePhaseTermsAux, phaseProductCount]
  | cons op ops₁ ih =>
      cases op <;>simp [annotatePhaseTermsAux, phaseProductCount, ih, Nat.add_assoc, Nat.add_comm]

lemma annotatePhaseTermsAux_append_zero
  (k : ℕ) (ops₁ ops₂ : List (valid_ops k)) :
  annotatePhaseTermsAux k 0 (ops₁ ++ ops₂) =
    annotatePhaseTermsAux k 0 ops₁ ++
      annotatePhaseTermsAux k (phaseProductCount ops₁) ops₂ := by
  simpa using annotatePhaseTermsAux_append k 0 ops₁ ops₂


/-- The most significant chunk is the last chunk. It gets sign-extension;
    all lower chunks get zero-extension. -/

instance {k : ℕ} (i : Fin k) : Decidable (isTopChunk i) := by
  unfold isTopChunk
  infer_instance

/-- Number of additional high bits needed to go from `src` to `dst`. -/
def extraDelta (src dst : ExtReg) : ℕ :=
  dst.extra - src.extra

/-- Allocation gate for a single chunk. Lower chunks are zero-extended;
    the top chunk is sign-extended. -/
def allocChunkGate {k : ℕ} (i : Fin k) (src dst : ExtReg) : Gate :=
  let n := extraDelta src dst
  if _h0 : n = 0 then
    Gate.id
  else if _htop : isTopChunk i then
    Gate.signExtend src n
  else
    Gate.zeroExtend src n

/-- Matching deallocation gate for a single chunk. -/
def deallocChunkGate {k : ℕ} (i : Fin k) (src dst : ExtReg) : Gate :=
  let n := extraDelta src dst
  if _h0 : n = 0 then
    Gate.id
  else if _htop : isTopChunk i then
    Gate.signDealloc src n
  else
    Gate.zeroDealloc src n

/-- Allocation program for the first `n` chunks, in increasing order `0,1,...,n-1`. -/
def compileSignedAllocationsAux {k : ℕ} (src dst : LayoutState k) :
    ∀ (n : ℕ), n ≤ k → Gate
  | 0, _ => Gate.id
  | n + 1, hn =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      compileSignedAllocationsAux src dst n hk' ;;
      allocChunkGate i (src.xslot i) (dst.xslot i) ;;
      allocChunkGate i (src.zslot i) (dst.zslot i)

/-- Emit all chunk allocations before the signed arithmetic body. -/
def compileSignedAllocations (k : ℕ) (src dst : LayoutState k) : Gate :=
  compileSignedAllocationsAux src dst k (le_rfl)

/-- Deallocation program for the first `n` chunks, in decreasing order `n-1,...,1,0`. -/
def compileSignedDeallocationsAux {k : ℕ} (src dst : LayoutState k) :
    ∀ (n : ℕ), n ≤ k → Gate
  | 0, _ => Gate.id
  | n + 1, hn =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
      deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
      compileSignedDeallocationsAux src dst n hk'

/-- Emit all chunk deallocations after the signed arithmetic body. -/
def compileSignedDeallocations (k : ℕ) (src dst : LayoutState k) : Gate :=
  compileSignedDeallocationsAux src dst k (le_rfl)

@[simp] lemma compileSignedAllocationsAux_zero {k : ℕ} (src dst : LayoutState k) (h : 0 ≤ k) :
  compileSignedAllocationsAux src dst 0 h = Gate.id := rfl

@[simp] lemma compileSignedAllocationsAux_succ {k : ℕ} (src dst : LayoutState k)
  (n : ℕ) (hn : n + 1 ≤ k) :
  compileSignedAllocationsAux src dst (n + 1) hn
    =
  let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
  let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
  compileSignedAllocationsAux src dst n hk' ;;
  allocChunkGate i (src.xslot i) (dst.xslot i) ;;
  allocChunkGate i (src.zslot i) (dst.zslot i) := rfl

@[simp] lemma compileSignedDeallocationsAux_zero {k : ℕ} (src dst : LayoutState k) (h : 0 ≤ k) :
  compileSignedDeallocationsAux src dst 0 h = Gate.id := rfl

@[simp] lemma compileSignedDeallocationsAux_succ {k : ℕ} (src dst : LayoutState k)
  (n : ℕ) (hn : n + 1 ≤ k) :
  compileSignedDeallocationsAux src dst (n + 1) hn
    =
  let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
  let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
  deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
  deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
  compileSignedDeallocationsAux src dst n hk' := rfl



/-! =========================================================
    Section 7: Compilation from valid ops to `Gate`
========================================================= -/

/-- Signed compiler for annotated ops.  The layout state already contains
    enough extra width in each slot, so compilation only emits gates and does
    not resize the state further. -/
def compileAnnotatedOpsToSignedGateAux
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (ops : List (AnnotatedOp k)) : Gate :=
  match ops with
  | [] => Gate.id
  | ⟨op, term?⟩ :: rest =>
      let tail := compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st rest
      match op with
      | .shiftL i n =>
          Gate.ShiftL (st.xslot i) n ;;
          Gate.ShiftL (st.zslot i) n ;; tail
      | .shiftR i n =>
          Gate.ShiftR (st.xslot i) n ;;
          Gate.ShiftR (st.zslot i) n ;; tail
      | .negate i =>
          Gate.Negate (st.xslot i) ;;
          Gate.Negate (st.zslot i) ;; tail
      | .addScaled dst src negsrc sh =>
          Gate.AddScaled (st.xslot dst) (st.xslot src) negsrc sh ;;
          Gate.AddScaled (st.zslot dst) (st.zslot src) negsrc sh ;; tail
      | .phaseProduct i =>
          match term? with
          | some l =>
              Gate.SignedPhaseProd
                (phi * ((phaseCoeff l : ℚ) : ℝ))
                (st.xslot i)
                (st.zslot i) ;; tail
          | none =>
              tail

noncomputable def compileOpsToSignedGate
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (phaseCoeff : Fin (q k) → ℚ)
  (ops : List (valid_ops k)) : Gate :=
  let annOps : List (AnnotatedOp k) :=
    annotatePhaseTermsAux k 0 ops
  let need : NeededWidths k :=
    scanNeededWidths x z ops
  let stInit : LayoutState k :=
    initSignedLayoutState x z k
  let stFinal : LayoutState k :=
    targetSignedLayoutState x z k need
  let allocs : Gate :=
    compileSignedAllocations k stInit stFinal
  let body : Gate :=
    compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff stFinal annOps
  let deallocs : Gate :=
    compileSignedDeallocations k stInit stFinal
  allocs ;; body ;; deallocs


-- noncomputable def compileOpsToSignedGate
--   (k : ℕ) (hk : 1 < k)
--   (phi : ℝ)
--   (x z : ExtReg)
--   (phaseCoeff : Fin (q k) → ℚ)
--   (ops : List (valid_ops k)) : Gate :=
--   let annOps : List (AnnotatedOp k) :=
--     annotatePhaseTermsAux k 0 ops
--   let need : NeededWidths k :=
--     scanNeededWidths x z ops
--   let stInit : LayoutState k :=
--     initSignedLayoutState x z k
--   let stFinal : LayoutState k :=
--     targetSignedLayoutState x z k need
--   let allocs : Gate :=
--     compileSignedAllocations k stInit stFinal
--   let body : Gate :=
--     compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff stFinal annOps
--   let deallocs : Gate :=
--     compileSignedDeallocations k stInit stFinal
--   allocs ;; body ;; deallocs


def tcMod (r : Reg) (z : ℤ) : ℕ :=
  Int.toNat (z % (ASize r : ℤ))

def tcNegVal (r : Reg) (x : ℕ) : ℕ :=
  tcMod r (-(x : ℤ))

def tcAddScaledVal
    {β : Type} [RegEncoding β]
    (dst src : Reg) (negSrc : Bool) (sh : ℕ) (b : β) : ℕ :=
  let sgn : ℤ := if negSrc then -1 else 1
  tcMod dst
    ((RegEncoding.toNat dst b : ℤ) +
      sgn * (RegEncoding.toNat src b : ℤ) * ((2 : ℤ) ^ sh))

open Gate
open Operations

variable (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
variable [GateSemanticsFacts qs]


/-! =========================================================
    Section 13: Extensionality from basis states
========================================================= -/

omit [RegEncoding QSemantics.Basis] in
lemma gate_eq_of_ket_eq
  {U V : Gate}
  (hket : ∀ b : qs.Basis, qs.eval U (qs.ket b) = qs.eval V (qs.ket b)) :
  ∀ ψ : qs.State, qs.eval U ψ = qs.eval V ψ := by
  intro ψ
  let P : qs.State → Prop := fun ψ => qs.eval U ψ = qs.eval V ψ
  have h0 : P 0 := by
    dsimp [P]
    rw [qs.eval_zero, qs.eval_zero]
  have hadd : ∀ ψ φ, P ψ → P φ → P (ψ + φ) := by
    intro ψ φ hψ hφ
    dsimp [P] at *
    rw [qs.eval_add, qs.eval_add, hψ, hφ]
  have hsmul : ∀ (a : ℂ) ψ, P ψ → P (a • ψ) := by
    intro a ψ hψ
    dsimp [P] at *
    rw [qs.eval_smul, qs.eval_smul, hψ]
  have hbasis : ∀ b : qs.Basis, P (qs.ket b) := by
    intro b
    dsimp [P]
    exact hket b
  exact qs.state_induction P h0 hadd hsmul hbasis ψ

open scoped BigOperators

open scoped BigOperators

/-- Mathematically exact polynomial evaluation of a register's chunks at a point. -/
noncomputable def pointEval {qs : QSemantics} [RegEncoding qs.Basis]
  (r : Reg) (k : ℕ) (hk : 0 < k) (b : qs.Basis) (pt : Point) : ℝ :=
  match pt with
  | .int z => ∑ i : Fin k,
      (RegEncoding.toNat ((layoutOfReg r k).slot i) b : ℝ) * (z : ℝ) ^ (i.val)
  | .inf   =>
      RegEncoding.toNat ((layoutOfReg r k).slot ⟨k - 1, Nat.sub_lt hk (by decide)⟩) b



@[simp] lemma phaseProductCount_addConstAux
  {k : ℕ} (dst src : Fin k) (neg' : Bool) (n sh : ℕ) :
  phaseProductCount (addConstAux (k := k) dst src neg' n sh) = 0 := by
  rw [addConstAux_eq_shifts (k := k) (dst := dst) (src := src) (neg' := neg') n sh]
  induction shiftsOfAux n sh with
  | nil =>
      simp [phaseProductCount]
  | cons s ss ih =>
      simp [phaseProductCount, ih]

@[simp] lemma phaseProductCount_addConstFrom
  {k : ℕ} (dst src : Fin k) (c : Int) :
  phaseProductCount (addConstFrom (k := k) dst src c) = 0 := by
  by_cases hc : c = 0
  · simp [addConstFrom, hc, phaseProductCount]
  · simp [addConstFrom, hc, phaseProductCount_addConstAux]

@[simp] lemma phaseProductCount_append
  {k : ℕ} (xs ys : List (valid_ops k)) :
  phaseProductCount (xs ++ ys) =
    phaseProductCount xs + phaseProductCount ys := by
  induction xs with
  | nil =>
      simp [phaseProductCount]
  | cons op xs ih =>
      cases op <;> simp [phaseProductCount, ih,  Nat.add_comm, Nat.add_left_comm]

@[simp] lemma phaseProductCount_computeLocalAux
  {k : ℕ} (hk : 0 < k) (z : Int) :
  ∀ js : List (Fin k), phaseProductCount (computeLocalAux (k := k) hk z js) = 0
  | [] => by
      simp [computeLocalAux, phaseProductCount]
  | j :: js => by
      simp [computeLocalAux, phaseProductCount_append,
            phaseProductCount_addConstFrom,
            phaseProductCount_computeLocalAux]

@[simp] lemma phaseProductCount_computeLocal2
  {k : ℕ} (hk : 0 < k) (z : Int) :
  phaseProductCount (computeLocal2 (k := k) hk z) = 0 := by
  simp [computeLocal2, phaseProductCount_computeLocalAux]


/-! =========================================================
    Section 14: Compiler correctness theorems
========================================================= -/
def slotVal
  (x : Reg) (k : ℕ) (j : Fin k) (b : qs.Basis) : ℕ :=
  RegEncoding.toNat ((layoutOfReg x k).slot j) b

def pointValue
  (k : ℕ) (pt : Point) (x : Reg) (b : qs.Basis) : ℤ :=
  ∑ j : Fin k, (expectedRow (k := k) pt j) * (slotVal (qs := qs) x k j b : ℤ)



open ExtRegEncoding

/-- How the original source basis should be read when forming chunk rows:
    lower chunks are ordinary radix digits, while the top chunk is signed. -/
def sourceChunkXInt
  (st : LayoutState k) (i : Fin k) (b : qs.Basis) : ℤ :=
  if isTopChunk i then
    ExtRegEncoding.extToInt (st.xslot i) b
  else
    (ExtReg.toNat (st.xslot i) b : ℤ)

/-- Same mixed source interpretation for the `z` slots. -/
def sourceChunkZInt
  (st : LayoutState k) (i : Fin k) (b : qs.Basis) : ℤ :=
  if isTopChunk i then
    ExtRegEncoding.extToInt (st.zslot i) b
  else
    (ExtReg.toNat (st.zslot i) b : ℤ)

/-- Row evaluation of `x` against the original basis:
    lower chunks contribute as unsigned digits, top chunk as signed. -/
def evalRowX
  (st : LayoutState k) (r : Register k) (b : qs.Basis) : ℤ :=
  ∑ j : Fin k, r j * sourceChunkXInt (qs := qs) st j b

/-- Row evaluation of `z` against the original basis:
    lower chunks contribute as unsigned digits, top chunk as signed. -/
def evalRowZ
  (st : LayoutState k) (r : Register k) (b : qs.Basis) : ℤ :=
  ∑ j : Fin k, r j * sourceChunkZInt (qs := qs) st j b

/-- One-layout encoding relation: the current machine state is read signed,
    while the reference basis is interpreted by the mixed chunk semantics above. -/
def EncodesState
  (st : LayoutState k) (σ : State k) (b0 b : qs.Basis) : Prop :=
  (∀ i : Fin k,
    ExtRegEncoding.extToInt (st.xslot i) b
      = evalRowX (qs := qs) st (σ i) b0) ∧
  (∀ i : Fin k,
    ExtRegEncoding.extToInt (st.zslot i) b
      = evalRowZ (qs := qs) st (σ i) b0)

/-- Two-layout version: the current widened machine state is read signed on `dst`,
    while the original basis is interpreted using the mixed chunk semantics on `src`. -/
def EncodesStateFrom
  (src dst : LayoutState k) (σ : State k) (b0 b : qs.Basis) : Prop :=
  (∀ i : Fin k,
    ExtRegEncoding.extToInt (dst.xslot i) b
      = evalRowX (qs := qs) src (σ i) b0) ∧
  (∀ i : Fin k,
    ExtRegEncoding.extToInt (dst.zslot i) b
      = evalRowZ (qs := qs) src (σ i) b0)

def EncodesStateFromFits
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src dst : LayoutState k) (σ : State k) (b0 b : qs.Basis) : Prop :=
  EncodesStateFrom (qs := qs) src dst σ b0 b ∧
  (∀ i : Fin k,
    FitsSignedWidth (ExtReg.width (dst.xslot i))
      (evalRowX (qs := qs) src (σ i) b0)) ∧
  (∀ i : Fin k,
    FitsSignedWidth (ExtReg.width (dst.zslot i))
      (evalRowZ (qs := qs) src (σ i) b0))

def WidthStateSound
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k) (cur : WidthState k) (σ : State k) (b0 : qs.Basis) : Prop :=
  (∀ i : Fin k,
    FitsSignedWidth (cur.xw i)
      (evalRowX (qs := qs) src (σ i) b0)) ∧
  (∀ i : Fin k,
    FitsSignedWidth (cur.zw i)
      (evalRowZ (qs := qs) src (σ i) b0))

def WidthStateDominatedByLayout
  {k : ℕ} (cur : WidthState k) (dst : LayoutState k) : Prop :=
  (∀ i : Fin k, cur.xw i ≤ ExtReg.width (dst.xslot i)) ∧
  (∀ i : Fin k, cur.zw i ≤ ExtReg.width (dst.zslot i))

def EncodesStateFromWithWidths
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src dst : LayoutState k) (cur : WidthState k)
  (σ : State k) (b0 b : qs.Basis) : Prop :=
  EncodesStateFrom (qs := qs) src dst σ b0 b ∧
  WidthStateSound (qs := qs) src cur σ b0 ∧
  WidthStateDominatedByLayout cur dst

lemma EncodesStateFromWithWidths.toFits
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  {src dst : LayoutState k} {cur : WidthState k}
  {σ : State k} {b0 b : qs.Basis}
  (h : EncodesStateFromWithWidths
    (qs := qs) src dst cur σ b0 b) :
  EncodesStateFromFits (qs := qs) src dst σ b0 b := by
  rcases h with ⟨hEnc, hSoundX, hDom⟩
  rcases hSoundX with ⟨hSoundX, hSoundZ⟩
  rcases hDom with ⟨hDomX, hDomZ⟩
  refine ⟨hEnc, ?_, ?_⟩
  ·
    intro i
    exact FitsSignedWidth_mono (hDomX i) (hSoundX i)
  ·
    intro i
    exact FitsSignedWidth_mono (hDomZ i) (hSoundZ i)

/-- The accumulated scalar now uses the same mixed source-row semantics as
    `EncodesStateFrom`, so the body lemma stays aligned with the invariant. -/
noncomputable def phaseScalarFrom
  (k : ℕ) (phi : ℝ) (coeff : Fin (q k) → ℚ)
  (st : LayoutState k) (b0 : qs.Basis) :
  (pts : List Point) → (n : ℕ) → (hn : n + pts.length = q k) → ℂ
| [], n, hn => 1
| pt :: pts, n, hn =>
    let l : Fin (q k) := ⟨n, by
      have hlt : n < n + (pt :: pts).length := by
        simp
      aesop
    ⟩
    let hn' : n + 1 + pts.length = q k := by
      simp at hn
      omega
    Complex.exp
      ((phi * ((coeff l : ℚ) : ℝ)) * Complex.I *
        (((evalRowX (qs := qs) st (expectedRow (k := k) pt) b0 : ℤ) : ℂ) *
         (((evalRowZ (qs := qs) st (expectedRow (k := k) pt) b0 : ℤ) : ℂ))))
    * phaseScalarFrom k phi coeff st b0 pts (n + 1) hn'

lemma chunkSize_mono {k : ℕ} (i : Fin k) {n m : ℕ} (h : n ≤ m) :
  chunkSize n k i ≤ chunkSize m k i := by
  cases k with
  | zero =>
      apply i.elim0
  | succ k =>
      unfold chunkSize
      set qn : ℕ := n / (Nat.succ k)
      set rn : ℕ := n % (Nat.succ k)
      set qm : ℕ := m / (Nat.succ k)
      set rm : ℕ := m % (Nat.succ k)
      have hn : n = qn * (Nat.succ k) + rn := by
        dsimp [qn, rn]
        have:=(Nat.div_add_mod n (Nat.succ k)).symm
        simp at this
        rw[mul_comm,← this]
      have hm : m = qm * (Nat.succ k) + rm := by
        dsimp [qm, rm]
        have:=(Nat.div_add_mod m (Nat.succ k)).symm
        simp at this
        rw[mul_comm,← this]
      have hrn : rn < Nat.succ k := by
        dsimp [rn]
        exact Nat.mod_lt _ (Nat.succ_pos _)
      have hrm : rm < Nat.succ k := by
        dsimp [rm]
        exact Nat.mod_lt _ (Nat.succ_pos _)
      by_cases hin : i.1 < rn
      · by_cases him : i.1 < rm
        · simp[hin,him,qn,qm]
          exact Nat.div_le_div_right h
        · have hirn : i.1 + 1 ≤ rn := Nat.succ_le_of_lt hin
          have hirm : rm ≤ i.1 := Nat.le_of_not_gt him
          simp[hin,him,qn,qm]
          have h_rm_lt_rn : rm < rn := lt_of_le_of_lt hirm hin
          have hqn : n / (k + 1) = qn := by simp [qn]
          have hqm : m / (k + 1) = qm := by simp [qm]
          rw [hqn, hqm]
          have hneq : qn ≠ qm := by
            intro hqq
            simp[hqq] at *
            omega
          have hle : qn ≤ qm := by
            simp[qn,qm]
            exact Nat.div_le_div_right h
          exact lt_of_le_of_ne hle hneq

      · by_cases him : i.1 < rm
        · have hirn : rn ≤ i.1 := Nat.le_of_not_gt hin
          have hirm : i.1 + 1 ≤ rm := Nat.succ_le_of_lt him
          simp[hin,him,qn,qm]
          have:=Nat.div_le_div_right h (c:= k+1)
          omega
        · have hirn : rn ≤ i.1 := Nat.le_of_not_gt hin
          have hirm : rm ≤ i.1 := Nat.le_of_not_gt him
          simp[hin,him,qn,qm]
          exact Nat.div_le_div_right h

lemma slot_size_le_splitLogicalWidth_x {k : ℕ} (x : ExtReg) (i : Fin k) :
  regSize ((layoutOfReg x.base k).slot i) ≤ splitLogicalWidth (ExtReg.width x) k i := by
  simp [layoutOfReg, regSize, splitLogicalWidth]
  exact chunkSize_mono (i := i) (by
    simp [ExtReg.width,regSize])

lemma slot_size_le_splitLogicalWidth_z {k : ℕ} (z : ExtReg) (i : Fin k) :
  regSize ((layoutOfReg z.base k).slot i) ≤ splitLogicalWidth (ExtReg.width z) k i := by
  simp [layoutOfReg, regSize, splitLogicalWidth]
  exact chunkSize_mono (i := i) (by
    simp [ExtReg.width,regSize])



/-- I recommend replacing the original `scanNeededWidths` body by this exact helper call. -/
lemma scanNeededWidths_eq_aux {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
  scanNeededWidths x z ops =
    scanNeededWidthsAux (initWidthState x z k) (widthsOfState (initWidthState x z k)) ops := by
  simp[scanNeededWidths]


lemma scanNeededWidthsAux_x_ge
  {k : ℕ} (i : Fin k) :
  ∀ (ops : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    mx.xneed i ≤ (scanNeededWidthsAux cur mx ops).xneed i
  | [], cur, mx => by
      simp [scanNeededWidthsAux]
  | op :: rest, cur, mx => by
      simp [scanNeededWidthsAux]
      have htail :
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))).xneed i
            ≤
          (scanNeededWidthsAux
              (updateWidthState cur op)
              (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
              rest).xneed i :=
        scanNeededWidthsAux_x_ge
          (i := i)
          rest
          (updateWidthState cur op)
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
      exact le_trans (le_max_left _ _) htail

lemma scanNeededWidthsAux_z_ge
  {k : ℕ} (i : Fin k) :
  ∀ (ops : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    mx.zneed i ≤ (scanNeededWidthsAux cur mx ops).zneed i
  | [], cur, mx => by
      simp [scanNeededWidthsAux]
  | op :: rest, cur, mx => by
      simp [scanNeededWidthsAux]
      have htail :
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))).zneed i
            ≤
          (scanNeededWidthsAux
              (updateWidthState cur op)
              (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
              rest).zneed i :=
        scanNeededWidthsAux_z_ge
          (i := i)
          rest
          (updateWidthState cur op)
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
      exact le_trans (le_max_left _ _) htail


/-! =========================================================
    Helper stack for `allocated_widths_sound`
========================================================= -/

/-- Proof-only width invariant: the symbolic value fits in the tracked width
    plus one extra sign bit. This matches `commonNeededWidth = 1 + sup ...`. -/
def WidthStateSoundPlus
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k) (cur : WidthState k) (σ : State k) (b0 : qs.Basis) : Prop :=
  (∀ i : Fin k,
    FitsSignedWidth (cur.xw i + 1)
      (evalRowX (qs := qs) src (σ i) b0)) ∧
  (∀ i : Fin k,
    FitsSignedWidth (cur.zw i + 1)
      (evalRowZ (qs := qs) src (σ i) b0))

lemma FitsSignedWidth_of_nonneg_lt_pow
  {w : ℕ} {n : ℕ}
  (h : n < 2 ^ w) :
  FitsSignedWidth (w + 1) (n : ℤ) := by
  unfold FitsSignedWidth signedMin signedMax
  constructor <;> simp
  constructor
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hneg : (-(2 : ℤ) ^ (w + 1)) ≤ 0 := by
    have hpow0 : (0 : ℤ) ≤ (2 : ℤ) ^ (w + 1) := by positivity
    omega
  omega
  norm_cast

lemma tcDecodeWidth_fits_succ
  {w n : ℕ}
  (h : n < 2 ^ w) :
  FitsSignedWidth (w + 1) (tcDecodeWidth w n) := by
  unfold FitsSignedWidth signedMin signedMax tcDecodeWidth
  by_cases hs : n < 2 ^ (w - 1)
  · simp
    constructor <;>
    split
    next x x_1 =>
      simp_all only [pow_zero, Nat.lt_one_iff, zero_tsub, zero_lt_one, Int.reduceNeg, Left.neg_nonpos_iff,
        zero_le_one]
    next x x_1 w =>
      simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
        exact_mod_cast Nat.zero_le n
      have hneg : (-(2 : ℤ) ^ (w + 1)) ≤ 0 := by
        have hpow0 : (0 : ℤ) ≤ (2 : ℤ) ^ (w + 1) := by positivity
        omega
      omega
    simp
    simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
    norm_cast
  · simp
    constructor <;>
    split
    next x x_1 =>
      simp_all only [pow_zero, Nat.lt_one_iff, zero_tsub, zero_lt_one, Int.reduceNeg, Left.neg_nonpos_iff,
        zero_le_one]
      simp at hs
    next x x_1 w =>
      simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
      have hge : 2 ^ w ≤ n := Nat.le_of_not_lt hs
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
        exact_mod_cast Nat.zero_le n
      omega
    simp
    simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, not_lt]
    split
    next h_1 => norm_cast
    next h_1 =>
      simp_all only [not_lt]; rename_i x1 x w
      have hlt : (n : ℤ) < (2 : ℤ) ^ (w + 1) := by
        exact_mod_cast h
      omega

lemma extToInt_fits_width_succ
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (e : ExtReg) (b : qs.Basis) :
  FitsSignedWidth (ExtReg.width e + 1) (ExtRegEncoding.extToInt e b) := by
  unfold ExtRegEncoding.extToInt
  have hlt : ExtRegEncoding.extToNat e b < 2 ^ ExtReg.width e := by
    simpa using
      (ExtensionSemantics.extToNat_lt_width
        (qs := qs) (e := e) (b := b))
  exact tcDecodeWidth_fits_succ hlt


/-- If `z` fits signed width `w+1`, then `(2^n) * z` fits signed width `w+n+1`. -/
lemma FitsSignedWidth_shiftL_raw
  {w n : ℕ} {z : ℤ}
  (hfit : FitsSignedWidth (w + 1) z) :
  FitsSignedWidth (w + n + 1) (((2 : ℤ)^n) * z) := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  have hp0 : (0 : ℤ) ≤ (2 : ℤ)^n := by positivity
  have hp : (0 : ℤ) < (2 : ℤ)^n := by positivity

  have hpow :
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ))
        = (((2 ^ (w + n) : ℕ) : ℤ)) := by
    calc
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ))
          = (((2 ^ n : ℕ) : ℤ)) * (((2 ^ w : ℕ) : ℤ)) := by norm_num
      _ = (((2 ^ n * 2 ^ w : ℕ) : ℤ)) := by norm_num
      _ = (((2 ^ (n + w) : ℕ) : ℤ)) := by
            exact_mod_cast (pow_add 2 n w).symm
      _ = (((2 ^ (w + n) : ℕ) : ℤ)) := by rw [Nat.add_comm]

  have hpow_neg :
      ((2 : ℤ)^n) * (-(((2 ^ w : ℕ) : ℤ)))
        = -(((2 ^ (w + n) : ℕ) : ℤ)) := by
    simp
    rw[pow_add,mul_comm]

  have hL :
      ((2 : ℤ)^n) * (-(((2 ^ w : ℕ) : ℤ)))
        ≤
      ((2 : ℤ)^n) * z := by
    exact mul_le_mul_of_nonneg_left (by simp_all) hp0

  have hU :
      ((2 : ℤ)^n) * z
        <
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ)) := by
    exact mul_lt_mul_of_pos_left (by simp_all) hp

  constructor
  · simp
  · aesop

/-- If `z = 2^n * q` and `z` fits signed width `w+1`, then the exact quotient
    fits signed width `(w - n) + 1`. -/
lemma FitsSignedWidth_shiftR_of_mul
  {w n : ℕ} {z q : ℤ}
  (hfit : FitsSignedWidth (w + 1) z)
  (hz : z = ((2 : ℤ)^n) * q) :
  FitsSignedWidth (w - n + 1) q := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  by_cases hnw : n ≤ w
  · have hpos : (0 : ℤ) < (2 : ℤ)^n := by positivity

    have hpow :
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ))
          = (((2 ^ w : ℕ) : ℤ)) := by
      calc
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ))
            = (((2 ^ n : ℕ) : ℤ)) * (((2 ^ (w - n) : ℕ) : ℤ)) := by norm_num
        _ = (((2 ^ n * 2 ^ (w - n) : ℕ) : ℤ)) := by norm_num
        _ = (((2 ^ (n + (w - n)) : ℕ) : ℤ)) := by
              exact_mod_cast (pow_add 2 n (w - n)).symm
        _ = (((2 ^ w : ℕ) : ℤ)) := by rw [Nat.add_sub_of_le hnw]

    have hupper :
        ((2 : ℤ)^n) * q
          <
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ)) := by
      simp_all
    have hlower :
        ((2 : ℤ)^n) * (-(((2 ^ (w - n) : ℕ) : ℤ)))
          ≤
        ((2 : ℤ)^n) * q := by
      have : -(((2 ^ w : ℕ) : ℤ)) ≤ ((2 : ℤ)^n) * q := by
        simp_all
      simp_all

    constructor
    · simp_all
    · simp_all
      constructor
      · have h1 : -(2 ^ n * 2 ^ (w - n) : ℤ) ≤ 2 ^ n * q := by
          rw [hpow]; exact hhi.1
        have h2 : (2 ^ n : ℤ) * -(2 ^ (w - n)) ≤ 2 ^ n * q := by
          rw [mul_neg]; exact h1
        exact le_of_mul_le_mul_left h2 (by positivity)
      · have h1 : (2 ^ n * q : ℤ) < 2 ^ n * 2 ^ (w - n) := by
          rw [hpow]; exact hhi.2
        exact lt_of_mul_lt_mul_left h1 (by positivity)


  · have hwn : w < n := lt_of_not_ge hnw
    have hpowNat : 2 ^ w < 2 ^ n := by
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) hwn
    have hpowInt : (((2 ^ w : ℕ) : ℤ)) < ((2 : ℤ)^n) := by
      exact_mod_cast hpowNat

    have hq0 : q = 0 := by
      by_cases hq : q = 0
      · exact hq
      · rcases lt_or_gt_of_ne hq with hqneg | hqpos
        · have hqle : q ≤ -1 := by omega
          have hmul : ((2 : ℤ)^n) * q ≤ -((2 : ℤ)^n) := by
            calc
              ((2 : ℤ)^n) * q ≤ ((2 : ℤ)^n) * (-1) := by
                gcongr
              _ = -((2 : ℤ)^n) := by ring
          have hzlt : z < -(((2 ^ w : ℕ) : ℤ)) := by
            rw [hz]
            have hnegpow : -((2 : ℤ)^n) < -(((2 ^ w : ℕ) : ℤ)) := by
              omega
            exact lt_of_le_of_lt hmul hnegpow
          simp_all
          rcases hhi with ⟨hlo, hhi⟩
          omega
        · have hqge : (1 : ℤ) ≤ q := by omega
          have hmul : ((2 : ℤ)^n) ≤ ((2 : ℤ)^n) * q := by
            calc
              ((2 : ℤ)^n) = ((2 : ℤ)^n) * 1 := by ring
              _ ≤ ((2 : ℤ)^n) * q := by
                gcongr
          have hzgt : (((2 ^ w : ℕ) : ℤ)) < z := by
            rw [hz]
            exact lt_of_lt_of_le hpowInt hmul
          simp_all
          rcases hhi with ⟨hlo, hhi⟩
          omega

    subst hq0
    have hw0 : w - n = 0 := by omega
    rw [hw0]
    constructor <;> norm_num [signedMin, signedMax]

/-- Negation is always safe if we widen by one additional bit. -/
lemma FitsSignedWidth_neg_widen
  {w : ℕ} {z : ℤ}
  (hfit : FitsSignedWidth (w + 1) z) :
  FitsSignedWidth (w + 2) (-z) := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  have hpow : (((2 ^ w : ℕ) : ℤ)) ≤ (((2 ^ (w + 1) : ℕ) : ℤ)) := by
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ w))
  constructor <;> simp_all
  refine ⟨?_, ?_⟩
  · linarith [hhi.2, hpow]
  · have hpos : (0 : ℤ) < 2 ^ w := by positivity
    omega

/-- Adding a shifted source into a destination is safe in the width prescribed
    by `updateWidthState` (plus the proof-only extra sign bit). -/
lemma FitsSignedWidth_addScaled_widen
  {wd ws sh : ℕ} {dstv srcv : ℤ} (negSrc : Bool)
  (hdst : FitsSignedWidth (wd + 1) dstv)
  (hsrc : FitsSignedWidth (ws + 1) srcv) :
  FitsSignedWidth (max wd (ws + sh) + 2)
    (dstv + (if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ)^sh) * srcv) := by
  have hscaled :
      FitsSignedWidth (ws + sh + 1) (((2 : ℤ)^sh) * srcv) := by
    exact FitsSignedWidth_shiftL_raw (w := ws) (n := sh) (z := srcv) hsrc

  unfold FitsSignedWidth signedMin signedMax at hdst hscaled ⊢
  rcases hdst with ⟨hdlo, hdhi⟩
  rcases hscaled with ⟨hslo, hshi⟩

  set M : ℕ := max wd (ws + sh)

  have hwdM : (((2 ^ wd : ℕ) : ℤ)) ≤ (((2 ^ M : ℕ) : ℤ)) := by
    dsimp [M]
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_left wd (ws + sh)))

  have hwsM : (((2 ^ (ws + sh) : ℕ) : ℤ)) ≤ (((2 ^ M : ℕ) : ℤ)) := by
    dsimp [M]
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_right wd (ws + sh)))

  cases hsgn : negSrc <;> simp_all
  · constructor <;> omega
  · constructor <;> omega

/-- Start-state row evaluation picks out the requested x-slot. -/
lemma evalRowX_start_state
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} (st : LayoutState k) (i : Fin k) (b : qs.Basis) :
  evalRowX (qs := qs) st (State.start_state i) b = sourceChunkXInt (qs := qs) st i b := by
  unfold evalRowX State.start_state
  classical
  simp

/-- Start-state row evaluation picks out the requested z-slot. -/
lemma evalRowZ_start_state
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} (st : LayoutState k) (i : Fin k) (b : qs.Basis) :
  evalRowZ (qs := qs) st (State.start_state i) b = sourceChunkZInt (qs := qs) st i b := by
  unfold evalRowZ State.start_state
  classical
  simp

/-- If a physical slot is given logical width `w`, and its physical size is at most
    `w`, then the resulting `ExtReg` has width exactly `w`. -/
lemma withLogicalWidth_width_eq_of_le
  (r : Reg) (w : ℕ)
  (h : regSize r ≤ w) :
  ExtReg.width (withLogicalWidth r w) = w := by
  unfold withLogicalWidth ExtReg.width
  simp
  omega

/-- Small Nat lemma: clipping both endpoints by the same upper bound cannot
    increase the interval length. -/
lemma min_sub_min_le_sub
  {n a b : ℕ}
  (hab : a ≤ b) :
  Nat.min n b - Nat.min n a ≤ b - a := by
  by_cases hna : n ≤ a
  · have hnb : n ≤ b := le_trans hna hab
    simp [Nat.min_eq_left hna, Nat.min_eq_left hnb]
  · have han : a < n := Nat.lt_of_not_ge hna
    by_cases hnb : n ≤ b
    · have hmina : Nat.min n a = a := Nat.min_eq_right (Nat.le_of_lt han)
      have hminb : Nat.min n b = n := Nat.min_eq_left hnb
      rw [hmina, hminb]
      omega
    · have hbn : b < n := Nat.lt_of_not_ge hnb
      have hmina : Nat.min n a = a := Nat.min_eq_right (Nat.le_of_lt han)
      have hminb : Nat.min n b = b := Nat.min_eq_right (Nat.le_of_lt hbn)
      rw [hmina, hminb]
/-- Physical size of a phase slot is bounded by its logical top-heavy width. -/
lemma regSize_phaseSlot_le_splitWidth
    (r : Reg) (k W : ℕ) (i : Fin k)
    (w : ℕ)
    (hphys : regSize r ≤ w)
    (_hWle : W ≤ w / k) :
    regSize (phaseSlot r k W i) ≤ phaseSplitLogicalWidth w W k i := by
  by_cases htop : isTopChunk i
  · have hgoal : regSize r - Nat.min (regSize r) (i.1 * W) ≤ w - i.1 * W := by
      by_cases hle : regSize r ≤ i.1 * W
      · have hmin : Nat.min (regSize r) (i.1 * W) = regSize r :=
          Nat.min_eq_left hle
        rw [hmin]
        simp
      · have hlt : i.1 * W < regSize r := Nat.lt_of_not_ge hle
        have hmin : Nat.min (regSize r) (i.1 * W) = i.1 * W :=
          Nat.min_eq_right (Nat.le_of_lt hlt)
        rw [hmin]
        exact Nat.sub_le_sub_right hphys _
    simpa [phaseSlot, phaseSplitLogicalWidth, phaseChunkStart, htop, regSize] using hgoal
  · have hgoal : Nat.min (regSize r) ((i.1 + 1) * W) - Nat.min (regSize r) (i.1 * W) ≤ W := by
      have hstart_end : i.1 * W ≤ (i.1 + 1) * W := by
        exact Nat.mul_le_mul_right W (Nat.le_succ i.1)
      have hmin_le :
          Nat.min (regSize r) ((i.1 + 1) * W)
            - Nat.min (regSize r) (i.1 * W)
            ≤ ((i.1 + 1) * W) - (i.1 * W) :=
        min_sub_min_le_sub hstart_end
      have hdiff : ((i.1 + 1) * W) - (i.1 * W) = W := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      exact le_trans hmin_le (by simp [hdiff])
    simpa [phaseSlot, phaseSplitLogicalWidth, phaseChunkStart, phaseChunkEnd, htop, regSize] using hgoal

/-- The physical x-slot chosen by the phase layout fits inside its initial logical width. -/
lemma phaseSlot_size_le_initWidth_x
    {k : ℕ} (x z : ExtReg) (i : Fin k) :
    regSize ((phaseLayoutOfReg x.base k (phaseLimbWidth x z k)).slot i)
      ≤
    (initWidthState x z k).xw i := by
  dsimp [phaseLayoutOfReg, initWidthState]
  apply regSize_phaseSlot_le_splitWidth
  · simp [ExtReg.width]
  ·
    unfold phaseLimbWidth phaseLimbWidthOfWidth
    exact Nat.min_le_left _ _

/-- The physical z-slot chosen by the phase layout fits inside its initial logical width. -/
lemma phaseSlot_size_le_initWidth_z
    {k : ℕ} (x z : ExtReg) (i : Fin k) :
    regSize ((phaseLayoutOfReg z.base k (phaseLimbWidth x z k)).slot i)
      ≤
    (initWidthState x z k).zw i := by
  dsimp [phaseLayoutOfReg, initWidthState]
  apply regSize_phaseSlot_le_splitWidth
  · simp [ExtReg.width]
  ·
    unfold phaseLimbWidth phaseLimbWidthOfWidth
    exact Nat.min_le_right _ _

/-- Initial x-slot has exactly the width recorded in `initWidthState`. -/
lemma stInit_xslot_width
  {k : ℕ} (x z : ExtReg) (i : Fin k) :
  ExtReg.width ((initSignedLayoutState x z k).xslot i)
    =
  (initWidthState x z k).xw i := by
  dsimp [initSignedLayoutState, initWidthState]
  exact withLogicalWidth_width_eq_of_le
    ((phaseLayoutOfReg x.base k (phaseLimbWidth x z k)).slot i)
    (phaseSplitLogicalWidth (ExtReg.width x) (phaseLimbWidth x z k) k i)
    (by simpa [initWidthState] using phaseSlot_size_le_initWidth_x x z i)

/-- Initial z-slot has exactly the width recorded in `initWidthState`. -/
lemma stInit_zslot_width
  {k : ℕ} (x z : ExtReg) (i : Fin k) :
  ExtReg.width ((initSignedLayoutState x z k).zslot i)
    =
  (initWidthState x z k).zw i := by
  dsimp [initSignedLayoutState, initWidthState]
  exact withLogicalWidth_width_eq_of_le
    ((phaseLayoutOfReg z.base k (phaseLimbWidth x z k)).slot i)
    (phaseSplitLogicalWidth (ExtReg.width z) (phaseLimbWidth x z k) k i)
    (by simpa [initWidthState] using phaseSlot_size_le_initWidth_z x z i)

/-- Lower/top chunk of the initial x-layout fits its tracked initial width plus
    one extra sign bit. -/
lemma sourceChunkXInt_init_fits
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (x z : ExtReg) (i : Fin k) (b : qs.Basis) :
  FitsSignedWidth ((initWidthState x z k).xw i + 1)
    (sourceChunkXInt (qs := qs) (initSignedLayoutState x z k) i b) := by
  unfold sourceChunkXInt
  by_cases htop : isTopChunk i
  · simp [htop]
    have hwidth :
        ExtReg.width ((initSignedLayoutState x z k).xslot i)
          =
        (initWidthState x z k).xw i :=
      stInit_xslot_width x z i
    have hfit :
        FitsSignedWidth
          (ExtReg.width ((initSignedLayoutState x z k).xslot i) + 1)
          (ExtRegEncoding.extToInt ((initSignedLayoutState x z k).xslot i) b) :=
      extToInt_fits_width_succ
        (qs := qs)
        ((initSignedLayoutState x z k).xslot i)
        b
    simpa [hwidth] using hfit
  · simp [htop]
    have hwidth :
        ExtReg.width ((initSignedLayoutState x z k).xslot i)
          =
        (initWidthState x z k).xw i :=
      stInit_xslot_width x z i
    have hlt :
        ExtReg.toNat ((initSignedLayoutState x z k).xslot i) b
          <
        2 ^ ((initWidthState x z k).xw i) := by
      simpa [ExtReg.toNat, hwidth] using
        (ExtensionSemantics.extToNat_lt_width
          (qs := qs)
          (e := (initSignedLayoutState x z k).xslot i)
          (b := b))
    exact FitsSignedWidth_of_nonneg_lt_pow hlt


/-- Lower/top chunk of the initial z-layout fits its tracked initial width plus
    one extra sign bit. -/
lemma sourceChunkZInt_init_fits
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (x z : ExtReg) (i : Fin k) (b : qs.Basis) :
  FitsSignedWidth ((initWidthState x z k).zw i + 1)
    (sourceChunkZInt (qs := qs) (initSignedLayoutState x z k) i b) := by
  unfold sourceChunkZInt
  by_cases htop : isTopChunk i
  · simp [htop]
    have hwidth :
        ExtReg.width ((initSignedLayoutState x z k).zslot i)
          =
        (initWidthState x z k).zw i :=
      stInit_zslot_width x z i
    have hfit :
        FitsSignedWidth
          (ExtReg.width ((initSignedLayoutState x z k).zslot i) + 1)
          (ExtRegEncoding.extToInt ((initSignedLayoutState x z k).zslot i) b) :=
      extToInt_fits_width_succ
        (qs := qs)
        ((initSignedLayoutState x z k).zslot i)
        b
    simpa [hwidth] using hfit
  · simp [htop]
    have hwidth :
        ExtReg.width ((initSignedLayoutState x z k).zslot i)
          =
        (initWidthState x z k).zw i :=
      stInit_zslot_width x z i
    have hlt :
        ExtReg.toNat ((initSignedLayoutState x z k).zslot i) b
          <
        2 ^ ((initWidthState x z k).zw i) := by
      simpa [ExtReg.toNat, hwidth] using
        (ExtensionSemantics.extToNat_lt_width
          (qs := qs)
          (e := (initSignedLayoutState x z k).zslot i)
          (b := b))
    exact FitsSignedWidth_of_nonneg_lt_pow hlt

lemma widthStateSoundPlus_start_state
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (b : qs.Basis) :
  WidthStateSoundPlus
    (qs := qs)
    (initSignedLayoutState x z k)
    (initWidthState x z k)
    State.start_state
    b :=
  by
  constructor
  · intro i
    rw [evalRowX_start_state]
    simpa [WidthStateSoundPlus, initWidthState] using
      (sourceChunkXInt_init_fits
        (qs := qs) (x := x) (z := z) (i := i) (b := b))
  · intro i
    rw [evalRowZ_start_state]
    simpa [WidthStateSoundPlus, initWidthState] using
      (sourceChunkZInt_init_fits
        (qs := qs) (x := x) (z := z) (i := i) (b := b))

lemma evalRowX_shiftL_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (m : ℕ)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (r.shiftL m) b
    =
  ((2 : ℤ)^m) * evalRowX (qs := qs) src r b := by
  classical
  unfold evalRowX Register.shiftL
  calc
    (∑ j : Fin k, (r j * (2 : ℤ)^m) * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

lemma evalRowZ_shiftL_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (m : ℕ)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (r.shiftL m) b
    =
  ((2 : ℤ)^m) * evalRowZ (qs := qs) src r b := by
  classical
  unfold evalRowZ Register.shiftL
  calc
    (∑ j : Fin k, (r j * (2 : ℤ)^m) * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

lemma evalRowX_negate_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (Register.negate r) b
    =
  - evalRowX (qs := qs) src r b := by
  classical
  unfold evalRowX Register.negate
  calc
    (∑ j : Fin k, (-r j) * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, -(r j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = - ∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.sum_neg_distrib]

lemma evalRowZ_negate_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (Register.negate r) b
    =
  - evalRowZ (qs := qs) src r b := by
  classical
  unfold evalRowZ Register.negate
  calc
    (∑ j : Fin k, (-r j) * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, -(r j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = - ∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.sum_neg_distrib]

lemma evalRowX_shiftR_exact
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r r' : Register k)
  (m : ℕ)
  (b : qs.Basis)
  (hshift : Register.shiftR? r m = some r') :
  evalRowX (qs := qs) src r b
    =
  ((2 : ℤ)^m) * evalRowX (qs := qs) src r' b := by
  classical
  have hdiv := Register.shiftR?_some_divisible hshift
  have hval := Register.shiftR?_some_value hshift
  unfold evalRowX
  calc
    (∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, (((2 : ℤ)^m) * r' j) * sourceChunkXInt (qs := qs) src j b := by
        apply Finset.sum_congr rfl
        intro j hj
        have hdvd : ((2 : ℤ)^m) ∣ r j := Int.dvd_of_emod_eq_zero (hdiv j)
        have hrj : r j = ((2 : ℤ)^m) * r' j := by
          calc
            r j = ((2 : ℤ)^m) * (r j / ((2 : ℤ)^m)) := by
              symm
              exact Int.mul_ediv_cancel' hdvd
            _ = ((2 : ℤ)^m) * r' j := by
              rw [hval j]
        rw [hrj]
    _ =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r' j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r' j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

lemma evalRowZ_shiftR_exact
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r r' : Register k)
  (m : ℕ)
  (b : qs.Basis)
  (hshift : Register.shiftR? r m = some r') :
  evalRowZ (qs := qs) src r b
    =
  ((2 : ℤ)^m) * evalRowZ (qs := qs) src r' b := by
  classical
  have hdiv := Register.shiftR?_some_divisible hshift
  have hval := Register.shiftR?_some_value hshift
  unfold evalRowZ
  calc
    (∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, (((2 : ℤ)^m) * r' j) * sourceChunkZInt (qs := qs) src j b := by
        apply Finset.sum_congr rfl
        intro j hj
        have hdvd : ((2 : ℤ)^m) ∣ r j := Int.dvd_of_emod_eq_zero (hdiv j)
        have hrj : r j = ((2 : ℤ)^m) * r' j := by
          calc
            r j = ((2 : ℤ)^m) * (r j / ((2 : ℤ)^m)) := by
              symm
              exact Int.mul_ediv_cancel' hdvd
            _ = ((2 : ℤ)^m) * r' j := by
              rw [hval j]
        rw [hrj]
    _ =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r' j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r' j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

lemma evalRowX_addScaled_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (dstReg srcReg : Register k)
  (negSrc : Bool)
  (sh : ℕ)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (Register.addScaled dstReg srcReg negSrc sh) b
    =
  evalRowX (qs := qs) src dstReg b
    + (if negSrc then (-1 : ℤ) else 1)
        * ((2 : ℤ)^sh)
        * evalRowX (qs := qs) src srcReg b := by
  classical
  unfold evalRowX Register.addScaled
  calc
    (∑ j : Fin k,
        (dstReg j + (if negSrc then (-1 : ℤ) else 1) * srcReg j * (2 : ℤ) ^ sh)
          * sourceChunkXInt (qs := qs) src j b)
        =
    (∑ j : Fin k,
      (dstReg j * sourceChunkXInt (qs := qs) src j b
        +
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkXInt (qs := qs) src j b))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkXInt (qs := qs) src j b)
      +
    ∑ j : Fin k,
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkXInt (qs := qs) src j b) := by
          rw [Finset.sum_add_distrib]
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkXInt (qs := qs) src j b)
      +
    ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
      * ∑ j : Fin k, srcReg j * sourceChunkXInt (qs := qs) src j b := by
          rw [Finset.mul_sum]

lemma evalRowZ_addScaled_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (dstReg srcReg : Register k)
  (negSrc : Bool)
  (sh : ℕ)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (Register.addScaled dstReg srcReg negSrc sh) b
    =
  evalRowZ (qs := qs) src dstReg b
    + (if negSrc then (-1 : ℤ) else 1)
        * ((2 : ℤ)^sh)
        * evalRowZ (qs := qs) src srcReg b := by
  classical
  unfold evalRowZ Register.addScaled
  calc
    (∑ j : Fin k,
        (dstReg j + (if negSrc then (-1 : ℤ) else 1) * srcReg j * (2 : ℤ) ^ sh)
          * sourceChunkZInt (qs := qs) src j b)
        =
    (∑ j : Fin k,
      (dstReg j * sourceChunkZInt (qs := qs) src j b
        +
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkZInt (qs := qs) src j b))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkZInt (qs := qs) src j b)
      +
    ∑ j : Fin k,
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkZInt (qs := qs) src j b) := by
          rw [Finset.sum_add_distrib]
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkZInt (qs := qs) src j b)
      +
    ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
      * ∑ j : Fin k, srcReg j * sourceChunkZInt (qs := qs) src j b := by
          rw [Finset.mul_sum]

lemma widthStateSoundPlus_step
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (cur : WidthState k)
  (σ σ1 : State k)
  (op : valid_ops k)
  (b : qs.Basis)
  (hstep : applyOp? σ op = some σ1)
  (hfit : WidthStateSoundPlus (qs := qs) src cur σ b) :
  WidthStateSoundPlus
    (qs := qs) src (updateWidthState cur op) σ1 b := by
  rcases hfit with ⟨hx, hz⟩
  cases op with
  | shiftL i n =>
      have hσ1 : σ1 = State.shiftLReg σ i n := by
        simp [applyOp?] at  hstep
        simp[hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hji : i = j
        · subst hji
          have hrow :
              evalRowX (qs := qs) src ((σ i).shiftL n) b
                =
              ((2 : ℤ)^n) * evalRowX (qs := qs) src (σ i) b := by
            simpa using
              (evalRowX_shiftL_raw
                (qs := qs) (src := src) (r := σ i) (m := n) (b := b))
          have hnew :
              FitsSignedWidth (cur.xw i + n + 1)
                (((2 : ℤ)^n) * evalRowX (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_shiftL_raw (w := cur.xw i) (n := n) (hfit := hx i)
          simpa [updateWidthState, State.shiftLReg, State.setReg, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.shiftLReg, State.setReg, hji', Function.update]
            using hx j
      · intro j
        by_cases hji : i = j
        · subst hji
          have hrow :
              evalRowZ (qs := qs) src ((σ i).shiftL n) b
                =
              ((2 : ℤ)^n) * evalRowZ (qs := qs) src (σ i) b := by
            simpa using
              (evalRowZ_shiftL_raw
                (qs := qs) (src := src) (r := σ i) (m := n) (b := b))
          have hnew :
              FitsSignedWidth (cur.zw i + n + 1)
                (((2 : ℤ)^n) * evalRowZ (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_shiftL_raw (w := cur.zw i) (n := n) (hfit := hz i)
          simpa [updateWidthState, State.shiftLReg, State.setReg, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.shiftLReg, State.setReg, hji', Function.update]
            using hz j

  | shiftR i n =>
      cases hreg : Register.shiftR? (σ i) n with
      | none =>
          simp [applyOp?, State.shiftRReg?, hreg] at hstep
      | some r' =>
          have hσ1 : σ1 = State.setReg σ i r' := by
            have:σ.setReg i r' = σ1:=by simpa [applyOp?, State.shiftRReg?, hreg] using hstep
            rw[this]
          subst hσ1
          constructor
          · intro j
            by_cases hji : i = j
            · subst hji
              have hrow :
                  evalRowX (qs := qs) src (σ i) b
                    =
                  ((2 : ℤ)^n) * evalRowX (qs := qs) src r' b := by
                simpa using
                  (evalRowX_shiftR_exact
                    (qs := qs) (src := src) (r := σ i) (r' := r')
                    (m := n) (b := b) hreg)
              have hnew :
                  FitsSignedWidth (cur.xw i - n + 1)
                    (evalRowX (qs := qs) src r' b) := by
                exact FitsSignedWidth_shiftR_of_mul
                  (w := cur.xw i) (n := n)
                  (z := evalRowX (qs := qs) src (σ i) b)
                  (q := evalRowX (qs := qs) src r' b)
                  (hfit := hx i) hrow
              simpa [updateWidthState, State.setReg, Function.update]
                using hnew
            · have hji' : j ≠ i := by omega
              simpa [updateWidthState, State.setReg, hji', Function.update]
                using hx j
          · intro j
            by_cases hji : i = j
            · subst hji
              have hrow :
                  evalRowZ (qs := qs) src (σ i) b
                    =
                  ((2 : ℤ)^n) * evalRowZ (qs := qs) src r' b := by
                simpa using
                  (evalRowZ_shiftR_exact
                    (qs := qs) (src := src) (r := σ i) (r' := r')
                    (m := n) (b := b) hreg)
              have hnew :
                  FitsSignedWidth (cur.zw i - n + 1)
                    (evalRowZ (qs := qs) src r' b) := by
                exact FitsSignedWidth_shiftR_of_mul
                  (w := cur.zw i) (n := n)
                  (z := evalRowZ (qs := qs) src (σ i) b)
                  (q := evalRowZ (qs := qs) src r' b)
                  (hfit := hz i) hrow
              simpa [updateWidthState, State.setReg, Function.update]
                using hnew
            · have hji' : j ≠ i := by omega
              simpa [updateWidthState, State.setReg, hji', Function.update]
                using hz j

  | negate i =>
      have hσ1 : σ1 = State.negateReg σ i := by
        simp [applyOp?] at hstep
        simp[hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hji : i=j
        · subst hji
          have hrow :
              evalRowX (qs := qs) src (Register.negate (σ i)) b
                =
              - evalRowX (qs := qs) src (σ i) b := by
            simpa using
              (evalRowX_negate_raw
                (qs := qs) (src := src) (r := σ i) (b := b))
          have hnew :
              FitsSignedWidth (cur.xw i + 2)
                (- evalRowX (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_neg_widen (w := cur.xw i) (hfit := hx i)
          simpa [updateWidthState, State.negateReg, State.setReg, Function.update, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.negateReg, State.setReg, hji', Function.update]
            using hx j
      · intro j
        by_cases hji : i=j
        · subst hji
          have hrow :
              evalRowZ (qs := qs) src (Register.negate (σ i)) b
                =
              - evalRowZ (qs := qs) src (σ i) b := by
            simpa using
              (evalRowZ_negate_raw
                (qs := qs) (src := src) (r := σ i) (b := b))
          have hnew :
              FitsSignedWidth (cur.zw i + 2)
                (- evalRowZ (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_neg_widen (w := cur.zw i) (hfit := hz i)
          simpa [updateWidthState, State.negateReg, State.setReg, Function.update, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.negateReg, State.setReg, hji', Function.update]
            using hz j

  | addScaled dsti srci negSrc sh =>
      have hσ1 : σ1 = State.addScaledReg σ dsti srci negSrc sh := by
        simp [applyOp?] at hstep
        simp[hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hjd : dsti = j
        · subst hjd
          have hrow :
              evalRowX (qs := qs) src
                (Register.addScaled (σ dsti) (σ srci) negSrc sh) b
                  =
              evalRowX (qs := qs) src (σ dsti) b
                + (if negSrc then (-1 : ℤ) else 1)
                    * ((2 : ℤ)^sh)
                    * evalRowX (qs := qs) src (σ srci) b := by
            simpa using
              (evalRowX_addScaled_raw
                (qs := qs) (src := src)
                (dstReg := σ dsti) (srcReg := σ srci)
                (negSrc := negSrc) (sh := sh) (b := b))
          have hnew :
              FitsSignedWidth (max (cur.xw dsti) (cur.xw srci + sh) + 2)
                (evalRowX (qs := qs) src (σ dsti) b
                  + (if negSrc then (-1 : ℤ) else 1)
                      * ((2 : ℤ)^sh)
                      * evalRowX (qs := qs) src (σ srci) b) := by
            exact FitsSignedWidth_addScaled_widen
              (wd := cur.xw dsti) (ws := cur.xw srci) (sh := sh)
              (negSrc := negSrc) (hdst := hx dsti) (hsrc := hx srci)
          simp [updateWidthState, State.addScaledReg, State.setReg, Function.update, hrow] at *
          rw[add_comm,← add_assoc, add_comm];simp[hnew]
        · have hjd' : j ≠ dsti := by omega
          simpa [updateWidthState, State.addScaledReg, State.setReg, hjd', Function.update]
            using hx j
      · intro j
        by_cases hjd : dsti = j
        · subst hjd
          have hrow :
              evalRowZ (qs := qs) src
                (Register.addScaled (σ dsti) (σ srci) negSrc sh) b
                  =
              evalRowZ (qs := qs) src (σ dsti) b
                + (if negSrc then (-1 : ℤ) else 1)
                    * ((2 : ℤ)^sh)
                    * evalRowZ (qs := qs) src (σ srci) b := by
            simpa using
              (evalRowZ_addScaled_raw
                (qs := qs) (src := src)
                (dstReg := σ dsti) (srcReg := σ srci)
                (negSrc := negSrc) (sh := sh) (b := b))
          have hnew :
              FitsSignedWidth (max (cur.zw dsti) (cur.zw srci + sh) + 2)
                (evalRowZ (qs := qs) src (σ dsti) b
                  + (if negSrc then (-1 : ℤ) else 1)
                      * ((2 : ℤ)^sh)
                      * evalRowZ (qs := qs) src (σ srci) b) := by
            exact FitsSignedWidth_addScaled_widen
              (wd := cur.zw dsti) (ws := cur.zw srci) (sh := sh)
              (negSrc := negSrc) (hdst := hz dsti) (hsrc := hz srci)
          simp [updateWidthState, State.addScaledReg, State.setReg, Function.update, hrow] at *
          rw[add_comm,← add_assoc, add_comm];simp[hnew]
        · have hjd' : j ≠ dsti := by omega
          simpa [updateWidthState, State.addScaledReg, State.setReg, hjd', Function.update]
            using hz j

  | phaseProduct i =>
      have hσ1 : σ1 = σ := by
        simp [applyOp?] at hstep
        simp[hstep]
      subst hσ1
      simp [updateWidthState,WidthStateSoundPlus] at *
      simp_all

/-- Folded run preservation of the proof-only invariant. -/
lemma widthStateSoundPlus_run
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (cur : WidthState k)
  (σ σf : State k)
  (ops : Prog k)
  (b : qs.Basis)
  (hrun : run? ops σ = some σf)
  (hfit : WidthStateSoundPlus (qs := qs) src cur σ b) :
  WidthStateSoundPlus
    (qs := qs)
    src
    (ops.foldl updateWidthState cur)
    σf
    b := by
  induction ops generalizing cur σ σf with
  | nil =>
      simp
      simp at hrun;aesop
  | cons op ops ih =>
      cases hstep : applyOp? σ op with
      | none =>
          simp [run?, hstep] at hrun
      | some σ1 =>
          have hrunTail : run? ops σ1 = some σf := by
            simpa [run?, hstep] using hrun
          have hfit1 :
              WidthStateSoundPlus (qs := qs) src (updateWidthState cur op) σ1 b := by
            exact widthStateSoundPlus_step
              (qs := qs) (src := src) (cur := cur)
              (σ := σ) (σ1 := σ1) (op := op) (b := b)
              hstep hfit
          simpa [List.foldl] using
            ih (cur := updateWidthState cur op) (σ := σ1) (σf := σf) hrunTail hfit1

/-- Prefix-folded x-widths are bounded by the full scan result. -/
lemma prefix_foldl_updateWidthState_x_le_scanAux
  {k : ℕ} (i : Fin k) :
  ∀ (pre rest : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    cur.xw i ≤ mx.xneed i →
    (pre.foldl updateWidthState cur).xw i
      ≤
    (scanNeededWidthsAux cur mx (pre ++ rest)).xneed i
  | [], rest, cur, mx, hcur => by
      exact le_trans hcur (scanNeededWidthsAux_x_ge (i := i) rest cur mx)
  | op :: pre, rest, cur, mx, hcur => by
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      have hcur' : cur'.xw i ≤ mx'.xneed i := by
        simp [cur', mx', mergeNeededWidths, widthsOfState]
      simpa [scanNeededWidthsAux, cur', mx'] using
        prefix_foldl_updateWidthState_x_le_scanAux
          (i := i) pre rest cur' mx' hcur'

/-- Prefix-folded z-widths are bounded by the full scan result. -/
lemma prefix_foldl_updateWidthState_z_le_scanAux
  {k : ℕ} (i : Fin k) :
  ∀ (pre rest : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    cur.zw i ≤ mx.zneed i →
    (pre.foldl updateWidthState cur).zw i
      ≤
    (scanNeededWidthsAux cur mx (pre ++ rest)).zneed i
  | [], rest, cur, mx, hcur => by
      exact le_trans hcur (scanNeededWidthsAux_z_ge (i := i) rest cur mx)
  | op :: pre, rest, cur, mx, hcur => by
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      have hcur' : cur'.zw i ≤ mx'.zneed i := by
        simp [cur', mx', mergeNeededWidths, widthsOfState]
      simpa [scanNeededWidthsAux, cur', mx'] using
        prefix_foldl_updateWidthState_z_le_scanAux
          (i := i) pre rest cur' mx' hcur'

lemma prefix_foldl_updateWidthState_x_le_scanNeeded
  {k : ℕ}
  (x z : ExtReg) (ops pre rest : Prog k) (i : Fin k)
  (hops : ops = pre ++ rest) :
  (pre.foldl updateWidthState (initWidthState x z k)).xw i
    ≤
  (scanNeededWidths x z ops).xneed i := by
  rw [hops, scanNeededWidths_eq_aux]
  exact prefix_foldl_updateWidthState_x_le_scanAux
    (i := i)
    pre rest
    (initWidthState x z k)
    (widthsOfState (initWidthState x z k))
    (by simp [widthsOfState])

lemma prefix_foldl_updateWidthState_z_le_scanNeeded
  {k : ℕ}
  (x z : ExtReg) (ops pre rest : Prog k) (i : Fin k)
  (hops : ops = pre ++ rest) :
  (pre.foldl updateWidthState (initWidthState x z k)).zw i
    ≤
  (scanNeededWidths x z ops).zneed i := by
  rw [hops, scanNeededWidths_eq_aux]
  exact prefix_foldl_updateWidthState_z_le_scanAux
    (i := i)
    pre rest
    (initWidthState x z k)
    (widthsOfState (initWidthState x z k))
    (by simp [widthsOfState])
/-! =========================================================
    Helper stack for `allocated_widths_sound`
========================================================= -/

lemma commonNeededWidth_ge_xneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.xneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h :
      max (need.xneed i) (need.zneed i)
        ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j))
      (Finset.mem_univ i)
  have h' : need.xneed i ≤ _ := le_trans (le_max_left _ _) h
  omega

lemma commonNeededWidth_ge_zneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.zneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h :
      max (need.xneed i) (need.zneed i)
        ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j))
      (Finset.mem_univ i)
  have h' : need.zneed i ≤ _ := le_trans (le_max_right _ _) h
  omega


lemma stFinal_xslot_width
  {k : ℕ} (x z : ExtReg) (need : NeededWidths k) (i : Fin k)
  (h :
    regSize ((phaseLayoutOfReg x.base k (phaseLimbWidth x z k)).slot i)
      ≤ commonNeededWidth need) :
  ExtReg.width ((targetSignedLayoutState x z k need).xslot i)
    =
  commonNeededWidth need := by
  simp [targetSignedLayoutState, withLogicalWidth, ExtReg.width]
  omega

lemma stFinal_zslot_width
  {k : ℕ} (x z : ExtReg) (need : NeededWidths k) (i : Fin k)
  (h :
    regSize ((phaseLayoutOfReg z.base k (phaseLimbWidth x z k)).slot i)
      ≤ commonNeededWidth need) :
  ExtReg.width ((targetSignedLayoutState x z k need).zslot i)
    =
  commonNeededWidth need := by
  simp [targetSignedLayoutState, withLogicalWidth, ExtReg.width]
  omega

lemma targetSignedLayoutState_xslot_width_scan
  {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
  ExtReg.width ((targetSignedLayoutState x z k (scanNeededWidths x z ops)).xslot i)
    =
  commonNeededWidth (scanNeededWidths x z ops) := by
  apply stFinal_xslot_width
  have hslot :
      regSize ((phaseLayoutOfReg x.base k (phaseLimbWidth x z k)).slot i)
        ≤ (initWidthState x z k).xw i :=
    phaseSlot_size_le_initWidth_x x z i
  have hscan :
      (initWidthState x z k).xw i
        ≤ (scanNeededWidths x z ops).xneed i := by
    rw [scanNeededWidths_eq_aux]
    simpa [widthsOfState] using
      scanNeededWidthsAux_x_ge
        (i := i)
        ops
        (initWidthState x z k)
        (widthsOfState (initWidthState x z k))
  have hW :
      (scanNeededWidths x z ops).xneed i + 1
        ≤ commonNeededWidth (scanNeededWidths x z ops) :=
    commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i
  omega

lemma targetSignedLayoutState_zslot_width_scan
  {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
  ExtReg.width ((targetSignedLayoutState x z k (scanNeededWidths x z ops)).zslot i)
    =
  commonNeededWidth (scanNeededWidths x z ops) := by
  apply stFinal_zslot_width
  have hslot :
      regSize ((phaseLayoutOfReg z.base k (phaseLimbWidth x z k)).slot i)
        ≤ (initWidthState x z k).zw i :=
    phaseSlot_size_le_initWidth_z x z i
  have hscan :
      (initWidthState x z k).zw i
        ≤ (scanNeededWidths x z ops).zneed i := by
    rw [scanNeededWidths_eq_aux]
    simpa [widthsOfState] using
      scanNeededWidthsAux_z_ge
        (i := i)
        ops
        (initWidthState x z k)
        (widthsOfState (initWidthState x z k))
  have hW :
      (scanNeededWidths x z ops).zneed i + 1
        ≤ commonNeededWidth (scanNeededWidths x z ops) :=
    commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i
  omega

/-- Final theorem: any symbolic state reachable after a prefix of `ops`
    fits in the final allocated layout widths. -/
lemma allocated_widths_sound
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (ops : Prog k)
  (b : qs.Basis) :
  let src := initSignedLayoutState x z k
  let dst := targetSignedLayoutState x z k (scanNeededWidths x z ops)
  ∀ {σ : State k},
    (∃ pre rest,
      ops = pre ++ rest ∧
      run? pre State.start_state = some σ) →
    (∀ i : Fin k,
      FitsSignedWidth (ExtReg.width (dst.xslot i))
        (evalRowX (qs := qs) src (σ i) b)) ∧
    (∀ i : Fin k,
      FitsSignedWidth (ExtReg.width (dst.zslot i))
        (evalRowZ (qs := qs) src (σ i) b)) := by
  dsimp
  intro σ hprefix
  rcases hprefix with ⟨pre, rest, hops, hrun⟩

  let cur0 : WidthState k := initWidthState x z k
  let curPre : WidthState k := pre.foldl updateWidthState cur0

  have hstart :
      WidthStateSoundPlus
        (qs := qs)
        (initSignedLayoutState x z k)
        cur0
        State.start_state
        b := by
    simpa [cur0] using
      widthStateSoundPlus_start_state
        (qs := qs) (x := x) (z := z) (b := b)

  have hpre :
      WidthStateSoundPlus
        (qs := qs)
        (initSignedLayoutState x z k)
        curPre
        σ
        b := by
    simpa [cur0, curPre] using
      widthStateSoundPlus_run
        (qs := qs)
        (src := initSignedLayoutState x z k)
        (cur := cur0)
        (σ := State.start_state)
        (σf := σ)
        (ops := pre)
        (b := b)
        hrun
        hstart

  constructor
  · intro i
    have hfitPre :
        FitsSignedWidth (curPre.xw i + 1)
          (evalRowX (qs := qs) (initSignedLayoutState x z k) (σ i) b) :=
      hpre.1 i

    have hprele :
        curPre.xw i ≤ (scanNeededWidths x z ops).xneed i := by
      simpa [curPre, cur0] using
        prefix_foldl_updateWidthState_x_le_scanNeeded
          (x := x) (z := z)
          (ops := ops) (pre := pre) (rest := rest)
          (i := i) hops

    rw [targetSignedLayoutState_xslot_width_scan x z ops i]

    exact FitsSignedWidth_mono
      (by
        have hW :=
          commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i
        omega)
      hfitPre

  · intro i
    have hfitPre :
        FitsSignedWidth (curPre.zw i + 1)
          (evalRowZ (qs := qs) (initSignedLayoutState x z k) (σ i) b) :=
      hpre.2 i

    have hprele :
        curPre.zw i ≤ (scanNeededWidths x z ops).zneed i := by
      simpa [curPre, cur0] using
        prefix_foldl_updateWidthState_z_le_scanNeeded
          (x := x) (z := z)
          (ops := ops) (pre := pre) (rest := rest)
          (i := i) hops

    rw [targetSignedLayoutState_zslot_width_scan x z ops i]

    exact FitsSignedWidth_mono
      (by
        have hW :=
          commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i
        omega)
      hfitPre
