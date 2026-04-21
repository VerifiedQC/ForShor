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

/-- Contiguous near-even splitting of a register into `k` chunks. -/
def layoutOfReg (r : Reg) (k : ℕ) : Layout k where
  slot := fun i =>
    let n := regSize r
    let s := chunkStart n k i
    let m := chunkSize n k i
    ⟨r.lo + s, r.lo + s + m⟩
  disjoint := by
    intro i j hij
    wlog hlt : i.1 < j.1 generalizing i j
    · have hji : j.1 < i.1 := by
        have hne : j.1 ≠ i.1 := by
          intro h
          apply hij
          apply Fin.ext
          rw [h]
        omega
      simp [Disjoint] at *
      have h_not_eq : j ≠ i := by omega
      have final_or := this j i h_not_eq hji
      omega
    left
    simp [chunkStart, chunkSize, regSize]
    have hmain :
      chunkStart (regSize r) k i + chunkSize (regSize r) k i
        ≤ chunkStart (regSize r) k j := by
      unfold chunkStart chunkSize regSize
      simp
      split_ifs
      have h_le : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hlt
      set N := r.hi - r.lo
      set Q := N / k
      set R := N % k
      by_cases hj : ↑j < R
      · have hi : i.val < R := by omega
        have h1 : (j.val).min R = ↑j := Nat.min_eq_left (Nat.le_of_lt hj)
        have : (i.val).min R = ↑i := Nat.min_eq_left (Nat.le_of_lt hi)
        rw [this, h1]
        have hQ : i.1 * Q + i.1 + (Q + 1) = (i.1 + 1) * (Q + 1) := by
          ring
        have hJ : j.1 * Q + j.1 = j.1 * (Q + 1) := by
          ring
        rw [hQ, hJ]
        gcongr
      · have hi : i.val < R := by omega
        have hi_min : (i.1).min R = i.1 := Nat.min_eq_left (Nat.le_of_lt hi)
        have hj_min : (j.1).min R = R := Nat.min_eq_right (Nat.le_of_not_gt hj)
        have h_le : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hlt
        rw [hi_min, hj_min]
        have hiR : i.1 + 1 ≤ R := Nat.succ_le_of_lt hi
        have hmul : Q * (i.1 + 1) ≤ Q * j.1 :=
          Nat.mul_le_mul_left Q h_le
        have hsum : Q * (i.1 + 1) + (i.1 + 1) ≤ Q * j.1 + R :=
          Nat.add_le_add hmul hiR
        have hrewriteL : i.1 * Q + i.1 + (Q + 1) = Q * (i.1 + 1) + (i.1 + 1) := by
          ring
        have hrewriteR : j.1 * Q + R = Q * j.1 + R := by
          ring
        rw [hrewriteL, hrewriteR]
        exact hsum
      · set N : ℕ := r.hi - r.lo
        set Q : ℕ := N / k
        set R : ℕ := N % k
        have hi : ¬ i.val < R := by omega
        have hi_ge : R ≤ i.1 := Nat.le_of_not_gt hi
        have hj_ge : R ≤ j.1 := le_trans hi_ge (Nat.le_of_lt hlt)
        have hi_min : (i.1).min R = R := Nat.min_eq_right hi_ge
        have hj_min : (j.1).min R = R := Nat.min_eq_right hj_ge
        have hle : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hlt
        rw [hi_min, hj_min]
        have hmul : (i.1 + 1) * Q ≤ j.1 * Q := Nat.mul_le_mul_right Q hle
        have hrewrite : i.1 * Q + R + (Q + 0) = (i.1 + 1) * Q + R := by
          ring
        rw [hrewrite]
        exact Nat.add_le_add_right hmul R
    have := Nat.add_le_add_left hmain r.lo
    simpa [chunkStart, chunkSize, regSize, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

/-- Each slot in a split layout has size at most the original register. -/
lemma slot_size_le (x : Reg) (k : ℕ) (hk : 1 ≤ k) (i : Fin k) :
  regSize ((layoutOfReg x k).slot i) ≤ regSize x := by
  dsimp [layoutOfReg]
  simp [regSize]
  generalize (x.hi - x.lo) = n
  unfold chunkSize
  have hk : 1 ≤ k := by omega
  have hdiv : n / k * k + n % k = n := by
    rw [mul_comm]
    exact Nat.div_add_mod n k
  have hmul : n / k ≤ n / k * k := by
    calc
      n / k = n / k * 1 := by rw [Nat.mul_one]
      _ ≤ n / k * k := Nat.mul_le_mul_left (n / k) hk
  simp
  split_ifs with h
  · have hrem : 1 ≤ n % k := by omega
    omega
  · omega

/-- If `k > 1` and the register is nontrivial, each slot is strictly smaller. -/
lemma slot_size_lt (x : Reg) {k : ℕ} (hk : 1 < k) (hx : 1 < regSize x) (i : Fin k) :
  regSize ((layoutOfReg x k).slot i) < regSize x := by
  dsimp [layoutOfReg] at *
  simp [regSize] at *
  generalize h_n : (x.hi - x.lo) = n at *
  unfold chunkSize
  have hdiv : n / k * k + n % k = n := by
    rw [mul_comm]
    exact Nat.div_add_mod n k
  simp
  split_ifs with h
  ·
    by_cases hq : n / k = 0
    · omega
    · have hq_pos : 1 ≤ n / k := by
        have hq_pos : 0 < n / k := Nat.pos_of_ne_zero hq
        omega
      have hmul : n / k * 2 ≤ n / k * k := Nat.mul_le_mul_left (n / k) hk
      omega
  ·
    by_cases hq : n / k = 0
    · omega
    · have hq_pos : 1 ≤ n / k := by
        have hq_pos : 0 < n / k := Nat.pos_of_ne_zero hq
        omega
      have hmul : n / k * 2 ≤ n / k * k := Nat.mul_le_mul_left (n / k) hk
      have hrem : 0 ≤ n % k := by omega
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

/-- Initial logical widths come from the current semantic widths of `x` and `z`,
    not just from the raw physical register sizes. -/
def initWidthState (x z : ExtReg) (k : ℕ) : WidthState k where
  xw := fun i => splitLogicalWidth (ExtReg.width x) k i
  zw := fun i => splitLogicalWidth (ExtReg.width z) k i

def updateWidthState {k : ℕ} (st : WidthState k) : valid_ops k → WidthState k
  | .shiftL i n =>
      { xw := Function.update st.xw i (st.xw i + n)
        zw := Function.update st.zw i (st.zw i + n) }
  | .shiftR i n =>
      { xw := Function.update st.xw i (st.xw i - n)
        zw := Function.update st.zw i (st.zw i - n) }
  | .negate _ =>
      st
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

/-- Pull the recursion in `scanNeededWidths` out to a top-level helper. -/
def scanNeededWidthsAux {k : ℕ} (cur : WidthState k) (mx : NeededWidths k) :
    List (valid_ops k) → NeededWidths k
  | [] => mx
  | op :: rest =>
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      scanNeededWidthsAux cur' mx' rest

def scanNeededWidths {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
    NeededWidths k :=
  scanNeededWidthsAux (initWidthState x z k) (widthsOfState (initWidthState x z k)) ops

/-- Build an `ExtReg` over a physical slot with the requested logical width. -/
def withLogicalWidth (r : Reg) (w : ℕ) : ExtReg :=
  { base := r, extra := w - regSize r }

/-- Common target width so that all chunks are widened to the same size. -/
def commonNeededWidth {k : ℕ} (need : NeededWidths k) : ℕ :=
  1 + Finset.univ.sup (fun i : Fin k => max (need.xneed i) (need.zneed i))

/-- Initial chunk views, reflecting the current semantic widths of `x` and `z`
    before any additional allocation performed by the compiler. -/
def initSignedLayoutState (x z : ExtReg) (k : ℕ) : LayoutState k :=
  { xslot := fun i =>
      let r := (layoutOfReg x.base k).slot i
      withLogicalWidth r (splitLogicalWidth (ExtReg.width x) k i)
    zslot := fun i =>
      let r := (layoutOfReg z.base k).slot i
      withLogicalWidth r (splitLogicalWidth (ExtReg.width z) k i) }

/-- Final widened chunk views used by the compiled signed body.
    Every chunk is widened to the same common width `W`. -/
def targetSignedLayoutState (x z : ExtReg) (k : ℕ) (need : NeededWidths k) : LayoutState k :=
  let W := commonNeededWidth need
  { xslot := fun i =>
      let r := (layoutOfReg x.base k).slot i
      withLogicalWidth r W
    zslot := fun i =>
      let r := (layoutOfReg z.base k).slot i
      withLogicalWidth r W }

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
def isTopChunk {k : ℕ} (i : Fin k) : Prop :=
  i.1 + 1 = k
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

/-- Mathematically exact polynomial evaluation of a register's chunks at a point.
    (No sorry here, purely constructive). -/
noncomputable def pointEval {qs : QSemantics} [RegEncoding qs.Basis]
  (r : Reg) (k : ℕ) (hk : 0 < k) (b : qs.Basis) (pt : Point) : ℝ :=
  match pt with
  | .int z => ∑ i : Fin k,
      (RegEncoding.toNat ((layoutOfReg r k).slot i) b : ℝ) * (z : ℝ) ^ (i.val)
  | .inf   =>
      RegEncoding.toNat ((layoutOfReg r k).slot ⟨k - 1, Nat.sub_lt hk (by decide)⟩) b



-- /-- The mathematical Toom-Cook phase decomposition theorem. -/
-- lemma toom_cook_decomposition
--   {qs : QSemantics} [RegEncoding qs.Basis]
--   (k : ℕ) (hk : 1 < k) (x z : Reg) (b : qs.Basis)
--   (pts : List Point) (hpts : pts.length = q k)
--   (coeff : Fin (q k) → ℚ)
--   (hcoeff : coeff = phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k)) :
--   (∑ i : Fin pts.length, (coeff ⟨i.val, by rw [←hpts]; exact i.is_lt⟩ : ℝ) *
--     pointEval x k (by omega) b (pts.get i) *
--     pointEval z k (by omega) b (pts.get i))
--   = (RegEncoding.toNat x b : ℝ) * (RegEncoding.toNat z b : ℝ) := by sorry

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

lemma scanNeededWidths_x_ge_init
  {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
  splitLogicalWidth (ExtReg.width x) k i ≤ (scanNeededWidths x z ops).xneed i := by
  rw [scanNeededWidths_eq_aux]
  simpa [initWidthState, widthsOfState] using
    (scanNeededWidthsAux_x_ge
      (i := i)
      ops
      (initWidthState x z k)
      (widthsOfState (initWidthState x z k)))

lemma scanNeededWidths_z_ge_init
  {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
  splitLogicalWidth (ExtReg.width z) k i ≤ (scanNeededWidths x z ops).zneed i := by
  rw [scanNeededWidths_eq_aux]
  simpa [initWidthState, widthsOfState] using
    (scanNeededWidthsAux_z_ge
      (i := i)
      ops
      (initWidthState x z k)
      (widthsOfState (initWidthState x z k)))
/-! =========================================================
    Helper lemmas for layout disjointness and width bounds
========================================================= -/

def WellFormedReg (r : Reg) : Prop :=
  r.lo ≤ r.hi


/-- Slots of a single layout are disjoint from each other. -/
lemma layout_slot_disjoint_slot {k : ℕ} (r : Reg) (i j : Fin k) (hij : i ≠ j) :
  Disjoint ((layoutOfReg r k).slot i) ((layoutOfReg r k).slot j) :=
  (layoutOfReg r k).disjoint i j hij

lemma chunkStart_add_chunkSize_le
  (n k : ℕ) (i : Fin (k + 1)) :
  chunkStart n (k + 1) i + chunkSize n (k + 1) i ≤ n := by
  unfold chunkStart chunkSize
  set q : ℕ := n / (k + 1)
  set r : ℕ := n % (k + 1)
  have hdiv : q * (k + 1) + r = n := by
    dsimp [q, r]
    have:=Nat.div_add_mod n (k + 1)
    rw[mul_comm,this]
  have hi : i.1 < k + 1 := i.is_lt
  by_cases hir : i.1 < r
  · have hmin : min i.1 r = i.1 := Nat.min_eq_left (Nat.le_of_lt hir)
    simp at *
    simp_all only [inf_of_le_left, ↓reduceIte, q, r]
    have h1 : i.1 + 1 ≤ r := Nat.succ_le_of_lt hir
    calc
      i.1 * q + i.1 + (q + 1)
          = (i.1 + 1) * q + (i.1 + 1) := by ring
      _ ≤ r * q + r := by
          gcongr
      _ ≤ q * (k + 1) + r := by
          have hrle : r ≤ k + 1 := Nat.le_of_lt_succ (by sorry)
          -- easier to use `omega` only here
          sorry
      _ = n := by sorry
  · have hmin : min i.1 r = r := Nat.min_eq_right (Nat.le_of_not_gt hir)
    sorry

lemma slot_subset_base {k : ℕ} (r : Reg) (i : Fin k) (hWF: WellFormedReg r):
  r.lo ≤ ((layoutOfReg r k).slot i).lo ∧
  ((layoutOfReg r k).slot i).hi ≤ r.hi := by
  cases k with
  | zero =>
      apply i.elim0
  | succ k =>
      dsimp [layoutOfReg]
      constructor
      · omega
      · have hmain :
            chunkStart (regSize r) (k + 1) i + chunkSize (regSize r) (k + 1) i ≤ regSize r := by
          simpa using chunkStart_add_chunkSize_le (regSize r) k i
        have:=Nat.add_le_add_left hmain r.lo
        simp[regSize] at *
        have hmain' :
            r.lo + (chunkStart (r.hi - r.lo) (k + 1) i + chunkSize (r.hi - r.lo) (k + 1) i)
              ≤ r.lo + (r.hi - r.lo) := by
          exact Nat.add_le_add_left hmain r.lo
        have htop : r.lo + (r.hi - r.lo) = r.hi := by
          simp[WellFormedReg] at hWF
          omega
        rw [htop] at hmain'
        simpa [Nat.add_assoc] using hmain'




/-- Slots of disjoint parent registers are disjoint. -/
lemma layout_slot_disjoint_of_base_disjoint {k : ℕ} (r s : Reg)
  (hrs : Disjoint r s) (i j : Fin k) (hWFr: WellFormedReg r) (hWFs: WellFormedReg s):
  Disjoint ((layoutOfReg r k).slot i) ((layoutOfReg s k).slot j) := by
  rcases slot_subset_base r i hWFr with ⟨hri_lo, hri_hi⟩
  rcases slot_subset_base s j hWFs with ⟨hsj_lo, hsj_hi⟩
  cases hrs with
  | inl h => exact Or.inl (le_trans hri_hi (le_trans h hsj_lo))
  | inr h => exact Or.inr (le_trans hsj_hi (le_trans h hri_lo))

/-- Common width is at least `1 + xneed i` for every `i`. -/
lemma commonNeededWidth_ge_xneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.xneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h : max (need.xneed i) (need.zneed i)
      ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j))
      (Finset.mem_univ i)
  have h' : need.xneed i ≤ _ := le_trans (le_max_left _ _) h
  omega

lemma commonNeededWidth_ge_zneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.zneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h : max (need.xneed i) (need.zneed i)
      ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j))
      (Finset.mem_univ i)
  have h' : need.zneed i ≤ _ := le_trans (le_max_right _ _) h
  omega

/-- The logical width stored in `stInit.xslot i` equals `need.xneed i`, provided
    `splitLogicalWidth ≥ regSize`. -/
lemma stInit_xslot_width {k : ℕ} (x z : ExtReg) (i : Fin k)
  (h : regSize ((layoutOfReg x.base k).slot i) ≤ splitLogicalWidth (ExtReg.width x) k i) :
  ExtReg.width ((initSignedLayoutState x z k).xslot i) = splitLogicalWidth (ExtReg.width x) k i := by
  simp [initSignedLayoutState, withLogicalWidth, ExtReg.width]
  set a:=regSize ((layoutOfReg z.base k).slot i)
  set b:=splitLogicalWidth (regSize z.base + z.extra) k i
  have := Nat.add_sub_cancel a b
  rw[← Nat.add_sub_assoc, Nat.add_comm,Nat.add_sub_cancel]
  unfold b ExtReg.width at *
  simp[h]

lemma stInit_zslot_width {k : ℕ} (x z : ExtReg) (i : Fin k)
  (h : regSize ((layoutOfReg z.base k).slot i) ≤ splitLogicalWidth (ExtReg.width z) k i) :
  ExtReg.width ((initSignedLayoutState x z k).zslot i) = splitLogicalWidth (ExtReg.width z) k i := by
  simp [initSignedLayoutState, withLogicalWidth, ExtReg.width]
  set a:=regSize ((layoutOfReg z.base k).slot i)
  set b:=splitLogicalWidth (regSize z.base + z.extra) k i
  have := Nat.add_sub_cancel a b
  rw[← Nat.add_sub_assoc, Nat.add_comm,Nat.add_sub_cancel]
  unfold b ExtReg.width at *
  simp[h]


/-- Same for `stFinal.xslot i` with width `W`. -/
lemma stFinal_xslot_width {k : ℕ} (x z : ExtReg) (need : NeededWidths k) (i : Fin k)
  (h : regSize ((layoutOfReg x.base k).slot i) ≤ commonNeededWidth need) :
  ExtReg.width ((targetSignedLayoutState x z k need).xslot i) = commonNeededWidth need := by
  simp [targetSignedLayoutState, withLogicalWidth, ExtReg.width]
  omega

lemma stFinal_zslot_width {k : ℕ} (x z : ExtReg) (need : NeededWidths k) (i : Fin k)
  (h : regSize ((layoutOfReg z.base k).slot i) ≤ commonNeededWidth need) :
  ExtReg.width ((targetSignedLayoutState x z k need).zslot i) = commonNeededWidth need := by
  simp [targetSignedLayoutState, withLogicalWidth, ExtReg.width]
  omega

lemma stFinal_xslot_eq_addExtra
  {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
  let stInit := initSignedLayoutState x z k
  let stFinal := targetSignedLayoutState x z k (scanNeededWidths x z ops)
  stFinal.xslot i = ExtReg.addExtra (stInit.xslot i)
      (extraDelta (stInit.xslot i) (stFinal.xslot i)) := by
  dsimp [initSignedLayoutState, targetSignedLayoutState, ExtReg.addExtra, extraDelta, withLogicalWidth]
  set r := (layoutOfReg x.base k).slot i
  set splitW := splitLogicalWidth (ExtReg.width x) k i
  set W := commonNeededWidth (scanNeededWidths x z ops)
  have hrs : regSize r ≤ splitW := by
    simpa [r, splitW] using slot_size_le_splitLogicalWidth_x x i
  have hscan : splitW ≤ (scanNeededWidths x z ops).xneed i := by
    simpa [splitW] using scanNeededWidths_x_ge_init x z ops i
  have hW : splitW ≤ W := by
    have := commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i
    omega
  congr
  omega

lemma stFinal_zslot_eq_addExtra
  {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
  let stInit := initSignedLayoutState x z k
  let stFinal := targetSignedLayoutState x z k (scanNeededWidths x z ops)
  stFinal.zslot i = ExtReg.addExtra (stInit.zslot i)
      (extraDelta (stInit.zslot i) (stFinal.zslot i)) := by
  dsimp [initSignedLayoutState, targetSignedLayoutState, ExtReg.addExtra, extraDelta, withLogicalWidth]
  set r := (layoutOfReg z.base k).slot i
  set splitW := splitLogicalWidth (ExtReg.width z) k i
  set W := commonNeededWidth (scanNeededWidths x z ops)
  have hrs : regSize r ≤ splitW := by
    simpa [r, splitW] using slot_size_le_splitLogicalWidth_z z i
  have hscan : splitW ≤ (scanNeededWidths x z ops).zneed i := by
    simpa [splitW] using scanNeededWidths_z_ge_init x z ops i
  have hW : splitW ≤ W := by
    have := commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i
    omega
  congr
  omega

lemma extraDelta_xslot_pos
  {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
  let stInit := initSignedLayoutState x z k
  let stFinal := targetSignedLayoutState x z k (scanNeededWidths x z ops)
  0 < extraDelta (stInit.xslot i) (stFinal.xslot i) := by
  dsimp [initSignedLayoutState, targetSignedLayoutState, extraDelta, withLogicalWidth]
  set r := (layoutOfReg x.base k).slot i
  set splitW := splitLogicalWidth (ExtReg.width x) k i
  set W := commonNeededWidth (scanNeededWidths x z ops)
  have hrs : regSize r ≤ splitW := by
    simpa [r, splitW] using slot_size_le_splitLogicalWidth_x x  i
  have hscan : splitW ≤ (scanNeededWidths x z ops).xneed i := by
    simpa [splitW] using scanNeededWidths_x_ge_init x z ops i
  have hW : splitW + 1 ≤ W := by
    have := commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i
    omega
  omega

lemma extraDelta_zslot_pos
  {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
  let stInit := initSignedLayoutState x z k
  let stFinal := targetSignedLayoutState x z k (scanNeededWidths x z ops)
  0 < extraDelta (stInit.zslot i) (stFinal.zslot i) := by
  dsimp [initSignedLayoutState, targetSignedLayoutState, extraDelta, withLogicalWidth]
  set r := (layoutOfReg z.base k).slot i
  set splitW := splitLogicalWidth (ExtReg.width z) k i
  set W := commonNeededWidth (scanNeededWidths x z ops)
  have hrs : regSize r ≤ splitW := by
    simpa [r, splitW] using slot_size_le_splitLogicalWidth_z z i
  have hscan : splitW ≤ (scanNeededWidths x z ops).zneed i := by
    simpa [splitW] using scanNeededWidths_z_ge_init x z ops i
  have hW : splitW + 1 ≤ W := by
    have := commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i
    omega
  omega

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


lemma eval_allocChunkGate_x_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (hxwf : WellFormedReg x.base)
  (hzwf : WellFormedReg z.base)
  (ops : Prog k)
  (i : Fin k)
  (bcur : qs.Basis) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState x z k
  let stFinal : LayoutState k := targetSignedLayoutState x z k need
  ∃ bX : qs.Basis,
    qs.eval (allocChunkGate i (stInit.xslot i) (stFinal.xslot i)) (qs.ket bcur) = qs.ket bX ∧
    ExtRegEncoding.extToInt (stFinal.xslot i) bX = sourceChunkXInt (qs := qs) stInit i bcur ∧
    (∀ j : Fin k, j ≠ i →
      ExtRegEncoding.extToInt (stFinal.xslot j) bX =
        ExtRegEncoding.extToInt (stFinal.xslot j) bcur) ∧
    (∀ j : Fin k,
      ExtRegEncoding.extToInt (stFinal.zslot j) bX =
        ExtRegEncoding.extToInt (stFinal.zslot j) bcur) ∧
    (∀ j : Fin k,
      sourceChunkXInt (qs := qs) stInit j bX =
        sourceChunkXInt (qs := qs) stInit j bcur) ∧
    (∀ j : Fin k,
      sourceChunkZInt (qs := qs) stInit j bX =
        sourceChunkZInt (qs := qs) stInit j bcur) := by
  dsimp
  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k := initSignedLayoutState x z k
  set stFinal : LayoutState k := targetSignedLayoutState x z k need
  set δ : ℕ := extraDelta (stInit.xslot i) (stFinal.xslot i)

  have hδpos : 0 < δ := by
    simpa [δ, need, stInit, stFinal] using
      (extraDelta_xslot_pos (x := x) (z := z) (ops := ops) (i := i))

  have hslot :
      stFinal.xslot i = ExtReg.addExtra (stInit.xslot i) δ := by
    simpa [δ, need, stInit, stFinal] using
      (stFinal_xslot_eq_addExtra (x := x) (z := z) (ops := ops) (i := i))

  have hδne : δ ≠ 0 := Nat.ne_of_gt hδpos

  have hdisj_xx_src (j : Fin k) (hji : j ≠ i) :
      Disjoint (stInit.xslot i).base (stInit.xslot j).base := by
    simpa [stInit, initSignedLayoutState, withLogicalWidth]
      using layout_slot_disjoint_slot x.base i j (Ne.symm hji)

  have hdisj_xx_tgt (j : Fin k) (hji : j ≠ i) :
      Disjoint (stInit.xslot i).base (stFinal.xslot j).base := by
    simpa [stInit, stFinal, initSignedLayoutState, targetSignedLayoutState, withLogicalWidth]
      using layout_slot_disjoint_slot x.base i j (Ne.symm hji)

  have hdisj_xz_src (j : Fin k) :
      Disjoint (stInit.xslot i).base (stInit.zslot j).base := by
    simpa [stInit, initSignedLayoutState, withLogicalWidth]
      using layout_slot_disjoint_of_base_disjoint x.base z.base hxz i j hxwf hzwf

  have hdisj_xz_tgt (j : Fin k) :
      Disjoint (stInit.xslot i).base (stFinal.zslot j).base := by
    simpa [stInit, stFinal, initSignedLayoutState, targetSignedLayoutState, withLogicalWidth]
      using layout_slot_disjoint_of_base_disjoint x.base z.base hxz i j hxwf hzwf

  by_cases htop : isTopChunk i
  ·
    have hgate :
        allocChunkGate i (stInit.xslot i) (stFinal.xslot i)
          = Gate.signExtend (stInit.xslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]

    rcases ExtensionSemantics.eval_signExtend_ket
        (qs := qs) (r := stInit.xslot i) (n := δ) (b := bcur) with
      ⟨bX, hEval0, hToNat, hWide, hLoc⟩

    have hEval :
        qs.eval (allocChunkGate i (stInit.xslot i) (stFinal.xslot i)) (qs.ket bcur)
          = qs.ket bX := by
      rw [hgate]
      exact hEval0

    refine ⟨bX, hEval, ?_, ?_, ?_, ?_, ?_⟩

    ·
      calc
        ExtRegEncoding.extToInt (stFinal.xslot i) bX
            = ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.xslot i) δ) bX := by
                rw [hslot]
        _ = ExtRegEncoding.extToInt (stInit.xslot i) bcur := hWide
        _ = sourceChunkXInt (qs := qs) stInit i bcur := by
              unfold sourceChunkXInt
              simp [htop]

    ·
      intro j hji
      exact signExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.xslot i) (e := stFinal.xslot j)
        (n := δ) (b := bcur) (b' := bX)
        (hdisj_xx_tgt j hji) hEval0

    ·
      intro j
      exact signExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.xslot i) (e := stFinal.zslot j)
        (n := δ) (b := bcur) (b' := bX)
        (hdisj_xz_tgt j) hEval0

    ·
      intro j
      unfold sourceChunkXInt
      by_cases hjtop : isTopChunk j
      · simp [hjtop]
        by_cases hji : j = i
        · subst hji
          unfold ExtRegEncoding.extToInt ExtReg.toNat
          have := congrArg (tcDecodeWidth (ExtReg.width (stInit.xslot j))) hToNat
          simpa [ExtReg.toNat] using this
        · exact signExtend_preserves_disjoint_extToInt
            (qs := qs)
            (r := stInit.xslot i) (e := stInit.xslot j)
            (n := δ) (b := bcur) (b' := bX)
            (hdisj_xx_src j hji) hEval0
      · simp [hjtop]
        by_cases hji : j = i
        · subst hji
          simpa using hToNat
        · exact hLoc (stInit.xslot j) (by have := hdisj_xx_src j hji;simp[Disjoint] at *;omega)

    ·
      intro j
      unfold sourceChunkZInt
      by_cases hjtop : isTopChunk j
      · simp [hjtop]
        exact signExtend_preserves_disjoint_extToInt
          (qs := qs)
          (r := stInit.xslot i) (e := stInit.zslot j)
          (n := δ) (b := bcur) (b' := bX)
          (hdisj_xz_src j) hEval0
      · simp [hjtop]
        exact hLoc (stInit.zslot j) (by have := hdisj_xz_src j;simp[Disjoint] at *;omega)

  ·
    have hgate :
        allocChunkGate i (stInit.xslot i) (stFinal.xslot i)
          = Gate.zeroExtend (stInit.xslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]

    rcases ExtensionSemantics.eval_zeroExtend_ket
        (qs := qs) (r := stInit.xslot i) (n := δ) (b := bcur) with
      ⟨bX, hEval0, hToNat, hWideNat, hLoc⟩

    have hEval :
        qs.eval (allocChunkGate i (stInit.xslot i) (stFinal.xslot i)) (qs.ket bcur)
          = qs.ket bX := by
      rw [hgate]
      exact hEval0

    have hWide :
        ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.xslot i) δ) bX
          = (ExtReg.toNat (stInit.xslot i) bcur : ℤ) := by
      exact zeroExtend_extToInt
        (qs := qs)
        (r := stInit.xslot i) (n := δ)
        (b := bcur) (b' := bX)
        hδpos hEval0

    refine ⟨bX, hEval, ?_, ?_, ?_, ?_, ?_⟩

    ·
      calc
        ExtRegEncoding.extToInt (stFinal.xslot i) bX
            = ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.xslot i) δ) bX := by
                rw [hslot]
        _ = (ExtReg.toNat (stInit.xslot i) bcur : ℤ) := hWide
        _ = sourceChunkXInt (qs := qs) stInit i bcur := by
              unfold sourceChunkXInt
              simp [htop]

    ·
      intro j hji
      exact zeroExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.xslot i) (e := stFinal.xslot j)
        (n := δ) (b := bcur) (b' := bX)
        (hdisj_xx_tgt j hji) hEval0

    ·
      intro j
      exact zeroExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.xslot i) (e := stFinal.zslot j)
        (n := δ) (b := bcur) (b' := bX)
        (hdisj_xz_tgt j) hEval0

    ·
      intro j
      unfold sourceChunkXInt
      by_cases hjtop : isTopChunk j
      · simp [hjtop]
        by_cases hji : j = i
        · subst hji
          exfalso
          exact htop hjtop
        · exact zeroExtend_preserves_disjoint_extToInt
            (qs := qs)
            (r := stInit.xslot i) (e := stInit.xslot j)
            (n := δ) (b := bcur) (b' := bX)
            (hdisj_xx_src j hji) hEval0
      · simp [hjtop]
        by_cases hji : j = i
        · subst hji
          simpa using hToNat
        · exact hLoc (stInit.xslot j) (by have := (hdisj_xx_src j hji);simp[Disjoint] at *;omega)

    ·
      intro j
      unfold sourceChunkZInt
      by_cases hjtop : isTopChunk j
      · simp [hjtop]
        exact zeroExtend_preserves_disjoint_extToInt
          (qs := qs)
          (r := stInit.xslot i) (e := stInit.zslot j)
          (n := δ) (b := bcur) (b' := bX)
          (hdisj_xz_src j) hEval0
      · simp [hjtop]
        exact hLoc (stInit.zslot j) (by have := (hdisj_xz_src j);simp[Disjoint] at *;omega)

lemma eval_allocChunkGate_z_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (hxwf : WellFormedReg x.base)
  (hzwf : WellFormedReg z.base)
  (ops : Prog k)
  (i : Fin k)
  (bcur : qs.Basis) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState x z k
  let stFinal : LayoutState k := targetSignedLayoutState x z k need
  ∃ bZ : qs.Basis,
    qs.eval (allocChunkGate i (stInit.zslot i) (stFinal.zslot i)) (qs.ket bcur) = qs.ket bZ ∧
    ExtRegEncoding.extToInt (stFinal.zslot i) bZ = sourceChunkZInt (qs := qs) stInit i bcur ∧
    (∀ j : Fin k,
      ExtRegEncoding.extToInt (stFinal.xslot j) bZ =
        ExtRegEncoding.extToInt (stFinal.xslot j) bcur) ∧
    (∀ j : Fin k, j ≠ i →
      ExtRegEncoding.extToInt (stFinal.zslot j) bZ =
        ExtRegEncoding.extToInt (stFinal.zslot j) bcur) ∧
    (∀ j : Fin k,
      sourceChunkXInt (qs := qs) stInit j bZ =
        sourceChunkXInt (qs := qs) stInit j bcur) ∧
    (∀ j : Fin k,
      sourceChunkZInt (qs := qs) stInit j bZ =
        sourceChunkZInt (qs := qs) stInit j bcur) := by
  dsimp
  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k := initSignedLayoutState x z k
  set stFinal : LayoutState k := targetSignedLayoutState x z k need
  set δ : ℕ := extraDelta (stInit.zslot i) (stFinal.zslot i)

  have hxz' : Disjoint z.base x.base := by
    cases hxz with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h

  have hδpos : 0 < δ := by
    simpa [δ, need, stInit, stFinal] using
      (extraDelta_zslot_pos (x := x) (z := z) (ops := ops) (i := i))

  have hslot :
      stFinal.zslot i = ExtReg.addExtra (stInit.zslot i) δ := by
    simpa [δ, need, stInit, stFinal] using
      (stFinal_zslot_eq_addExtra (x := x) (z := z) (ops := ops) (i := i))

  have hδne : δ ≠ 0 := Nat.ne_of_gt hδpos

  have hdisj_zx_src (j : Fin k) :
      Disjoint (stInit.zslot i).base (stInit.xslot j).base := by
    simpa [stInit, initSignedLayoutState, withLogicalWidth]
      using layout_slot_disjoint_of_base_disjoint z.base x.base hxz' i j hzwf hxwf

  have hdisj_zx_tgt (j : Fin k) :
      Disjoint (stInit.zslot i).base (stFinal.xslot j).base := by
    simpa [stInit, stFinal, initSignedLayoutState, targetSignedLayoutState, withLogicalWidth]
      using layout_slot_disjoint_of_base_disjoint z.base x.base hxz' i j hzwf hxwf

  have hdisj_xz_src_rev (j : Fin k) :
      Disjoint (stInit.xslot j).base (stInit.zslot i).base := by
    simpa [stInit, initSignedLayoutState, withLogicalWidth]
      using layout_slot_disjoint_of_base_disjoint x.base z.base hxz j i hxwf hzwf

  have hdisj_zz_src (j : Fin k) (hji : j ≠ i) :
      Disjoint (stInit.zslot i).base (stInit.zslot j).base := by
    simpa [stInit, initSignedLayoutState, withLogicalWidth]
      using layout_slot_disjoint_slot z.base i j (by omega)

  have hdisj_zz_src_rev (j : Fin k) (hji : j ≠ i) :
      Disjoint (stInit.zslot j).base (stInit.zslot i).base := by
    simpa [stInit, initSignedLayoutState, withLogicalWidth]
      using layout_slot_disjoint_slot z.base j i hji

  have hdisj_zz_tgt (j : Fin k) (hji : j ≠ i) :
      Disjoint (stInit.zslot i).base (stFinal.zslot j).base := by
    simpa [stInit, stFinal, initSignedLayoutState, targetSignedLayoutState, withLogicalWidth]
      using layout_slot_disjoint_slot z.base i j (by omega)

  by_cases htop : isTopChunk i
  ·
    have hgate :
        allocChunkGate i (stInit.zslot i) (stFinal.zslot i)
          = Gate.signExtend (stInit.zslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]

    rcases ExtensionSemantics.eval_signExtend_ket
        (qs := qs) (r := stInit.zslot i) (n := δ) (b := bcur) with
      ⟨bZ, hEval0, hToNat, hWide, hLoc⟩

    have hEval :
        qs.eval (allocChunkGate i (stInit.zslot i) (stFinal.zslot i)) (qs.ket bcur)
          = qs.ket bZ := by
      rw [hgate]
      exact hEval0

    refine ⟨bZ, hEval, ?_, ?_, ?_, ?_, ?_⟩

    ·
      calc
        ExtRegEncoding.extToInt (stFinal.zslot i) bZ
            = ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.zslot i) δ) bZ := by
                rw [hslot]
        _ = ExtRegEncoding.extToInt (stInit.zslot i) bcur := hWide
        _ = sourceChunkZInt (qs := qs) stInit i bcur := by
              unfold sourceChunkZInt
              simp [htop]

    ·
      intro j
      exact signExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.zslot i) (e := stFinal.xslot j)
        (n := δ) (b := bcur) (b' := bZ)
        (hdisj_zx_tgt j) hEval0

    ·
      intro j hji
      exact signExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.zslot i) (e := stFinal.zslot j)
        (n := δ) (b := bcur) (b' := bZ)
        (hdisj_zz_tgt j hji) hEval0

    ·
      intro j
      unfold sourceChunkXInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        exact signExtend_preserves_disjoint_extToInt
          (qs := qs)
          (r := stInit.zslot i) (e := stInit.xslot j)
          (n := δ) (b := bcur) (b' := bZ)
          (hdisj_zx_src j) hEval0
      ·
        simp [hjtop]
        exact hLoc (stInit.xslot j) (hdisj_xz_src_rev j)

    ·
      intro j
      unfold sourceChunkZInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        by_cases hji : j = i
        · subst hji
          have := congrArg (tcDecodeWidth (ExtReg.width (stInit.zslot j))) hToNat
          simpa [ExtReg.toNat] using this
        · exact signExtend_preserves_disjoint_extToInt
            (qs := qs)
            (r := stInit.zslot i) (e := stInit.zslot j)
            (n := δ) (b := bcur) (b' := bZ)
            (hdisj_zz_src j hji) hEval0
      ·
        simp [hjtop]
        by_cases hji : j = i
        · subst hji
          exfalso
          exact hjtop htop
        · exact hLoc (stInit.zslot j) (hdisj_zz_src_rev j hji)

  ·
    have hgate :
        allocChunkGate i (stInit.zslot i) (stFinal.zslot i)
          = Gate.zeroExtend (stInit.zslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]

    rcases ExtensionSemantics.eval_zeroExtend_ket
        (qs := qs) (r := stInit.zslot i) (n := δ) (b := bcur) with
      ⟨bZ, hEval0, hToNat, hWideNat, hLoc⟩

    have hEval :
        qs.eval (allocChunkGate i (stInit.zslot i) (stFinal.zslot i)) (qs.ket bcur)
          = qs.ket bZ := by
      rw [hgate]
      exact hEval0

    have hWide :
        ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.zslot i) δ) bZ
          = (ExtReg.toNat (stInit.zslot i) bcur : ℤ) := by
      exact zeroExtend_extToInt
        (qs := qs)
        (r := stInit.zslot i) (n := δ)
        (b := bcur) (b' := bZ)
        hδpos hEval0

    refine ⟨bZ, hEval, ?_, ?_, ?_, ?_, ?_⟩

    ·
      calc
        ExtRegEncoding.extToInt (stFinal.zslot i) bZ
            = ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.zslot i) δ) bZ := by
                rw [hslot]
        _ = (ExtReg.toNat (stInit.zslot i) bcur : ℤ) := hWide
        _ = sourceChunkZInt (qs := qs) stInit i bcur := by
              unfold sourceChunkZInt
              simp [htop]

    ·
      intro j
      exact zeroExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.zslot i) (e := stFinal.xslot j)
        (n := δ) (b := bcur) (b' := bZ)
        (hdisj_zx_tgt j) hEval0

    ·
      intro j hji
      exact zeroExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.zslot i) (e := stFinal.zslot j)
        (n := δ) (b := bcur) (b' := bZ)
        (hdisj_zz_tgt j hji) hEval0

    ·
      intro j
      unfold sourceChunkXInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        exact zeroExtend_preserves_disjoint_extToInt
          (qs := qs)
          (r := stInit.zslot i) (e := stInit.xslot j)
          (n := δ) (b := bcur) (b' := bZ)
          (hdisj_zx_src j) hEval0
      ·
        simp [hjtop]
        exact hLoc (stInit.xslot j) (hdisj_xz_src_rev j)

    ·
      intro j
      unfold sourceChunkZInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        by_cases hji : j = i
        · subst hji
          exfalso
          exact htop hjtop
        · exact zeroExtend_preserves_disjoint_extToInt
            (qs := qs)
            (r := stInit.zslot i) (e := stInit.zslot j)
            (n := δ) (b := bcur) (b' := bZ)
            (hdisj_zz_src j hji) hEval0
      ·
        simp [hjtop]
        by_cases hji : j = i
        · subst hji
          simpa using hToNat
        · exact hLoc (stInit.zslot j) (hdisj_zz_src_rev j hji)


lemma eval_compileSignedAllocationsAux_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (hxwf : WellFormedReg x.base)
  (hzwf : WellFormedReg z.base)
  (ops : Prog k)
  (b : qs.Basis) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState x z k
  let stFinal : LayoutState k := targetSignedLayoutState x z k need
  ∀ (n : ℕ) (hn : n ≤ k),
    ∃ bAlloc : qs.Basis,
      qs.eval (compileSignedAllocationsAux stInit stFinal n hn) (qs.ket b) = qs.ket bAlloc ∧
      (∀ i : Fin k, i.1 < n →
        ExtRegEncoding.extToInt (stFinal.xslot i) bAlloc =
          evalRowX (qs := qs) stInit (State.start_state i) b) ∧
      (∀ i : Fin k, i.1 < n →
        ExtRegEncoding.extToInt (stFinal.zslot i) bAlloc =
          evalRowZ (qs := qs) stInit (State.start_state i) b) ∧
      (∀ i : Fin k, n ≤ i.1 →
        sourceChunkXInt (qs := qs) stInit i bAlloc =
          sourceChunkXInt (qs := qs) stInit i b) ∧
      (∀ i : Fin k, n ≤ i.1 →
        sourceChunkZInt (qs := qs) stInit i bAlloc =
          sourceChunkZInt (qs := qs) stInit i b) := by
  dsimp
  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k := initSignedLayoutState x z k
  set stFinal : LayoutState k := targetSignedLayoutState x z k need
  intro n hn
  induction n generalizing b with
  | zero =>
      refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
      · simp [compileSignedAllocationsAux_zero, QSemantics.eval_id]
      · intro i hi
        omega
      · intro i hi
        omega
      · intro i hi
        rfl
      · intro i hi
        rfl
  | succ n ih =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let idx : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩

      rcases ih b hk' with
        ⟨bMid, hMidEval, hMidX, hMidZ, hKeepX, hKeepZ⟩

      rcases
        (eval_allocChunkGate_x_ket
          (qs := qs)
          (x := x) (z := z)
          (hxz := hxz) (hxwf := hxwf) (hzwf := hzwf)
          (ops := ops)
          (i := idx)
          (bcur := bMid))
        with ⟨bX, hXEval, hXVal, hXKeepX, hXKeepZTarget, hXKeepSrcX, hXKeepSrcZ⟩

      rcases
        (eval_allocChunkGate_z_ket
          (qs := qs)
          (x := x) (z := z)
          (hxz := hxz) (hxwf := hxwf) (hzwf := hzwf)
          (ops := ops)
          (i := idx)
          (bcur := bX))
        with ⟨bAlloc, hZEval, hZVal, hZKeepX, hZKeepZ, hZKeepSrcX, hZKeepSrcZ⟩

      refine ⟨bAlloc, ?_, ?_, ?_, ?_, ?_⟩
      · rw [compileSignedAllocationsAux_succ (src := stInit) (dst := stFinal) (n := n) (hn := hn)]
        rw [QSemantics.eval_seq]
        rw [hMidEval]
        rw [QSemantics.eval_seq]
        rw [hXEval]
        simpa [QSemantics.eval_seq, hk', idx] using hZEval
      · intro j hj
        by_cases hji : j = idx
        · subst hji
          calc
            ExtRegEncoding.extToInt (stFinal.xslot idx) bAlloc
                = ExtRegEncoding.extToInt (stFinal.xslot idx) bX := by
                    simpa using hZKeepX idx
            _ = sourceChunkXInt (qs := qs) stInit idx bMid := hXVal
            _ = sourceChunkXInt (qs := qs) stInit idx b := by
                  exact hKeepX idx (by change n ≤ n;exact Nat.le_refl n)
            _ = evalRowX (qs := qs) stInit (State.start_state idx) b := by
                  symm
                  simpa using evalRowX_start_state (qs := qs) stInit idx b
        · have hjn : j.1 < n := by
            have hjne : j.1 ≠ n := by
              intro hEq
              apply hji
              apply Fin.ext
              simpa [idx] using hEq
            omega
          calc
            ExtRegEncoding.extToInt (stFinal.xslot j) bAlloc
                = ExtRegEncoding.extToInt (stFinal.xslot j) bX := by
                    simpa using hZKeepX j
            _ = ExtRegEncoding.extToInt (stFinal.xslot j) bMid := by
                  exact hXKeepX j hji
            _ = evalRowX (qs := qs) stInit (State.start_state j) b := hMidX j hjn
      · intro j hj
        by_cases hji : j = idx
        · subst hji
          calc
            ExtRegEncoding.extToInt (stFinal.zslot idx) bAlloc
                = sourceChunkZInt (qs := qs) stInit idx bX := hZVal
            _ = sourceChunkZInt (qs := qs) stInit idx bMid := by
                  simpa using hXKeepSrcZ idx
            _ = sourceChunkZInt (qs := qs) stInit idx b := by
                  exact hKeepZ idx (by change n ≤ n;exact Nat.le_refl n)
            _ = evalRowZ (qs := qs) stInit (State.start_state idx) b := by
                  symm
                  simpa using evalRowZ_start_state (qs := qs) stInit idx b
        · have hjn : j.1 < n := by
            have hjne : j.1 ≠ n := by
              intro hEq
              apply hji
              apply Fin.ext
              simpa [idx] using hEq
            omega
          calc
            ExtRegEncoding.extToInt (stFinal.zslot j) bAlloc
                = ExtRegEncoding.extToInt (stFinal.zslot j) bX := by
                    exact hZKeepZ j hji
            _ = ExtRegEncoding.extToInt (stFinal.zslot j) bMid := by
                  simpa using hXKeepZTarget j
            _ = evalRowZ (qs := qs) stInit (State.start_state j) b := hMidZ j hjn
      · intro j hj
        calc
          sourceChunkXInt (qs := qs) stInit j bAlloc
              = sourceChunkXInt (qs := qs) stInit j bX := by
                  simpa using hZKeepSrcX j
          _ = sourceChunkXInt (qs := qs) stInit j bMid := by
                simpa using hXKeepSrcX j
          _ = sourceChunkXInt (qs := qs) stInit j b := hKeepX j (by omega)
      · intro j hj
        calc
          sourceChunkZInt (qs := qs) stInit j bAlloc
              = sourceChunkZInt (qs := qs) stInit j bX := by
                  simpa using hZKeepSrcZ j
          _ = sourceChunkZInt (qs := qs) stInit j bMid := by
                simpa using hXKeepSrcZ j
          _ = sourceChunkZInt (qs := qs) stInit j b := hKeepZ j (by omega)

/-- Top-level allocation correctness theorem. -/
lemma eval_compileSignedAllocations_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (hxwf : WellFormedReg x.base)
  (hzwf : WellFormedReg z.base)
  (ops : Prog k)
  (b : qs.Basis) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState x z k
  let stFinal : LayoutState k := targetSignedLayoutState x z k need
  ∃ bAlloc : qs.Basis,
    qs.eval (compileSignedAllocations k stInit stFinal) (qs.ket b) = qs.ket bAlloc ∧
    EncodesStateFrom (qs := qs) stInit stFinal State.start_state b bAlloc := by
  dsimp [compileSignedAllocations]
  rcases
    (eval_compileSignedAllocationsAux_ket
      (qs := qs)
      (x := x) (z := z)
      (hxz := hxz) (hxwf := hxwf) (hzwf := hzwf)
      (ops := ops) (b := b)
      k le_rfl)
    with ⟨bAlloc, hEval, hX, hZ, _hKeepX, _hKeepZ⟩
  refine ⟨bAlloc, hEval, ?_⟩
  constructor
  · intro i
    exact hX i i.is_lt
  · intro i
    exact hZ i i.is_lt

lemma eval_compileAnnotatedOpsToSignedGateAux_of_blocks
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (pts : List Point)
  (hpts : pts.length = q k)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (b0 bMid : qs.Basis)
  (ops : Prog k)
  (hEnc : EncodesStateFrom (qs := qs) src dst State.start_state b0 bMid)
  (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
        (annotatePhaseTermsAux k 0 ops))
      (qs.ket bMid)
    =
  phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) •
    qs.ket bMid := by
  sorry


lemma eval_compileSignedDeallocations_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (b bAlloc : qs.Basis)
  (hAlloc :
    qs.eval (compileSignedAllocations k src dst) (qs.ket b) = qs.ket bAlloc) :
  qs.eval (compileSignedDeallocations k src dst) (qs.ket bAlloc) = qs.ket b := by
  sorry


lemma eval_compileOpsToSignedGate_correct_ket_of_blocks
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (hxwf : WellFormedReg x.base)
  (hzwf : WellFormedReg z.base)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (b : qs.Basis)
  (ops : Prog k)
  (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state)
  :
  let W : ℕ := commonNeededWidth (scanNeededWidths x z ops)
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k W pts hpts
  qs.eval
      (compileOpsToSignedGate k hk phi x z coeff ops)
      (qs.ket b)
    =
  qs.eval
      (Gate.SignedPhaseProd phi x z)
      (qs.ket b) := by
  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k := initSignedLayoutState x z k
  set stFinal : LayoutState k := targetSignedLayoutState x z k need
  set W : ℕ := commonNeededWidth need
  set coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k W pts hpts

  simp [compileOpsToSignedGate, need, W]

  have hAlloc :=
    eval_compileSignedAllocations_ket
      (qs := qs)
      (x := x) (z := z)
      (hxz := hxz)
      (ops := ops) (b := b) (hxwf) hzwf

  rcases hAlloc with ⟨bAlloc, hAlloc1, hAlloc2⟩

  have hMid :=
    eval_compileAnnotatedOpsToSignedGateAux_of_blocks
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (pts := pts) (hpts := hpts)
      (coeff := coeff)
      (src := stInit) (dst := stFinal)
      (b0 := b) (bMid := bAlloc)
      (ops := ops)
      (hEnc := hAlloc2)
      (hB := hB)
      (run_ops_start_state := run_ops_start_state)

  have hDealloc :=
    eval_compileSignedDeallocations_ket
      (qs := qs)
      (src := stInit) (dst := stFinal)
      (b := b) (bAlloc := bAlloc)
      hAlloc1

  rw [hAlloc1, hMid, qs.eval_smul, hDealloc]
  rw [PhaseSemantics.eval_SignedPhaseProd_ket]

  sorry


/-- Signed basis-state correctness for the recursive compiler with
    explicit allocation/deallocation of chunk widening. -/
lemma eval_compileOpsToSignedGate_correct_ket
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (hxwf : WellFormedReg x.base)
  (hzwf : WellFormedReg z.base)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (b : qs.Basis)
  (ops : Prog k)
  (hC : ProgConsumesPts (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state)
  :
  let W : ℕ := commonNeededWidth (scanNeededWidths x z ops)
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k W pts hpts
  qs.eval
      (compileOpsToSignedGate k hk phi x z coeff ops)
      (qs.ket b)
    =
  qs.eval
      (Gate.SignedPhaseProd phi x z)
      (qs.ket b) := by
  have hB :
      BlockDecomposition (k := k) (by omega) State.start_state ops pts :=
    progConsumesPts_has_blockDecomposition
      (k := k) (by omega) ops State.start_state pts hC
  simpa using
    (eval_compileOpsToSignedGate_correct_ket_of_blocks
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (x := x) (z := z)
      (pts := pts) (hpts := hpts)
      (b := b)
      (ops := ops)
      (hB := hB)
      (run_ops_start_state := run_ops_start_state)
      (hxz:=hxz) hxwf hzwf
      )


/-- Full-state correctness for the recursive signed compiler. -/
lemma eval_compileOpsToSignedGate_correct
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (hxwf : WellFormedReg x.base)
  (hzwf : WellFormedReg z.base)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (ψ : qs.State)
  (ops : Prog k)
  (hC : ProgConsumesPts (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state)
  :
  let W : ℕ := commonNeededWidth (scanNeededWidths x z ops)
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k W pts hpts
  qs.eval
      (compileOpsToSignedGate k hk phi x z coeff ops)
      ψ
    =
  qs.eval
      (Gate.SignedPhaseProd phi x z)
      ψ := by
  have hket :=
    eval_compileOpsToSignedGate_correct_ket
      (qs := qs) (k := k) (hk := hk)
      (phi := phi) (x := x) (z := z)
      (pts := pts) (hpts := hpts)
      (ops := ops) (hC := hC)
      (run_ops_start_state := run_ops_start_state) (hxz) hxwf hzwf
  exact gate_eq_of_ket_eq qs hket ψ
