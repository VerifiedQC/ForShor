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

def scanNeededWidths {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
    NeededWidths k :=
  let init : WidthState k := initWidthState x z k
  let rec go (cur : WidthState k) (mx : NeededWidths k) :
      List (valid_ops k) → NeededWidths k
    | [] => mx
    | op :: rest =>
        let cur' := updateWidthState cur op
        let mx' := mergeNeededWidths mx (widthsOfState cur')
        go cur' mx' rest
  go init (widthsOfState init) ops

/-- Build an `ExtReg` over a physical slot with the requested logical width. -/
def withLogicalWidth (r : Reg) (w : ℕ) : ExtReg :=
  { base := r, extra := w - regSize r }

/-- Common target width so that all chunks are widened to the same size. -/
def commonNeededWidth {k : ℕ} (need : NeededWidths k) : ℕ :=
  Finset.univ.sup (fun i : Fin k => max (need.xneed i) (need.zneed i))

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

/-- Emit all chunk allocations before the signed arithmetic body. -/
def compileSignedAllocations (k : ℕ) (src dst : LayoutState k) : Gate :=
  (List.finRange k).foldr
    (fun i acc =>
      allocChunkGate i (src.xslot i) (dst.xslot i) ;;
      allocChunkGate i (src.zslot i) (dst.zslot i) ;;
      acc)
    Gate.id

/-- Emit all chunk deallocations after the signed arithmetic body. -/
def compileSignedDeallocations (k : ℕ) (src dst : LayoutState k) : Gate :=
  ((List.finRange k).reverse).foldr
    (fun i acc =>
      deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
      deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
      acc)
    Gate.id

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



/-- The mathematical Toom-Cook phase decomposition theorem. -/
lemma toom_cook_decomposition
  {qs : QSemantics} [RegEncoding qs.Basis]
  (k : ℕ) (hk : 1 < k) (x z : Reg) (b : qs.Basis)
  (pts : List Point) (hpts : pts.length = q k)
  (coeff : Fin (q k) → ℚ)
  (hcoeff : coeff = phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k)) :
  (∑ i : Fin pts.length, (coeff ⟨i.val, by rw [←hpts]; exact i.is_lt⟩ : ℝ) *
    pointEval x k (by omega) b (pts.get i) *
    pointEval z k (by omega) b (pts.get i))
  = (RegEncoding.toNat x b : ℝ) * (RegEncoding.toNat z b : ℝ) := by sorry

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
/-- Signed basis-state correctness for the recursive compiler with
    explicit allocation/deallocation of chunk widening. -/
lemma eval_compileOpsToSignedGate_correct_ket
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
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
  sorry

/-- Full-state correctness for the recursive signed compiler. -/
lemma eval_compileOpsToSignedGate_correct
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
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
      (run_ops_start_state := run_ops_start_state)
  exact gate_eq_of_ket_eq qs hket ψ
