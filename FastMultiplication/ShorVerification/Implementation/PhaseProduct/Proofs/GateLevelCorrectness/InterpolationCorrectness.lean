import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateLevelCorrectness.SupportLemmas

-- Proof-only lemmas relocated from PhaseProduct/DefsCore (definition layer keeps only defs).

namespace Shor
open Gate
open Operations
open scoped BigOperators

lemma splitChunk_toNat_lt
    {Basis : Type u}
    [RegEncoding Basis]
    {parent : ExtReg}
    {k W : ℕ}
    (layout : PhaseSplitLayout parent k W)
    (i : Fin k)
    (b : Basis) :
    ExtReg.toNat (layout.child i) b
      <
    2 ^
      (if isTopChunk i then
        parent.width - i.1 * W
      else
        W) := by
  have h :=
    ExtReg.toNat_lt (layout.child i) b
  rw [layout.child_width i] at h
  simpa [phaseSplitLogicalWidth] using h


/-- A sequence of `n` base-`2^W` digits represents a number below
    `2^(n*W)`. -/
lemma fin_sum_digits_lt_pow
    (W : ℕ) :
    ∀ {n : ℕ}
      (digits : Fin n → ℕ),
      (∀ i, digits i < 2 ^ W) →
      (∑ i : Fin n,
          digits i * 2 ^ (i.1 * W))
        <
      2 ^ (n * W)
  | 0, digits, hdigits => by
      simp
  | n + 1, digits, hdigits => by
      have hlow :
          (∑ i : Fin n,
              digits i.castSucc *
                2 ^ (i.1 * W))
            <
          2 ^ (n * W) := by
        apply fin_sum_digits_lt_pow W
        intro i
        exact hdigits i.castSucc
      have hlast :
          digits (Fin.last n) < 2 ^ W :=
        hdigits (Fin.last n)
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      calc
        (∑ i : Fin n,
            digits i.castSucc *
              2 ^ (i.1 * W))
            +
          digits (Fin.last n) *
            2 ^ (n * W)
            <
          2 ^ (n * W) +
            digits (Fin.last n) *
              2 ^ (n * W) :=
          Nat.add_lt_add_right hlow _
        _ =
          (digits (Fin.last n) + 1) *
            2 ^ (n * W) := by
          ring
        _ ≤
          2 ^ W * 2 ^ (n * W) := by
          exact Nat.mul_le_mul_right
            (2 ^ (n * W))
            (Nat.succ_le_of_lt hlast)
        _ =
          2 ^ ((n + 1) * W) := by
          rw [Nat.add_mul, pow_add]
          simp [Nat.mul_comm]


/-- Concatenating an unsigned low block with a signed high block and then
    decoding gives the low block plus the shifted signed high block. -/
lemma tcDecodeWidth_concat
    {lowWidth highWidth low high : ℕ}
    (hHighWidth : 0 < highWidth)
    (hLow : low < 2 ^ lowWidth)
    (hHigh : high < 2 ^ highWidth) :
    tcDecodeWidth
        (lowWidth + highWidth)
        (low + high * 2 ^ lowWidth)
      =
    (low : ℤ) +
      tcDecodeWidth highWidth high *
        (2 : ℤ) ^ lowWidth := by
  obtain ⟨h, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hHighWidth)
  by_cases hsign : high < 2 ^ h
  · have hcombined :
        low + high * 2 ^ lowWidth
          <
        2 ^ (lowWidth + h) := by
      calc
        low + high * 2 ^ lowWidth
            <
        2 ^ lowWidth +
          high * 2 ^ lowWidth :=
          Nat.add_lt_add_right hLow _
        _ =
        (high + 1) * 2 ^ lowWidth := by
          ring
        _ ≤
        2 ^ h * 2 ^ lowWidth := by
          exact Nat.mul_le_mul_right
            (2 ^ lowWidth)
            (Nat.succ_le_of_lt hsign)
        _ =
        2 ^ (lowWidth + h) := by
          rw [pow_add]
          ring
    rw [show lowWidth + (h + 1) = (lowWidth + h) + 1 by omega]
    simp only [tcDecodeWidth]
    simp [hcombined, hsign]
  · have hhighLower : 2 ^ h ≤ high :=
      Nat.le_of_not_gt hsign
    have hcombined :
        ¬ low + high * 2 ^ lowWidth
            <
          2 ^ (lowWidth + h) := by
      apply Nat.not_lt_of_ge
      calc
        2 ^ (lowWidth + h)
            =
        2 ^ h * 2 ^ lowWidth := by
          rw [pow_add]
          ring
        _ ≤
        high * 2 ^ lowWidth :=
          Nat.mul_le_mul_right
            (2 ^ lowWidth)
            hhighLower
        _ ≤
        low + high * 2 ^ lowWidth :=
          Nat.le_add_left _ _
    rw [show lowWidth + (h + 1) = (lowWidth + h) + 1 by omega]
    simp only [tcDecodeWidth]
    simp [hsign, pow_add]
    rw[pow_add] at hcombined
    simp[hcombined]
    ring


/-- Binary positional decomposition for the concrete `take`/`drop` split. -/
lemma toNat_take_drop
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (m : ℕ)
    (hm : m ≤ regSize r)
    (b : Basis) :
    RegEncoding.toNat r b
      =
    RegEncoding.toNat (r.take m) b
      +
    2 ^ m * RegEncoding.toNat (r.drop m) b := by
  let sp : SplitPoint r := ⟨m, hm⟩
  have h :=
    RegEncoding.toNat_split
      (r := r)
      (m := sp)
      (b := b)
  unfold SplitPoint at *
  have hmin :
      min m r.qubits.length = m := by
    rw [Nat.min_eq_left]
    simpa [regSize, Reg.width] using hm
  simpa [sp, splitLeft, splitRight, ASize, regSize, Reg.width, Reg.take, hmin] using h


/-- Taking a block after first restricting to a prefix gives the same block,
    provided the complete block lies inside that prefix. -/
lemma take_drop_take_eq
    (r : Reg)
    (pre start width : ℕ)
    (hfit : start + width ≤ pre) :
    ((r.take pre).drop start).take width
      =
    (r.drop start).take width := by
  cases r with
  | mk qubits nodup =>
      have hw :
          width ≤ pre - start :=
        by omega
      simp [Reg.take, Reg.drop, List.drop_take, List.take_take, Nat.min_eq_left hw]


/-- Reconstruction of an `n·W`-bit register from `n` consecutive
    width-`W` blocks. -/
lemma toNat_uniform_chunks
    {Basis : Type u}
    [RegEncoding Basis]
    (W : ℕ) :
    ∀ (n : ℕ)
      (r : Reg)
      (b : Basis),
      regSize r = n * W →
      RegEncoding.toNat r b
        =
      ∑ i : Fin n,
        RegEncoding.toNat
          ((r.drop (i.1 * W)).take W)
          b *
        2 ^ (i.1 * W)
  | 0, r, b, hwidth => by
      have hlt :
          RegEncoding.toNat r b < ASize r :=
        RegEncoding.toNat_lt_ASize r b
      have hr0 : regSize r = 0 := by
        simpa using hwidth
      have hnat : RegEncoding.toNat r b = 0 := by
        unfold ASize at hlt
        rw [hr0] at hlt
        simp at hlt
        omega
      simp [hnat]
  | n + 1, r, b, hwidth => by
      have hWle : W ≤ regSize r := by
        rw [hwidth, Nat.add_mul]
        simp
      have hsplit :
          RegEncoding.toNat r b
            =
          RegEncoding.toNat (r.take W) b
            +
          2 ^ W *
            RegEncoding.toNat (r.drop W) b :=
        toNat_take_drop r W hWle b
      have htailWidth :
          regSize (r.drop W) = n * W := by
        have hwidth' :
            r.qubits.length = (n + 1) * W := by
          simpa [regSize, Reg.width] using hwidth
        have hdrop :
            r.qubits.length - W = n * W := by
          rw [hwidth']
          rw [Nat.succ_mul]
          simp [Nat.add_comm]
        simpa [regSize, Reg.width, Reg.drop] using hdrop
      have htail :
          RegEncoding.toNat (r.drop W) b
            =
          ∑ i : Fin n,
            RegEncoding.toNat
              (((r.drop W).drop (i.1 * W)).take W)
              b *
            2 ^ (i.1 * W) :=
        toNat_uniform_chunks W n (r.drop W) b htailWidth
      have hzero :
          (r.drop (0 * W)).take W = r.take W := by
        cases r
        simp [Reg.drop, Reg.take]
      have hsucc :
          ∀ i : Fin n,
            (r.drop ((i.succ : Fin (n + 1)).1 * W)).take W
              =
            ((r.drop W).drop (i.1 * W)).take W := by
        intro i
        cases r
        simp [Reg.drop, Reg.take, List.drop_drop, Nat.add_mul, Nat.add_comm]
      rw [hsplit, htail]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, zero_mul, pow_zero, Nat.mul_one]
      rw [show (r.drop 0).take W = r.take W by simpa using hzero]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hsucc i]
      have hexp :
          ((i.succ : Fin (n + 1)).1 * W)
            =
          W + i.1 * W := by
        simp [Nat.add_mul, Nat.add_comm]
      rw [hexp, pow_add]
      ring


/-- A non-top phase chunk is the corresponding width-`W` block of the
    `(k-1)·W`-bit lower prefix. -/
lemma phaseChunkActive_castSucc
    (parent : ExtReg)
    (n W : ℕ)
    (i : Fin n)
    (_hcut : n * W ≤ parent.width) :
    phaseChunkActive
        parent (n + 1) W
        (i.castSucc : Fin (n + 1))
      =
    (((parent.active.take (n * W)).drop
        (i.1 * W)).take W) := by
  have hnotTop :
      ¬ isTopChunk
        (i.castSucc : Fin (n + 1)) := by
    unfold isTopChunk
    simp only [Fin.val_castSucc]
    omega
  have hi : i.1 + 1 ≤ n :=
    Nat.succ_le_of_lt i.2
  have hfit :
      i.1 * W + W ≤ n * W := by
    calc
      i.1 * W + W = (i.1 + 1) * W := by
        rw [Nat.add_mul]
        simp
      _ ≤ n * W :=
        Nat.mul_le_mul_right W hi
  unfold phaseChunkActive phaseChunkStart
  rw [phaseSplitLogicalWidth]
  simp only [hnotTop, if_false]
  exact
    (take_drop_take_eq
      parent.active
      (n * W)
      (i.1 * W)
      W
      hfit).symm


/-- The final phase chunk is exactly the suffix following the lower
    `(k-1)` width-`W` blocks. -/
lemma phaseChunkActive_last
    (parent : ExtReg)
    (n W : ℕ)
    (hcut : n * W ≤ parent.width) :
    phaseChunkActive
        parent (n + 1) W
        (Fin.last n)
      =
    parent.active.drop (n * W) := by
  have htop :
      isTopChunk
        (Fin.last n : Fin (n + 1)) := by
    unfold isTopChunk
    simp
  cases parent with
  | mk active reserve hdisj =>
      cases active with
      | mk qubits nodup =>
          simp [phaseChunkActive, phaseChunkStart, phaseSplitLogicalWidth, htop, ExtReg.width, regSize, Reg.width, Reg.take, Reg.drop]


/-- Reconstruct the unsigned parent value from all child chunk values. -/
theorem phaseChunks_reconstruct_nat
    {Basis : Type u}
    [RegEncoding Basis]
    {parent : ExtReg}
    {k W : ℕ}
    (layout : PhaseSplitLayout parent k W)
    (b : Basis) :
    ExtReg.toNat parent b
      =
    ∑ i : Fin k,
      ExtReg.toNat (layout.child i) b *
        2 ^ (i.1 * W) := by
  obtain ⟨hk, hbound, htopValid⟩ :=
    layout.valid
  cases k with
  | zero =>
      omega
  | succ n =>
      simp only [Nat.succ_sub_one] at hbound
      let cut : ℕ := n * W
      let lower : Reg := parent.active.take cut
      let upper : Reg := parent.active.drop cut
      have hcut :
          cut ≤ parent.width := by
        simpa [cut] using hbound
      have hlowerWidth :
          regSize lower = n * W := by
        dsimp [lower, cut]
        simp [regSize, Reg.width, Reg.take]
        unfold cut ExtReg.width regSize Reg.width at *
        apply hcut
      have hsplit :
          ExtReg.toNat parent b
            =
          RegEncoding.toNat lower b
            +
          2 ^ cut *
            RegEncoding.toNat upper b := by
        unfold ExtReg.toNat
        simpa [lower, upper, cut] using
          toNat_take_drop
            parent.active
            cut
            hcut
            b
      have hlower :
          RegEncoding.toNat lower b
            =
          ∑ i : Fin n,
            RegEncoding.toNat
              ((lower.drop (i.1 * W)).take W)
              b *
            2 ^ (i.1 * W) :=
        toNat_uniform_chunks
          W n lower b hlowerWidth
      have hlowerChild :
          ∀ i : Fin n,
            ExtReg.toNat
                (layout.child
                  (i.castSucc : Fin (n + 1)))
                b
              =
            RegEncoding.toNat
              ((lower.drop (i.1 * W)).take W)
              b := by
        intro i
        unfold ExtReg.toNat
        change
          RegEncoding.toNat
              (phaseChunkActive
                parent (n + 1) W
                (i.castSucc : Fin (n + 1))) b
            =
          RegEncoding.toNat ((lower.drop (i.1 * W)).take W) b
        rw [ phaseChunkActive_castSucc parent n W i hcut ]
      have hupperChild :
          ExtReg.toNat
              (layout.child
                (Fin.last n : Fin (n + 1)))
              b
            =
          RegEncoding.toNat upper b := by
        unfold ExtReg.toNat
        change
          RegEncoding.toNat
              (phaseChunkActive
                parent (n + 1) W
                (Fin.last n))
              b
            =
          RegEncoding.toNat upper b
        rw [phaseChunkActive_last parent n W hcut]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [hsplit, hlower]
      have hlowerSum :
          (∑ i : Fin n,
              RegEncoding.toNat
                ((lower.drop (i.1 * W)).take W)
                b *
              2 ^ (i.1 * W))
            =
          ∑ i : Fin n,
              ExtReg.toNat
                (layout.child
                  (i.castSucc : Fin (n + 1)))
                b *
              2 ^ (i.1 * W) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hlowerChild i]
      rw [hlowerSum, hupperChild]
      dsimp [cut]
      ring


/-- Decode a chunk sum where the final chunk is interpreted as signed two's-complement. -/
theorem tcDecode_chunks_signed_top
    {k W total raw : ℕ}
    (hk : 0 < k)
    (hbound : (k - 1) * W ≤ total)
    (htop : total = 0 ∨ (k - 1) * W < total)
    (hraw : raw < 2 ^ total)
    (chunks : Fin k → ℕ)
    (hchunks :
      ∀ i : Fin k,
        chunks i <
          2 ^
            (if isTopChunk i then
              total - i.1 * W
            else
              W))
    (hchunk :
      raw =
        ∑ i : Fin k,
          chunks i * 2 ^ (i.1 * W)) :
    tcDecodeWidth total raw
      =
    ∑ i : Fin k,
      (if isTopChunk i then
          tcDecodeWidth
            (total - i.1 * W)
            (chunks i)
        else
          (chunks i : ℤ)) *
        (2 : ℤ) ^ (i.1 * W) := by
  cases k with
  | zero =>
      omega
  | succ n =>
      simp only [Nat.succ_sub_one] at hbound htop
      by_cases htotal : total = 0
      · subst total
        have hrawZero : raw = 0 := by
          simpa using hraw
        have hchunksZero :
            ∀ i : Fin (n + 1), chunks i = 0 := by
          intro i
          have htermLe :
              chunks i * 2 ^ (i.1 * W)
                ≤
              ∑ j : Fin (n + 1),
                chunks j * 2 ^ (j.1 * W) := by
            aesop
          rw [← hchunk, hrawZero] at htermLe
          have hpowPos :
              0 < 2 ^ (i.1 * W) := by
            positivity
          aesop
        subst raw
        simp [tcDecodeWidth, hchunksZero]
      · have htotalPos : 0 < total :=
          Nat.pos_of_ne_zero htotal
        have htopStrict : n * W < total :=
          htop.resolve_left htotal
        let lowWidth : ℕ := n * W
        let highWidth : ℕ := total - lowWidth
        let low : ℕ :=
          ∑ i : Fin n,
            chunks i.castSucc *
              2 ^ (i.1 * W)
        let high : ℕ :=
          chunks (Fin.last n)
        have hwidthEq :
            lowWidth + highWidth = total := by
          dsimp [lowWidth, highWidth]
          exact Nat.add_sub_of_le hbound
        have hHighWidthPos :
            0 < highWidth := by
          dsimp [highWidth, lowWidth]
          exact Nat.sub_pos_of_lt htopStrict
        have hnotTop :
            ∀ i : Fin n,
              ¬ isTopChunk
                (i.castSucc : Fin (n + 1)) := by
          intro i
          unfold isTopChunk
          simp only [Fin.val_castSucc]
          omega
        have htopLast :
            isTopChunk
              (Fin.last n : Fin (n + 1)) := by
          unfold isTopChunk
          simp
        have hlowerDigit :
            ∀ i : Fin n,
              chunks i.castSucc < 2 ^ W := by
          intro i
          have hi := hchunks i.castSucc
          simpa [hnotTop i] using hi
        have hLow :
            low < 2 ^ lowWidth := by
          dsimp [low, lowWidth]
          exact fin_sum_digits_lt_pow
            W
            (fun i : Fin n =>
              chunks i.castSucc)
            hlowerDigit
        have hHigh :
            high < 2 ^ highWidth := by
          have hi := hchunks
            (Fin.last n : Fin (n + 1))
          simpa [high, highWidth, lowWidth, htopLast] using hi
        have hdecomp :
            raw =
              low +
                high * 2 ^ lowWidth := by
          rw [hchunk, Fin.sum_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last]
          rfl
        have hdecode :
            tcDecodeWidth total raw
              =
            (low : ℤ) +
              tcDecodeWidth highWidth high *
                (2 : ℤ) ^ lowWidth := by
          calc
            tcDecodeWidth total raw
                =
            tcDecodeWidth
              (lowWidth + highWidth)
              (low + high * 2 ^ lowWidth) := by
                rw [hwidthEq, hdecomp]
            _ =
            (low : ℤ) +
              tcDecodeWidth highWidth high *
                (2 : ℤ) ^ lowWidth :=
              tcDecodeWidth_concat
                hHighWidthPos hLow hHigh
        have hLowCast :
            (low : ℤ)
              =
            ∑ i : Fin n,
              (chunks i.castSucc : ℤ) *
                (2 : ℤ) ^ (i.1 * W) := by
          dsimp [low]
          push_cast
          rfl
        rw [hdecode, Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        simp_rw [if_neg (hnotTop _)]
        rw [if_pos htopLast]
        rw [← hLowCast]


theorem splitChunkInt_reconstruct
    {Basis : Type u}
    [RegEncoding Basis]
    {parent : ExtReg}
    {k W : ℕ}
    (layout : PhaseSplitLayout parent k W)
    (b : Basis) :
    extToInt parent b
      =
    ∑ i : Fin k,
      splitChunkInt layout i b *
        ((2 : ℤ) ^ (i.1 * W)) := by
  obtain ⟨hk, hbound, htop⟩ := layout.valid
  have hraw :
      ExtReg.toNat parent b < 2 ^ parent.width :=
    ExtReg.toNat_lt parent b
  have hreconstruct :
      ExtReg.toNat parent b
        =
      ∑ i : Fin k,
        ExtReg.toNat (layout.child i) b *
          2 ^ (i.1 * W) :=
    phaseChunks_reconstruct_nat layout b
  unfold extToInt
  simpa [splitChunkInt] using
    tcDecode_chunks_signed_top
    (k := k)
    (W := W)
    (total := parent.width)
    (raw := ExtReg.toNat parent b)
    (chunks := fun i =>
      ExtReg.toNat (layout.child i) b)
    hk hbound htop hraw
    (fun i => splitChunk_toNat_lt layout i b)
    hreconstruct


end Shor


namespace Shor
open Gate
open Operations
open scoped BigOperators

/-!
# Phase-Product Interpolation Correctness
This file proves the algebraic identity behind phase-product compilation. The
accumulated phase over the Toom-Cook interpolation points is converted into a
polynomial interpolation sum, evaluated at the limb radix, and shown to equal the
signed product phase on the original extended registers.
-/

/-! =========================================================
    Section 1: Rational point terms and product coefficients
    These definitions translate source-row values into the rational data used by
    Toom-Cook interpolation: point terms, the final product target, and grouped
    product-polynomial coefficients.
========================================================= -/

/-- Rational version of the integer point phase term used by `phaseScalarFrom`. -/
def tcPointTerm
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (st : LayoutState k)
  (b : qs.Basis)
  (pts : List Point)
  (hpts : pts.length = q k) :
  Fin (q k) → ℚ :=
  fun i =>
    ((evalRowX (qs := qs) st
        (expectedRow (k := k) ((ToomCookMath.listToFin pts hpts) i)) b
      *
      evalRowZ (qs := qs) st
        (expectedRow (k := k) ((ToomCookMath.listToFin pts hpts) i)) b : ℤ) : ℚ)

/-- The final target product, as a rational number. -/
def tcTarget
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  (x z : ExtReg)
  (b : qs.Basis) : ℚ :=
  (((extToInt x b) *
    (extToInt z b) : ℤ) : ℚ)

/-- Coefficients of the product polynomial, grouped by total chunk degree. -/
def tcProductCoeff
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (st : LayoutState k)
  (b : qs.Basis) :
  Fin (q k) → ℚ :=
  fun l =>
    ∑ ij : Fin k × Fin k,
      if _h : ij.1.1 + ij.2.1 = l.1 then
        ((sourceChunkXInt (qs := qs) st ij.1 b *
          sourceChunkZInt (qs := qs) st ij.2 b : ℤ) : ℚ)
      else
        0

/-- The compiler's phase coefficients are exactly the generic interpolation coefficients. -/
lemma phaseCoeffFromPtsWidth_eq_interpCoeff
  {k W : ℕ}
  (pts : List Point)
  (hpts : pts.length = q k) :
  phaseCoeffFromPtsWidth k W pts hpts
    =
  ToomCookMath.interpCoeff
    (row := interpEntry k)
    (pts := ToomCookMath.listToFin pts hpts)
    ((2 : ℚ) ^ W) := by
  funext i
  simp [phaseCoeffFromPtsWidth, phaseCoeffFromPts, ToomCookMath.interpCoeff]
  unfold ToomCookMath.interpMatrix ToomCookMath.radixRow interpMatrix radixRow ptsToFin ToomCookMath.listToFin
  simp

/-! =========================================================
    Section 2: Phase scalar and point-evaluation bridge
    The lemmas here connect the compiler's phase accumulator to the generic
    Toom-Cook point-evaluation.
========================================================= -/

/-- Tail-indexed bridge from the compiler scalar recursion to the generic list scalar recursion. -/
lemma phaseScalarFrom_eq_phaseScalarFromList_aux
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (b : qs.Basis)
  (full : List Point)
  (hfull : full.length = q k) :
  ∀ (rest : List Point) (n : ℕ)
    (hn : n + rest.length = q k),
    full.drop n = rest →
    phaseScalarFrom (qs := qs) k phi coeff st b rest n hn
      =
    ToomCookMath.phaseScalarFromList
      phi coeff (tcPointTerm qs st b full hfull) rest n hn := by
  intro rest
  induction rest with
  | nil =>
      intro n hn hdrop
      simp [phaseScalarFrom, ToomCookMath.phaseScalarFromList]
  | cons pt rest ih =>
      intro n hn hdrop
      have hnlt : n < full.length := by rw [hfull]; simp at hn; omega
      have hget :
          (ToomCookMath.listToFin full hfull)
            ⟨n, by simpa [hfull] using hnlt⟩ = pt := by
        unfold ToomCookMath.listToFin
        simp_all
        have hget? : full[n]? = some pt := by
          have h0 := congrArg (fun xs : List Point => xs[0]?) hdrop
          simpa [List.getElem?_drop, Nat.zero_add] using h0
        have hget?₂ : some full[n] = some pt := by
          simpa [List.getElem?_eq_getElem hnlt] using hget?
        exact Option.some.inj hget?₂
      have htail_drop :
          full.drop (n + 1) = rest := by
        have := congrArg List.tail hdrop
        have hdrop_tail : ∀ (xs : List Point) (m : ℕ), (List.drop m xs).tail = List.drop (m + 1) xs := by simp
        rw [← hdrop_tail full n]
        simpa using this
      simp [phaseScalarFrom, ToomCookMath.phaseScalarFromList]
      have hterm :
          tcPointTerm qs st b full hfull
            ⟨n, by
              rw [← hn]
              simp
            ⟩
          =
          ((evalRowX (qs := qs) st (expectedRow (k := k) pt) b *
            evalRowZ (qs := qs) st (expectedRow (k := k) pt) b : ℤ) : ℚ) := by
        unfold tcPointTerm
        simp [hget]
      rw [hterm]
      have htail :
          phaseScalarFrom (qs := qs) k phi coeff st b rest (n + 1) (by simp at hn; omega) =
          ToomCookMath.phaseScalarFromList phi coeff (tcPointTerm qs st b full hfull) rest (n + 1) (by simp at hn; omega) := by
        exact ih (n + 1) (by simp at hn; omega) htail_drop
      rw [htail]
      unfold ToomCookMath.phaseFactor
      have hprodC : (((evalRowX (qs := qs) st (expectedRow (k := k) pt) b * evalRowZ (qs := qs) st (expectedRow (k := k) pt) b : ℤ) : ℚ) : ℂ) =
          ((evalRowX (qs := qs) st (expectedRow (k := k) pt) b : ℂ) * (evalRowZ (qs := qs) st (expectedRow (k := k) pt) b : ℂ)) := by norm_num
      rw [hprodC]
      simp[mul_comm]

/-- The full compiler scalar agrees with the generic list scalar over the same point list. -/
lemma phaseScalarFrom_eq_phaseScalarFromList
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (b : qs.Basis)
  (pts : List Point)
  (hpts : pts.length = q k) :
  phaseScalarFrom (qs := qs) k phi coeff st b pts 0 (by simpa using hpts)
    =
  ToomCookMath.phaseScalarFromList phi coeff (tcPointTerm qs st b pts hpts) pts 0
    (by simpa using hpts) := by
  simpa using
    phaseScalarFrom_eq_phaseScalarFromList_aux
      (qs := qs)
      (phi := phi)
      (coeff := coeff)
      (st := st)
      (b := b)
      (full := pts)
      (hfull := hpts)
      (rest := pts)
      (n := 0)
      (hn := by simpa using hpts)
      (by simp)
/-- Multiplying two expected-row entries gives the interpolation row entry at their total degree. -/
lemma expectedRow_mul_expectedRow_eq_interpEntry
  {k : ℕ}
  (hk : 1 < k)
  (pt : Point)
  (i j : Fin k) :
  (((expectedRow (k := k) pt i) *
    (expectedRow (k := k) pt j) : ℤ) : ℚ)
    =
  interpEntry k pt
    ⟨i.1 + j.1, by
      simp [q]
      omega
    ⟩ := by
  cases pt with
  | int z =>
      simp [expectedRow, interpEntry]
      norm_cast
      rw [pow_add]
  | frac c =>
      change
        (((c ^ (k - 1 - i.1) * c ^ (k - 1 - j.1) : ℤ) : ℚ)
          =
        (c : ℚ) ^ (q k - 1 - (i.1 + j.1)))
      norm_cast
      rw [← pow_add]
      congr 1
      simp [q]
      omega

/-- Reindex a double sum by total degree, collapsing the indicator-weighted outer sum. -/
lemma sum_degree_group
  {k : ℕ}
  (hk : 1 < k)
  (A : Fin k × Fin k → ℚ)
  (row : Fin (q k) → ℚ) :
  (∑ l : Fin (q k),
      (∑ ij : Fin k × Fin k,
        if _h : ij.1.1 + ij.2.1 = l.1 then
          A ij
        else
          0) * row l)
    =
  ∑ ij : Fin k × Fin k,
    A ij * row
      ⟨ij.1.1 + ij.2.1, by simp [q]; omega⟩ := by
  classical
  calc
    (∑ l : Fin (q k),
        (∑ ij : Fin k × Fin k,
          if _h : ij.1.1 + ij.2.1 = l.1 then
            A ij
          else
            0) * row l)
        =
      ∑ l : Fin (q k),
        ∑ ij : Fin k × Fin k,
          (if _h : ij.1.1 + ij.2.1 = l.1 then
            A ij
          else
            0) * row l := by
          simp [Finset.sum_mul]
    _ =
      ∑ ij : Fin k × Fin k,
        ∑ l : Fin (q k),
          (if _h : ij.1.1 + ij.2.1 = l.1 then
            A ij
          else
            0) * row l := by
          rw [Finset.sum_comm]
    _ =
      ∑ ij : Fin k × Fin k,
        A ij * row
          ⟨ij.1.1 + ij.2.1, by
            simp [q]
            omega
          ⟩ := by
          apply Finset.sum_congr rfl
          intro ij hij
          let d : Fin (q k) := ⟨ij.1.1 + ij.2.1, by simp [q]; omega⟩
          have hsingle :
              (∑ l : Fin (q k),
                (if _h : ij.1.1 + ij.2.1 = l.1 then
                  A ij
                else
                  0) * row l)
              =
              A ij * row d := by
            trans
              ((if _h : ij.1.1 + ij.2.1 = d.1 then A ij else 0) * row d)
            · refine Finset.sum_eq_single d ?_ ?_
              · intro l hl hld
                have hne : ij.1.1 + ij.2.1 ≠ l.1 := by
                  intro h
                  apply hld; apply Fin.ext; dsimp [d]; rw [h]
                simp [hne]
              · intro hd
                exfalso
                exact hd (Finset.mem_univ d)
            · dsimp [d]
              simp
          simpa [d] using hsingle

/-! =========================================================
    Section 3: Polynomial reconstruction
    This block proves that evaluating the grouped product polynomial at the limb
    radix reconstructs the product of the original extended-register values.
========================================================= -/

/-- Point terms are evaluations of the grouped product polynomial at the Toom-Cook points. -/
lemma tcPointTerm_eq_evalAtPoint_tcProductCoeff
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (hk : 1 < k)
  (st : LayoutState k)
  (b : qs.Basis)
  (pts : List Point)
  (hpts : pts.length = q k) :
  tcPointTerm qs st b pts hpts =
    fun i : Fin (q k) =>
      ToomCookMath.evalAtPoint
        (q k)
        (interpEntry k)
        (tcProductCoeff qs st b)
        ((ptsToFin k pts hpts) i) := by
  funext i
  unfold ToomCookMath.evalAtPoint
  let pt : Point := ptsToFin k pts hpts i
  let X : Fin k → ℤ := fun a => sourceChunkXInt (qs := qs) st a b
  let Z : Fin k → ℤ := fun a => sourceChunkZInt (qs := qs) st a b
  have hlist :
      (ToomCookMath.listToFin pts hpts) i = ptsToFin k pts hpts i := by
    rfl
  unfold tcPointTerm tcProductCoeff evalRowX evalRowZ
  change
    (((∑ a : Fin k,
          expectedRow (k := k) pt a * X a) *
       (∑ b : Fin k,
          expectedRow (k := k) pt b * Z b) : ℤ) : ℚ)
      =
    ∑ l : Fin (q k),
      (∑ ij : Fin k × Fin k,
        if _h : ij.1.1 + ij.2.1 = l.1 then
          ((X ij.1 * Z ij.2 : ℤ) : ℚ)
        else
          0) *
        interpEntry k pt l
  calc
    (((∑ a : Fin k,
          expectedRow (k := k) pt a * X a) *
       (∑ b : Fin k,
          expectedRow (k := k) pt b * Z b) : ℤ) : ℚ)
        =
      ∑ ij : Fin k × Fin k,
        (((expectedRow (k := k) pt ij.1 * X ij.1) *
          (expectedRow (k := k) pt ij.2 * Z ij.2) : ℤ) : ℚ) := by
          norm_cast
          calc
            (∑ a : Fin k, expectedRow pt a * X a) *
                (∑ b : Fin k, expectedRow pt b * Z b)
                =
              ∑ a : Fin k,
                (expectedRow pt a * X a) *
                  (∑ b : Fin k, expectedRow pt b * Z b) := by
                rw [Finset.sum_mul]
            _ =
              ∑ a : Fin k,
                ∑ b : Fin k,
                  (expectedRow pt a * X a) *
                    (expectedRow pt b * Z b) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [Finset.mul_sum]
            _ =
              ∑ ij : Fin k × Fin k,
                (expectedRow pt ij.1 * X ij.1) *
                  (expectedRow pt ij.2 * Z ij.2) := by
                  simpa using
                    (Finset.sum_product
                      (s := (Finset.univ : Finset (Fin k)))
                      (t := (Finset.univ : Finset (Fin k)))
                      (f := fun ij : Fin k × Fin k =>
                        expectedRow pt ij.1 * X ij.1 *
                          (expectedRow pt ij.2 * Z ij.2))).symm
            _ =
              ∑ ij : Fin k × Fin k,
                expectedRow pt ij.1 * X ij.1 *
                  (expectedRow pt ij.2 * Z ij.2) := by
                apply Finset.sum_congr rfl
                intro ij hij
                ring
    _ =
      ∑ ij : Fin k × Fin k,
        ((X ij.1 * Z ij.2 : ℤ) : ℚ) *
          interpEntry k pt
            ⟨ij.1.1 + ij.2.1, by
              simp [q]
              omega
            ⟩ := by
          apply Finset.sum_congr rfl
          intro ij _
          have hrow :=
            expectedRow_mul_expectedRow_eq_interpEntry
              (k := k) hk pt ij.1 ij.2
          calc
            (((expectedRow (k := k) pt ij.1 * X ij.1) *
              (expectedRow (k := k) pt ij.2 * Z ij.2) : ℤ) : ℚ)
                =
              (((expectedRow (k := k) pt ij.1 *
                 expectedRow (k := k) pt ij.2) *
                (X ij.1 * Z ij.2) : ℤ) : ℚ) := by
                  norm_num
                  ring
            _ =
              (((expectedRow (k := k) pt ij.1 *
                 expectedRow (k := k) pt ij.2 : ℤ) : ℚ) *
                ((X ij.1 * Z ij.2 : ℤ) : ℚ)) := by
                  norm_num
            _ =
              ((X ij.1 * Z ij.2 : ℤ) : ℚ) *
                interpEntry k pt
                  ⟨ij.1.1 + ij.2.1, by
                    simp [q]
                    omega
                  ⟩ := by
                    rw [hrow]
                    ring
    _ =
      ∑ l : Fin (q k),
        (∑ ij : Fin k × Fin k,
          if _h : ij.1.1 + ij.2.1 = l.1 then
            ((X ij.1 * Z ij.2 : ℤ) : ℚ)
          else
            0) *
          interpEntry k pt l := by
          symm
          exact sum_degree_group
            (k := k)
            hk
            (fun ij => ((X ij.1 * Z ij.2 : ℤ) : ℚ))
            (fun l => interpEntry k pt l)

/-- The phase-product point condition is the generic interpolation-point condition. -/
lemma GoodToomCookPoints.to_GoodInterpolationPoints
  {k : ℕ}
  {pts : List Point}
  (hpts : pts.length = q k)
  (hInterp : GoodToomCookPoints k pts hpts) :
  ToomCookMath.GoodInterpolationPoints
    (interpEntry k)
    (ptsToFin k pts hpts) := by
  simpa [GoodToomCookPoints, ptsToFin]

/-- Radix evaluation of the product coefficients factors into the two chunk-value polynomials. -/
lemma evalAtRadix_tcProductCoeff_eq_chunk_product
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (hk : 1 < k)
  (st : LayoutState k)
  (b : qs.Basis)
  (B : ℚ) :
  ToomCookMath.evalAtRadix
      (q k)
      (tcProductCoeff qs st b)
      B
    =
  (∑ i : Fin k,
      ((sourceChunkXInt (qs := qs) st i b : ℤ) : ℚ) * B ^ (i : ℕ))
    *
  (∑ j : Fin k,
      ((sourceChunkZInt (qs := qs) st j b : ℤ) : ℚ) * B ^ (j : ℕ)) := by
  classical
  let X : Fin k → ℚ :=
    fun i => ((sourceChunkXInt (qs := qs) st i b : ℤ) : ℚ)
  let Z : Fin k → ℚ :=
    fun i => ((sourceChunkZInt (qs := qs) st i b : ℤ) : ℚ)
  unfold ToomCookMath.evalAtRadix tcProductCoeff
  calc
    (∑ l : Fin (q k),
        (∑ ij : Fin k × Fin k,
          if _h : ij.1.1 + ij.2.1 = l.1 then
            ((sourceChunkXInt (qs := qs) st ij.1 b *
              sourceChunkZInt (qs := qs) st ij.2 b : ℤ) : ℚ)
          else
            0) *
          B ^ (l : ℕ))
        =
      ∑ ij : Fin k × Fin k,
        (X ij.1 * Z ij.2) *
          B ^ (ij.1.1 + ij.2.1) := by
        simpa [X, Z] using
          sum_degree_group
            (k := k)
            hk
            (fun ij : Fin k × Fin k => X ij.1 * Z ij.2)
            (fun l : Fin (q k) => B ^ (l : ℕ))
    _ =
      ∑ ij : Fin k × Fin k,
        (X ij.1 * B ^ (ij.1 : ℕ)) *
          (Z ij.2 * B ^ (ij.2 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro ij _
        have hp : B ^ (ij.1.1 + ij.2.1) = B ^ (ij.1 : ℕ) * B ^ (ij.2 : ℕ) := by rw [pow_add]
        rw [hp]; ring
    _ =
      (∑ i : Fin k, X i * B ^ (i : ℕ)) *
      (∑ j : Fin k, Z j * B ^ (j : ℕ)) := by
        symm
        calc
          (∑ i : Fin k, X i * B ^ (i : ℕ)) *
          (∑ j : Fin k, Z j * B ^ (j : ℕ))
              =
            ∑ i : Fin k,
              (X i * B ^ (i : ℕ)) *
              (∑ j : Fin k, Z j * B ^ (j : ℕ)) := by
              rw [Finset.sum_mul]
          _ =
            ∑ i : Fin k,
              ∑ j : Fin k,
                (X i * B ^ (i : ℕ)) *
                (Z j * B ^ (j : ℕ)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
          _ =
            ∑ ij : Fin k × Fin k,
              (X ij.1 * B ^ (ij.1 : ℕ)) *
              (Z ij.2 * B ^ (ij.2 : ℕ)) := by
              simpa using
                (Finset.sum_product
                  (s := (Finset.univ : Finset (Fin k)))
                  (t := (Finset.univ : Finset (Fin k)))
                  (f := fun ij : Fin k × Fin k =>
                    X ij.1 * B ^ (ij.1 : ℕ) * (Z ij.2 * B ^ (ij.2 : ℕ)))).symm
    _ =
      (∑ i : Fin k,
          ((sourceChunkXInt (qs := qs) st i b : ℤ) : ℚ) * B ^ (i : ℕ))
        *
      (∑ j : Fin k,
          ((sourceChunkZInt (qs := qs) st j b : ℤ) : ℚ) * B ^ (j : ℕ)) := by
        simp [X, Z]

/-- The source `x` chunks reconstruct the signed value of the original `x` register at the limb radix. -/
lemma sourceChunks_reconstruct_x
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (b : qs.Basis) :
  let stInit : LayoutState k :=
    initSignedLayoutState layout
  let W : ℕ := phaseLimbWidth x z k
  let B : ℚ := (2 : ℚ) ^ W
  ((extToInt x b : ℤ) : ℚ)
    =
  ∑ i : Fin k,
    ((sourceChunkXInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
  dsimp
  have hchunk :
      ∀ i : Fin k,
        sourceChunkXInt (qs := qs) (initSignedLayoutState layout) i b
          = splitChunkInt layout.xSplit i b := by
    intro i
    by_cases htop : i.1 + 1 = k
    · have hw :
          (layout.xSplit.child i).width
            = x.width - i.1 * phaseLimbWidth x z k := by
        rw [PhaseSplitLayout.child_width]
        simp [phaseSplitLogicalWidth, isTopChunk, htop]
      simp only [sourceChunkXInt, splitChunkInt, initSignedLayoutState,
        isTopChunk, if_pos htop, extToInt, hw]
    · simp only [sourceChunkXInt, splitChunkInt, initSignedLayoutState,
        isTopChunk, if_neg htop]
  rw [splitChunkInt_reconstruct layout.xSplit b]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hchunk i, ← pow_mul, Nat.mul_comm]

/-- The source `z` chunks reconstruct the signed value of the original `z` register at the limb radix. -/
lemma sourceChunks_reconstruct_z
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (b : qs.Basis) :
  let stInit : LayoutState k :=
    initSignedLayoutState layout
  let W : ℕ := phaseLimbWidth x z k
  let B : ℚ := (2 : ℚ) ^ W
  ((extToInt z b : ℤ) : ℚ)
    =
  ∑ i : Fin k,
    ((sourceChunkZInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
  dsimp
  have hchunk :
      ∀ i : Fin k,
        sourceChunkZInt (qs := qs) (initSignedLayoutState layout) i b
          = splitChunkInt layout.zSplit i b := by
    intro i
    by_cases htop : i.1 + 1 = k
    · have hw :
          (layout.zSplit.child i).width
            = z.width - i.1 * phaseLimbWidth x z k := by
        rw [PhaseSplitLayout.child_width]
        simp [phaseSplitLogicalWidth, isTopChunk, htop]
      simp only [sourceChunkZInt, splitChunkInt, initSignedLayoutState,
        isTopChunk, if_pos htop, extToInt, hw]
    · simp only [sourceChunkZInt, splitChunkInt, initSignedLayoutState,
        isTopChunk, if_neg htop]
  rw [splitChunkInt_reconstruct layout.zSplit b]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hchunk i, ← pow_mul, Nat.mul_comm]

/-- Radix evaluation of the product coefficients is the signed product of the original registers. -/
lemma evalAtRadix_tcProductCoeff_eq_ext_product
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (hk : 1 < k)
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (b : qs.Basis) :
  let stInit : LayoutState k :=
    initSignedLayoutState layout
  let W : ℕ := phaseLimbWidth x z k
  let B : ℚ := (2 : ℚ) ^ W
  ToomCookMath.evalAtRadix (q k) (tcProductCoeff qs stInit b) B
    =
  (((extToInt x b * extToInt z b : ℤ) : ℚ)) := by
  dsimp
  set stInit : LayoutState k :=
    initSignedLayoutState layout
  set W : ℕ := phaseLimbWidth x z k
  set B : ℚ := (2 : ℚ) ^ W
  have hChunk :
      ToomCookMath.evalAtRadix
          (q k)
          (tcProductCoeff qs stInit b)
          B
        =
      (∑ i : Fin k,
          ((sourceChunkXInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ))
        *
      (∑ j : Fin k,
          ((sourceChunkZInt (qs := qs) stInit j b : ℤ) : ℚ) * B ^ (j : ℕ)) := by
    exact evalAtRadix_tcProductCoeff_eq_chunk_product (qs := qs) (hk := hk) (st := stInit) (b := b) (B := B)
  have hx :
      ((extToInt x b : ℤ) : ℚ)
        =
      ∑ i : Fin k,
        ((sourceChunkXInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
    simpa [stInit, W, B] using
      sourceChunks_reconstruct_x (qs := qs) (layout := layout) (b := b)
  have hz :
      ((extToInt z b : ℤ) : ℚ)
        =
      ∑ i : Fin k,
        ((sourceChunkZInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
    simpa [stInit, W, B] using
      sourceChunks_reconstruct_z (qs := qs) (layout := layout) (b := b)
  calc
    ToomCookMath.evalAtRadix
        (q k)
        (tcProductCoeff qs stInit b)
        B
        =
      (∑ i : Fin k,
          ((sourceChunkXInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ))
        *
      (∑ j : Fin k,
          ((sourceChunkZInt (qs := qs) stInit j b : ℤ) : ℚ) * B ^ (j : ℕ)) := hChunk
    _ =
      ((extToInt x b : ℤ) : ℚ) *
      ((extToInt z b : ℤ) : ℚ) := by
        rw [← hx, ← hz]
    _ =
      (((extToInt x b *
         extToInt z b : ℤ) : ℚ)) := by
        norm_num

/-! =========================================================
    Section 4: Final Toom-Cook phase identity
    The final theorem combines point interpolation, radix reconstruction, and
    the compiler phase scalar to produce the signed phase-product scalar.
========================================================= -/

/-- Final interpolation theorem: the accumulated phase scalar is the signed product phase. -/
lemma toom_cook_interpolation
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (layout : Gate.PhaseProductLayout x z k)
  (pts : List Point)
  (hpts : pts.length = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (b : qs.Basis) :
  let stInit : LayoutState k := initSignedLayoutState layout
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsForRegs k x z pts hpts
  phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
    =
  Complex.exp (phi * Complex.I * (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ)))) := by
  dsimp
  set stInit : LayoutState k :=
    initSignedLayoutState layout
  set W : ℕ := phaseLimbWidth x z k
  set B : ℚ := (2 : ℚ) ^ W
  set coeff : Fin (q k) → ℚ := phaseCoeffFromPtsForRegs k x z pts hpts
  set polyCoeff : Fin (q k) → ℚ := tcProductCoeff qs stInit b
  have hCoeff :
      coeff =
        ToomCookMath.interpCoeff
          (interpEntry k)
          (ptsToFin k pts hpts)
          B := by
    simpa [coeff, phaseCoeffFromPtsForRegs, W, B] using
      phaseCoeffFromPtsWidth_eq_interpCoeff
        (k := k) (W := W) (pts := pts) (hpts := hpts)
  have hPoint :
      tcPointTerm qs stInit b pts hpts =
        fun i : Fin (q k) =>
          ToomCookMath.evalAtPoint
            (q k)
            (interpEntry k)
            polyCoeff
            ((ptsToFin k pts hpts) i) := by
    simpa [polyCoeff] using
      tcPointTerm_eq_evalAtPoint_tcProductCoeff
        (qs := qs) (hk := hk) (st := stInit) (b := b) (pts := pts) (hpts := hpts)
  have hInterpSum :
      (∑ i : Fin (q k),
          coeff i *
            ToomCookMath.evalAtPoint
              (q k)
              (interpEntry k)
              polyCoeff
              ((ptsToFin k pts hpts) i))
        =
      ToomCookMath.evalAtRadix
        (q k)
        polyCoeff
        B := by
    rw [hCoeff]
    exact ToomCookMath.interpCoeff_correct
      (row := interpEntry k)
      (pts := ptsToFin k pts hpts)
      (B := B)
      (polyCoeff := polyCoeff)
      (hGood :=
        GoodToomCookPoints.to_GoodInterpolationPoints (hpts := hpts) hInterp)
  have hRadix :
      ToomCookMath.evalAtRadix
          (q k)
          polyCoeff
          B
        =
      (((extToInt x b *
         extToInt z b : ℤ) : ℚ)) := by
    simpa [polyCoeff, stInit, W, B] using
      evalAtRadix_tcProductCoeff_eq_ext_product
        (qs := qs) (hk := hk) (x := x) (z := z) (layout := layout) (b := b)
  have hScalar :
      phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
        =
      Complex.exp
        (phi * Complex.I *
          (((∑ i : Fin (q k),
              coeff i *
                ToomCookMath.evalAtPoint
                  (q k)
                  (interpEntry k)
                  polyCoeff
                  ((ptsToFin k pts hpts) i) : ℚ) : ℂ))) := by
      have hScalarList :
          phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
            =
          ToomCookMath.phaseScalarFromList
            phi coeff (tcPointTerm qs stInit b pts hpts) pts 0
            (by simpa using hpts) := by
        simpa using
          phaseScalarFrom_eq_phaseScalarFromList
            (qs := qs) (phi := phi) (coeff := coeff) (st := stInit) (b := b) (pts := pts) (hpts := hpts)
      rw [hScalarList]
      have hTerms :
          (tcPointTerm qs stInit b pts hpts)
            =
          fun i : Fin (q k) =>
            ToomCookMath.evalAtPoint
              (q k)
              (interpEntry k)
              polyCoeff
              (ptsToFin k pts hpts i) := hPoint
      rw [hTerms]
      exact
        ToomCookMath.phaseScalarFromList_eq_exp_sum
          (k := k)
          (phi := phi)
          (coeff := coeff)
          (terms := fun i : Fin (q k) =>
            ToomCookMath.evalAtPoint
              (q k)
              (interpEntry k)
              polyCoeff
              (ptsToFin k pts hpts i))
          (pts := pts)
          (hpts := hpts)
  calc
    phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
        =
      Complex.exp
        (phi * Complex.I *
          (((∑ i : Fin (q k),
              coeff i *
                ToomCookMath.evalAtPoint
                  (q k)
                  (interpEntry k)
                  polyCoeff
                  ((ptsToFin k pts hpts) i) : ℚ) : ℂ))) := hScalar
    _ =
      Complex.exp
        (phi * Complex.I *
          (((ToomCookMath.evalAtRadix (q k) polyCoeff B : ℚ) : ℂ))) := by
        rw [hInterpSum]
    _ =
      Complex.exp
        (phi * Complex.I *
          (((((extToInt x b *
               extToInt z b : ℤ) : ℚ)) : ℂ))) := by
        rw [hRadix]
    _ =
      Complex.exp
        (phi * Complex.I *
          (((extToInt x b : ℤ) : ℂ) *
           (((extToInt z b : ℤ) : ℂ)))) := by
        congr 2
        norm_num

end Shor
