import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.SupportLemmas

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
