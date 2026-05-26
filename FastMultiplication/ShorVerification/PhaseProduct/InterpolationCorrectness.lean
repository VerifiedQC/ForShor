import FastMultiplication.ShorVerification.PhaseProduct.SupportLemmas

namespace Shor
open Gate
open Operations
open scoped BigOperators

/--
This is the rational version of the integer phase term already appearing in
`phaseScalarFrom`.
-/
def tcPointTerm
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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
  [RegEncoding QSemantics.Basis]
  [ExtRegEncoding qs.Basis]
  (x z : ExtReg)
  (b : qs.Basis) : ℚ :=
  (((ExtRegEncoding.extToInt x b) *
    (ExtRegEncoding.extToInt z b) : ℤ) : ℚ)

def tcProductCoeff
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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
  simp [ phaseCoeffFromPtsWidth, phaseCoeffFromPts, ToomCookMath.interpCoeff]
  unfold ToomCookMath.interpMatrix ToomCookMath.radixRow interpMatrix radixRow ptsToFin ToomCookMath.listToFin
  simp


lemma phaseScalarFrom_eq_phaseScalarFromList_aux
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
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

      have hnlt : n < full.length := by
        rw [hfull]
        simp at hn
        omega

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
        have htail : (List.drop n full).tail = rest := by
          simpa using this

        have hdrop_tail :
            ∀ (xs : List Point) (m : ℕ),
              (List.drop m xs).tail = List.drop (m + 1) xs := by
          simp

        have htail : (List.drop n full).tail = rest := by
          simpa using this

        rw [← hdrop_tail full n]
        exact htail

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
          phaseScalarFrom (qs := qs) k phi coeff st b rest (n + 1)
            (by
              simp at hn
              omega)
          =
          ToomCookMath.phaseScalarFromList
            phi coeff (tcPointTerm qs st b full hfull) rest (n + 1)
            (by
              simp at hn
              omega) := by
        exact ih (n + 1) (by
          simp at hn
          omega) htail_drop

      rw [htail]
      unfold ToomCookMath.phaseFactor

      have hprodC :
          (((evalRowX (qs := qs) st (expectedRow (k := k) pt) b *
              evalRowZ (qs := qs) st (expectedRow (k := k) pt) b : ℤ) : ℚ) : ℂ)
            =
          ((evalRowX (qs := qs) st (expectedRow (k := k) pt) b : ℂ) *
          (evalRowZ (qs := qs) st (expectedRow (k := k) pt) b : ℂ)) := by
        norm_num

      rw [hprodC]
      simp[mul_comm]

lemma phaseScalarFrom_eq_phaseScalarFromList
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
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
  | inf =>
      simp [expectedRow, interpEntry, q]
      by_cases hi : i.1 + 1 = k
      · by_cases hj : j.1 + 1 = k
        · have hij : i.1 + j.1 = 2 * k - 2 := by omega
          cases k with
          | zero =>
              omega

          | succ k' =>
              have hi_last : i = ⟨k', by omega⟩ := by
                apply Fin.ext
                exact Nat.succ_injective hi

              have hj_last : j = ⟨k', by omega⟩ := by
                apply Fin.ext
                exact Nat.succ_injective hj

              have hdeg : i.1 + j.1 = 2 * (k' + 1) - 1 - 1 := by
                omega
              simp [hdeg]
              simp_all only [lt_add_iff_pos_left, ↓reduceIte]
        · have hij : i.1 + j.1 ≠ 2 * k - 2 := by omega

          cases k with
          | zero =>
              omega

          | succ k' =>
              have hi_last : i = ⟨k', by omega⟩ := by
                apply Fin.ext
                exact Nat.succ_injective hi

              have hj_not_last : j ≠ ⟨k', by omega⟩ := by
                intro hj_last
                apply hj
                rw [hj_last]
              have hdeg : k' + j.1 ≠ 2 * (k' + 1) - 1 - 1 := by
                omega
              aesop

      · by_cases hj : j.1 + 1 = k
        · have hij : i.1 + j.1 ≠ 2 * k - 2 := by omega
          cases k with
          | zero =>
              omega

          | succ k' =>
              have hj_last : j = ⟨k', by omega⟩ := by
                apply Fin.ext
                exact Nat.succ_injective hj

              have hi_not_last : i ≠ ⟨k', by omega⟩ := by
                intro hi_last
                apply hi
                rw [hi_last]

              aesop
        · have hij : i.1 + j.1 ≠ 2 * k - 2 := by omega

          cases k with
          | zero =>
              omega

          | succ k' =>
              have hi_not_last : i ≠ ⟨k', by omega⟩ := by
                intro hi_last
                apply hi
                rw [hi_last]
              have hj_not_last : j ≠ ⟨k', by omega⟩ := by
                intro hj_last
                apply hj
                rw [hj_last]
              have hdeg : i.1 + j.1 ≠ 2 * (k' + 1) - 1 - 1 := by
                omega
              simp [hi_not_last, hj_not_last, hdeg]

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
      ⟨ij.1.1 + ij.2.1, by
        simp [q]
        omega
      ⟩ := by
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
          let d : Fin (q k) :=
            ⟨ij.1.1 + ij.2.1, by
              simp [q]
              omega
            ⟩
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
                  apply hld
                  apply Fin.ext
                  dsimp [d]
                  rw[h]
                simp [hne]
              · intro hd
                exfalso
                exact hd (Finset.mem_univ d)
            · dsimp [d]
              simp
          simpa [d] using hsingle

lemma tcPointTerm_eq_evalAtPoint_tcProductCoeff
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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
    unfold ToomCookMath.listToFin ptsToFin
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

lemma GoodToomCookPoints.to_GoodInterpolationPoints
  {k : ℕ}
  {pts : List Point}
  (hpts : pts.length = q k)
  (hInterp : GoodToomCookPoints k pts hpts) :
  ToomCookMath.GoodInterpolationPoints
    (interpEntry k)
    (ptsToFin k pts hpts) := by
  -- probably by unfolding GoodToomCookPoints
  simpa [GoodToomCookPoints, ptsToFin]

lemma evalAtRadix_tcProductCoeff_eq_chunk_product
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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
        have hp :
            B ^ (ij.1.1 + ij.2.1)
              =
            B ^ (ij.1 : ℕ) * B ^ (ij.2 : ℕ) := by
          rw [pow_add]
        rw [hp]
        ring

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

lemma sourceChunks_reconstruct_x
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  {k : ℕ}
  (hk : 0 < k)
  (x z : ExtReg)
  (b : qs.Basis) :
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let W : ℕ := phaseLimbWidth x z k
  let B : ℚ := (2 : ℚ) ^ W
  ((ExtRegEncoding.extToInt x b : ℤ) : ℚ)
    =
  ∑ i : Fin k,
    ((sourceChunkXInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
  dsimp
  let W : ℕ := phaseLimbWidth x z k
  have hValid : ValidPhaseSplit x k W := by
    dsimp [W]
    exact phaseLimbWidth_valid_left x z hk
  have hrec :
      ((ExtRegEncoding.extToInt x b : ℤ) : ℚ)
        =
      ∑ i : Fin k,
        ((splitChunkInt x W i b : ℤ) : ℚ)
          * ((2 : ℚ) ^ W) ^ (i : ℕ) := by
    exact
      splitExtReg_reconstruct_int
        (Basis := qs.Basis)
        x k W b hValid
  simpa [initSignedLayoutState, sourceChunkXInt, splitChunkInt, W] using hrec

lemma sourceChunks_reconstruct_z
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  {k : ℕ}
  (hk : 0 < k)
  (x z : ExtReg)
  (b : qs.Basis) :
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let W : ℕ := phaseLimbWidth x z k
  let B : ℚ := (2 : ℚ) ^ W
  ((ExtRegEncoding.extToInt z b : ℤ) : ℚ)
    =
  ∑ i : Fin k,
    ((sourceChunkZInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
  dsimp
  let W : ℕ := phaseLimbWidth x z k
  have hValid : ValidPhaseSplit z k W := by
    dsimp [W]
    exact phaseLimbWidth_valid_right x z hk
  have hrec :
      ((ExtRegEncoding.extToInt z b : ℤ) : ℚ)
        =
      ∑ i : Fin k,
        ((splitChunkInt z W i b : ℤ) : ℚ)
          * ((2 : ℚ) ^ W) ^ (i : ℕ) := by
    exact
      splitExtReg_reconstruct_int
        (Basis := qs.Basis)
        z k W b hValid
  simpa [initSignedLayoutState, sourceChunkZInt, splitChunkInt, W] using hrec

lemma evalAtRadix_tcProductCoeff_eq_ext_product
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  {k : ℕ}
  (hk : 1 < k)
  (x z : ExtReg)
  (b : qs.Basis) :
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let W : ℕ := phaseLimbWidth x z k
  let B : ℚ := (2 : ℚ) ^ W
  ToomCookMath.evalAtRadix
      (q k)
      (tcProductCoeff qs stInit b)
      B
    =
  (((ExtRegEncoding.extToInt x b *
     ExtRegEncoding.extToInt z b : ℤ) : ℚ)) := by
  dsimp

  set stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
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
    exact evalAtRadix_tcProductCoeff_eq_chunk_product
      (qs := qs)
      (hk := hk)
      (st := stInit)
      (b := b)
      (B := B)

  have hx :
      ((ExtRegEncoding.extToInt x b : ℤ) : ℚ)
        =
      ∑ i : Fin k,
        ((sourceChunkXInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
    simpa [stInit, W, B] using
      sourceChunks_reconstruct_x
        (qs := qs)
        (x := x)
        (z := z)
        (b := b)
        (by omega)

  have hz :
      ((ExtRegEncoding.extToInt z b : ℤ) : ℚ)
        =
      ∑ i : Fin k,
        ((sourceChunkZInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
    simpa [stInit, W, B] using
      sourceChunks_reconstruct_z
        (qs := qs)
        (x := x)
        (z := z)
        (b := b)
        (by omega)

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
      ((ExtRegEncoding.extToInt x b : ℤ) : ℚ) *
      ((ExtRegEncoding.extToInt z b : ℤ) : ℚ) := by
        rw [← hx, ← hz]
    _ =
      (((ExtRegEncoding.extToInt x b *
         ExtRegEncoding.extToInt z b : ℤ) : ℚ)) := by
        norm_num

lemma toom_cook_interpolation
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (pts : List Point)
  (hpts : pts.length = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (b : qs.Basis) :
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsForRegs k x z pts hpts
  phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
    =
  Complex.exp
    (phi * Complex.I *
      (((ExtRegEncoding.extToInt x b : ℤ) : ℂ) *
       (((ExtRegEncoding.extToInt z b : ℤ) : ℂ)))) := by
  dsimp

  set stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
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
        (k := k)
        (W := W)
        (pts := pts)
        (hpts := hpts)

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
        (qs := qs)
        (hk := hk)
        (st := stInit)
        (b := b)
        (pts := pts)
        (hpts := hpts)

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
        GoodToomCookPoints.to_GoodInterpolationPoints
          (hpts := hpts)
          hInterp)

  have hRadix :
      ToomCookMath.evalAtRadix
          (q k)
          polyCoeff
          B
        =
      (((ExtRegEncoding.extToInt x b *
         ExtRegEncoding.extToInt z b : ℤ) : ℚ)) := by
    simpa [polyCoeff, stInit, W, B] using
      evalAtRadix_tcProductCoeff_eq_ext_product
        (qs := qs)
        (hk := hk)
        (x := x)
        (z := z)
        (b := b)

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
            (qs := qs)
            (phi := phi)
            (coeff := coeff)
            (st := stInit)
            (b := b)
            (pts := pts)
            (hpts := hpts)

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
          (((((ExtRegEncoding.extToInt x b *
               ExtRegEncoding.extToInt z b : ℤ) : ℚ)) : ℂ))) := by
        rw [hRadix]
    _ =
      Complex.exp
        (phi * Complex.I *
          (((ExtRegEncoding.extToInt x b : ℤ) : ℂ) *
           (((ExtRegEncoding.extToInt z b : ℤ) : ℂ)))) := by
        congr 2
        norm_num


end Shor
