import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage

open Operations

namespace Table_Generation

/- Given that the operations are well formed, then the operations are also safe -/

lemma SafeProg_of_WellFormed {k : ℕ} {ops : Prog k}
    (hWF : Prog.WellFormed ops) :
    SafeProg ops := by
  intro pre rest d s negSrc sh hops
  have hmem : valid_ops.addScaled d s negSrc sh ∈ ops := by
    rw [hops]
    simp
  simpa [Prog.OpOK] using hWF (valid_ops.addScaled d s negSrc sh) hmem

/- The `carrierAdds` operations are well-formed -/

lemma carrierAdds_WellFormed
    (k : ℕ) (type : PointPairType) (e : ℕ) (dst : Fin k) (parity : ℕ) :
    Prog.WellFormed (carrierAdds k type e dst parity) := by
  unfold carrierAdds
  let f : Prog k → Fin k → Prog k := fun acc j =>
    let d := parityDegree type k j
    if d % 2 = parity then
      if j = dst then acc else acc ++ addConstFrom dst j (twoPowInt (e * d))
    else acc
  have hfold :
      ∀ (xs : List (Fin k)) (acc : Prog k),
        Prog.WellFormed acc → Prog.WellFormed (List.foldl f acc xs) := by
    intro xs
    induction xs with
    | nil => simp
    | cons j js ih =>
        intro acc hacc
        simp [List.foldl]
        apply ih
        dsimp [f]
        by_cases hp : parityDegree type k j % 2 = parity
        · simp [hp]
          by_cases hj : j = dst
          · simpa [hj] using hacc
          ·
            simpa [hj] using
              (WellFormed_append (k := k) hacc
                (addConstFrom_WellFormed (k := k) (dst := dst) (src := j) (by
                  intro h
                  exact hj (by simpa using h.symm)) (twoPowInt (e * parityDegree type k j))))
        · simpa [hp] using hacc
  exact hfold (List.finRange k) [] (by simp [Prog.WellFormed])

/- The `combineParityCarriers` operations are well-formed -/

lemma combineParityCarriers_WellFormed
    {k : ℕ} {even odd : Fin k} (h : even ≠ odd) :
    Prog.WellFormed (combineParityCarriers even odd) := by
  intro op hop
  simp [combineParityCarriers, Prog.OpOK] at hop ⊢
  aesop

/- The `generateParityInitialBlock` operations are well-formed -/

lemma generateParityInitialBlock_WellFormed (k : ℕ) (hk : k ≥ 4) :
    Prog.WellFormed (generateParityInitialBlock k hk) := by
  unfold generateParityInitialBlock
  repeat' apply WellFormed_append
  · apply carrierAdds_WellFormed
  · apply carrierAdds_WellFormed
  · apply combineParityCarriers_WellFormed
    simp
  · intro op hop
    simp at hop
    rcases hop with h | h | h | h <;> subst op <;> simp [Prog.OpOK]
  · apply Prog.apply_Op_inverse_preserves_WF
    repeat' apply WellFormed_append
    · apply carrierAdds_WellFormed
    · apply carrierAdds_WellFormed
    · apply combineParityCarriers_WellFormed
      simp

/-
  The selected even and odd carriers are distinct (for the parity generation), for
  both integer and fraction point pair types
-/

lemma evenCarrier_ne_oddCarrier
    (k : ℕ) (hk : k ≥ 4) (type : PointPairType) :
    evenCarrier k hk type ≠ oddCarrier k hk type := by
  cases type with
  | integer =>
      intro h
      have hv := congrArg Fin.val h
      norm_num [evenCarrier, oddCarrier] at hv
  | fraction =>
      intro h
      have hv := congrArg Fin.val h
      simp [evenCarrier, oddCarrier] at hv
      omega

/- The `generateParityPairBlock` operations are well-formed -/

lemma generateParityPairBlock_WellFormed
    (k : ℕ) (hk : k ≥ 4) (type : PointPairType) (e : ℕ) :
    Prog.WellFormed (generateParityPairBlock k hk type e) := by
  let reven : Fin k := evenCarrier k hk type
  let rodd : Fin k := oddCarrier k hk type
  let buildEven := carrierAdds k type e reven 0
  let buildOdd := [valid_ops.shiftL rodd e] ++ carrierAdds k type e rodd 1
  let build := buildEven ++ buildOdd ++ combineParityCarriers reven rodd
  have hEven : Prog.WellFormed buildEven := by
    dsimp [buildEven, reven]
    apply carrierAdds_WellFormed
  have hOdd : Prog.WellFormed buildOdd := by
    dsimp [buildOdd, rodd]
    simpa using
      (WellFormed_append (k := k)
        (p := [valid_ops.shiftL (oddCarrier k hk type) e])
        (q := carrierAdds k type e (oddCarrier k hk type) 1)
        (by
          intro op hop
          simp at hop
          subst op
          simp [Prog.OpOK])
        (carrierAdds_WellFormed k type e (oddCarrier k hk type) 1))
  have hCombine : Prog.WellFormed (combineParityCarriers reven rodd) := by
    dsimp [reven, rodd]
    exact combineParityCarriers_WellFormed (evenCarrier_ne_oddCarrier k hk type)
  have hbuild : Prog.WellFormed build := by
    dsimp [build]
    exact WellFormed_append (WellFormed_append hEven hOdd) hCombine
  have hphase :
      Prog.WellFormed ([valid_ops.phaseProduct rodd, valid_ops.phaseProduct reven] : Prog k) := by
    intro op hop
    simp at hop
    rcases hop with h | h <;> subst op <;> simp [Prog.OpOK]
  simpa [generateParityPairBlock, reven, rodd, buildEven, buildOdd, build] using
    WellFormed_append (k := k) hbuild
      (WellFormed_append (k := k) hphase (Prog.apply_Op_inverse_preserves_WF hbuild))

lemma phaseProduct_singleton_WellFormed {k : ℕ} (i : Fin k) :
    Prog.WellFormed ([valid_ops.phaseProduct i] : Prog k) := by
  intro op hop
  simp at hop
  subst op
  simp [Prog.OpOK]

lemma opsForPointWithProduct_WellFormed {k : ℕ} (hk : 0 < k) (pt : Point) :
    Prog.WellFormed (opsForPointWithProduct (k := k) hk pt) := by
  cases pt with
  | int z =>
      have hBuild : Prog.WellFormed (computeLocal2 (k := k) hk z) :=
        computeLocal2_Valid (k := k) (z := z) hk
      have hPhase : Prog.WellFormed ([valid_ops.phaseProduct (finZero hk)] : Prog k) :=
        phaseProduct_singleton_WellFormed (k := k) (finZero hk)
      have hInv : Prog.WellFormed (apply_Op_inverse (computeLocal2 (k := k) hk z)) :=
        Prog.apply_Op_inverse_preserves_WF hBuild
      simpa [opsForPointWithProduct] using
        WellFormed_append (k := k) hBuild (WellFormed_append (k := k) hPhase hInv)
  | frac c =>
      by_cases hc : c = 0
      · have hPhase : Prog.WellFormed ([valid_ops.phaseProduct (finLast hk)] : Prog k) :=
          phaseProduct_singleton_WellFormed (k := k) (finLast hk)
        simpa [opsForPointWithProduct, hc] using hPhase
      · have hBuild : Prog.WellFormed (computeFracLocal2 (k := k) hk c) :=
          computeFracLocal2_Valid (k := k) (c := c) hk
        have hPhase : Prog.WellFormed ([valid_ops.phaseProduct (finLast hk)] : Prog k) :=
          phaseProduct_singleton_WellFormed (k := k) (finLast hk)
        have hInv : Prog.WellFormed (apply_Op_inverse (computeFracLocal2 (k := k) hk c)) :=
          Prog.apply_Op_inverse_preserves_WF hBuild
        simpa [opsForPointWithProduct, hc] using
          WellFormed_append (k := k) hBuild (WellFormed_append (k := k) hPhase hInv)

/- The `generateParitySingletonBlock` operations are well-formed -/

lemma generateParitySingletonBlock_WellFormed (k : ℕ) (hk : k ≥ 4) (x : Point) :
    Prog.WellFormed (generateParitySingletonBlock k hk x) := by
  simpa [generateParitySingletonBlock] using
    opsForPointWithProduct_WellFormed (k := k) (by omega) x

/- The `generateParityPairBlocks` operations are well-formed -/

lemma generateParityPairBlocks_WellFormed
    (k : ℕ) (hk : k ≥ 4) (pairCount : ℕ) :
    Prog.WellFormed (generateParityPairBlocks k hk pairCount) := by
  unfold generateParityPairBlocks
  let f : Prog k → ℕ → Prog k := fun acc i =>
    acc ++ generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i)
  have hfold :
      ∀ (xs : List ℕ) (acc : Prog k),
        Prog.WellFormed acc → Prog.WellFormed (List.foldl f acc xs) := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa
    | cons i is ih =>
        intro acc hacc
        simp [List.foldl]
        apply ih
        dsimp [f]
        exact WellFormed_append hacc
          (generateParityPairBlock_WellFormed k hk (pairKindOfIndex i) (pairExponentOfIndex i))
  exact hfold (List.range pairCount) [] (by simp [Prog.WellFormed])

/- The parity block operations are well-formed for PhaseProduct and PhaseTripleProduct -/

lemma generateParityForMode_WellFormed
    (mode : ProductMode) (k : ℕ) (hk : k ≥ 4) :
    Prog.WellFormed (generateParityForMode mode k hk) := by
  unfold generateParityForMode
  by_cases hodd : (mode.pointCount k - 4) % 2 = 1
  · simp only [hodd, ↓reduceIte]
    exact WellFormed_append
      (WellFormed_append
        (generateParityInitialBlock_WellFormed k hk)
        (generateParityPairBlocks_WellFormed k hk ((mode.pointCount k - 4) / 2)))
      (generateParitySingletonBlock_WellFormed k hk (streamPoint (4 + 2 * ((mode.pointCount k - 4) / 2))))
  · simp only [hodd, ↓reduceIte]
    simpa using
      WellFormed_append
        (generateParityInitialBlock_WellFormed k hk)
        (generateParityPairBlocks_WellFormed k hk ((mode.pointCount k - 4) / 2))

end Table_Generation
