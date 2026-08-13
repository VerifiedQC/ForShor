import FastMultiplication.ShorVerification.Implementation.GateCount.Definitions
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.GateConstructions
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.MasterTheoremProof

namespace Shor

/-! =========================================================
    PhaseProduct Gate-Count Lemmas

This file contains the reusable proof infrastructure for the PhaseProduct
asymptotic gate-count theorem: generated-program facts, width-growth bounds,
one-node recurrence estimates, exponent arithmetic, unsigned reductions, and the
controlled signed comparison lemmas.  The public theorem assembly lives in
`PhaseProduct.Main`.
========================================================= -/


/-! ---------------------------------------------------------
    Generated interpolation table facts

This section proves that the automatically generated interpolation program is
well formed, safely consumes the interpolation table, and contributes exactly one
recursive PhaseProduct leaf per generated point.
--------------------------------------------------------- -/

section GeneratedInterpolationFacts

/-- A well-formed PhaseProduct program is safe for the only operation family
whose safety condition is not purely structural: `addScaled`. -/
lemma SafeProg_of_WellFormed {k : ℕ} {ops : Prog k}
    (hWF : Prog.WellFormed ops) :
    SafeProg ops := by
  intro pre rest d s negSrc sh hops
  have hmem : Operations.valid_ops.addScaled d s negSrc sh ∈ ops := by
    rw [hops]
    simp
  simpa [Prog.OpOK] using hWF (Operations.valid_ops.addScaled d s negSrc sh) hmem


/-- A singleton PhaseProduct operation is well formed, serving as the leaf in
each generated interpolation-point block. -/
lemma phaseProduct_singleton_WellFormed {k : ℕ} (i : Fin k) :
    Prog.WellFormed ([Operations.valid_ops.phaseProduct i] : Prog k) := by
  intro op hop
  simp at hop
  subst op
  simp [Prog.OpOK]

/-- The program emitted for one interpolation point is well formed: compute the
local value, emit one PhaseProduct, then uncompute. -/
lemma opsForPointWithProduct_WellFormed {k : ℕ} (hk : 0 < k) (pt : Operations.Point) :
    Prog.WellFormed (opsForPointWithProduct (k := k) hk pt) := by
  cases pt with
  | int z =>
      have hBuild : Prog.WellFormed (computeLocal2 (k := k) hk z) :=
        computeLocal2_Valid (k := k) (z := z) hk
      have hPhase : Prog.WellFormed ([Operations.valid_ops.phaseProduct (finZero hk)] : Prog k) :=
        phaseProduct_singleton_WellFormed (k := k) (finZero hk)
      have hInv : Prog.WellFormed (apply_Op_inverse (computeLocal2 (k := k) hk z)) :=
        Prog.apply_Op_inverse_preserves_WF hBuild
      simpa [opsForPointWithProduct] using
        WellFormed_append (k := k) hBuild (WellFormed_append (k := k) hPhase hInv)
  | frac c =>
      by_cases hc : c = 0
      · have hPhase : Prog.WellFormed ([Operations.valid_ops.phaseProduct (finLast hk)] : Prog k) :=
          phaseProduct_singleton_WellFormed (k := k) (finLast hk)
        simpa [opsForPointWithProduct, hc] using hPhase
      · have hBuild : Prog.WellFormed (computeFracLocal2 (k := k) hk c) :=
          computeFracLocal2_Valid (k := k) (c := c) hk
        have hPhase : Prog.WellFormed ([Operations.valid_ops.phaseProduct (finLast hk)] : Prog k) :=
          phaseProduct_singleton_WellFormed (k := k) (finLast hk)
        have hInv : Prog.WellFormed (apply_Op_inverse (computeFracLocal2 (k := k) hk c)) :=
          Prog.apply_Op_inverse_preserves_WF hBuild
        simpa [opsForPointWithProduct, hc] using
          WellFormed_append (k := k) hBuild (WellFormed_append (k := k) hPhase hInv)

/-- A list of generated point blocks is well formed by appending the
well-formed block for each interpolation point. -/
lemma genOpsWithProduct_WellFormed {k : ℕ} (hk : 0 < k) :
    ∀ pts : List Operations.Point, Prog.WellFormed (genOpsWithProduct (k := k) hk pts)
  | [] => by
      intro op hop
      simp [genOpsWithProduct] at hop
  | pt :: pts => by
      simpa [genOpsWithProduct] using
        WellFormed_append (k := k) (opsForPointWithProduct_WellFormed (k := k) hk pt)
          (genOpsWithProduct_WellFormed (k := k) hk pts)

/-- The generated table safely consumes exactly the interpolation points while
using only well-formed arithmetic operations. -/
lemma genOpsWithProduct_ProgConsumesPtsSafe {k : ℕ} (hk : 0 < k)
    (pts : List Operations.Point) :
    ProgConsumesPtsSafe (k := k) hk State.start_state
      (genOpsWithProduct (k := k) hk pts) pts where
  consumes := genOpsWithProduct_ProgConsumesPts (k := k) hk pts
  safe_add := SafeProg_of_WellFormed
    (genOpsWithProduct_WellFormed (k := k) hk pts)

/-- Integer local-computation blocks contain no PhaseProduct leaves, so they
contribute zero to the PhaseProduct leaf count. -/
lemma computeLocal2_NoPhase {k : ℕ} (hk : 0 < k) (z : ℤ) :
    NoPhase (computeLocal2 (k := k) hk z) := by
  exact NoPhase_of_onlyAddScaled (onlyAddScaled_computeLocal2 (k := k) hk z)

/-- The inverse of an integer local-computation block also contains no
PhaseProduct leaves, keeping uncomputation out of the branching factor. -/
lemma computeLocal2_inverse_NoPhase {k : ℕ} (hk : 0 < k) (z : ℤ) :
    NoPhase (apply_Op_inverse (computeLocal2 (k := k) hk z)) := by
  rw [computeLocal_eq (k := k) (z := z) hk]
  exact (computeLocal_NoPhase_2 (k := k) hk z).2

/-- Each interpolation-point block contributes exactly one recursive
PhaseProduct leaf. -/
lemma phaseProductCount_opsForPointWithProduct {k : ℕ} (hk : 0 < k)
    (pt : Operations.Point) :
    phaseProductCount (opsForPointWithProduct (k := k) hk pt) = 1 := by
  cases pt with
  | int z =>
      have hBuild :
          phaseProductCount (computeLocal2 (k := k) hk z) = 0 :=
        phaseProductCount_eq_zero_of_NoPhase (computeLocal2_NoPhase (k := k) hk z)
      have hInv :
          phaseProductCount (apply_Op_inverse (computeLocal2 (k := k) hk z)) = 0 :=
        phaseProductCount_eq_zero_of_NoPhase (computeLocal2_inverse_NoPhase (k := k) hk z)
      simp [opsForPointWithProduct, phaseProductCount_append,
        phaseProductCount, hBuild, hInv]
  | frac c =>
      by_cases hc : c = 0
      · simp [opsForPointWithProduct, hc, phaseProductCount]
      · have hBuild :
            phaseProductCount (computeFracLocal2 (k := k) hk c) = 0 :=
          phaseProductCount_eq_zero_of_NoPhase (computeFracLocal2_NoPhase (k := k) hk c)
        have hInv :
            phaseProductCount (apply_Op_inverse (computeFracLocal2 (k := k) hk c)) = 0 :=
          phaseProductCount_eq_zero_of_NoPhase ((computeFracLocal2_NoPhase_2 (k := k) hk c).2)
        simp [opsForPointWithProduct, hc, phaseProductCount_append,
          phaseProductCount, hBuild, hInv]

/-- The generated program has one PhaseProduct leaf per interpolation point,
giving the final branching factor `q k `. -/
lemma phaseProductCount_genOpsWithProduct {k : ℕ} (hk : 0 < k) :
    ∀ pts : List Operations.Point,
      phaseProductCount (genOpsWithProduct (k := k) hk pts) = pts.length
  | [] => by
      simp [genOpsWithProduct, phaseProductCount]
  | pt :: pts => by
      simp [genOpsWithProduct, phaseProductCount_append,
        phaseProductCount_opsForPointWithProduct (k := k) hk pt,
        phaseProductCount_genOpsWithProduct (k := k) hk pts, Nat.add_comm]

end GeneratedInterpolationFacts

open Operations

/-! ---------------------------------------------------------
    One-node arithmetic overhead

This short section isolates the fact that the nonrecursive body work at one
PhaseProduct recursion node is linear in the common working width.
--------------------------------------------------------- -/

section ArithmeticOverhead

/-- The fixed body program contributes at most a linear function of the working
width to each recursion node. -/
lemma phaseProgramOverhead_linear
    {k : ℕ}
    (ops : Prog k) :
    ∃ A B : ℕ, ∀ W : ℕ,
      phaseProgramOverhead W ops ≤ A * W + B := by
  induction ops with
  | nil =>
      refine ⟨0, 0, ?_⟩
      intro W
      simp [phaseProgramOverhead]
  | cons op ops ih =>
      rcases ih with ⟨A, B, htail⟩
      refine ⟨A + 20, B + 4, ?_⟩
      intro W
      have hop :
          phaseArithmeticOpCost (k := k) W op ≤ 20 * W + 4 := by
        cases op <;> simp [phaseArithmeticOpCost, rippleAdderGateBound] <;> omega
      calc
        phaseProgramOverhead W (op :: ops)
            = phaseArithmeticOpCost (k := k) W op + phaseProgramOverhead W ops := rfl
        _ ≤ (20 * W + 4) + (A * W + B) :=
            Nat.add_le_add hop (htail W)
        _ ≤ (A + 20) * W + (B + 4) := by
            nlinarith [Nat.zero_le A, Nat.zero_le B, Nat.zero_le W]


end ArithmeticOverhead

/-! ---------------------------------------------------------
    Width-growth bounds for recursive children

This section follows the width scanner through a PhaseProduct body program.  It
shows that every child width is bounded by the top-heavy split width plus a
program-dependent constant, and that failure to recurse can only happen when one
operand is bounded by a program-dependent constant.
--------------------------------------------------------- -/

section WidthGrowthBounds

/-- Updating a bounded width state by one operation preserves boundedness after
adding that operation's advertised width growth. -/
lemma updateWidthState_bounded
    {k : ℕ}
    {st : WidthState k}
    {B : ℕ}
    (hst : WidthStateBounded st B)
    (op : valid_ops k) :
    WidthStateBounded
      (updateWidthState st op)
      (B + phaseOpWidthGrowth op) := by
  classical
  intro i

  cases op with
  | shiftL j n =>
      by_cases hij : i = j
      · subst i
        rcases hst j with ⟨hx, hz⟩
        have hpair :
            st.xw j + n ≤ B + n ∧
            st.zw j + n ≤ B + n := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth] using hpair
      ·
        rcases hst i with ⟨hx, hz⟩
        have hpair :
            st.xw i ≤ B + n ∧
            st.zw i ≤ B + n := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth,
          hij, Ne.symm hij] using hpair

  | shiftR j n =>
      by_cases hij : i = j
      · subst i
        rcases hst j with ⟨hx, hz⟩
        have hpair :
            st.xw j - n ≤ B ∧
            st.zw j - n ≤ B := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth] using hpair
      ·
        rcases hst i with ⟨hx, hz⟩
        have hpair :
            st.xw i ≤ B ∧
            st.zw i ≤ B :=
          ⟨hx, hz⟩
        simpa [updateWidthState, phaseOpWidthGrowth,
          hij, Ne.symm hij] using hpair

  | negate j =>
      by_cases hij : i = j
      · subst i
        rcases hst j with ⟨hx, hz⟩
        have hpair :
            st.xw j + 1 ≤ B + 1 ∧
            st.zw j + 1 ≤ B + 1 := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth] using hpair
      ·
        rcases hst i with ⟨hx, hz⟩
        have hpair :
            st.xw i ≤ B + 1 ∧
            st.zw i ≤ B + 1 := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth,
          hij, Ne.symm hij] using hpair

  | addScaled dst src negSrc shift =>
      by_cases hidst : i = dst
      · subst i
        rcases hst dst with ⟨hxdst, hzdst⟩
        rcases hst src with ⟨hxsrc, hzsrc⟩

        have hxmax :
            max (st.xw dst) (st.xw src + shift)
              ≤ B + shift := by
          apply max_le
          · omega
          · omega

        have hzmax :
            max (st.zw dst) (st.zw src + shift)
              ≤ B + shift := by
          apply max_le
          · omega
          · omega

        have hpair :
            1 + max (st.xw dst) (st.xw src + shift)
                ≤ B + (shift + 1) ∧
            1 + max (st.zw dst) (st.zw src + shift)
                ≤ B + (shift + 1) := by
          constructor <;> omega

        simpa [updateWidthState, phaseOpWidthGrowth] using hpair
      ·
        rcases hst i with ⟨hx, hz⟩
        have hpair :
            st.xw i ≤ B + (shift + 1) ∧
            st.zw i ≤ B + (shift + 1) := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth,
          hidst, Ne.symm hidst] using hpair

  | phaseProduct j =>
      simpa [updateWidthState, phaseOpWidthGrowth] using hst i

/-- The current width state is also a valid bound on the recorded needed
widths, used to initialize the scan invariant. -/
lemma widthsOfState_bounded
    {k : ℕ}
    {st : WidthState k}
    {B : ℕ}
    (hst : WidthStateBounded st B) :
    NeededWidthsBounded (widthsOfState st) B := by
  intro i
  simpa [widthsOfState] using hst i

/-- Needed-width bounds can be weakened, letting later scan steps absorb more
additive growth. -/
lemma neededWidthsBounded_mono
    {k : ℕ}
    {need : NeededWidths k}
    {A B : ℕ}
    (hneed : NeededWidthsBounded need A)
    (hAB : A ≤ B) :
    NeededWidthsBounded need B := by
  intro i
  rcases hneed i with ⟨hx, hz⟩
  exact ⟨hx.trans hAB, hz.trans hAB⟩

/-- Merging two needed-width summaries preserves a common upper bound. -/
lemma mergeNeededWidths_bounded
    {k : ℕ}
    {a b : NeededWidths k}
    {B : ℕ}
    (ha : NeededWidthsBounded a B)
    (hb : NeededWidthsBounded b B) :
    NeededWidthsBounded (mergeNeededWidths a b) B := by
  intro i
  rcases ha i with ⟨hax, haz⟩
  rcases hb i with ⟨hbx, hbz⟩
  change
    max (a.xneed i) (b.xneed i) ≤ B ∧
    max (a.zneed i) (b.zneed i) ≤ B
  exact ⟨max_le hax hbx, max_le haz hbz⟩

/-- Scanning a full program accumulates only the sum of per-operation width
growth, a key input to the recursive-size bound. -/
lemma scanNeededWidthsAux_bounded
    {k : ℕ}
    (cur : WidthState k)
    (mx : NeededWidths k)
    (ops : List (valid_ops k))
    (B : ℕ)
    (hcur : WidthStateBounded cur B)
    (hmx : NeededWidthsBounded mx B) :
    NeededWidthsBounded
      (scanNeededWidthsAux cur mx ops)
      (B + phaseProgramWidthGrowth ops) := by
  induction ops generalizing cur mx B with
  | nil =>
      simpa [scanNeededWidthsAux, phaseProgramWidthGrowth] using hmx

  | cons op rest ih =>
      have hcur' :
          WidthStateBounded
            (updateWidthState cur op)
            (B + phaseOpWidthGrowth op) :=
        updateWidthState_bounded hcur op

      have hmxOld :
          NeededWidthsBounded
            mx
            (B + phaseOpWidthGrowth op) := by
        apply neededWidthsBounded_mono hmx
        omega

      have hcurNeed :
          NeededWidthsBounded
            (widthsOfState (updateWidthState cur op))
            (B + phaseOpWidthGrowth op) :=
        widthsOfState_bounded hcur'

      have hmx' :
          NeededWidthsBounded
            (mergeNeededWidths
              mx
              (widthsOfState (updateWidthState cur op)))
            (B + phaseOpWidthGrowth op) :=
        mergeNeededWidths_bounded hmxOld hcurNeed

      have htail :=
        ih
          (cur := updateWidthState cur op)
          (mx :=
            mergeNeededWidths
              mx
              (widthsOfState (updateWidthState cur op)))
          (B := B + phaseOpWidthGrowth op)
          hcur'
          hmx'

      simpa [scanNeededWidthsAux, phaseProgramWidthGrowth,
        Nat.add_assoc] using htail

/-- A bound on every recorded needed width bounds the common target width
chosen for recursive children. -/
lemma commonNeededWidth_le_of_bounded
    {k : ℕ}
    {need : NeededWidths k}
    {B : ℕ}
    (hneed : NeededWidthsBounded need B) :
    commonNeededWidth need ≤ B + 1 := by
  unfold commonNeededWidth

  have hsup :
      Finset.univ.sup
          (fun i : Fin k =>
            max (need.xneed i) (need.zneed i))
        ≤ B := by
    apply Finset.sup_le
    intro i hi
    exact max_le (hneed i).1 (hneed i).2

  omega

/-- The top-heavy split leaves every limb no larger than the top chunk, which
is the initial width before fixed program growth is added. -/
lemma phaseSplitLogicalWidth_le_topHeavy
    (k W w n : ℕ)
    (hk : 0 < k)
    (hw : w ≤ n)
    (hkW : k * W ≤ n)
    (i : Fin k) :
    phaseSplitLogicalWidth w W k i
      ≤ n - (k - 1) * W := by
  by_cases htop : isTopChunk i
  ·
    have hiSucc : i.val + 1 = k := by
      simpa [isTopChunk] using htop

    have hi : i.val = k - 1 := by
      omega

    simp only [phaseSplitLogicalWidth, if_pos htop, hi]
    omega

  ·
    have hkDecomp : k - 1 + 1 = k := by
      omega

    have hsum :
        W + (k - 1) * W ≤ n := by
      calc
        W + (k - 1) * W
            = (k - 1) * W + W := Nat.add_comm _ _
        _ = ((k - 1) + 1) * W := by
              simp [Nat.add_mul]
        _ = k * W := by
              rw [hkDecomp]
        _ ≤ n := hkW

    have hW :
        W ≤ n - (k - 1) * W := by
      omega

    simpa [phaseSplitLogicalWidth, htop] using hW

/-- The initial layout created from the two input registers is bounded by the
top-heavy chunk width. -/
lemma initWidthState_bounded_topHeavy
    (k : ℕ)
    (hk : 0 < k)
    (x z : ExtReg) :
    WidthStateBounded
      (initWidthState x z k)
      (phaseInputSize x z
        - (k - 1) * phaseLimbWidth x z k) := by
  intro i

  let W : ℕ := phaseLimbWidth x z k
  let n : ℕ := phaseInputSize x z

  have hxle : ExtReg.width x ≤ n := by
    simp [n, phaseInputSize]

  have hzle : ExtReg.width z ≤ n := by
    simp [n, phaseInputSize]

  have hWdiv :
      W ≤ ExtReg.width x / k := by
    simp [W, phaseLimbWidth, phaseLimbWidthOfWidth]

  have hWmul :
      W * k ≤ ExtReg.width x :=
    (Nat.le_div_iff_mul_le hk).mp hWdiv

  have hkW : k * W ≤ n := by
    have hWmax : W * k ≤ n :=
      hWmul.trans hxle
    simpa [Nat.mul_comm] using hWmax

  change
    phaseSplitLogicalWidth (ExtReg.width x) W k i
        ≤ n - (k - 1) * W ∧
    phaseSplitLogicalWidth (ExtReg.width z) W k i
        ≤ n - (k - 1) * W

  exact
    ⟨phaseSplitLogicalWidth_le_topHeavy
        k W (ExtReg.width x) n hk hxle hkW i,
      phaseSplitLogicalWidth_le_topHeavy
        k W (ExtReg.width z) n hk hzle hkW i⟩

/-- The recursive child width is at most the top-heavy chunk width plus the
fixed program's additive growth. -/
lemma nextSignedWidth_le_topHeavy_add_growth
    {k : ℕ}
    (hk : 0 < k)
    (ops : Prog k)
    (x z : ExtReg) :
    nextSignedWidth x z ops
      ≤
    phaseInputSize x z
      - (k - 1) * phaseLimbWidth x z k
      + (phaseProgramWidthGrowth ops + 1) := by
  have hinit :
      WidthStateBounded
        (initWidthState x z k)
        (phaseInputSize x z
          - (k - 1) * phaseLimbWidth x z k) :=
    initWidthState_bounded_topHeavy k hk x z

  have hscan :
      NeededWidthsBounded
        (scanNeededWidths x z ops)
        ((phaseInputSize x z
            - (k - 1) * phaseLimbWidth x z k)
          + phaseProgramWidthGrowth ops) := by
    simpa [scanNeededWidths] using
      scanNeededWidthsAux_bounded
        (cur := initWidthState x z k)
        (mx := widthsOfState (initWidthState x z k))
        (ops := ops)
        (B :=
          phaseInputSize x z
            - (k - 1) * phaseLimbWidth x z k)
        hinit
        (widthsOfState_bounded hinit)

  have hcommon :=
    commonNeededWidth_le_of_bounded hscan

  simpa [nextSignedWidth, Nat.add_assoc] using hcommon



/-- Specializes the top-heavy child-width bound to the generated interpolation program. -/
lemma genOpsWithProduct_nextSignedWidth_topHeavy
    (k : ℕ)
    (hk : 0 < k)
    (pts : List Point) :
    ∃ c : ℕ, ∀ x z : ExtReg,
      nextSignedWidth
          x z
          (genOpsWithProduct (k := k) hk pts)
        ≤
      phaseInputSize x z
        - (k - 1) * phaseLimbWidth x z k
        + c := by
  exact ⟨phaseProgramWidthGrowth (genOpsWithProduct (k := k) hk pts) + 1,
    fun x z => nextSignedWidth_le_topHeavy_add_growth hk
      (genOpsWithProduct (k := k) hk pts) x z⟩
/--
For balanced inputs, every recursively compiled evaluation value has width

  ceil(n / k) + O_k(1).

This is the formal version of the paper's phrase “size roughly n/k”.
-/
lemma genOpsWithProduct_balanced_nextSignedWidth
    (k : ℕ)
    (hk : 1 < k)
    (hk0 : 0 < k)
    (pts : List Point) :
    ∃ c : ℕ, ∀ x z : ExtReg,
      ExtReg.width x = ExtReg.width z →
      nextSignedWidth
          x z
          (genOpsWithProduct (k := k) hk0 pts)
        ≤
      (ExtReg.width x + k - 1) / k + c := by
  rcases
      genOpsWithProduct_nextSignedWidth_topHeavy
        k hk0 pts with
    ⟨c, hc⟩
  refine ⟨c + (k - 1), ?_⟩
  intro x z hbalanced
  let n := ExtReg.width x
  have hsize : phaseInputSize x z = n := by
    simp [phaseInputSize, n, hbalanced]
  have hlimb : phaseLimbWidth x z k = n / k := by
    simp [phaseLimbWidth, phaseLimbWidthOfWidth, n, hbalanced]
  have hceil :
      n - (k - 1) * (n / k) ≤ (n + k - 1) / k + (k - 1) := by
    let q := n / k
    have hdiv : k * q ≤ n := by
      simpa [q] using Nat.mul_div_le n k
    have hmul : k * q = (k - 1) * q + q := by
      have hk_eq : k = (k - 1) + 1 := by omega
      calc
        k * q = ((k - 1) + 1) * q := by
          nth_rewrite 1 [hk_eq]
          rfl
        _ = (k - 1) * q + q := by rw [Nat.add_mul, one_mul]
    have hrem : n % k = n - k * q := by
      simpa [q] using (Nat.mod_eq_sub_mul_div : n % k = n - k * (n / k))
    have hsplit :
        n - (k - 1) * q =
          n % k + q := by
      omega
    have hmod : n % k ≤ k - 1 := by
      have hlt : n % k < k := Nat.mod_lt n hk0
      omega
    have hq_le_ceil : q ≤ (n + k - 1) / k := by
      apply Nat.div_le_div_right
      omega
    have hq :
        n - (k - 1) * q ≤ (n + k - 1) / k + (k - 1) := by
      rw [hsplit]
      omega
    simpa [q] using hq
  calc
    nextSignedWidth x z (genOpsWithProduct (k := k) hk0 pts)
        ≤ phaseInputSize x z - (k - 1) * phaseLimbWidth x z k + c :=
          hc x z
    _ = n - (k - 1) * (n / k) + c := by
          rw [hsize, hlimb]
    _ ≤ (n + k - 1) / k + (c + (k - 1)) := by
          omega

/--
For arbitrary unequal inputs, the first recursive working width is at most the
larger input width plus a constant depending only on the fixed table.
-/
lemma genOpsWithProduct_nextSignedWidth_le_input_add_const
    (k : ℕ)
    (hk : 0 < k)
    (pts : List Point) :
    ∃ c : ℕ, ∀ x z : ExtReg,
      nextSignedWidth
          x z
          (genOpsWithProduct (k := k) hk pts)
        ≤
      phaseInputSize x z + c := by
  rcases
      genOpsWithProduct_nextSignedWidth_topHeavy
        k hk pts with
    ⟨c, hc⟩
  exact ⟨c, fun x z => (hc x z).trans <|
    Nat.add_le_add_right
      (Nat.sub_le (phaseInputSize x z) ((k - 1) * phaseLimbWidth x z k)) c⟩

/-- If the generated signed PhaseProduct does not recurse, then one operand is bounded by a constant. -/
lemma genOpsWithProduct_no_recurse_implies_small_operand
    (k : ℕ)
    (hk : 1 < k)
    (hk0 : 0 < k)
    (pts : List Point) :
    ∃ d : ℕ, ∀ x z : ExtReg,
      (¬ nextSignedWidth x z (genOpsWithProduct (k := k) hk0 pts)
        < phaseInputSize x z)
        →
      (min (ExtReg.width x) (ExtReg.width z) ≤ d) := by
  rcases
      genOpsWithProduct_nextSignedWidth_topHeavy
        k hk0 pts with
    ⟨c, hc⟩
  refine ⟨k * c + k, ?_⟩
  intro x z hnot
  let n := phaseInputSize x z
  let m := min (ExtReg.width x) (ExtReg.width z)
  let W := phaseLimbWidth x z k
  have hn_le_next :
      n ≤ nextSignedWidth x z (genOpsWithProduct (k := k) hk0 pts) := by
    exact Nat.le_of_not_gt hnot
  have hnext :
      nextSignedWidth x z (genOpsWithProduct (k := k) hk0 pts)
        ≤ n - (k - 1) * W + c := by
    simpa [n, W] using hc x z
  have hn_le : n ≤ n - (k - 1) * W + c :=
    le_trans hn_le_next hnext
  have hW : W = m / k := by
    unfold W m phaseLimbWidth phaseLimbWidthOfWidth
    by_cases hxz : ExtReg.width x ≤ ExtReg.width z
    · have hdiv : ExtReg.width x / k ≤ ExtReg.width z / k :=
        Nat.div_le_div_right hxz
      simp [Nat.min_eq_left hxz, Nat.min_eq_left hdiv]
    · have hzx : ExtReg.width z ≤ ExtReg.width x := le_of_not_ge hxz
      have hdiv : ExtReg.width z / k ≤ ExtReg.width x / k :=
        Nat.div_le_div_right hzx
      simp [Nat.min_eq_right hzx, Nat.min_eq_right hdiv]
  by_cases hremove : (k - 1) * W ≤ n
  · have hremove_le_c : (k - 1) * W ≤ c := by
      omega
    have hW_le_c : W ≤ c := by
      have hkpred : 1 ≤ k - 1 := by omega
      nlinarith [hremove_le_c, hkpred, Nat.zero_le W]
    have hmod : m % k ≤ k - 1 := by
      have hlt : m % k < k := Nat.mod_lt m hk0
      omega
    have hsplit : m = k * (m / k) + m % k := by
      simpa [Nat.add_comm] using (Nat.mod_add_div m k).symm
    change m ≤ k * c + k
    rw [hW] at hW_le_c
    calc
      m = k * (m / k) + m % k := hsplit
      _ ≤ k * c + (k - 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left k hW_le_c) hmod
      _ ≤ k * c + k :=
          Nat.add_le_add_left (Nat.sub_le k 1) (k * c)
  · have hn_le_c : n ≤ c := by
      omega
    have hm_le_n : m ≤ n := by
      simp [m, n, phaseInputSize]
    change m ≤ k * c + k
    exact le_trans hm_le_n (le_trans hn_le_c (by nlinarith [Nat.zero_le k, Nat.zero_le c]))

end WidthGrowthBounds

/-! ---------------------------------------------------------
    Exact one-recursion-level cost

This section proves the exact bookkeeping facts for allocation/deallocation and
the one-level low-gate-count estimate for compiling a signed PhaseProduct body.
--------------------------------------------------------- -/

section OneLevelCost
open Gate

variable {Basis : Type u}
  [RegEncoding Basis]
variable (k : ℕ) (hk : 1 < k) (pts : List Point) (hpts : pts.length = q k) (ops : Prog k)

local notation "COST " plan =>
  LowGate.gateCount shorGateCostModel
    (lowerGateRec plan)

@[simp] lemma lgc_id
    (initSize : ℕ) :
    LowGate.gateCount
        shorGateCostModel
        (lowerGateRec
          (PhaseLoweringPlan.id
            (k := k)
            (hk := hk)
            (pts := pts)
            (hpts := hpts)
            (ops := ops)
            initSize))
      =
    0 := by
  rfl

@[simp] lemma lgc_seq
    {initSize : ℕ}
    {U V : Gate}
    (left :
      PhaseLoweringPlan
        k hk pts hpts ops initSize U)
    (right :
      PhaseLoweringPlan
        k hk pts hpts ops initSize V) :
    LowGate.gateCount
        shorGateCostModel
        (lowerGateRec
          (PhaseLoweringPlan.seq left right))
      =
    LowGate.gateCount
        shorGateCostModel
        (lowerGateRec left)
      +
    LowGate.gateCount
        shorGateCostModel
        (lowerGateRec right) := by
  rfl

/--
`lowerGateRec` is insensitive to transports of the plan's `initSize` index.
-/
@[simp] lemma lowerGateRec_transport_initSize_eq
    {m n : ℕ}
    {U : Gate}
    (h : m = n)
    (plan : PhaseLoweringPlan k hk pts hpts ops m U) :
    lowerGateRec (h ▸ plan) = lowerGateRec plan := by
  cases h
  rfl

/--
`lowerGateRec` is insensitive to transports of the plan's gate index.
-/
@[simp] lemma lowerGateRec_transport_gate_eq
    {initSize : ℕ}
    {U V : Gate}
    (h : U = V)
    (plan : PhaseLoweringPlan k hk pts hpts ops initSize U) :
    lowerGateRec (h ▸ plan) = lowerGateRec plan := by
  cases h
  rfl

/--
Erase a cast whose source and target plan types differ only in `initSize`.
The separate index equality is what makes this dependent elimination valid.
-/
lemma lowerGateRec_cast_initSize_of_eq
    {m n : ℕ}
    {U : Gate}
    (hmn : m = n)
    {hType :
      PhaseLoweringPlan k hk pts hpts ops m U =
        PhaseLoweringPlan k hk pts hpts ops n U}
    (plan : PhaseLoweringPlan k hk pts hpts ops m U) :
    lowerGateRec (cast hType plan) = lowerGateRec plan := by
  subst n
  have hh : hType = rfl := Subsingleton.elim _ _
  cases hh
  rfl

/--
Erase a cast whose source and target plan types differ only in the gate index.
-/
lemma lowerGateRec_cast_gate_of_eq
    {initSize : ℕ}
    {U V : Gate}
    (hUV : U = V)
    {hType :
      PhaseLoweringPlan k hk pts hpts ops initSize U =
        PhaseLoweringPlan k hk pts hpts ops initSize V}
    (plan : PhaseLoweringPlan k hk pts hpts ops initSize U) :
    lowerGateRec (cast hType plan) = lowerGateRec plan := by
  subst V
  have hh : hType = rfl := Subsingleton.elim _ _
  cases hh
  rfl

/--
The `Eq.mpr` orientation of `lowerGateRec_cast_gate_of_eq`.
-/
lemma lowerGateRec_mpr_gate_of_eq
    {initSize : ℕ}
    {U V : Gate}
    (hUV : U = V)
    {hType :
      PhaseLoweringPlan k hk pts hpts ops initSize V =
        PhaseLoweringPlan k hk pts hpts ops initSize U}
    (plan : PhaseLoweringPlan k hk pts hpts ops initSize U) :
    lowerGateRec (Eq.mpr hType plan) = lowerGateRec plan := by
  subst V
  have hh : hType = rfl := Subsingleton.elim _ _
  cases hh
  rfl

@[simp] lemma lgc_shiftL
    (initSize : ℕ) (r : ExtReg) (n : ℕ) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (PhaseLoweringPlan.ShiftL
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) initSize r n))
      = 0 := by
  rfl

@[simp] lemma lgc_shiftR
    (initSize : ℕ) (r : ExtReg) (n : ℕ) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (PhaseLoweringPlan.ShiftR
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) initSize r n))
      = 0 := by
  rfl

@[simp] lemma lgc_negate
    (initSize : ℕ) (r : ExtReg) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (PhaseLoweringPlan.Negate
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) initSize r))
      = negateGateBound r := by
  rfl

@[simp] lemma lgc_addScaled
    (initSize : ℕ) (dst src : ExtReg) (b : Bool) (sh : ℕ) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (PhaseLoweringPlan.AddScaled
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) initSize dst src b sh))
      = rippleAdderGateBound (ExtReg.width dst) := by
  rfl

@[simp] lemma lgc_zeroExtend
    (initSize : ℕ) (r : ExtReg) (n : ℕ) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (PhaseLoweringPlan.zeroExtend
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) initSize r n))
      = 0 := by
  rfl

@[simp] lemma lgc_signExtend
    (initSize : ℕ) (r : ExtReg) (n : ℕ) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (PhaseLoweringPlan.signExtend
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) initSize r n))
      = 0 := by
  rfl

@[simp] lemma lgc_zeroDealloc
    (initSize : ℕ) (r : ExtReg) (n : ℕ) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (PhaseLoweringPlan.zeroDealloc
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) initSize r n))
      = 0 := by
  rfl

@[simp] lemma lgc_signDealloc
    (initSize : ℕ) (r : ExtReg) (n : ℕ) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (PhaseLoweringPlan.signDealloc
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) initSize r n))
      = 0 := by
  rfl

@[simp] lemma lgc_radixReverse
    (initSize : ℕ) (r : Reg) (m : ℕ) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (PhaseLoweringPlan.RadixReverse
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) initSize r m))
      = radixReverseGateCount r m := by
  unfold lowerGateRec LowGate.gateCount shorGateCostModel phaseProductCostModel
  rfl

/-
The direct plan-unfolding proof below is intentionally disabled.  The
conditional plan definitions elaborate to opaque `Eq.mpr` transports, so
reducing those particular proof terms is the wrong abstraction for gate
counting.
-/

/-!
Allocation and deallocation plans are indexed by conditional high-level gates.
Gate counting does not need to unfold those dependent plan terms.  Instead, we
recognize the zero-cost bookkeeping fragment from the plan's gate index and
reason structurally over `PhaseLoweringPlan`.
-/

/-- The fragment of high-level gates whose lowerings are pure zero-cost allocation bookkeeping. -/
def BookkeepingGate : Gate → Prop
  | Gate.id =>
      True
  | Gate.seq U V =>
      BookkeepingGate U ∧ BookkeepingGate V
  | Gate.zeroExtend _ _ =>
      True
  | Gate.signExtend _ _ =>
      True
  | Gate.zeroDealloc _ _ =>
      True
  | Gate.signDealloc _ _ =>
      True
  | _ =>
      False

/-- Any lowering plan whose gate index is bookkeeping has zero low-gate cost. -/
lemma gateCount_lowerGateRec_eq_zero_of_bookkeeping
    {initSize : ℕ}
    {U : Gate}
    (plan :
      PhaseLoweringPlan
        k hk pts hpts ops initSize U)
    (hbook : BookkeepingGate U) :
    LowGate.gateCount shorGateCostModel
      (lowerGateRec plan) = 0 := by
  revert hbook
  induction plan with
  | id initSize =>
      intro _
      rfl
  | seq left right ihLeft ihRight =>
      intro hbook
      rcases hbook with ⟨hleft, hright⟩
      simp only [lowerGateRec, LowGate.gateCount]
      simpa only [lowerGateRec] using congrArg₂ Nat.add (ihLeft hleft) (ihRight hright)
  | zeroExtend initSize r n =>
      intro _
      rfl
  | signExtend initSize r n =>
      intro _
      rfl
  | zeroDealloc initSize r n =>
      intro _
      rfl
  | signDealloc initSize r n =>
      intro _
      rfl
  | H initSize qbit =>
      simp [BookkeepingGate]
  | X initSize qbit =>
      simp [BookkeepingGate]
  | Prim initSize tag args =>
      simp [BookkeepingGate]
  | ShiftL initSize r n =>
      simp [BookkeepingGate]
  | ShiftR initSize r n =>
      simp [BookkeepingGate]
  | Negate initSize r =>
      simp [BookkeepingGate]
  | AddScaled initSize dst src negSrc shift =>
      simp [BookkeepingGate]
  | RadixReverse initSize r m =>
      simp [BookkeepingGate]
  | signedBase phi x z hstop =>
      simp [BookkeepingGate]
  | signedStep phi x z layout hrec hcapacity child ihChild =>
      simp [BookkeepingGate]
  | cSignedBase ctrl phi x z hstop =>
      simp [BookkeepingGate]
  | cSignedStep ctrl phi x z layout hrec hcapacity hctrl child ihChild =>
      simp [BookkeepingGate]

/-- Allocating one chunk is recognized as zero-cost bookkeeping. -/
lemma allocChunkGate_bookkeeping
    (i : Fin k)
    (src dst : ExtReg) :
    BookkeepingGate
      (allocChunkGate i src dst) := by
  by_cases h0 : extraDelta src dst = 0
  · simp [allocChunkGate, h0, BookkeepingGate]
  · by_cases htop : isTopChunk i <;>
      simp [allocChunkGate, h0, htop, BookkeepingGate]

/-- Deallocating one chunk is recognized as zero-cost bookkeeping. -/
lemma deallocChunkGate_bookkeeping
    (i : Fin k)
    (src dst : ExtReg) :
    BookkeepingGate
      (deallocChunkGate i src dst) := by
  by_cases h0 : extraDelta src dst = 0
  · simp [deallocChunkGate, h0, BookkeepingGate]
  · by_cases htop : isTopChunk i <;>
      simp [deallocChunkGate, h0, htop, BookkeepingGate]

/-- The auxiliary signed-allocation compiler emits only bookkeeping gates. -/
lemma compileSignedAllocationsAux_bookkeeping
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      BookkeepingGate
        (compileSignedAllocationsAux src dst n hn) := by
  intro n
  induction n with
  | zero =>
      intro hn
      simp [compileSignedAllocationsAux, BookkeepingGate]
  | succ m ih =>
      intro hn
      simp only [compileSignedAllocationsAux, BookkeepingGate]
      constructor
      · exact
          ih
            (Nat.le_trans
              (Nat.le_of_lt (Nat.lt_succ_self m))
              hn)
      · constructor
        · exact allocChunkGate_bookkeeping (k := k) ⟨m, Nat.lt_of_succ_le hn⟩ (src.xslot ⟨m, Nat.lt_of_succ_le hn⟩) (dst.xslot ⟨m, Nat.lt_of_succ_le hn⟩)
        · exact allocChunkGate_bookkeeping (k := k) ⟨m, Nat.lt_of_succ_le hn⟩ (src.zslot ⟨m, Nat.lt_of_succ_le hn⟩) (dst.zslot ⟨m, Nat.lt_of_succ_le hn⟩)

/-- The auxiliary signed-deallocation compiler emits only bookkeeping gates. -/
lemma compileSignedDeallocationsAux_bookkeeping
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      BookkeepingGate
        (compileSignedDeallocationsAux src dst n hn) := by
  intro n
  induction n with
  | zero =>
      intro hn
      simp [compileSignedDeallocationsAux, BookkeepingGate]
  | succ m ih =>
      intro hn
      simp only [compileSignedDeallocationsAux, BookkeepingGate]
      constructor
      · exact deallocChunkGate_bookkeeping (k := k) ⟨m, Nat.lt_of_succ_le hn⟩ (src.zslot ⟨m, Nat.lt_of_succ_le hn⟩) (dst.zslot ⟨m, Nat.lt_of_succ_le hn⟩)
      · constructor
        · exact deallocChunkGate_bookkeeping (k := k) ⟨m, Nat.lt_of_succ_le hn⟩ (src.xslot ⟨m, Nat.lt_of_succ_le hn⟩) (dst.xslot ⟨m, Nat.lt_of_succ_le hn⟩)
        · exact
            ih
              (Nat.le_trans
                (Nat.le_of_lt (Nat.lt_succ_self m))
                hn)

/-- The signed-allocation compiler emits only bookkeeping gates. -/
lemma compileSignedAllocations_bookkeeping
    (src dst : LayoutState k) :
    BookkeepingGate
      (compileSignedAllocations k src dst) := by
  unfold compileSignedAllocations
  exact
    compileSignedAllocationsAux_bookkeeping
      (k := k) src dst k le_rfl

/-- The signed-deallocation compiler emits only bookkeeping gates. -/
lemma compileSignedDeallocations_bookkeeping
    (src dst : LayoutState k) :
    BookkeepingGate
      (compileSignedDeallocations k src dst) := by
  unfold compileSignedDeallocations
  exact
    compileSignedDeallocationsAux_bookkeeping
      (k := k) src dst k le_rfl

/-- Signed allocation plans contribute zero to the low-gate count. -/
lemma lgc_allocs
    (initSize : ℕ) (src dst : LayoutState k) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (planCompileSignedAllocations
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) initSize src dst))
      = 0 := by
  apply gateCount_lowerGateRec_eq_zero_of_bookkeeping
  exact compileSignedAllocations_bookkeeping (k := k) src dst

/-- Signed deallocation plans contribute zero to the low-gate count. -/
lemma lgc_deallocs
    (initSize : ℕ) (src dst : LayoutState k) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (planCompileSignedDeallocations
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) initSize src dst))
      = 0 := by
  apply gateCount_lowerGateRec_eq_zero_of_bookkeeping
  exact compileSignedDeallocations_bookkeeping (k := k) src dst

/-- Unfolds the definition of the signed PhaseProduct gate count to the standard lowering plan. -/
lemma gateCount_standardSignedPhaseLoweringPlan
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : ExtReg)
    (hworkspace :
      SignedRecursiveWorkspaceOK ops x z) :
    LowGate.gateCount
        shorGateCostModel
        (lowerGateRec
          (standardSignedPhaseLoweringPlan
            k hk φ x z ops hworkspace))
      =
    signedPhaseProductGateCount
      (Basis := Basis)
      k hk ops φ x z hworkspace := by
  rfl

/-- In the nonrecursive branch, the standard signed lowering has exactly direct base-case cost. -/
lemma gateCount_standardSignedPhaseLoweringPlan_of_not_recurse
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : ExtReg)
    (hworkspace : SignedRecursiveWorkspaceOK ops x z)
    (hno : ¬ nextSignedWidth x z ops < phaseInputSize x z) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (standardSignedPhaseLoweringPlan
            k hk φ x z ops hworkspace))
      =
    ExtReg.width x * ExtReg.width z := by
  unfold standardSignedPhaseLoweringPlan
  simp only [hno, ↓reduceDIte, PhaseLoweringPlan.lowerGateRec_signedBase]
  rfl

/-- The body overhead of a cons program splits into the head operation cost plus tail overhead. -/
lemma phaseProgramOverhead_cons (W : ℕ) (op : valid_ops k) (rest : List (valid_ops k)) :
    phaseProgramOverhead W (op :: rest)
      = phaseArithmeticOpCost W op + phaseProgramOverhead W rest := rfl

/-- Bounds the lowered cost of a compiled signed body by node overhead plus recursive leaf costs. -/
lemma lgc_body_le
    (W : ℕ)
    (st : LayoutState k)
    (coeff : Fin (q k) → ℚ)
    (φ : ℝ) (R : ℝ)
    (hR : 0 ≤ R)
    (hxw : ∀ i : Fin k, ExtReg.width (st.xslot i) = W)
    (hzw : ∀ i : Fin k, ExtReg.width (st.zslot i) = W)
    (recurse :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan
          k hk pts hpts ops W
          (Gate.SignedPhaseProd
            theta
            (st.xslot i)
            (st.zslot i)))
    (hchild : ∀ (ψ : ℝ) (i : Fin k),
      ((LowGate.gateCount shorGateCostModel
        (lowerGateRec (recurse i ψ))) : ℝ) ≤ R)
    (n : ℕ) (l : List (valid_ops k)) :
      ((LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (planCompileAnnotatedOpsToSignedGateAux
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops) W φ coeff st recurse
            (annotatePhaseTermsAux k n l)))) : ℝ)
      ≤ (phaseProgramOverhead W l : ℝ) + (phaseProductCount l : ℝ) * R := by
  induction l generalizing n with
  | nil =>
      simp [annotatePhaseTermsAux, planCompileAnnotatedOpsToSignedGateAux,
        phaseProgramOverhead, phaseProductCount]
  | cons op rest ih =>
      cases op with
      | shiftL i m =>
          simpa [annotatePhaseTermsAux, planCompileAnnotatedOpsToSignedGateAux,
            lowerGateRec, LowGate.gateCount, phaseProgramOverhead_cons,
            phaseProductCount, phaseArithmeticOpCost] using ih n
      | shiftR i m =>
          simpa [annotatePhaseTermsAux, planCompileAnnotatedOpsToSignedGateAux,
            lowerGateRec, LowGate.gateCount, phaseProgramOverhead_cons,
            phaseProductCount, phaseArithmeticOpCost] using ih n
      | negate i =>
          have ht := ih n
          simp [annotatePhaseTermsAux, planCompileAnnotatedOpsToSignedGateAux,
            lowerGateRec, LowGate.gateCount, shorGateCostModel, phaseProductCostModel,
            phaseProgramOverhead_cons, phaseProductCount, phaseArithmeticOpCost,
            negateGateBound, hxw i, hzw i] at ht ⊢
          linarith
      | addScaled dst src negsrc sh =>
          have ht := ih n
          simp [annotatePhaseTermsAux, planCompileAnnotatedOpsToSignedGateAux,
            lowerGateRec, LowGate.gateCount, shorGateCostModel, phaseProductCostModel,
            phaseProgramOverhead_cons, phaseProductCount, phaseArithmeticOpCost,
            hxw dst, hzw dst] at ht ⊢
          linarith
      | phaseProduct i =>
              classical

  let bodyCost : List (AnnotatedOp k) → ℕ :=
    fun annotatedOps =>
      LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (planCompileAnnotatedOpsToSignedGateAux
            W φ coeff st recurse annotatedOps))

  change
    (bodyCost
        (annotatePhaseTermsAux
          k n (valid_ops.phaseProduct i :: rest)) : ℝ)
      ≤
    (phaseProgramOverhead
        W (valid_ops.phaseProduct i :: rest) : ℝ)
      +
    (phaseProductCount
        (valid_ops.phaseProduct i :: rest) : ℝ) * R

  by_cases hn : n < q k

  · let childCost : ℕ :=
      LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (recurse i
            (φ * ((coeff ⟨n, hn⟩ : ℚ) : ℝ))))

    have hann :
        annotatePhaseTermsAux
            k n (valid_ops.phaseProduct i :: rest)
          =
        ⟨valid_ops.phaseProduct i, some ⟨n, hn⟩⟩
          ::
        annotatePhaseTermsAux k (n + 1) rest := by
      simp [annotatePhaseTermsAux, hn]

    have hcost :
        bodyCost
            (⟨valid_ops.phaseProduct i, some ⟨n, hn⟩⟩
              ::
            annotatePhaseTermsAux k (n + 1) rest)
          =
        childCost
          +
        bodyCost
          (annotatePhaseTermsAux k (n + 1) rest) := by
      rfl

    have hc :
        (childCost : ℝ) ≤ R := by
      dsimp [childCost]
      exact
        hchild
          (φ * ((coeff ⟨n, hn⟩ : ℚ) : ℝ))
          i

    have ht :
        (bodyCost
            (annotatePhaseTermsAux
              k (n + 1) rest) : ℝ)
          ≤
        (phaseProgramOverhead W rest : ℝ)
          +
        (phaseProductCount rest : ℝ) * R := by
      simpa [bodyCost] using ih (n + 1)

    calc
      (bodyCost
          (annotatePhaseTermsAux
            k n (valid_ops.phaseProduct i :: rest)) : ℝ)
          =
        (bodyCost
          (⟨valid_ops.phaseProduct i, some ⟨n, hn⟩⟩
            ::
          annotatePhaseTermsAux k (n + 1) rest) : ℝ) := by
            rw [hann]

      _ =
        (childCost : ℝ)
          +
        (bodyCost
          (annotatePhaseTermsAux k (n + 1) rest) : ℝ) := by
            rw [hcost, Nat.cast_add]

      _ ≤
        R +
          ((phaseProgramOverhead W rest : ℝ)
            +
          (phaseProductCount rest : ℝ) * R) :=
        add_le_add hc ht

      _ =
        (phaseProgramOverhead W rest : ℝ)
          +
        ((phaseProductCount rest : ℝ) + 1) * R := by
          ring

      _ =
        (phaseProgramOverhead
            W (valid_ops.phaseProduct i :: rest) : ℝ)
          +
        (phaseProductCount
            (valid_ops.phaseProduct i :: rest) : ℝ) * R := by
          simp only [
            phaseProgramOverhead_cons,
            phaseArithmeticOpCost,
            phaseProductCount,
            Nat.zero_add,
            Nat.cast_add,
            Nat.cast_one
          ]

  · have hann :
        annotatePhaseTermsAux
            k n (valid_ops.phaseProduct i :: rest)
          =
        ⟨valid_ops.phaseProduct i, none⟩
          ::
        annotatePhaseTermsAux k (n + 1) rest := by
      simp [annotatePhaseTermsAux, hn]

    have hcost :
        bodyCost
            (⟨valid_ops.phaseProduct i, none⟩
              ::
            annotatePhaseTermsAux k (n + 1) rest)
          =
        bodyCost
          (annotatePhaseTermsAux k (n + 1) rest) := by
      rfl

    have ht :
        (bodyCost
            (annotatePhaseTermsAux
              k (n + 1) rest) : ℝ)
          ≤
        (phaseProgramOverhead W rest : ℝ)
          +
        (phaseProductCount rest : ℝ) * R := by
      simpa [bodyCost] using ih (n + 1)

    have hcountMono :
        (phaseProductCount rest : ℝ) * R
          ≤
        ((phaseProductCount rest : ℝ) + 1) * R := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact hR

    calc
      (bodyCost
          (annotatePhaseTermsAux
            k n (valid_ops.phaseProduct i :: rest)) : ℝ)
          =
        (bodyCost
          (⟨valid_ops.phaseProduct i, none⟩
            ::
          annotatePhaseTermsAux k (n + 1) rest) : ℝ) := by
            rw [hann]

      _ =
        (bodyCost
          (annotatePhaseTermsAux k (n + 1) rest) : ℝ) := by
            rw [hcost]

      _ ≤
        (phaseProgramOverhead W rest : ℝ)
          +
        (phaseProductCount rest : ℝ) * R :=
        ht

      _ ≤
        (phaseProgramOverhead W rest : ℝ)
          +
        ((phaseProductCount rest : ℝ) + 1) * R := by
        simp[hcountMono]

      _ =
        (phaseProgramOverhead
            W (valid_ops.phaseProduct i :: rest) : ℝ)
          +
        (phaseProductCount
            (valid_ops.phaseProduct i :: rest) : ℝ) * R := by
          simp only [
            phaseProgramOverhead_cons,
            phaseArithmeticOpCost,
            phaseProductCount,
            Nat.zero_add,
            Nat.cast_add,
            Nat.cast_one
          ]

end OneLevelCost

/-! ---------------------------------------------------------
    Signed PhaseProduct recurrence setup

This section lifts the one-node gate-count facts into the natural-number
recurrence for recursively lowered signed PhaseProduct gates, then proves the
finite bounded-input base needed by strong induction.
--------------------------------------------------------- -/

section SignedRecurrence

/-- One recursive signed PhaseProduct node costs its nonrecursive arithmetic
overhead plus one child cost for each PhaseProduct leaf in the source program. -/
lemma lowerSignedPhaseProd_one_level_cost_le
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : ExtReg)
    (hworkspace : SignedRecursiveWorkspaceOK ops x z)
    (hrec :
      nextSignedWidth x z ops <
        phaseInputSize x z)
    (R : ℝ)
    (hchildren :
      ∀ (ψ : ℝ)
        (a b : ExtReg)
        (hw : SignedRecursiveWorkspaceOK ops a b),
        ExtReg.width a =
            nextSignedWidth x z ops →
        ExtReg.width b =
            nextSignedWidth x z ops →
        (signedPhaseProductGateCount
            (Basis := Basis)
            k hk ops ψ a b hw : ℝ)
          ≤ R) :
    (signedPhaseProductGateCount
        (Basis := Basis)
        k hk ops φ x z hworkspace : ℝ)
      ≤
    (phaseProgramOverhead
        (nextSignedWidth x z ops) ops : ℝ)
      +
    (phaseProductCount ops : ℝ) * R := by

  have hpts :
      (genInterpolationPoints k).length = q k :=
    generatedInterpolationPoints_length k

  let step : CanonicalSignedStep ops x z :=
    canonicalSignedStep
      hk ops x z hrec hworkspace

  let src : LayoutState k :=
    initSignedLayoutState step.layout

  let dst : LayoutState k :=
    targetSignedLayoutState
      src
      (scanNeededWidths x z ops)

  have hxw :
      ∀ i : Fin k,
        ExtReg.width (dst.xslot i) =
          nextSignedWidth x z ops := by
    intro i
    simpa [dst, src, nextSignedWidth] using
      targetSignedLayoutState_xslot_width_scan
        step.layout ops i step.capacity

  have hzw :
      ∀ i : Fin k,
        ExtReg.width (dst.zslot i) =
          nextSignedWidth x z ops := by
    intro i
    simpa [dst, src, nextSignedWidth] using
      targetSignedLayoutState_zslot_width_scan
        step.layout ops i step.capacity

  have childWorkspace
      (i : Fin k) :
      SignedRecursiveWorkspaceOK
        ops
        (dst.xslot i)
        (dst.zslot i) := by
    simpa [src, dst] using
      step.childWorkspace i

  have childSize
      (i : Fin k) :
      phaseInputSize
          (dst.xslot i)
          (dst.zslot i)
        =
      nextSignedWidth x z ops := by
    simpa [src, dst] using
      step.childInputSize i

  have hR : 0 ≤ R := by
    have hi : (0 : ℕ) < k := by
      omega

    have hbound :=
      hchildren
        φ
        (dst.xslot ⟨0, hi⟩)
        (dst.zslot ⟨0, hi⟩)
        (childWorkspace ⟨0, hi⟩)
        (hxw ⟨0, hi⟩)
        (hzw ⟨0, hi⟩)

    exact
      le_trans
        (by positivity)
        hbound

  let recurse :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan
          k hk
          (genInterpolationPoints k)
          hpts
          ops
          (nextSignedWidth x z ops)
          (Gate.SignedPhaseProd
            theta
            (dst.xslot i)
            (dst.zslot i)) := by
    intro i theta
    have hchild :
        SignedRecursiveWorkspaceOK
          ops (dst.xslot i) (dst.zslot i) :=
      childWorkspace i
    have childPlan :=
      standardSignedPhaseLoweringPlan
        k hk theta
        (dst.xslot i)
        (dst.zslot i)
        ops
        hchild
    have hsize :
        phaseInputSize (dst.xslot i) (dst.zslot i) =
          nextSignedWidth x z ops :=
      childSize i
    simpa [hsize] using childPlan

  have hchild :
      ∀ (ψ : ℝ) (i : Fin k),
        (LowGate.gateCount
            shorGateCostModel
            (lowerGateRec
              (recurse i ψ)) : ℝ)
          ≤ R := by
    intro ψ i

    have htransport :
        lowerGateRec (recurse i ψ)
          =
        lowerGateRec
          (standardSignedPhaseLoweringPlan
            k hk ψ
            (dst.xslot i)
            (dst.zslot i)
            ops
            (childWorkspace i)) := by
      dsimp [recurse]
      exact
        lowerGateRec_cast_initSize_of_eq
          (k := k)
          (hk := hk)
          (pts := genInterpolationPoints k)
          (hpts := hpts)
          (ops := ops)
          (childSize i)
          (standardSignedPhaseLoweringPlan
            k hk ψ
            (dst.xslot i)
            (dst.zslot i)
            ops
            (childWorkspace i))

    rw [htransport]

    simpa [
      signedPhaseProductGateCount,
      lowerSignedPhaseProdWithWorkspace,
      lowerSignedPhaseProd
    ] using
      hchildren
        ψ
        (dst.xslot i)
        (dst.zslot i)
        (childWorkspace i)
        (hxw i)
        (hzw i)

  unfold
    signedPhaseProductGateCount
    lowerSignedPhaseProdWithWorkspace
    lowerSignedPhaseProd

  unfold standardSignedPhaseLoweringPlan

  simp only [hrec, ↓reduceDIte]

  simp only [ PhaseLoweringPlan.lowerGateRec_signedStep ]
  unfold planCompiledSignedPhaseGate

  simp only [
    id_eq,
    lgc_seq,
    lgc_allocs,
    lgc_deallocs,
    Nat.zero_add,
    Nat.add_zero
  ]

  have hbody :=
    lgc_body_le
      (k := k)
      (hk := hk)
      (pts := genInterpolationPoints k)
      (hpts := hpts)
      (ops := ops)
      (W := nextSignedWidth x z ops)
      (st := dst)
      (coeff :=
        loweringPhaseCoeff
          k x z (genInterpolationPoints k) hpts)
      (φ := φ)
      (R := R)
      (hR := hR)
      (hxw := hxw)
      (hzw := hzw)
      (recurse := recurse)
      (hchild := hchild)
      (n := 0)
      (l := ops)

  simpa [
    step,
    src,
    dst,
    recurse,
    lowerGateRec_transport_initSize_eq
  ] using hbody

/-- The per-operation overhead is monotone in the common working width. -/
lemma phaseArithmeticOpCost_mono
    {k : ℕ}
    {W₁ W₂ : ℕ}
    (hW : W₁ ≤ W₂)
    (op : valid_ops k) :
    phaseArithmeticOpCost W₁ op ≤
      phaseArithmeticOpCost W₂ op := by
  cases op <;>
    simp [phaseArithmeticOpCost, rippleAdderGateBound] <;>
    omega


/-- The nonrecursive overhead of a fixed program is monotone in width. -/
lemma phaseProgramOverhead_mono
    {k : ℕ}
    (ops : Prog k)
    {W₁ W₂ : ℕ}
    (hW : W₁ ≤ W₂) :
    phaseProgramOverhead W₁ ops ≤
      phaseProgramOverhead W₂ ops := by
  induction ops with
  | nil =>
      simp [phaseProgramOverhead]

  | cons op rest ih =>
      have hop :
          phaseArithmeticOpCost W₁ op ≤
            phaseArithmeticOpCost W₂ op :=
        phaseArithmeticOpCost_mono hW op

      simpa [phaseProgramOverhead] using
        Nat.add_le_add hop ih

/-- Natural-number form of the one-level recurrence, convenient for finite
base-case induction. -/
lemma lowerSignedPhaseProd_one_level_cost_le_nat
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : ExtReg)
    (hworkspace : SignedRecursiveWorkspaceOK ops x z)
    (hrec :
      nextSignedWidth x z ops < phaseInputSize x z)
    (D : ℕ)
    (hchildren :
      ∀ (ψ : ℝ) (a b : ExtReg) (hw : SignedRecursiveWorkspaceOK ops a b),
        ExtReg.width a = nextSignedWidth x z ops →
        ExtReg.width b = nextSignedWidth x z ops →
        signedPhaseProductGateCount
            (Basis := Basis) k hk ops ψ a b hw
          ≤ D) :
    signedPhaseProductGateCount
        (Basis := Basis) k hk ops φ x z hworkspace
      ≤
    phaseProgramOverhead
        (nextSignedWidth x z ops) ops
      +
    phaseProductCount ops * D := by

  have hchildrenR :
      ∀ (ψ : ℝ) (a b : ExtReg) (hw : SignedRecursiveWorkspaceOK ops a b),
        ExtReg.width a = nextSignedWidth x z ops →
        ExtReg.width b = nextSignedWidth x z ops →
        (signedPhaseProductGateCount
            (Basis := Basis) k hk ops ψ a b hw : ℝ)
          ≤ (D : ℝ) := by
    intro ψ a b hw ha hb
    have h := hchildren ψ a b hw ha hb
    exact_mod_cast h

  have hreal :=
    lowerSignedPhaseProd_one_level_cost_le
      (Basis := Basis)
      k hk ops φ x z
      hworkspace
      hrec
      (D : ℝ)
      hchildrenR

  have hcast :
      (signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ x z hworkspace : ℝ)
        ≤
      ((phaseProgramOverhead
          (nextSignedWidth x z ops) ops
          + phaseProductCount ops * D : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hreal

  exact_mod_cast hcast

/--
Uniform boundedness on a finite range of input widths.

This supplies the finite base cases in the strong-induction proof of the
recurrence.
-/
lemma signedPhaseProductGateCount_bounded_on_bounded_inputs
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (N : ℕ) :
    ∃ D : ℕ, ∀ (φ : ℝ) (x z : ExtReg)
      (hworkspace : SignedRecursiveWorkspaceOK ops x z),
      phaseInputSize x z ≤ N →
      signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ x z hworkspace
        ≤ D := by
  classical

  induction N with
  | zero =>
      refine ⟨0, ?_⟩
      intro φ x z hworkspace hsize

      have hsize0 : phaseInputSize x z = 0 :=
        Nat.eq_zero_of_le_zero hsize

      have hx : ExtReg.width x = 0 := by
        have hxle :
            ExtReg.width x ≤ phaseInputSize x z := by
          simp [phaseInputSize]
        omega

      have hz : ExtReg.width z = 0 := by
        have hzle :
            ExtReg.width z ≤ phaseInputSize x z := by
          simp [phaseInputSize]
        omega

      have hno :
          ¬ nextSignedWidth x z ops < phaseInputSize x z := by
        omega
      unfold
        signedPhaseProductGateCount
        lowerSignedPhaseProdWithWorkspace
        lowerSignedPhaseProd
      rw [
        gateCount_standardSignedPhaseLoweringPlan_of_not_recurse
          (Basis := Basis) k hk ops φ x z hworkspace hno,
        hx,
        hz
      ]

  | succ N ih =>
      rcases ih with ⟨D, hD⟩

      refine
        ⟨max
            (N.succ * N.succ)
            (phaseProgramOverhead N ops
              + phaseProductCount ops * D),
          ?_⟩

      intro φ x z hworkspace hsize

      by_cases hrec :
          nextSignedWidth x z ops < phaseInputSize x z

      · -- Recursive case.
        have hW :
            nextSignedWidth x z ops ≤ N := by
          omega

        have hchildren :
            ∀ (ψ : ℝ) (a b : ExtReg) (hw : SignedRecursiveWorkspaceOK ops a b),
              ExtReg.width a = nextSignedWidth x z ops →
              ExtReg.width b = nextSignedWidth x z ops →
              signedPhaseProductGateCount
                  (Basis := Basis) k hk ops ψ a b hw
                ≤ D := by
          intro ψ a b hw ha hb
          apply hD ψ a b hw

          have :
              phaseInputSize a b =
                nextSignedWidth x z ops := by
            simp [phaseInputSize, ha, hb]

          rw [this]
          exact hW

        have hnode :
            signedPhaseProductGateCount
                (Basis := Basis) k hk ops φ x z hworkspace
              ≤
            phaseProgramOverhead
                (nextSignedWidth x z ops) ops
              +
            phaseProductCount ops * D :=
          lowerSignedPhaseProd_one_level_cost_le_nat
            (Basis := Basis)
            k hk ops φ x z
            hworkspace
            hrec
            D
            hchildren

        have hoverhead :
            phaseProgramOverhead
                (nextSignedWidth x z ops) ops
              ≤
            phaseProgramOverhead N ops :=
          phaseProgramOverhead_mono ops hW

        have hnode' :
            signedPhaseProductGateCount
                (Basis := Basis) k hk ops φ x z hworkspace
              ≤
            phaseProgramOverhead N ops
              + phaseProductCount ops * D :=
          hnode.trans
            (Nat.add_le_add_right
              hoverhead
              (phaseProductCount ops * D))

        exact hnode'.trans (Nat.le_max_right _ _)

      · -- Direct/base-case branch.
        have hbase :
            signedPhaseProductGateCount
                (Basis := Basis) k hk ops φ x z hworkspace
              =
            ExtReg.width x * ExtReg.width z := by
          unfold
            signedPhaseProductGateCount
            lowerSignedPhaseProdWithWorkspace
            lowerSignedPhaseProd
          exact
            gateCount_standardSignedPhaseLoweringPlan_of_not_recurse
              (Basis := Basis) k hk ops φ x z hworkspace hrec

        have hxmax :
            ExtReg.width x ≤ phaseInputSize x z := by
          simp [phaseInputSize]

        have hzmax :
            ExtReg.width z ≤ phaseInputSize x z := by
          simp[phaseInputSize]

        have hx : ExtReg.width x ≤ N.succ :=
          hxmax.trans hsize

        have hz : ExtReg.width z ≤ N.succ :=
          hzmax.trans hsize

        have hprod :
            ExtReg.width x * ExtReg.width z
              ≤ N.succ * N.succ :=
          Nat.mul_le_mul hx hz

        rw [hbase]
        exact hprod.trans (Nat.le_max_left _ _)



end SignedRecurrence

/-! ---------------------------------------------------------
    Exponent arithmetic

This section contains the real-analysis facts about the comparison exponent
`log_k (2k - 1)` used when solving the PhaseProduct recurrence.
--------------------------------------------------------- -/

section ExponentArithmetic

/-- Since `2k - 1 > k` for `k > 1`, the paper's exponent is greater than one. -/
lemma one_lt_phaseProductExponent
    (k : ℕ)
    (hk : 1 < k) :
    1 < phaseProductExponent k := by
  have hkR : 1 < (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := lt_trans zero_lt_one hkR
  have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  have hkqNat : k < q k  := by
    unfold q
    omega
  have hkq : (k : ℝ) < (q k  : ℝ) := by exact_mod_cast hkqNat
  have hloglt : Real.log (k : ℝ) < Real.log (q k  : ℝ) :=
    Real.log_lt_log hkpos hkq
  unfold phaseProductExponent
  rw [lt_div_iff₀ hlogpos]
  simpa using hloglt

/--
The exponent was chosen so that one level's branching factor is exactly the
corresponding power of the shrink factor:

  k ^ log_k(2k - 1) = 2k - 1.
-/
lemma rpow_phaseProductExponent_eq_q
    (k : ℕ)
    (hk : 1 < k) :
    Real.rpow (k : ℝ) (phaseProductExponent k) = (q k : ℝ) := by
  have hkR : 1 < (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := lt_trans zero_lt_one hkR
  have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  have hqposNat : 0 < q k  := by
    unfold q
    omega
  have hqpos : 0 < (q k  : ℝ) := by exact_mod_cast hqposNat
  unfold phaseProductExponent
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hkpos]
  have hmul :
      Real.log (k : ℝ) * (Real.log (q k  : ℝ) / Real.log (k : ℝ))
        = Real.log (q k : ℝ) := by
    field_simp [hlogpos.ne']
  rw [hmul, Real.exp_log hqpos]



/-- Converts the balanced child-width shrinkage estimate into the shifted form used by recurrence solving. -/
lemma balanced_nextSignedWidth_shifted
    (k c n W : ℕ)
    (hk : 1 < k)
    (hM : k * (c + 1) + 1 ≤ n)
    (hW : W ≤ (n + k - 1) / k + c) :
    W ≤
      k * (c + 1) + 1 +
        (n - (k * (c + 1) + 1)) / k := by
  let M : ℕ := k * (c + 1) + 1
  let t : ℕ := n - M

  have hn : n = M + t := by
    dsimp [M, t]
    omega

  have hk0 : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega

  have hnum :
      M + t + k - 1 =
        t + k * (c + 2) := by
    dsimp [M]
    have h₁ :
        k * (c + 1) + 1 + t + k - 1 =
          k * (c + 1) + t + k := by
      omega
    rw [h₁]
    ring

  have hdiv :
      (M + t + k - 1) / k + c
        =
      t / k + (c + 2) + c := by
    rw [hnum]
    rw [Nat.add_mul_div_left t (c + 2) hk0]

  have hkc :
      2 * (c + 1) ≤ k * (c + 1) :=
    Nat.mul_le_mul_right (c + 1) hk2

  have hsmall :
      t / k + (c + 2) + c
        ≤
      M + t / k := by
    dsimp [M]
    omega

  rw [hn] at hW
  rw [hdiv] at hW
  simpa [M, t, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hW.trans hsmall

end ExponentArithmetic

/-! ---------------------------------------------------------
    Balanced signed recurrence solution

This section packages the one-level recurrence, child-width shrinkage, and the
master theorem into the balanced signed PhaseProduct asymptotic bound. It then
prepares the bridge from balanced signed instances to the public unsigned gate.
--------------------------------------------------------- -/

section BalancedSignedSolution

/-- Solves the balanced signed PhaseProduct recurrence using the master theorem. -/
lemma balanced_phaseProduct_recurrence_solution
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hcount :
      phaseProductCount ops = q k )
    (hwidth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        ExtReg.width x = ExtReg.width z →
        nextSignedWidth x z ops
          ≤ (ExtReg.width x + k - 1) / k + c)
    (hoverhead :
      ∃ A B : ℕ, ∀ W : ℕ,
        phaseProgramOverhead W ops ≤ A * W + B) :
    ∃ C : ℝ, 0 < C ∧
      BalancedSignedPhaseProductBound
        (Basis := Basis) k hk ops C := by
  classical

  rcases hwidth with ⟨c, hwidth⟩
  rcases hoverhead with ⟨A, B, hoverhead⟩

  let size : BalancedPhaseProductInstance ops → ℕ :=
    fun i => ExtReg.width i.x

  let next : BalancedPhaseProductInstance ops → ℕ :=
    fun i => nextSignedWidth i.x i.z ops

  let cost : BalancedPhaseProductInstance ops → ℕ :=
    fun i =>
      signedPhaseProductGateCount
        (Basis := Basis)
        k hk ops i.φ i.x i.z i.hworkspace

  /-
  The generated recursive width is at most

      ceil(n / k) + c

  on every balanced instance.
  -/
  have hnext :
      ∀ i : BalancedPhaseProductInstance ops,
        next i ≤
          (size i + k - 1) / k + c := by
    intro i

    simpa [next, size] using
      hwidth i.x i.z i.hwidth

  /-
  All instances whose widths lie below a fixed cutoff have a uniform
  gate-count bound.
  -/
  have hbounded :
      ∀ N : ℕ,
        ∃ D : ℕ, ∀ i : BalancedPhaseProductInstance ops,
          size i ≤ N →
          cost i ≤ D := by
    intro N

    obtain ⟨D, hD⟩ :=
      signedPhaseProductGateCount_bounded_on_bounded_inputs
        (Basis := Basis)
        k hk ops N

    refine ⟨D, ?_⟩
    intro i hi

    apply hD i.φ i.x i.z i.hworkspace

    have hsize :
        phaseInputSize i.x i.z = size i := by
      simp [phaseInputSize, size, i.hwidth]

    rw [hsize]
    exact hi

  /-
  This is the compiler-specific one-level recurrence.

  If all balanced instances of the recursive width have cost at most `D`,
  then this instance has cost at most

      A * next + B + q(k) * D.
  -/
  have hstep :
      ∀ i : BalancedPhaseProductInstance ops,
        next i < size i →
        ∀ D : ℕ,
          (∀ j : BalancedPhaseProductInstance ops,
            size j = next i →
            cost j ≤ D) →
          cost i ≤
            A * next i + B + q k  * D := by
    intro i hrec D hchildrenBound

    have hrec' :
        nextSignedWidth i.x i.z ops
          < phaseInputSize i.x i.z := by
      simpa [next, size, phaseInputSize, i.hwidth] using hrec

    have hchildren :
        ∀ (ψ : ℝ) (a b : ExtReg) (hw : SignedRecursiveWorkspaceOK ops a b),
          ExtReg.width a =
              nextSignedWidth i.x i.z ops →
          ExtReg.width b =
              nextSignedWidth i.x i.z ops →
          signedPhaseProductGateCount
              (Basis := Basis)
              k hk ops ψ a b hw
            ≤ D := by
      intro ψ a b hw ha hb

      let j : BalancedPhaseProductInstance ops :=
        {
          φ := ψ
          x := a
          z := b
          hwidth := ha.trans hb.symm
          hworkspace := hw
        }

      have hjsize :
          size j = next i := by
        simp [j, size, next, ha]

      exact hchildrenBound j hjsize

    have honeLevel :
        signedPhaseProductGateCount
            (Basis := Basis)
            k hk ops i.φ i.x i.z i.hworkspace
          ≤
        phaseProgramOverhead
            (nextSignedWidth i.x i.z ops)
            ops
          +
        phaseProductCount ops * D :=
      lowerSignedPhaseProd_one_level_cost_le_nat
        (Basis := Basis)
        k hk ops
        i.φ i.x i.z
        i.hworkspace
        hrec'
        D
        hchildren

    have hoverhead' :
        phaseProgramOverhead (next i) ops
          ≤ A * next i + B :=
      hoverhead (next i)

    calc
      cost i
          ≤
        phaseProgramOverhead (next i) ops
          + phaseProductCount ops * D := by
            simpa [cost, next] using honeLevel
      _ ≤
        (A * next i + B)
          + phaseProductCount ops * D :=
        Nat.add_le_add_right
          hoverhead'
          (phaseProductCount ops * D)
      _ =
        A * next i + B + q k  * D := by
          rw [hcount]

  obtain ⟨C, hC, hmaster⟩ :=
    shifted_master_theorem_exact_family
      (ι := BalancedPhaseProductInstance ops)
      (k := k)
      (q := q k )
      (c := c)
      (A := A)
      (B := B)
      (α := phaseProductExponent k)
      hk
      (one_lt_phaseProductExponent k hk)
      (rpow_phaseProductExponent_eq_q k  hk)
      size
      next
      cost
      hnext
      hbounded
      hstep

  refine ⟨C, hC, ?_⟩

  intro φ x z hworkspace hxz

  let i : BalancedPhaseProductInstance ops :=
    {
      φ := φ
      x := x
      z := z
      hwidth := hxz
      hworkspace := hworkspace
    }

  have hi := hmaster i

  simpa [
    i,
    size,
    cost,
    phaseProductSafeRate
  ] using hi

/-- The public unsigned macro's workspace proof contains exactly the signed
recursive workspace proof needed by its central signed phase-product node. -/
lemma phaseProdUsing_signedWorkspace
    (ops : Prog k)
    (φ : ℝ)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (hworkspace :
      GateWorkspaceOK ops
        (Gate.PhaseProdUsing φ x z ws)) :
    SignedRecursiveWorkspaceOK ops
      (ws.xExt.grow 1)
      (ws.zExt.grow 1) := by
  simpa [GateWorkspaceOK, Gate.PhaseProdUsing] using hworkspace

/-- Rewrites the public unsigned `PhaseProdUsing` lowering as the signed
recurrence on the two one-bit-grown workspace registers. -/
lemma lowerGate_PhaseProdUsing_gateCount_eq_signed
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (hworkspace :
      GateWorkspaceOK ops
        (Gate.PhaseProdUsing φ x z ws)) :
    LowGate.gateCount shorGateCostModel
      (lowerGate (Basis := Basis) k hk ops
        (Gate.PhaseProdUsing φ x z ws) hworkspace)
      =
    signedPhaseProductGateCount
      (Basis := Basis) k hk ops φ
      (ws.xExt.grow 1)
      (ws.zExt.grow 1)
      (phaseProdUsing_signedWorkspace ops φ x z ws hworkspace) := by
  simp [
    lowerGate,
    Gate.PhaseProdUsing,
    signedPhaseProductGateCount,
    lowerSignedPhaseProdWithWorkspace,
    LowGate.gateCount,
    shorGateCostModel,
    phaseProductCostModel
  ]

/-- The unsigned bridge adds exactly one active high bit to the x operand. -/
@[simp]
lemma width_phaseProdUsing_x
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z) :
    ExtReg.width (ws.xExt.grow 1) = regSize x + 1 := by
  simpa [Gate.PhaseProdWorkspace.xExt, ExtReg.width] using
    ExtReg.width_grow ws.xExt 1 ws.xExt_canGrow

/-- The unsigned bridge adds exactly one active high bit to the z operand. -/
@[simp]
lemma width_phaseProdUsing_z
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z) :
    ExtReg.width (ws.zExt.grow 1) = regSize z + 1 := by
  simpa [Gate.PhaseProdWorkspace.zExt, ExtReg.width] using
    ExtReg.width_grow ws.zExt 1 ws.zExt_canGrow

/-- The signed input size of the two grown operands is the original maximum
register width plus one. -/
@[simp]
lemma phaseInputSize_phaseProdUsing
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z) :
    phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1)
      =
    max (regSize x) (regSize z) + 1 := by
  simp only [
    phaseInputSize,
    width_phaseProdUsing_x,
    width_phaseProdUsing_z
  ]
  by_cases h : regSize x ≤ regSize z
  · rw [
      max_eq_right h,
      max_eq_right (Nat.add_le_add_right h 1)
    ]
  · have h' : regSize z ≤ regSize x :=
      Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [
      max_eq_left h',
      max_eq_left (Nat.add_le_add_right h' 1)
    ]

/-- Absorbs the safe-rate clamp and additive width growth into a constant multiple of the raw rate. -/
lemma phaseProductSafeRate_le_scaled_rpow
    (k : ℕ)
    (hk : 1 < k)
    {W n s : ℕ}
    (hn : 1 ≤ n)
    (hW : W ≤ n + s) :
    phaseProductSafeRate k W
      ≤
    Real.rpow ((s + 1 : ℕ) : ℝ) (phaseProductExponent k) *
      Real.rpow (n : ℝ) (phaseProductExponent k) := by
  have hα :
      0 ≤ phaseProductExponent k := by
    have hα' := one_lt_phaseProductExponent k hk
    linarith

  have hmax :
      max 1 W ≤ n + s := by
    apply max_le
    · omega
    · exact hW

  have hs_mul :
      s ≤ s * n := by
    simpa using Nat.mul_le_mul_left s hn

  have hscale :
      n + s ≤ (s + 1) * n := by
    calc
      n + s ≤ n + s * n :=
        Nat.add_le_add_left hs_mul n
      _ = (s + 1) * n := by
        simp [Nat.add_mul, Nat.add_comm]

  have hpow₁ :
      Real.rpow ((max 1 W : ℕ) : ℝ)
          (phaseProductExponent k)
        ≤
      Real.rpow ((n + s : ℕ) : ℝ)
          (phaseProductExponent k) :=
    Real.rpow_le_rpow
      (by positivity)
      (by exact_mod_cast hmax)
      hα

  have hpow₂ :
      Real.rpow ((n + s : ℕ) : ℝ)
          (phaseProductExponent k)
        ≤
      Real.rpow (((s + 1) * n : ℕ) : ℝ)
          (phaseProductExponent k) :=
    Real.rpow_le_rpow
      (by positivity)
      (by exact_mod_cast hscale)
      hα

  calc
    phaseProductSafeRate k W
        =
      Real.rpow ((max 1 W : ℕ) : ℝ)
        (phaseProductExponent k) := rfl
    _ ≤
      Real.rpow ((n + s : ℕ) : ℝ)
        (phaseProductExponent k) := hpow₁
    _ ≤
      Real.rpow (((s + 1) * n : ℕ) : ℝ)
        (phaseProductExponent k) := hpow₂
    _ =
      Real.rpow ((s + 1 : ℕ) : ℝ)
          (phaseProductExponent k) *
        Real.rpow (n : ℝ)
          (phaseProductExponent k) := by
      simpa only [Nat.cast_mul] using
        (Real.mul_rpow
          (show 0 ≤ ((s + 1 : ℕ) : ℝ) by positivity)
          (show 0 ≤ (n : ℝ) by positivity)
          (z := phaseProductExponent k))

/--
For `n ≥ 1`, the linear function `n` is bounded by the
PhaseProduct comparison power because its exponent is greater than one.
-/
lemma natCast_le_phaseProduct_rpow
    (k : ℕ)
    (hk : 1 < k)
    {n : ℕ}
    (hn : 1 ≤ n) :
    (n : ℝ)
      ≤
    Real.rpow (n : ℝ) (phaseProductExponent k) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  exact
    Real.self_le_rpow_of_one_le
      hnR
      (le_of_lt (one_lt_phaseProductExponent k hk))

/--
In the nonrecursive branch, lowering is exactly the direct signed
PhaseProduct, whose cost is the product of the operand widths.
-/
lemma signedPhaseProductGateCount_eq_direct_of_not_recurse
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : ExtReg)
    (hworkspace :
      SignedRecursiveWorkspaceOK ops x z)
    (hno :
      ¬ nextSignedWidth x z ops < phaseInputSize x z) :
    signedPhaseProductGateCount
        (Basis := Basis) k hk ops φ x z hworkspace
      =
    ExtReg.width x * ExtReg.width z := by
  unfold
    signedPhaseProductGateCount
    lowerSignedPhaseProdWithWorkspace
    lowerSignedPhaseProd
  exact
    gateCount_standardSignedPhaseLoweringPlan_of_not_recurse
      (Basis := Basis) k hk ops φ x z hworkspace hno

/-- Bounds the public unsigned theorem's recursive branch by applying the
balanced signed bound to the equal-width recursive children. -/
lemma signedPhaseProductGateCount_unsignedView_recurse_case_bound
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hcount :
      phaseProductCount ops = q k )
    (hoverhead :
      ∃ A B : ℕ, ∀ W : ℕ,
        phaseProgramOverhead W ops ≤ A * W + B)
    (hgrowth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        nextSignedWidth x z ops ≤ phaseInputSize x z + c)
    (C : ℝ)
    (hC : 0 < C)
    (hbalanced :
      BalancedSignedPhaseProductBound
        (Basis := Basis) k hk ops C) :
    ∃ Cᵣ : ℝ, 0 < Cᵣ ∧
    ∃ nᵣ : ℕ, 1 ≤ nᵣ ∧
      ∀ (φ : ℝ) (x z : Reg)
        (ws : Gate.PhaseProdWorkspace x z)
        (hworkspace :
          SignedRecursiveWorkspaceOK ops
            (ws.xExt.grow 1)
            (ws.zExt.grow 1)),
        let n := max (regSize x) (regSize z)
        nextSignedWidth (ws.xExt.grow 1) (ws.zExt.grow 1) ops
          < phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1) →
        nᵣ ≤ n →
        (signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ
          (ws.xExt.grow 1) (ws.zExt.grow 1) hworkspace : ℝ)
          ≤ Cᵣ * Real.rpow n (phaseProductExponent k) := by
  rcases hoverhead with ⟨A, B, hAB⟩
  rcases hgrowth with ⟨c, hc⟩

  let s : ℕ := c + 1

  let K : ℝ :=
    Real.rpow ((s + 1 : ℕ) : ℝ)
      (phaseProductExponent k)

  let L : ℝ :=
    (A : ℝ) * ((s + 1 : ℕ) : ℝ) + (B : ℝ)

  let Cᵣ : ℝ :=
    1 + L + (q k  : ℝ) * C * K

  have hKpos : 0 < K := by
    dsimp [K]
    positivity

  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    positivity

  have hCᵣ : 0 < Cᵣ := by
    dsimp [Cᵣ]
    have hq : 0 ≤ (q k  : ℝ) := by positivity
    have hterm :
        0 ≤ (q k  : ℝ) * C * K := by
      positivity
    linarith

  refine ⟨Cᵣ, hCᵣ, 1, by omega, ?_⟩

  intro φ x z ws hworkspace
  dsimp only
  intro hrec hn

  let ux : ExtReg := ws.xExt.grow 1
  let uz : ExtReg := ws.zExt.grow 1
  let n : ℕ := max (regSize x) (regSize z)
  let W : ℕ := nextSignedWidth ux uz ops

  have hn' : 1 ≤ n := by
    simpa [n] using hn

  have hinput :
      phaseInputSize ux uz = n + 1 := by
    simp [ux, uz, n]

  have hrec' :
      W < phaseInputSize ux uz := by
    simpa [W, ux, uz] using hrec

  have hW :
      W ≤ n + s := by
    have hg := hc ux uz
    rw [hinput] at hg
    dsimp [s]
    omega

  have hnPow :
      (n : ℝ)
        ≤
      Real.rpow (n : ℝ) (phaseProductExponent k) :=
    natCast_le_phaseProduct_rpow k hk hn'

  have hsafe :
      phaseProductSafeRate k W
        ≤
      K * Real.rpow (n : ℝ) (phaseProductExponent k) := by
    simpa [K] using
      phaseProductSafeRate_le_scaled_rpow
        k hk hn' hW

  have hWscaleNat :
      W ≤ (s + 1) * n := by
    exact hW.trans (by
      have hs_mul :
          s ≤ s * n := by
        simpa using Nat.mul_le_mul_left s hn'
      calc
        n + s ≤ n + s * n :=
          Nat.add_le_add_left hs_mul n
        _ = (s + 1) * n := by
          simp [Nat.add_mul, Nat.add_comm])

  have hWscale :
      (W : ℝ)
        ≤
      ((s + 1 : ℕ) : ℝ) * (n : ℝ) := by
    exact_mod_cast hWscaleNat

  have hoverheadR :
      (phaseProgramOverhead W ops : ℝ)
        ≤
      (A : ℝ) * (W : ℝ) + (B : ℝ) := by
    exact_mod_cast hAB W

  have hAW :
      (A : ℝ) * (W : ℝ)
        ≤
      (A : ℝ) * (((s + 1 : ℕ) : ℝ) * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left
      hWscale
      (by positivity)

  have hnR :
      (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn'

  have hB :
      (B : ℝ) ≤ (B : ℝ) * (n : ℝ) := by
    have :=
      mul_le_mul_of_nonneg_left
        hnR
        (show 0 ≤ (B : ℝ) by positivity)
    simpa using this

  have hoverheadLinear :
      (phaseProgramOverhead W ops : ℝ)
        ≤
      L * (n : ℝ) := by
    calc
      (phaseProgramOverhead W ops : ℝ)
          ≤
        (A : ℝ) * (W : ℝ) + (B : ℝ) :=
        hoverheadR
      _ ≤
        (A : ℝ) *
            (((s + 1 : ℕ) : ℝ) * (n : ℝ)) +
          (B : ℝ) :=
        by nlinarith [hAW]
      _ ≤
        (A : ℝ) *
            (((s + 1 : ℕ) : ℝ) * (n : ℝ)) +
          (B : ℝ) * (n : ℝ) :=
        by nlinarith [hB]
      _ = L * (n : ℝ) := by
        dsimp [L]
        ring

  have hoverheadPow :
      (phaseProgramOverhead W ops : ℝ)
        ≤
      L * Real.rpow (n : ℝ) (phaseProductExponent k) :=
    hoverheadLinear.trans
      (mul_le_mul_of_nonneg_left hnPow hLnonneg)

  have hchildren :
      ∀ (ψ : ℝ) (a b : ExtReg)
        (hw : SignedRecursiveWorkspaceOK ops a b),
        ExtReg.width a = W →
        ExtReg.width b = W →
        (signedPhaseProductGateCount
            (Basis := Basis) k hk ops ψ a b hw : ℝ)
          ≤
        C * phaseProductSafeRate k W := by
    intro ψ a b hw ha hb
    have hbnd := hbalanced ψ a b hw (ha.trans hb.symm)
    simpa [ha] using hbnd

  have hone :=
    lowerSignedPhaseProd_one_level_cost_le
      (Basis := Basis)
      k hk ops φ ux uz
      hworkspace
      hrec'
      (C * phaseProductSafeRate k W)
      hchildren

  have hone' :
      (signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ ux uz hworkspace : ℝ)
        ≤
      (phaseProgramOverhead W ops : ℝ) +
        (q k  : ℝ) * (C * phaseProductSafeRate k W) := by
    simpa [W, hcount] using hone

  have hqC :
      0 ≤ (q k  : ℝ) * C := by
    positivity

  have hrecursiveTerm :
      (q k  : ℝ) * (C * phaseProductSafeRate k W)
        ≤
      ((q k  : ℝ) * C * K) *
        Real.rpow (n : ℝ) (phaseProductExponent k) := by
    calc
      (q k  : ℝ) * (C * phaseProductSafeRate k W)
          =
        ((q k  : ℝ) * C) * phaseProductSafeRate k W := by
        ring
      _ ≤
        ((q k  : ℝ) * C) *
          (K * Real.rpow (n : ℝ) (phaseProductExponent k)) :=
        mul_le_mul_of_nonneg_left hsafe hqC
      _ =
        ((q k  : ℝ) * C * K) *
          Real.rpow (n : ℝ) (phaseProductExponent k) := by
        ring

  have hpowNonneg :
      0 ≤ Real.rpow (n : ℝ) (phaseProductExponent k) :=
    Real.rpow_nonneg (by positivity) _

  change
    (signedPhaseProductGateCount
      (Basis := Basis) k hk ops φ ux uz hworkspace : ℝ)
      ≤
    Cᵣ * Real.rpow (n : ℝ) (phaseProductExponent k)

  calc
    (signedPhaseProductGateCount
        (Basis := Basis) k hk ops φ ux uz hworkspace : ℝ)
        ≤
      (phaseProgramOverhead W ops : ℝ) +
        (q k  : ℝ) * (C * phaseProductSafeRate k W) :=
      hone'
    _ ≤
      L * Real.rpow (n : ℝ) (phaseProductExponent k) +
        ((q k  : ℝ) * C * K) *
          Real.rpow (n : ℝ) (phaseProductExponent k) :=
      add_le_add hoverheadPow hrecursiveTerm
    _ =
      (L + (q k  : ℝ) * C * K) *
        Real.rpow (n : ℝ) (phaseProductExponent k) := by
      ring
    _ ≤
      Cᵣ * Real.rpow (n : ℝ) (phaseProductExponent k) := by
      apply mul_le_mul_of_nonneg_right _ hpowNonneg
      dsimp [Cᵣ]
      linarith

/-- Bounds the public unsigned theorem's nonrecursive branch: the direct
quadratic base case becomes linear because the smaller operand is bounded. -/
lemma signedPhaseProductGateCount_unsignedView_no_recurse_case_bound
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hnarrow :
      ∃ d : ℕ, ∀ x z : ExtReg,
        ¬ nextSignedWidth x z ops < phaseInputSize x z →
        min (ExtReg.width x) (ExtReg.width z) ≤ d) :
    ∃ Cₙ : ℝ, 0 < Cₙ ∧
    ∃ nₙ : ℕ, 1 ≤ nₙ ∧
      ∀ (φ : ℝ) (x z : Reg)
        (ws : Gate.PhaseProdWorkspace x z)
        (hworkspace :
          SignedRecursiveWorkspaceOK ops
            (ws.xExt.grow 1)
            (ws.zExt.grow 1)),
        let n := max (regSize x) (regSize z)
        ¬ nextSignedWidth (ws.xExt.grow 1) (ws.zExt.grow 1) ops
          < phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1) →
        nₙ ≤ n →
        (signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ
          (ws.xExt.grow 1) (ws.zExt.grow 1) hworkspace : ℝ)
          ≤ Cₙ * Real.rpow n (phaseProductExponent k) := by
  rcases hnarrow with ⟨d, hd⟩

  refine ⟨2 * (d : ℝ) + 1, by positivity, 1, by omega, ?_⟩

  intro φ x z ws hworkspace
  dsimp only
  intro hno hn

  let ux : ExtReg := ws.xExt.grow 1
  let uz : ExtReg := ws.zExt.grow 1
  let n : ℕ := max (regSize x) (regSize z)

  have hn' : 1 ≤ n := by
    simpa [n] using hn

  have hno' :
      ¬ nextSignedWidth ux uz ops < phaseInputSize ux uz := by
    simpa [ux, uz] using hno

  have hsmall :
      min (regSize x + 1) (regSize z + 1) ≤ d := by
    simpa [ux, uz] using hd ux uz hno'

  have hprod :
      (regSize x + 1) * (regSize z + 1)
        ≤
      2 * d * n := by
    by_cases hxz : regSize x ≤ regSize z
    · have hnEq : n = regSize z := by
        simp [n, max_eq_right hxz]

      have hxz' :
          regSize x + 1 ≤ regSize z + 1 :=
        Nat.add_le_add_right hxz 1

      have hxsmall :
          regSize x + 1 ≤ d := by
        simpa [min_eq_left hxz'] using hsmall

      have hzpos : 1 ≤ regSize z := by
        simpa [hnEq] using hn'

      have hzdouble :
          regSize z + 1 ≤ 2 * regSize z := by
        omega

      calc
        (regSize x + 1) * (regSize z + 1)
            ≤
          d * (regSize z + 1) :=
          Nat.mul_le_mul hxsmall (le_refl _)
        _ ≤
          d * (2 * regSize z) :=
          Nat.mul_le_mul_left d hzdouble
        _ = 2 * d * n := by
          rw [hnEq]
          ring

    · have hzx : regSize z ≤ regSize x :=
        Nat.le_of_lt (Nat.lt_of_not_ge hxz)

      have hnEq : n = regSize x := by
        simp [n, max_eq_left hzx]

      have hzx' :
          regSize z + 1 ≤ regSize x + 1 :=
        Nat.add_le_add_right hzx 1

      have hzsmall :
          regSize z + 1 ≤ d := by
        simpa [min_eq_right hzx'] using hsmall

      have hxpos : 1 ≤ regSize x := by
        simpa [hnEq] using hn'

      have hxdouble :
          regSize x + 1 ≤ 2 * regSize x := by
        omega

      calc
        (regSize x + 1) * (regSize z + 1)
            =
          (regSize z + 1) * (regSize x + 1) := by
          ac_rfl
        _ ≤
          d * (regSize x + 1) :=
          Nat.mul_le_mul hzsmall (le_refl _)
        _ ≤
          d * (2 * regSize x) :=
          Nat.mul_le_mul_left d hxdouble
        _ = 2 * d * n := by
          rw [hnEq]
          ring

  have hdirect :
      signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ ux uz hworkspace
        =
      (regSize x + 1) * (regSize z + 1) := by
    calc
      signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ ux uz hworkspace
          =
        ExtReg.width ux * ExtReg.width uz :=
        signedPhaseProductGateCount_eq_direct_of_not_recurse
          (Basis := Basis)
          k hk ops φ ux uz hworkspace hno'
      _ =
        (regSize x + 1) * (regSize z + 1) := by
        simp only [ux, uz, width_phaseProdUsing_x, width_phaseProdUsing_z]

  have hlinear :
      (signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ ux uz hworkspace : ℝ)
        ≤
      (2 * (d : ℝ)) * (n : ℝ) := by
    rw [hdirect]
    exact_mod_cast hprod

  have hnPow :
      (n : ℝ)
        ≤
      Real.rpow (n : ℝ) (phaseProductExponent k) :=
    natCast_le_phaseProduct_rpow k hk hn'

  have hlinearPow :
      (2 * (d : ℝ)) * (n : ℝ)
        ≤
      (2 * (d : ℝ)) *
        Real.rpow (n : ℝ) (phaseProductExponent k) :=
    mul_le_mul_of_nonneg_left hnPow (by positivity)

  have hpowNonneg :
      0 ≤ Real.rpow (n : ℝ) (phaseProductExponent k) :=
    Real.rpow_nonneg (by positivity) _

  change
    (signedPhaseProductGateCount
      (Basis := Basis) k hk ops φ ux uz hworkspace : ℝ)
      ≤
    (2 * (d : ℝ) + 1) *
      Real.rpow (n : ℝ) (phaseProductExponent k)

  calc
    (signedPhaseProductGateCount
        (Basis := Basis) k hk ops φ ux uz hworkspace : ℝ)
        ≤
      (2 * (d : ℝ)) * (n : ℝ) :=
      hlinear
    _ ≤
      (2 * (d : ℝ)) *
        Real.rpow (n : ℝ) (phaseProductExponent k) :=
      hlinearPow
    _ ≤
      (2 * (d : ℝ) + 1) *
        Real.rpow (n : ℝ) (phaseProductExponent k) := by
      apply mul_le_mul_of_nonneg_right _ hpowNonneg
      linarith



end BalancedSignedSolution

/-! ---------------------------------------------------------
    Unsigned and generated-program bounds

This section bridges the balanced signed theorem to public unsigned PhaseProduct
gates and proves the generated-program width hypotheses consumed by `Main.lean`.
--------------------------------------------------------- -/

section UnsignedReductionLemmas

/-- Combines the recursive and nonrecursive unsigned-view estimates to obtain
the public unsigned PhaseProduct bound from the balanced signed bound. -/
lemma phaseProductGateCountBound_of_balanced_signed_bound
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hcount :
      phaseProductCount ops = q k )
    (hoverhead :
      ∃ A B : ℕ, ∀ W : ℕ,
        phaseProgramOverhead W ops ≤ A * W + B)
    (hgrowth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        nextSignedWidth x z ops ≤ phaseInputSize x z + c)
    (hnarrow :
      ∃ d : ℕ, ∀ x z : ExtReg,
        ¬ nextSignedWidth x z ops < phaseInputSize x z →
        min (ExtReg.width x) (ExtReg.width z) ≤ d)
    (C : ℝ)
    (hC : 0 < C)
    (hbalanced :
      BalancedSignedPhaseProductBound
        (Basis := Basis) k hk ops C) :
    PhaseProductGateCountBound
      (Basis := Basis) k hk ops := by
  rcases
    signedPhaseProductGateCount_unsignedView_recurse_case_bound
      (Basis := Basis) k hk ops hcount hoverhead hgrowth C hC hbalanced
    with ⟨Cᵣ, hCᵣ, nᵣ, hnᵣ, hrecurse⟩
  rcases
    signedPhaseProductGateCount_unsignedView_no_recurse_case_bound
      (Basis := Basis) k hk ops hnarrow
    with ⟨Cₙ, hCₙ, nₙ, hnₙ, hnoRecurse⟩

  refine ⟨Cᵣ + Cₙ, by linarith, max nᵣ nₙ, ?_, ?_⟩
  · exact le_trans hnᵣ (Nat.le_max_left nᵣ nₙ)
  · intro φ x z ws hworkspace
    dsimp
    intro hnLarge
    let hsigned :
        SignedRecursiveWorkspaceOK ops
          (ws.xExt.grow 1)
          (ws.zExt.grow 1) :=
      phaseProdUsing_signedWorkspace
        ops φ x z ws hworkspace
    let n := max (regSize x) (regSize z)
    have hnᵣ_le : nᵣ ≤ n := by
      exact le_trans (Nat.le_max_left nᵣ nₙ) hnLarge
    have hnₙ_le : nₙ ≤ n := by
      exact le_trans (Nat.le_max_right nᵣ nₙ) hnLarge
    have hn_pos_nat : 0 < n := by
      exact lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hnᵣ) hnᵣ_le
    have hrate_nonneg :
        0 ≤ Real.rpow (n : ℝ) (phaseProductExponent k) := by
      exact le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hn_pos_nat) _)

    rw [lowerGate_PhaseProdUsing_gateCount_eq_signed
      (Basis := Basis) k hk ops φ x z ws hworkspace]

    by_cases hrec :
      nextSignedWidth (ws.xExt.grow 1) (ws.zExt.grow 1) ops
        < phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1)
    · have hb :=
        hrecurse φ x z ws hsigned hrec hnᵣ_le
      dsimp [n] at hb ⊢
      nlinarith [hb, hrate_nonneg, le_of_lt hCₙ]
    · have hb :=
        hnoRecurse φ x z ws hsigned hrec hnₙ_le
      dsimp [n] at hb ⊢
      nlinarith [hb, hrate_nonneg, le_of_lt hCᵣ]



/-- Supplies the balanced child-width shrinkage hypothesis for an arbitrary fixed program. -/
lemma prog_balanced_nextSignedWidth
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    ∃ c : ℕ, ∀ x z : ExtReg,
      ExtReg.width x = ExtReg.width z →
      nextSignedWidth x z ops
        ≤
      (ExtReg.width x + k - 1) / k + c := by
  let hk0 : 0 < k := by omega
  let c : ℕ := phaseProgramWidthGrowth ops + 1

  refine ⟨c + (k - 1), ?_⟩
  intro x z hbalanced

  let n := ExtReg.width x

  have hsize :
      phaseInputSize x z = n := by
    simp [phaseInputSize, n, hbalanced]

  have hlimb :
      phaseLimbWidth x z k = n / k := by
    simp [phaseLimbWidth, phaseLimbWidthOfWidth, n, hbalanced]

  have htop :
      nextSignedWidth x z ops
        ≤
      phaseInputSize x z
        - (k - 1) * phaseLimbWidth x z k
        + c := by
    simpa [c] using
      nextSignedWidth_le_topHeavy_add_growth
        hk0 ops x z

  have hceil :
      n - (k - 1) * (n / k)
        ≤
      (n + k - 1) / k + (k - 1) := by
    let d := n / k

    have hdiv :
        k * d ≤ n := by
      simpa [d] using Nat.mul_div_le n k

    have hrem :
        n % k = n - k * d := by
      simpa [d] using
        (Nat.mod_eq_sub_mul_div :
          n % k = n - k * (n / k))

    have hsplit :
        n - (k - 1) * d = n % k + d := by
      simp[hrem]
      simp[Nat.sub_mul];
      have hd_le_kd : d ≤ k * d := by
        nlinarith [hk0, Nat.zero_le d]
      rw [Nat.sub_sub_right n hd_le_kd]
      rw [Nat.sub_add_comm hdiv]



    have hmod :
        n % k ≤ k - 1 := by
      have hlt := Nat.mod_lt n hk0
      omega

    have hdceil :
        d ≤ (n + k - 1) / k := by
      apply Nat.div_le_div_right
      omega

    rw [show n / k = d by rfl, hsplit]
    omega

  calc
    nextSignedWidth x z ops
        ≤
      phaseInputSize x z
        - (k - 1) * phaseLimbWidth x z k
        + c :=
      htop
    _ =
      n - (k - 1) * (n / k) + c := by
      rw [hsize, hlimb]
    _ ≤
      (n + k - 1) / k + (c + (k - 1)) := by
      omega


/-- Supplies the input-plus-constant child-width bound for an arbitrary fixed program. -/
lemma prog_nextSignedWidth_le_input_add_const
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    ∃ c : ℕ, ∀ x z : ExtReg,
      nextSignedWidth x z ops
        ≤ phaseInputSize x z + c := by
  let hk0 : 0 < k := by omega

  exact ⟨phaseProgramWidthGrowth ops + 1, fun x z =>
    (nextSignedWidth_le_topHeavy_add_growth hk0 ops x z).trans <|
      Nat.add_le_add_right
        (Nat.sub_le (phaseInputSize x z) ((k - 1) * phaseLimbWidth x z k))
        (phaseProgramWidthGrowth ops + 1)⟩


/-- Supplies the small-operand nonrecursion hypothesis for an arbitrary fixed program. -/
lemma prog_no_recurse_implies_small_operand
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    ∃ d : ℕ, ∀ x z : ExtReg,
      (¬ nextSignedWidth x z ops < phaseInputSize x z) →
      min (ExtReg.width x) (ExtReg.width z) ≤ d := by
  let hk0 : 0 < k := by omega
  let c : ℕ := phaseProgramWidthGrowth ops + 1

  refine ⟨k * c + k, ?_⟩
  intro x z hnot

  let n := phaseInputSize x z
  let m := min (ExtReg.width x) (ExtReg.width z)
  let W := phaseLimbWidth x z k

  have hn_le_next :
      n ≤ nextSignedWidth x z ops := by
    exact Nat.le_of_not_gt hnot

  have hnext :
      nextSignedWidth x z ops
        ≤ n - (k - 1) * W + c := by
    simpa [n, W, c] using
      nextSignedWidth_le_topHeavy_add_growth
        hk0 ops x z

  have hn_le :
      n ≤ n - (k - 1) * W + c :=
    hn_le_next.trans hnext

  have hW :
      W = m / k := by
    unfold W m phaseLimbWidth phaseLimbWidthOfWidth
    by_cases hxz : ExtReg.width x ≤ ExtReg.width z
    · have hdiv :
          ExtReg.width x / k ≤ ExtReg.width z / k :=
        Nat.div_le_div_right hxz
      simp [Nat.min_eq_left hxz, Nat.min_eq_left hdiv]
    · have hzx :
          ExtReg.width z ≤ ExtReg.width x :=
        le_of_not_ge hxz
      have hdiv :
          ExtReg.width z / k ≤ ExtReg.width x / k :=
        Nat.div_le_div_right hzx
      simp [Nat.min_eq_right hzx, Nat.min_eq_right hdiv]

  by_cases hremove : (k - 1) * W ≤ n
  · have hremove_le_c :
        (k - 1) * W ≤ c := by
      omega

    have hW_le_c : W ≤ c := by
      have hkpred : 1 ≤ k - 1 := by omega
      nlinarith [hremove_le_c, hkpred, Nat.zero_le W]

    have hmod :
        m % k ≤ k - 1 := by
      have hlt := Nat.mod_lt m hk0
      omega

    have hsplit :
        m = k * (m / k) + m % k := by
      simpa [Nat.add_comm] using
        (Nat.mod_add_div m k).symm

    change m ≤ k * c + k
    rw [hW] at hW_le_c

    calc
      m = k * (m / k) + m % k := hsplit
      _ ≤ k * c + (k - 1) :=
        Nat.add_le_add
          (Nat.mul_le_mul_left k hW_le_c)
          hmod
      _ ≤ k * c + k := by omega

  · have hn_le_c : n ≤ c := by
      omega

    have hm_le_n : m ≤ n := by
      simp [m, n, phaseInputSize]

    change m ≤ k * c + k
    exact hm_le_n.trans
      (hn_le_c.trans (by
        nlinarith [Nat.zero_le k, Nat.zero_le c]))



end UnsignedReductionLemmas

/-! ---------------------------------------------------------
    Controlled PhaseProduct

This namespace contains the comparison between controlled and uncontrolled
signed PhaseProduct lowering.  The main controlled asymptotic theorem is kept in
`PhaseProduct.Main`; this file proves the reusable five-times-cost lemmas.
--------------------------------------------------------- -/

namespace CPhaseProductReduction

/-- The controlled compiled body costs at most five times the corresponding uncontrolled signed body. -/
lemma lgc_cbody_le_five
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (W : ℕ)
    (ctrl : ℕ)
    (st : LayoutState k)
    (coeff : Fin (q k) → ℚ)
    (φ : ℝ)
    (recurseC :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan k hk pts hpts ops W
          (Gate.CSignedPhaseProd
            ctrl theta (st.xslot i) (st.zslot i)))
    (recurseS :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan k hk pts hpts ops W
          (Gate.SignedPhaseProd
            theta (st.xslot i) (st.zslot i)))
    (hchild :
      ∀ (i : Fin k) (theta : ℝ),
        LowGate.gateCount shorGateCostModel
            (lowerGateRec (recurseC i theta))
          ≤
        5 *
          LowGate.gateCount shorGateCostModel
            (lowerGateRec (recurseS i theta)))
    (n : ℕ)
    (l : List (valid_ops k)) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (planCompileAnnotatedOpsToCSignedGateAux
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops)
            W ctrl φ coeff st recurseC
            (annotatePhaseTermsAux k n l)))
      ≤
    5 *
      LowGate.gateCount shorGateCostModel
        (lowerGateRec
          (planCompileAnnotatedOpsToSignedGateAux
            (k := k) (hk := hk) (pts := pts) (hpts := hpts)
            (ops := ops)
            W φ coeff st recurseS
            (annotatePhaseTermsAux k n l))) := by
  induction l generalizing n with
  | nil =>
      simp [
        annotatePhaseTermsAux,
        planCompileAnnotatedOpsToCSignedGateAux,
        planCompileAnnotatedOpsToSignedGateAux,
        lowerGateRec,
        LowGate.gateCount
      ]
  | cons op rest ih =>
      cases op with
      | shiftL i m =>
          have ht := ih n
          simpa [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToCSignedGateAux,
            planCompileAnnotatedOpsToSignedGateAux,
            lowerGateRec,
            LowGate.gateCount,
            shorGateCostModel,
            phaseProductCostModel
          ] using ht
      | shiftR i m =>
          have ht := ih n
          simpa [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToCSignedGateAux,
            planCompileAnnotatedOpsToSignedGateAux,
            lowerGateRec,
            LowGate.gateCount,
            shorGateCostModel,
            phaseProductCostModel
          ] using ht
      | negate i =>
          have ht := ih n
          simp [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToCSignedGateAux,
            planCompileAnnotatedOpsToSignedGateAux,
            lowerGateRec,
            LowGate.gateCount
          ] at ht ⊢
          omega
      | addScaled dst src negSrc shift =>
          have ht := ih n
          simp [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToCSignedGateAux,
            planCompileAnnotatedOpsToSignedGateAux,
            lowerGateRec,
            LowGate.gateCount
          ] at ht ⊢
          omega
      | phaseProduct i =>
          classical
          by_cases hn : n < q k
          · have hc :=
              hchild i
                (φ * (((coeff ⟨n, hn⟩ : ℚ) : ℝ)))
            have ht := ih (n + 1)
            have hann :
                annotatePhaseTermsAux
                    k n (valid_ops.phaseProduct i :: rest)
                  =
                ⟨valid_ops.phaseProduct i, some ⟨n, hn⟩⟩
                  ::
                annotatePhaseTermsAux k (n + 1) rest := by
              simp [annotatePhaseTermsAux, hn]
            rw [hann]
            change
              LowGate.gateCount shorGateCostModel
                    (lowerGateRec
                      (recurseC i
                        (φ * (((coeff ⟨n, hn⟩ : ℚ) : ℝ))))
                    )
                +
                LowGate.gateCount shorGateCostModel
                    (lowerGateRec
                      (planCompileAnnotatedOpsToCSignedGateAux
                        W ctrl φ coeff st recurseC
                        (annotatePhaseTermsAux k (n + 1) rest)))
              ≤
              5 *
                (LowGate.gateCount shorGateCostModel
                      (lowerGateRec
                        (recurseS i
                          (φ * (((coeff ⟨n, hn⟩ : ℚ) : ℝ))))
                      )
                  +
                  LowGate.gateCount shorGateCostModel
                      (lowerGateRec
                        (planCompileAnnotatedOpsToSignedGateAux
                          W φ coeff st recurseS
                          (annotatePhaseTermsAux k (n + 1) rest))))
            omega
          · have ht := ih (n + 1)
            have hann :
                annotatePhaseTermsAux
                    k n (valid_ops.phaseProduct i :: rest)
                  =
                ⟨valid_ops.phaseProduct i, none⟩
                  ::
                annotatePhaseTermsAux k (n + 1) rest := by
              simp [annotatePhaseTermsAux, hn]
            rw [hann]
            change
              LowGate.gateCount shorGateCostModel
                  (lowerGateRec
                    (planCompileAnnotatedOpsToCSignedGateAux
                      W ctrl φ coeff st recurseC
                      (annotatePhaseTermsAux k (n + 1) rest)))
                ≤
              5 *
                LowGate.gateCount shorGateCostModel
                  (lowerGateRec
                    (planCompileAnnotatedOpsToSignedGateAux
                      W φ coeff st recurseS
                      (annotatePhaseTermsAux k (n + 1) rest)))
            exact ht

/-- Controlled signed PhaseProduct lowering costs at most five times signed PhaseProduct lowering. -/
lemma cSignedPhaseProductGateCount_le_five_signed
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (ctrl : ℕ)
    (φ : ℝ)
    (x z : ExtReg)
    (hworkspace :
      CSignedRecursiveWorkspaceOK ops ctrl x z) :
    cSignedPhaseProductGateCount
        (Basis := Basis)
        k hk ops ctrl φ x z hworkspace
      ≤
    5 *
      signedPhaseProductGateCount
        (Basis := Basis)
        k hk ops φ x z
        hworkspace.toSignedRecursiveWorkspaceOK := by
  by_cases hrec :
      nextSignedWidth x z ops <
        phaseInputSize x z
  · let step : CanonicalSignedStep ops x z :=
      canonicalSignedStep
        hk ops x z hrec
        hworkspace.toSignedRecursiveWorkspaceOK
    let src : LayoutState k :=
      initSignedLayoutState step.layout
    let dst : LayoutState k :=
      targetSignedLayoutState
        src
        (scanNeededWidths x z ops)
    have hctrlLayout :
        step.layout.ControlDisjoint ctrl :=
      step.layout.controlDisjoint_of_ctrlDisjoint
        hworkspace.control_disjoint
    have hctrlDst :
        (∀ i, ctrl ∉ (dst.xslot i).ownedQubits) ∧
        (∀ i, ctrl ∉ (dst.zslot i).ownedQubits) := by
      simpa [src, dst] using
        controlDisjoint_target
          step.layout ctrl
          (scanNeededWidths x z ops)
          hctrlLayout
    let signedChildWorkspace :
        ∀ i : Fin k,
          SignedRecursiveWorkspaceOK
            ops (dst.xslot i) (dst.zslot i) :=
      fun i => by
        simpa [src, dst] using step.childWorkspace i
    let controlledChildWorkspace :
        ∀ i : Fin k,
          CSignedRecursiveWorkspaceOK
            ops ctrl (dst.xslot i) (dst.zslot i) :=
      fun i =>
        {
          toSignedRecursiveWorkspaceOK :=
            signedChildWorkspace i
          control_disjoint :=
            ⟨hctrlDst.1 i, hctrlDst.2 i⟩
        }
    have childSize (i : Fin k) :
        phaseInputSize (dst.xslot i) (dst.zslot i) =
          nextSignedWidth x z ops := by
      simpa [src, dst] using step.childInputSize i
    let recurseC :
        ∀ (i : Fin k) (theta : ℝ),
          PhaseLoweringPlan
            k hk
            (genInterpolationPoints k)
            (generatedInterpolationPoints_length k)
            ops
            (nextSignedWidth x z ops)
            (Gate.CSignedPhaseProd
              ctrl theta (dst.xslot i) (dst.zslot i)) :=
      fun i theta => by
        have hsize := childSize i
        simpa [hsize] using
          standardCSignedPhaseLoweringPlan
            k hk ctrl theta
            (dst.xslot i) (dst.zslot i)
            ops (controlledChildWorkspace i)
    let recurseS :
        ∀ (i : Fin k) (theta : ℝ),
          PhaseLoweringPlan
            k hk
            (genInterpolationPoints k)
            (generatedInterpolationPoints_length k)
            ops
            (nextSignedWidth x z ops)
            (Gate.SignedPhaseProd
              theta (dst.xslot i) (dst.zslot i)) :=
      fun i theta => by
        have hsize := childSize i
        simpa [hsize] using
          standardSignedPhaseLoweringPlan
            k hk theta
            (dst.xslot i) (dst.zslot i)
            ops (signedChildWorkspace i)
    have hchild :
        ∀ (i : Fin k) (theta : ℝ),
          LowGate.gateCount shorGateCostModel
              (lowerGateRec (recurseC i theta))
            ≤
          5 *
            LowGate.gateCount shorGateCostModel
              (lowerGateRec (recurseS i theta)) := by
      intro i theta
      have htransportC :
          lowerGateRec (recurseC i theta) =
            lowerGateRec
              (standardCSignedPhaseLoweringPlan
                k hk ctrl theta
                (dst.xslot i) (dst.zslot i)
                ops (controlledChildWorkspace i)) := by
        dsimp [recurseC]
        exact
          lowerGateRec_cast_initSize_of_eq
            (k := k)
            (hk := hk)
            (pts := genInterpolationPoints k)
            (hpts := generatedInterpolationPoints_length k)
            (ops := ops)
            (childSize i)
            (standardCSignedPhaseLoweringPlan
              k hk ctrl theta
              (dst.xslot i) (dst.zslot i)
              ops (controlledChildWorkspace i))
      have htransportS :
          lowerGateRec (recurseS i theta) =
            lowerGateRec
              (standardSignedPhaseLoweringPlan
                k hk theta
                (dst.xslot i) (dst.zslot i)
                ops (signedChildWorkspace i)) := by
        dsimp [recurseS]
        exact
          lowerGateRec_cast_initSize_of_eq
            (k := k)
            (hk := hk)
            (pts := genInterpolationPoints k)
            (hpts := generatedInterpolationPoints_length k)
            (ops := ops)
            (childSize i)
            (standardSignedPhaseLoweringPlan
              k hk theta
              (dst.xslot i) (dst.zslot i)
              ops (signedChildWorkspace i))
      rw [htransportC, htransportS]
      simpa [
        cSignedPhaseProductGateCount,
        signedPhaseProductGateCount,
        lowerCSignedPhaseProdWithWorkspace,
        lowerSignedPhaseProdWithWorkspace,
        lowerCSignedPhaseProd,
        lowerSignedPhaseProd
      ] using
        cSignedPhaseProductGateCount_le_five_signed
          (Basis := Basis)
          k hk ops ctrl theta
          (dst.xslot i) (dst.zslot i)
          (controlledChildWorkspace i)
    have hpts :
        (genInterpolationPoints k).length = q k :=
      generatedInterpolationPoints_length k
    unfold cSignedPhaseProductGateCount signedPhaseProductGateCount
      lowerCSignedPhaseProdWithWorkspace
      lowerSignedPhaseProdWithWorkspace
      lowerCSignedPhaseProd
      lowerSignedPhaseProd
    unfold
      standardCSignedPhaseLoweringPlan
      standardSignedPhaseLoweringPlan
    simp only [hrec, ↓reduceDIte]
    simp only [
      PhaseLoweringPlan.lowerGateRec_cSignedStep,
      PhaseLoweringPlan.lowerGateRec_signedStep
    ]
    change
      LowGate.gateCount shorGateCostModel
          (lowerGateRec
            (planCompiledCSignedPhaseGate
              hk (genInterpolationPoints k) hpts
              ops ctrl φ x z step.layout
              (by simpa [src, dst] using recurseC)))
        ≤
      5 *
        LowGate.gateCount shorGateCostModel
          (lowerGateRec
            (planCompiledSignedPhaseGate
              hk (genInterpolationPoints k) hpts
              ops φ x z step.layout
              (by simpa [src, dst] using recurseS)))
    unfold
      planCompiledCSignedPhaseGate
      planCompiledSignedPhaseGate
    dsimp only
    rw [
      lowerGateRec_mpr_gate_of_eq
        (k := k)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts := hpts)
        (ops := ops)
        (hUV := by
          simp [
            compiledCSignedPhaseGate,
            compileOpsToCSignedGate,
            compileOpsToSignedGate,
            controlPhaseLeaves,
            controlPhaseLeaves_compileSignedAllocations,
            controlPhaseLeaves_compileSignedDeallocations
          ])
    ]
    simp only [
      id_eq,
      lgc_seq,
      lgc_allocs,
      lgc_deallocs,
      Nat.zero_add,
      Nat.add_zero
    ]
    exact
      lgc_cbody_le_five
        (nextSignedWidth x z ops)
        ctrl
        dst
        (loweringPhaseCoeff
          k x z
          (genInterpolationPoints k)
          hpts)
        φ
        recurseC
        recurseS
        hchild
        0
        ops
  · unfold
      cSignedPhaseProductGateCount
      signedPhaseProductGateCount
      lowerCSignedPhaseProdWithWorkspace
      lowerSignedPhaseProdWithWorkspace
      lowerCSignedPhaseProd
      lowerSignedPhaseProd
    unfold
      standardCSignedPhaseLoweringPlan
      standardSignedPhaseLoweringPlan
    simp only [
      hrec,
      ↓reduceDIte,
      lowerGateRec,
      LowGate.gateCount,
      shorGateCostModel,
      phaseProductCostModel,
      directCSignedPhaseProductGateCount,
      directSignedPhaseProductGateCount
    ]
    simp [Nat.mul_assoc]
termination_by phaseInputSize x z
decreasing_by
  calc
    phaseInputSize (dst.xslot i) (dst.zslot i)
        =
      nextSignedWidth x z ops := by
        simpa [src, dst] using step.childInputSize i
    _ < phaseInputSize x z := hrec

/-- The controlled namespace reuses the unsigned workspace extraction for its public bridge theorem. -/
lemma phaseProdUsing_signedWorkspace
    (ops : Prog k)
    (φ : ℝ)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (hworkspace :
      GateWorkspaceOK ops
        (Gate.PhaseProdUsing φ x z ws)) :
    SignedRecursiveWorkspaceOK ops
      (ws.xExt.grow 1)
      (ws.zExt.grow 1) := by
  simpa [GateWorkspaceOK, Gate.PhaseProdUsing] using hworkspace

/-- Extracts controlled signed recursive workspace from a public controlled PhaseProduct workspace proof. -/
lemma cPhaseProdUsing_controlledWorkspace
    (ops : Prog k)
    (ctrl : ℕ)
    (φ : ℝ)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (hworkspace :
      GateWorkspaceOK ops
        (Gate.CPhaseProdUsing ctrl φ x z ws)) :
    CSignedRecursiveWorkspaceOK ops ctrl
      (ws.xExt.grow 1)
      (ws.zExt.grow 1) := by
  simpa [GateWorkspaceOK, Gate.CPhaseProdUsing] using hworkspace

/-- Identifies public controlled PhaseProduct lowering cost with controlled signed recursive cost. -/
lemma lowerGate_CPhaseProdUsing_gateCount_eq_cSigned
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (ctrl : ℕ)
    (φ : ℝ)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (hworkspace :
      GateWorkspaceOK ops
        (Gate.CPhaseProdUsing ctrl φ x z ws)) :
    LowGate.gateCount shorGateCostModel
        (lowerGate
          (Basis := Basis)
          k hk ops
          (Gate.CPhaseProdUsing ctrl φ x z ws)
          hworkspace)
      =
    cSignedPhaseProductGateCount
      (Basis := Basis)
      k hk ops ctrl φ
      (ws.xExt.grow 1)
      (ws.zExt.grow 1)
      (cPhaseProdUsing_controlledWorkspace
        ops ctrl φ x z ws hworkspace) := by
  simp [
    lowerGate,
    Gate.CPhaseProdUsing,
    cSignedPhaseProductGateCount,
    lowerCSignedPhaseProdWithWorkspace,
    LowGate.gateCount,
    shorGateCostModel,
    phaseProductCostModel
  ]


end CPhaseProductReduction

end Shor
