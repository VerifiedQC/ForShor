import FastMultiplication.ShorVerification.GateCount.QFT_GateCount

open Shor
open Filter

/-! =========================================================
    Complete Shor gate-count bound
========================================================= -/
/--
The per-modular-multiplication precision used in the Shor construction.

For fixed `δ > 0`, this is Θ(1 / n²).
-/
noncomputable def shorEta
    (δ : ℝ)
    (n : ℕ) : ℝ :=
  δ / (n : ℝ) ^ 2

/--
The size/layout assumptions used in the Shor gate-count theorem.

Here `n` is the width of the modulus/data register.
-/
def ShorGateCountLayout
    (cWork n : ℕ)
    (x y work : Reg)
    (flag : ℕ) : Prop :=
  regSize y = n ∧
  n ≤ regSize x ∧
  regSize x ≤ 2 * n ∧
  n ≤ regSize work ∧
  regSize work ≤ cWork * n ∧
  ModExpLayout x y work flag

/-- Gate count of the complete lowered approximate order-finding circuit. -/
noncomputable def shorOrderFindingGateCount
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (a N : ℕ)
    (x y work : Reg)
    (flag : ℕ) : ℕ :=
  LowGate.gateCount
    shorGateCostModel (orderFindingApproxLow qs k hk ops a N x y work flag)

/--
The complete Shor order-finding circuit has gate count

  O(n^(2 + ε)).

Here `n = regSize inst.y`, the precision is the concrete Shor schedule
`δ / n²`, and the workspace-growth factor used by the proof is derived
internally from that schedule.  The final constant may depend on `δ`, `k`,
and `ops`, but not on `n` or on the individual Shor instance.
-/
def ShorGateCountBound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (ε δ: ℝ)
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∃ n₀ : ℕ, 1 ≤ n₀ ∧

    ∀ (inst : ShorOrderFindingInstance) (work : Reg) (flag : ℕ) (b0 : qs.Basis),
      let n:= regSize inst.y
      n₀ ≤ n →
      ShorApproxSetup qs (shorEta δ (regSize inst.y)) inst.a inst.N inst.x inst.y work flag b0 →
      (shorOrderFindingGateCount qs k hk ops inst.a inst.N inst.x inst.y work flag : ℝ)
        ≤
      C * shorGateRate ε n

/-! =========================================================
    Elementary structural gate-count lemmas
========================================================= -/

/-!
This section contains small facts about the lowered syntax and register
locality.  They are used by the larger counting arguments but do not depend
on any asymptotic estimates.
-/

/-! ### Lowered structural identities -/

/--
Lowering `H_reg r` produces exactly one Hadamard for each qubit of `r`.
-/
lemma lowered_H_reg_gateCount
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : Reg) :
    LowGate.gateCount
        shorGateCostModel
        (lowerGate
          (Basis := qs.Basis)
          k hk ops
          (H_reg r))
      =
    regSize r := by
  have hfold :
      ∀ (l : List ℕ) (U : Gate),
        LowGate.gateCount
            shorGateCostModel
            (lowerGate
              (Basis := qs.Basis)
              k hk ops
              (l.foldl
                (fun acc q => Gate.seq (Gate.H q) acc)
                U))
          =
        l.length +
          LowGate.gateCount
            shorGateCostModel
            (lowerGate
              (Basis := qs.Basis)
              k hk ops
              U) := by
    intro l
    induction l with
    | nil =>
        intro U
        simp
    | cons q l ih =>
        intro U
        simp only [List.foldl_cons]
        rw [ih]
        simp [lowerGate, LowGate.gateCount]
        omega

  simpa [
    H_reg,
    regQubits,
    regSize,
    lowerGate,
    LowGate.gateCount
  ] using hfold (regQubits r) Gate.id

/-! ### Locality facts for extended registers -/

/--
Disjointness from the one-qubit extension implies disjointness from the
original data register.
-/
lemma disjoint_data_work_of_disjoint_extendHi
    (data work : Reg)
    (h : Shor.Disjoint (extendHi data) work) :
    Shor.Disjoint data work := by
  unfold Shor.Disjoint at h ⊢

  rcases h with h | h
  · left

    have hData :
        data.hi ≤ (extendHi data).hi := by
      simp [extendHi, Reg.hi]

    exact hData.trans h

  · right
    simpa [extendHi] using h
/--
A control outside `extendHi data` is also outside `data`.
-/
lemma qubitOutside_data_of_qubitOutside_extendHi
    (ctrl : ℕ)
    (data : Reg)
    (h : QubitOutside ctrl (extendHi data)) :
    QubitOutside ctrl data := by
  unfold QubitOutside at h ⊢

  rcases h with h | h
  · left
    simpa [extendHi] using h

  · right

    have hData :
        data.hi ≤ (extendHi data).hi := by
      simp [extendHi, Reg.hi]

    exact hData.trans h

/-! =========================================================
    Step 1: one controlled modular multiplication
========================================================= -/

/-!
### Rate lemmas

The core modular-multiplication proof uses a fixed workspace factor `cWork`.
The data register and `extendHi data` are bounded by `2n`, while the work
register is bounded by `cWork * n`.  Thus every width `W` relevant to the
PhaseProduct/QFT sub-bounds is bounded by

    max 2 cWork * n.

The next two lemmas record the resulting scaled `α`-power bound, first for a
raw width and then for `phaseProductSafeRate`.
-/

/--
A width bounded by `c*n` has its `α`-th power bounded by `c^α * n^α`.
-/
lemma rpow_le_constPow_mul_rpow
    (k c W n : ℕ)
    (hk : 1 < k)
    (hW : W ≤ c * n) :
    Real.rpow (W : ℝ) (phaseProductExponent k)
      ≤
    Real.rpow (c : ℝ) (phaseProductExponent k) *
      Real.rpow (n : ℝ) (phaseProductExponent k) := by
  have hα : 0 ≤ phaseProductExponent k := by
    linarith [one_lt_phaseProductExponent k hk]

  have hWR :
      (W : ℝ) ≤ ((c * n : ℕ) : ℝ) := by
    exact_mod_cast hW

  calc
    Real.rpow (W : ℝ) (phaseProductExponent k)
        ≤
      Real.rpow ((c * n : ℕ) : ℝ)
        (phaseProductExponent k) :=
          Real.rpow_le_rpow (by positivity) hWR hα

    _ =
      Real.rpow (c : ℝ) (phaseProductExponent k) *
        Real.rpow (n : ℝ) (phaseProductExponent k) := by
        simpa [Nat.cast_mul] using
          (Real.mul_rpow
            (show 0 ≤ (c : ℝ) by positivity)
            (show 0 ≤ (n : ℝ) by positivity)
            (z := phaseProductExponent k))

/--
The same bound for `phaseProductSafeRate`, whose base is `max 1 W`.
-/
lemma phaseProductSafeRate_le_constPow_mul_rpow
    (k c W n : ℕ)
    (hk : 1 < k)
    (hn : 1 ≤ n)
    (hc : 1 ≤ c)
    (hW : W ≤ c * n) :
    phaseProductSafeRate k W
      ≤
    Real.rpow (c : ℝ) (phaseProductExponent k) *
      Real.rpow (n : ℝ) (phaseProductExponent k) := by
  have hmax :
      max 1 W ≤ c * n := by
    apply max_le
    · exact le_trans hc (Nat.le_mul_of_pos_right c hn)
    · exact hW

  exact
    rpow_le_constPow_mul_rpow
      k c (max 1 W) n hk hmax

/--
The Hadamard layers and reversible arithmetic primitives in
`CmodMulInPlaceCore` contribute only linearly in `n`, provided

  regSize work ≤ cWork * n.

The resulting constant may depend on the fixed workspace factor `cWork`.
-/
lemma linearPrimitive_part_le
    (cWork n : ℕ)
    (work xext : Reg)
    (R : ℝ)
    (hxextSize : regSize xext = n + 1)
    (hworkUpper : regSize work ≤ cWork * n)
    (hnLeR : (n : ℝ) ≤ R)
    (hOneLeR : (1 : ℝ) ≤ R) :
    2 * (regSize work : ℝ)
        +
      2 * (linearPrimitiveGateBound (regSize xext) : ℝ)
        +
      (linearPrimitiveGateBound
        (regSize xext + regSize work) : ℝ)
      ≤
    (22 * (cWork : ℝ) + 150) * R := by

  have hLinearNat :
      2 * regSize work
          +
        2 * linearPrimitiveGateBound (regSize xext)
          +
        linearPrimitiveGateBound
          (regSize xext + regSize work)
        ≤
      (22 * cWork + 60) * n + 90 := by
    calc
      2 * regSize work
          +
        2 * linearPrimitiveGateBound (regSize xext)
          +
        linearPrimitiveGateBound
          (regSize xext + regSize work)
          =
        22 * regSize work + 60 * n + 90 := by
          rw [hxextSize]
          simp [linearPrimitiveGateBound]
          ring

      _ ≤
        22 * (cWork * n) + 60 * n + 90 := by
          omega

      _ =
        (22 * cWork + 60) * n + 90 := by
          ring

  have hCast :
      (2 * (regSize work : ℝ)
          +
        2 * (linearPrimitiveGateBound (regSize xext) : ℝ)
          +
        (linearPrimitiveGateBound
          (regSize xext + regSize work) : ℝ))
        ≤
      (((22 * cWork + 60) * n + 90 : ℕ) : ℝ) := by
    exact_mod_cast hLinearNat

  have hCoeffNonneg :
      0 ≤ 22 * (cWork : ℝ) + 60 := by
    positivity

  have hMain :
      (22 * (cWork : ℝ) + 60) * (n : ℝ)
        ≤
      (22 * (cWork : ℝ) + 60) * R :=
    mul_le_mul_of_nonneg_left
      hnLeR
      hCoeffNonneg

  have hConst :
      (90 : ℝ) ≤ 90 * R := by
    nlinarith

  refine hCast.trans ?_

  push_cast

  nlinarith

/-! ### Exact decomposition of the core circuit -/

/--
Exact gate-count decomposition of the lowered `CmodMulInPlaceCore`.

The circuit consists of two Hadamard layers on `work`, two QFTs on `work`,
two QFTs on `extendHi data`, one uncontrolled and two controlled
PhaseProducts, and a fixed number of reversible arithmetic primitives.
-/
lemma cmodMulInPlaceCore_gateCount_decompose
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (c N ctrl : ℕ)
    (data work : Reg)
    (flag : ℕ) :
    LowGate.gateCount
        shorGateCostModel
        (lowerGate
          (Basis := qs.Basis)
          k hk ops
          (CmodMulInPlaceCore
            (Basis := qs.Basis)
            c N ctrl data work flag))
      =
    2 * regSize work
      +
    LowGate.gateCount
      shorGateCostModel
      (lowerGate
        (Basis := qs.Basis)
        k hk ops
        (Gate.CPhaseProd
          ctrl
          ((2 * Real.pi * (((c + N - 1) % N : ℕ) : ℝ)) / (N : ℝ))
          data work))
      +
    2 *
      LowGate.gateCount
        shorGateCostModel
        (lowerGate
          (Basis := qs.Basis)
          k hk ops
          (Gate.QFT work))
      +
    2 *
      LowGate.gateCount
        shorGateCostModel
        (lowerGate
          (Basis := qs.Basis)
          k hk ops
          (Gate.QFT (extendHi data)))
      +
    LowGate.gateCount
      shorGateCostModel
      (lowerGate
        (Basis := qs.Basis)
        k hk ops
        (Gate.PhaseProd
          ((2 * Real.pi * (N : ℝ)) /
            ((2 : ℝ) ^ (regSize work + regSize (extendHi data))))
          work (extendHi data)))
      +
    LowGate.gateCount
      shorGateCostModel
      (lowerGate
        (Basis := qs.Basis)
        k hk ops
        (Gate.CPhaseProd
          ctrl
          ((2 * Real.pi * (((step5Constant c N) % N : ℕ) : ℝ)) / (N : ℝ))
          (extendHi data) work))
      +
    2 * linearPrimitiveGateBound (regSize (extendHi data))
      +
    linearPrimitiveGateBound
      (regSize (extendHi data) + regSize work) := by
  have hHWork :
      LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (H_reg work))
        =
      regSize work :=
    lowered_H_reg_gateCount qs k hk ops work

  simp only [
    CmodMulInPlaceCore,
    step1,
    step2,
    step3,
    step4,
    step5,
    IQFT,
    lowerGate,
    LowGate.gateCount
  ]

  rw [hHWork]

  simp [
    shorGateCostModel,
    phaseProductCostModel,
    shorPrimCost,
    Reg.hi,
    regSize,
    extendHi
  ]

  ring_nf

/-! ### Asymptotic bound for one controlled modular multiplication -/

lemma cmodMulInPlaceCore_gateCount_phase_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (cWork : ℕ)
    (_hcWork : 1 ≤ cWork)
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hPhase :
      PhaseProductGateCountBound
        (Basis := qs.Basis) k hk ops)
    (hCPhase :
      CPhaseProductGateCountBound
        (Basis := qs.Basis) k hk ops)
    (hQFT :
      QFTGateCountBound
        (Basis := qs.Basis) k hk ops) :
    ∃ A : ℝ, 0 < A ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (n c N ctrl : ℕ)
        (data work : Reg)
        (flag : ℕ),
        n₀ ≤ n →
        regSize data = n →
        n ≤ regSize work →
        regSize work ≤ cWork * n →
        ModMulCoreLayout data work flag ctrl →
        (LowGate.gateCount
            shorGateCostModel
            (lowerGate
              (Basis := qs.Basis)
              k hk ops
              (CmodMulInPlaceCore
                (Basis := qs.Basis)
                c N ctrl data work flag)) : ℝ)
          ≤
        A *
          Real.rpow
            (n : ℝ)
            (phaseProductExponent k) := by

  rcases hPhase with
    ⟨CPhase, hCPhasePos, nPhase, hnPhase, hPhase⟩

  rcases hCPhase with
    ⟨CControl, hCControlPos, nControl, hnControl, hCPhase⟩

  rcases hQFT with
    ⟨CQFT, hCQFTPos, nQFT, hnQFT, hQFT⟩

  /-
  `data` and `extendHi data` are bounded by `2n`,
  while `work` is bounded by `cWork * n`.

  Hence every register involved in this circuit is bounded by

      cMax * n

  where `cMax = max 2 cWork`.
  -/
  let cMax : ℕ := max 2 cWork

  let α : ℝ :=
    phaseProductExponent k

  let S : ℝ :=
    Real.rpow (cMax : ℝ) α

  /-
  The linear primitive contribution is bounded by

      (22 * cWork + 150) * n^α.
  -/
  let D : ℝ :=
    22 * (cWork : ℝ) + 150

  let A : ℝ :=
    S * (CPhase + 2 * CControl + 4 * CQFT) + D

  let n₀ : ℕ :=
    max 1 (max nPhase (max nControl nQFT))

  have hα :
      0 ≤ α := by
    dsimp [α]
    linarith [one_lt_phaseProductExponent k hk]

  have hS :
      0 ≤ S := by
    dsimp [S]
    positivity

  have hD :
      0 < D := by
    dsimp [D]
    positivity

  have hCoeff :
      0 < CPhase + 2 * CControl + 4 * CQFT := by
    positivity

  have hA :
      0 < A := by
    dsimp [A]
    positivity

  have hn₀ :
      1 ≤ n₀ := by
    dsimp [n₀]
    omega

  refine ⟨A, hA, n₀, hn₀, ?_⟩

  intro n c N ctrl data work flag
    hn hDataSize hworkLower hworkUpper hLayout

  have hnOne :
      1 ≤ n := by
    exact hn₀.trans hn

  have hnPhase' :
      nPhase ≤ n := by
    dsimp [n₀] at hn
    omega

  have hnControl' :
      nControl ≤ n := by
    dsimp [n₀] at hn
    omega

  have hnQFT' :
      nQFT ≤ n := by
    dsimp [n₀] at hn
    omega

  /-
  Basic facts about `cMax`.
  -/
  have hTwoLeMax :
      2 ≤ cMax := by
    dsimp [cMax]
    exact Nat.le_max_left _ _

  have hWorkLeMax :
      cWork ≤ cMax := by
    dsimp [cMax]
    exact Nat.le_max_right _ _

  have hOneLeMax :
      1 ≤ cMax := by
    omega

  have hTwoMulLeMaxMul :
      2 * n ≤ cMax * n := by
    exact Nat.mul_le_mul_right n hTwoLeMax

  have hWorkMulLeMaxMul :
      cWork * n ≤ cMax * n := by
    exact Nat.mul_le_mul_right n hWorkLeMax

  let xext : Reg :=
    extendHi data

  have hxextSize :
      regSize xext = n + 1 := by
    dsimp [xext]
    change regSize (extendHi data) = n + 1
    change data.size + 1 = n + 1
    exact congrArg Nat.succ hDataSize

  have hxextLower :
      n ≤ regSize xext := by
    rw [hxextSize]
    omega

  /-
  `xext` is intrinsically at most `2n`, hence also at most `cMax*n`.
  -/
  have hxextUpperTwo :
      regSize xext ≤ 2 * n := by
    rw [hxextSize]
    omega

  have hxextUpper :
      regSize xext ≤ cMax * n :=
    hxextUpperTwo.trans hTwoMulLeMaxMul

  /-
  `data` has exactly width `n`, hence is also bounded by `cMax*n`.
  -/
  have hdataUpperTwo :
      regSize data ≤ 2 * n := by
    rw [hDataSize]
    omega

  have hdataUpper :
      regSize data ≤ cMax * n :=
    hdataUpperTwo.trans hTwoMulLeMaxMul

  /-
  The assumed linear workspace bound gives the same common `cMax*n`
  envelope for `work`.
  -/
  have hworkUpperMax :
      regSize work ≤ cMax * n :=
    hworkUpper.trans hWorkMulLeMaxMul

  rcases hLayout with
    ⟨hDisjointExt,
      _hFlagExt,
      _hFlagWork,
      hCtrlExt,
      hCtrlWork,
      _hCtrlFlag⟩

  have hDisjointData :
      Shor.Disjoint data work :=
    disjoint_data_work_of_disjoint_extendHi
      data work hDisjointExt

  have hDisjointWorkExt :
      Shor.Disjoint work xext := by
    dsimp [xext]
    unfold Shor.Disjoint at hDisjointExt ⊢
    tauto

  have hCtrlData :
      QubitOutside ctrl data :=
    qubitOutside_data_of_qubitOutside_extendHi
      ctrl data hCtrlExt

  have hCtrlXext :
      QubitOutside ctrl xext := by
    simpa [xext] using hCtrlExt

  have hWellFormed (r : Reg) :
      WellFormedReg r :=
    Reg.lo_le_hi r

  let R : ℝ :=
    Real.rpow (n : ℝ) α

  have hRNonneg :
      0 ≤ R := by
    dsimp [R]
    positivity

  have hnReal :
      (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hnOne

  have hnLeR :
      (n : ℝ) ≤ R := by
    dsimp [R, α]
    exact
      natCast_le_phaseProduct_rpow
        k hk hnOne

  have hOneLeR :
      (1 : ℝ) ≤ R :=
    hnReal.trans hnLeR

  /-
  Every relevant width is now bounded by

      cMax * n,

  so its α-power is bounded by

      cMax^α * n^α = S * R.
  -/
  have hRawRate :
      ∀ W : ℕ,
        W ≤ cMax * n →
        Real.rpow (W : ℝ) α
          ≤
        S * R := by
    intro W hW
    simpa [α, S, R] using
      rpow_le_constPow_mul_rpow
        k cMax W n hk hW

  have hSafeRate :
      ∀ W : ℕ,
        W ≤ cMax * n →
        phaseProductSafeRate k W
          ≤
        S * R := by
    intro W hW
    simpa [α, S, R] using
      phaseProductSafeRate_le_constPow_mul_rpow
        k cMax W n
        hk
        hnOne
        hOneLeMax
        hW

  let phi1 : ℝ :=
    (2 * Real.pi *
      (((c + N - 1) % N : ℕ) : ℝ)) /
      (N : ℝ)

  let phi2 : ℝ :=
    (2 * Real.pi * (N : ℝ)) /
      ((2 : ℝ) ^
        (regSize work + regSize xext))

  let phi5 : ℝ :=
    (2 * Real.pi *
      (((step5Constant c N) % N : ℕ) : ℝ)) /
      (N : ℝ)

  /- ---------------------------------------------------------
     First controlled PhaseProduct: `data × work`
     --------------------------------------------------------- -/

  have hControl1Large :
      nControl ≤
        max (regSize data) (regSize work) := by
    calc
      nControl ≤ n := hnControl'
      _ ≤ regSize work := hworkLower
      _ ≤ max (regSize data) (regSize work) :=
        Nat.le_max_right _ _

  have hControl1Size :
      max (regSize data) (regSize work)
        ≤
      cMax * n :=
    max_le hdataUpper hworkUpperMax

  have hControl1₀ :=
    hCPhase
      ctrl phi1 data work
      (hWellFormed data)
      (hWellFormed work)
      hDisjointData
      hCtrlData
      hCtrlWork
      hControl1Large

  have hControl1 :
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (Gate.CPhaseProd
              ctrl phi1 data work)) : ℝ)
        ≤
      CControl * S * R := by
    rw [mul_assoc]
    exact
      hControl1₀.trans
        (mul_le_mul_of_nonneg_left
          (hSafeRate _ hControl1Size)
          (le_of_lt hCControlPos))

  /- ---------------------------------------------------------
     Second controlled PhaseProduct: `xext × work`
     --------------------------------------------------------- -/

  have hControl2Large :
      nControl ≤
        max (regSize xext) (regSize work) := by
    calc
      nControl ≤ n := hnControl'
      _ ≤ regSize work := hworkLower
      _ ≤ max (regSize xext) (regSize work) :=
        Nat.le_max_right _ _

  have hControl2Size :
      max (regSize xext) (regSize work)
        ≤
      cMax * n :=
    max_le hxextUpper hworkUpperMax

  have hControl2₀ :=
    hCPhase
      ctrl phi5 xext work
      (hWellFormed xext)
      (hWellFormed work)
      hDisjointExt
      hCtrlXext
      hCtrlWork
      hControl2Large

  have hControl2 :
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (Gate.CPhaseProd
              ctrl phi5 xext work)) : ℝ)
        ≤
      CControl * S * R := by
    rw [mul_assoc]
    exact
      hControl2₀.trans
        (mul_le_mul_of_nonneg_left
          (hSafeRate _ hControl2Size)
          (le_of_lt hCControlPos))

  /- ---------------------------------------------------------
     Ordinary PhaseProduct: `work × xext`
     --------------------------------------------------------- -/

  have hPhaseLarge :
      nPhase ≤
        max (regSize work) (regSize xext) := by
    calc
      nPhase ≤ n := hnPhase'
      _ ≤ regSize work := hworkLower
      _ ≤ max (regSize work) (regSize xext) :=
        Nat.le_max_left _ _

  have hPhaseSize :
      max (regSize work) (regSize xext)
        ≤
      cMax * n :=
    max_le hworkUpperMax hxextUpper

  have hPhase₀ :=
    hPhase
      phi2 work xext
      (hWellFormed work)
      (hWellFormed xext)
      hDisjointWorkExt
      hPhaseLarge

  have hPhaseBound :
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (Gate.PhaseProd
              phi2 work xext)) : ℝ)
        ≤
      CPhase * S * R := by
    rw [mul_assoc]
    refine
      hPhase₀.trans
        (mul_le_mul_of_nonneg_left
          ?_
          (le_of_lt hCPhasePos))

    exact
      hRawRate _ hPhaseSize

  /- ---------------------------------------------------------
     QFT on `work`
     --------------------------------------------------------- -/

  have hQFTWork₀ :=
    hQFT
      work
      (hWellFormed work)
      (hnQFT'.trans hworkLower)

  have hQFTWork :
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (Gate.QFT work)) : ℝ)
        ≤
      CQFT * S * R := by
    rw [mul_assoc]
    exact
      hQFTWork₀.trans
        (mul_le_mul_of_nonneg_left
          (hSafeRate _ hworkUpperMax)
          (le_of_lt hCQFTPos))

  /- ---------------------------------------------------------
     QFT on `extendHi data`
     --------------------------------------------------------- -/

  have hQFTXext₀ :=
    hQFT
      xext
      (hWellFormed xext)
      (hnQFT'.trans hxextLower)

  have hQFTXext :
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (Gate.QFT xext)) : ℝ)
        ≤
      CQFT * S * R := by
    rw [mul_assoc]
    exact
      hQFTXext₀.trans
        (mul_le_mul_of_nonneg_left
          (hSafeRate _ hxextUpper)
          (le_of_lt hCQFTPos))

  /-
  Linear gates.

  Here the constant depends on `cWork`, which is allowed because
  `cWork` is fixed before the asymptotic size `n` varies.
  -/
  have hLinear' :
      2 * (regSize work : ℝ)
          +
        2 * (linearPrimitiveGateBound
          (regSize xext) : ℝ)
          +
        (linearPrimitiveGateBound
          (regSize xext + regSize work) : ℝ)
        ≤
      D * R := by
    simpa [D] using
      linearPrimitive_part_le
        cWork n work xext R
        hxextSize
        hworkUpper
        hnLeR
        hOneLeR

  /-
  Exact circuit decomposition.
  -/
  let gc : Gate → ℕ :=
    fun G =>
      LowGate.gateCount
        shorGateCostModel
        (lowerGate
          (Basis := qs.Basis)
          k hk ops G)

  have hExact :
      gc
          (CmodMulInPlaceCore
            (Basis := qs.Basis)
            c N ctrl data work flag)
        =
      2 * regSize work
        +
      gc (Gate.CPhaseProd ctrl phi1 data work)
        +
      2 * gc (Gate.QFT work)
        +
      2 * gc (Gate.QFT xext)
        +
      gc (Gate.PhaseProd phi2 work xext)
        +
      gc (Gate.CPhaseProd ctrl phi5 xext work)
        +
      2 * linearPrimitiveGateBound (regSize xext)
        +
      linearPrimitiveGateBound
        (regSize xext + regSize work) :=
    cmodMulInPlaceCore_gateCount_decompose
      qs k hk ops c N ctrl data work flag

  have hExactR :=
    congrArg (fun t : ℕ => (t : ℝ)) hExact

  push_cast at hExactR

  change
    (gc
      (CmodMulInPlaceCore
        (Basis := qs.Basis)
        c N ctrl data work flag) : ℝ)
      ≤
    A *
      Real.rpow
        (n : ℝ)
        (phaseProductExponent k)

  have hControl1' :
      (gc
        (Gate.CPhaseProd ctrl phi1 data work) : ℝ)
        ≤
      CControl * S * R := by
    simpa [gc] using hControl1

  have hControl2' :
      (gc
        (Gate.CPhaseProd ctrl phi5 xext work) : ℝ)
        ≤
      CControl * S * R := by
    simpa [gc] using hControl2

  have hPhaseBound' :
      (gc
        (Gate.PhaseProd phi2 work xext) : ℝ)
        ≤
      CPhase * S * R := by
    simpa [gc] using hPhaseBound

  have hQFTWork' :
      (gc (Gate.QFT work) : ℝ)
        ≤
      CQFT * S * R := by
    simpa [gc] using hQFTWork

  have hQFTXext' :
      (gc (Gate.QFT xext) : ℝ)
        ≤
      CQFT * S * R := by
    simpa [gc] using hQFTXext

  rw [hExactR]

  change
    _ ≤
      (S *
          (CPhase + 2 * CControl + 4 * CQFT)
        + D) *
      Real.rpow
        (n : ℝ)
        (phaseProductExponent k)

  have hR :
      Real.rpow
          (n : ℝ)
          (phaseProductExponent k)
        =
      R := by
    rfl

  rw [hR]

  nlinarith

/-! =========================================================
    Step 2: modular exponentiation
========================================================= -/

/-!
This section lifts the one-controlled-modular-multiplication estimate to the
whole modular-exponentiation loop.  The only loop-count fact needed here is
the Shor exponent-width bound `regSize x ≤ 2*n`; the work-register bound is
kept as the fixed internal factor `cWork`.
-/

/--
If every controlled modular multiplication costs at most

  A * n^(phaseProductExponent k),

then modular exponentiation costs at most

  B * n * n^(phaseProductExponent k).

The proof is an induction over `modExpApproxStepsValid`. The layout hypothesis
provides `ModMulCoreLayout` for every control qubit, and `regSize x ≤ 2n`
bounds the number of recursive calls.
-/
lemma modExpApproxValid_gateCount_phase_bound_of_core
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (cWork : ℕ)
    (_hcWork : 1 ≤ cWork)
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (A : ℝ)
    (hA : 0 < A)
    (nCore : ℕ)
    (hnCore : 1 ≤ nCore)
    (hCore :
      ∀ (n c N ctrl : ℕ) (data work : Reg) (flag : ℕ),
        nCore ≤ n → regSize data = n → n ≤ regSize work → regSize work ≤ cWork * n →
        ModMulCoreLayout data work flag ctrl →
        (LowGate.gateCount shorGateCostModel
          (lowerGate (Basis := qs.Basis) k hk ops (CmodMulInPlaceCore (Basis := qs.Basis) c N ctrl data work flag)) : ℝ)
          ≤
        A *  Real.rpow (n : ℝ) (phaseProductExponent k)) :
    ∃ B : ℝ, 0 < B ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (n a N : ℕ) (x data work : Reg) (flag : ℕ),
        n₀ ≤ n →
        ShorGateCountLayout cWork n x data work flag →
        (LowGate.gateCount shorGateCostModel
          (lowerGate (Basis := qs.Basis)  k hk ops (modExpApproxValid (Basis := qs.Basis)  a N x data work flag)) : ℝ)
          ≤
        B * (n : ℝ) *
          Real.rpow
            (n : ℝ)
            (phaseProductExponent k) := by
  refine ⟨2 * A, by positivity, nCore, hnCore, ?_⟩

  intro n a N x data work flag hn hLayout

  rcases hLayout with
    ⟨hDataSize,
      hxLower,
      hxUpper,
      hworkLower,
      hworkUpper,
      hFullLayout⟩

  let R : ℝ :=
    Real.rpow
      (n : ℝ)
      (phaseProductExponent k)

  have hR_nonneg : 0 ≤ R := by
    unfold R
    exact Real.rpow_nonneg (by positivity) _

  have hAR_nonneg : 0 ≤ A * R :=
    mul_nonneg (le_of_lt hA) hR_nonneg

  /-
  A tail of `t` exponent bits contains at most `t` modular
  multiplications, each costing at most `A * R`.
  -/
  have hSteps :
      ∀ (t q : ℕ),
        ModExpTailLayout x data work flag q t →
        (LowGate.gateCount
            shorGateCostModel
            (lowerGate
              (Basis := qs.Basis)
              k hk ops
              (modExpApproxStepsValid
                (Basis := qs.Basis)
                a N x data work flag q t)) : ℝ)
          ≤
        (t : ℝ) * (A * R) := by
    intro t

    induction t with
    | zero =>
        intro q _hLayout
        simp [modExpApproxStepsValid]

    | succ t ih =>
        intro q hTailLayout

        let c : ℕ :=
          (a ^ (2 ^ (q - x.lo))) % N

        have hHeadLayout :
            ModMulCoreLayout data work flag q := by
          have h :=
            hTailLayout.2.2 0 (by omega)
          simpa using h

        have hHead :
            (LowGate.gateCount
                shorGateCostModel
                (lowerGate
                  (Basis := qs.Basis)
                  k hk ops
                  (CmodMulInPlaceCore
                    (Basis := qs.Basis)
                    c N q data work flag)) : ℝ)
              ≤
            A * R := by
          simpa [c, R] using
            hCore
              n c N q data work flag
              hn
              hDataSize
              hworkLower
              hworkUpper
              hHeadLayout

        have hTailLayout' :
            ModExpTailLayout
              x data work flag (q + 1) t :=
          modExpTailLayout_tail
            x data work flag q t hTailLayout

        have hTail :
            (LowGate.gateCount
                shorGateCostModel
                (lowerGate
                  (Basis := qs.Basis)
                  k hk ops
                  (modExpApproxStepsValid
                    (Basis := qs.Basis)
                    a N x data work flag (q + 1) t)) : ℝ)
              ≤
            (t : ℝ) * (A * R) :=
          ih (q + 1) hTailLayout'

        calc
          (LowGate.gateCount
              shorGateCostModel
              (lowerGate
                (Basis := qs.Basis)
                k hk ops
                (modExpApproxStepsValid
                  (Basis := qs.Basis)
                  a N x data work flag q (t + 1))) : ℝ)
              =
            (LowGate.gateCount
                shorGateCostModel
                (lowerGate
                  (Basis := qs.Basis)
                  k hk ops
                  (CmodMulInPlaceCore
                    (Basis := qs.Basis)
                    c N q data work flag)) : ℝ)
              +
            (LowGate.gateCount
                shorGateCostModel
                (lowerGate
                  (Basis := qs.Basis)
                  k hk ops
                  (modExpApproxStepsValid
                    (Basis := qs.Basis)
                    a N x data work flag (q + 1) t)) : ℝ) := by
                simp [modExpApproxStepsValid, c]

          _ ≤
            A * R + (t : ℝ) * (A * R) :=
              add_le_add hHead hTail

          _ =
            ((t + 1 : ℕ) : ℝ) * (A * R) := by
              push_cast
              ring

  have hInitialTailLayout :
      ModExpTailLayout
        x data work flag x.lo (tbits x) := by
    simpa [ModExpLayout] using hFullLayout

  have hAllSteps :
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (modExpApproxStepsValid
              (Basis := qs.Basis)
              a N x data work flag
              x.lo (tbits x))) : ℝ)
        ≤
      (tbits x : ℝ) * (A * R) :=
    hSteps (tbits x) x.lo hInitialTailLayout

  have hxUpper' :
      tbits x ≤ 2 * n := by
    simpa [tbits] using hxUpper

  have hxUpperR :
      (tbits x : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast hxUpper'

  calc
    (LowGate.gateCount
        shorGateCostModel
        (lowerGate
          (Basis := qs.Basis)
          k hk ops
          (modExpApproxValid
            (Basis := qs.Basis)
            a N x data work flag)) : ℝ)
        =
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (modExpApproxStepsValid
              (Basis := qs.Basis)
              a N x data work flag
              x.lo (tbits x))) : ℝ) := by
          rfl

    _ ≤
      (tbits x : ℝ) * (A * R) :=
        hAllSteps

    _ ≤
      (2 * (n : ℝ)) * (A * R) :=
        mul_le_mul_of_nonneg_right
          hxUpperR
          hAR_nonneg

    _ =
      (2 * A) * (n : ℝ) *
        Real.rpow
          (n : ℝ)
          (phaseProductExponent k) := by
        unfold R
        ring

/-! =========================================================
    Step 3: complete order-finding circuit
========================================================= -/

/-!
This section adds the order-finding wrapper around modular exponentiation:
initial Hadamards on the exponent register, initialization of the data
register, and the final QFT.  It produces the natural
`n^(1 + phaseProductExponent k)` bound before the final exponent comparison.
-/

/--
Add the initial Hadamards, initialization `X`, and final QFT to the modular
exponentiation bound.

The result is the natural fixed-`k` complexity

  O(n^(1 + phaseProductExponent k)).
-/
lemma orderFindingApproxLow_gateCount_phase_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (cWork : ℕ)
    (_hcWork : 1 ≤ cWork)
    (hQFT :
      QFTGateCountBound
        (Basis := qs.Basis) k hk ops)
    (B : ℝ)
    (hB : 0 < B)
    (nModExp : ℕ)
    (hnModExp : 1 ≤ nModExp)
    (hModExp :
      ∀ (n a N : ℕ)
        (x data work : Reg)
        (flag : ℕ),
        nModExp ≤ n →
        ShorGateCountLayout cWork n x data work flag →
        (LowGate.gateCount
            shorGateCostModel
            (lowerGate
              (Basis := qs.Basis)
              k hk ops
              (modExpApproxValid
                (Basis := qs.Basis)
                a N x data work flag)) : ℝ)
          ≤
        B * (n : ℝ) *
          Real.rpow
            (n : ℝ)
            (phaseProductExponent k)) :
    ∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (n a N : ℕ)
        (x y work : Reg)
        (flag : ℕ),
        n₀ ≤ n →
        ShorGateCountLayout cWork n x y work flag →
        (shorOrderFindingGateCount
            qs k hk ops a N x y work flag : ℝ)
          ≤
        C *
          Real.rpow
            (n : ℝ)
            (1 + phaseProductExponent k) := by
  rcases hQFT with
    ⟨CQFT, hCQFT, nQFT, hnQFT, hQFT⟩

  let α : ℝ :=
    phaseProductExponent k

  let S : ℝ :=
    Real.rpow (2 : ℝ) α

  /-
  The coefficient `3` absorbs:

  * the `2n` initial Hadamards;
  * the single initialization `X`.

  The final QFT contributes `CQFT * S`.
  -/
  let C : ℝ :=
    B + 3 + CQFT * S

  let n₀ : ℕ :=
    max nModExp nQFT

  have hα : 0 ≤ α := by
    dsimp [α]
    linarith [one_lt_phaseProductExponent k hk]

  have hS : 0 ≤ S := by
    dsimp [S]
    positivity

  have hC : 0 < C := by
    dsimp [C]
    positivity

  have hn₀ : 1 ≤ n₀ := by
    dsimp [n₀]
    omega

  refine ⟨C, hC, n₀, hn₀, ?_⟩

  intro n a N x y work flag hn hLayout

  have hLayoutCopy :
      ShorGateCountLayout cWork n x y work flag :=
    hLayout

  rcases hLayout with
    ⟨hySize,
      hxLower,
      hxUpper,
      hworkLower,
      hworkUpper,
      hModExpLayout⟩

  have hnOne : 1 ≤ n := by
    exact hn₀.trans hn

  have hnModExp' : nModExp ≤ n := by
    dsimp [n₀] at hn
    omega

  have hnQFT' : nQFT ≤ n := by
    dsimp [n₀] at hn
    omega

  let R : ℝ :=
    Real.rpow (n : ℝ) α

  have hRNonneg : 0 ≤ R := by
    dsimp [R]
    positivity

  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hnOne

  have hnPositive : (0 : ℝ) < (n : ℝ) :=
    lt_of_lt_of_le zero_lt_one hnReal

  /-
  Since `α > 1`, both `n` and `1` are bounded by `n^α`.
  -/
  have hnLeR :
      (n : ℝ) ≤ R := by
    dsimp [R, α]
    exact
      natCast_le_phaseProduct_rpow
        k hk hnOne

  have hOneLeR : (1 : ℝ) ≤ R :=
    hnReal.trans hnLeR

  /-
  `n * R` is exactly `n^(1 + α)`.
  -/
  have hPower :
      Real.rpow (n : ℝ) (1 + α)
        =
      (n : ℝ) * R := by
    calc
      Real.rpow (n : ℝ) (1 + α)
          =
        Real.rpow (n : ℝ) 1 *
          Real.rpow (n : ℝ) α :=
            Real.rpow_add hnPositive 1 α

      _ =
        (n : ℝ) * R := by
          simp [R]

  have hModExpBound :
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (modExpApproxValid
              (Basis := qs.Basis)
              a N x y work flag)) : ℝ)
        ≤
      B * (n : ℝ) * R := by
    simpa [R, α] using
      hModExp
        n a N x y work flag
        hnModExp'
        hLayoutCopy

  have hxQFTLarge :
      nQFT ≤ regSize x :=
    hnQFT'.trans hxLower

  have hxWellFormed :
      WellFormedReg x :=
    Reg.lo_le_hi x

  have hQFTBound₀ :=
    hQFT x hxWellFormed hxQFTLarge

  have hxOne :
      1 ≤ regSize x :=
    hnOne.trans hxLower

  have hQFTRate :
      phaseProductSafeRate k (regSize x)
        ≤
      S * R := by
    have hxCast :
        (regSize x : ℝ)
          ≤
        ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast hxUpper

    calc
      phaseProductSafeRate k (regSize x)
          =
        Real.rpow
          (regSize x : ℝ)
          α := by
            simp [
              phaseProductSafeRate,
              max_eq_right hxOne,
              α
            ]

      _ ≤
        Real.rpow
          ((2 * n : ℕ) : ℝ)
          α :=
            Real.rpow_le_rpow
              (by positivity)
              hxCast
              hα

      _ =
        S * R := by
          simpa [S, R, Nat.cast_mul] using
            (Real.mul_rpow
              (show 0 ≤ (2 : ℝ) by positivity)
              (show 0 ≤ (n : ℝ) by positivity)
              (z := α))

  have hQFTBound :
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (Gate.QFT x)) : ℝ)
        ≤
      CQFT * S * R := by
    calc
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (Gate.QFT x)) : ℝ)
          ≤
        CQFT *
          phaseProductSafeRate k (regSize x) :=
            hQFTBound₀

      _ ≤
        CQFT * (S * R) :=
          mul_le_mul_of_nonneg_left
            hQFTRate
            (le_of_lt hCQFT)

      _ =
        CQFT * S * R := by
          ring

  /-
  Move the QFT bound from `R` to `n * R`.
  -/
  have hRLeNR :
      R ≤ (n : ℝ) * R := by
    calc
      R = 1 * R := by ring
      _ ≤ (n : ℝ) * R :=
        mul_le_mul_of_nonneg_right
          hnReal
          hRNonneg

  have hQFTBound' :
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (Gate.QFT x)) : ℝ)
        ≤
      CQFT * S * ((n : ℝ) * R) := by
    calc
      (LowGate.gateCount
          shorGateCostModel
          (lowerGate
            (Basis := qs.Basis)
            k hk ops
            (Gate.QFT x)) : ℝ)
          ≤
        CQFT * S * R :=
          hQFTBound

      _ ≤
        CQFT * S * ((n : ℝ) * R) :=
          mul_le_mul_of_nonneg_left
            hRLeNR
            (mul_nonneg
              (le_of_lt hCQFT)
              hS)

  /-
  The Hadamard layer has at most `2n` gates.
  -/
  have hxCast :
      (regSize x : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast hxUpper

  have hnLeNR :
      (n : ℝ) ≤ (n : ℝ) * R := by
    calc
      (n : ℝ) = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * R :=
        mul_le_mul_of_nonneg_left
          hOneLeR
          (by positivity)

  have hxBound :
      (regSize x : ℝ)
        ≤
      2 * ((n : ℝ) * R) := by
    calc
      (regSize x : ℝ)
          ≤
        2 * (n : ℝ) :=
          hxCast

      _ ≤
        2 * ((n : ℝ) * R) :=
          mul_le_mul_of_nonneg_left
            hnLeNR
            (by norm_num)

  /-
  The initialization `X` contributes one gate.
  -/
  have hOneLeNR :
      (1 : ℝ) ≤ (n : ℝ) * R :=
    hnReal.trans hnLeNR

  /-
  Exact decomposition of the complete order-finding circuit.
  -/
  let gc : Gate → ℕ :=
    fun G =>
      LowGate.gateCount
        shorGateCostModel
        (lowerGate
          (Basis := qs.Basis)
          k hk ops
          G)

  have hExact :
      shorOrderFindingGateCount
          qs k hk ops a N x y work flag
        =
      regSize x
        +
      1
        +
      gc
        (modExpApproxValid
          (Basis := qs.Basis)
          a N x y work flag)
        +
      gc (Gate.QFT x) := by
    dsimp [
      shorOrderFindingGateCount,
      orderFindingApproxLow,
      orderFindingApprox,
      initY1,
      gc
    ]

    simp [
      lowerGate,
      LowGate.gateCount,
      lowered_H_reg_gateCount
    ]

    ring

  have hExactR :=
    congrArg (fun t : ℕ => (t : ℝ)) hExact

  push_cast at hExactR

  have hModExpBound' :
      (gc
        (modExpApproxValid
          (Basis := qs.Basis)
          a N x y work flag) : ℝ)
        ≤
      B * ((n : ℝ) * R) := by
    dsimp [gc]
    convert hModExpBound using 1 ; ring

  have hQFTBound'' :
      (gc (Gate.QFT x) : ℝ)
        ≤
      CQFT * S * ((n : ℝ) * R) := by
    simpa [gc] using hQFTBound'

  rw [hExactR]

  change
    (regSize x : ℝ)
        + 1
        + (gc
            (modExpApproxValid
              (Basis := qs.Basis)
              a N x y work flag) : ℝ)
        + (gc (Gate.QFT x) : ℝ)
      ≤
    C *
      Real.rpow
        (n : ℝ)
        (1 + phaseProductExponent k)

  have hFinal :
      (regSize x : ℝ)
          + 1
          + (gc
              (modExpApproxValid
                (Basis := qs.Basis)
                a N x y work flag) : ℝ)
          + (gc (Gate.QFT x) : ℝ)
        ≤
      (B + 3 + CQFT * S) *
        ((n : ℝ) * R) := by
    nlinarith

  calc
    (regSize x : ℝ)
        + 1
        + (gc
            (modExpApproxValid
              (Basis := qs.Basis)
              a N x y work flag) : ℝ)
        + (gc (Gate.QFT x) : ℝ)
        ≤
      (B + 3 + CQFT * S) *
        ((n : ℝ) * R) :=
          hFinal

    _ =
      C *
        Real.rpow
          (n : ℝ)
          (1 + phaseProductExponent k) := by
        rw [show
          Real.rpow
              (n : ℝ)
              (1 + phaseProductExponent k)
            =
          (n : ℝ) * R by
            simpa [α] using hPower
        ]


/-! =========================================================
    Step 4: exponent comparison
========================================================= -/

/-!
The previous section gives a bound in terms of
`1 + phaseProductExponent k`.  This section is the final asymptotic conversion
to the advertised `2 + ε` exponent under the component-theorem hypothesis
`phaseProductExponent k ≤ 1 + ε`.
-/

/--
If

  phaseProductExponent k ≤ 1 + ε,

then

  n^(1 + phaseProductExponent k) ≤ n^(2 + ε)

for `n ≥ 1`.
-/
lemma phaseProduct_succ_rate_le_shorGateRate
    (ε : ℝ)
    (k n : ℕ)
    (hn : 1 ≤ n)
    (hExponent :
      phaseProductExponent k ≤ 1 + ε) :
    Real.rpow
        (n : ℝ)
        (1 + phaseProductExponent k)
      ≤
    shorGateRate ε n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hExp :
      1 + phaseProductExponent k ≤ 2 + ε := by
    linarith

  have hpow :=
    Real.rpow_le_rpow_of_exponent_le hnR hExp

  simpa [shorGateRate, max_eq_right hn] using hpow


/-! =========================================================
    Shor register widths
========================================================= -/

/-!
These lemmas convert the exact public Shor register-size formulas into the
layout inequalities needed by the gate-count proof.  The exponent register
is still bounded by `2 * regSize y`; only the work register uses the
internally chosen workspace factor.
-/



lemma shor_y_width_le_x_width
    (N : ℕ)
    (x y : Reg)
    (hN : 1 < N)
    (hx : regSize x = Nat.log2 (2 * N^2))
    (hy : regSize y = Nat.log2 (2 * N)) :
    regSize y ≤ regSize x := by
  rw [hx, hy]

  have harg :
      2 * N ≤ 2 * N^2 := by
    nlinarith

  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right harg

lemma shor_x_width_le_two_y_width
    (N : ℕ)
    (x y : Reg)
    (hN : 1 < N)
    (hx : regSize x = Nat.log2 (2 * N^2))
    (hy : regSize y = Nat.log2 (2 * N)) :
    regSize x ≤ 2 * regSize y := by
  have hNne : N ≠ 0 := by
    omega

  have hNsqne : N ^ 2 ≠ 0 := by
    positivity

  have hN_lt_pow :
      N < 2 ^ (Nat.log2 N + 1) := by
    exact
      (Nat.log2_lt hNne).mp
        (by omega)

  have hsq :
      N ^ 2 <
        (2 ^ (Nat.log2 N + 1)) ^ 2 := by
    nlinarith

  have hpow_eq :
      (2 ^ (Nat.log2 N + 1)) ^ 2
        =
      2 ^ (2 * Nat.log2 N + 2) := by
    rw [← pow_mul]
    congr 1
    omega

  have hsq' :
      N ^ 2 <
        2 ^ (2 * Nat.log2 N + 2) := by
    calc
      N ^ 2
          < (2 ^ (Nat.log2 N + 1)) ^ 2 := hsq
      _ = 2 ^ (2 * Nat.log2 N + 2) := hpow_eq

  have hlogSq :
      Nat.log2 (N ^ 2)
        < 2 * Nat.log2 N + 2 := by
    exact
      (Nat.log2_lt hNsqne).mpr hsq'

  rw [hx, hy]
  rw [Nat.log2_two_mul hNsqne]
  rw [Nat.log2_two_mul hNne]
  omega

/-! =========================================================
    Algorithm-1 workspace growth
========================================================= -/

/-!
The correctness setup specifies the work register exactly as

    regSize work = regSize data + algorithm1ExtraBits η.

The first lemma turns any eventual bound on the extra bits into a concrete
linear work-register bound.  The next two lemmas prove such a bound for the
specific Shor precision schedule `η(n) = δ / n²`, choosing a fixed workspace
factor internally.
-/

lemma Algorithm1Precision.work_width_le_mul
    {η : ℝ}
    {data work : Reg}
    {cWork : ℕ}
    (hcWork : 1 ≤ cWork)
    (h : Algorithm1Precision η data work)
    (hExtra :
      algorithm1ExtraBits η
        ≤
      (cWork - 1) * regSize data) :
    regSize work ≤ cWork * regSize data := by
  rw [work_width h]
  calc
    regSize data + algorithm1ExtraBits η
        ≤ regSize data + (cWork - 1) * regSize data :=
          Nat.add_le_add_left hExtra _
    _ = cWork * regSize data := by
          calc
            regSize data + (cWork - 1) * regSize data
                =
              (1 + (cWork - 1)) * regSize data := by
                rw [Nat.add_mul, one_mul]
            _ = cWork * regSize data := by
                rw [Nat.add_comm, Nat.sub_add_cancel hcWork]

lemma shorEta_inv_two_mul
    (δ : ℝ)
    (hδ : 0 < δ)
    (n : ℕ)
    (hn : 1 ≤ n) :
    1 / (2 * shorEta δ n)
      =
    (n : ℝ)^2 / (2 * δ) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  dsimp [shorEta]
  field_simp [hδ.ne', hn0]

lemma algorithm1ExtraBits_shorEta_eventually_linear
    (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ cWork : ℕ, 1 ≤ cWork ∧
    ∃ nExtra : ℕ, 1 ≤ nExtra ∧
      ∀ n : ℕ,
        nExtra ≤ n →
        algorithm1ExtraBits (shorEta δ n)
          ≤
        (cWork - 1) * n := by

  have hconst :
      Tendsto
        (fun n : ℕ => (2 : ℝ) / (2 : ℝ)^n)
        atTop
        (nhds 0) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt
        0
        (show (1 : ℝ) < 2 by norm_num)).const_mul (2 : ℝ)

  have hquad0 :
      Tendsto
        (fun n : ℕ => ((n : ℝ)^2 / (2 : ℝ)^n))
        atTop
        (nhds 0) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt
        2
        (show (1 : ℝ) < 2 by norm_num))

  have hquad :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ)^2 / (2 * δ)) / (2 : ℝ)^n)
        atTop
        (nhds 0) := by
    have h :=
      hquad0.const_mul ((2 * δ)⁻¹)
    simpa [
      div_eq_mul_inv,
      mul_comm,
      mul_left_comm,
      mul_assoc
    ] using h

  have hsum :
      Tendsto
        (fun n : ℕ =>
          (2 + (n : ℝ)^2 / (2 * δ)) / (2 : ℝ)^n)
        atTop
        (nhds 0) := by
    have h :=
      hconst.add hquad
    simpa [zero_add] using
      h.congr' (by
        filter_upwards with n
        field_simp [
          pow_ne_zero
            _
            (show (2 : ℝ) ≠ 0 by norm_num)
        ])

  have hlt :
      ∀ᶠ n : ℕ in atTop,
        (2 + (n : ℝ)^2 / (2 * δ)) / (2 : ℝ)^n
          <
        1 :=
    hsum.eventually
      (Iio_mem_nhds
        (show (0 : ℝ) < 1 by norm_num))

  rw [eventually_atTop] at hlt
  rcases hlt with
    ⟨N, hN⟩

  refine ⟨3, by omega, max 1 N, by omega, ?_⟩

  intro n hn

  have hn1 : 1 ≤ n := by
    omega

  have hratio :
      (2 + (n : ℝ)^2 / (2 * δ)) / (2 : ℝ)^n
        <
      1 :=
    hN n (by omega)

  have hdenpos :
      0 < (2 : ℝ)^n :=
    pow_pos (by norm_num) _

  have harg_le_pow :
      2 + (n : ℝ)^2 / (2 * δ)
        ≤
      (2 : ℝ)^n := by
    have hmul :=
      mul_lt_mul_of_pos_right hratio hdenpos
    exact le_of_lt <| by
      calc
        2 + (n : ℝ)^2 / (2 * δ)
            =
          ((2 + (n : ℝ)^2 / (2 * δ)) / (2 : ℝ)^n)
            * (2 : ℝ)^n := by
              field_simp [
                pow_ne_zero
                  _
                  (show (2 : ℝ) ≠ 0 by norm_num)
              ]
        _ < (1 : ℝ) * (2 : ℝ)^n :=
              hmul
        _ = (2 : ℝ)^n := by
              ring

  have hargpos :
      0 < 2 + (n : ℝ)^2 / (2 * δ) := by
    positivity

  have hlog :
      Real.logb 2 (2 + (n : ℝ)^2 / (2 * δ))
        ≤
      (n : ℝ) := by
    have hp :
        2 + (n : ℝ)^2 / (2 * δ)
          ≤
        (2 : ℝ) ^ (n : ℝ) := by
      simpa [Real.rpow_natCast] using harg_le_pow
    exact
      (Real.logb_le_iff_le_rpow
        (show (1 : ℝ) < 2 by norm_num)
        hargpos).2 hp

  have heta :
      1 / (2 * shorEta δ n)
        =
      (n : ℝ)^2 / (2 * δ) :=
    shorEta_inv_two_mul δ hδ n hn1

  have hceil :
      algorithm1ExtraBits (shorEta δ n)
        ≤
      2 * n := by
    dsimp [algorithm1ExtraBits]
    rw [heta]
    exact
      Nat.ceil_le.mpr
        (by
          norm_num
          nlinarith)

  simpa using hceil

/-! =========================================================
    Correctness setup to gate-count layout
========================================================= -/

/-!
This bridge is where the public `ShorApproxSetup` used by correctness becomes
the internal `ShorGateCountLayout cWork`.  It combines the Shor register-width
facts, Algorithm 1's exact work-width formula, and the externally supplied
register-disjointness layout from the setup.
-/

lemma ShorApproxSetup.toShorGateCountLayout
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cWork : ℕ)
    (hcWork : 1 ≤ cWork)
    (inst : ShorOrderFindingInstance)
    (work : Reg)
    (flag : ℕ)
    (b0 : qs.Basis)
    (hsetup :
      ShorApproxSetup
        qs η
        inst.a inst.N
        inst.x inst.y
        work flag b0)
    (hExtra :
      algorithm1ExtraBits η
        ≤
      (cWork - 1) * regSize inst.y) :
    ShorGateCountLayout
      cWork
      (regSize inst.y)
      inst.x inst.y work flag := by

  have hN : 1 < inst.N := by
    rcases inst.range with ⟨ha0, haN⟩
    omega

  have hxLower :
      regSize inst.y ≤ regSize inst.x :=
    shor_y_width_le_x_width
      inst.N
      inst.x
      inst.y
      hN
      inst.x_width
      inst.y_width

  have hxUpper :
      regSize inst.x ≤ 2 * regSize inst.y :=
    shor_x_width_le_two_y_width
      inst.N
      inst.x
      inst.y
      hN
      inst.x_width
      inst.y_width

  have hworkLower :
      regSize inst.y ≤ regSize work :=
    data_width_le_work_width
      hsetup.work_precision

  have hworkUpper :
      regSize work ≤ cWork * regSize inst.y :=
    Algorithm1Precision.work_width_le_mul
      hcWork
      hsetup.work_precision
      hExtra

  exact
    ⟨ rfl,
      hxLower,
      hxUpper,
      hworkLower,
      hworkUpper,
      hsetup.register_layout ⟩

/-! =========================================================
    Final component assembly
========================================================= -/

/-!
The final assembly chooses the fixed workspace factor implied by
`shorEta δ n = δ/n²`, invokes the three generalized component bounds with
that same factor, derives `ShorGateCountLayout` from each `ShorApproxSetup`,
and finishes with the exponent comparison.
-/

/--
The PhaseProduct, controlled PhaseProduct, and QFT bounds imply the complete
`O(n^(2 + ε))` Shor gate-count bound whenever

  phaseProductExponent k ≤ 1 + ε.
-/
theorem shorGateCountBound_of_components
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (ε δ : ℝ)
    (hδ : 0 < δ)
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hExponent :
      phaseProductExponent k ≤ 1 + ε)
    (hPhase :
      PhaseProductGateCountBound
        (Basis := qs.Basis) k hk ops)
    (hCPhase :
      CPhaseProductGateCountBound
        (Basis := qs.Basis) k hk ops)
    (hQFT :
      QFTGateCountBound
        (Basis := qs.Basis) k hk ops) :
    ShorGateCountBound qs ε δ k hk ops := by

  rcases
      algorithm1ExtraBits_shorEta_eventually_linear
        δ hδ
    with
      ⟨cWork, hcWork, nExtra, hnExtra, hExtraFits⟩

  rcases
      cmodMulInPlaceCore_gateCount_phase_bound
        qs cWork hcWork k hk ops hPhase hCPhase hQFT
    with
      ⟨A, hA, nCore, hnCore, hCore⟩

  rcases
      modExpApproxValid_gateCount_phase_bound_of_core
        qs cWork hcWork k hk ops
        A hA nCore hnCore hCore
    with
      ⟨B, hB, nModExp, hnModExp, hModExp⟩

  rcases
      orderFindingApproxLow_gateCount_phase_bound
        qs k hk ops
        cWork hcWork
        hQFT
        B hB nModExp hnModExp hModExp
    with
      ⟨C, hC, nOrder, hnOrder, hOrderFinding⟩

  let nFinal : ℕ :=
    max nOrder nExtra

  have hnFinal : 1 ≤ nFinal := by
    dsimp [nFinal]
    omega

  refine ⟨C, hC, nFinal, hnFinal, ?_⟩

  intro inst work flag b0
  dsimp
  intro hn hsetup

  let n : ℕ :=
    regSize inst.y

  have hnOrder' : nOrder ≤ n := by
    dsimp [nFinal, n] at hn
    omega

  have hnExtra' : nExtra ≤ n := by
    dsimp [nFinal, n] at hn
    omega

  have hn_one : 1 ≤ n :=
    le_trans hnOrder hnOrder'

  have hExtra :
      algorithm1ExtraBits (shorEta δ (regSize inst.y))
        ≤
      (cWork - 1) * regSize inst.y :=
    hExtraFits (regSize inst.y) (by
      simpa [n] using hnExtra')

  have hLayout :
      ShorGateCountLayout
        cWork n
        inst.x inst.y work flag := by
    dsimp [n]
    exact
      ShorApproxSetup.toShorGateCountLayout
        cWork hcWork
        inst work flag b0 hsetup hExtra

  have hPreliminary :
      (shorOrderFindingGateCount
          qs k hk ops inst.a inst.N inst.x inst.y work flag : ℝ)
        ≤
      C *
        Real.rpow
          (n : ℝ)
          (1 + phaseProductExponent k) :=
    hOrderFinding
      n inst.a inst.N inst.x inst.y work flag hnOrder' hLayout

  have hRate :
      Real.rpow
          (n : ℝ)
          (1 + phaseProductExponent k)
        ≤
      shorGateRate ε n :=
    phaseProduct_succ_rate_le_shorGateRate
      ε k n hn_one hExponent

  exact
    hPreliminary.trans
      (mul_le_mul_of_nonneg_left
        hRate
        (le_of_lt hC))


/-! =========================================================
    Every valid table
========================================================= -/

/-!
This last section packages the component theorem for any interpolation table
that satisfies `PhaseProductProgramOK`, supplying the PhaseProduct,
controlled PhaseProduct, and QFT component bounds from the table assumptions.
-/

/--
For a fixed suitable `k`, every interpolation table satisfying
`PhaseProductProgramOK` gives the complete Shor gate-count bound.

The constant in `ShorGateCountBound` may depend on `ops`.
-/
theorem shorGateCountBound_of_programOK
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (ε δ : ℝ)
    (hδ : 0 < δ)
    (k : ℕ)
    (hk : 1 < k)
    (hExponent : phaseProductExponent k ≤ 1 + ε) :
    ∀ ops : Prog k,
      PhaseProductProgramOK k hk ops →
      ShorGateCountBound qs ε δ k hk ops := by
  intro ops hops

  apply
    shorGateCountBound_of_components
      qs ε δ hδ k hk ops hExponent

  · exact
      phaseProductGateCountBound_of_programOK
        (Basis := qs.Basis)
        k hk ops hops

  · exact
      cPhaseProductGateCountBound_of_programOK
        (Basis := qs.Basis)
        k hk ops hops

  · exact
      qftGateCountBound_of_programOK
        (Basis := qs.Basis)
        k hk ops hops

lemma exists_k_phaseProductExponent_le
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ k : ℕ,
      1 < k ∧
      phaseProductExponent k ≤ 1 + ε := by
  obtain ⟨m : ℕ, hm⟩ :=
    exists_nat_gt (1 / ε)

  let k : ℕ := 2 ^ (m + 1)

  have hpowpos :
      0 < 2 ^ m := by
    positivity

  have hk :
      1 < k := by
    dsimp [k]
    rw [pow_succ]
    omega

  have hkR :
      (1 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk

  have hlogk_pos :
      0 < Real.log (k : ℝ) :=
    Real.log_pos hkR

  have hm_succ :
      1 / ε < ((m + 1 : ℕ) : ℝ) := by
    calc
      1 / ε < (m : ℝ) := hm
      _ < ((m + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self m

  have hmε :
      1 < ((m + 1 : ℕ) : ℝ) * ε := by
    exact (div_lt_iff₀ hε).mp hm_succ

  have hk_cast :
      (k : ℝ) = (2 : ℝ) ^ (m + 1) := by
    simp [k]

  have hlogk :
      Real.log (k : ℝ)
        =
      ((m + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [hk_cast, Real.log_pow]

  have hlog2_pos :
      0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)

  have hlog2_le :
      Real.log 2
        ≤
      ε * Real.log (k : ℝ) := by
    have hmε_le :
        (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * ε :=
      le_of_lt hmε

    calc
      Real.log 2
          =
        1 * Real.log 2 := by
          ring

      _ ≤
        (((m + 1 : ℕ) : ℝ) * ε) *
          Real.log 2 :=
        mul_le_mul_of_nonneg_right
          hmε_le
          (le_of_lt hlog2_pos)

      _ =
        ε * Real.log (k : ℝ) := by
          rw [hlogk]
          ring
  have hq_pos_nat :
      0 < q k := by
    unfold q
    omega

  have hq_lt_nat :
      q k < 2 * k := by
    unfold q
    omega

  have hq_pos :
      0 < (q k : ℝ) := by
    exact_mod_cast hq_pos_nat

  have hq_lt :
      (q k : ℝ) < 2 * (k : ℝ) := by
    exact_mod_cast hq_lt_nat

  have hlogq_le :
      Real.log (q k : ℝ)
        ≤
      Real.log (2 * (k : ℝ)) := by
    exact
      le_of_lt
        (Real.log_lt_log hq_pos hq_lt)

  refine ⟨k, hk, ?_⟩

  unfold phaseProductExponent
  rw [div_le_iff₀ hlogk_pos]

  calc
    Real.log (q k : ℝ)
        ≤
      Real.log (2 * (k : ℝ)) :=
        hlogq_le

    _ =
      Real.log 2 + Real.log (k : ℝ) := by
        rw [Real.log_mul
          (by norm_num : (2 : ℝ) ≠ 0)
          (by positivity : (k : ℝ) ≠ 0)]

    _ ≤
      (1 + ε) * Real.log (k : ℝ) := by
        nlinarith [hlog2_le]
/--
For every interpolation arity `k > 1`, there exists a generated
interpolation program satisfying `PhaseProductProgramOK`.

The witness is the canonical program produced by `genOpsWithProduct`
on `genInterpolationPoints k`.
-/
theorem exists_phaseProductProgramOK
    (k : ℕ)
    (hk : 1 < k) :
    ∃ ops : Prog k,
      PhaseProductProgramOK k hk ops := by

  have hk0 : 0 < k := by
    omega

  refine
    ⟨genOpsWithProduct (k := k)  hk0  (genInterpolationPoints k), ?_⟩

  unfold PhaseProductProgramOK
  dsimp

  constructor

  · simpa using genInterpolationPoints_good k

  constructor

  · exact genOpsWithProduct_ProgConsumesPtsSafe (k := k) hk0 (genInterpolationPoints k)

  constructor

  · exact genOpsWithProduct_returns_to_original (k := k) hk0 (genInterpolationPoints k)

  · simpa [genInterpolationPoints, q] using
      phaseProductCount_genOpsWithProduct
        (k := k)
        hk0
        (genInterpolationPoints k)

theorem exists_shorGateCountBound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (ε δ : ℝ)
    (hδ : 0 < δ)
    (hε : 0 < ε) :
    ∃ k : ℕ,
    ∃ hk : 1 < k,
    ∃ ops : Prog k,
      PhaseProductProgramOK k hk ops ∧
      ShorGateCountBound qs ε δ k hk ops := by
  rcases exists_k_phaseProductExponent_le ε hε with
    ⟨k, hk, hExponent⟩

  rcases exists_phaseProductProgramOK k hk with
    ⟨ops, hops⟩

  refine ⟨k, hk, ops, hops, ?_⟩

  exact
    shorGateCountBound_of_programOK
      qs ε δ hδ k hk hExponent
      ops hops

/--
For every `ε > 0`, there is a recursion parameter `k` such that every
interpolation program satisfying `PhaseProductProgramOK` gives the complete
Shor gate-count bound `O(n^(2 + ε))`.

The selected `k` depends only on `ε`. The constant and threshold inside
`ShorGateCountBound` may depend on `δ`, `k`, and `ops`.
-/
theorem exists_k_shorGateCountBound_of_programOK
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (ε δ : ℝ)
    (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∃ (k : ℕ) (hk : 1 < k),
      ∀ ops : Prog k,
        PhaseProductProgramOK k hk ops →
        ShorGateCountBound qs ε δ k hk ops := by
  rcases exists_k_phaseProductExponent_le ε hε with ⟨k, hk, hExponent⟩
  exact ⟨k, hk, shorGateCountBound_of_programOK qs ε δ hδ k hk hExponent⟩
