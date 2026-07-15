import FastMultiplication.ShorVerification.GateCount.Definitions

open Shor

/-! ---------------------------------------------------------
    Exact QFT
--------------------------------------------------------- -/

/--
For fixed `k` and interpolation program `ops`, the recursively lowered exact
QFT has the same exponent as PhaseProduct:

  O(n^(log_k(2k - 1))).

This corresponds to the recurrence consisting of two half-sized QFTs, one
PhaseProduct between the two halves, and a linear-cost radix reversal.
-/
def QFTGateCountBound
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ r : Reg,
      WellFormedReg r →
      n₀ ≤ regSize r →
      (LowGate.gateCount shorGateCostModel
          (lowerGate
            (Basis := Basis)
            k hk ops
            (Gate.QFT r)) : ℝ)
        ≤
      C * phaseProductSafeRate k (regSize r)

/-! =========================================================
    Exact-QFT gate-count proof
========================================================= -/

/-! ---------------------------------------------------------
    The balanced QFT split used by the paper
--------------------------------------------------------- -/

/-- The paper chooses the split point `m = n / 2`. -/
def qftHalfWidth (r : Reg) : ℕ :=
  regSize r / 2

/-- The first half of the QFT register. -/
def qftLeftReg (r : Reg) : Reg :=
  { lo := r.lo
    size := qftHalfWidth r }

/-- The second half of the QFT register. -/
def qftRightReg (r : Reg) : Reg :=
  { lo := r.lo + qftHalfWidth r
    size := regSize r - qftHalfWidth r }

/-- Gate count of the recursively lowered exact QFT. -/
noncomputable def loweredQFTGateCount
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : Reg) : ℕ :=
  LowGate.gateCount
    shorGateCostModel
    (lowerGate
      (Basis := Basis)
      k hk ops
      (Gate.QFT r))

/--
Gate count of the PhaseProduct joining the two halves of one QFT recursion
node.
-/
noncomputable def qftSplitPhaseGateCount
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : Reg) : ℕ :=
  LowGate.gateCount
    shorGateCostModel
    (lowerGate
      (Basis := Basis)
      k hk ops
      (Gate.PhaseProd
        (qftPhi (regSize r))
        (qftLeftReg r)
        (qftRightReg r)))

/-- Gate count of the final radix reversal at one QFT recursion node. -/
def qftSplitRadixGateCount (r : Reg) : ℕ :=
  LowGate.gateCount
    shorGateCostModel
    (LowGate.RadixReverse r (qftHalfWidth r))


/-! ---------------------------------------------------------
    Step 1: geometry of the half split
--------------------------------------------------------- -/

/-- The left register has width `floor(n / 2)`. -/
@[simp]
lemma regSize_qftLeftReg (r : Reg) :
    regSize (qftLeftReg r) = regSize r / 2 := by
  rfl

/-- The right register has width `n - floor(n / 2) = ceil(n / 2)`. -/
@[simp]
lemma regSize_qftRightReg (r : Reg) :
    regSize (qftRightReg r) =
      regSize r - regSize r / 2 := by
  rfl

/-- The two QFT halves are disjoint. -/
lemma qftSplit_disjoint (r : Reg) :
    Disjoint (qftLeftReg r) (qftRightReg r) := by
  left
  unfold qftLeftReg qftRightReg qftHalfWidth Reg.hi
  simp [regSize]

/-- Splitting a well-formed register produces two well-formed registers. -/
lemma qftSplit_wellFormed
    (r : Reg)
    (_hr : WellFormedReg r) :
    WellFormedReg (qftLeftReg r) ∧
    WellFormedReg (qftRightReg r) := by
  constructor <;>
    simp [WellFormedReg, qftLeftReg, qftRightReg, qftHalfWidth, Reg.hi]

/--
Both recursive QFT calls are strictly smaller whenever the parent has at
least two qubits.
-/
lemma qftSplit_strictly_smaller
    (r : Reg)
    (hsize : 2 ≤ regSize r) :
    regSize (qftLeftReg r) < regSize r ∧
    regSize (qftRightReg r) < regSize r := by
  constructor
  · simp [qftLeftReg, qftHalfWidth]
    exact Nat.div_lt_self (by omega) (by omega)
  · simp [qftRightReg, qftHalfWidth]
    have hpos : 0 < regSize r / 2 :=
      Nat.div_pos hsize (by omega)
    omega

/-- The larger half has size `ceil(n / 2)`. -/
lemma qftSplit_max_size (r : Reg) :
    max
        (regSize (qftLeftReg r))
        (regSize (qftRightReg r))
      =
    regSize r - regSize r / 2 := by
  have htwice :
      2 * (regSize r / 2) ≤ regSize r := by
    simpa using Nat.mul_div_le (regSize r) 2
  have hhalf :
      regSize r / 2 ≤ regSize r - regSize r / 2 := by
    omega
  simp [qftLeftReg, qftRightReg, qftHalfWidth, max_eq_right hhalf]

/--
The PhaseProduct joining the two halves acts on registers whose maximum width
lies between `floor(n / 2)` and `n`.
-/
lemma qftSplit_phase_size_bounds (r : Reg) :
    regSize r / 2
        ≤
      max
        (regSize (qftLeftReg r))
        (regSize (qftRightReg r))
    ∧
      max
        (regSize (qftLeftReg r))
        (regSize (qftRightReg r))
        ≤ regSize r := by
  constructor
  · exact Nat.le_max_left _ _
  · rw [qftSplit_max_size]
    exact Nat.sub_le _ _


/-! ---------------------------------------------------------
    Step 2: exact gate-count decomposition
--------------------------------------------------------- -/

/--
The right recursive call produced by one QFT recursion node is exactly the
lowering of the right half register.

Both sides reduce to `lowerQFTAux` applied to `qftRightReg r` at its own width
`regSize r - qftHalfWidth r`, so the equality is definitional once `lowerGate`
and `lowerQFT` are unfolded.
-/
lemma lowerQFT_right_eq
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : Reg) :
    LowGate.gateCount shorGateCostModel
        (lowerQFTAux (Basis := Basis) k hk ops
          (regSize r - qftHalfWidth r) (qftRightReg r))
      =
    loweredQFTGateCount (Basis := Basis) k hk ops (qftRightReg r) := by
  unfold loweredQFTGateCount
  rw [lowerGate, lowerQFT]
  rfl

/--
The left recursive call produced by one QFT recursion node is exactly the
lowering of the left half register.

As with `lowerQFT_right_eq`, both sides reduce to `lowerQFTAux` applied to
`qftLeftReg r` at its own width `qftHalfWidth r`.
-/
lemma lowerQFT_left_eq
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : Reg) :
    LowGate.gateCount shorGateCostModel
        (lowerQFTAux (Basis := Basis) k hk ops
          (qftHalfWidth r) (qftLeftReg r))
      =
    loweredQFTGateCount (Basis := Basis) k hk ops (qftLeftReg r) := by
  unfold loweredQFTGateCount
  rw [lowerGate, lowerQFT]
  rfl

/--
The PhaseProduct emitted inside one QFT recursion node (via `lowerPhaseProd`)
has the same gate count as the public `Gate.PhaseProd` lowering used by
`qftSplitPhaseGateCount`.

Both lower `Gate.PhaseProd φ x z` to the same recursive signed PhaseProduct: the
initial-size cutoff of `lowerPhaseProd` is exactly `phaseInputSize` of the two
unsigned views, which is the branch condition `lowerSignedPhaseProd` uses.
-/
lemma lowerGate_split_phase_eq
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : Reg) :
    LowGate.gateCount shorGateCostModel
        (lowerPhaseProd (Basis := Basis) k hk φ x z ops)
      =
    LowGate.gateCount shorGateCostModel
        (lowerGate (Basis := Basis) k hk ops (Gate.PhaseProd φ x z)) := by
  rw [lowerGate_PhaseProd_gateCount_eq_signed_unsignedView]
  unfold lowerPhaseProd
  simp only [Gate.PhaseProd, signedPhaseProductGateCount, lowerSignedPhaseProd,
    lowerGateRec, LowGate.gateCount, shorGateCostModel, phaseProductCostModel,
    Nat.zero_add, Nat.add_zero]

/--
This is the gate-count form of the paper's exact-QFT decomposition:

  QFT(right);
  PhaseProduct(left, right);
  QFT(left);
  RadixReverse.

It follows by unfolding `lowerGate`, `lowerQFT`, and `lowerQFTAux`.
-/
lemma loweredQFTGateCount_split
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : Reg)
    (hsize : 2 ≤ regSize r) :
    loweredQFTGateCount
        (Basis := Basis) k hk ops r
      =
    loweredQFTGateCount
        (Basis := Basis) k hk ops (qftRightReg r)
      +
    qftSplitPhaseGateCount
        (Basis := Basis) k hk ops r
      +
    loweredQFTGateCount
        (Basis := Basis) k hk ops (qftLeftReg r)
      +
    qftSplitRadixGateCount r := by
  -- One step of the `lowerQFTAux` recurrence, phrased with the balanced-split
  -- registers `qftLeftReg`/`qftRightReg` rather than the internal `let`s.
  have hsplit :
      lowerQFTAux (Basis := Basis) k hk ops (regSize r) r
        = (lowerQFTAux (Basis := Basis) k hk ops
              (regSize r - qftHalfWidth r) (qftRightReg r)) ;;
          (lowerPhaseProd (Basis := Basis) k hk (qftPhi (regSize r))
              (qftLeftReg r) (qftRightReg r) ops) ;;
          (lowerQFTAux (Basis := Basis) k hk ops
              (qftHalfWidth r) (qftLeftReg r)) ;;
          (LowGate.RadixReverse r (qftHalfWidth r)) := by
    obtain ⟨n, hn⟩ : ∃ n, regSize r = n + 2 := ⟨regSize r - 2, by omega⟩
    rw [hn, lowerQFTAux]
    simp only [qftLeftReg, qftRightReg, qftHalfWidth, hn]
  -- Expand the parent gate count into the four sequential contributions.
  have hLHS :
      loweredQFTGateCount (Basis := Basis) k hk ops r
        = LowGate.gateCount shorGateCostModel
            (lowerQFTAux (Basis := Basis) k hk ops
                (regSize r - qftHalfWidth r) (qftRightReg r))
          + LowGate.gateCount shorGateCostModel
            (lowerPhaseProd (Basis := Basis) k hk (qftPhi (regSize r))
                (qftLeftReg r) (qftRightReg r) ops)
          + LowGate.gateCount shorGateCostModel
            (lowerQFTAux (Basis := Basis) k hk ops (qftHalfWidth r) (qftLeftReg r))
          + LowGate.gateCount shorGateCostModel
            (LowGate.RadixReverse r (qftHalfWidth r)) := by
    rw [loweredQFTGateCount, lowerGate, lowerQFT, hsplit]
    simp only [LowGate.gateCount_seq]
    omega
  -- The internal PhaseProduct matches the public `qftSplitPhaseGateCount`.
  have hB :
      LowGate.gateCount shorGateCostModel
          (lowerPhaseProd (Basis := Basis) k hk (qftPhi (regSize r))
              (qftLeftReg r) (qftRightReg r) ops)
        = qftSplitPhaseGateCount (Basis := Basis) k hk ops r :=
    lowerGate_split_phase_eq k hk ops (qftPhi (regSize r)) (qftLeftReg r) (qftRightReg r)
  rw [hLHS, lowerQFT_right_eq, lowerQFT_left_eq, hB]
  rfl

/-! ---------------------------------------------------------
    Step 3: bounding the nonrecursive work
--------------------------------------------------------- -/

/-- The PhaseProduct comparison function is monotone in its size argument. -/
lemma phaseProductGateRate_mono
    (k : ℕ)
    (hk : 1 < k)
    {m n : ℕ}
    (hmn : m ≤ n) :
    phaseProductGateRate k m ≤
      phaseProductGateRate k n := by
  have hα :
      0 ≤ phaseProductExponent k := by
    linarith [one_lt_phaseProductExponent k hk]

  unfold phaseProductGateRate

  exact
    Real.rpow_le_rpow
      (by positivity)
      (by exact_mod_cast hmn)
      hα

/--
Because the PhaseProduct bound is eventual, choose the parent QFT threshold
large enough that its half-sized PhaseProduct operands are past the
PhaseProduct threshold.

The PhaseProduct cost at one QFT recursion node is then bounded by the parent's

  n^(phaseProductExponent k)

rate.
-/
lemma qftSplitPhaseGateCount_eventually_le
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hPhase :
      PhaseProductGateCountBound
        (Basis := Basis) k hk ops) :
    ∃ Cφ : ℝ, 0 < Cφ ∧
    ∃ Nφ : ℕ, 2 ≤ Nφ ∧
      ∀ r : Reg,
        WellFormedReg r →
        Nφ ≤ regSize r →
        (qftSplitPhaseGateCount
            (Basis := Basis) k hk ops r : ℝ)
          ≤
        Cφ * phaseProductGateRate k (regSize r) := by
  rcases hPhase with ⟨Cφ, hCφ, n₀, hn₀, hPhase⟩
  refine ⟨Cφ, hCφ, max 2 (2 * n₀), by omega, ?_⟩
  intro r hr hn

  have hleftLarge : n₀ ≤ regSize r / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    omega

  have hchildLarge :
      n₀ ≤
        max
          (regSize (qftLeftReg r))
          (regSize (qftRightReg r)) := by
    rw [regSize_qftLeftReg]
    exact hleftLarge.trans (Nat.le_max_left _ _)

  have hwf := qftSplit_wellFormed r hr

  have hnode :=
    hPhase
      (qftPhi (regSize r))
      (qftLeftReg r)
      (qftRightReg r)
      hwf.1
      hwf.2
      (qftSplit_disjoint r)
      hchildLarge

  have hsizeLe :
      max
          (regSize (qftLeftReg r))
          (regSize (qftRightReg r))
        ≤ regSize r :=
    (qftSplit_phase_size_bounds r).2

  have hrate :=
    phaseProductGateRate_mono k hk hsizeLe

  unfold qftSplitPhaseGateCount

  exact hnode.trans
    (mul_le_mul_of_nonneg_left hrate (le_of_lt hCφ))

/--
A linear function is eventually bounded by `n^α` when `α > 1`.

This is the analytic fact used to absorb radix reversal into the
PhaseProduct-rate term.
-/
lemma linear_eventually_le_phaseProductGateRate
    (k : ℕ)
    (hk : 1 < k) :
    ∃ C : ℝ, 0 < C ∧
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        (n : ℝ)
          ≤
        C * phaseProductGateRate k n := by
  refine ⟨1, by norm_num, 1, by omega, ?_⟩
  intro n hn
  simpa [phaseProductGateRate] using
    natCast_le_phaseProduct_rpow k hk hn

/--
Radix reversal costs only linearly many gates, so it is eventually bounded by
the PhaseProduct rate because `phaseProductExponent k > 1`.
-/
lemma qftSplitRadixGateCount_eventually_le
    (k : ℕ)
    (hk : 1 < k) :
    ∃ Cr : ℝ, 0 < Cr ∧
    ∃ Nr : ℕ, 1 ≤ Nr ∧
      ∀ r : Reg,
        WellFormedReg r →
        Nr ≤ regSize r →
        (qftSplitRadixGateCount r : ℝ)
          ≤
        Cr * phaseProductGateRate k (regSize r) := by
  refine ⟨3, by norm_num, 1, by omega, ?_⟩
  intro r _hr hn

  have hcost :
      qftSplitRadixGateCount r ≤ 3 * regSize r := by
    unfold qftSplitRadixGateCount qftHalfWidth
    simp [LowGate.gateCount, shorGateCostModel, phaseProductCostModel,
      radixReverseGateCount]
    have hdiv :
        regSize r / 2 / 2 ≤ regSize r := by
      exact (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
    exact hdiv

  have hlinear :
      ((3 * regSize r : ℕ) : ℝ)
        ≤
      (3 : ℝ) * phaseProductGateRate k (regSize r) := by
    have hn' :
        (regSize r : ℝ)
          ≤
        phaseProductGateRate k (regSize r) := by
      simpa [phaseProductGateRate] using
        natCast_le_phaseProduct_rpow k hk hn
    norm_num
    nlinarith

  have hcostR :
      (qftSplitRadixGateCount r : ℝ)
        ≤
      ((3 * regSize r : ℕ) : ℝ) := by
    exact_mod_cast hcost

  exact hcostR.trans hlinear

/--
Combining the exact split, the PhaseProduct bound, and the linear radix bound
gives the one-level QFT recurrence

  Q(n) ≤ Q(ceil(n/2)) + Q(floor(n/2)) + A n^α.
-/
lemma loweredQFTGateCount_one_level_recurrence
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hPhase :
      PhaseProductGateCountBound
        (Basis := Basis) k hk ops) :
    ∃ A : ℝ, 0 < A ∧
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ r : Reg,
        WellFormedReg r →
        N ≤ regSize r →
        (loweredQFTGateCount
            (Basis := Basis) k hk ops r : ℝ)
          ≤
        (loweredQFTGateCount
            (Basis := Basis) k hk ops (qftRightReg r) : ℝ)
          +
        (loweredQFTGateCount
            (Basis := Basis) k hk ops (qftLeftReg r) : ℝ)
          +
        A * phaseProductGateRate k (regSize r) := by
  rcases
      qftSplitPhaseGateCount_eventually_le
        (Basis := Basis) k hk ops hPhase with
    ⟨Cφ, hCφ, Nφ, hNφ, hPhaseNode⟩

  rcases
      qftSplitRadixGateCount_eventually_le k hk with
    ⟨Cr, hCr, Nr, hNr, hRadixNode⟩

  refine
    ⟨Cφ + Cr, by linarith,
      max Nφ Nr, by omega, ?_⟩

  intro r hr hn

  have hnφ : Nφ ≤ regSize r :=
    le_trans (Nat.le_max_left Nφ Nr) hn

  have hnr : Nr ≤ regSize r :=
    le_trans (Nat.le_max_right Nφ Nr) hn

  have htwo : 2 ≤ regSize r :=
    le_trans hNφ hnφ

  have hsplit :
      (loweredQFTGateCount
          (Basis := Basis) k hk ops r : ℝ)
        =
      (loweredQFTGateCount
          (Basis := Basis) k hk ops (qftRightReg r) : ℝ)
        +
      (qftSplitPhaseGateCount
          (Basis := Basis) k hk ops r : ℝ)
        +
      (loweredQFTGateCount
          (Basis := Basis) k hk ops (qftLeftReg r) : ℝ)
        +
      (qftSplitRadixGateCount r : ℝ) := by
    exact_mod_cast
      loweredQFTGateCount_split
        (Basis := Basis) k hk ops r htwo

  have hphase :=
    hPhaseNode r hr hnφ

  have hradix :=
    hRadixNode r hr hnr

  calc
    (loweredQFTGateCount
        (Basis := Basis) k hk ops r : ℝ)
        =
      (loweredQFTGateCount
          (Basis := Basis) k hk ops (qftRightReg r) : ℝ)
        +
      (qftSplitPhaseGateCount
          (Basis := Basis) k hk ops r : ℝ)
        +
      (loweredQFTGateCount
          (Basis := Basis) k hk ops (qftLeftReg r) : ℝ)
        +
      (qftSplitRadixGateCount r : ℝ) := hsplit

    _ ≤
      (loweredQFTGateCount
          (Basis := Basis) k hk ops (qftRightReg r) : ℝ)
        +
      Cφ * phaseProductGateRate k (regSize r)
        +
      (loweredQFTGateCount
          (Basis := Basis) k hk ops (qftLeftReg r) : ℝ)
        +
      Cr * phaseProductGateRate k (regSize r) := by
        linarith

    _ =
      (loweredQFTGateCount
          (Basis := Basis) k hk ops (qftRightReg r) : ℝ)
        +
      (loweredQFTGateCount
          (Basis := Basis) k hk ops (qftLeftReg r) : ℝ)
        +
      (Cφ + Cr) *
        phaseProductGateRate k (regSize r) := by
        ring


/-! ---------------------------------------------------------
    Step 4: finite base cases
--------------------------------------------------------- -/

/--
The PhaseProduct occurring in a QFT node has uniformly bounded cost when the
parent QFT width is bounded.
-/
lemma qftSplitPhaseGateCount_bounded_on_bounded_sizes
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (N : ℕ) :
    ∃ P : ℕ,
      ∀ r : Reg,
        regSize r ≤ N →
        qftSplitPhaseGateCount
            (Basis := Basis) k hk ops r
          ≤ P := by
  rcases
      signedPhaseProductGateCount_bounded_on_bounded_inputs
        (Basis := Basis)
        k hk ops (N + 1) with
    ⟨P, hP⟩

  refine ⟨P, ?_⟩
  intro r hr

  unfold qftSplitPhaseGateCount

  rw [
    lowerGate_PhaseProd_gateCount_eq_signed_unsignedView
      (Basis := Basis)
      k hk ops
      (qftPhi (regSize r))
      (qftLeftReg r)
      (qftRightReg r)
  ]

  apply hP

  rw [phaseInputSize_unsignedView]

  have hmax :
      max
          (regSize (qftLeftReg r))
          (regSize (qftRightReg r))
        ≤ N :=
    (qftSplit_phase_size_bounds r).2.trans hr

  omega


/-- Radix reversal at a QFT node has linear gate count. -/
lemma qftSplitRadixGateCount_le
    (r : Reg) :
    qftSplitRadixGateCount r ≤
      3 * regSize r := by
  unfold qftSplitRadixGateCount
  unfold qftHalfWidth

  simp [
    LowGate.gateCount,
    shorGateCostModel,
    phaseProductCostModel,
    radixReverseGateCount
  ]

  have hdiv :
      regSize r / 2 / 2 ≤ regSize r :=
    (Nat.div_le_self _ _).trans
      (Nat.div_le_self _ _)

  exact hdiv

/--
For each fixed size cutoff, all QFT circuits below that cutoff have a uniform
gate-count bound.

This handles the finitely many leaves where either the QFT recursion stops or
the PhaseProduct asymptotic bound has not yet become applicable.
-/
lemma loweredQFTGateCount_bounded_on_bounded_sizes
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (N : ℕ) :
    ∃ D : ℕ,
      ∀ r : Reg,
        WellFormedReg r →
        regSize r ≤ N →
        loweredQFTGateCount
            (Basis := Basis) k hk ops r
          ≤ D := by
    induction N with
  | zero =>
      refine ⟨0, ?_⟩
      intro r _hr hsize

      have hr0 :
          regSize r = 0 := by
        omega

      simp [
        loweredQFTGateCount,
        lowerGate,
        lowerQFT,
        hr0,
        lowerQFTAux
      ]

  | succ N ih =>
      rcases ih with ⟨D, hD⟩

      rcases
          qftSplitPhaseGateCount_bounded_on_bounded_sizes
            (Basis := Basis)
            k hk ops (N + 1) with
        ⟨P, hP⟩

      let B : ℕ :=
        max D
          (2 * D + P + 3 * (N + 1))

      refine ⟨B, ?_⟩
      intro r hr hsize

      by_cases hprevious :
          regSize r ≤ N

      · exact
          (hD r hr hprevious).trans
            (Nat.le_max_left _ _)

      · have hrSize :
            regSize r = N + 1 := by
          omega

        by_cases htwo :
            2 ≤ regSize r

        · have hhalves :=
            qftSplit_wellFormed r hr

          have hsmaller :=
            qftSplit_strictly_smaller r htwo

          have hleftN :
              regSize (qftLeftReg r) ≤ N := by
            omega

          have hrightN :
              regSize (qftRightReg r) ≤ N := by
            omega

          have hleftCost :=
            hD
              (qftLeftReg r)
              hhalves.1
              hleftN

          have hrightCost :=
            hD
              (qftRightReg r)
              hhalves.2
              hrightN

          have hphaseCost :=
            hP r hsize

          have hradixCost :
              qftSplitRadixGateCount r
                ≤ 3 * (N + 1) := by
            exact
              (qftSplitRadixGateCount_le r).trans
                (Nat.mul_le_mul_left 3 hsize)

          rw [
            loweredQFTGateCount_split
              (Basis := Basis)
              k hk ops r htwo
          ]

          dsimp [B]

          apply
            le_trans
              (show
                loweredQFTGateCount
                    (Basis := Basis)
                    k hk ops (qftRightReg r)
                  +
                qftSplitPhaseGateCount
                    (Basis := Basis)
                    k hk ops r
                  +
                loweredQFTGateCount
                    (Basis := Basis)
                    k hk ops (qftLeftReg r)
                  +
                qftSplitRadixGateCount r
                  ≤
                2 * D + P + 3 * (N + 1) by
                  omega)

          exact Nat.le_max_right _ _

        · have hrOne :
              regSize r = 1 := by
            omega

          have hcost :
              loweredQFTGateCount
                  (Basis := Basis)
                  k hk ops r
                = 1 := by
            simp [
              loweredQFTGateCount,
              lowerGate,
              lowerQFT,
              hrOne,
              lowerQFTAux
            ]

          rw [hcost]

          dsimp [B]

          apply
            le_trans
              (show
                1 ≤
                  2 * D + P + 3 * (N + 1) by
                omega)

          exact Nat.le_max_right _ _


/-! ---------------------------------------------------------
    Step 5: solve the binary recurrence
--------------------------------------------------------- -/

/--
The two half-size recursive rates contract by a fixed factor below one because

  phaseProductExponent k > 1.

This is the precise fact distinguishing the PhaseProduct toll from the linear
binary-recursion contribution.
-/
lemma qft_half_rate_contraction
    (k : ℕ)
    (_hk : 1 < k)
    (hα : 1 < phaseProductExponent k) :
    ∃ ρ : ℝ,
      0 ≤ ρ ∧ ρ < 1 ∧
      ∀ n : ℕ,
        2 ≤ n →
        phaseProductGateRate k (n / 2)
          +
        phaseProductGateRate k (n - n / 2)
          ≤
        ρ * phaseProductGateRate k n := by
  let α : ℝ :=
  phaseProductExponent k

  let ρ : ℝ :=
    Real.rpow (1 / 3 : ℝ) α
      +
    Real.rpow (2 / 3 : ℝ) α

  have hα' :
      1 < α := by
    simpa [α] using hα

  have hρnonneg :
      0 ≤ ρ := by
    dsimp [ρ]
    positivity

  have hthird :
      Real.rpow (1 / 3 : ℝ) α
        < (1 / 3 : ℝ) := by
    exact
      Real.rpow_lt_self_of_lt_one
        (by norm_num)
        (by norm_num)
        hα'

  have htwoThirds :
      Real.rpow (2 / 3 : ℝ) α
        < (2 / 3 : ℝ) := by
    exact
      Real.rpow_lt_self_of_lt_one
        (by norm_num)
        (by norm_num)
        hα'

  have hρlt :
      ρ < 1 := by
    have hsum :
        Real.rpow (1 / 3 : ℝ) α
            + Real.rpow (2 / 3 : ℝ) α
          <
        (1 / 3 : ℝ) + (2 / 3 : ℝ) :=
      add_lt_add hthird htwoThirds
    norm_num at hsum
    simpa [ρ] using hsum

  refine ⟨ρ, hρnonneg, hρlt, ?_⟩

  intro n hn

  let a : ℕ := n / 2
  let b : ℕ := n - a

  have hnpos :
      0 < n := by
    omega

  have haPos :
      0 < a := by
    dsimp [a]
    exact Nat.div_pos hn (by omega)

  have haLe :
      a ≤ n := by
    dsimp [a]
    exact Nat.div_le_self _ _

  have hbPos :
      0 < b := by
    dsimp [b]
    omega

  have hab :
      a + b = n := by
    dsimp [b]
    omega

  have htwoA :
      2 * a ≤ n := by
    dsimp [a]
    simpa using Nat.mul_div_le n 2

  have hmod :
      n % 2 < 2 :=
    Nat.mod_lt n (by omega)

  have hdecomp :
      n % 2 + 2 * a = n := by
    dsimp [a]
    simpa using Nat.mod_add_div n 2

  have hnLeThreeA :
      n ≤ 3 * a := by
    omega

  have hthreeALeTwoN :
      3 * a ≤ 2 * n := by
    omega

  have hnR :
      0 < (n : ℝ) := by
    exact_mod_cast hnpos

  let t : ℝ :=
    (a : ℝ) / (n : ℝ)

  have htLower :
      (1 / 3 : ℝ) ≤ t := by
    dsimp [t]

    have hcast :
        (n : ℝ) ≤ 3 * (a : ℝ) := by
      exact_mod_cast hnLeThreeA

    rw [le_div_iff₀ hnR]
    nlinarith

  have htUpper :
      t ≤ (2 / 3 : ℝ) := by
    dsimp [t]
    apply (div_le_iff₀ hnR).2

    have hcast :
        3 * (a : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast hthreeALeTwoN

    linarith

  let lam : ℝ :=
    2 - 3 * t

  let μ : ℝ :=
    3 * t - 1

  have hlam :
      0 ≤ lam := by
    dsimp [lam]
    linarith

  have hμ :
      0 ≤ μ := by
    dsimp [μ]
    linarith

  have hlamμ :
      lam + μ = 1 := by
    dsimp [lam, μ]
    ring

  have hμlam :
      μ + lam = 1 := by
    linarith [hlamμ]

  have htCombination :
      lam * (1 / 3 : ℝ)
          + μ * (2 / 3 : ℝ)
        =
      t := by
    dsimp [lam, μ]
    ring

  have honeMinusCombination :
      μ * (1 / 3 : ℝ)
          + lam * (2 / 3 : ℝ)
        =
      1 - t := by
    dsimp [lam, μ]
    ring

  have hconvex :=
    convexOn_rpow
      (p := α)
      (le_of_lt hα')

  have htPow :
      Real.rpow t α
        ≤
      lam * Real.rpow (1 / 3 : ℝ) α
        +
      μ * Real.rpow (2 / 3 : ℝ) α := by
    have hc :=
      hconvex.right
        (show (1 / 3 : ℝ) ∈ Set.Ici (0 : ℝ) by norm_num)
        (show (2 / 3 : ℝ) ∈ Set.Ici (0 : ℝ) by norm_num)
        hlam
        hμ
        hlamμ

    rw [← htCombination]
    simpa [smul_eq_mul] using hc

  have honeMinusPow :
      Real.rpow (1 - t) α
        ≤
      μ * Real.rpow (1 / 3 : ℝ) α
        +
      lam * Real.rpow (2 / 3 : ℝ) α := by
    have hc :=
      hconvex.right
        (show (1 / 3 : ℝ) ∈ Set.Ici (0 : ℝ) by norm_num)
        (show (2 / 3 : ℝ) ∈ Set.Ici (0 : ℝ) by norm_num)
        hμ
        hlam
        hμlam

    rw [← honeMinusCombination]
    simpa [smul_eq_mul] using hc

  have hnormalized :
      Real.rpow t α
          + Real.rpow (1 - t) α
        ≤
      ρ := by
    calc
      Real.rpow t α
          + Real.rpow (1 - t) α
          ≤
        (lam * Real.rpow (1 / 3 : ℝ) α
            + μ * Real.rpow (2 / 3 : ℝ) α)
          +
        (μ * Real.rpow (1 / 3 : ℝ) α
            + lam * Real.rpow (2 / 3 : ℝ) α) :=
        add_le_add htPow honeMinusPow

      _ =
        (lam + μ) *
            (Real.rpow (1 / 3 : ℝ) α
              + Real.rpow (2 / 3 : ℝ) α) := by
        ring

      _ = ρ := by
        rw [hlamμ, one_mul]

  have hbCast :
      (b : ℝ) =
        (n : ℝ) - (a : ℝ) := by
    dsimp [b]
    rw [Nat.cast_sub haLe]

  have hbRatio :
      (b : ℝ) / (n : ℝ)
        =
      1 - t := by
    dsimp [t]
    rw [hbCast]
    field_simp [ne_of_gt hnR]

  have htMul :
      t * (n : ℝ) = (a : ℝ) := by
    dsimp [t]
    field_simp [ne_of_gt hnR]

  have honeMinusMul :
      (1 - t) * (n : ℝ) = (b : ℝ) := by
    rw [← hbRatio]
    field_simp [ne_of_gt hnR]

  have htNonneg :
      0 ≤ t := by
    linarith [htLower]

  have honeMinusNonneg :
      0 ≤ 1 - t := by
    linarith [htUpper]

  have haPow :
      Real.rpow (a : ℝ) α
        =
      Real.rpow t α *
        Real.rpow (n : ℝ) α := by
    have hmul :=
      Real.mul_rpow
        htNonneg
        (le_of_lt hnR)
        (z := α)

    rw [htMul] at hmul
    exact hmul

  have hbPow :
      Real.rpow (b : ℝ) α
        =
      Real.rpow (1 - t) α *
        Real.rpow (n : ℝ) α := by
    have hmul :=
      Real.mul_rpow
        honeMinusNonneg
        (le_of_lt hnR)
        (z := α)

    rw [honeMinusMul] at hmul
    exact hmul

  change
    Real.rpow (a : ℝ) α
        + Real.rpow (b : ℝ) α
      ≤
    ρ * Real.rpow (n : ℝ) α

  rw [haPow, hbPow]

  calc
    Real.rpow t α * Real.rpow (n : ℝ) α
        +
      Real.rpow (1 - t) α *
        Real.rpow (n : ℝ) α
        =
      (Real.rpow t α
          + Real.rpow (1 - t) α)
        *
      Real.rpow (n : ℝ) α := by
        ring

    _ ≤
      ρ * Real.rpow (n : ℝ) α :=
        mul_le_mul_of_nonneg_right
          hnormalized
          (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) _)

/--
Strong-induction solution of the exact-QFT recurrence.

The proof chooses `C` large enough to cover the finite base cases and to
satisfy

  ρ C + A ≤ C,

where `ρ < 1` is the contraction factor for the two recursive halves.
-/
lemma qft_binary_recurrence_solution
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (_hα : 1 < phaseProductExponent k)
    (hcontract :
      ∃ ρ : ℝ,
        0 ≤ ρ ∧ ρ < 1 ∧
        ∀ n : ℕ,
          2 ≤ n →
          phaseProductGateRate k (n / 2)
            +
          phaseProductGateRate k (n - n / 2)
            ≤
          ρ * phaseProductGateRate k n)
    (hbase :
      ∀ N : ℕ,
        ∃ D : ℕ,
          ∀ r : Reg,
            WellFormedReg r →
            regSize r ≤ N →
            loweredQFTGateCount
                (Basis := Basis) k hk ops r
              ≤ D)
    (hstep :
      ∃ A : ℝ, 0 < A ∧
      ∃ N : ℕ, 2 ≤ N ∧
        ∀ r : Reg,
          WellFormedReg r →
          N ≤ regSize r →
          (loweredQFTGateCount
              (Basis := Basis) k hk ops r : ℝ)
            ≤
          (loweredQFTGateCount
              (Basis := Basis) k hk ops (qftRightReg r) : ℝ)
            +
          (loweredQFTGateCount
              (Basis := Basis) k hk ops (qftLeftReg r) : ℝ)
            +
          A * phaseProductGateRate k (regSize r)) :
    ∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ r : Reg,
        WellFormedReg r →
        n₀ ≤ regSize r →
        (loweredQFTGateCount
            (Basis := Basis) k hk ops r : ℝ)
          ≤
        C * phaseProductGateRate k (regSize r) := by
  rcases hcontract with
  ⟨ρ, hρnonneg, hρlt, hcontractBound⟩

  rcases hstep with
    ⟨A, hA, N, hN, hstepBound⟩

  rcases hbase N with
    ⟨D, hD⟩

  have hdelta :
      0 < 1 - ρ :=
    sub_pos.mpr hρlt

  let C : ℝ :=
    max
        (D : ℝ)
        (A / (1 - ρ))
      + 1

  have hC :
      0 < C := by
    have hDnonneg :
        0 ≤ (D : ℝ) := by
      positivity

    have hmaxNonneg :
        0 ≤
          max
            (D : ℝ)
            (A / (1 - ρ)) :=
      hDnonneg.trans
        (le_max_left _ _)

    dsimp [C]
    linarith

  have hDleC :
      (D : ℝ) ≤ C := by
    have hmax :=
      le_max_left
        (D : ℝ)
        (A / (1 - ρ))

    dsimp [C]
    linarith

  have hfracLeC :
      A / (1 - ρ) ≤ C := by
    have hmax :=
      le_max_right
        (D : ℝ)
        (A / (1 - ρ))

    dsimp [C]
    linarith

  have hAle :
      A ≤ (1 - ρ) * C := by
    have hdiv :=
      (div_le_iff₀ hdelta).1 hfracLeC

    nlinarith

  have habsorb :
      ρ * C + A ≤ C := by
    nlinarith [hAle]

  have hall :
      ∀ n : ℕ,
        1 ≤ n →
        ∀ r : Reg,
          WellFormedReg r →
          regSize r = n →
          (loweredQFTGateCount
              (Basis := Basis) k hk ops r : ℝ)
            ≤
          C * phaseProductGateRate k n := by
    intro n

    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn r hr hrSize

        by_cases hsmall :
            n < N

        · have hcostNat :
              loweredQFTGateCount
                  (Basis := Basis) k hk ops r
                ≤ D :=
            hD r hr (by omega)

          have hcost :
              (loweredQFTGateCount
                  (Basis := Basis) k hk ops r : ℝ)
                ≤
              (D : ℝ) := by
            exact_mod_cast hcostNat

          have hnR :
              (1 : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast hn

          have hnRate :
              (n : ℝ) ≤
                phaseProductGateRate k n := by
            simpa [phaseProductGateRate] using
              natCast_le_phaseProduct_rpow
                k hk hn

          have hrate :
              (1 : ℝ) ≤
                phaseProductGateRate k n :=
            hnR.trans hnRate

          calc
            (loweredQFTGateCount
                (Basis := Basis) k hk ops r : ℝ)
                ≤ (D : ℝ) :=
              hcost

            _ ≤ C :=
              hDleC

            _ ≤
              C * phaseProductGateRate k n := by
                nlinarith [le_of_lt hC, hrate]

        · have hNn :
              N ≤ n :=
            Nat.le_of_not_gt hsmall

          have htwo :
              2 ≤ n :=
            hN.trans hNn

          have htwoR :
              2 ≤ regSize r := by
            simpa [hrSize] using htwo

          have hhalves :=
            qftSplit_wellFormed r hr

          have hsmaller :=
            qftSplit_strictly_smaller
              r htwoR

          have hleftPos :
              1 ≤ regSize (qftLeftReg r) := by
            rw [regSize_qftLeftReg, hrSize]
            exact
              Nat.div_pos htwo
                (by omega)

          have hrightPos :
              1 ≤ regSize (qftRightReg r) := by
            rw [regSize_qftRightReg, hrSize]

            have hhalfPos :
                0 < n / 2 :=
              Nat.div_pos htwo (by omega)

            omega

          have hleftBound :=
            ih
              (regSize (qftLeftReg r))
              (by simpa [hrSize] using hsmaller.1)
              hleftPos
              (qftLeftReg r)
              hhalves.1
              rfl

          have hrightBound :=
            ih
              (regSize (qftRightReg r))
              (by simpa [hrSize] using hsmaller.2)
              hrightPos
              (qftRightReg r)
              hhalves.2
              rfl

          have hnode :
              (loweredQFTGateCount
                  (Basis := Basis) k hk ops r : ℝ)
                ≤
              (loweredQFTGateCount
                  (Basis := Basis)
                  k hk ops (qftRightReg r) : ℝ)
                +
              (loweredQFTGateCount
                  (Basis := Basis)
                  k hk ops (qftLeftReg r) : ℝ)
                +
              A * phaseProductGateRate k n := by
            simpa [hrSize] using
              hstepBound r hr
                (by simpa [hrSize] using hNn)

          have hcontractChildren :
              phaseProductGateRate k
                  (regSize (qftLeftReg r))
                +
              phaseProductGateRate k
                  (regSize (qftRightReg r))
                ≤
              ρ * phaseProductGateRate k n := by
            simpa [
              regSize_qftLeftReg,
              regSize_qftRightReg,
              hrSize
            ] using
              hcontractBound n htwo

          have hcontractScaled :
              C *
                  (phaseProductGateRate k
                      (regSize (qftLeftReg r))
                    +
                   phaseProductGateRate k
                      (regSize (qftRightReg r)))
                ≤
              C *
                (ρ * phaseProductGateRate k n) :=
            mul_le_mul_of_nonneg_left
              hcontractChildren
              (le_of_lt hC)

          calc
            (loweredQFTGateCount
                (Basis := Basis) k hk ops r : ℝ)
                ≤
              (loweredQFTGateCount
                  (Basis := Basis)
                  k hk ops (qftRightReg r) : ℝ)
                +
              (loweredQFTGateCount
                  (Basis := Basis)
                  k hk ops (qftLeftReg r) : ℝ)
                +
              A * phaseProductGateRate k n :=
              hnode

            _ ≤
              C * phaseProductGateRate k
                    (regSize (qftRightReg r))
                +
              C * phaseProductGateRate k
                    (regSize (qftLeftReg r))
                +
              A * phaseProductGateRate k n := by
                linarith

            _ =
              C *
                (phaseProductGateRate k
                    (regSize (qftLeftReg r))
                  +
                 phaseProductGateRate k
                    (regSize (qftRightReg r)))
                +
              A * phaseProductGateRate k n := by
                ring

            _ ≤
              C *
                (ρ * phaseProductGateRate k n)
                +
              A * phaseProductGateRate k n :=
                by
                  linarith

            _ =
              (ρ * C + A) *
                phaseProductGateRate k n := by
                ring

            _ ≤
              C * phaseProductGateRate k n :=
                mul_le_mul_of_nonneg_right
                  habsorb
                  (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) _)

  refine
    ⟨C, hC, 1, by omega, ?_⟩

  intro r hr hn

  exact
    hall
      (regSize r)
      hn
      r
      hr
      rfl


/-! ---------------------------------------------------------
    Final assembly
--------------------------------------------------------- -/

/--
The PhaseProduct bound implies the exact-QFT bound.
-/
theorem qftGateCountBound_of_phaseProduct
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hPhase :
      PhaseProductGateCountBound
        (Basis := Basis) k hk ops) :
    QFTGateCountBound
      (Basis := Basis) k hk ops := by
  have hα :
      1 < phaseProductExponent k :=
    one_lt_phaseProductExponent k hk

  have hcontract :=
    qft_half_rate_contraction k hk hα

  have hbase :
      ∀ N : ℕ,
        ∃ D : ℕ,
          ∀ r : Reg,
            WellFormedReg r →
            regSize r ≤ N →
            loweredQFTGateCount
                (Basis := Basis) k hk ops r
              ≤ D :=
    loweredQFTGateCount_bounded_on_bounded_sizes
      (Basis := Basis) k hk ops

  have hstep :=
    loweredQFTGateCount_one_level_recurrence
      (Basis := Basis) k hk ops hPhase

  rcases
    qft_binary_recurrence_solution
      (Basis := Basis)
      k hk ops
      hα
      hcontract
      hbase
      hstep with
    ⟨C, hC, n₀, hn₀, hbound⟩

  refine ⟨C, hC, n₀, hn₀, ?_⟩
  intro r hr hn

  have hsize_pos : 1 ≤ regSize r :=
    le_trans hn₀ hn

  have hgate := hbound r hr hn

  simpa [loweredQFTGateCount, phaseProductSafeRate, phaseProductGateRate,
    max_eq_right hsize_pos] using hgate

/--
Generated interpolation programs satisfy the exact-QFT bound.
-/
theorem qftGateCountBound_of_programOK
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hops : PhaseProductProgramOK k hk ops) :
    QFTGateCountBound
      (Basis := Basis) k hk ops := by
  exact
    qftGateCountBound_of_phaseProduct
      (Basis := Basis) k hk ops
      (phaseProductGateCountBound_of_programOK
        (Basis := Basis) k hk ops hops)
