import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.NaiveShor.Preliminaries
import Mathlib.Data.Nat.Totient


/-!
# Ideal order-finding good-outcome mass lower bound
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [ContinuedFractionPost]
variable [Spec]
/-! =========================================================
    Shor's ideal order-finding probability analysis

This follows the structure of Shor, Section 5:
  (5.2)      periodic modular-exponentiation state
  (5.4-5.7) Fourier/output probability formula
  (5.11-13) lower bound near multiples of Q/r
  (5.24-25) count coprime numerators
========================================================= -/


/-! ---------------------------------------------------------
    Step 1: elementary order/size consequences
--------------------------------------------------------- -/

omit [ContinuedFractionPost] [Spec] in
/--
For Shor's order `r`, the standard setting gives

    0 < r < N
    r² ≤ 2^m.

The last inequality is the continued-fraction precision requirement:
`r < N` and `N² < 2^m`.
-/
lemma shor_order_parameter_bounds
    {a r N m n : ℕ}
    (hsetting : BasicSetting a r N m n) :
    0 < r ∧ r < N ∧ r ^ 2 ≤ 2 ^ m := by
  rcases hsetting with
    ⟨ha0, haN, hOrder, hN2, _hm_hi, _hNn, _hn_hi⟩

  rcases hOrder with ⟨hcop, hr⟩
  subst r

  have hNgt1 : 1 < N := by
    omega

  haveI : NeZero N := ⟨by omega⟩

  let u : (ZMod N)ˣ :=
    ZMod.unitOfCoprime a hcop

  have hrpos : 0 < orderOf u := by
    exact orderOf_pos u

  have hr_le_phi :
      orderOf u ≤ Nat.totient N := by
    calc
      orderOf u
          ≤ Fintype.card (ZMod N)ˣ :=
        orderOf_le_card_univ
      _ = Nat.totient N :=
        ZMod.card_units_eq_totient N

  have hrN : orderOf u < N := by
    exact lt_of_le_of_lt
      hr_le_phi
      (Nat.totient_lt N hNgt1)

  have hrsq_lt :
      orderOf u ^ 2 < N ^ 2 := by
    nlinarith

  have hrsq :
      orderOf u ^ 2 ≤ 2 ^ m := by
    exact Nat.le_of_lt
      (lt_trans hrsq_lt hN2)

  simpa [u] using
    (And.intro hrpos (And.intro hrN hrsq))


/-! ---------------------------------------------------------
    Step 2: Shor equation (5.2)
--------------------------------------------------------- -/

/--
The ideal state immediately before the inverse QFT:

    1 / √Q ∑_{t=0}^{Q-1} |t⟩ |a^t mod N⟩.

Writing this as a definition keeps all later Fourier lemmas independent
of the implementation of `H_reg`, `initY1`, and `modExpIdeal'`.
-/
noncomputable def idealPreIQFTState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (a N : ℕ)
    (x y : ExtReg)
    (b0 : qs.Basis) :
    qs.State :=
  ((1 / Real.sqrt (ASize x.active : ℝ) : ℂ)) •
    ∑ t : Fin (ASize x.active),
      qs.ket
        (RegEncoding.writeNat y.active
          (a ^ t.1 % N)
          (RegEncoding.writeNat x.active t.1 b0))

/-! ---------------------------------------------------------
    Exact preparation of the ideal Shor state
--------------------------------------------------------- -/

omit [ContinuedFractionPost] [Spec] in
/--
The `BasicSetting` assumptions imply the numerical facts needed
to initialize and use the modular-data register.
-/
private lemma basicSetting_data_facts
    {a r N m n : ℕ}
    (hsetting : BasicSetting a r N m n) :
    1 < N ∧
    0 < n ∧
    N ≤ 2 ^ n := by
  rcases hsetting with
    ⟨ha0, haN, _hord,
      _hm_lo, _hm_hi, hn_lo, _hn_hi⟩

  have hN : 1 < N := by
    omega

  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 :=
      Nat.eq_zero_of_not_pos h
    rw [hn0] at hn_lo
    norm_num at hn_lo
    omega

  exact
    ⟨hN, hnpos, Nat.le_of_lt hn_lo⟩


omit [ContinuedFractionPost] [Spec] in
/--
For a nonempty register, Shor's `initY1` circuit is the Pauli-X
on its least-significant qubit.
-/
private lemma initY1_eq_X_lowQubit_naive
    (r : Reg)
    (hr : 0 < regSize r) :
    initY1 r = Gate.X (r.lowQubit hr) := by
  cases r with
  | mk qubits nodup =>
      cases qubits with
      | nil =>
          simp [regSize, Reg.width] at hr
      | cons q qubits =>
          simp [initY1, Reg.lowQubit]

omit [ContinuedFractionPost] [Spec] [MeasureClass qs] in
/--
Writing an exponent value into a register disjoint from `y` leaves
`y = 0`; consequently `initY1` changes that basis state to `y = 1`.
-/
private lemma eval_initY1_after_exponent_write
    [GateSemanticsFacts qs]
    (x y : Reg)
    (b0 : qs.Basis)
    (hxy : Disjoint x y)
    (hy0 : RegEncoding.toNat y b0 = 0)
    (hypos : 0 < regSize y)
    (t : Fin (ASize x)) :
    qs.eval
        (initY1 y)
        (qs.ket
          (RegEncoding.writeNat x t.1 b0))
      =
    qs.ket
      (RegEncoding.writeNat y 1
        (RegEncoding.writeNat x t.1 b0)) := by

  let bt : qs.Basis :=
    RegEncoding.writeNat x t.1 b0

  have hy_bt :
      RegEncoding.toNat y bt = 0 := by
    calc
      RegEncoding.toNat y bt
          =
        RegEncoding.toNat y b0 := by
          dsimp [bt]
          exact
            RegEncoding.toNat_left_write_right
              y x
              (Disjoint.symm hxy)
              b0 t.1

      _ = 0 := hy0

  rw [initY1_eq_X_lowQubit_naive y hypos]

  exact
    PauliXSemantics.eval_X_low_zero_reg_ket
      (qs := qs)
      y bt hypos hy_bt

omit [ContinuedFractionPost] [Spec] in
private lemma qftPhase_zero_left
    (N y : ℕ) :
    qftPhase N 0 y = 1 := by
  simp [qftPhase, ωPow]


omit [ContinuedFractionPost] [Spec] [MeasureClass qs] in
lemma eval_Hreg_zero_uniform_sum
    [GateSemanticsFacts qs]
    (r : ExtReg)
    (b : qs.Basis)
    (hzero : RegEncoding.toNat r.active b = 0) :
    qs.eval (H_reg r.active) (qs.ket b)
      =
    ((1 / Real.sqrt (ASize r.active : ℝ) : ℂ)) •
      ∑ t : Fin (ASize r.active),
        qs.ket
          (RegEncoding.writeNat r.active t.1 b) := by

  have hzero' :
      ExtReg.toNat r b = 0 := by
    simpa [ExtReg.toNat] using hzero

  calc
    qs.eval (H_reg r.active) (qs.ket b)
        =
      qs.eval (Gate.QFT r) (qs.ket b) := by
        simpa [H_reg] using
          (GateSemanticsFacts.eval_Hreg_zero_eq_QFT
            (qs := qs)
            r b hzero')

    _ =
      ((1 / Real.sqrt (ASize r.active : ℝ) : ℂ)) •
        ∑ t : Fin (ASize r.active),
          qs.ket
            (RegEncoding.writeNat r.active t.1 b) := by
      rw [QFTSemantics.eval_QFT_ket]
      simp [
        ExtReg.width,
        ExtReg.toNat,
        ASize,
        hzero,
        qftPhase_zero_left
      ]

omit [MeasureClass qs] [ContinuedFractionPost] [Spec] in
/--
Starting from `x = 0` and `y = 0`, the first two pieces of ideal
order finding create

    1/√Q ∑ₜ |t⟩ |1⟩.

This is Shor's state immediately before modular exponentiation.
-/
private lemma eval_initY1_after_Hreg_zero
    [GateSemanticsFacts qs]
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hx0 : RegEncoding.toNat x.active b0 = 0)
    (hy0 : RegEncoding.toNat y.active b0 = 0)
    (hxy : Disjoint x.active y.active)
    (hypos : 0 < regSize y.active) :
    qs.eval
        (initY1 y.active)
        (qs.eval (H_reg x.active) (qs.ket b0))
      =
    ((1 / Real.sqrt (ASize x.active : ℝ) : ℂ)) •
      ∑ t : Fin (ASize x.active),
        qs.ket
          (RegEncoding.writeNat y.active 1
            (RegEncoding.writeNat x.active t.1 b0)) := by
  classical

  rw [
    eval_Hreg_zero_uniform_sum
      (qs := qs) x b0 hx0
  ]

  rw [qs.eval_smul, eval_finset_sum]

  apply congrArg
    (fun ψ : qs.State =>
      ((1 / Real.sqrt (ASize x.active : ℝ) : ℂ)) • ψ)

  apply Finset.sum_congr rfl
  intro t _ht

  exact
    eval_initY1_after_exponent_write
      (qs := qs)
      x.active y.active b0
      hxy hy0 hypos t

theorem eval_modExpIdeal_ket
    [GateSemanticsCore qs]
    [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ)
    (x y : Reg)
    (b : qs.Basis)
    (hN : 1 < N)
    (ha : Nat.Coprime a N)
    (hxy : Disjoint x y)
    (hsize : N ≤ ASize y)
    (hy : RegEncoding.toNat y b < N) :
    qs.eval (modExpIdeal' qs a N x y) (qs.ket b)
      =
    qs.ket
      (RegEncoding.writeNat y
        ((RegEncoding.toNat y b *
            a ^ RegEncoding.toNat x b) % N)
        b) := by
  sorry

/--
Exact modular exponentiation on one initialized Shor basis label:

    |t⟩ |1⟩  ↦  |t⟩ |a^t mod N⟩.
-/
private lemma eval_modExpIdeal_on_initialized_label
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ)
    (x y : Reg)
    (b0 : qs.Basis)
    (hN : 1 < N)
    (ha : Nat.Coprime a N)
    (hxy : Disjoint x y)
    (hsize : N ≤ ASize y)
    (t : Fin (ASize x)) :
    qs.eval
        (modExpIdeal' qs a N x y)
        (qs.ket
          (RegEncoding.writeNat y 1
            (RegEncoding.writeNat x t.1 b0)))
      =
    qs.ket
      (RegEncoding.writeNat y
        (a ^ t.1 % N)
        (RegEncoding.writeNat x t.1 b0)) := by

  let bx : qs.Basis :=
    RegEncoding.writeNat x t.1 b0

  let b1 : qs.Basis :=
    RegEncoding.writeNat y 1 bx

  have hone_lt :
      1 < ASize y :=
    lt_of_lt_of_le hN hsize

  have hyval :
      RegEncoding.toNat y b1 = 1 := by
    dsimp [b1]
    exact
      RegEncoding.toNat_writeNat_of_lt
        y 1 bx hone_lt

  have hxval :
      RegEncoding.toNat x b1 = t.1 := by
    calc
      RegEncoding.toNat x b1
          =
        RegEncoding.toNat x bx := by
          dsimp [b1]
          exact
            RegEncoding.toNat_left_write_right
              x y hxy bx 1

      _ = t.1 := by
        dsimp [bx]
        exact
          RegEncoding.toNat_writeNat_of_lt
            x t.1 b0 t.isLt

  have hylt :
      RegEncoding.toNat y b1 < N := by
    rw [hyval]
    exact hN

  have hmod :=
    eval_modExpIdeal_ket
      (qs := qs)
      a N
      x y
      b1
      hN
      ha
      hxy
      hsize
      hylt

  rw [hyval, hxval] at hmod

  calc
    qs.eval
        (modExpIdeal' qs a N x y)
        (qs.ket
          (RegEncoding.writeNat y 1
            (RegEncoding.writeNat x t.1 b0)))
        =
      qs.ket
        (RegEncoding.writeNat y
          ((1 * a ^ t.1) % N)
          b1) := by
            simpa [b1, bx] using hmod

    _ =
      qs.ket
        (RegEncoding.writeNat y
          (a ^ t.1 % N)
          bx) := by
        apply congrArg qs.ket
        simp only [one_mul]
        dsimp [b1]
        exact
          writeNat_overwrite_same_reg
            y
            (a ^ t.1 % N)
            1
            bx

    _ =
      qs.ket
        (RegEncoding.writeNat y
          (a ^ t.1 % N)
          (RegEncoding.writeNat x t.1 b0)) := by
        rfl

/--
By linearity, exact modular exponentiation maps the initialized
uniform superposition

    1/√Q ∑ₜ |t⟩ |1⟩

to

    1/√Q ∑ₜ |t⟩ |a^t mod N⟩.
-/
private lemma eval_modExpIdeal_on_initialized_superposition
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ)
    (x y : Reg)
    (b0 : qs.Basis)
    (hN : 1 < N)
    (ha : Nat.Coprime a N)
    (hxy : Disjoint x y)
    (hsize : N ≤ ASize y) :
    qs.eval
        (modExpIdeal' qs a N x y)
        (
          ((1 / Real.sqrt (ASize x : ℝ) : ℂ)) •
            ∑ t : Fin (ASize x),
              qs.ket
                (RegEncoding.writeNat y 1
                  (RegEncoding.writeNat x t.1 b0))
        )
      =
    ((1 / Real.sqrt (ASize x : ℝ) : ℂ)) •
      ∑ t : Fin (ASize x),
        qs.ket
          (RegEncoding.writeNat y
            (a ^ t.1 % N)
            (RegEncoding.writeNat x t.1 b0)) := by
  classical

  rw [qs.eval_smul, eval_finset_sum]

  apply congrArg
    (fun ψ : qs.State =>
      ((1 / Real.sqrt (ASize x : ℝ) : ℂ)) • ψ)

  apply Finset.sum_congr rfl
  intro t _ht

  exact
    eval_modExpIdeal_on_initialized_label
      (qs := qs)
      a N
      x y
      b0
      hN ha hxy hsize
      t

/--
Shor (5.2): Hadamards followed by exact modular exponentiation create
the uniform periodic state.

This is where `eval_modExpIdeal_ket` is used.
-/
lemma eval_orderFindingIdeal_prefix
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hsetting :
      BasicSetting
        inst.a
        (ord inst.a inst.N inst.coprime)
        inst.N
        (regSize x.active)
        (regSize y.active))
    (hinput : IdealOrderFindingInput qs x y b0) :
    qs.eval
        ((H_reg x.active) ;;
         (initY1 y.active) ;;
         (modExpIdeal' qs inst.a inst.N x.active y.active))
        (qs.ket b0)
      =
    idealPreIQFTState
      qs inst.a inst.N x y b0 := by
  classical

  rcases hinput with
    ⟨hx0, hy0, howned⟩

  have hxy :
      Disjoint x.active y.active :=
    ExtReg.activeDisjoint_of_ownedDisjoint
      howned

  have hdata :=
    basicSetting_data_facts hsetting

  have hN :
      1 < inst.N :=
    hdata.1

  have hypos :
      0 < regSize y.active :=
    hdata.2.1

  have hsize :
      inst.N ≤ ASize y.active := by
    simpa [ASize] using hdata.2.2

  have ha :
      Nat.Coprime inst.a inst.N :=
    (Nat.coprime_iff_gcd_eq_one).2
      inst.coprime

  rw [qs.eval_seq, qs.eval_seq]

  rw [
    eval_initY1_after_Hreg_zero
      (qs := qs)
      x
      y
      b0
      hx0
      hy0
      hxy
      hypos
  ]

  simpa [idealPreIQFTState] using
    (eval_modExpIdeal_on_initialized_superposition
      (qs := qs)
      inst.a
      inst.N
      x.active
      y.active
      b0
      hN
      ha
      hxy
      hsize)

/-! ---------------------------------------------------------
    Step 3: Shor equations (5.4)--(5.7)
--------------------------------------------------------- -/

/--
The contribution from one residue class `s mod r` to output `o`.

The filter

    { t < Q | t % r = s }

is exactly Shor's substitution `t = j*r + s`.

Because the circuit uses IQFT, the QFT phase is conjugated.
-/
noncomputable def shorPeriodClassAmplitude
    (Q r s o : ℕ) : ℂ :=
  (1 / (Q : ℂ)) *
    ∑ t ∈ (Finset.range Q).filter (fun t => t % r = s),
      star (qftPhase Q t o)


/--
Shor's probability of observing exponent-register output `o`,
after summing over the `r` possible values of the modular-data register.

This is the marginal version of equations (5.5)--(5.7).
-/
noncomputable def shorPaperOutcomeProb
    (Q r o : ℕ) : ℝ :=
  ∑ s ∈ Finset.range r,
    ‖shorPeriodClassAmplitude Q r s o‖ ^ 2


/--
Equations (5.4)--(5.7).

Starting from the explicit periodic state, IQFT followed by measurement
of the exponent register has exactly the period-class probability above.

This proof consists of:
* linearity of IQFT;
* Fourier inversion / conjugated `qftPhase`;
* `a^t mod N = a^s mod N` iff `t ≡ s (mod r)`;
* orthogonality of distinct computational basis states of `y`;
* the computational-basis measurement law.
-/
lemma measProbAfter_orderFindingIdeal_eq_paper_formula
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hsetting : BasicSetting inst.a (ord inst.a inst.N inst.coprime) inst.N (regSize x.active) (regSize y.active))
    (hinput : IdealOrderFindingInput qs x y b0)
    (hpre : qs.eval ((H_reg x.active) ;; (initY1 y.active) ;; (modExpIdeal' qs inst.a inst.N x.active y.active)) (qs.ket b0)
        =
      idealPreIQFTState qs inst.a inst.N x y b0)
    (o : Fin (ASize x.active)) :
    measProbAfter (qs := qs) qs.eval x.active o.1
        (orderFindingIdeal (qs := qs) inst.a inst.N x y)
        (qs.ket b0)
      =
    shorPaperOutcomeProb
      (ASize x.active)
      (ord inst.a inst.N inst.coprime)
      o.1 := by
  sorry


/-! ---------------------------------------------------------
    Step 4: Shor equations (5.11)--(5.13)
--------------------------------------------------------- -/

/--
The Fourier-peak estimate.

If

    |o/Q - k/r| ≤ 1/(2Q),

then the phases in each period class lie sufficiently close together.
Summing the resulting geometric progression gives the standard
`4 / π²` phase-estimation lower bound after marginalizing over the
second register:

    P(o) ≥ (4 / π²) / r.

This is the analytic heart of Shor's equations (5.7)--(5.13).
-/
lemma shor_paper_peak_lower_bound
    {Q r o k : ℕ}
    (hk : k < r)
    (hrQ : r ^ 2 ≤ Q)
    (happrox :
      approxRat o Q k r
        (1 / (2 * (Q : ℝ)))) :
    (4 / Real.pi ^ 2) * (1 / (r : ℝ))
      ≤
    shorPaperOutcomeProb Q r o := by
  sorry


/--
A `GoodOutcome` therefore has the Fourier lower bound.

This is only unpacking `GoodOutcome`; all analytic work stays in
`shor_paper_peak_lower_bound`.
-/
lemma shor_paper_goodOutcome_lower_bound
    {Q r o : ℕ}
    (hgood : GoodOutcome o Q r) :
    (4 / Real.pi ^ 2) * (1 / (r : ℝ))
      ≤
    shorPaperOutcomeProb Q r o := by
  rcases hgood with
    ⟨k, hk, _hcoprime, hrQ, happrox⟩

  exact shor_paper_peak_lower_bound
    hk hrQ happrox


/-! ---------------------------------------------------------
    Step 5: count the good Fourier outputs
--------------------------------------------------------- -/

/--
The finite set of exponent-register outputs satisfying `GoodOutcome`.
-/
noncomputable def goodOutcomeFinset
    (Q r : ℕ) :
    Finset (Fin Q) := by
  classical
  exact Finset.univ.filter
    (fun o => GoodOutcome o.1 Q r)

omit [ContinuedFractionPost] [Spec] in
@[simp]
lemma mem_goodOutcomeFinset
    {Q r : ℕ}
    (o : Fin Q) :
    o ∈ goodOutcomeFinset Q r ↔
      GoodOutcome o.1 Q r := by
  classical
  simp [goodOutcomeFinset]


/--
Shor's counting step.

For every `k < r` coprime to `r`, choose the integer `o` nearest to

    Q*k/r.

Because `r² ≤ Q`, that output satisfies

    |o/Q - k/r| ≤ 1/(2Q),

and different reduced fractions `k/r` give different outputs.

Hence there are at least `φ(r)` good outputs.
-/
lemma goodOutcome_card_ge_totient
    {Q r : ℕ}
    (hr : 0 < r)
    (hrQ : r ^ 2 ≤ Q) :
    Nat.totient r ≤
      (goodOutcomeFinset Q r).card := by
  sorry


/-! ---------------------------------------------------------
    Step 6: sum the pointwise probabilities
--------------------------------------------------------- -/
omit [ContinuedFractionPost] [Spec] in
/--
Pure finite-sum bookkeeping.

If:
* there are at least `φ(r)` good outputs, and
* every good output has probability at least `(4/π²)/r`,

then their total probability is at least

    (4/π²) * φ(r)/r.

This lemma contains no quantum reasoning.
-/
lemma goodOutcome_mass_lower_bound_from_card_and_pointwise
    (Q r : ℕ)
    (p : Fin Q → ℝ)
    (hr : 0 < r)
    (hcard :
      Nat.totient r ≤
        (goodOutcomeFinset Q r).card)
    (hpoint :
      ∀ o : Fin Q,
        GoodOutcome o.1 Q r →
          (4 / Real.pi ^ 2) * (1 / (r : ℝ))
            ≤ p o) :
    (4 / Real.pi ^ 2) *
        ((Nat.totient r : ℝ) / (r : ℝ))
      ≤
    ∑ o : Fin Q,
      goodOutcomeIndicator o.1 Q r * p o := by
  classical

  let c : ℝ :=
    (4 / Real.pi ^ 2) * (1 / (r : ℝ))

  have hc : 0 ≤ c := by
    dsimp [c]
    positivity

  have hcard_real :
      (Nat.totient r : ℝ) ≤
        ((goodOutcomeFinset Q r).card : ℝ) := by
    exact_mod_cast hcard

  calc
    (4 / Real.pi ^ 2) *
        ((Nat.totient r : ℝ) / (r : ℝ))
        =
      (Nat.totient r : ℝ) * c := by
        simp [c, div_eq_mul_inv]
        ring

    _ ≤
      ((goodOutcomeFinset Q r).card : ℝ) * c := by
        exact mul_le_mul_of_nonneg_right
          hcard_real hc

    _ =
      ∑ o ∈ goodOutcomeFinset Q r, c := by
        simp

    _ ≤
      ∑ o ∈ goodOutcomeFinset Q r, p o := by
        apply Finset.sum_le_sum
        intro o ho
        apply hpoint o
        exact (mem_goodOutcomeFinset o).mp ho

    _ =
      ∑ o : Fin Q,
        goodOutcomeIndicator o.1 Q r * p o := by
        simp [
          goodOutcomeFinset,
          goodOutcomeIndicator,
          Finset.sum_filter
        ]

/-! ---------------------------------------------------------
    Step 7: the loose number-theoretic bound used by this repo
--------------------------------------------------------- -/

/--
A deliberately weak consequence of the standard lower bounds for
Euler's totient ratio.

For an order `r < N`,

    φ(r) / r ≥ exp(-2) / log₂(N)^4.

This is much weaker than the classical asymptotic bound used by Shor,
but is convenient because it gives exactly the public theorem's
inverse-polylogarithmic form.
-/
lemma shor_totient_ratio_log4_lower_bound
    {a r N m n : ℕ}
    (hsetting : BasicSetting a r N m n) :
    Real.exp (-2) / (Nat.log2 N : ℝ) ^ 4
      ≤
    (Nat.totient r : ℝ) / (r : ℝ) := by
  sorry


/-! =========================================================
    Final quantum good-outcome mass theorem
========================================================= -/

lemma ideal_orderFinding_goodOutcome_mass_lower_bound
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hsetting :
      BasicSetting
        inst.a
        (ord inst.a inst.N inst.coprime)
        inst.N
        (regSize x.active)
        (regSize y.active))
    (hinput : IdealOrderFindingInput qs x y b0) :
    κ / (Nat.log2 inst.N : ℝ) ^ 4
      ≤
    ∑ o : Fin (ASize x.active),
      goodOutcomeIndicator
        o.1
        (ASize x.active)
        (ord inst.a inst.N inst.coprime)
        *
      measProbAfter
        (qs := qs)
        qs.eval
        x.active
        o.1
        (orderFindingIdeal
          (qs := qs) inst.a inst.N x y)
        (qs.ket b0) := by
  classical

  let r : ℕ :=
    ord inst.a inst.N inst.coprime

  let Q : ℕ :=
    ASize x.active

  /- Step 1: `0 < r`, `r < N`, and `r² ≤ Q`. -/
  have hparams :
      0 < r ∧
      r < inst.N ∧
      r ^ 2 ≤ Q := by
    have h :=
      shor_order_parameter_bounds hsetting

    simpa [r, Q, ASize] using h

  have hr : 0 < r :=
    hparams.1

  have hrQ : r ^ 2 ≤ Q :=
    hparams.2.2

  /- Step 2: equation (5.2). -/
  have hpre :
      qs.eval
          ((H_reg x.active) ;;
           (initY1 y.active) ;;
           (modExpIdeal'
             qs inst.a inst.N
             x.active y.active))
          (qs.ket b0)
        =
      idealPreIQFTState
        qs inst.a inst.N x y b0 :=
    eval_orderFindingIdeal_prefix
      inst x y b0 hsetting hinput

  /- Step 3: equations (5.4)--(5.7). -/
  have hformula :
      ∀ o : Fin Q,
        measProbAfter
            (qs := qs)
            qs.eval
            x.active
            o.1
            (orderFindingIdeal
              (qs := qs)
              inst.a inst.N x y)
            (qs.ket b0)
          =
        shorPaperOutcomeProb Q r o.1 := by
    intro o

    simpa [Q, r] using
      (measProbAfter_orderFindingIdeal_eq_paper_formula
        inst x y b0
        hsetting hinput hpre
        (show Fin (ASize x.active) from
          ⟨o.1, by simp [Q]⟩))

  /- Step 4: every good Fourier peak has probability ≥ 4/(π² r). -/
  have hpoint :
      ∀ o : Fin Q,
        GoodOutcome o.1 Q r →
          (4 / Real.pi ^ 2) *
              (1 / (r : ℝ))
            ≤
          measProbAfter
            (qs := qs)
            qs.eval
            x.active
            o.1
            (orderFindingIdeal
              (qs := qs)
              inst.a inst.N x y)
            (qs.ket b0) := by
    intro o hgood

    rw [hformula o]

    exact
      shor_paper_goodOutcome_lower_bound
        hgood

  /- Step 5: at least φ(r) distinct good outputs. -/
  have hcard :
      Nat.totient r ≤
        (goodOutcomeFinset Q r).card :=
    goodOutcome_card_ge_totient
      hr hrQ

  /- Step 6: sum their probabilities. -/
  have hmass :
      (4 / Real.pi ^ 2) *
          ((Nat.totient r : ℝ) / (r : ℝ))
        ≤
      ∑ o : Fin Q,
        goodOutcomeIndicator
          o.1 Q r *
        measProbAfter
          (qs := qs)
          qs.eval
          x.active
          o.1
          (orderFindingIdeal
            (qs := qs)
            inst.a inst.N x y)
          (qs.ket b0) :=
    goodOutcome_mass_lower_bound_from_card_and_pointwise
      Q r
      (fun o =>
        measProbAfter
          (qs := qs)
          qs.eval
          x.active
          o.1
          (orderFindingIdeal
            (qs := qs)
            inst.a inst.N x y)
          (qs.ket b0))
      hr
      hcard
      hpoint

  /- Step 7: replace φ(r)/r by the desired inverse-polylog bound. -/
  have hphi :
      Real.exp (-2) /
          (Nat.log2 inst.N : ℝ) ^ 4
        ≤
      (Nat.totient r : ℝ) / (r : ℝ) := by
    simpa [r] using
      (shor_totient_ratio_log4_lower_bound
        hsetting)

  have hfourier_nonneg :
      0 ≤ (4 / Real.pi ^ 2 : ℝ) := by
    positivity

  have hscaled :
      (4 / Real.pi ^ 2) *
          (Real.exp (-2) /
            (Nat.log2 inst.N : ℝ) ^ 4)
        ≤
      (4 / Real.pi ^ 2) *
          ((Nat.totient r : ℝ) / (r : ℝ)) :=
    mul_le_mul_of_nonneg_left
      hphi hfourier_nonneg

  calc
    κ / (Nat.log2 inst.N : ℝ) ^ 4
        =
      (4 / Real.pi ^ 2) *
        (Real.exp (-2) /
          (Nat.log2 inst.N : ℝ) ^ 4) := by
            unfold κ
            ring

    _ ≤
      (4 / Real.pi ^ 2) *
        ((Nat.totient r : ℝ) / (r : ℝ)) :=
      hscaled

    _ ≤
      ∑ o : Fin Q,
        goodOutcomeIndicator o.1 Q r *
          measProbAfter
            (qs := qs)
            qs.eval
            x.active
            o.1
            (orderFindingIdeal
              (qs := qs)
              inst.a inst.N x y)
            (qs.ket b0) :=
      hmass

    _ =
      ∑ o : Fin (ASize x.active),
        goodOutcomeIndicator
          o.1
          (ASize x.active)
          (ord inst.a inst.N inst.coprime) *
        measProbAfter
          (qs := qs)
          qs.eval
          x.active
          o.1
          (orderFindingIdeal
            (qs := qs)
            inst.a inst.N x y)
          (qs.ket b0) := by
      simp [Q, r]


end Shor
