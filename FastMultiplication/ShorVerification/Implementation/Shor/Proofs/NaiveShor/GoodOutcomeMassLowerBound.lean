import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.NaiveShor.Preliminaries
import Mathlib.Data.Nat.Totient


/-!
# Ideal order-finding good-outcome mass lower bound
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
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

private lemma qftPhase_zero_left
    (N y : ℕ) :
    qftPhase N 0 y = 1 := by
  simp [qftPhase, ωPow]

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
    [Spec]
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
    [Spec]
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
    [Spec]
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
    [Spec]
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

private def shorOutputBasis
    (a N : ℕ)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (o s : ℕ) : qs.Basis :=
  RegEncoding.writeNat x.active o
    (RegEncoding.writeNat y.active
      (a ^ s % N) b0)


private noncomputable def shorGroupedPostIQFTState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (a N Q r : ℕ)
    (x y : ExtReg)
    (b0 : qs.Basis) : qs.State :=
  ∑ o : Fin Q,
    ∑ s ∈ Finset.range r,
      shorPeriodClassAmplitude Q r s o.1 •
        qs.ket
          (shorOutputBasis
            (qs := qs) a N x y b0 o.1 s)

private lemma active_disjoint_of_ownedDisjoint
    {x y : ExtReg}
    (h : ExtReg.OwnedDisjoint x y) :
    Disjoint x.active y.active := by
  intro q hx hy
  exact
    h
      (List.mem_append_left x.reserve.qubits hx)
      (List.mem_append_left y.reserve.qubits hy)


private lemma eval_finset_sum_local
    [GateSemanticsCore qs]
    (U : Gate)
    {ι : Type*}
    (s : Finset ι)
    (f : ι → qs.State) :
    qs.eval U (∑ i ∈ s, f i)
      =
    ∑ i ∈ s, qs.eval U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [qs.eval_zero]
  | @insert a s ha ih =>
      simp [Finset.sum_insert, ha, qs.eval_add, ih]


private lemma eval_fintype_sum_local
    [GateSemanticsCore qs]
    (U : Gate)
    {ι : Type*}
    [Fintype ι]
    (f : ι → qs.State) :
    qs.eval U (∑ i, f i)
      =
    ∑ i, qs.eval U (f i) := by
  classical
  simpa using
    (eval_finset_sum_local
      (qs := qs) U
      (Finset.univ : Finset ι) f)


private lemma shor_inv_sqrt_sq
    (Q : ℕ)
    (hQ : 0 < Q) :
    ((1 / Real.sqrt (Q : ℝ) : ℂ) *
      (1 / Real.sqrt (Q : ℝ) : ℂ))
      =
    1 / (Q : ℂ) := by
  have hQr : 0 < (Q : ℝ) := by
    exact_mod_cast hQ

  have hs0 :
      (Real.sqrt (Q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (Real.sqrt_pos.2 hQr))

  have hQ0 :
      (Q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hQ)

  field_simp [hs0, hQ0]
  norm_cast
  simp
/--
Exact inverse-QFT action on a computational-basis state.

This is Fourier inversion: the inverse transform uses the conjugated
`qftPhase`.
-/
private lemma eval_IQFT_ket_exact
    [GateSemanticsFacts qs]
    (x : ExtReg)
    (b : qs.Basis) :
    qs.eval (IQFT x) (qs.ket b)
      =
    ((1 / Real.sqrt (ASize x.active : ℝ) : ℂ)) •
      ∑ o : Fin (ASize x.active),
        star
            (qftPhase
              (ASize x.active)
              (RegEncoding.toNat x.active b)
              o.1) •
          qs.ket
            (RegEncoding.writeNat
              x.active o.1 b) := by
  simpa [IQFT, ExtReg.toNat] using
    (QFTSemantics.eval_adj_QFT_ket
      (qs := qs) x b)

/--
Powers of `a` modulo `N` are periodic with period
`ord a N gcd`.
-/
private lemma shor_pow_mod_periodic
    (inst : ShorOrderFindingInstance)
    (t : ℕ) :
    inst.a ^ t % inst.N
      =
    inst.a ^
        (t % ord inst.a inst.N inst.coprime) %
      inst.N := by
  let u : (ZMod inst.N)ˣ :=
    ZMod.unitOfCoprime
      inst.a
      ((Nat.coprime_iff_gcd_eq_one).2 inst.coprime)

  have hu :
      u ^ (t % orderOf u) = u ^ t :=
    pow_mod_orderOf u t

  have hz :
      ((inst.a ^
          (t % ord inst.a inst.N inst.coprime) : ℕ) :
          ZMod inst.N)
        =
      ((inst.a ^ t : ℕ) : ZMod inst.N) := by
    have hcoe :
        ((u : ZMod inst.N) ^ (t % orderOf u))
          =
        ((u : ZMod inst.N) ^ t) :=
      congrArg
        (fun z : (ZMod inst.N)ˣ =>
          (z : ZMod inst.N))
        hu

    simpa [
      u,
      ord,
      ZMod.coe_unitOfCoprime,
      Nat.cast_pow
    ] using hcoe

  have hmod :=
    (ZMod.natCast_eq_natCast_iff'
      (inst.a ^
        (t % ord inst.a inst.N inst.coprime))
      (inst.a ^ t)
      inst.N).1 hz

  exact hmod.symm

/--
Before one full order has elapsed, distinct exponents give distinct
powers modulo `N`.
-/
private lemma shor_pow_mod_injective_below_order
    (inst : ShorOrderFindingInstance)
    {s t : ℕ}
    (hs :  s < ord inst.a inst.N inst.coprime)
    (ht : t < ord inst.a inst.N inst.coprime)
    (h : inst.a ^ s % inst.N = inst.a ^ t % inst.N) :
    s = t := by
  let u : (ZMod inst.N)ˣ :=
    ZMod.unitOfCoprime
      inst.a
      ((Nat.coprime_iff_gcd_eq_one).2 inst.coprime)

  have hz :
      ((inst.a ^ s : ℕ) : ZMod inst.N)
        =
      ((inst.a ^ t : ℕ) : ZMod inst.N) :=
    (ZMod.natCast_eq_natCast_iff'
      (inst.a ^ s)
      (inst.a ^ t)
      inst.N).2 h

  have hu :
      u ^ s = u ^ t := by
    apply Units.ext
    simpa [
      u,
      ZMod.coe_unitOfCoprime
    ] using hz

  exact
    (pow_injOn_Iio_orderOf (x := u))
      (by simpa [u, ord] using hs)
      (by simpa [u, ord] using ht)
      hu

private lemma shor_preIQFT_x_value
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hxy : Disjoint x.active y.active)
    (t : Fin (ASize x.active)) :
    RegEncoding.toNat x.active
        (RegEncoding.writeNat y.active
          (inst.a ^ t.1 % inst.N)
          (RegEncoding.writeNat
            x.active t.1 b0))
      =
    t.1 := by
  rw [
    RegEncoding.toNat_left_write_right
      x.active
      y.active
      hxy
  ]

  exact
    RegEncoding.toNat_writeNat_of_lt
      x.active t.1 b0 t.isLt

private lemma shor_IQFT_output_basis_eq
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hxy : Disjoint x.active y.active)
    (t o : Fin (ASize x.active)) :
    RegEncoding.writeNat x.active o.1
        (RegEncoding.writeNat y.active
          (inst.a ^ t.1 % inst.N)
          (RegEncoding.writeNat
            x.active t.1 b0))
      =
    shorOutputBasis
      (qs := qs)
      inst.a inst.N
      x y b0
      o.1
      (t.1 %
        ord inst.a inst.N inst.coprime) := by
  rw [shor_pow_mod_periodic inst t.1]

  unfold shorOutputBasis

  rw [
    writeNat_comm_of_disjoint
      y.active
      x.active
      (Disjoint.symm hxy)
  ]

  rw [writeNat_overwrite_same_reg]

private lemma sum_range_group_by_mod
    {M : Type*}
    [AddCommMonoid M]
    (Q r : ℕ)
    (hr : 0 < r)
    (f : ℕ → ℕ → M) :
    (∑ t ∈ Finset.range Q,
        f (t % r) t)
      =
    ∑ s ∈ Finset.range r,
      ∑ t ∈
          (Finset.range Q).filter
            (fun t => t % r = s),
        f s t := by
  classical
  symm

  calc
    (∑ s ∈ Finset.range r,
        ∑ t ∈
            (Finset.range Q).filter
              (fun t => t % r = s),
          f s t)
        =
      ∑ s ∈ Finset.range r,
        ∑ t ∈ Finset.range Q,
          if t % r = s then
            f s t
          else
            0 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_filter]

    _ =
      ∑ t ∈ Finset.range Q,
        ∑ s ∈ Finset.range r,
          if t % r = s then
            f s t
          else
            0 := by
      rw [Finset.sum_comm]

    _ =
      ∑ t ∈ Finset.range Q,
        f (t % r) t := by
      apply Finset.sum_congr rfl
      intro t ht

      have hm :
          t % r ∈ Finset.range r :=
        Finset.mem_range.mpr
          (Nat.mod_lt t hr)

      rw [
        Finset.sum_eq_single
          (t % r)
      ]

      · simp

      · intro s hs hne
        have hne' : t % r ≠ s :=
          Ne.symm hne
        simp [hne']

      · intro hnot
        exact False.elim (hnot hm)

private lemma shor_group_fixed_output
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hr :
      0 < ord inst.a inst.N inst.coprime)
    (o : Fin (ASize x.active)) :
    (∑ t ∈ Finset.range (ASize x.active),
        ((1 / (ASize x.active : ℂ)) *
          star
            (qftPhase
              (ASize x.active)
              t
              o.1)) •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0
              o.1
              (t %
                ord inst.a inst.N
                  inst.coprime)))
      =
    ∑ s ∈
        Finset.range
          (ord inst.a inst.N inst.coprime),
      shorPeriodClassAmplitude
          (ASize x.active)
          (ord inst.a inst.N inst.coprime)
          s o.1 •
        qs.ket
          (shorOutputBasis
            (qs := qs)
            inst.a inst.N
            x y b0
            o.1 s) := by
  classical

  rw [
    sum_range_group_by_mod
      (ASize x.active)
      (ord inst.a inst.N inst.coprime)
      hr
      (fun s t =>
        ((1 / (ASize x.active : ℂ)) *
          star
            (qftPhase
              (ASize x.active)
              t o.1)) •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0
              o.1 s))
  ]

  apply Finset.sum_congr rfl
  intro s hs

  rw [← Finset.sum_smul]

  congr 1

  simp [
    shorPeriodClassAmplitude,
    Finset.mul_sum
  ]
/--
After IQFT, regroup the exponent sum according to `t % r`.

For a fixed output `o` and residue class `s`, the coefficient is exactly

    1/Q * ∑_{t<Q, t % r = s} conj(qftPhase Q t o),

which is `shorPeriodClassAmplitude`.
-/
private lemma eval_IQFT_idealPreIQFTState_grouped
    [GateSemanticsFacts qs]
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
    (hinput :
      IdealOrderFindingInput qs x y b0) :
    qs.eval
        (IQFT x)
        (idealPreIQFTState
          qs inst.a inst.N x y b0)
      =
    shorGroupedPostIQFTState
      qs inst.a inst.N
      (ASize x.active)
      (ord inst.a inst.N inst.coprime)
      x y b0 := by
  classical

  let Q : ℕ :=
    ASize x.active

  let r : ℕ :=
    ord inst.a inst.N inst.coprime

  let c : ℂ :=
    (1 / Real.sqrt (Q : ℝ) : ℂ)

  have hQ : 0 < Q := by
    simp [Q, ASize]

  have hr : 0 < r := by
    simpa [r] using
      (shor_order_parameter_bounds hsetting).1

  have hxy :
      Disjoint x.active y.active :=
    active_disjoint_of_ownedDisjoint
      hinput.2.2

  have hscalar :
      c * c = 1 / (Q : ℂ) := by
    simpa [c] using
      shor_inv_sqrt_sq Q hQ

  change
    qs.eval
        (IQFT x)
        (c •
          ∑ t : Fin Q,
            qs.ket
              (RegEncoding.writeNat y.active
                (inst.a ^ t.1 % inst.N)
                (RegEncoding.writeNat
                  x.active t.1 b0)))
      =
    _

  calc
    qs.eval
        (IQFT x)
        (c •
          ∑ t : Fin Q,
            qs.ket
              (RegEncoding.writeNat y.active
                (inst.a ^ t.1 % inst.N)
                (RegEncoding.writeNat
                  x.active t.1 b0)))
        =
      c •
        ∑ t : Fin Q,
          c •
            ∑ o : Fin Q,
              star
                  (qftPhase Q t.1 o.1) •
                qs.ket
                  (RegEncoding.writeNat
                    x.active o.1
                    (RegEncoding.writeNat y.active
                      (inst.a ^ t.1 % inst.N)
                      (RegEncoding.writeNat
                        x.active t.1 b0))) := by
      rw [
        qs.eval_smul,
        eval_fintype_sum_local
      ]

      congr 1

      apply Finset.sum_congr rfl
      intro t ht

      have hxt :=
        shor_preIQFT_x_value
          (qs := qs)
          inst x y b0 hxy
          (show Fin (ASize x.active) from
            ⟨t.1, by simp[Q]⟩)

      have hiqft :=
        eval_IQFT_ket_exact
          (qs := qs)
          x
          (RegEncoding.writeNat y.active
            (inst.a ^ t.1 % inst.N)
            (RegEncoding.writeNat
              x.active t.1 b0))

      simpa [Q, c, hxt] using hiqft

    _ =
      ∑ t : Fin Q,
        ∑ o : Fin Q,
          ((1 / (Q : ℂ)) *
            star
              (qftPhase Q t.1 o.1)) •
            qs.ket
              (RegEncoding.writeNat
                x.active o.1
                (RegEncoding.writeNat y.active
                  (inst.a ^ t.1 % inst.N)
                  (RegEncoding.writeNat
                    x.active t.1 b0))) := by
      rw [Finset.smul_sum]

      apply Finset.sum_congr rfl
      intro t ht

      rw [smul_smul, Finset.smul_sum]

      apply Finset.sum_congr rfl
      intro o ho

      rw [smul_smul]

      congr 1
      rw [hscalar]

    _ =
      ∑ t : Fin Q,
        ∑ o : Fin Q,
          ((1 / (Q : ℂ)) *
            star
              (qftPhase Q t.1 o.1)) •
            qs.ket
              (shorOutputBasis
                (qs := qs)
                inst.a inst.N
                x y b0
                o.1
                (t.1 % r)) := by
      apply Finset.sum_congr rfl
      intro t ht

      apply Finset.sum_congr rfl
      intro o ho

      have hbasis :=
        shor_IQFT_output_basis_eq
          (qs := qs)
          inst x y b0 hxy
          (show Fin (ASize x.active) from
            ⟨t.1, by simp[Q]⟩)
          (show Fin (ASize x.active) from
            ⟨o.1, by simp[Q]⟩)

      simpa [r] using
        congrArg
          (fun b =>
            ((1 / (Q : ℂ)) *
              star
                (qftPhase Q t.1 o.1)) •
              qs.ket b)
          hbasis

    _ =
      ∑ o : Fin Q,
        ∑ t : Fin Q,
          ((1 / (Q : ℂ)) *
            star
              (qftPhase Q t.1 o.1)) •
            qs.ket
              (shorOutputBasis
                (qs := qs)
                inst.a inst.N
                x y b0
                o.1
                (t.1 % r)) := by
      rw [Finset.sum_comm]

    _ =
      ∑ o : Fin Q,
        ∑ t ∈ Finset.range Q,
          ((1 / (Q : ℂ)) *
            star
              (qftPhase Q t o.1)) •
            qs.ket
              (shorOutputBasis
                (qs := qs)
                inst.a inst.N
                x y b0
                o.1
                (t % r)) := by
      apply Finset.sum_congr rfl
      intro o ho

      exact
        Fin.sum_univ_eq_sum_range
          (fun t =>
            ((1 / (Q : ℂ)) *
              star
                (qftPhase Q t o.1)) •
              qs.ket
                (shorOutputBasis
                  (qs := qs)
                  inst.a inst.N
                  x y b0
                  o.1
                  (t % r)))
          Q

    _ =
      ∑ o : Fin Q,
        ∑ s ∈ Finset.range r,
          shorPeriodClassAmplitude
              Q r s o.1 •
            qs.ket
              (shorOutputBasis
                (qs := qs)
                inst.a inst.N
                x y b0
                o.1 s) := by
      apply Finset.sum_congr rfl
      intro o ho

      simpa [Q, r] using
        (shor_group_fixed_output
          (qs := qs)
          inst x y b0
          (by simpa [r] using hr)
          (show Fin (ASize x.active) from
            ⟨o.1, by simp [Q]⟩))

    _ =
      shorGroupedPostIQFTState
        qs inst.a inst.N
        (ASize x.active)
        (ord inst.a inst.N inst.coprime)
        x y b0 := by
      simp [
        shorGroupedPostIQFTState,
        Q,
        r
      ]

@[simp]
private lemma shorOutputBasis_x_value
    (a N : ℕ)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (o : Fin (ASize x.active))
    (s : ℕ) :
    RegEncoding.toNat x.active
        (shorOutputBasis
          (qs := qs)
          a N x y b0 o.1 s)
      =
    o.1 := by
  exact
    RegEncoding.toNat_writeNat_of_lt
      x.active
      o.1
      (RegEncoding.writeNat y.active
        (a ^ s % N) b0)
      o.isLt

/--
Measuring exponent outcome `o` kills every outer Fourier component
except the component labelled by `o`.
-/
private lemma measProj_shorGroupedPostIQFTState
    [MeasureClass qs]
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (o : Fin (ASize x.active)) :
    MeasureClass.measProj x.active o.1
        (shorGroupedPostIQFTState
          qs
          inst.a inst.N
          (ASize x.active)
          (ord inst.a inst.N inst.coprime)
          x y b0)
      =
    ∑ s ∈
        Finset.range
          (ord inst.a inst.N inst.coprime),
      shorPeriodClassAmplitude
          (ASize x.active)
          (ord inst.a inst.N inst.coprime)
          s o.1 •
        qs.ket
          (shorOutputBasis
            (qs := qs)
            inst.a inst.N
            x y b0 o.1 s) := by
  classical

  let P :=
    MeasureClass.measProj
      (qs := qs) x.active o.1

  unfold shorGroupedPostIQFTState
  change
    P
      (∑ o' : Fin (ASize x.active),
        ∑ s ∈
          Finset.range
            (ord inst.a inst.N inst.coprime),
          shorPeriodClassAmplitude
              (ASize x.active)
              (ord inst.a inst.N inst.coprime)
              s o'.1 •
            qs.ket
              (shorOutputBasis
                (qs := qs)
                inst.a inst.N
                x y b0 o'.1 s))
      =
    _

  rw [map_sum]

  have hkeep :
      P
          (∑ s ∈
            Finset.range
              (ord inst.a inst.N inst.coprime),
            shorPeriodClassAmplitude
                (ASize x.active)
                (ord inst.a inst.N inst.coprime)
                s o.1 •
              qs.ket
                (shorOutputBasis
                  (qs := qs)
                  inst.a inst.N
                  x y b0 o.1 s))
        =
      ∑ s ∈
        Finset.range
          (ord inst.a inst.N inst.coprime),
        shorPeriodClassAmplitude
            (ASize x.active)
            (ord inst.a inst.N inst.coprime)
            s o.1 •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0 o.1 s) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [map_smul]
    dsimp [P]
    rw [MeasureClass.measProj_ket]
    simp [shorOutputBasis_x_value]

  refine
    Finset.sum_eq_single o ?_ ?_ |>.trans hkeep

  · intro o' ho' hne

    have hval :
        o'.1 ≠ o.1 := by
      intro h
      apply hne
      exact Fin.ext h

    rw [map_sum]

    apply Finset.sum_eq_zero
    intro s hs

    rw [map_smul]
    dsimp [P]
    rw [MeasureClass.measProj_ket]

    have hx :
        RegEncoding.toNat x.active
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0 o'.1 s)
          =
        o'.1 := by
      exact
        RegEncoding.toNat_writeNat_of_lt
          x.active
          o'.1
          (RegEncoding.writeNat y.active
            (inst.a ^ s % inst.N) b0)
          o'.isLt

    simp [hx, hval]

  · intro ho
    exact False.elim (ho (Finset.mem_univ o))

private lemma shorOutputBasis_ne_of_residue_ne
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (o : Fin (ASize x.active))
    {s t : ℕ}
    (hs :
      s < ord inst.a inst.N inst.coprime)
    (ht :
      t < ord inst.a inst.N inst.coprime)
    (hst : s ≠ t)
    (hsetting :
      BasicSetting
        inst.a
        (ord inst.a inst.N inst.coprime)
        inst.N
        (regSize x.active)
        (regSize y.active))
    (hinput :
      IdealOrderFindingInput qs x y b0) :
    shorOutputBasis
        (qs := qs)
        inst.a inst.N x y b0 o.1 s
      ≠
    shorOutputBasis
        (qs := qs)
        inst.a inst.N x y b0 o.1 t := by
  classical

  have howned :
      ExtReg.OwnedDisjoint x y :=
    hinput.2.2

  have hxy :
      Disjoint x.active y.active :=
    active_disjoint_of_ownedDisjoint howned

  rcases hsetting with
    ⟨_ha0, _haN, _hord,
      _hmlo, _hmhi, hNlt, _hnhi⟩

  have hNpos :
      0 < inst.N := by
    omega

  have hNlt' :
      inst.N < ASize y.active := by
    simpa [ASize] using hNlt

  have hslt :
      inst.a ^ s % inst.N < ASize y.active := by
    exact lt_trans
      (Nat.mod_lt _ hNpos)
      hNlt'

  have htlt :
      inst.a ^ t % inst.N < ASize y.active := by
    exact lt_trans
      (Nat.mod_lt _ hNpos)
      hNlt'

  have hread_s :
      RegEncoding.toNat y.active
          (shorOutputBasis
            (qs := qs)
            inst.a inst.N x y b0 o.1 s)
        =
      inst.a ^ s % inst.N := by
    unfold shorOutputBasis

    rw [
      RegEncoding.toNat_left_write_right
        y.active
        x.active
        (Disjoint.symm hxy)
    ]

    exact
      RegEncoding.toNat_writeNat_of_lt
        y.active
        (inst.a ^ s % inst.N)
        b0
        hslt

  have hread_t :
      RegEncoding.toNat y.active
          (shorOutputBasis
            (qs := qs)
            inst.a inst.N x y b0 o.1 t)
        =
      inst.a ^ t % inst.N := by
    unfold shorOutputBasis

    rw [
      RegEncoding.toNat_left_write_right
        y.active
        x.active
        (Disjoint.symm hxy)
    ]

    exact
      RegEncoding.toNat_writeNat_of_lt
        y.active
        (inst.a ^ t % inst.N)
        b0
        htlt

  intro heq

  have hpowers :
      inst.a ^ s % inst.N =
      inst.a ^ t % inst.N := by
    have h :=
      congrArg
        (RegEncoding.toNat y.active)
        heq

    simpa [hread_s, hread_t] using h

  apply hst

  exact
    shor_pow_mod_injective_below_order
      inst hs ht hpowers

omit [RegEncoding QSemantics.Basis] in
private lemma norm_sq_sum_eq_sum_norm_sq_of_orthogonal_shor
    {ι : Type*}
    (S : Finset ι)
    (f : ι → qs.State)
    (horth :
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        inner ℂ (f i) (f j) = 0) :
    ‖∑ i ∈ S, f i‖ ^ 2
      =
    ∑ i ∈ S, ‖f i‖ ^ 2 := by
  classical

  revert horth

  induction S using Finset.induction_on with
  | empty =>
      intro _
      simp

  | insert a S ha ih =>
      intro horth

      have horthS :
          ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
            inner ℂ (f i) (f j) = 0 := by
        intro i hi j hj hij
        exact
          horth
            i (Finset.mem_insert_of_mem hi)
            j (Finset.mem_insert_of_mem hj)
            hij

      have hih :
          ‖∑ i ∈ S, f i‖ ^ 2
            =
          ∑ i ∈ S, ‖f i‖ ^ 2 :=
        ih horthS

      have hcross :
          inner ℂ (f a) (∑ i ∈ S, f i) = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro i hi

        apply
          horth
            a
            (by simp)
            i
            (Finset.mem_insert_of_mem hi)

        intro hai
        subst i
        exact ha hi

      calc
        ‖∑ i ∈ insert a S, f i‖ ^ 2
            =
          ‖f a + ∑ i ∈ S, f i‖ ^ 2 := by
            rw [Finset.sum_insert ha]

        _ =
          ‖f a‖ ^ 2
            +
          2 * Complex.re
            (inner ℂ (f a) (∑ i ∈ S, f i))
            +
          ‖∑ i ∈ S, f i‖ ^ 2 := by
            exact norm_add_sq (𝕜 := ℂ) _ _

        _ =
          ‖f a‖ ^ 2 +
          ‖∑ i ∈ S, f i‖ ^ 2 := by
            rw [hcross]
            simp

        _ =
          ‖f a‖ ^ 2 +
          ∑ i ∈ S, ‖f i‖ ^ 2 := by
            rw [hih]

        _ =
          ∑ i ∈ insert a S, ‖f i‖ ^ 2 := by
            rw [Finset.sum_insert ha]
/--
The data-register states corresponding to distinct `s < r` are
orthogonal, so the squared norm of the period-class superposition is
the sum of the squared coefficient norms.
-/
private lemma norm_sq_shor_period_class_sum
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
    (hinput :
      IdealOrderFindingInput qs x y b0)
    (o : Fin (ASize x.active)) :
    ‖ ∑ s ∈ Finset.range (ord inst.a inst.N inst.coprime),
        shorPeriodClassAmplitude
            (ASize x.active)
            (ord inst.a inst.N inst.coprime)
            s o.1 •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0 o.1 s)‖ ^ 2
      =
    shorPaperOutcomeProb
      (ASize x.active)
      (ord inst.a inst.N inst.coprime)
      o.1 := by
  classical

  let r : ℕ :=
    ord inst.a inst.N inst.coprime

  let S : Finset ℕ :=
    Finset.range r

  let α : ℕ → ℂ :=
    fun s =>
      shorPeriodClassAmplitude
        (ASize x.active)
        r s o.1

  let label : ℕ → qs.Basis :=
    fun s =>
      shorOutputBasis
        (qs := qs)
        inst.a inst.N
        x y b0 o.1 s

  have horth :
      ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
        inner ℂ
          (α s • qs.ket (label s))
          (α t • qs.ket (label t))
          =
        0 := by
    intro s hs t ht hst

    have hs' : s < r :=
      Finset.mem_range.mp hs

    have ht' : t < r :=
      Finset.mem_range.mp ht

    have hlabel :
        label s ≠ label t := by
      dsimp [label]
      exact
        shorOutputBasis_ne_of_residue_ne
          (qs := qs)
          inst
          x y b0 o
          (by simpa [r] using hs')
          (by simpa [r] using ht')
          hst
          hsetting
          hinput

    rw [
      inner_smul_left,
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne hlabel
    ]

    simp

  have hpyth :
      ‖∑ s ∈ S,
          α s • qs.ket (label s)‖ ^ 2
        =
      ∑ s ∈ S,
        ‖α s • qs.ket (label s)‖ ^ 2 :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_shor
      S
      (fun s =>
        α s • qs.ket (label s))
      horth

  calc
    ‖
      ∑ s ∈
        Finset.range
          (ord inst.a inst.N inst.coprime),
        shorPeriodClassAmplitude
            (ASize x.active)
            (ord inst.a inst.N inst.coprime)
            s o.1 •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0 o.1 s)
    ‖ ^ 2
        =
      ∑ s ∈ S,
        ‖α s • qs.ket (label s)‖ ^ 2 := by
          simpa [S, α, label, r] using hpyth

    _ =
      ∑ s ∈ S,
        ‖α s‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [norm_smul, ket_norm_one qs]

    _ =
      shorPaperOutcomeProb
        (ASize x.active)
        (ord inst.a inst.N inst.coprime)
        o.1 := by
      simp [
        S,
        α,
        r,
        shorPaperOutcomeProb
      ]

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
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    [MeasureClass qs]
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
  classical

  /-
  First expose the final IQFT.
  -/
  have hcircuit :
      qs.eval
          (orderFindingIdeal
            (qs := qs)
            inst.a inst.N x y)
          (qs.ket b0)
        =
      qs.eval
          (IQFT x)
          (idealPreIQFTState
            qs inst.a inst.N x y b0) := by
    have h :=
      congrArg
        (fun ψ : qs.State =>
          qs.eval (IQFT x) ψ)
        hpre

    simpa [
      orderFindingIdeal,
      qs.eval_seq
    ] using h

  /-
  Regroup the final state by residue class modulo r.
  -/
  have hgroup :
      qs.eval
          (IQFT x)
          (idealPreIQFTState
            qs inst.a inst.N x y b0)
        =
      shorGroupedPostIQFTState
        qs
        inst.a inst.N
        (ASize x.active)
        (ord inst.a inst.N inst.coprime)
        x y b0 :=
    eval_IQFT_idealPreIQFTState_grouped
      inst x y b0
      hsetting hinput

  /-
  The x-measurement projector keeps precisely output `o`.
  -/
  have hproj :
      MeasureClass.measProj
          x.active o.1
          (shorGroupedPostIQFTState
            qs
            inst.a inst.N
            (ASize x.active)
            (ord inst.a inst.N inst.coprime)
            x y b0)
        =
      ∑ s ∈
          Finset.range
            (ord inst.a inst.N inst.coprime),
        shorPeriodClassAmplitude
            (ASize x.active)
            (ord inst.a inst.N inst.coprime)
            s o.1 •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0 o.1 s) :=
    measProj_shorGroupedPostIQFTState
      inst x y b0 o

  /-
  Distinct residues give orthogonal y-register states.
  -/
  have hnorm :
      ‖∑ s ∈ Finset.range (ord inst.a inst.N inst.coprime),
          shorPeriodClassAmplitude (ASize x.active) (ord inst.a inst.N inst.coprime) s o.1 •
            qs.ket
              (shorOutputBasis (qs := qs) inst.a inst.N x y b0 o.1 s)‖ ^ 2
        =
      shorPaperOutcomeProb
        (ASize x.active)
        (ord inst.a inst.N inst.coprime)
        o.1 :=
    norm_sq_shor_period_class_sum
      inst x y b0
      hsetting hinput o

  unfold measProbAfter
  rw [MeasureClass.probMeas_born]
  rw [hcircuit, hgroup, hproj]

  exact hnorm

/-! ---------------------------------------------------------
    Step 4: Shor equations (5.11)--(5.13)
--------------------------------------------------------- -/
/-! =========================================================
    Fourier peak bound for ideal Shor
========================================================= -/

/--
The Fourier coefficient of the period-class amplitude vector
in character `k`.
-/
private noncomputable def shorSpectralAmplitude
    (Q r k o : ℕ) : ℂ :=
  (1 / (Q : ℂ)) *
    ∑ t ∈ Finset.range Q,
      qftPhase r t k * star (qftPhase Q t o)


/--
The ordinary normalized QPE geometric sum corresponding to
the rational-frequency difference `k/r - o/Q`.
-/
private noncomputable def shorQPEAmplitude
    (Q r k o : ℕ) : ℂ :=
  let δ : ℝ :=
    (k : ℝ) / (r : ℝ) -
      (o : ℝ) / (Q : ℝ)
  let ζ : ℂ :=
    Complex.exp
      (Complex.I *
        ((2 * Real.pi * δ : ℝ) : ℂ))
  (1 / (Q : ℂ)) *
    ∑ t ∈ Finset.range Q, ζ ^ t

private lemma qftPhase_eq_exp_grid_shor
    (M z t : ℕ) :
    qftPhase M z t
      =
    Complex.exp
      (((2 * Real.pi) / (M : ℝ)) * Complex.I *
        ((z : ℂ) * (t : ℂ))) := by
  simp [
    qftPhase,
    ωPow,
    ω,
    div_eq_mul_inv,
    mul_assoc,
    mul_left_comm,
    mul_comm
  ]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring


private lemma star_qftPhase_eq_negative_grid_phase_shor
    (M z t : ℕ) :
    star (qftPhase M z t)
      =
    Complex.exp
      (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (((z : ℂ) * (t : ℂ)) / (M : ℂ)))) := by
  rw [qftPhase_eq_exp_grid_shor]
  simp
  rw [← Complex.exp_conj]
  congr 1
  simp [div_eq_mul_inv]
  simp [starRingEnd]
  ring

private lemma omega_pow_self_shor
    (r : ℕ)
    (hr : 0 < r) :
    (ω r) ^ r = 1 := by
  unfold ω

  rw [← Complex.exp_nat_mul]

  have hr0 : (r : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hr

  have harg :
      (r : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I /
            (r : ℂ))
        =
      2 * (Real.pi : ℂ) * Complex.I := by
    field_simp [hr0]

  rw [harg, Complex.exp_two_pi_mul_I]


private lemma qftPhase_mod_left_shor
    (r t k : ℕ)
    (hr : 0 < r) :
    qftPhase r t k =
      qftPhase r (t % r) k := by
  unfold qftPhase ωPow

  have ht :
      t * k =
        (t % r) * k +
          r * ((t / r) * k) := by
    calc
      t * k
          =
        (t % r + r * (t / r)) * k := by
          rw [Nat.mod_add_div]
      _ =
        (t % r) * k +
          r * ((t / r) * k) := by
            ring

  rw [ht, pow_add]

  have hp :
      (ω r) ^ (r * ((t / r) * k)) = 1 := by
    rw [pow_mul, omega_pow_self_shor r hr]
    simp

  rw [hp, mul_one]


private lemma norm_qftPhase_one_shor
    (M x y : ℕ) :
    ‖qftPhase M x y‖ = 1 := by
  rw [qftPhase_eq_exp_grid_shor, Complex.norm_exp]
  simp

private lemma shorSpectralAmplitude_eq_period_classes
    {Q r k o : ℕ}
    (hr : 0 < r) :
    shorSpectralAmplitude Q r k o
      =
    ∑ s ∈ Finset.range r,
      qftPhase r s k *
        shorPeriodClassAmplitude Q r s o := by
  classical

  unfold shorSpectralAmplitude
  unfold shorPeriodClassAmplitude

  calc
    (1 / (Q : ℂ)) *
        ∑ t ∈ Finset.range Q,
          qftPhase r t k *
            star (qftPhase Q t o)
        =
      (1 / (Q : ℂ)) *
        ∑ t ∈ Finset.range Q,
          qftPhase r (t % r) k *
            star (qftPhase Q t o) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      rw [qftPhase_mod_left_shor r t k hr]

    _ =
      (1 / (Q : ℂ)) *
        ∑ s ∈ Finset.range r,
          ∑ t ∈
              (Finset.range Q).filter
                (fun t => t % r = s),
            qftPhase r s k *
              star (qftPhase Q t o) := by
      congr 1
      exact
        sum_range_group_by_mod
          Q r hr
          (fun s t =>
            qftPhase r s k *
              star (qftPhase Q t o))

    _ =
      ∑ s ∈ Finset.range r,
        qftPhase r s k *
          ((1 / (Q : ℂ)) *
            ∑ t ∈
                (Finset.range Q).filter
                  (fun t => t % r = s),
              star (qftPhase Q t o)) := by
      rw [Finset.mul_sum]

      apply Finset.sum_congr rfl
      intro s hs

      rw [← Finset.mul_sum]
      ring

private lemma sq_sum_le_card_mul_sum_sq_shor
    {ι : Type*}
    (S : Finset ι)
    (f : ι → ℝ) :
    (∑ i ∈ S, f i) ^ 2
      ≤
    (S.card : ℝ) *
      ∑ i ∈ S, (f i) ^ 2 := by
  classical

  induction S using Finset.induction_on with
  | empty =>
      simp

  | @insert a S ha ih =>
      by_cases hS : S = ∅

      · subst S
        simp

      ·
        have hcardNat : 0 < S.card :=
          Finset.card_pos.mpr
            (Finset.nonempty_iff_ne_empty.mpr hS)

        have hcard :
            0 < (S.card : ℝ) := by
          exact_mod_cast hcardNat

        let A : ℝ :=
          ∑ i ∈ S, f i

        let B : ℝ :=
          ∑ i ∈ S, (f i) ^ 2

        have hih :
            A ^ 2 ≤
              (S.card : ℝ) * B := by
          simpa [A, B] using ih

        have hcross :
            2 * f a * A
              ≤
            B + (S.card : ℝ) * (f a) ^ 2 := by
          have hsquare :
              0 ≤
                (A - (S.card : ℝ) * f a) ^ 2 :=
            sq_nonneg _

          nlinarith [hih, hsquare]

        simp [
          Finset.sum_insert,
          ha,
          Finset.card_insert_of_notMem,
          Nat.cast_add,
          Nat.cast_one
        ]

        change
          (f a + A) ^ 2
            ≤
          ((S.card : ℝ) + 1) *
            ((f a) ^ 2 + B)

        nlinarith [hih, hcross]

private lemma norm_sum_le_sum_norm_shor
    {ι : Type*}
    (S : Finset ι)
    (f : ι → ℂ) :
    ‖∑ i ∈ S, f i‖
      ≤
    ∑ i ∈ S, ‖f i‖ := by
  classical

  induction S using Finset.induction_on with
  | empty =>
      simp

  | @insert a S ha ih =>
      rw [Finset.sum_insert ha]
      rw [Finset.sum_insert ha]

      exact
        le_trans
          (norm_add_le (f a) (∑ i ∈ S, f i))
          (add_le_add (le_refl ‖f a‖) ih)

private lemma shorSpectralAmplitude_sq_le_paper
    {Q r k o : ℕ}
    (hr : 0 < r) :
    ‖shorSpectralAmplitude Q r k o‖ ^ 2
      ≤
    (r : ℝ) *
      shorPaperOutcomeProb Q r o := by
  classical

  let A : ℕ → ℂ :=
    fun s =>
      shorPeriodClassAmplitude
        Q r s o

  have hregroup :
      shorSpectralAmplitude Q r k o
        =
      ∑ s ∈ Finset.range r,
        qftPhase r s k * A s := by
    simpa [A] using
      (shorSpectralAmplitude_eq_period_classes
        (Q := Q) (r := r) (k := k) (o := o) hr)

  rw [hregroup]

  have htri0 :
      ‖∑ s ∈ Finset.range r,
          qftPhase r s k * A s‖
        ≤
      ∑ s ∈ Finset.range r,
        ‖qftPhase r s k * A s‖ :=
    norm_sum_le_sum_norm_shor
      (Finset.range r)
      (fun s =>
        qftPhase r s k * A s)

  have hterms :
      (∑ s ∈ Finset.range r,
          ‖qftPhase r s k * A s‖)
        =
      ∑ s ∈ Finset.range r,
        ‖A s‖ := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [norm_mul, norm_qftPhase_one_shor]
    simp

  have htri :
      ‖∑ s ∈ Finset.range r,
          qftPhase r s k * A s‖
        ≤
      ∑ s ∈ Finset.range r,
        ‖A s‖ := by
    exact htri0.trans_eq hterms

  have hsum_nonneg :
      0 ≤
      ∑ s ∈ Finset.range r,
        ‖A s‖ :=
    Finset.sum_nonneg
      (fun s hs => norm_nonneg _)

  have hnorm_nonneg :
      0 ≤
      ‖∑ s ∈ Finset.range r,
          qftPhase r s k * A s‖ :=
    norm_nonneg _

  have hsquare :
      ‖∑ s ∈ Finset.range r,
          qftPhase r s k * A s‖ ^ 2
        ≤
      (∑ s ∈ Finset.range r,
          ‖A s‖) ^ 2 := by

    have hprod :
        0 ≤
          ((∑ s ∈ Finset.range r, ‖A s‖) -
              ‖∑ s ∈ Finset.range r,
                  qftPhase r s k * A s‖) *
          ((∑ s ∈ Finset.range r, ‖A s‖) +
              ‖∑ s ∈ Finset.range r,
                  qftPhase r s k * A s‖) :=
      mul_nonneg
        (sub_nonneg.mpr htri)
        (add_nonneg hsum_nonneg hnorm_nonneg)

    nlinarith [hprod]

  have hcauchy :=
    sq_sum_le_card_mul_sum_sq_shor
      (Finset.range r)
      (fun s => ‖A s‖)

  calc
    ‖∑ s ∈ Finset.range r,
        qftPhase r s k * A s‖ ^ 2
        ≤
      (∑ s ∈ Finset.range r,
        ‖A s‖) ^ 2 :=
      hsquare

    _ ≤
      (r : ℝ) *
        ∑ s ∈ Finset.range r,
          ‖A s‖ ^ 2 := by
      simpa using hcauchy

    _ =
      (r : ℝ) *
        shorPaperOutcomeProb Q r o := by
      simp [
        A,
        shorPaperOutcomeProb
      ]

private lemma shorSpectralAmplitude_eq_qpe
    (Q r k o : ℕ) :
    shorSpectralAmplitude Q r k o
      =
    shorQPEAmplitude Q r k o := by
  classical

  unfold shorSpectralAmplitude
  unfold shorQPEAmplitude
  dsimp

  congr 1

  apply Finset.sum_congr rfl
  intro t ht

  rw [qftPhase_eq_exp_grid_shor]

  have hstar :
      (starRingEnd ℂ) (qftPhase Q t o)
        =
      Complex.exp
        (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (((t : ℂ) * (o : ℂ)) / (Q : ℂ)))) := by
    simpa only [starRingEnd] using
      (star_qftPhase_eq_negative_grid_phase_shor Q t o)

  rw [hstar, ← Complex.exp_add, ← Complex.exp_nat_mul]

  congr 1
  push_cast
  simp [div_eq_mul_inv]
  ring

private lemma norm_natCast_complex_shor
    (n : ℕ) :
    ‖(n : ℂ)‖ = (n : ℝ) := by
  simp


private lemma shor_normalized_geometric_peak
    (Q : ℕ)
    (δ : ℝ)
    (hQ : 0 < Q)
    (hδ :
      |δ| ≤ 1 / (2 * (Q : ℝ))) :
    2 / Real.pi
      ≤
    ‖(1 / (Q : ℂ)) *
      ∑ t ∈ Finset.range Q,
        (Complex.exp
          (Complex.I *
            ((2 * Real.pi * δ : ℝ) : ℂ))) ^ t‖ := by
  classical

  have hQr :
      0 < (Q : ℝ) := by
    exact_mod_cast hQ

  have hQC :
      (Q : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hQ

  let ζ : ℂ :=
    Complex.exp
      (Complex.I *
        ((2 * Real.pi * δ : ℝ) : ℂ))

  let G : ℂ :=
    ∑ t ∈ Finset.range Q, ζ ^ t

  change
    2 / Real.pi ≤
      ‖(1 / (Q : ℂ)) * G‖

  by_cases hδ0 : δ = 0

  ·
    have hζ :
        ζ = 1 := by
      simp [ζ, hδ0]

    have hG :
        G = (Q : ℂ) := by
      simp [G, hζ]

    have htwo :
        2 / Real.pi ≤ 1 := by
      apply (div_le_iff₀ Real.pi_pos).2
      simpa using Real.two_le_pi

    rw [hG]
    simpa [hQC] using htwo

  ·
    have hδpos :
        0 < |δ| :=
      abs_pos.mpr hδ0

    /- geometric-series identity -/
    have hgeom :
        G * (ζ - 1) =
          ζ ^ Q - 1 := by
      dsimp [G]
      exact geom_sum_mul ζ Q

    /-
    Upper bound on the denominator chord:

        |e^{2πiδ} - 1| ≤ 2π|δ|.
    -/
    have hden_upper :
        ‖ζ - 1‖
          ≤
        2 * Real.pi * |δ| := by
      dsimp [ζ]

      have h :=
        Real.norm_exp_I_mul_ofReal_sub_one_le
          (x := 2 * Real.pi * δ)

      calc
        ‖Complex.exp
            (Complex.I *
              ((2 * Real.pi * δ : ℝ) : ℂ)) - 1‖
            ≤
          ‖2 * Real.pi * δ‖ :=
            h

        _ =
          2 * Real.pi * |δ| := by
          rw [
            Real.norm_eq_abs,
            abs_mul,
            abs_mul,
            abs_of_nonneg
              (by norm_num : (0 : ℝ) ≤ 2),
            abs_of_pos Real.pi_pos
          ]

    /-
    From |δ| ≤ 1/(2Q),

        |π Q δ| ≤ π/2.
    -/
    have hQδ :
        (Q : ℝ) * |δ| ≤ 1 / 2 := by
      calc
        (Q : ℝ) * |δ|
            ≤
          (Q : ℝ) *
            (1 / (2 * (Q : ℝ))) :=
          mul_le_mul_of_nonneg_left
            hδ
            (le_of_lt hQr)

        _ = 1 / 2 := by
          field_simp [ne_of_gt hQr]

    have harg :
        |Real.pi * (Q : ℝ) * δ|
          ≤
        Real.pi / 2 := by
      calc
        |Real.pi * (Q : ℝ) * δ|
            =
          Real.pi *
            ((Q : ℝ) * |δ|) := by
          rw [
            abs_mul,
            abs_mul,
            abs_of_pos Real.pi_pos,
            abs_of_pos hQr
          ]
          ring

        _ ≤
          Real.pi * (1 / 2) :=
          mul_le_mul_of_nonneg_left
            hQδ
            (le_of_lt Real.pi_pos)

        _ =
          Real.pi / 2 := by
          ring

    /-
    Jordan:

        2/π |πQδ| ≤ |sin(πQδ)|,

    hence

        2Q|δ| ≤ |sin(πQδ)|.
    -/
    have hjordan :
        2 / Real.pi *
            |Real.pi * (Q : ℝ) * δ|
          ≤
        |Real.sin
          (Real.pi * (Q : ℝ) * δ)| :=
      Real.mul_abs_le_abs_sin harg

    have hsin_lower :
        2 * (Q : ℝ) * |δ|
          ≤
        |Real.sin
          (Real.pi * (Q : ℝ) * δ)| := by
      calc
        2 * (Q : ℝ) * |δ|
            =
          2 / Real.pi *
            |Real.pi * (Q : ℝ) * δ| := by
          rw [
            abs_mul,
            abs_mul,
            abs_of_pos Real.pi_pos,
            abs_of_pos hQr
          ]
          field_simp [Real.pi_ne_zero]

        _ ≤
          |Real.sin
            (Real.pi * (Q : ℝ) * δ)| :=
          hjordan

    /-
    ζ^Q = exp(i · 2πQδ).
    -/
    have hζpow :
        ζ ^ Q =
          Complex.exp
            (Complex.I *
              ((2 * Real.pi *
                  (Q : ℝ) * δ : ℝ) : ℂ)) := by
      dsimp [ζ]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring

    /-
    Exact numerator chord:

        |ζ^Q - 1| = 2 |sin(πQδ)|.
    -/
    have hnum_eq :
        ‖ζ ^ Q - 1‖
          =
        2 *
          |Real.sin
            (Real.pi * (Q : ℝ) * δ)| := by
      rw [
        hζpow,
        Complex.norm_exp_I_mul_ofReal_sub_one
      ]

      rw [Real.norm_eq_abs]

      have hhalf :
          (2 * Real.pi *
              (Q : ℝ) * δ) / 2
            =
          Real.pi * (Q : ℝ) * δ := by
        ring

      rw [hhalf, abs_mul]
      norm_num

    have hnum_lower :
        4 * (Q : ℝ) * |δ|
          ≤
        ‖ζ ^ Q - 1‖ := by
      rw [hnum_eq]
      nlinarith [hsin_lower]

    /-
    Multiply the geometric identity by norms:
      |G| |ζ-1| = |ζ^Q-1|.
    -/
    have hprod :
        ‖G‖ * ‖ζ - 1‖ =
          ‖ζ ^ Q - 1‖ := by
      calc
        ‖G‖ * ‖ζ - 1‖
            =
          ‖G * (ζ - 1)‖ := by
            rw [norm_mul]

        _ =
          ‖ζ ^ Q - 1‖ := by
            rw [hgeom]

    have hmain :
        4 * (Q : ℝ) * |δ|
          ≤
        ‖G‖ *
          (2 * Real.pi * |δ|) := by
      calc
        4 * (Q : ℝ) * |δ|
            ≤
          ‖ζ ^ Q - 1‖ :=
          hnum_lower

        _ =
          ‖G‖ * ‖ζ - 1‖ :=
          hprod.symm

        _ ≤
          ‖G‖ *
            (2 * Real.pi * |δ|) :=
          mul_le_mul_of_nonneg_left
            hden_upper
            (norm_nonneg _)

    /-
    Cancel the positive `2π|δ|`.
    -/
    have hD :
        0 <
          2 * Real.pi * |δ| := by
      positivity

    have hmul :
        (2 * (Q : ℝ) / Real.pi) *
            (2 * Real.pi * |δ|)
          ≤
        ‖G‖ *
            (2 * Real.pi * |δ|) := by
      calc
        (2 * (Q : ℝ) / Real.pi) *
            (2 * Real.pi * |δ|)
            =
          4 * (Q : ℝ) * |δ| := by
            field_simp [Real.pi_ne_zero]
            ring

        _ ≤
          ‖G‖ *
            (2 * Real.pi * |δ|) :=
          hmain

    have hG_lower :
        2 * (Q : ℝ) / Real.pi
          ≤
        ‖G‖ := by
      exact le_of_mul_le_mul_right hmul (by omega)

    /- put back the `1/Q` normalization -/
    have hscale :
        ‖(1 / (Q : ℂ))‖ =
          1 / (Q : ℝ) := by
      rw [
        norm_div,
        norm_one,
        norm_natCast_complex_shor
      ]

    rw [norm_mul, hscale]

    calc
      2 / Real.pi
          =
        (1 / (Q : ℝ)) *
          (2 * (Q : ℝ) / Real.pi) := by
        field_simp [
          ne_of_gt hQr,
          Real.pi_ne_zero
        ]

      _ ≤
        (1 / (Q : ℝ)) * ‖G‖ :=
        mul_le_mul_of_nonneg_left
          hG_lower
          (by positivity)

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
    (happrox :
      approxRat o Q k r
        (1 / (2 * (Q : ℝ)))) :
    (4 / Real.pi ^ 2) *
        (1 / (r : ℝ))
      ≤
    shorPaperOutcomeProb Q r o := by
  classical

  rcases happrox with
    ⟨hQ, hr, happ⟩

  let δ : ℝ :=
    (k : ℝ) / (r : ℝ) -
      (o : ℝ) / (Q : ℝ)

  have hδ :
      |δ| ≤
        1 / (2 * (Q : ℝ)) := by
    dsimp [δ]
    simpa [abs_sub_comm] using happ

  /-
  The relevant Fourier mode has amplitude at least `2 / π`.
  -/
  have hgeom :
      2 / Real.pi
        ≤
      ‖shorQPEAmplitude Q r k o‖ := by
    simpa [shorQPEAmplitude, δ] using
      (shor_normalized_geometric_peak
        Q δ hQ hδ)

  have hpeak :
      2 / Real.pi
        ≤
      ‖shorSpectralAmplitude Q r k o‖ := by
    rw [shorSpectralAmplitude_eq_qpe]
    exact hgeom

  /-
  Square the `2 / π` bound.
  -/
  have htwo_nonneg :
      0 ≤ 2 / Real.pi := by
    positivity

  have hsqprod :
      0 ≤
        (‖shorSpectralAmplitude Q r k o‖ -
            2 / Real.pi) *
        (‖shorSpectralAmplitude Q r k o‖ +
            2 / Real.pi) :=
    mul_nonneg
      (sub_nonneg.mpr hpeak)
      (add_nonneg
        (norm_nonneg _)
        htwo_nonneg)

  have hpeak_sq :
      4 / Real.pi ^ 2
        ≤
      ‖shorSpectralAmplitude Q r k o‖ ^ 2 := by
    have hsq :
        (2 / Real.pi) ^ 2
          ≤
        ‖shorSpectralAmplitude Q r k o‖ ^ 2 := by
      nlinarith [hsqprod]

    calc
      4 / Real.pi ^ 2
          =
        (2 / Real.pi) ^ 2 := by
          field_simp [Real.pi_ne_zero]
          ring

      _ ≤
        ‖shorSpectralAmplitude Q r k o‖ ^ 2 :=
        hsq

  /-
  Cauchy-Schwarz:
      |B_k|² ≤ r · P(o).
  -/
  have hspectral :
      ‖shorSpectralAmplitude Q r k o‖ ^ 2
        ≤
      (r : ℝ) *
        shorPaperOutcomeProb Q r o :=
    shorSpectralAmplitude_sq_le_paper
      (Q := Q)
      (r := r)
      (k := k)
      (o := o)
      hr

  have hrR :
      0 < (r : ℝ) := by
    exact_mod_cast hr

  /-
  Divide the resulting inequality by `r`.
  -/
  have hmul :
      (r : ℝ) *
          ((4 / Real.pi ^ 2) *
            (1 / (r : ℝ)))
        ≤
      (r : ℝ) *
        shorPaperOutcomeProb Q r o := by
    calc
      (r : ℝ) *
          ((4 / Real.pi ^ 2) *
            (1 / (r : ℝ)))
          =
        4 / Real.pi ^ 2 := by
          field_simp [
            ne_of_gt hrR,
            Real.pi_ne_zero
          ]

      _ ≤
        ‖shorSpectralAmplitude Q r k o‖ ^ 2 :=
        hpeak_sq

      _ ≤
        (r : ℝ) *
          shorPaperOutcomeProb Q r o :=
        hspectral

  by_contra h
  have hlt :
      shorPaperOutcomeProb Q r o
        <
      (4 / Real.pi ^ 2) * (1 / (r : ℝ)) :=
    lt_of_not_ge h

  have hmul' :
      (r : ℝ) * shorPaperOutcomeProb Q r o
        <
      (r : ℝ) *
        ((4 / Real.pi ^ 2) * (1 / (r : ℝ))) :=
    mul_lt_mul_of_pos_left hlt hrR

  exact (not_lt_of_ge hmul) hmul'


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

  exact shor_paper_peak_lower_bound happrox


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

@[simp]
lemma mem_goodOutcomeFinset
    {Q r : ℕ}
    (o : Fin Q) :
    o ∈ goodOutcomeFinset Q r ↔
      GoodOutcome o.1 Q r := by
  classical
  simp [goodOutcomeFinset]

private noncomputable def shorNearestOutput
    (Q r k : ℕ) : ℕ :=
  ⌊((Q : ℝ) * (k : ℝ) / (r : ℝ) + (1 : ℝ) / 2)⌋₊

private lemma shorNearestOutput_spec
    {Q r k : ℕ}
    (hr : 0 < r)
    (hrQ : r ^ 2 ≤ Q)
    (hk : k < r) :
    shorNearestOutput Q r k < Q ∧
      approxRat
        (shorNearestOutput Q r k)
        Q k r
        (1 / (2 * (Q : ℝ))) := by
  classical

  have hQ : 0 < Q := by
    have hr2 : 0 < r ^ 2 := by positivity
    omega

  have hrR : 0 < (r : ℝ) := by
    exact_mod_cast hr

  have hQR : 0 < (Q : ℝ) := by
    exact_mod_cast hQ

  let x : ℝ :=
    (Q : ℝ) * (k : ℝ) / (r : ℝ)

  let a : ℝ :=
    x + 1 / 2

  let o : ℕ :=
    shorNearestOutput Q r k

  have ho_floor :
      o = ⌊a⌋₊ := by
    simp [o, shorNearestOutput, a, x]

  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity

  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity

  /-
  floor(a) ≤ a < floor(a) + 1.
  -/
  have hfloor_le :
      (o : ℝ) ≤ a := by
    rw [ho_floor]
    exact
      (Nat.le_floor_iff ha0).mp
        (le_refl ⌊a⌋₊)

  have hfloor_lt :
      a < (o : ℝ) + 1 := by
    rw [ho_floor]

    by_contra h

    have hge :
        ((⌊a⌋₊ : ℕ) : ℝ) + 1 ≤ a :=
      le_of_not_gt h

    have hbad :
        ⌊a⌋₊ + 1 ≤ ⌊a⌋₊ := by
      apply Nat.le_floor
      simpa [Nat.cast_add, Nat.cast_one] using hge

    omega

  /-
  Hence the rounded integer is within 1/2 of x.
  -/
  have hround :
      |(o : ℝ) - x| ≤ 1 / 2 := by
    rw [abs_le]

    constructor
    · dsimp [a] at hfloor_lt
      linarith

    · dsimp [a] at hfloor_le
      linarith

  /-
  Since k ≤ r - 1 and Q ≥ r²,

      Q - Q*k/r ≥ Q/r ≥ 1,

  so rounding cannot reach Q.
  -/
  have hr1 : 1 ≤ r := by
    omega

  have hr_le_sq :
      r ≤ r ^ 2 := by
    calc
      r = r * 1 := by simp
      _ ≤ r * r := by
        exact Nat.mul_le_mul_left r hr1
      _ = r ^ 2 := by
        ring

  have hrQ' :
      r ≤ Q :=
    le_trans hr_le_sq hrQ

  have hqdiv :
      (1 : ℝ) ≤ (Q : ℝ) / (r : ℝ) := by
    apply (le_div_iff₀ hrR).2
    have h : (r : ℝ) ≤ (Q : ℝ) := by
      exact_mod_cast hrQ'
    simpa using h

  have hk1 :
      k + 1 ≤ r :=
    Nat.succ_le_of_lt hk

  have hkR :
      (k : ℝ) + 1 ≤ (r : ℝ) := by
    exact_mod_cast hk1

  have hgap :
      (1 : ℝ) ≤ (r : ℝ) - (k : ℝ) := by
    linarith

  have hprod :
      (1 : ℝ) ≤
        ((Q : ℝ) / (r : ℝ)) *
          ((r : ℝ) - (k : ℝ)) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤
          ((Q : ℝ) / (r : ℝ)) *
            ((r : ℝ) - (k : ℝ)) := by
        exact mul_le_mul
          hqdiv hgap
          (by norm_num)
          (by linarith)

  have hQminusx :
      (Q : ℝ) - x =
        ((Q : ℝ) / (r : ℝ)) *
          ((r : ℝ) - (k : ℝ)) := by
    dsimp [x]
    field_simp [ne_of_gt hrR]

  have hQgap :
      (1 : ℝ) ≤ (Q : ℝ) - x := by
    rw [hQminusx]
    exact hprod

  have haQ :
      a < (Q : ℝ) := by
    dsimp [a]
    linarith

  have hoQ_real :
      (o : ℝ) < (Q : ℝ) :=
    lt_of_le_of_lt hfloor_le haQ

  have hoQ :
      o < Q := by
    exact_mod_cast hoQ_real

  /-
  Divide the rounding error by Q.
  -/
  have hdiff :
      (o : ℝ) / (Q : ℝ) -
          (k : ℝ) / (r : ℝ)
        =
      ((o : ℝ) - x) / (Q : ℝ) := by
    dsimp [x]
    field_simp [
      ne_of_gt hQR,
      ne_of_gt hrR
    ]

  have happ :
      |(o : ℝ) / (Q : ℝ) -
          (k : ℝ) / (r : ℝ)|
        ≤
      1 / (2 * (Q : ℝ)) := by
    rw [
      hdiff,
      abs_div,
      abs_of_pos hQR
    ]

    calc
      |(o : ℝ) - x| / (Q : ℝ)
          ≤
        (1 / 2) / (Q : ℝ) :=
        div_le_div_of_nonneg_right
          hround
          (le_of_lt hQR)

      _ =
        1 / (2 * (Q : ℝ)) := by
          field_simp [ne_of_gt hQR]

  refine ⟨hoQ, ?_⟩

  refine ⟨hQ, hr, ?_⟩

  simpa [abs_sub_comm] using happ

private lemma shorNearestOutput_injective_below
    {Q r k₁ k₂ : ℕ}
    (hr : 0 < r)
    (hrQ : r ^ 2 ≤ Q)
    (hk₁ : k₁ < r)
    (hk₂ : k₂ < r)
    (heq : shorNearestOutput Q r k₁ = shorNearestOutput Q r k₂) :
    k₁ = k₂ := by

  by_cases hr1 : r = 1
  · omega

  have hrgt : 1 < r := by
    omega

  have hQ : 0 < Q := by
    have hr2 : 0 < r ^ 2 := by positivity
    omega

  have hrR : 0 < (r : ℝ) := by
    exact_mod_cast hr

  have hQR : 0 < (Q : ℝ) := by
    exact_mod_cast hQ

  by_contra hne

  have ha₁ :=
    (shorNearestOutput_spec
      (Q := Q) (r := r) (k := k₁)
      hr hrQ hk₁).2

  have ha₂ :=
    (shorNearestOutput_spec
      (Q := Q) (r := r) (k := k₂)
      hr hrQ hk₂).2

  rcases ha₁ with
    ⟨_hQ₁, _hr₁, ha₁⟩

  rcases ha₂ with
    ⟨_hQ₂, _hr₂, ha₂⟩

  rw [← heq] at ha₂

  /-
  If both rationals lie within 1/(2Q) of the same output,
  then they are within 1/Q of each other.
  -/
  have htri :
      |(k₁ : ℝ) / (r : ℝ) -
          (k₂ : ℝ) / (r : ℝ)|
        ≤
      1 / (Q : ℝ) := by
    calc
      |(k₁ : ℝ) / (r : ℝ) -
          (k₂ : ℝ) / (r : ℝ)|
          =
        |((k₁ : ℝ) / (r : ℝ) -
            (shorNearestOutput Q r k₁ : ℝ) /
              (Q : ℝ))
          +
          ((shorNearestOutput Q r k₁ : ℝ) /
              (Q : ℝ) -
            (k₂ : ℝ) / (r : ℝ))| := by
          congr 1
          ring

      _ ≤
        |(k₁ : ℝ) / (r : ℝ) -
            (shorNearestOutput Q r k₁ : ℝ) /
              (Q : ℝ)|
        +
        |(shorNearestOutput Q r k₁ : ℝ) /
              (Q : ℝ) -
            (k₂ : ℝ) / (r : ℝ)| :=
          abs_add_le _ _

      _ ≤
        1 / (2 * (Q : ℝ)) +
        1 / (2 * (Q : ℝ)) := by
          apply add_le_add
          · simpa [abs_sub_comm] using ha₁
          · exact ha₂

      _ =
        1 / (Q : ℝ) := by
          field_simp [ne_of_gt hQR]
          ring

  have hfrac :
      |(k₁ : ℝ) - (k₂ : ℝ)| /
          (r : ℝ)
        ≤
      1 / (Q : ℝ) := by
    have he :
        |(k₁ : ℝ) / (r : ℝ) -
            (k₂ : ℝ) / (r : ℝ)|
          =
        |(k₁ : ℝ) - (k₂ : ℝ)| /
          (r : ℝ) := by
      rw [
        ← sub_div,
        abs_div,
        abs_of_pos hrR
      ]

    rw [← he]
    exact htri

  /-
  Distinct natural numbers differ by at least one.
  -/
  have hdiff :
      (1 : ℝ) ≤
        |(k₁ : ℝ) - (k₂ : ℝ)| := by
    rcases lt_or_gt_of_ne hne with hlt | hgt

    · have hg :
          (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hlt

      have hnonpos :
          (k₁ : ℝ) - (k₂ : ℝ) ≤ 0 := by
        have hle : (k₁ : ℝ) ≤ (k₂ : ℝ) := by
          exact_mod_cast Nat.le_of_lt hlt
        linarith

      rw [abs_of_nonpos hnonpos]
      linarith

    · have hg :
          (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hgt

      have hnonneg :
          0 ≤ (k₁ : ℝ) - (k₂ : ℝ) := by
        have hle : (k₂ : ℝ) ≤ (k₁ : ℝ) := by
          exact_mod_cast Nat.le_of_lt hgt
        linarith

      rw [abs_of_nonneg hnonneg]
      linarith

  have hrecip :
      1 / (r : ℝ) ≤ 1 / (Q : ℝ) := by
    calc
      1 / (r : ℝ)
          ≤
        |(k₁ : ℝ) - (k₂ : ℝ)| /
          (r : ℝ) :=
        div_le_div_of_nonneg_right
          hdiff
          (le_of_lt hrR)

      _ ≤ 1 / (Q : ℝ) :=
        hfrac

  /-
  1/r ≤ 1/Q implies Q ≤ r.
  -/
  have hQrR :
      (Q : ℝ) ≤ (r : ℝ) :=
    le_of_one_div_le_one_div
      hrR hrecip

  have hQr :
      Q ≤ r := by
    exact_mod_cast hQrR

  have hrsq :
      r < r ^ 2 := by
    calc
      r = r * 1 := by simp
      _ < r * r :=
        Nat.mul_lt_mul_of_pos_left
          hrgt hr
      _ = r ^ 2 := by
        ring

  omega
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
  classical

  let S : Finset ℕ :=
    (Finset.range r).filter (Nat.Coprime r)

  let f :
      ↥S →
        ↥(goodOutcomeFinset Q r) :=
    fun k => by
      have hkS :
          k.1 ∈ S :=
        k.2

      have hkdata :
          k.1 < r ∧
            Nat.Coprime r k.1 := by
        have hkfilter :
            k.1 ∈ (Finset.range r).filter (Nat.Coprime r) := by
          simp [S] at hkS ⊢
        exact
          ⟨
            Finset.mem_range.mp (Finset.mem_filter.mp hkfilter).1,
            (Finset.mem_filter.mp hkfilter).2
          ⟩

      have hk :
          k.1 < r :=
        hkdata.1

      have hspec :=
        shorNearestOutput_spec
          (Q := Q)
          (r := r)
          (k := k.1)
          hr hrQ hk

      exact
        ⟨
          ⟨shorNearestOutput Q r k.1,
            hspec.1⟩,
          by
            rw [mem_goodOutcomeFinset]

            refine
              ⟨k.1, hk, ?_, hrQ, hspec.2⟩

            exact hkdata.2.symm
        ⟩

  have hf :
      Function.Injective f := by
    intro k₁ k₂ h

    apply Subtype.ext

    have hk₁ :
        k₁.1 < r := by
      have hmem :
          k₁.1 ∈ (Finset.range r).filter (Nat.Coprime r) := by
        simp [S] at k₁ ⊢
      exact Finset.mem_range.mp (Finset.mem_filter.mp hmem).1

    have hk₂ :
        k₂.1 < r := by
      have hmem :
          k₂.1 ∈ (Finset.range r).filter (Nat.Coprime r) := by
        simp [S] at k₂ ⊢
      exact Finset.mem_range.mp (Finset.mem_filter.mp hmem).1

    have hout :
        shorNearestOutput Q r k₁.1 =
          shorNearestOutput Q r k₂.1 := by
      have h' :=
        congrArg
          (fun z :
            ↥(goodOutcomeFinset Q r) =>
              z.1.1)
          h

      simpa [f] using h'

    exact
      shorNearestOutput_injective_below
        hr hrQ hk₁ hk₂ hout

  calc
    Nat.totient r
        =
      S.card := by
        simpa [S] using
          Nat.totient_eq_card_coprime r

    _ ≤
      (goodOutcomeFinset Q r).card :=
        Finset.card_le_card_of_injective hf


/-! ---------------------------------------------------------
    Step 6: sum the pointwise probabilities
--------------------------------------------------------- -/
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
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    [MeasureClass qs]
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
