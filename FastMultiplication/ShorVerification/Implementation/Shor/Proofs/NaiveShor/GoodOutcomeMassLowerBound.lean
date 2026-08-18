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


/-- Exponent accumulated by processing a list of control qubits, the head at
bit weight `2^e`. Matches the recursion of `modExpIdealSteps`. -/
private def ctrlExp (e : ℕ) (ctrls : List ℕ) (b : qs.Basis) : ℕ :=
  match ctrls with
  | [] => 0
  | ctrl :: rest =>
      2 ^ e * (if RegEncoding.bit ctrl b then 1 else 0) + ctrlExp (e + 1) rest b

private lemma ctrlExp_eq_sum (e : ℕ) (ctrls : List ℕ) (b : qs.Basis) :
    ctrlExp e ctrls b
      = ∑ i ∈ Finset.range ctrls.length,
          2 ^ (e + i) * (if RegEncoding.bit (ctrls.getD i 0) b then 1 else 0) := by
  induction ctrls generalizing e with
  | nil => simp [ctrlExp]
  | cons c cs ih =>
      rw [ctrlExp, ih (e + 1), List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
      conv_rhs => rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      omega

/-- Bridge: processing all of `x`'s qubits accumulates exactly `toNat x b`. -/
private lemma ctrlExp_zero_qubits_eq_toNat (x : Reg) (b : qs.Basis) :
    ctrlExp 0 x.qubits b = RegEncoding.toNat x b := by
  rw [ctrlExp_eq_sum]
  have hlt : RegEncoding.toNat x b < 2 ^ x.qubits.length := by
    have := RegEncoding.toNat_lt_ASize x b
    simpa [ASize, regSize, Reg.width] using this
  rw [← sum_two_pow_toNat_testBit x.qubits.length (RegEncoding.toNat x b) hlt]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hget : x.qubits.getD i 0 = x.get ⟨i, by simpa [Reg.width] using hi⟩ := by
    rw [Reg.get]
    rw [List.getD_eq_getElem _ _ (by simpa [Reg.width] using hi)]
    rfl
  rw [hget]
  have hbit :
      RegEncoding.bit (x.get ⟨i, by simpa [Reg.width] using hi⟩) b
        = Nat.testBit (RegEncoding.toNat x b) i := by
    have := RegEncoding.bit_eq_testBit_toNat x b ⟨i, by simpa [regSize, Reg.width] using hi⟩
    simpa using this
  simp only [Nat.zero_add]
  rw [hbit]
  cases Nat.testBit (RegEncoding.toNat x b) i <;> simp

/-- Control bits of qubits disjoint from `y` are unaffected by writes to `y`,
so the accumulated exponent is unchanged. -/
private lemma ctrlExp_writeNat_out (y : Reg) (v : ℕ) :
    ∀ (e : ℕ) (ctrls : List ℕ) (b : qs.Basis),
      (∀ ctrl ∈ ctrls, ctrl ∉ y.qubits) →
      ctrlExp e ctrls (RegEncoding.writeNat y v b) = ctrlExp e ctrls b := by
  intro e ctrls
  induction ctrls generalizing e with
  | nil => intro b _; rfl
  | cons c cs ih =>
      intro b hmem
      rw [ctrlExp, ctrlExp,
          RegEncoding.bit_writeNat_out y v b c (hmem c (List.mem_cons_self)),
          ih (e + 1) b (fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc'))]

/-- Generalized recursion: the ideal modexp step-list multiplies `y` in place by
`a ^ (accumulated exponent of the processed control bits)` mod `N`. -/
private lemma eval_modExpIdealSteps_ket
    [GateSemanticsCore qs] [Spec] [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ) (y : Reg) (hN : 1 < N) (ha : Nat.Coprime a N) (hsize : N ≤ ASize y) :
    ∀ (e : ℕ) (ctrls : List ℕ) (b : qs.Basis),
      (∀ ctrl ∈ ctrls, ctrl ∉ y.qubits) →
      RegEncoding.toNat y b < N →
      qs.eval (modExpIdealSteps qs a N y e ctrls) (qs.ket b)
        = qs.ket (RegEncoding.writeNat y
            ((RegEncoding.toNat y b * a ^ ctrlExp e ctrls b) % N) b) := by
  intro e ctrls
  induction ctrls generalizing e with
  | nil =>
      intro b _ hb
      simp only [modExpIdealSteps, ctrlExp, pow_zero, mul_one, qs.eval_id]
      rw [Nat.mod_eq_of_lt hb, RegEncoding.writeNat_toNat]
  | cons ctrl ctrls ih =>
      intro b hmem hb
      have hpeel : modExpIdealSteps qs a N y e (ctrl :: ctrls)
          = Spec.idealCtrlModMul ((a ^ 2 ^ e) % N) N y ctrl ;;
            modExpIdealSteps qs a N y (e + 1) ctrls := by
        simp [modExpIdealSteps]
      rw [hpeel, qs.eval_seq]
      have hc : Nat.Coprime ((a ^ 2 ^ e) % N) N := by
        have hp : Nat.Coprime (a ^ 2 ^ e) N := ha.pow_left _
        have hg : Nat.gcd ((a ^ 2 ^ e) % N) N = Nat.gcd (a ^ 2 ^ e) N := by
          rw [Nat.gcd_comm (a ^ 2 ^ e) N, ← Nat.gcd_rec]
        unfold Nat.Coprime
        rw [hg]; exact hp
      have hctrl : ctrl ∉ y.qubits := hmem ctrl (List.mem_cons_self)
      rw [IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact
            ((a ^ 2 ^ e) % N) N y ctrl b hN hsize hc hctrl hb]
      set v0 := if RegEncoding.bit ctrl b then ((a ^ 2 ^ e) % N * RegEncoding.toNat y b) % N
                else RegEncoding.toNat y b with hv0def
      have hv0lt : v0 < N := by
        rw [hv0def]; split
        · exact Nat.mod_lt _ (by omega)
        · exact hb
      have hv0size : v0 < ASize y := lt_of_lt_of_le hv0lt hsize
      have hb'lt : RegEncoding.toNat y (RegEncoding.writeNat y v0 b) < N := by
        rw [RegEncoding.toNat_writeNat_of_lt y v0 b hv0size]; exact hv0lt
      have hmem' : ∀ c' ∈ ctrls, c' ∉ y.qubits :=
        fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc')
      rw [ih (e + 1) (RegEncoding.writeNat y v0 b) hmem' hb'lt]
      rw [RegEncoding.writeNat_overwrite,
          RegEncoding.toNat_writeNat_of_lt y v0 b hv0size,
          ctrlExp_writeNat_out y v0 (e + 1) ctrls b hmem']
      congr 2
      rw [ctrlExp, hv0def]
      by_cases hbit : RegEncoding.bit ctrl b
      · simp only [hbit, if_true, mul_one]
        rw [pow_add]
        have hmod :
            ((a ^ 2 ^ e) % N * RegEncoding.toNat y b) % N * a ^ ctrlExp (e + 1) ctrls b
              ≡ RegEncoding.toNat y b * (a ^ 2 ^ e * a ^ ctrlExp (e + 1) ctrls b) [MOD N] :=
          calc ((a ^ 2 ^ e) % N * RegEncoding.toNat y b) % N * a ^ ctrlExp (e + 1) ctrls b
              ≡ ((a ^ 2 ^ e) % N * RegEncoding.toNat y b) * a ^ ctrlExp (e + 1) ctrls b [MOD N] :=
                (Nat.mod_modEq _ _).mul_right _
            _ ≡ (a ^ 2 ^ e * RegEncoding.toNat y b) * a ^ ctrlExp (e + 1) ctrls b [MOD N] :=
                ((Nat.mod_modEq _ _).mul_right _).mul_right _
            _ = RegEncoding.toNat y b * (a ^ 2 ^ e * a ^ ctrlExp (e + 1) ctrls b) := by ring
        exact hmod
      · simp [hbit]

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
  have hmem : ∀ ctrl ∈ x.qubits, ctrl ∉ y.qubits := by
    rw [Disjoint, List.disjoint_left] at hxy
    exact fun ctrl hctrl => hxy hctrl
  have h := eval_modExpIdealSteps_ket (qs := qs) a N y hN ha hsize 0 x.qubits b hmem hy
  rw [show modExpIdeal' qs a N x y = modExpIdealSteps qs a N y 0 x.qubits from rfl]
  rw [h, ctrlExp_zero_qubits_eq_toNat]

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
























/-! ---------------------------------------------------------
    Step 5: count the good Fourier outputs
--------------------------------------------------------- -/







/-! ---------------------------------------------------------
    Step 6: sum the pointwise probabilities
--------------------------------------------------------- -/

/-! ---------------------------------------------------------
    Step 7: the loose number-theoretic bound used by this repo
--------------------------------------------------------- -/



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
