import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.NaiveShor.Preliminaries
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.NaiveShor.PhaseEstimation
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

  have hparams :=
    shor_order_parameter_bounds hsetting

  have hr : 0 < r :=
    hparams.1

  have hrN : r < N :=
    hparams.2.1

  /-
  BasicSetting has 0 < a < N, hence N ≥ 2.
  -/
  have hN2 : 2 ≤ N := by
    rcases hsetting with
      ⟨ha0, haN, _horder,
       _hmlo, _hmhi, _hnlo, _hnhi⟩
    omega

  have hlog :
      1 ≤ Nat.log2 N := by
    rw [Nat.log2_def, if_pos hN2]
    omega

  have hanalytic :
      Real.exp (-2) /
          (Nat.log2 N : ℝ) ^ 4
        ≤
      1 /
          (((Nat.log2 N + 1 : ℕ) : ℝ)) :=
    exp_neg_two_div_pow4_le_inv_succ
      (Nat.log2 N) hlog

  have htotient :
      1 /
          (((Nat.log2 N + 1 : ℕ) : ℝ))
        ≤
      (Nat.totient r : ℝ) / (r : ℝ) :=
    totient_ratio_ge_inv_log2_succ
      hr hrN

  exact le_trans hanalytic htotient

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
