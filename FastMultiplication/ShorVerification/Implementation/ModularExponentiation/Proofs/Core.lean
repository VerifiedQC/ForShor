import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Defs
import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateSemanticsLemmas
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Shor

universe u v

namespace Shor

/-! =========================================================
    Modular Multiplication Bounds Core

This file contains the shared definitions for the modular-multiplication and
modular-exponentiation approximation proofs: ideal specifications, Algorithm 1
gates, layout and validity predicates, precision side conditions, reusable
configuration records, and the reference packets used by the Step 1/2/3/4/5
bound files.
========================================================= -/

/-! ---------------------------------------------------------
    Shared circuit syntax and workspace

This section defines the reusable high-level gates for Algorithm 1, together
with the concrete workspace predicate that provides the phase-product reserves
needed by Steps 1, 2, and 5.
--------------------------------------------------------- -/

section CircuitSyntaxAndWorkspace

end CircuitSyntaxAndWorkspace

/-! ---------------------------------------------------------
    Valid inputs and ideal controlled multiplication

The later approximation theorems work on a valid-input subspace. This section
defines the layout and clean-input predicates for that subspace, specifies the
ideal controlled modular multiplier on good basis states, and proves that the
ideal gate preserves the whole valid subspace.
--------------------------------------------------------- -/

section ValidInputsAndIdealSemantics

/-- Writing the active portion of an extended register preserves freshness of its reserve prefix. -/
lemma ExtReg.freshFor_write_active
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg)
    (n value : ℕ)
    (b : Basis)
    (hfresh : e.FreshFor n b) :
    e.FreshFor n
      (RegEncoding.writeNat e.active value b) := by
  have hnew_active :
      Disjoint (e.newBits n) e.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqNew hqActive

    have hdisj := e.active_reserve_disjoint
    rw [Disjoint, List.disjoint_left] at hdisj

    exact hdisj hqActive
      (List.mem_of_mem_take hqNew)

  unfold ExtReg.FreshFor FreshZero at hfresh ⊢

  calc
    RegEncoding.toNat (e.newBits n)
        (RegEncoding.writeNat e.active value b)
      =
        RegEncoding.toNat (e.newBits n) b := by
          exact
            RegEncoding.toNat_left_write_right
              (e.newBits n)
              e.active
              hnew_active
              b
              value
    _ = 0 := hfresh

/-- The ideal controlled multiplier maps good basis inputs to good basis outputs with the expected residue. -/
theorem IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    (c N : ℕ)
    (data work : ExtReg)
    (flag ctrl : ℕ)
    (b : qs.Basis)
    (hN : 1 < N)
    (hsize : N ≤ ASize data.active)
    (hcoprime : Nat.Coprime c N)
    (hlayout : ModMulCoreLayout data work flag ctrl)
    (hb : GoodModMulBasisInput qs N data work flag b) :
    ∃ b' : qs.Basis,
      qs.eval
          (Spec.idealCtrlModMul c N data.active ctrl)
          (qs.ket b)
        =
      qs.ket b'
        ∧
      GoodModMulBasisInput qs N data work flag b'
        ∧
      RegEncoding.bit ctrl b' =
        RegEncoding.bit ctrl b
        ∧
      RegEncoding.toNat data.active b'
        =
        if RegEncoding.bit ctrl b then
          (c * RegEncoding.toNat data.active b) % N
        else
          RegEncoding.toNat data.active b := by
  classical

  let out : ℕ :=
    if RegEncoding.bit ctrl b then
      (c * RegEncoding.toNat data.active b) % N
    else
      RegEncoding.toNat data.active b

  let b' : qs.Basis :=
    RegEncoding.writeNat data.active out b

  have hNpos : 0 < N :=
    Nat.lt_trans Nat.zero_lt_one hN

  have howned :
      ∀ q,
        q ∈ data.ownedQubits →
        q ∈ work.ownedQubits →
        False := by
    have h := hlayout.1
    rw [
      ExtReg.OwnedDisjoint,
      List.disjoint_left
    ] at h
    exact h

  have hwork_data :
      Disjoint work.active data.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqWork hqData

    apply howned

    · show q ∈ data.active.qubits ++ data.reserve.qubits
      exact List.mem_append_left _ hqData

    · show q ∈ work.active.qubits ++ work.reserve.qubits
      exact List.mem_append_left _ hqWork

  have hworkNew_data :
      Disjoint (work.newBits 1) data.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqNew hqData

    have hqReserve :
        q ∈ work.reserve.qubits :=
      List.mem_of_mem_take hqNew

    apply howned

    · show q ∈ data.active.qubits ++ data.reserve.qubits
      exact List.mem_append_left _ hqData

    · show q ∈ work.active.qubits ++ work.reserve.qubits
      exact List.mem_append_right _ hqReserve

  have hflag_data :
      Disjoint (qubitReg flag) data.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqFlag hqData

    have hq : q = flag := by
      simpa [qubitReg, Reg.singleton] using hqFlag
    subst q

    exact hlayout.2.1
      (show flag ∈ data.ownedQubits by
        exact List.mem_append_left _ hqData)

  have hctrl_data :
      ctrl ∉ data.active.qubits := by
    intro hctrlActive

    exact hlayout.2.2.2.1
      (show ctrl ∈ data.ownedQubits by
        exact List.mem_append_left _ hctrlActive)

  have hout_lt_N : out < N := by
    by_cases hctrl : RegEncoding.bit ctrl b
    · simpa [out, hctrl] using
        Nat.mod_lt
          (c * RegEncoding.toNat data.active b)
          hNpos
    · simpa [out, hctrl] using hb.1

  have hout_lt_cap :
      out < ASize data.active :=
    lt_of_lt_of_le hout_lt_N hsize

  have hdata_out :
      RegEncoding.toNat data.active b' = out := by
    dsimp [b']
    exact
      RegEncoding.toNat_writeNat_of_lt
        data.active out b hout_lt_cap

  have hdataFresh_out :
      data.FreshFor 2 b' := by
    dsimp [b']
    exact
      ExtReg.freshFor_write_active
        data 2 out b hb.2.1

  have hwork_out :
      RegEncoding.toNat work.active b' = 0 := by
    calc
      RegEncoding.toNat work.active b'
        =
          RegEncoding.toNat work.active b := by
            dsimp [b']
            exact
              RegEncoding.toNat_left_write_right
                work.active
                data.active
                hwork_data
                b
                out
      _ = 0 := hb.2.2.1

  have hworkFresh_in :
      RegEncoding.toNat (work.newBits 1) b = 0 := by
    simpa [ExtReg.FreshFor, FreshZero] using
      hb.2.2.2.1

  have hworkFresh_out :
      work.FreshFor 1 b' := by
    have hzero :
        RegEncoding.toNat (work.newBits 1) b' = 0 := by
      calc
        RegEncoding.toNat (work.newBits 1) b'
          =
            RegEncoding.toNat (work.newBits 1) b := by
              dsimp [b']
              exact
                RegEncoding.toNat_left_write_right
                  (work.newBits 1)
                  data.active
                  hworkNew_data
                  b
                  out
        _ = 0 := hworkFresh_in

    simpa [ExtReg.FreshFor, FreshZero] using hzero

  have hflag_out :
      RegEncoding.toNat (qubitReg flag) b' = 0 := by
    calc
      RegEncoding.toNat (qubitReg flag) b'
        =
          RegEncoding.toNat (qubitReg flag) b := by
            dsimp [b']
            exact
              RegEncoding.toNat_left_write_right
                (qubitReg flag)
                data.active
                hflag_data
                b
                out
      _ = 0 := hb.2.2.2.2

  have hgood_out :
      GoodModMulBasisInput
        qs N data work flag b' := by
    refine
      ⟨?_,
       hdataFresh_out,
       hwork_out,
       hworkFresh_out,
       hflag_out⟩

    calc
      RegEncoding.toNat data.active b' = out :=
        hdata_out
      _ < N := hout_lt_N

  have hctrl_out :
      RegEncoding.bit ctrl b' =
        RegEncoding.bit ctrl b := by
    dsimp [b']
    exact
      RegEncoding.bit_writeNat_out
        (r := data.active)
        (v := out)
        (b := b)
        (q := ctrl)
        hctrl_data

  have heval :
      qs.eval
          (Spec.idealCtrlModMul
            c N data.active ctrl)
          (qs.ket b)
        =
      qs.ket b' := by
    simpa [b', out] using
      (IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket_exact
          (qs := qs)
          c N data work flag ctrl b
          hN
          hsize
          hcoprime
          hlayout
          hb)

  refine
    ⟨b',
     heval,
     hgood_out,
     hctrl_out,
     ?_⟩

  simpa [out] using hdata_out



/-- The ideal controlled multiplier preserves the span of all good modular-multiplication states. -/
theorem idealCtrlModMul_preserves_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    (c N : ℕ)
    (data work : ExtReg)
    (flag ctrl : ℕ)
    (hN : 1 < N)
    (hsize : N ≤ ASize data.active)
    (hcoprime : Nat.Coprime c N)
    (hlayout : ModMulCoreLayout data work flag ctrl)
    (ψ : qs.State)
    (hvalid :
      ψ ∈ ValidModMulState
        qs N data work flag) :
    qs.eval
        (Spec.idealCtrlModMul
          c N data.active ctrl)
        ψ
      ∈
    ValidModMulState
      qs N data work flag := by
  classical

  let validSet : Set qs.State :=
    { ξ : qs.State |
      ∃ b : qs.Basis,
        GoodModMulBasisInput
          qs N data work flag b
          ∧
        ξ = qs.ket b }

  change
    ψ ∈ Submodule.span ℂ validSet
      at hvalid

  change
    qs.eval
        (Spec.idealCtrlModMul
          c N data.active ctrl)
        ψ
      ∈
    Submodule.span ℂ validSet

  refine
    Submodule.span_induction
      (s := validSet)
      (p := fun ξ _ =>
        qs.eval
            (Spec.idealCtrlModMul
              c N data.active ctrl)
            ξ
          ∈
        Submodule.span ℂ validSet)
      ?basis
      ?zero
      ?add
      ?smul
      hvalid

  case basis =>
    intro ξ hξ

    change
      ∃ b : qs.Basis,
        GoodModMulBasisInput
          qs N data work flag b
          ∧
        ξ = qs.ket b
      at hξ

    rcases hξ with ⟨b, hb, rfl⟩

    obtain
      ⟨b', heval, hgood, _hctrl, _hdata⟩ :=
        IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket
            (qs := qs)
            c N data work flag ctrl b
            hN
            hsize
            hcoprime
            hlayout
            hb

    rw [heval]

    exact
      Submodule.subset_span
        (show qs.ket b' ∈ validSet from
          ⟨b', hgood, rfl⟩)

  case zero =>
    change
      qs.eval
          (Spec.idealCtrlModMul
            c N data.active ctrl)
          0
        ∈
      Submodule.span ℂ validSet

    rw [qs.eval_zero]
    exact
      (Submodule.span ℂ validSet).zero_mem

  case add =>
    intro ξ ζ _hξ _hζ hξEval hζEval

    change
      qs.eval
          (Spec.idealCtrlModMul
            c N data.active ctrl)
          (ξ + ζ)
        ∈
      Submodule.span ℂ validSet

    rw [qs.eval_add]

    exact
      (Submodule.span ℂ validSet).add_mem
        hξEval hζEval

  case smul =>
    intro a ξ _hξ hξEval

    change
      qs.eval
          (Spec.idealCtrlModMul
            c N data.active ctrl)
          (a • ξ)
        ∈
      Submodule.span ℂ validSet

    rw [qs.eval_smul]

    exact
      (Submodule.span ℂ validSet).smul_mem
        a hξEval

end ValidInputsAndIdealSemantics

/-! ---------------------------------------------------------
    Algorithm 1 precision and arithmetic constants

This section packages the concrete precision schedule for Algorithm 1 and the
Step-5 inverse constant used by the cleanup phase.
--------------------------------------------------------- -/

section Algorithm1PrecisionAndConstants

/-- The error parameter is positive. -/
lemma eta_pos
    {η : ℝ}
    {data work : Reg}
    (h : Algorithm1Precision η data work) :
    0 < η :=
  h.1

/-- The work register has exactly the width prescribed by Algorithm 1. -/
lemma work_width
    {η : ℝ}
    {data work : Reg}
    (h : Algorithm1Precision η data work) :
    regSize work =
      regSize data + algorithm1ExtraBits η :=
  h.2.2

/-- Algorithm 1's work register is at least as wide as the data register. -/
lemma data_width_le_work_width
    {η : ℝ}
    {data work : Reg}
    (h : Algorithm1Precision η data work) :
    regSize data ≤ regSize work := by
  rw [work_width h]
  simp

/--
The difference between the work width and the data width is exactly the
number of extra bits prescribed by Algorithm 1.
-/
lemma work_width_sub_data_width
    {η : ℝ}
    {data work : Reg}
    (h : Algorithm1Precision η data work) :
    regSize work - regSize data =
      algorithm1ExtraBits η := by
  rw [work_width h]
  omega

/--
The exact workspace choice made by Algorithm 1 implies the quantitative
precision inequality previously stored directly in `Algorithm1Precision`:

  2^(m - n) ≥ (2 + 1/(2η))^2.
-/
lemma pow_bound
    {η : ℝ}
    {data work : Reg}
    (h : Algorithm1Precision η data work) :
    (2 : ℝ) ^ (regSize work - regSize data)
      ≥
    (2 + 1 / (2 * η)) ^ 2 := by
  let a : ℝ := 2 + 1 / (2 * η)

  have ha : 0 < a := by
    dsimp [a]
    have hη : 0 < η := eta_pos h
    positivity

  have hdiff :
      regSize work - regSize data =
        algorithm1ExtraBits η :=
    work_width_sub_data_width h

  rw [hdiff]

  have hceil :
      2 * Real.logb 2 a
        ≤
      (algorithm1ExtraBits η : ℝ) := by
    dsimp [algorithm1ExtraBits]
    exact Nat.le_ceil _


  have hlog :
      Real.logb 2 (a ^ 2)
        ≤
      (algorithm1ExtraBits η : ℝ) := by
    rw [Real.logb_pow]
    simpa using hceil

  have hrpow :
      a ^ 2
        ≤
      (2 : ℝ) ^ (algorithm1ExtraBits η : ℝ) := by
    exact
      (Real.logb_le_iff_le_rpow
        (by norm_num : (1 : ℝ) < 2)
        (by positivity : 0 < a ^ 2)).1
        hlog

  have hpow :
      a ^ 2
        ≤
      (2 : ℝ) ^ algorithm1ExtraBits η := by
    simpa [Real.rpow_natCast] using hrpow

  simpa [a] using hpow
/--
The Step-5 constant represents `1 - c⁻¹ mod N`.

The concrete `step5Constant` above chooses such an inverse with `Nat.find`
when coprimality guarantees one exists.
-/
def Step5ConstantOK (c N k5val : ℕ) : Prop :=
  ∃ cinv : ℕ,
    cinv < N ∧
    (c * cinv) % N = 1 % N ∧
    k5val % N = (1 + N - cinv) % N

/-- The concrete `step5Constant` satisfies the modular inverse cleanup specification. -/
theorem step5Constant_ok
    (c N : ℕ)
    (hN : 1 < N)
    (hcoprime : Nat.Coprime c N) :
    Step5ConstantOK c N (step5Constant c N) := by
  classical
  have hExists : ∃ cinv : ℕ, cinv < N ∧ (c * cinv) % N = 1 :=
    Nat.exists_mul_mod_eq_one_of_coprime hcoprime hN
  let cinv : ℕ := Nat.find hExists
  have hcinv : cinv < N ∧ (c * cinv) % N = 1 := by
    simpa [cinv] using Nat.find_spec hExists
  refine ⟨cinv, hcinv.1, ?_, ?_⟩
  · have h1lt : 1 < N := hN
    simpa [Nat.mod_eq_of_lt h1lt] using hcinv.2
  · unfold step5Constant
    rw [dif_pos hExists]
    simp [cinv]

end Algorithm1PrecisionAndConstants

/-! ---------------------------------------------------------
    Modular-exponentiation layout and gates

The current modular-exponentiation API recurses over a list of control qubits.
These predicates and gates express the layout and coprimality side conditions
for that list-based recursion.
--------------------------------------------------------- -/

section ModExpLayoutAndGates

end ModExpLayoutAndGates

/-! ---------------------------------------------------------
    Shared configurations

The bound files pass around compact records rather than repeatedly threading the
modulus, registers, precision proof, workspace proof, layout proof, and
coprimality hypotheses.
--------------------------------------------------------- -/

section SharedConfigurations

namespace ModExpConfig

end ModExpConfig



/-! ---------------------------------------------------------
    One controlled modular multiplication
--------------------------------------------------------- -/

namespace ModMulConfig

/-! ---------------------------------------------------------
    Algorithm 1 staged gates

These names expose the five-step core as stage-level gates used throughout the
Step 1/2/3/4/5 correctness and error-bound files.
--------------------------------------------------------- -/

/-- Stage name for the exact Step 3/4 comparator block. -/
noncomputable def U34
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  step3 cfg.env.N (cfg.env.data.grow 1).active cfg.flag ;;
  step4 cfg.env.N (cfg.env.data.grow 1).active cfg.env.work.active cfg.flag

/-- The staged form of the full five-step modular-multiplication core. -/
noncomputable def stagedGate
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  U1 (Basis := Basis) cfg ;;
  U2 (Basis := Basis) cfg ;;
  U34 (Basis := Basis) cfg ;;
  U5 (Basis := Basis) cfg

end ModMulConfig

end SharedConfigurations

/-! ---------------------------------------------------------
    Derived primitive semantics and ideal configuration facts

Steps 3 and 4 use opaque primitive gates whose basic semantics live in the
framework. This section derives the implementation-specific Step 3/4 facts and
provides the configuration-specific ideal multiplier lemma.
--------------------------------------------------------- -/

section PrimitiveAndIdealConfigFacts

section ModMulPrimitiveDerivedSemantics

variable
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ModMulPrimitiveGateSemantics qs]

/-! ---------------------------------------------------------
    Small register/flag helpers
--------------------------------------------------------- -/

private lemma disjoint_qubitReg_of_outside
    {q : ℕ} {r : Reg}
    (h : q ∉ r.qubits) :
    Disjoint (qubitReg q) r := by
  rw [Disjoint, List.disjoint_left]
  intro p hp hr
  have hpq : p = q := by
    simpa [qubitReg, Reg.singleton] using hp
  subst p
  exact h hr

omit [GateSemanticsCore qs] [ModMulPrimitiveGateSemantics qs] in
lemma bit_qubitReg_eq_testBit_zero
    (q : ℕ) (b : qs.Basis) :
    RegEncoding.bit q b =
      Nat.testBit (RegEncoding.toNat (qubitReg q) b) 0 := by
  simpa [qubitReg, Reg.singleton, Reg.get, regSize, Reg.width] using
    (RegEncoding.bit_eq_testBit_toNat
      (r := qubitReg q)
      (b := b)
      (i := (⟨0, by simp⟩ : Fin (regSize (qubitReg q)))))

omit [GateSemanticsCore qs] [ModMulPrimitiveGateSemantics qs] in
lemma bit_false_of_qubitReg_toNat_zero
    (q : ℕ) (b : qs.Basis)
    (h : RegEncoding.toNat (qubitReg q) b = 0) :
    RegEncoding.bit q b = false := by
  rw [bit_qubitReg_eq_testBit_zero (qs := qs) q b, h]
  simp
omit [GateSemanticsCore qs] [ModMulPrimitiveGateSemantics qs] in
lemma bit_true_of_qubitReg_toNat_one
    (q : ℕ) (b : qs.Basis)
    (h : RegEncoding.toNat (qubitReg q) b = 1) :
    RegEncoding.bit q b = true := by
  rw [bit_qubitReg_eq_testBit_zero (qs := qs) q b, h]
  simp
omit [GateSemanticsCore qs] [ModMulPrimitiveGateSemantics qs] in
lemma bit_write_qubitReg_zero
    (q : ℕ) (b : qs.Basis) :
    RegEncoding.bit q
        (RegEncoding.writeNat (qubitReg q) 0 b) = false := by
  apply bit_false_of_qubitReg_toNat_zero (qs := qs)
  exact RegEncoding.toNat_writeNat_of_lt
    (qubitReg q) 0 b (by simp [ASize])

omit [GateSemanticsCore qs] [ModMulPrimitiveGateSemantics qs] in
lemma bit_write_qubitReg_one
    (q : ℕ) (b : qs.Basis) :
    RegEncoding.bit q
        (RegEncoding.writeNat (qubitReg q) 1 b) = true := by
  apply bit_true_of_qubitReg_toNat_one (qs := qs)
  exact RegEncoding.toNat_writeNat_of_lt
    (qubitReg q) 1 b (by simp [ASize])

theorem eval_step3_clean_ket_of_primitive
    (N : ℕ)
    (x_ext : Reg)
    (flag : ℕ)
    (b : qs.Basis)
    (hout : QubitOutside flag x_ext)
    (hflag :
      RegEncoding.toNat (qubitReg flag) b = 0):
    qs.eval (step3 N x_ext flag) (qs.ket b)
      =
    qs.ket
      (RegEncoding.writeNat
        (qubitReg flag)
        (if N ≤ RegEncoding.toNat x_ext b then 1 else 0)
        (RegEncoding.writeNat x_ext
          (if N ≤ RegEncoding.toNat x_ext b then
            RegEncoding.toNat x_ext b - N
          else
            RegEncoding.toNat x_ext b)
          b)) := by
  have hout' : flag ∉ x_ext.qubits := by
    simpa [QubitOutside] using hout

  have hflag_x :
      Disjoint (qubitReg flag) x_ext :=
    disjoint_qubitReg_of_outside hout'

  have hx_flag :
      Disjoint x_ext (qubitReg flag) :=
    Disjoint.symm hflag_x

  have hbit0 :
      RegEncoding.bit flag b = false :=
    bit_false_of_qubitReg_toNat_zero
      (qs := qs) flag b hflag

  have hxcap :
      RegEncoding.toNat x_ext b < ASize x_ext :=
    RegEncoding.toNat_lt_ASize x_ext b

  rw [step3, qs.eval_seq]

  rw [
    ModMulPrimitiveGateSemantics.eval_cmp_ge_const_ket
      (qs := qs) N x_ext flag b hout'
  ]

  by_cases hge : N ≤ RegEncoding.toNat x_ext b

  · -- The comparison sets flag = 1, then CSUB subtracts N.
    simp only [hbit0, Bool.false_eq_true, if_false, hge, if_pos]

    let b₁ :=
      RegEncoding.writeNat (qubitReg flag) 1 b

    have hx₁ :
        RegEncoding.toNat x_ext b₁ =
          RegEncoding.toNat x_ext b := by
      exact
        RegEncoding.toNat_left_write_right
          x_ext
          (qubitReg flag)
          hx_flag
          b
          1

    have hbit₁ :
        RegEncoding.bit flag b₁ = true := by
      exact bit_write_qubitReg_one
        (qs := qs) flag b

    have hNcap :
        N < ASize x_ext := by
      exact lt_of_le_of_lt hge hxcap

    have hsubcap :
        RegEncoding.toNat x_ext b - N < ASize x_ext := by
      omega

    have hwrapped :
        (RegEncoding.toNat x_ext b
              + ASize x_ext
              - (N % ASize x_ext))
            % ASize x_ext
          =
        RegEncoding.toNat x_ext b - N := by
      rw [Nat.mod_eq_of_lt hNcap]

      have hrewrite :
          RegEncoding.toNat x_ext b + ASize x_ext - N
            =
          ASize x_ext
            + (RegEncoding.toNat x_ext b - N) := by
        omega

      rw [hrewrite]
      simp [Nat.mod_eq_of_lt hsubcap]

    rw [
      ModMulPrimitiveGateSemantics.eval_csub_const_ket
        (qs := qs) N x_ext flag b₁ hout'
    ]

    simp only [hbit₁, if_true, hx₁, hwrapped]

    apply congrArg qs.ket

    exact
      (writeNat_comm_of_disjoint
        (qubitReg flag)
        x_ext
        hflag_x
        1
        (RegEncoding.toNat x_ext b - N)
        b).symm

  · -- The comparison leaves flag = 0, so CSUB is inactive.
    simp only [hbit0, Bool.false_eq_true, if_false, hge]

    let b₀ :=
      RegEncoding.writeNat (qubitReg flag) 0 b

    have hx₀ :
        RegEncoding.toNat x_ext b₀ =
          RegEncoding.toNat x_ext b := by
      exact
        RegEncoding.toNat_left_write_right
          x_ext
          (qubitReg flag)
          hx_flag
          b
          0

    have hbit₀ :
        RegEncoding.bit flag b₀ = false := by
      exact bit_write_qubitReg_zero
        (qs := qs) flag b

    rw [
      ModMulPrimitiveGateSemantics.eval_csub_const_ket
        (qs := qs) N x_ext flag b₀ hout'
    ]

    simp only [hbit₀, Bool.false_eq_true, if_false]

    have hwrite₀ :
        RegEncoding.writeNat x_ext
            (RegEncoding.toNat x_ext b) b₀
          =
        b₀ := by
      rw [← hx₀]
      exact RegEncoding.writeNat_toNat x_ext b₀

    rw [hx₀,hwrite₀]
    rw [RegEncoding.writeNat_toNat]

theorem eval_step4_cancels_ket_of_primitive
    (N : ℕ)
    (x_ext w_reg : Reg)
    (flag : ℕ)
    (b : qs.Basis)
    (hx : QubitOutside flag x_ext)
    (hw : QubitOutside flag w_reg)
    (hflag :
      RegEncoding.toNat (qubitReg flag) b
        =
      if RegEncoding.toNat x_ext b * ASize w_reg
            < N * RegEncoding.toNat w_reg b then
        1
      else
        0) :
    qs.eval (step4 N x_ext w_reg flag) (qs.ket b)
      =
    qs.ket
      (RegEncoding.writeNat (qubitReg flag) 0 b) := by

  have hx' : flag ∉ x_ext.qubits := by
    simpa [QubitOutside] using hx

  have hw' : flag ∉ w_reg.qubits := by
    simpa [QubitOutside] using hw

  rw [step4]

  rw [
    ModMulPrimitiveGateSemantics.eval_cmp_lt_nw_ket
      (qs := qs) N x_ext w_reg flag b hx' hw'
  ]

  by_cases hcmp :
      RegEncoding.toNat x_ext b * ASize w_reg
        < N * RegEncoding.toNat w_reg b

  · have hflag1 :
        RegEncoding.toNat (qubitReg flag) b = 1 := by
      simpa [hcmp] using hflag

    have hbit :
        RegEncoding.bit flag b = true :=
      bit_true_of_qubitReg_toNat_one
        (qs := qs) flag b hflag1

    simp [hcmp, hbit]

  · have hflag0 :
        RegEncoding.toNat (qubitReg flag) b = 0 := by
      simpa [hcmp] using hflag

    have hbit :
        RegEncoding.bit flag b = false :=
      bit_false_of_qubitReg_toNat_zero
        (qs := qs) flag b hflag0

    simp [hcmp, hbit]

theorem eval_step3_local_ket_of_primitive
    (N : ℕ)
    (dataCarry : Reg)
    (flag : ℕ)
    (b : qs.Basis)
    (hout : QubitOutside flag dataCarry) :
    ∃ b' : qs.Basis,
      qs.eval (step3 N dataCarry flag) (qs.ket b)
        =
      qs.ket b'
      ∧
      ∀ q,
        q ∉ dataCarry.qubits →
        q ≠ flag →
        RegEncoding.bit q b' =
          RegEncoding.bit q b := by

  classical

  have hout' : flag ∉ dataCarry.qubits := by
    simpa [QubitOutside] using hout

  let cmpValue : ℕ :=
    if RegEncoding.bit flag b then
      if N ≤ RegEncoding.toNat dataCarry b then 0 else 1
    else
      if N ≤ RegEncoding.toNat dataCarry b then 1 else 0

  let b₁ : qs.Basis :=
    RegEncoding.writeNat
      (qubitReg flag) cmpValue b

  let subValue : ℕ :=
    if RegEncoding.bit flag b₁ then
      (RegEncoding.toNat dataCarry b₁
          + ASize dataCarry
          - (N % ASize dataCarry))
        % ASize dataCarry
    else
      RegEncoding.toNat dataCarry b₁

  let b' : qs.Basis :=
    RegEncoding.writeNat dataCarry subValue b₁

  refine ⟨b', ?_, ?_⟩

  · rw [step3, qs.eval_seq]

    rw [
      ModMulPrimitiveGateSemantics.eval_cmp_ge_const_ket
        (qs := qs) N dataCarry flag b hout'
    ]

    change
      qs.eval
          (Gate.Prim
            "CSUB_CONST"
            ([N, flag] ++ dataCarry.qubits))
          (qs.ket b₁)
        =
      qs.ket b'

    rw [
      ModMulPrimitiveGateSemantics.eval_csub_const_ket
        (qs := qs) N dataCarry flag b₁ hout'
    ]

  · intro q hqData hqFlag

    have hqFlagReg :
        q ∉ (qubitReg flag).qubits := by
      simpa [qubitReg, Reg.singleton] using hqFlag

    dsimp [b', b₁]

    rw [
      RegEncoding.bit_writeNat_out
        dataCarry subValue b₁ q hqData
    ]

    exact
      RegEncoding.bit_writeNat_out
        (qubitReg flag) cmpValue b q hqFlagReg

theorem eval_step4_local_ket_of_primitive
    (N : ℕ)
    (dataCarry work : Reg)
    (flag : ℕ)
    (b : qs.Basis)
    (hdata : QubitOutside flag dataCarry)
    (hwork : QubitOutside flag work) :
    ∃ b' : qs.Basis,
      qs.eval (step4 N dataCarry work flag) (qs.ket b)
        =
      qs.ket b'
      ∧
      ∀ q,
        q ∉ dataCarry.qubits →
        q ∉ work.qubits →
        q ≠ flag →
        RegEncoding.bit q b' =
          RegEncoding.bit q b := by

  have hdata' : flag ∉ dataCarry.qubits := by
    simpa [QubitOutside] using hdata

  have hwork' : flag ∉ work.qubits := by
    simpa [QubitOutside] using hwork

  let flagValue : ℕ :=
    if RegEncoding.bit flag b then
      if RegEncoding.toNat dataCarry b * ASize work
            < N * RegEncoding.toNat work b then
        0
      else
        1
    else
      if RegEncoding.toNat dataCarry b * ASize work
            < N * RegEncoding.toNat work b then
        1
      else
        0

  let b' : qs.Basis :=
    RegEncoding.writeNat
      (qubitReg flag) flagValue b

  refine ⟨b', ?_, ?_⟩

  · rw [step4]

    simpa [b', flagValue] using
      (ModMulPrimitiveGateSemantics.eval_cmp_lt_nw_ket
        (qs := qs)
        N dataCarry work flag b
        hdata' hwork')

  · intro q _ _ hqFlag

    have hqFlagReg :
        q ∉ (qubitReg flag).qubits := by
      simpa [qubitReg, Reg.singleton] using hqFlag

    dsimp [b']

    exact
      RegEncoding.bit_writeNat_out
        (qubitReg flag) flagValue b q hqFlagReg

end ModMulPrimitiveDerivedSemantics

/-- Configuration wrapper around the exact ideal controlled-multiplier basis semantics. -/
theorem IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_cfg
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η) (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval (ModMulConfig.idealGate cfg) (qs.ket b)
      =
    qs.ket
      (RegEncoding.writeNat cfg.env.data.active
        (if RegEncoding.bit cfg.ctrl b then
          (cfg.c * RegEncoding.toNat cfg.env.data.active b) % cfg.env.N
        else
          RegEncoding.toNat cfg.env.data.active b)
        b) := by
  simpa [ModMulConfig.idealGate] using
    (IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket_exact
      (qs := qs)
      cfg.c
      cfg.env.N
      cfg.env.data
      cfg.env.work
      cfg.flag
      cfg.ctrl
      b
      cfg.env.modulus_gt_one
      cfg.env.data_capacity
      cfg.coprime
      cfg.layout
      hb)

end PrimitiveAndIdealConfigFacts

/-! ---------------------------------------------------------
    Algorithm 1 reference arithmetic

These scalar definitions describe the intended residues, fractional work labels,
good QPE labels, and exact Step-2 integer shift used by the error proof.
--------------------------------------------------------- -/

section Algorithm1ReferenceArithmetic

/-- Target residue loaded by the Step-1 fractional phase, before final multiplication cleanup. -/
noncomputable def alg1TargetResidue
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℕ :=
  if RegEncoding.bit cfg.ctrl b then
    (((cfg.c + cfg.env.N - 1) % cfg.env.N)
      * RegEncoding.toNat cfg.env.data.active b) % cfg.env.N
  else
    0

/-- Target residue as a normalized real fraction of the modulus. -/
noncomputable def alg1TargetFraction
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℝ :=
  (alg1TargetResidue cfg b : ℝ) / (cfg.env.N : ℝ)

/-- Work-register label as a normalized real fraction. -/
noncomputable def alg1WorkFraction
    {η : ℝ}
    (cfg : ModMulConfig η)
    (t : Fin (ASize cfg.env.work.active)) : ℝ :=
  (t.1 : ℝ) / (ASize cfg.env.work.active : ℝ)

/-- QPE labels whose work fractions are close enough to the target fraction. -/
noncomputable def alg1GoodLabels
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) :
    Finset (Fin (ASize cfg.env.work.active)) :=
  Finset.univ.filter fun t =>
    |alg1TargetFraction cfg b - alg1WorkFraction cfg t|
      < η / (ASize cfg.env.data.active : ℝ)

/-- Exact data-carry value that Step 2 should produce for a retained good label. -/
noncomputable def alg1Step2Value
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℕ :=
  RegEncoding.toNat cfg.env.data.active b + alg1TargetResidue cfg b


end Algorithm1ReferenceArithmetic

/-! ---------------------------------------------------------
    Step-2 Fourier coefficient scaffolding

The Step-2 proof compares the actual Fourier coefficient produced by the
PhaseProduct with the ideal coefficient for the exact integer shift. These
definitions name the relevant phases, index types, labels, and multipliers.
--------------------------------------------------------- -/

section Step2FourierScaffolding

/--
The Step-2 phase angle, written independently of the `let`s in `step2`.
-/
noncomputable def alg1Step2Phase
    {η : ℝ}
    (cfg : ModMulConfig η) : ℝ :=
  (2 * Real.pi * (cfg.env.N : ℝ)) /
    ((2 : ℝ) ^
      (regSize cfg.env.work.active + regSize (cfg.env.data.grow 1).active))

/--
The normalizing scalar in the QFT on `data.grow 1`.
-/
noncomputable def alg1Step2QFTScale
    {η : ℝ}
    (cfg : ModMulConfig η) : ℂ :=
  (1 / Real.sqrt ((ASize (cfg.env.data.grow 1).active : ℕ) : ℝ) : ℂ)

/--
The Fourier coefficient after the first QFT and the actual Step-2
`PhaseProd`, before the final inverse QFT.
-/
noncomputable def alg1Step2ActualFourierCoeff
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work.active))
    (y : Fin (ASize (cfg.env.data.grow 1).active)) : ℂ :=
  alg1Step2QFTScale cfg *
    qftPhase
      (ASize (cfg.env.data.grow 1).active)
      (RegEncoding.toNat cfg.env.data.active b)
      y.1 *
    Complex.exp
      (alg1Step2Phase cfg * Complex.I *
        ((t.1 : ℂ) * (y.1 : ℂ)))

/--
The Fourier coefficient of the exact desired integer shift
`alg1Step2Value cfg b`.
-/
noncomputable def alg1Step2IdealFourierCoeff
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (y : Fin (ASize (cfg.env.data.grow 1).active)) : ℂ :=
  alg1Step2QFTScale cfg *
    qftPhase
      (ASize (cfg.env.data.grow 1).active)
      (alg1Step2Value cfg b)
      y.1

/--
The real difference between the fractional Step-2 shift produced by work
label `t` and the desired integer residue.

The actual shift is `N * t / ASize work`; the ideal one is the target
residue.
-/
noncomputable def alg1Step2ShiftDiscrepancy
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work.active)) : ℝ :=
  (cfg.env.N : ℝ) * alg1WorkFraction cfg t
    - (alg1TargetResidue cfg b : ℝ)


/-- Source index for Step-2 packets: an input basis branch plus a work label. -/
abbrev Alg1Step2SourceIndex
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η) :=
  Σ _b : qs.Basis, Fin (ASize cfg.env.work.active)

/-- Fourier-expanded Step-2 index: a source index plus a data-carry Fourier label. -/
abbrev Alg1Step2FourierIndex
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η) :=
  Σ _i : Alg1Step2SourceIndex qs cfg,
    Fin (ASize (cfg.env.data.grow 1).active)

/-- Expand every retained source index over all data-carry Fourier labels. -/
noncomputable def alg1Step2FourierIndices
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Alg1Step2SourceIndex qs cfg)) :
    Finset (Alg1Step2FourierIndex qs cfg) := by
  classical
  exact S.sigma fun _ => Finset.univ

/-- Basis label associated with one Step-2 Fourier-expanded index. -/
noncomputable def alg1Step2FourierLabel
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (p : Alg1Step2FourierIndex qs cfg) : qs.Basis :=
  RegEncoding.writeNat
    (cfg.env.data.grow 1).active
    p.2.1
    (RegEncoding.writeNat cfg.env.work.active p.1.2.1 p.1.1)

/-- Base Fourier coefficient before applying the actual-vs-ideal multiplier discrepancy. -/
noncomputable def alg1Step2FourierBaseCoeff
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (α : Alg1Step2SourceIndex qs cfg → ℂ)
    (p : Alg1Step2FourierIndex qs cfg) : ℂ :=
  α p.1 *
    alg1Step2QFTScale cfg *
    qftPhase
      (ASize (cfg.env.data.grow 1).active)
      (RegEncoding.toNat cfg.env.data.active p.1.1)
      p.2.1

/-- Difference between the actual Step-2 phase multiplier and the ideal Fourier multiplier. -/
noncomputable def alg1Step2FourierMultiplier
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (r : ℕ)
    (p : Alg1Step2FourierIndex qs cfg) : ℂ :=
  Complex.exp
    (alg1Step2Phase cfg * Complex.I *
      ((p.1.2.1 : ℂ) * (p.2.1 : ℂ)))
    -
  qftPhase
    (ASize (cfg.env.data.grow 1).active)
    r
    p.2.1




/-! ---------------------------------------------------------
    Coherent Step-2 error vector
--------------------------------------------------------- -/

/--
The one-label Step-2 error vector.
-/
noncomputable def alg1Step2Error
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work.active)) : qs.State :=
  qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
      (qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b))
    -
  qs.ket
    (RegEncoding.writeNat
      (cfg.env.data.grow 1).active
      (alg1Step2Value cfg b)
      (RegEncoding.writeNat cfg.env.work.active t.1 b))

end Step2FourierScaffolding

/-! ---------------------------------------------------------
    Step-3/4 labels and trace packets

This section records the exact data values after the comparator/subtractor
stages and packages the finite trace expansions used by the Appendix-E-style
Algorithm 1 error decomposition.
--------------------------------------------------------- -/

section Step34LabelsAndTracePackets

/-- Final data value expected after exact Steps 3 and 4. -/
def alg1OutputValue
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℕ :=
  if RegEncoding.bit cfg.ctrl b then
    (cfg.c * RegEncoding.toNat cfg.env.data.active b) % cfg.env.N
  else
    RegEncoding.toNat cfg.env.data.active b

/-- Comparator condition used by Step 4 to decide whether the flag should clear. -/
def alg1Step4CrossCondition
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work.active)) : Prop :=
  alg1OutputValue cfg b * ASize cfg.env.work.active < cfg.env.N * t.1

/-- Whether the pre-reduction Step-2 value overflows the modulus. -/
abbrev alg1Overflow
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : Prop :=
  cfg.env.N ≤ alg1Step2Value cfg b

/-- Finite trace data for a valid input superposition through Step 1. -/
structure Alg1Trace
    {η : ℝ}
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (cfg : ModMulConfig η)
    (ψ : qs.State) where

  support : Finset qs.Basis

  inputCoeff :
    qs.Basis → ℂ

  phaseCoeff :
    qs.Basis →
      Fin (ASize cfg.env.work.active) →
        ℂ

  input_eq :
    ψ =
      ∑ b ∈ support,
        inputCoeff b • qs.ket b

  input_good :
    ∀ b ∈ support,
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b

  full_step1_eq :
    qs.eval
        (step1 (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
        ψ
      =
    ∑ b ∈ support,
      inputCoeff b •
        ∑ t : Fin (ASize cfg.env.work.active),
          phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work.active t.1 b)

  step34_support :
    ∀ b ∈ support,
      ∀ t ∈ alg1GoodLabels cfg b,
        phaseCoeff b t ≠ 0 →
          (alg1Step4CrossCondition cfg b t ↔
            alg1Overflow cfg b)

/-- The target residue is always a canonical residue modulo `N`. -/
lemma alg1TargetResidue_lt_N
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) :
    alg1TargetResidue cfg b < cfg.env.N := by
  have hNpos : 0 < cfg.env.N :=
    Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one
  unfold alg1TargetResidue
  split
  · exact Nat.mod_lt _ hNpos
  · exact hNpos

/-- The ideal Step-2 data-carry value fits in the one-bit-grown data register. -/
lemma alg1Step2Value_lt_dataCarry_capacity
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (hb :
      GoodModMulBasisInput
        (inferInstance : QSemantics)
        cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    alg1Step2Value cfg b < ASize (cfg.env.data.grow 1).active := by
  have hdata_lt_N :
      RegEncoding.toNat cfg.env.data.active b < cfg.env.N := hb.1
  have htarget_lt_N :
      alg1TargetResidue cfg b < cfg.env.N :=
    alg1TargetResidue_lt_N cfg b
  have hsum_lt :
      alg1Step2Value cfg b < 2 * cfg.env.N := by
    unfold alg1Step2Value
    omega
  have hcap :
      2 * cfg.env.N ≤ ASize (cfg.env.data.grow 1).active := by
    have hNcap : cfg.env.N ≤ ASize cfg.env.data.active :=
      cfg.env.data_capacity
    have hcarry :
        cfg.env.data.CanGrow 1 :=
      cfg.env.circuit_workspace.data_canGrow_one

    have hpow :
        ASize (cfg.env.data.grow 1).active =
          2 * ASize cfg.env.data.active := by
      have hReserveLen :
          1 ≤ cfg.env.data.reserve.qubits.length := by
        simpa [ExtReg.CanGrow, ExtReg.capacity, regSize, Reg.width]
          using hcarry
      simp [ASize, ExtReg.grow, ExtReg.newBits, Reg.append,
        Reg.take, regSize, Reg.width, Nat.min_eq_left hReserveLen,
        Nat.pow_succ, Nat.mul_comm]
    omega
  exact lt_of_lt_of_le hsum_lt hcap

/-- The final Algorithm 1 output value fits back in the original data register. -/
lemma alg1OutputValue_lt_data_capacity
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (hb :
      GoodModMulBasisInput
        (inferInstance : QSemantics)
        cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    alg1OutputValue cfg b < ASize cfg.env.data.active := by
  have hNpos : 0 < cfg.env.N :=
    Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one
  unfold alg1OutputValue
  split
  · exact lt_of_lt_of_le (Nat.mod_lt _ hNpos) cfg.env.data_capacity
  · exact lt_of_lt_of_le hb.1 cfg.env.data_capacity




/-! ---------------------------------------------------------
    Concrete reference states used in the Appendix-E proof
--------------------------------------------------------- -/

namespace Alg1Trace

/-- The retained good-label packet after Step 1. -/
noncomputable def goodStep1
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ alg1GoodLabels cfg b,
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work.active t.1 b)

/--
The reference state after Step 2.

For every retained good label `t`, replace the approximate Fourier addition
with the exact integer value `alg1Step2Value cfg b`.
-/
noncomputable def afterStep2Ref
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ alg1GoodLabels cfg b,
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1Step2Value cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b))

/--
The reference state after exact Steps 3 and 4.

The data/carry register now contains the desired residue, while the work
register still contains the good phase-estimation label.
-/
noncomputable def afterStep34Ref
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ alg1GoodLabels cfg b,
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b))


end Alg1Trace

end Step34LabelsAndTracePackets

/-! ---------------------------------------------------------
    Step-1 and Step-5 coefficient packets

The Step-5 cleanup proof compares the original Step-1 fractional load with the
forward circuit whose adjoint is Step 5. These definitions name the QPE
bad-label mass, bad-label packets, shared phase scalars, and inverse-QFT
coefficients for that comparison.
--------------------------------------------------------- -/

section Step1Step5CoefficientPackets

/--
Canonical Step-1 phase-estimation coefficient.

This is the actual amplitude of the work-label basis vector in the Step-1
output.
-/
noncomputable def alg1PhaseCoeff
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work.active)) : ℂ :=
  inner ℂ
    (qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b))
    (qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) (qs.ket b))

/-- The QPE probability mass outside the retained good-label set for one basis input. -/
noncomputable def alg1QpeBadMass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis) : ℝ :=
  ∑ t ∈ Finset.univ.filter
      (fun t => t ∉ alg1GoodLabels cfg b),
    ‖alg1PhaseCoeff qs cfg b t‖ ^ 2

/--
The bad-label mass of a whole finite trace.

This is the squared input amplitude of each basis branch times that branch's
discarded QPE probability.
-/
noncomputable def alg1TraceBadMass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : ℝ :=
  ∑ b ∈ tr.support,
    ‖tr.inputCoeff b‖ ^ 2 *
      ∑ t ∈ Finset.univ.filter
          (fun t => t ∉ alg1GoodLabels cfg b),
        ‖tr.phaseCoeff b t‖ ^ 2

namespace Alg1Trace

/-- The Step-1 packet consisting only of the discarded QPE labels. -/
noncomputable def badStep1
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ Finset.univ.filter
          (fun t => t ∉ alg1GoodLabels cfg b),
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work.active t.1 b)

/--
The formal post-Step-3/4 packet with all QPE labels retained.

This is not the operational output of Steps 3–4 on bad labels. It is the
reference packet used to identify the inverse cleanup with the QPE tail.
-/
noncomputable def afterStep34Full
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t : Fin (ASize cfg.env.work.active),
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b))

/-- The discarded part of `afterStep34Full`. -/
noncomputable def afterStep34Bad
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ Finset.univ.filter
          (fun t => t ∉ alg1GoodLabels cfg b),
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b))

end Alg1Trace

/--
The forward circuit whose adjoint is `ModMulConfig.U5`.

Keeping this named avoids repeatedly unfolding `step5`.
-/
noncomputable def alg1Step5Forward
    {η : ℝ}
    {Basis : Type*}
    [RegEncoding Basis]
  (cfg : ModMulConfig η) : Gate :=
  (H_reg cfg.env.work.active) ;;
  (Gate.CPhaseProdUsing
    cfg.ctrl
    ((2 * Real.pi * ((step5Constant cfg.c cfg.env.N % cfg.env.N : ℕ) : ℝ)) / (cfg.env.N : ℝ))
    (cfg.env.data.grow 1).active
    cfg.env.work.active cfg.env.circuit_workspace.step5Workspace) ;;
  (IQFT cfg.env.work)

/-- The Step-1 controlled phase angle. -/
noncomputable def alg1Step1Phase
  {η : ℝ}
  (cfg : ModMulConfig η) : ℝ :=
  (2 * Real.pi *
      (((cfg.c + cfg.env.N - 1) % cfg.env.N : ℕ) : ℝ))
    / (cfg.env.N : ℝ)

/-- The forward Step-5 controlled phase angle. -/
noncomputable def alg1Step5Phase
  {η : ℝ}
  (cfg : ModMulConfig η) : ℝ :=
  (2 * Real.pi *
      ((step5Constant cfg.c cfg.env.N % cfg.env.N : ℕ) : ℝ))
    / (cfg.env.N : ℝ)

/--
The diagonal phase acquired by work label `z` during the original Step-1
fractional load.
-/
noncomputable def alg1Step1PhaseScalar
    {Basis : Type*}
    [RegEncoding Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : Basis)
    (z : Fin (ASize cfg.env.work.active)) : ℂ :=
  if RegEncoding.bit cfg.ctrl b then
    Complex.exp
      (alg1Step1Phase cfg * Complex.I *
        ((RegEncoding.toNat cfg.env.data.active b : ℂ) * (z.1 : ℂ)))
  else
    1

/--
The common target-residue form of a phase scalar.

Both Step 1 and the forward Step-5 fractional load reduce to this scalar.
-/
noncomputable def alg1TargetPhaseScalar
    [QSemantics]
    [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (z : Fin (ASize cfg.env.work.active)) : ℂ :=
  if RegEncoding.bit cfg.ctrl b then
    Complex.exp
      (((2 * Real.pi) / (cfg.env.N : ℝ)) * Complex.I *
        ((alg1TargetResidue cfg b : ℂ) * (z.1 : ℂ)))
  else
    1

/--
The uniform-H coefficient multiplied by the Step-1 diagonal phase.
-/
noncomputable def alg1LoadPreCoeff
    {Basis : Type*}
    [RegEncoding Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : Basis)
    (z : Fin (ASize cfg.env.work.active)) : ℂ :=
  (1 / Real.sqrt ((ASize cfg.env.work.active : ℕ) : ℝ) : ℂ) *
    alg1Step1PhaseScalar cfg b z

/-- The adjoint-QFT matrix entry from source work label `z` to target `t`. -/
noncomputable def alg1IQFTCoeff
    (work : Reg)
    (z t : Fin (ASize work)) : ℂ :=
  (1 / Real.sqrt ((ASize work : ℕ) : ℝ) : ℂ) *
    star (qftPhase (ASize work) z.1 t.1)

/--
The explicit final QPE / fractional-load coefficient.

This is the coefficient after H, diagonal phase, and inverse QFT.
-/
noncomputable def alg1FractionalLoadCoeff
    {Basis : Type*}
    [RegEncoding Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : Basis)
    (t : Fin (ASize cfg.env.work.active)) : ℂ :=
  ∑ z : Fin (ASize cfg.env.work.active),
    alg1LoadPreCoeff cfg b z *
      alg1IQFTCoeff cfg.env.work.active z t

end Step1Step5CoefficientPackets

/-! ---------------------------------------------------------
    Modular-exponentiation arithmetic helpers

The modular-exponentiation recursion repeatedly uses powers of the input base.
This final helper packages the coprimality fact needed for every such multiplier.
--------------------------------------------------------- -/

section ModExpArithmeticHelpers

/-- If `a` is coprime to `N`, every modular-exponentiation multiplier is also coprime to `N`. -/
theorem modExp_multiplier_coprime
    (a N e : ℕ)
    (hcoprime : Nat.Coprime a N) :
    Nat.Coprime ((a ^ (2 ^ e)) % N) N := by
  have hpow : Nat.Coprime (a ^ (2 ^ e)) N :=
    hcoprime.pow_left (2 ^ e)
  rw [Nat.coprime_iff_gcd_eq_one]
  calc
    Nat.gcd ((a ^ (2 ^ e)) % N) N
        = Nat.gcd (a ^ (2 ^ e)) N :=
          Nat.ModEq.gcd_eq (by simp [Nat.ModEq])
    _ = 1 := hpow.gcd_eq_one

end ModExpArithmeticHelpers

end Shor
