import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Config
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.CmpLtNW
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.Model
import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.Shared.States
import FastMultiplication.ShorVerification.Implementation.Shared.Registers
import FastMultiplication.ShorVerification.Implementation.Shared.Hadamard
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Shor

universe u

namespace Shor

namespace IdealCtrlModMulExactSemantics

theorem eval_idealCtrlModMul_good_ket_exact
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
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
    qs.eval (Gate.idealCtrlModMul c N data.active ctrl) (qs.ket b) =
    qs.ket
      (RegEncoding.writeNat data.active
        (if RegEncoding.bit ctrl b then
          (c * RegEncoding.toNat data.active b) % N
        else
          RegEncoding.toNat data.active b)
        b) := by
  apply IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact
  · exact hN
  · exact hsize
  · exact hcoprime
  · simp [ModMulCoreLayout] at hlayout
    intro hctrlActive
    exact hlayout.2.2.2.1 (by simp [ExtReg.ownedQubits, hctrlActive])
  · exact hb.1

end IdealCtrlModMulExactSemantics

/-! =========================================================
    Modular Multiplication Bounds Core

This file contains the shared definitions for the modular-multiplication and
modular-exponentiation approximation proofs: ideal specifications, Algorithm 1
gates, layout and validity predicates, precision side conditions, reusable
configuration records, and the reference packets used by the Step 1/2/3/4/5
bound files.
========================================================= -/

/-! =========================================================
    Valid inputs and ideal controlled multiplication

The later approximation theorems work on a valid-input subspace. This section
defines the layout and clean-input predicates for that subspace, specifies the
ideal controlled modular multiplier on good basis states, and proves that the
ideal gate preserves the whole valid subspace.
========================================================= -/

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
  have hnew_active : Disjoint (e.newBits n) e.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqNew hqActive

    have hdisj := e.active_reserve_disjoint
    rw [Disjoint, List.disjoint_left] at hdisj

    exact hdisj hqActive (List.mem_of_mem_take hqNew)

  unfold ExtReg.FreshFor FreshZero at hfresh ⊢

  calc
    RegEncoding.toNat (e.newBits n) (RegEncoding.writeNat e.active value b)
      = RegEncoding.toNat (e.newBits n) b := by
        exact
          RegEncoding.toNat_left_write_right (e.newBits n) e.active hnew_active b value
    _ = 0 := hfresh

/-- The ideal controlled multiplier maps good basis inputs to good basis outputs with the expected residue. -/
theorem IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
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
      qs.eval (Gate.idealCtrlModMul c N data.active ctrl) (qs.ket b) = qs.ket b' ∧
      GoodModMulBasisInput qs N data work flag b' ∧
      RegEncoding.bit ctrl b' = RegEncoding.bit ctrl b ∧
      RegEncoding.toNat data.active b' =
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

  let b' : qs.Basis := RegEncoding.writeNat data.active out b

  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN

  have howned : ∀ q, q ∈ data.ownedQubits → q ∈ work.ownedQubits → False := by
    have h := hlayout.1
    rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h
    exact h

  have hwork_data : Disjoint work.active data.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqWork hqData

    apply howned

    · show q ∈ data.active.qubits ++ data.reserve.qubits
      exact List.mem_append_left _ hqData

    · show q ∈ work.active.qubits ++ work.reserve.qubits
      exact List.mem_append_left _ hqWork

  have hworkNew_data : Disjoint (work.newBits 1) data.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqNew hqData

    have hqReserve : q ∈ work.reserve.qubits :=
      List.mem_of_mem_take hqNew

    apply howned

    · show q ∈ data.active.qubits ++ data.reserve.qubits
      exact List.mem_append_left _ hqData

    · show q ∈ work.active.qubits ++ work.reserve.qubits
      exact List.mem_append_right _ hqReserve

  have hflag_data : Disjoint (qubitReg flag) data.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqFlag hqData

    have hq : q = flag := by simpa [qubitReg, Reg.singleton] using hqFlag
    subst q

    exact hlayout.2.1 (show flag ∈ data.ownedQubits by exact List.mem_append_left _ hqData)

  have hctrl_data : ctrl ∉ data.active.qubits := by
    intro hctrlActive

    exact hlayout.2.2.2.1
      (show ctrl ∈ data.ownedQubits by exact List.mem_append_left _ hctrlActive)

  have hout_lt_N : out < N := by
    by_cases hctrl : RegEncoding.bit ctrl b
    · simpa [out, hctrl] using
        Nat.mod_lt (c * RegEncoding.toNat data.active b) hNpos
    · simpa [out, hctrl] using hb.1

  have hout_lt_cap : out < ASize data.active := lt_of_lt_of_le hout_lt_N hsize

  have hdata_out : RegEncoding.toNat data.active b' = out := by
    dsimp [b']
    exact RegEncoding.toNat_writeNat_of_lt data.active out b hout_lt_cap

  have hdataFresh_out : data.FreshFor 2 b' := by
    dsimp [b']
    exact ExtReg.freshFor_write_active data 2 out b hb.2.1

  have hwork_out : RegEncoding.toNat work.active b' = 0 := by
    calc
      RegEncoding.toNat work.active b' = RegEncoding.toNat work.active b := by
        dsimp [b']
        exact RegEncoding.toNat_left_write_right work.active data.active hwork_data b out
      _ = 0 := hb.2.2.1

  have hworkFresh_in : RegEncoding.toNat (work.newBits 1) b = 0 := by
    simpa [ExtReg.FreshFor, FreshZero] using hb.2.2.2.1

  have hworkFresh_out : work.FreshFor 1 b' := by
    have hzero : RegEncoding.toNat (work.newBits 1) b' = 0 := by
      calc
        RegEncoding.toNat (work.newBits 1) b' = RegEncoding.toNat (work.newBits 1) b := by
          dsimp [b']
          exact
            RegEncoding.toNat_left_write_right (work.newBits 1) data.active hworkNew_data b out
        _ = 0 := hworkFresh_in

    simpa [ExtReg.FreshFor, FreshZero] using hzero

  have hflag_out : RegEncoding.toNat (qubitReg flag) b' = 0 := by
    calc
      RegEncoding.toNat (qubitReg flag) b' = RegEncoding.toNat (qubitReg flag) b := by
        dsimp [b']
        exact RegEncoding.toNat_left_write_right (qubitReg flag) data.active hflag_data b out
      _ = 0 := hb.2.2.2.2

  have hgood_out : GoodModMulBasisInput qs N data work flag b' := by
    refine ⟨?_, hdataFresh_out, hwork_out, hworkFresh_out, hflag_out⟩

    calc
      RegEncoding.toNat data.active b' = out := hdata_out
      _ < N := hout_lt_N

  have hctrl_out : RegEncoding.bit ctrl b' = RegEncoding.bit ctrl b := by
    dsimp [b']
    exact
      RegEncoding.bit_writeNat_out (r := data.active) (v := out) (b := b) (q := ctrl) hctrl_data

  have heval : qs.eval (Gate.idealCtrlModMul c N data.active ctrl) (qs.ket b) = qs.ket b' := by
    simpa [b', out] using
      (IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket_exact
        (qs := qs) c N data work flag ctrl b hN hsize hcoprime hlayout hb)

  refine ⟨b', heval, hgood_out, hctrl_out, ?_⟩

  simpa [out] using hdata_out

/-- The ideal controlled multiplier preserves the span of all good modular-multiplication states. -/
theorem idealCtrlModMul_preserves_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [IdealCtrlModMulExactSemantics qs]
    (c N : ℕ)
    (data work : ExtReg)
    (flag ctrl : ℕ)
    (hN : 1 < N)
    (hsize : N ≤ ASize data.active)
    (hcoprime : Nat.Coprime c N)
    (hlayout : ModMulCoreLayout data work flag ctrl)
    (ψ : qs.State)
    (hvalid : ψ ∈ ValidModMulState qs N data work flag) :
    qs.eval (Gate.idealCtrlModMul c N data.active ctrl) ψ ∈
      ValidModMulState qs N data work flag := by
  classical

  let validSet : Set qs.State :=
    { ξ : qs.State | ∃ b : qs.Basis, GoodModMulBasisInput qs N data work flag b ∧ ξ = qs.ket b }

  change ψ ∈ Submodule.span ℂ validSet at hvalid

  change qs.eval (Gate.idealCtrlModMul c N data.active ctrl) ψ ∈ Submodule.span ℂ validSet

  refine
    Submodule.span_induction (s := validSet)
      (p := fun ξ _ =>
        qs.eval (Gate.idealCtrlModMul c N data.active ctrl) ξ ∈ Submodule.span ℂ validSet)
      ?basis ?zero ?add ?smul hvalid

  case basis =>
    intro ξ hξ

    change ∃ b : qs.Basis, GoodModMulBasisInput qs N data work flag b ∧ ξ = qs.ket b at hξ

    rcases hξ with ⟨b, hb, rfl⟩

    obtain ⟨b', heval, hgood, _hctrl, _hdata⟩ :=
      IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket
        (qs := qs) c N data work flag ctrl b hN hsize hcoprime hlayout hb

    rw [heval]

    exact Submodule.subset_span (show qs.ket b' ∈ validSet from ⟨b', hgood, rfl⟩)

  case zero =>
    change qs.eval (Gate.idealCtrlModMul c N data.active ctrl) 0 ∈ Submodule.span ℂ validSet

    rw [qs.eval_zero]
    exact (Submodule.span ℂ validSet).zero_mem

  case add =>
    intro ξ ζ _hξ _hζ hξEval hζEval

    change
      qs.eval (Gate.idealCtrlModMul c N data.active ctrl) (ξ + ζ) ∈ Submodule.span ℂ validSet

    rw [qs.eval_add]

    exact (Submodule.span ℂ validSet).add_mem hξEval hζEval

  case smul =>
    intro a ξ _hξ hξEval

    change
      qs.eval (Gate.idealCtrlModMul c N data.active ctrl) (a • ξ) ∈ Submodule.span ℂ validSet

    rw [qs.eval_smul]

    exact (Submodule.span ℂ validSet).smul_mem a hξEval

end ValidInputsAndIdealSemantics

/-! =========================================================
    Algorithm 1 precision and arithmetic constants

This section packages the concrete precision schedule for Algorithm 1 and the
Step-5 inverse constant used by the cleanup phase.
========================================================= -/

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
    regSize work = regSize data + algorithm1ExtraBits η :=
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
    regSize work - regSize data = algorithm1ExtraBits η := by
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
    (2 : ℝ) ^ (regSize work - regSize data) ≥ (2 + 1 / (2 * η)) ^ 2 := by
  let a : ℝ := 2 + 1 / (2 * η)

  have ha : 0 < a := by
    dsimp [a]
    have hη : 0 < η := eta_pos h
    positivity

  have hdiff : regSize work - regSize data = algorithm1ExtraBits η :=
    work_width_sub_data_width h

  rw [hdiff]

  have hceil : 2 * Real.logb 2 a ≤ (algorithm1ExtraBits η : ℝ) := by
    dsimp [algorithm1ExtraBits]
    exact Nat.le_ceil _

  have hlog : Real.logb 2 (a ^ 2) ≤ (algorithm1ExtraBits η : ℝ) := by
    rw [Real.logb_pow]
    simpa using hceil

  have hrpow : a ^ 2 ≤ (2 : ℝ) ^ (algorithm1ExtraBits η : ℝ) := by
    exact
      (Real.logb_le_iff_le_rpow
        (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < a ^ 2)).1 hlog

  have hpow : a ^ 2 ≤ (2 : ℝ) ^ algorithm1ExtraBits η := by
    simpa [Real.rpow_natCast] using hrpow

  simpa [a] using hpow

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

section ModExpLayoutAndGates

end ModExpLayoutAndGates

section PrimitiveAndIdealConfigFacts

section ModMulPrimitiveDerivedSemantics

variable
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]

/-! =========================================================
    Small register/flag helpers
========================================================= -/

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

omit [GateSemanticsCore qs] in
lemma bit_qubitReg_eq_testBit_zero
    (q : ℕ) (b : qs.Basis) :
    RegEncoding.bit q b = Nat.testBit (RegEncoding.toNat (qubitReg q) b) 0 := by
  simpa [qubitReg, Reg.singleton, Reg.get, regSize, Reg.width] using
    (RegEncoding.bit_eq_testBit_toNat (r := qubitReg q) (b := b)
      (i := (⟨0, by simp⟩ : Fin (regSize (qubitReg q)))))

omit [GateSemanticsCore qs] in
lemma bit_false_of_qubitReg_toNat_zero
    (q : ℕ) (b : qs.Basis)
    (h : RegEncoding.toNat (qubitReg q) b = 0) :
    RegEncoding.bit q b = false := by
  rw [bit_qubitReg_eq_testBit_zero (qs := qs) q b, h]
  simp
omit [GateSemanticsCore qs] in
lemma bit_true_of_qubitReg_toNat_one
    (q : ℕ) (b : qs.Basis)
    (h : RegEncoding.toNat (qubitReg q) b = 1) :
    RegEncoding.bit q b = true := by
  rw [bit_qubitReg_eq_testBit_zero (qs := qs) q b, h]
  simp
omit [GateSemanticsCore qs] in
lemma bit_write_qubitReg_zero
    (q : ℕ) (b : qs.Basis) :
    RegEncoding.bit q (RegEncoding.writeNat (qubitReg q) 0 b) = false := by
  apply bit_false_of_qubitReg_toNat_zero (qs := qs)
  exact RegEncoding.toNat_writeNat_of_lt (qubitReg q) 0 b (by simp [ASize])

omit [GateSemanticsCore qs] in
lemma bit_write_qubitReg_one
    (q : ℕ) (b : qs.Basis) :
    RegEncoding.bit q (RegEncoding.writeNat (qubitReg q) 1 b) = true := by
  apply bit_true_of_qubitReg_toNat_one (qs := qs)
  exact RegEncoding.toNat_writeNat_of_lt (qubitReg q) 1 b (by simp [ASize])

lemma eval_cmpGeConst_ket_of_outside
    [ModularArithmeticSemantics qs]
    (N : ℕ)
    (data scratch : ExtReg)
    (flag : ℕ)
    (b : qs.Basis)
    (hout : flag ∉ data.active.qubits) :
    qs.eval (Gate.CmpGeConst N data scratch flag) (qs.ket b) = qs.ket
      (RegEncoding.writeNat (qubitReg flag)
        (if RegEncoding.bit flag b then
          if N ≤ RegEncoding.toNat data.active b then 0 else 1
        else
          if N ≤ RegEncoding.toNat data.active b then 1 else 0)
        b) := by
  rw [ModularArithmeticSemantics.eval_CmpGeConst_ket]
  simp [cmpGeConstBasis, hout]

lemma eval_csubConst_ket_of_outside
    [ModularArithmeticSemantics qs]
    (N : ℕ)
    (data scratch : ExtReg)
    (flag : ℕ)
    (b : qs.Basis)
    (hout : flag ∉ data.active.qubits) :
    qs.eval (Gate.CSubConst N data scratch flag) (qs.ket b) = qs.ket
      (RegEncoding.writeNat data.active
        (if RegEncoding.bit flag b then
          (RegEncoding.toNat data.active b + ASize data.active - (N % ASize data.active)) %
            ASize data.active
        else
          RegEncoding.toNat data.active b)
        b) := by
  rw [ModularArithmeticSemantics.eval_CSubConst_ket]
  simp [csubConstBasis, hout]

theorem eval_step3_clean_ket
    [ModularArithmeticSemantics qs]
    (N : ℕ)
    (x_ext scratch : ExtReg)
    (flag : ℕ)
    (b : qs.Basis)
    (hout : QubitOutside flag x_ext.active)
    (hflag : RegEncoding.toNat (qubitReg flag) b = 0) :
    qs.eval (step3 N x_ext scratch flag) (qs.ket b) = qs.ket
      (RegEncoding.writeNat (qubitReg flag)
        (if N ≤ RegEncoding.toNat x_ext.active b then 1 else 0)
        (RegEncoding.writeNat x_ext.active
          (if N ≤ RegEncoding.toNat x_ext.active b then
            RegEncoding.toNat x_ext.active b - N
          else
            RegEncoding.toNat x_ext.active b)
          b)) := by
  have hout' : flag ∉ x_ext.active.qubits := by simpa [QubitOutside] using hout

  have hflag_x : Disjoint (qubitReg flag) x_ext.active := disjoint_qubitReg_of_outside hout'

  have hx_flag : Disjoint x_ext.active (qubitReg flag) := Disjoint.symm hflag_x

  have hbit0 : RegEncoding.bit flag b = false :=
    bit_false_of_qubitReg_toNat_zero (qs := qs) flag b hflag

  have hxcap : RegEncoding.toNat x_ext.active b < ASize x_ext.active :=
    RegEncoding.toNat_lt_ASize x_ext.active b

  rw [step3, qs.eval_seq]

  rw [eval_cmpGeConst_ket_of_outside (qs := qs) N x_ext scratch flag b hout']

  by_cases hge : N ≤ RegEncoding.toNat x_ext.active b

  · -- The comparison sets flag = 1, then CSUB subtracts N.
    simp only [hbit0, Bool.false_eq_true, if_false, hge, if_pos]

    let b₁ := RegEncoding.writeNat (qubitReg flag) 1 b

    have hx₁ : RegEncoding.toNat x_ext.active b₁ = RegEncoding.toNat x_ext.active b := by
      exact RegEncoding.toNat_left_write_right x_ext.active (qubitReg flag) hx_flag b 1

    have hbit₁ : RegEncoding.bit flag b₁ = true := by
      exact bit_write_qubitReg_one (qs := qs) flag b

    have hNcap : N < ASize x_ext.active := by exact lt_of_le_of_lt hge hxcap

    have hsubcap : RegEncoding.toNat x_ext.active b - N < ASize x_ext.active := by omega

    have hwrapped :
        (RegEncoding.toNat x_ext.active b + ASize x_ext.active - (N % ASize x_ext.active)) %
            ASize x_ext.active
          = RegEncoding.toNat x_ext.active b - N := by
      rw [Nat.mod_eq_of_lt hNcap]

      have hrewrite :
          RegEncoding.toNat x_ext.active b + ASize x_ext.active - N
            = ASize x_ext.active + (RegEncoding.toNat x_ext.active b - N) := by
        omega

      rw [hrewrite]
      simp [Nat.mod_eq_of_lt hsubcap]

    rw [eval_csubConst_ket_of_outside (qs := qs) N x_ext scratch flag b₁ hout']

    simp only [hbit₁, if_true, hx₁, hwrapped]

    apply congrArg qs.ket

    exact
      (writeNat_comm_of_disjoint (qubitReg flag) x_ext.active hflag_x 1
        (RegEncoding.toNat x_ext.active b - N) b).symm

  · -- The comparison leaves flag = 0, so CSUB is inactive.
    simp only [hbit0, Bool.false_eq_true, if_false, hge]

    let b₀ := RegEncoding.writeNat (qubitReg flag) 0 b

    have hx₀ : RegEncoding.toNat x_ext.active b₀ = RegEncoding.toNat x_ext.active b := by
      exact RegEncoding.toNat_left_write_right x_ext.active (qubitReg flag) hx_flag b 0

    have hbit₀ : RegEncoding.bit flag b₀ = false := by
      exact bit_write_qubitReg_zero (qs := qs) flag b

    rw [eval_csubConst_ket_of_outside (qs := qs) N x_ext scratch flag b₀ hout']

    simp only [hbit₀, Bool.false_eq_true, if_false]

    have hwrite₀ :
        RegEncoding.writeNat x_ext.active (RegEncoding.toNat x_ext.active b) b₀ = b₀ := by
      rw [← hx₀]
      exact RegEncoding.writeNat_toNat x_ext.active b₀

    rw [hx₀]
    apply congrArg qs.ket
    rw [hwrite₀]
    dsimp [b₀]
    rw [RegEncoding.writeNat_toNat]

end ModMulPrimitiveDerivedSemantics

section ModMulPrimitiveDerivedSemantics

variable
    (qs : QSemantics)
    [RegEncoding qs.Basis]

theorem eval_step4_cancels_ket
    [GateSemanticsFacts qs]
    (N : ℕ)
    (dataCarry work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace : CmpLtNWWorkspace N dataCarry work scratch flag)
    (b : qs.Basis)
    (hdataFresh : dataCarry.FreshFor 1 b)
    (hworkFresh : work.FreshFor 1 b)
    (hscratchZero : RegEncoding.toNat scratch.active b = 0)
    (hscratchFresh : scratch.FreshFor 1 b)
    (hflag :
      RegEncoding.toNat (qubitReg flag) b =
        if RegEncoding.toNat dataCarry.active b * ASize work.active <
            N * RegEncoding.toNat work.active b
        then 1
        else 0) :
    qs.eval (step4 N dataCarry work scratch flag hworkspace) (qs.ket b) =
      qs.ket (RegEncoding.writeNat (qubitReg flag) 0 b) := by
  rw [step4]
  rw [eval_cmp_lt_nw_ket (qs := qs) N dataCarry work scratch flag hworkspace b
    hdataFresh hworkFresh hscratchZero hscratchFresh]
  by_cases hcmp :
      RegEncoding.toNat dataCarry.active b * ASize work.active < N * RegEncoding.toNat work.active b
  · have hflag1 : RegEncoding.toNat (qubitReg flag) b = 1 := by simpa [hcmp] using hflag
    have hbit : RegEncoding.bit flag b = true :=
      bit_true_of_qubitReg_toNat_one (qs := qs) flag b hflag1
    simp [hcmp, hbit]
  · have hflag0 : RegEncoding.toNat (qubitReg flag) b = 0 := by simpa [hcmp] using hflag
    have hbit : RegEncoding.bit flag b = false :=
      bit_false_of_qubitReg_toNat_zero (qs := qs) flag b hflag0
    simp [hcmp, hbit]

theorem eval_step3_local_ket
    [GateSemanticsCore qs]
    [ModularArithmeticSemantics qs]
    (N : ℕ)
    (dataCarry scratch : ExtReg)
    (flag : ℕ)
    (b : qs.Basis)
    (hout : QubitOutside flag dataCarry.active) :
    ∃ b' : qs.Basis,
      qs.eval (step3 N dataCarry scratch flag) (qs.ket b) = qs.ket b' ∧
      ∀ q, q ∉ dataCarry.active.qubits → q ≠ flag →
        RegEncoding.bit q b' = RegEncoding.bit q b := by
  classical

  have hout' : flag ∉ dataCarry.active.qubits := by simpa [QubitOutside] using hout

  let cmpValue : ℕ :=
    if RegEncoding.bit flag b then
      if N ≤ RegEncoding.toNat dataCarry.active b then 0 else 1
    else
      if N ≤ RegEncoding.toNat dataCarry.active b then 1 else 0

  let b₁ : qs.Basis := RegEncoding.writeNat (qubitReg flag) cmpValue b

  let subValue : ℕ :=
    if RegEncoding.bit flag b₁ then
      (RegEncoding.toNat dataCarry.active b₁ + ASize dataCarry.active -
          (N % ASize dataCarry.active)) % ASize dataCarry.active
    else
      RegEncoding.toNat dataCarry.active b₁

  let b' : qs.Basis := RegEncoding.writeNat dataCarry.active subValue b₁

  refine ⟨b', ?_, ?_⟩

  · rw [step3, qs.eval_seq]

    rw [eval_cmpGeConst_ket_of_outside (qs := qs) N dataCarry scratch flag b hout']

    change qs.eval (Gate.CSubConst N dataCarry scratch flag) (qs.ket b₁) = qs.ket b'

    rw [eval_csubConst_ket_of_outside (qs := qs) N dataCarry scratch flag b₁ hout']
  · intro q hqData hqFlag

    have hqFlagReg : q ∉ (qubitReg flag).qubits := by
      simpa [qubitReg, Reg.singleton] using hqFlag

    dsimp [b', b₁]

    rw [RegEncoding.bit_writeNat_out dataCarry.active subValue b₁ q hqData]

    exact RegEncoding.bit_writeNat_out (qubitReg flag) cmpValue b q hqFlagReg

theorem eval_step4_local_ket
    [GateSemanticsFacts qs]
    (N : ℕ)
    (dataCarry work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace : CmpLtNWWorkspace N dataCarry work scratch flag)
    (b : qs.Basis)
    (hdataFresh : dataCarry.FreshFor 1 b)
    (hworkFresh : work.FreshFor 1 b)
    (hscratchZero : RegEncoding.toNat scratch.active b = 0)
    (hscratchFresh : scratch.FreshFor 1 b) :
    ∃ b' : qs.Basis,
      qs.eval (step4 N dataCarry work scratch flag hworkspace) (qs.ket b) = qs.ket b' ∧
      ∀ q, q ∉ dataCarry.active.qubits → q ∉ work.active.qubits → q ≠ flag →
        RegEncoding.bit q b' = RegEncoding.bit q b := by
  let flagValue : ℕ :=
    if RegEncoding.bit flag b then
      if RegEncoding.toNat dataCarry.active b * ASize work.active <
          N * RegEncoding.toNat work.active b
      then 0
      else 1
    else
      if RegEncoding.toNat dataCarry.active b * ASize work.active <
          N * RegEncoding.toNat work.active b
      then 1
      else 0

  let b' : qs.Basis := RegEncoding.writeNat (qubitReg flag) flagValue b

  refine ⟨b', ?_, ?_⟩
  · rw [step4]
    simpa [b', flagValue] using
      (eval_cmp_lt_nw_ket (qs := qs) N dataCarry work scratch flag hworkspace b
        hdataFresh hworkFresh hscratchZero hscratchFresh)
  · intro q _ _ hqFlag
    have hqFlagReg : q ∉ (qubitReg flag).qubits := by
      simpa [qubitReg, Reg.singleton] using hqFlag
    dsimp [b']
    exact RegEncoding.bit_writeNat_out (qubitReg flag) flagValue b q hqFlagReg

end ModMulPrimitiveDerivedSemantics

/-- Configuration wrapper around the exact ideal controlled-multiplier basis semantics. -/
theorem IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_cfg
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η) (b : qs.Basis)
    (hb : GoodModMulBasisInput qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval (ModMulConfig.idealGate cfg) (qs.ket b) = qs.ket
      (RegEncoding.writeNat cfg.env.data.active
        (if RegEncoding.bit cfg.ctrl b then
          (cfg.c * RegEncoding.toNat cfg.env.data.active b) % cfg.env.N
        else
          RegEncoding.toNat cfg.env.data.active b)
        b) := by
  simpa [ModMulConfig.idealGate] using
    (IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket_exact
      (qs := qs) cfg.c cfg.env.N cfg.env.data cfg.env.work cfg.flag cfg.ctrl b
      cfg.env.modulus_gt_one cfg.env.data_capacity cfg.coprime cfg.layout hb)

end PrimitiveAndIdealConfigFacts

/-! =========================================================
    Step-3/4 labels and trace packets

This section records the exact data values after the comparator/subtractor
stages and packages the finite trace expansions used by the Appendix-E-style
Algorithm 1 error decomposition.
========================================================= -/

section Step34LabelsAndTracePackets

/-- The target residue is always a canonical residue modulo `N`. -/
lemma alg1TargetResidue_lt_N
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) :
    alg1TargetResidue cfg b < cfg.env.N := by
  have hNpos : 0 < cfg.env.N := Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one
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
      GoodModMulBasisInput (inferInstance : QSemantics)
        cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    alg1Step2Value cfg b < ASize (cfg.env.data.grow 1).active := by
  have hdata_lt_N : RegEncoding.toNat cfg.env.data.active b < cfg.env.N := hb.1
  have htarget_lt_N : alg1TargetResidue cfg b < cfg.env.N := alg1TargetResidue_lt_N cfg b
  have hsum_lt : alg1Step2Value cfg b < 2 * cfg.env.N := by
    unfold alg1Step2Value
    omega
  have hcap : 2 * cfg.env.N ≤ ASize (cfg.env.data.grow 1).active := by
    have hNcap : cfg.env.N ≤ ASize cfg.env.data.active := cfg.env.data_capacity
    have hcarry : cfg.env.data.CanGrow 1 := cfg.env.circuit_workspace.data_canGrow_one

    have hpow :
        ASize (cfg.env.data.grow 1).active = 2 * ASize cfg.env.data.active := by
      have hReserveLen : 1 ≤ cfg.env.data.reserve.qubits.length := by
        simpa [ExtReg.CanGrow, ExtReg.capacity, regSize, Reg.width] using hcarry
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
      GoodModMulBasisInput (inferInstance : QSemantics)
        cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    alg1OutputValue cfg b < ASize cfg.env.data.active := by
  have hNpos : 0 < cfg.env.N := Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one
  unfold alg1OutputValue
  split
  · exact lt_of_lt_of_le (Nat.mod_lt _ hNpos) cfg.env.data_capacity
  · exact lt_of_lt_of_le hb.1 cfg.env.data_capacity

end Step34LabelsAndTracePackets

/-! =========================================================
    Modular-exponentiation arithmetic helpers

The modular-exponentiation recursion repeatedly uses powers of the input base.
This final helper packages the coprimality fact needed for every such multiplier.
========================================================= -/

section ModExpArithmeticHelpers

/-- If `a` is coprime to `N`, every modular-exponentiation multiplier is also coprime to `N`. -/
theorem modExp_multiplier_coprime
    (a N e : ℕ)
    (hcoprime : Nat.Coprime a N) :
    Nat.Coprime ((a ^ (2 ^ e)) % N) N := by
  have hpow : Nat.Coprime (a ^ (2 ^ e)) N := hcoprime.pow_left (2 ^ e)
  rw [Nat.coprime_iff_gcd_eq_one]
  calc
    Nat.gcd ((a ^ (2 ^ e)) % N) N
        = Nat.gcd (a ^ (2 ^ e)) N :=
          Nat.ModEq.gcd_eq (by simp [Nat.ModEq])
    _ = 1 := hpow.gcd_eq_one

end ModExpArithmeticHelpers

namespace RegisterHadamardSemantics

/-- The original `RegisterHadamardSemantics` result, derived solely from
ordinary one-qubit Hadamard semantics and the generic evaluator laws. -/
theorem eval_Hreg_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [HadamardSemantics qs]
    (r : Reg)
    (b : qs.Basis) :
    ∃ α : Fin (ASize r) → ℂ,
      qs.eval
          ((regQubits r).foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            Gate.id)
          (qs.ket b)
        =
      ∑ t : Fin (ASize r),
        α t •
          qs.ket
            (RegEncoding.writeNat r t.1 b) := by
  classical

  let S := ketSpan qs r b

  -- The initial ket is already one of the generators:
  -- choose the value currently stored in r.
  let t₀ : Fin (ASize r) :=
    ⟨RegEncoding.toNat r b,
      RegEncoding.toNat_lt_ASize r b⟩

  have hstart :
      qs.ket b ∈ S := by
    have hmem :
        qs.ket (RegEncoding.writeNat r t₀.1 b)
          ∈ S := by
      change
        qs.ket (RegEncoding.writeNat r t₀.1 b)
          ∈ Submodule.span ℂ
              (Set.range fun t : Fin (ASize r) =>
                qs.ket
                  (RegEncoding.writeNat r t.1 b))

      apply Submodule.subset_span
      exact Set.mem_range.mpr ⟨t₀, rfl⟩

    simpa [t₀, RegEncoding.writeNat_toNat] using hmem

  -- Every H in the fold acts on a qubit of r, hence the entire folded
  -- circuit stays inside S.
  have hout :
      qs.eval
          ((regQubits r).foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            Gate.id)
          (qs.ket b)
        ∈ S := by

    apply
      eval_foldl_H_mem
        qs r b
        (regQubits r)

    · intro q hq
      exact hq

    · intro ψ hψ
      simp [GateSemanticsCore.eval_id]
      exact hψ

    · exact hstart

  -- Membership in the span of a finite family is exactly existence of
  -- finite coefficients indexed by that family.
  have hout' :
      qs.eval
          ((regQubits r).foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            Gate.id)
          (qs.ket b)
        ∈
      Submodule.span ℂ
        (Set.range fun t : Fin (ASize r) =>
          qs.ket
            (RegEncoding.writeNat r t.1 b)) := by
    exact hout

  rcases
      (Submodule.mem_span_range_iff_exists_fun ℂ).mp hout'
    with ⟨α, hα⟩

  refine ⟨α, ?_⟩

  exact hα.symm

end RegisterHadamardSemantics

end Shor
