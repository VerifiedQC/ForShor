import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.OrderFinding
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.NaiveShor.Correctness
import FastMultiplication.ShorVerification.Implementation.Compilation.Correctness
import FastMultiplication.ShorVerification.Implementation.Semantics.Measurement
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Static
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Dynamic
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Setup
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.ModExp
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.ModExp
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Config
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Validity
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Precision
import FastMultiplication.ShorVerification.Framework.Submission
import FastMultiplication.ShorVerification.Framework.Math.ShorDefinition
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Shor/order-finding circuit statement

This file keeps the quantum-facing part of the Shor statement: the ideal and
approximate order-finding circuits, the measurement interface, and the final
success-probability theorem.  Classical order and continued-fraction material
lives in `MathBackbone/ShorAlgorithm.lean`.
-/
namespace Shor
open Gate
open Classical

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]

/-! =========================================================
    Probability-transfer lemmas

    These lemmas are the bridge from state-vector approximation to
    success-probability approximation.  The first group is pure real/probability
    bookkeeping; the second group uses gate isometry to move distance bounds
    through common circuit context.
========================================================= -/

/-- If two probabilities differ by at most `ε`, then the first is at least
    the second minus `ε`.

    This is the Lean version of:

        |A - B| ≤ ε  ⇒  A ≥ B - ε.
-/
lemma lower_bound_of_abs_sub_le {A B ε : ℝ}
    (h : |A - B| ≤ ε) :
    A ≥ B - ε := by
  have hleft : -ε ≤ A - B := (abs_le.mp h).1
  linarith

/-- If the approximate and ideal success probabilities differ by at most `ε`,
    and the ideal success probability is at least `L`, then the approximate
    success probability is at least `L - ε`. -/
lemma transfer_lower_bound_from_abs_prob
    {Papprox Pideal L ε : ℝ}
    (hprob : |Papprox - Pideal| ≤ ε)
    (hideal : Pideal ≥ L) :
    Papprox ≥ L - ε := by
  have hlow : Papprox ≥ Pideal - ε :=
    lower_bound_of_abs_sub_le hprob
  linarith

/-- Applying a common suffix gate preserves a state-distance bound. -/
lemma dist_eval_common_suffix_le
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (W A I : Gate)
    (ψ : qs.State)
    {ε : ℝ}
    (h : ‖qs.eval A ψ - qs.eval I ψ‖ ≤ ε) :
    ‖qs.eval W (qs.eval A ψ) - qs.eval W (qs.eval I ψ)‖ ≤ ε := by
  calc
    ‖qs.eval W (qs.eval A ψ) - qs.eval W (qs.eval I ψ)‖
        = ‖qs.eval A ψ - qs.eval I ψ‖ := by
            simpa using
              (eval_isometry qs W
                (by
                  intro ψ φ
                  simpa using qs.inner_preserved W ψ φ)
                (qs.eval A ψ)
                (qs.eval I ψ))
    _ ≤ ε := h

omit [MeasureClass qs] in
/-- Convert a state-distance bound between two complete circuits into a lower
bound on the approximate circuit's postprocessed success probability. -/
lemma probability_of_success_eval_dist [MeasureClass qs]
  [GateSemanticsCore qs]
  (T : ℕ → ℕ)
  (verify : ℕ → Bool)
  (x : Reg)
  (r Q : ℕ)
  (Gapprox Gideal : Gate)
  (ψ : qs.State)
  (ε : ℝ)
  (hψ : ‖ψ‖ = 1)
  (hdist :
    ‖qs.eval Gapprox ψ - qs.eval Gideal ψ‖ ≤ ε) :
  probability_of_success (qs := qs) (T := T)
      (verify := verify)
      (x := x) (r := r) (Q := Q)
      (evalC := qs.eval)
      (C := Gapprox)
      (ψ := ψ)
    ≥
  probability_of_success (qs := qs) (T := T)
      (verify := verify)
      (x := x) (r := r) (Q := Q)
      (evalC := qs.eval)
      (C := Gideal)
      (ψ := ψ)
    - 2 * ε := by
  let ψA : qs.State := qs.eval Gapprox ψ
  let ψI : qs.State := qs.eval Gideal ψ

  have hψA : ‖ψA‖ = 1 := by
    dsimp [ψA]
    simpa [hψ] using
      (eval_norm_preserved (qs := qs) Gapprox ψ)

  have hψI : ‖ψI‖ = 1 := by
    dsimp [ψI]
    simpa [hψ] using
      (eval_norm_preserved (qs := qs) Gideal ψ)

  let w : Fin Q → ℝ :=
    fun o => r_found (T := T) verify o.1 Q r

  have hw : ∀ o, 0 ≤ w o ∧ w o ≤ 1 := by
    intro o
    dsimp [w, r_found]
    by_cases h : OF_post (T := T) verify o.1 Q = r
    · simp [h]
    · simp [h]

  have hprob_dist :
      |probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x) (r := r) (Q := Q)
          (evalC := qs.eval)
          (C := Gapprox)
          (ψ := ψ)
        -
        probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x) (r := r) (Q := Q)
          (evalC := qs.eval)
          (C := Gideal)
          (ψ := ψ)|
      ≤ 2 * ‖qs.eval Gapprox ψ - qs.eval Gideal ψ‖ := by
    have hmain :=
      probMeas_weighted_dist
        (qs := qs)
        x Q w ψA ψI hw hψA hψI

    simpa [probability_of_success, MeasureClass.probMeas, ψA, ψI, w] using hmain

  have hprob :
      |probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x) (r := r) (Q := Q)
          (evalC := qs.eval)
          (C := Gapprox)
          (ψ := ψ)
        -
        probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x) (r := r) (Q := Q)
          (evalC := qs.eval)
          (C := Gideal)
          (ψ := ψ)|
      ≤ 2 * ε := by
    exact le_trans hprob_dist
      (mul_le_mul_of_nonneg_left hdist (by norm_num))

  exact lower_bound_of_abs_sub_le hprob

/-! =========================================================
    Final correctness statements

    The ideal theorem lives in `Proofs.NaiveShor.Correctness`.  This file imports that
    bound and transfers it across the modular-exponentiation implementation
    error to obtain the approximate order-finding statement.
========================================================= -/

lemma initY1_eq_X_lowQubit
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
After Shor's Hadamards on `x.active` and initialization of `y.active` to `1`,
the state is a valid input for modular exponentiation.

This uses only the clean computational-basis input, the list-based modular-
exponentiation layout, the `H_reg` expansion/locality theorem, and the
semantics of `Gate.X`.
-/
lemma ShorApproxSetup.prepared_state_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    {a N : ℕ}
    {x y work scratch : ExtReg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (ha : 0 < a ∧ a < N)
    (hxpos : 0 < regSize x.active)
    (hn : regSize y.active = Nat.log2 (2 * N))
    (hsetup : ShorApproxSetup qs η N x y work scratch flag b0) :
    qs.eval (initY1 y.active)
        (qs.eval (H_reg x.active) (qs.ket b0))
      ∈ ValidAlgorithm1State qs N y work scratch flag := by
  classical
  rcases hsetup.clean_input with
    ⟨hx0, hy0, hyFresh, hwork0, hworkFresh,
      hscratch0, hscratchFresh, hflag0⟩

  have hN : 1 < N := by
    omega

  have hypos : 0 < regSize y.active := by
    have harg_ne : 2 * N ≠ 0 := by omega
    have hle_log : 1 ≤ Nat.log2 (2 * N) := by
      rw [Nat.le_log2 harg_ne]
      have hN_ge_two : 2 ≤ N := by omega
      omega
    rw [hn]
    omega

  have hy_one_lt : 1 < ASize y.active := by
    have : regSize y.active ≠ 0 := Nat.ne_of_gt hypos
    simpa [ASize] using this

  have hcore0 : ModMulCoreLayout y work flag (x.active.get ⟨0, hxpos⟩) :=
    hsetup.register_layout ⟨0, hxpos⟩

  rcases hcore0 with
    ⟨hy_work_owned, hflag_y_owned, _hflag_work_owned,
      _hctrl_y0, _hctrl_work0, _hctrl_flag0⟩

  have hy_x : Disjoint y.active x.active :=
    Disjoint.symm
      (ExtReg.activeDisjoint_of_ownedDisjoint hsetup.exponent_data_disjoint)

  have hyNew_x : Disjoint (y.newBits 2) x.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqNew hqx
    exact hsetup.exponent_data_disjoint
      (List.mem_append_left _ hqx)
      (List.mem_append_right _ (List.mem_of_mem_take hqNew))

  have hworkOwned_x : work.ownedQubits.Disjoint x.active.qubits := by
    rw [List.disjoint_left]
    intro q hqw hqx
    rcases List.get_of_mem hqx with ⟨j, hj⟩
    let i : Fin (regSize x.active) :=
      ⟨j.1, by simp [regSize, Reg.width]⟩
    have hget : x.active.get i = q := by
      dsimp [i, Reg.get]
      simpa [Reg.width] using hj
    have hcore := hsetup.register_layout i
    rcases hcore with ⟨_, _, _, _, hctrl_work, _⟩
    exact hctrl_work (by simpa [hget] using hqw)

  have hwork_x : Disjoint work.active x.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqw hqx
    exact hworkOwned_x (List.mem_append_left _ hqw) hqx

  have hworkNew_x : Disjoint (work.newBits 1) x.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqNew hqx
    exact hworkOwned_x
      (List.mem_append_right _ (List.mem_of_mem_take hqNew))
      hqx

  have hscratchOwned_x : scratch.ownedQubits.Disjoint x.active.qubits := by
    rw [List.disjoint_left]
    intro q hqs hqx
    exact hsetup.exponent_scratch_disjoint
      (List.mem_append_left _ hqx)
      hqs

  have hscratch_x : Disjoint scratch.active x.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqs hqx
    exact hscratchOwned_x (List.mem_append_left _ hqs) hqx

  have hscratchNew_x : Disjoint (scratch.newBits 1) x.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqNew hqx
    exact hscratchOwned_x
      (List.mem_append_right _ (List.mem_of_mem_take hqNew))
      hqx

  have hflag_x : Disjoint (qubitReg flag) x.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqFlag hqx
    have hq : q = flag := by
      simpa [qubitReg, Reg.singleton] using hqFlag
    subst q
    rcases List.get_of_mem hqx with ⟨j, hj⟩
    let i : Fin (regSize x.active) :=
      ⟨j.1, by simp [regSize, Reg.width]⟩
    have hget : x.active.get i = flag := by
      dsimp [i, Reg.get]
      simpa [Reg.width] using hj
    have hcore := hsetup.register_layout i
    rcases hcore with ⟨_, _, _, _, _, hctrl_flag⟩
    exact hctrl_flag hget

  have hwork_y : Disjoint work.active y.active :=
    Disjoint.symm (ExtReg.activeDisjoint_of_ownedDisjoint hy_work_owned)

  have hworkNew_y : Disjoint (work.newBits 1) y.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqNew hqy
    exact hy_work_owned
      (List.mem_append_left _ hqy)
      (List.mem_append_right _ (List.mem_of_mem_take hqNew))

  have hflag_y : Disjoint (qubitReg flag) y.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqFlag hqy
    have hq : q = flag := by
      simpa [qubitReg, Reg.singleton] using hqFlag
    subst q
    exact hflag_y_owned (List.mem_append_left _ hqy)

  have hyScratchOwned : ExtReg.OwnedDisjoint y scratch := by
    simpa [ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow] using
      hsetup.step4_workspace.data_scratch_disjoint

  have hscratch_y : Disjoint scratch.active y.active :=
    Disjoint.symm
      (ExtReg.activeDisjoint_of_ownedDisjoint hyScratchOwned)

  have hscratchNew_y : Disjoint (scratch.newBits 1) y.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqNew hqy
    exact hyScratchOwned
      (List.mem_append_left _ hqy)
      (List.mem_append_right _ (List.mem_of_mem_take hqNew))

  let validSet : Set qs.State :=
    { ψ : qs.State |
      ∃ b : qs.Basis,
        GoodAlgorithm1BasisInput qs N y work scratch flag b ∧
        ψ = qs.ket b }

  have hH_expansion :
      ∃ β : Fin (ASize x.active) → ℂ,
        qs.eval (H_reg x.active) (qs.ket b0)
          =
        ∑ t : Fin (ASize x.active),
          β t • qs.ket (RegEncoding.writeNat x.active t.1 b0) := by
    rcases RegisterHadamardSemantics.eval_Hreg_ket
        (qs := qs) x.active b0 with ⟨β, hβ⟩
    refine ⟨β, ?_⟩
    simpa [H_reg] using hβ

  rcases hH_expansion with ⟨β, hβ⟩

  change
    qs.eval (initY1 y.active)
        (qs.eval (H_reg x.active) (qs.ket b0))
      ∈ Submodule.span ℂ validSet

  rw [hβ]
  have hsum_eval :
      qs.eval (initY1 y.active)
          (∑ t : Fin (ASize x.active),
            β t • qs.ket (RegEncoding.writeNat x.active t.1 b0))
        =
      ∑ t : Fin (ASize x.active),
        qs.eval (initY1 y.active)
          (β t • qs.ket (RegEncoding.writeNat x.active t.1 b0)) := by
    simpa using
      eval_finset_sum
        qs
        (initY1 y.active)
        Finset.univ
        (fun t : Fin (ASize x.active) =>
          β t • qs.ket (RegEncoding.writeNat x.active t.1 b0))
  rw [hsum_eval]

  apply Submodule.sum_mem
  intro t _ht
  rw [qs.eval_smul]
  apply (Submodule.span ℂ validSet).smul_mem

  let b : qs.Basis := RegEncoding.writeNat x.active t.1 b0

  have hy_b : RegEncoding.toNat y.active b = 0 := by
    calc
      RegEncoding.toNat y.active b
          = RegEncoding.toNat y.active b0 := by
            simpa [b] using
              RegEncoding.toNat_left_write_right y.active x.active hy_x b0 t.1
      _ = 0 := hy0

  have hyFresh_b : y.FreshFor 2 b := by
    unfold ExtReg.FreshFor FreshZero at hyFresh ⊢
    calc
      RegEncoding.toNat (y.newBits 2) b
          = RegEncoding.toNat (y.newBits 2) b0 := by
            simpa [b] using
              RegEncoding.toNat_left_write_right
                (y.newBits 2) x.active hyNew_x b0 t.1
      _ = 0 := hyFresh

  have hwork_b : RegEncoding.toNat work.active b = 0 := by
    calc
      RegEncoding.toNat work.active b
          = RegEncoding.toNat work.active b0 := by
            simpa [b] using
              RegEncoding.toNat_left_write_right
                work.active x.active hwork_x b0 t.1
      _ = 0 := hwork0

  have hworkFresh_b : work.FreshFor 1 b := by
    unfold ExtReg.FreshFor FreshZero at hworkFresh ⊢
    calc
      RegEncoding.toNat (work.newBits 1) b
          = RegEncoding.toNat (work.newBits 1) b0 := by
            simpa [b] using
              RegEncoding.toNat_left_write_right
                (work.newBits 1) x.active hworkNew_x b0 t.1
      _ = 0 := hworkFresh

  have hscratch_b : RegEncoding.toNat scratch.active b = 0 := by
    calc
      RegEncoding.toNat scratch.active b
          = RegEncoding.toNat scratch.active b0 := by
            simpa [b] using
              RegEncoding.toNat_left_write_right
                scratch.active x.active hscratch_x b0 t.1
      _ = 0 := hscratch0

  have hscratchFresh_b : scratch.FreshFor 1 b := by
    unfold ExtReg.FreshFor FreshZero at hscratchFresh ⊢
    calc
      RegEncoding.toNat (scratch.newBits 1) b
          = RegEncoding.toNat (scratch.newBits 1) b0 := by
            simpa [b] using
              RegEncoding.toNat_left_write_right
                (scratch.newBits 1) x.active hscratchNew_x b0 t.1
      _ = 0 := hscratchFresh

  have hflag_b :
      RegEncoding.toNat (qubitReg flag) b = 0 := by
    calc
      RegEncoding.toNat (qubitReg flag) b
          = RegEncoding.toNat (qubitReg flag) b0 := by
            simpa [b] using
              RegEncoding.toNat_left_write_right
                (qubitReg flag) x.active hflag_x b0 t.1
      _ = 0 := hflag0

  have hinit :
      qs.eval (initY1 y.active) (qs.ket b)
        =
      qs.ket (RegEncoding.writeNat y.active 1 b) := by
    rw [initY1_eq_X_lowQubit y.active hypos]
    exact
      PauliXSemantics.eval_X_low_zero_reg_ket
        (qs := qs) y.active b hypos hy_b

  rw [hinit]
  apply Submodule.subset_span
  refine ⟨RegEncoding.writeNat y.active 1 b, ?_, rfl⟩

  have hdata_lt :
      RegEncoding.toNat y.active
          (RegEncoding.writeNat y.active 1 b) < N := by
    calc
      RegEncoding.toNat y.active
          (RegEncoding.writeNat y.active 1 b) = 1 :=
            RegEncoding.toNat_writeNat_of_lt y.active 1 b hy_one_lt
      _ < N := hN

  have hyFreshOut :
      y.FreshFor 2 (RegEncoding.writeNat y.active 1 b) :=
    ExtReg.freshFor_write_active y 2 1 b hyFresh_b

  have hworkZeroOut :
      RegEncoding.toNat work.active
          (RegEncoding.writeNat y.active 1 b) = 0 := by
    calc
      RegEncoding.toNat work.active
          (RegEncoding.writeNat y.active 1 b)
          = RegEncoding.toNat work.active b := by
            exact RegEncoding.toNat_left_write_right
              work.active y.active hwork_y b 1
      _ = 0 := hwork_b

  have hworkFreshOut :
      work.FreshFor 1 (RegEncoding.writeNat y.active 1 b) := by
    unfold ExtReg.FreshFor FreshZero at hworkFresh_b ⊢
    calc
      RegEncoding.toNat (work.newBits 1)
          (RegEncoding.writeNat y.active 1 b)
          = RegEncoding.toNat (work.newBits 1) b := by
            exact RegEncoding.toNat_left_write_right
              (work.newBits 1) y.active hworkNew_y b 1
      _ = 0 := hworkFresh_b

  have hflagZeroOut :
      RegEncoding.toNat (qubitReg flag)
          (RegEncoding.writeNat y.active 1 b) = 0 := by
    calc
      RegEncoding.toNat (qubitReg flag)
          (RegEncoding.writeNat y.active 1 b)
          = RegEncoding.toNat (qubitReg flag) b := by
            exact RegEncoding.toNat_left_write_right
              (qubitReg flag) y.active hflag_y b 1
      _ = 0 := hflag_b

  have hscratchZeroOut :
      RegEncoding.toNat scratch.active
          (RegEncoding.writeNat y.active 1 b) = 0 := by
    calc
      RegEncoding.toNat scratch.active
          (RegEncoding.writeNat y.active 1 b)
          = RegEncoding.toNat scratch.active b := by
            exact RegEncoding.toNat_left_write_right
              scratch.active y.active hscratch_y b 1
      _ = 0 := hscratch_b

  have hscratchFreshOut :
      scratch.FreshFor 1 (RegEncoding.writeNat y.active 1 b) := by
    unfold ExtReg.FreshFor FreshZero at hscratchFresh_b ⊢
    calc
      RegEncoding.toNat (scratch.newBits 1)
          (RegEncoding.writeNat y.active 1 b)
          = RegEncoding.toNat (scratch.newBits 1) b := by
            exact RegEncoding.toNat_left_write_right
              (scratch.newBits 1) y.active hscratchNew_y b 1
      _ = 0 := hscratchFresh_b

  exact
    ⟨⟨hdata_lt, hyFreshOut, hworkZeroOut, hworkFreshOut, hflagZeroOut⟩,
      hscratchZeroOut, hscratchFreshOut⟩

lemma shor_data_capacity_from_log2
    (N : ℕ) :
    N ≤ 2 ^ Nat.log2 (2 * N) := by
  rcases N with _ | N
  · simp
  · have hlt :
        2 * (N + 1) < 2 ^ (Nat.log 2 (2 * (N + 1))).succ := by
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two (2 * (N + 1))
    rw [← Nat.log2_eq_log_two] at hlt
    rw [Nat.pow_succ] at hlt
    have hdouble_le :
        (N + 1) * 2 ≤ 2 ^ Nat.log2 (2 * (N + 1)) * 2 := by
      simpa [Nat.mul_comm] using hlt.le
    exact Nat.le_of_mul_le_mul_right hdouble_le (by norm_num : 0 < 2)

def ShorApproxSetup.toModExpConfig
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {a N : ℕ}
    {y : ExtReg}
    {η : ℝ}
    {x work scratch : ExtReg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (ha : 0 < a ∧ a < N)
    (hgcd : Nat.gcd a N = 1)
    (hn : regSize y.active = Nat.log2 (2 * N))
    (hsetup : ShorApproxSetup qs η N x y work scratch flag b0) :
    ModExpConfig η := by
  have hN : 1 < N := by
    omega
  have hcapacity : N ≤ ASize y.active := by
    simpa [ASize, hn] using shor_data_capacity_from_log2 N
  have hcoprime : Nat.Coprime a N := by
    rw [Nat.coprime_iff_gcd_eq_one]
    exact hgcd
  refine
    { env :=
        { N := N
          data := y
          work := work
          scratch := scratch
          modulus_gt_one := hN
          data_capacity := hcapacity
          precision := hsetup.work_precision
          circuit_workspace := hsetup.circuit_workspace
           }
      a := a
      x := x.active
      flag := flag
      layout := hsetup.register_layout
      arithmetic := ?_
      step4_workspace := hsetup.step4_workspace }
  intro i
  exact modExp_multiplier_coprime a N i.1 hcoprime

theorem Shor_correct_approx_uniform_of_modExp_bound
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (K : ℝ)
    (hmodExp :
      ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State),
        ModExpConfig.ValidUnitState qs cfg ψ →
        ‖qs.eval (ModExpConfig.approxGate cfg) ψ -
            qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
          ≤ (tbits cfg.x : ℝ) * stepErr K η)
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    ∀ (inst : ShorOrderFindingInstance)
      (x y w scratch : ExtReg) (flag : ℕ)
      (b0 : qs.Basis)
      (_hm : regSize x.active = Nat.log2 (2 * inst.N^2))
      (_hn : regSize y.active = Nat.log2 (2 * inst.N))
      (η : ℝ)
      (hsetup : ShorApproxSetup qs η inst.N x y w scratch flag b0),
      probability_of_success
          (qs := qs) (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := x.active)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize x.active)
          (evalC := qs.eval)
          (C := orderFindingApprox inst.a inst.N x y w scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace)
          (ψ := qs.ket b0)
        ≥
      κ / (Nat.log2 inst.N : ℝ)^4 -
        2 * (tbits x.active : ℝ) * Real.sqrt (2 * (K * η)) := by
  intro inst x y w scratch flag b0 hm hn η hsetup
  let a := inst.a
  let N := inst.N
  have ha : 0 < a ∧ a < N := inst.range
  have hgcd : Nat.gcd a N = 1 := inst.coprime
  let cfg : ModExpConfig η := ShorApproxSetup.toModExpConfig ha hgcd hn hsetup

  let ψpre : qs.State :=
    qs.eval (initY1 y.active) (qs.eval (H_reg x.active) (qs.ket b0))

  have hxpos : 0 < regSize x.active := by
    have harg_ne : 2 * N ^ 2 ≠ 0 := by
      have hNpos : 0 < N := by
        omega
      positivity

    have hle_log : 1 ≤ Nat.log2 (2 * N ^ 2) := by
      rw [Nat.le_log2 harg_ne]
      have hNsq_pos : 0 < N ^ 2 := by
        have hNpos : 0 < N := by
          omega
        positivity
      exact Nat.mul_le_mul_left 2 hNsq_pos

    rw [hm]; unfold N at *
    omega

  have hpreValid :
      ψpre ∈ ValidAlgorithm1State qs N y w scratch flag := by
    simpa [ψpre] using
      (ShorApproxSetup.prepared_state_valid
        (qs := qs)
        ha
        hxpos
        hn
        hsetup)

  have hpreUnit : ‖ψpre‖ = 1 := by
    dsimp [ψpre]
    calc
      ‖qs.eval (initY1 y.active) (qs.eval (H_reg x.active) (qs.ket b0))‖
          =
          ‖qs.eval (H_reg x.active) (qs.ket b0)‖ := by
            simpa using
              (eval_norm_preserved qs
                (initY1 y.active)
                (qs.eval (H_reg x.active) (qs.ket b0)))
      _ = ‖qs.ket b0‖ := by
            simpa using
              (eval_norm_preserved qs (H_reg x.active) (qs.ket b0))
      _ = 1 := ket_norm_one qs b0

  have hpre :
      ModExpConfig.ValidUnitState qs cfg ψpre := by
    simpa [
      ModExpConfig.ValidUnitState,
      cfg,
      ShorApproxSetup.toModExpConfig
    ] using
      (And.intro hpreValid hpreUnit)

  let ε : ℝ := (tbits x.active : ℝ) * stepErr K η

  have hmid :
      ‖qs.eval
          (modExpApproxValid
            a N x.active y w scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace)
          ψpre
        -
        qs.eval (modExpIdeal' (qs := qs) a N x.active y.active) ψpre‖
      ≤ ε := by
    simpa [
      ε,
      cfg,
      ShorApproxSetup.toModExpConfig,
      ModExpConfig.approxGate,
      ModExpConfig.idealGate
    ] using
      (hmodExp η cfg ψpre hpre)

  have hpost :
      ‖qs.eval (IQFT x)
          (qs.eval
            (modExpApproxValid
              a N x.active y w scratch flag
              hsetup.circuit_workspace hsetup.step4_workspace)
            ψpre)
        -
        qs.eval (IQFT x)
          (qs.eval (modExpIdeal' (qs := qs) a N x.active y.active) ψpre)‖
      ≤ ε := by
    exact dist_eval_common_suffix_le
      (qs := qs)
      (IQFT x)
      (modExpApproxValid
        a N x.active y w scratch flag
        hsetup.circuit_workspace hsetup.step4_workspace)
      (modExpIdeal' (qs := qs) a N x.active y.active)
      ψpre
      hmid

  have hdist_full :
      ‖qs.eval
          (orderFindingApprox a N x y w scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace)
          (qs.ket b0)
        -
        qs.eval
          (orderFindingIdeal (qs := qs) a N x y)
          (qs.ket b0)‖
      ≤ ε := by
    simpa [
      orderFindingApprox,
      orderFindingIdeal,
      ψpre,
      qs.eval_seq
    ] using hpost

  let verify : ℕ → Bool :=
    fun d => decide ((a ^ d) % N = 1)

  let r : ℕ := ord a N hgcd
  let Q : ℕ := ASize x.active

  have htransfer :
      probability_of_success (qs := qs) (T := T)
        (verify := verify)
        (x := x.active) (r := r) (Q := Q)
        (evalC := qs.eval)
        (C := orderFindingApprox a N x y w scratch flag
          hsetup.circuit_workspace hsetup.step4_workspace)
        (ψ := qs.ket b0)
      ≥
      probability_of_success (qs := qs) (T := T)
        (verify := verify)
        (x := x.active) (r := r) (Q := Q)
        (evalC := qs.eval)
        (C := orderFindingIdeal (qs := qs) a N x y)
        (ψ := qs.ket b0)
      - 2 * ε := by
    exact probability_of_success_eval_dist
      (qs := qs)
      T
      verify
      x.active
      r
      Q
      (orderFindingApprox a N x y w scratch flag
        hsetup.circuit_workspace hsetup.step4_workspace)
      (orderFindingIdeal (qs := qs) a N x y)
      (qs.ket b0)
      ε
      (ket_norm_one qs b0)
      hdist_full

  have hIdealInput :
      IdealOrderFindingInput qs x y b0 :=
    hsetup.toIdealOrderFindingInput

  have hideal :
      probability_of_success (qs := qs) (T := T)
        (verify := verify)
        (x := x.active) (r := r) (Q := Q)
        (evalC := qs.eval)
        (C := orderFindingIdeal (qs := qs) a N x y)
        (ψ := qs.ket b0)
      ≥ κ / (Nat.log2 N : ℝ)^4 := by
    simpa [verify, r, Q, a, N] using
      (Shor_correct (qs := qs) T hT inst x y b0 hm hn hIdealInput)

  calc
    probability_of_success (qs := qs) (T := T)
        (verify := fun d => decide ((a ^ d) % N = 1))
        (x := x.active)
        (r := ord a N hgcd)
        (Q := ASize x.active)
        (evalC := qs.eval)
        (C := orderFindingApprox a N x y w scratch flag
          hsetup.circuit_workspace hsetup.step4_workspace)
        (ψ := qs.ket b0)
      ≥
        probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x.active)
          (r := r)
          (Q := Q)
          (evalC := qs.eval)
          (C := orderFindingIdeal (qs := qs) a N x y)
          (ψ := qs.ket b0)
        - 2 * ε := by
          simpa [verify, r, Q] using htransfer
    _ ≥
        κ / (Nat.log2 N : ℝ)^4 - 2 * ε := by
          exact sub_le_sub_right hideal (2 * ε)
    _ =
        κ / (Nat.log2 N : ℝ)^4
          - 2 * (tbits x.active : ℝ) *
              Real.sqrt (2 * (K * η)) := by
          simp [ε, stepErr, mul_assoc]
/--
Uniform approximate Shor order-finding bound.

`K` is chosen before `η`, so it is independent of the precision parameter.
It may depend on the fixed instance data `qs`, `T`, `a`, `N`, `x`, `y`,
`w`, `flag`, `b0`, and the fixed size/arithmetic hypotheses.
-/
theorem Shor_correct_approx_uniform
    [GateSemanticsFacts qs] [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (inst : ShorOrderFindingInstance)
      (x y w scratch : ExtReg) (flag : ℕ)
      (b0 : qs.Basis)
      (_hm: regSize x.active = Nat.log2 (2 * inst.N^2))
      (_hn : regSize y.active = Nat.log2 (2 * inst.N))
      (η : ℝ)
      (hsetup : ShorApproxSetup qs η inst.N x y w scratch flag b0),
      probability_of_success (qs := qs) (T := T) (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active) (r := ord inst.a inst.N inst.coprime) (Q := ASize x.active)
        (evalC := qs.eval)
        (C := orderFindingApprox inst.a inst.N x y w scratch flag
          hsetup.circuit_workspace hsetup.step4_workspace)
        (ψ := qs.ket b0)
      ≥
        κ / (Nat.log2 inst.N : ℝ)^4
        - 2 * (tbits x.active : ℝ) * Real.sqrt (2 * (K * η)) := by
  obtain ⟨K, hK, _hK_le, hmodExp⟩ := modExpApprox_valid_dist_uniform (qs := qs)
  refine ⟨K, hK, ?_⟩
  exact Shor_correct_approx_uniform_of_modExp_bound
    (qs := qs) K hmodExp T hT

/-
Lowering preserves the success probability exactly when the current
whole-program lowering workspace and dynamic cleanliness hypotheses are
available.
-/
lemma probability_of_success_lowerGate_eq
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ) (hk : 1 < k)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe
      (k := k) (by omega)
      State.start_state ops
      (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state)
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    (x : Reg)
    (r Q : ℕ)
    (G : Gate)
    (hworkspace : GateWorkspaceOK ops G)
    (ψ : qs.State)
    (hclean : GateWorkspaceCleanState qs k hk ops G hworkspace ψ) :
    probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs))
        (T := T) (verify := verify) (x := x) (r := r) (Q := Q)
        (C := lowerGate k hk ops G hworkspace) (ψ := ψ)
      =
    probability_of_success (qs := qs) (evalC := qs.eval)
        (T := T) (verify := verify) (x := x) (r := r) (Q := Q)
        (C := G) (ψ := ψ) := by
  have hEval :
      LowerGateClass.evalL
          (qs := qs)
          (lowerGate k hk ops G hworkspace)
          ψ
        =
      qs.eval G ψ :=
    lowerGate_correctness
      qs
      k
      hk
      ops
      hC
      hRun
      G
      hworkspace
      ψ
      hclean

  unfold probability_of_success MeasureClass.probMeas
  apply Finset.sum_congr rfl
  intro o ho
  rw [hEval]

/--
Whole-program lowering introduces no additional success-probability error.

This compares the low-level lowering of `orderFindingApprox` with the same
high-level approximate circuit. It does not compare the approximate circuit
with `orderFindingIdeal`.
-/
theorem orderFindingApproxLow_probability_eq
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    (a N : ℕ)
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (hmodWorkspace : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hLowerWorkspace : GateWorkspaceOK lowering.ops
      (orderFindingApprox a N x y work scratch flag hmodWorkspace hstep4))
    (ψ : qs.State)
    (hclean : GateWorkspaceCleanState qs lowering.k lowering.hk lowering.ops
        (orderFindingApprox a N x y work scratch flag hmodWorkspace hstep4)
        hLowerWorkspace ψ)
    (r Q : ℕ) :
    probability_of_success
        (qs := qs)  (evalC := LowerGateClass.evalL (qs := qs))
        (T := T) (verify := verify) (x := x.active) (r := r)
        (Q := Q)
        (C := orderFindingApproxLow
            lowering.k lowering.hk lowering.ops a N x y work scratch flag
            hmodWorkspace hstep4 hLowerWorkspace)
        (ψ := ψ)
      =
    probability_of_success
        (qs := qs) (evalC := qs.eval)
        (T := T) (verify := verify) (x := x.active) (r := r)
        (Q := Q)
        (C := orderFindingApprox a N x y work scratch flag
          hmodWorkspace hstep4)
        (ψ := ψ) := by
  simpa only [orderFindingApproxLow] using
    (probability_of_success_lowerGate_eq
      (qs := qs)
      (k := lowering.k)
      (hk := lowering.hk)
      (ops := lowering.ops)
      (hC := lowering.consumes)
      (hRun := lowering.returns)
      (T := T)
      (verify := verify)
      (x := x.active)
      (r := r)
      (Q := Q)
      (G :=
        orderFindingApprox a N x y work scratch flag hmodWorkspace hstep4)
      (hworkspace := hLowerWorkspace)
      (ψ := ψ)
      (hclean := hclean))

theorem Shor_correct_approx_lowered_of_modExp_bound
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [IdealCtrlModMulExactSemantics qs]
    (K : ℝ)
    (hmodExp :
      ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State),
        ModExpConfig.ValidUnitState qs cfg ψ →
        ‖qs.eval (ModExpConfig.approxGate cfg) ψ -
            qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
          ≤ (tbits cfg.x : ℝ) * stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    (lowering : ShorLoweringSetup)
    (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N^2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N))
    (η : ℝ)
    (hready : LoweredShorReady
      qs lowering η inst.a inst.N x y work scratch flag b0) :
    probability_of_success
        (qs := qs) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)
        (evalC := LowerGateClass.evalL (qs := qs))
        (C := orderFindingApproxLow lowering.k lowering.hk lowering.ops
          inst.a inst.N x y work scratch flag
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace
          hready.workspace)
        (ψ := qs.ket b0)
      ≥
    κ / (Nat.log2 inst.N : ℝ)^4 -
      2 * (tbits x.active : ℝ) * Real.sqrt (2 * (K * η)) := by
  calc
    probability_of_success
        (qs := qs) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)
        (evalC := LowerGateClass.evalL (qs := qs))
        (C := orderFindingApproxLow lowering.k lowering.hk lowering.ops
          inst.a inst.N x y work scratch flag
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace
          hready.workspace)
        (ψ := qs.ket b0)
      =
    probability_of_success
        (qs := qs) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)
        (evalC := qs.eval)
        (C := orderFindingApprox inst.a inst.N x y work scratch flag
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace)
        (ψ := qs.ket b0) := by
      exact orderFindingApproxLow_probability_eq
        (qs := qs)
        (lowering := lowering)
        (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (a := inst.a) (N := inst.N)
        (x := x) (y := y) (work := work) (scratch := scratch) (flag := flag)
        (hmodWorkspace :=
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace)
        (hstep4 :=
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace)
        (hLowerWorkspace := hready.workspace)
        (ψ := qs.ket b0)
        (hclean := hready.workspace_clean)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)

    _ ≥ κ / (Nat.log2 inst.N : ℝ)^4 -
        2 * (tbits x.active : ℝ) * Real.sqrt (2 * (K * η)) := by
      exact Shor_correct_approx_uniform_of_modExp_bound
        (qs := qs) K hmodExp T hT
        inst x y work scratch flag b0 hm hn η
        (ShorApproxSetupMinimal.toShorApproxSetup hready.approx)
/-
A lowered approximate Shor theorem needs a repository bridge deriving the
whole-program lowering workspace and dynamic cleanliness facts for
`orderFindingApprox`.  The current lowerer exposes those hypotheses, but this
file does not yet contain the numerical allocation bridge from the Shor setup.
-/
