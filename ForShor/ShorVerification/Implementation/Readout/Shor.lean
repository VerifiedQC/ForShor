import ForShor.ShorVerification.Implementation.Readout.Proofs.ShorSetup
import ForShor.ShorVerification.Implementation.Readout.Proofs.ShorSuccess
import ForShor.ShorVerification.Implementation.Readout.Proofs.ApproxPhase
import ForShor.ShorVerification.Implementation.ModularExponentiation.Proofs.FinalModMul

/-!
# Readout: semiclassical order finding and its success probability

The full semiclassical order-finding circuit `orderFindingSemiclassical`
(`ShorStatement.lean`): `initY1` on the data register, then `m` rounds on ONE
recycled control qubit `c`, round `j` using the REAL controlled modular
multiplier `CmodMulInPlaceCore (a^(2^(m-1-j)) mod N) … (ctrl := c)` and the exact
feed-forward phase. Its success probability `probability_of_success_M` (the
record read as an integer `o`, post-processed by the same `r_found`) satisfies the
same bounds as the coherent approximate circuit `orderFindingApprox`:

* `Shor_correct_semiclassical_of_modMul_bound`: given a per-multiplier bound with
  constant `K` (the form of `modMul_approx_valid_dist_uniform`), success
  `≥ κ / log(log₂ N + 1) - 2 · m · √(2Kη)` with `m = regSize x.active`: the
  lower bound of `Shor_correct_approx_lowered_of_modExp_bound` at the same
  `Q = 2^m` and `η`.
* `Shor_correct_semiclassical`: the same with some `K ≤ 1600`, chosen before
  everything else (as in `ShorCorrectApproxLoweredUniform`).
* `Shor_correct_semiclassical_at_shorPrecision`: at every `η ≤ shorPrecision N x`
  success `≥ κ / (2 log(log₂ N + 1))`, the conclusion of
  `Shor_correct_approx_lowered_at_shorPrecision`.
* `Shor_correct_semiclassical_impl_of_modMul_bound` and
  `Shor_correct_semiclassical_impl_at_shorPrecision`: the same with every
  feed-forward phase replaced by an implemented rotation `R j r` within `ρ j` of
  the exact phase; the bounds lose `2 ∑_j ρ j` more. The Lean `ffPhase` is exact,
  so `ρ = 0` is the `MGate` statement; a synthesized (Ross-Selinger) rotation's
  error is budgeted outside Lean through `ρ`.
* `Shor_correct_semiclassical_impl_of_modMul_bound_up_to_phase` and
  `Shor_correct_semiclassical_impl_at_shorPrecision_up_to_phase`: the same with
  each `R j r` required to be `ρ j`-close to the exact phase only up to a global
  phase `exp(iα_{j,r})` (the form in which synthesis errors are stated), via
  `semiclassicalImpl_phaseEquiv` (global phases do not change record
  probabilities).

Proof (all inequalities, nothing assumed):
1. the `MGate` run from `|b0⟩` is the implemented readout from
   `|b1⟩ = initY1 |b0⟩` (data `= 1`) (`orderFindingSemiclassical_eval`);
2. implemented vs ideal semiclassical readout: `ℓ¹` distance of record
   distributions `≤ 2 ∑_j (stepErr K η + ρ j)` (`semiclassical_dist_le_sum_errors_finite`,
   hypotheses discharged in `Proofs/ShorSetup.lean`);
3. success(implemented) `≥` success(ideal semiclassical) `-` that `ℓ¹`
   distance, since `r_found ∈ {0,1}` (`probability_of_success_M_ge_sub`);
4. success(ideal semiclassical) `=` success of the textbook ideal circuit
   `orderFindingIdeal` (`semiclassical_eq_iqft` outcome by outcome, and
   `orderFindingIdeal_eval_start`);
5. that is `≥ κ / log(log₂ N + 1)` (`Shor_correct`);
6. at `η ≤ shorPrecision N x` the loss `2 · m · √(2 · 1600 · η)` is at most half
   of it (`lowering_loss_le_half`, the same arithmetic as the coherent theorem).

These are statements about the HIGH-LEVEL (`Gate`-level) circuit, like the
coherent `orderFindingApprox` theorems before lowering. The lowered statement
(`Policy.lowerGate` on the unitary parts, run by `MLowGate.eval`) is proved in
`Readout/LoweredShor.lean` (`Shor_correct_semiclassical_lowered_at_shorPrecision`), by the
lowering lemma of the measurement language (`Policy.lowerM_correct`) and the theorems here;
the balanced lowerings are in `Readout/BalancedShor.lean`.

The register `x` in the statements is a REFERENCE register only: the circuit
never touches it. It fixes `m = regSize x.active = log₂(2N²)` and lets step 4
compare with `orderFindingIdeal`; see `SemiclassicalShorSetup`.
-/

namespace Shor

open Readout

/-- **A control inside the data register is rejected.** If the control qubit
`c` is one of the data register's qubits (active or spare), no
`SemiclassicalLayout` exists for it. -/
theorem layout_collision_rejected (c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (h : c ∈ y.ownedQubits) : ¬ SemiclassicalLayout c y work scratch flag :=
  fun hl => hl.c_not_mem_data h

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis] [MeasureClass qs]
  [GateSemanticsFacts qs] [LowerGateClass qs]

/-- **Semiclassical order finding with implemented rotations, at a given
per-multiplier constant `K`.**

Hypotheses: `hmodMul`, every `CmodMulInPlaceCore` is within `stepErr K η` of the
ideal controlled multiplier on unit vectors of `ValidAlgorithm1State` (any
control qubit; this is what `modMul_approx_valid_dist_uniform` provides for some
`K ≤ 1600`); `T` makes the continued-fraction search complete; `inst = (a, N)`
an order-finding instance; `m = regSize x.active = log₂(2N²)` rounds,
`regSize y.active = log₂(2N)`; `hsetup`, the layout, workspaces, precision and
clean start of `SemiclassicalShorSetup` (control `c` outside the multiplier's
registers and `0`; `x` a reference register, `0`, disjoint from `y`); for every
round `j < m` and record `r` of length `j`, the implemented rotation `R j r` is
within `ρ j · ‖φ‖` of the exact feed-forward phase `Phase c (ffAngle j r)` on
every state `φ`, and does not increase norms.

Run: `initY1 y.active` on `|b0⟩`, then `semiclassicalImpl` (round `j`:
`H c`, the real multiplier by `a^(2^(m-1-j)) mod N` controlled by `c`, `R j r`,
`H c`, measure-and-reset `c`).

Conclusion: the probability that the record, read as `o` and post-processed by
`r_found`, returns the order of `a` mod `N` is at least
`κ / log(log₂ N + 1) - 2 ∑_{j<m} (stepErr K η + ρ j)`. -/
theorem Shor_correct_semiclassical_impl_of_modMul_bound (K : ℝ)
    (hmodMul : ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
      ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hR : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace)
          R (regSize x.active) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * ∑ j ∈ Finset.range (regSize x.active), (stepErr K η + ρ j) := by
  set m := regSize x.active with hmdef
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hN1 : 1 < inst.N := by omega
  have hNy : inst.N ≤ ASize y.active := by
    simpa [ASize, hn] using shor_data_capacity_from_log2 inst.N
  have ha : Nat.Coprime inst.a inst.N := Nat.coprime_iff_gcd_eq_one.2 inst.coprime
  have hy : 0 < regSize y.active := regSize_pos_of_log2 inst.N hN _ hn
  obtain ⟨hx0, hy0, -⟩ := hsetup.clean_input
  obtain ⟨hx1, hy1, hc1, -, hin, hnorm⟩ := semiclassical_start hsetup hN1 hNy
  have hc : c ∉ y.active.qubits := fun h =>
    hsetup.layout.c_not_mem_data (mem_owned_of_mem_active y c h)
  have hxy : Disjoint x.active y.active :=
    ExtReg.activeDisjoint_of_ownedDisjoint hsetup.reference_data_disjoint
  rw [eval_initY1_start y b0 hy hy0]
  set b1 := semiclassicalStartKet (qs := qs) y b0
  set verify : ℕ → Bool := fun d => decide ((inst.a ^ d) % inst.N = 1)
  set r := ord inst.a inst.N inst.coprime
  set u := semiclassicalImpl c (semiclassicalMultipliers inst.a inst.N c m y work scratch flag
      hsetup.circuit_workspace hsetup.step4_workspace) R m (MState.init (qs.ket b1))
  set v := (semiclassicalIdeal inst.a inst.N m y.active c).eval (MState.init (qs.ket b1))
  -- (2) ℓ¹ distance of the record distributions
  have hdist := semiclassical_dist_le_sum_errors_finite inst.a inst.N m y.active c
    (semiclassicalSide y work scratch flag) hN1 hNy ha hc
    (fun b w hb => semiclassicalSide_writeNat_ctrl hsetup.layout b w hb)
    (fun b w hb => semiclassicalSide_writeNat_data hsetup.circuit_workspace
      hsetup.step4_workspace b w hb)
    (qs.ket b1) hin hnorm _ R (fun _ => stepErr K η) ρ
    (fun j _ => semiclassicalMultiplier_dist_le K hmodMul hsetup hN1 hNy ha m j) hR hRc
  -- (3) success is stable under that distance
  have hstab := probability_of_success_M_ge_sub T verify m r (ASize x.active) rfl u v
  -- (4) the ideal semiclassical success is the textbook ideal success
  have hideal_eq : probability_of_success_M T verify m r (ASize x.active) v
      = probability_of_success (qs := qs) (T := T) (verify := verify) (x := x.active) (r := r)
          (Q := ASize x.active) (evalC := qs.eval) (C := orderFindingIdeal qs inst.a inst.N x y)
          (ψ := qs.ket b0) := by
    unfold probability_of_success_M probability_of_success
    rw [orderFindingIdeal_eval_start inst.a inst.N x y b0 hxy hy hx0 hy0]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [recordOutcomeProb, semiclassical_eq_iqft inst.a inst.N x y.active c b1 hN1 hNy ha hc hxy
      hx1 hy1 hc1 o.1]
  -- (5) the ideal bound
  have hideal := Shor_correct (qs := qs) T hT inst x y b0 hm hn
    ⟨hx0, hy0, hsetup.reference_data_disjoint⟩
  unfold ShorCorrect at hideal
  linarith

/-- **Semiclassical order finding (the `MGate`), at a given per-multiplier
constant `K`.** Same hypotheses as `Shor_correct_semiclassical_impl_of_modMul_bound`
without the rotations (the `MGate`'s feed-forward phases are exact). The success
probability of `orderFindingSemiclassical` run from `|b0⟩` is at least
`κ / log(log₂ N + 1) - 2 · m · √(2Kη)`, `m = regSize x.active`: the bound of
`Shor_correct_approx_lowered_of_modExp_bound` at the same `Q = 2^m` and `η`. -/
theorem Shor_correct_semiclassical_of_modMul_bound (K : ℝ)
    (hmodMul : ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
      ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        ((orderFindingSemiclassical inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace).eval (MState.init (qs.ket b0)))
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * (regSize x.active : ℝ) * Real.sqrt (2 * (K * η)) := by
  have hRc : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖exactPhase c j r φ‖ ≤ ‖φ‖ := fun j _ r _ φ => by
    simp only [exactPhase, lowL_apply]
    rw [norm_evalL_phase]
  have hR : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖exactPhase c j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖
        ≤ (fun _ => (0 : ℝ)) j * ‖φ‖ := fun j _ r _ φ => by
    simp [exactPhase]
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hy : 0 < regSize y.active := regSize_pos_of_log2 inst.N hN _ hn
  have h := Shor_correct_semiclassical_impl_of_modMul_bound K hmodMul T hT inst c x y work scratch
    flag b0 hm hn η hsetup (fun j => exactPhase c j) (fun _ => 0) hR hRc
  rw [eval_initY1_start y b0 hy hsetup.clean_input.2.1] at h
  rw [orderFindingSemiclassical_eval _ _ _ _ _ _ _ _ _ _ b0 hy hsetup.clean_input.2.1]
  have hsum : ∑ j ∈ Finset.range (regSize x.active), (stepErr K η + (fun _ => (0 : ℝ)) j)
      = (regSize x.active : ℝ) * Real.sqrt (2 * (K * η)) := by
    simp [stepErr]
  rw [hsum] at h
  linarith

-- `hm`, `hn` are binder names in the statement (read by the caller), not used by the proof term.
set_option linter.unusedVariables false in
/-- **Semiclassical order finding, uniform constant.** There is a constant
`0 ≤ K ≤ 1600`, chosen before the instance, the registers and the precision,
such that for every instance and every `SemiclassicalShorSetup` (with
`m = regSize x.active = log₂(2N²)`, `regSize y.active = log₂(2N)`) the success
probability of `orderFindingSemiclassical` is at least
`κ / log(log₂ N + 1) - 2 · m · √(2Kη)`. The semiclassical counterpart of
`ShorCorrectApproxLoweredUniform` (high-level circuit). -/
theorem Shor_correct_semiclassical (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ∃ K : ℝ, 0 ≤ K ∧ K ≤ 1600 ∧
      ∀ (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
        (b0 : qs.Basis)
        (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
        (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
        (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0),
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
            (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
            ((orderFindingSemiclassical inst.a inst.N c (regSize x.active) y work scratch flag
                hsetup.circuit_workspace hsetup.step4_workspace).eval (MState.init (qs.ket b0)))
          ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
            - 2 * (regSize x.active : ℝ) * Real.sqrt (2 * (K * η)) := by
  obtain ⟨K, hK0, hK, hmodMul⟩ := modMul_approx_valid_dist_uniform qs
  exact ⟨K, hK0, hK, fun inst c x y work scratch flag b0 hm hn η hsetup =>
    Shor_correct_semiclassical_of_modMul_bound K (hmodMul) T hT inst c x y work scratch flag b0
      hm hn η hsetup⟩

/-- The per-multiplier bound `modMul_approx_valid_dist_uniform` at the explicit
constant `1600` (`stepErr` is monotone in `K`, and `η > 0` on every
configuration). -/
theorem modMul_approx_valid_dist_1600 (qs : QSemantics) [RegEncoding qs.Basis]
    [GateSemanticsFacts qs] :
    ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State), ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr 1600 η := by
  obtain ⟨K, _, hK, h⟩ := modMul_approx_valid_dist_uniform qs
  intro η cfg ψ hψ
  refine (h η cfg ψ hψ).trans ?_
  unfold stepErr
  exact Real.sqrt_le_sqrt (by nlinarith [cfg.env.precision.1])

/-- **Semiclassical order finding with implemented rotations at
`shorPrecision`.** Hypotheses of `Shor_correct_semiclassical_impl_of_modMul_bound`
without `K` and `hmodMul` (the per-step bound is the proved one at `K = 1600`),
and `η ≤ shorPrecision N x`. Success `≥ κ / (2 log(log₂ N + 1)) - 2 ∑_{j<m} ρ j`. -/
theorem Shor_correct_semiclassical_impl_at_shorPrecision
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecision inst.N x.active)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hR : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace)
          R (regSize x.active) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))
        - 2 * ∑ j ∈ Finset.range (regSize x.active), ρ j := by
  have h := Shor_correct_semiclassical_impl_of_modMul_bound 1600 (modMul_approx_valid_dist_1600 qs)
    T hT inst c x y work scratch flag b0 hm hn η hsetup R ρ hR hRc
  have hsplit : ∑ j ∈ Finset.range (regSize x.active), (stepErr 1600 η + ρ j)
      = 2 * (regSize x.active : ℝ) * Real.sqrt (2 * (1600 * η)) / 2
        + ∑ j ∈ Finset.range (regSize x.active), ρ j := by
    rw [Finset.sum_add_distrib]
    simp [stepErr]
    ring
  rw [hsplit] at h
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hx : 1 ≤ regSize x.active := by
    rw [hm, Nat.log2_eq_log_two]
    exact Nat.log_pos Nat.one_lt_two (by nlinarith)
  have hloss := lowering_loss_le_half η inst.N hN x.active hx hη
  have hlogNat : 0 < Nat.log2 inst.N := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_pos Nat.one_lt_two hN
  have hLpos : (0 : ℝ) < (Nat.log2 inst.N : ℝ) := by exact_mod_cast hlogNat
  have hhalf :
      κ / Real.log ((Nat.log2 inst.N : ℝ) + 1) - κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))
        = κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
    field_simp
    ring
  linarith

/-- **Semiclassical order finding at `shorPrecision`.** For every instance,
every `SemiclassicalShorSetup` with `m = regSize x.active = log₂(2N²)`,
`regSize y.active = log₂(2N)`, and every `η ≤ shorPrecision N x`, the success
probability of `orderFindingSemiclassical` run from `|b0⟩` is at least
`κ / (2 log(log₂ N + 1))`: the conclusion of
`Shor_correct_approx_lowered_at_shorPrecision`, for the high-level circuit with
one control qubit instead of the exponent register. -/
theorem Shor_correct_semiclassical_at_shorPrecision
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecision inst.N x.active)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        ((orderFindingSemiclassical inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace).eval (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  have hRc : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖exactPhase c j r φ‖ ≤ ‖φ‖ := fun j _ r _ φ => by
    simp only [exactPhase, lowL_apply]
    rw [norm_evalL_phase]
  have hR : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖exactPhase c j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖
        ≤ (fun _ => (0 : ℝ)) j * ‖φ‖ := fun j _ r _ φ => by
    simp [exactPhase]
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hy : 0 < regSize y.active := regSize_pos_of_log2 inst.N hN _ hn
  have h := Shor_correct_semiclassical_impl_at_shorPrecision T hT inst c x y work scratch flag b0
    hm hn η hη hsetup (fun j => exactPhase c j) (fun _ => 0) hR hRc
  rw [eval_initY1_start y b0 hy hsetup.clean_input.2.1] at h
  rw [orderFindingSemiclassical_eval _ _ _ _ _ _ _ _ _ _ b0 hy hsetup.clean_input.2.1]
  simpa using h

/-- **`Shor_correct_semiclassical_impl_of_modMul_bound`, rotations exact only up
to global phase.** Same hypotheses and conclusion, with `hR` replaced by `hRg`:
for every round `j < m` and record `r` of length `j` there is a phase `α`
(depending on `j`, `r`, not on the state) such that
`‖exp(iα) • R j r φ - Phase c (ffAngle j r) φ‖ ≤ ρ j · ‖φ‖` for every `φ`. -/
theorem Shor_correct_semiclassical_impl_of_modMul_bound_up_to_phase (K : ℝ)
    (hmodMul : ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
      ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hRg : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∃ α : ℝ, ∀ φ : qs.State,
      ‖Complex.exp ((α : ℂ) * Complex.I) • R j r φ
          - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace)
          R (regSize x.active) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * ∑ j ∈ Finset.range (regSize x.active), (stepErr K η + ρ j) := by
  obtain ⟨α, hR', hRc'⟩ := exists_phaseCorrection c _ R ρ hRg hRc
  have h := Shor_correct_semiclassical_impl_of_modMul_bound K hmodMul T hT inst c x y work scratch
    flag b0 hm hn η hsetup (phaseCorrect α R) ρ hR' hRc'
  rwa [probability_of_success_M_congr _ _ _ _ _ (recordProb_phaseCorrect _ _ R α _ _)] at h

/-- **`Shor_correct_semiclassical_impl_at_shorPrecision`, rotations exact only up
to global phase** (hypothesis `hRg` as in
`Shor_correct_semiclassical_impl_of_modMul_bound_up_to_phase`). Success
`≥ κ / (2 log(log₂ N + 1)) - 2 ∑_{j<m} ρ j` at every `η ≤ shorPrecision N x`. -/
theorem Shor_correct_semiclassical_impl_at_shorPrecision_up_to_phase
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecision inst.N x.active)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hRg : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∃ α : ℝ, ∀ φ : qs.State,
      ‖Complex.exp ((α : ℂ) * Complex.I) • R j r φ
          - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace)
          R (regSize x.active) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))
        - 2 * ∑ j ∈ Finset.range (regSize x.active), ρ j := by
  obtain ⟨α, hR', hRc'⟩ := exists_phaseCorrection c _ R ρ hRg hRc
  have h := Shor_correct_semiclassical_impl_at_shorPrecision T hT inst c x y work scratch flag b0
    hm hn η hη hsetup (phaseCorrect α R) ρ hR' hRc'
  rwa [probability_of_success_M_congr _ _ _ _ _ (recordProb_phaseCorrect _ _ R α _ _)] at h

end Shor
