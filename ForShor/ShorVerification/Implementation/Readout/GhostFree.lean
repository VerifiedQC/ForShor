import ForShor.ShorVerification.Implementation.Readout.Proofs.GhostFreeSetup
import ForShor.ShorVerification.Implementation.Readout.BalancedShor

/-!
# Readout: semiclassical order finding WITHOUT an exponent register

The success theorems of `Readout/Shor.lean`, `LoweredShor.lean` and `BalancedShor.lean`
with the ghost reference register `x` removed from the statement AND from every
hypothesis. The number of rounds is `m = log₂(2N²)` (`Nat.log2 (2 * inst.N ^ 2)`), the
record is read as an integer `o < Q = 2^m`, and the hypotheses are only about the
registers the circuit uses (`SemiclassicalGhostFreeSetup`: control `c`, data `y`, `work`,
`scratch`, the flag). The precision condition is `η ≤ shorPrecisionRounds N m`, which is
`shorPrecision N x` for every register `x` with `regSize x = m`
(`shorPrecision_eq_rounds`).

* `Shor_correct_semiclassical_impl_ghostfree_of_modMul_bound`, `…_ghostfree_of_modMul_bound`,
  `Shor_correct_semiclassical_ghostfree` (some `K ≤ 1600`),
  `Shor_correct_semiclassical_impl_ghostfree_at_shorPrecision`,
  `Shor_correct_semiclassical_ghostfree_at_shorPrecision`, and the `_up_to_phase`
  variants: the high-level (`Gate`-level) circuit, conclusions identical to the ghost
  versions with `m = log₂(2N²)`.
* `Shor_correct_semiclassical_lowered_ghostfree_at_shorPrecision`,
  `…_lowered_balanced_ghostfree_at_shorPrecision`,
  `…_lowered_balancedU_ghostfree_at_shorPrecision`: the three lowered programs.

## How `x` disappears from the proof

The ghost proof used `x` once: to compare the ideal semiclassical success with the
textbook circuit `orderFindingIdeal` (which has an exponent register) and quote
`Shor_correct` there. Here (`Proofs/GhostFreeMass.lean`):

1. the ideal semiclassical success equals `successMass T verify a N m r`, a pure real
   number computed from the explicit branch vector
   `(1/2^m) ∑_κ exp(-2πi o κ / 2^m) |a^κ mod N⟩` (`semiclassical_success_eq_mass`; the
   branch closed form involves only `m`; the kets for distinct data values are
   orthonormal in every `QSemantics`);
2. `successMass … ≥ κ / log(log₂ N + 1)` (`successMass_ge_of_semantics`): the same number
   is the success of `orderFindingIdeal` on FRESH registers built inside that proof, where
   `Shor_correct` applies (every `QSemantics` reads and writes every qubit index).

The approximate-gate step (`semiclassical_dist_le_sum_errors_finite`) and the lowering
steps never involved `x`.

## Scope (unchanged from the ghost versions)

* The `MGate`'s feed-forward phases are the exact `Phase c (ffAngle j r)`: Lean's ρ is `0`.
  The `_impl_` theorems keep a ρ parameter for implemented rotations; a synthesized
  (Ross-Selinger) rotation's error is budgeted OUTSIDE Lean through it.
* Qubit count: the lowered QFT and phase-product blocks of the multipliers are counted by the existing
  proved walk exactly as in the coherent circuit (`QubitCount.lower_walk` via `qft_block` /
  `signed_block` / `csigned_block`): every named qubit they touch is counted in
  `semiclassical_peak_formula`, and their scratch is counted as a number. What is not proved
  is a syntactic list of the names those blocks reach (`MGate.qftPhaseReach`), which the qubit
  count does not need. Negation scratch and rotation-synthesis ancillas are counted as numbers
  or not modelled.
* The ghost versions remain in `Shor.lean`, `LoweredShor.lean`, `BalancedShor.lean`, for
  comparison.
-/

namespace Shor

open Readout

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis] [MeasureClass qs]
  [GateSemanticsFacts qs] [LowerGateClass qs]

/-- **Semiclassical order finding with implemented rotations, no exponent register, at a
given per-multiplier constant `K`.**

Hypotheses: `hmodMul`, every `CmodMulInPlaceCore` is within `stepErr K η` of the ideal
controlled multiplier on unit vectors of `ValidAlgorithm1State` (any control qubit; the
form of `modMul_approx_valid_dist_uniform`); `T` makes the continued-fraction search
complete; `inst = (a, N)` an order-finding instance; `regSize y.active = log₂(2N)`;
`hsetup : SemiclassicalGhostFreeSetup` (control `c` outside data/work/scratch/flag,
workspaces, precision, `b0` zero on those registers and on `c`); for every round
`j < m = log₂(2N²)` and record `r` of length `j`, the implemented rotation `R j r` is
within `ρ j · ‖φ‖` of the exact phase `Phase c (ffAngle j r)` on every `φ`, and does not
increase norms.

Run: `initY1 y.active` on `|b0⟩`, then `semiclassicalImpl` with `m` rounds.

Conclusion: the probability that the record, read as `o < 2^m` and post-processed by
`r_found`, returns the order of `a` mod `N` is at least
`κ / log(log₂ N + 1) - 2 ∑_{j<m} (stepErr K η + ρ j)`. -/
theorem Shor_correct_semiclassical_impl_ghostfree_of_modMul_bound (K : ℝ)
    (hmodMul : ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
      ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hR : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work scratch
            flag hsetup.circuit_workspace hsetup.step4_workspace)
          R (Nat.log2 (2 * inst.N ^ 2)) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * ∑ j ∈ Finset.range (Nat.log2 (2 * inst.N ^ 2)), (stepErr K η + ρ j) := by
  set m := Nat.log2 (2 * inst.N ^ 2) with hmdef
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hN1 : 1 < inst.N := by omega
  have hNy : inst.N ≤ ASize y.active := by
    simpa [ASize, hn] using shor_data_capacity_from_log2 inst.N
  have ha : Nat.Coprime inst.a inst.N := Nat.coprime_iff_gcd_eq_one.2 inst.coprime
  have hy : 0 < regSize y.active := regSize_pos_of_log2 inst.N hN _ hn
  have hy0 := hsetup.clean_input.1
  obtain ⟨hy1, hc1, -, hin, hnorm⟩ := semiclassical_start_ghostfree hsetup hN1 hNy
  have hc : c ∉ y.active.qubits := fun h =>
    hsetup.layout.c_not_mem_data (mem_owned_of_mem_active y c h)
  rw [eval_initY1_start y b0 hy hy0]
  set b1 := semiclassicalStartKet (qs := qs) y b0
  set verify : ℕ → Bool := fun d => decide ((inst.a ^ d) % inst.N = 1)
  set r := ord inst.a inst.N inst.coprime
  set u := semiclassicalImpl c (semiclassicalMultipliers inst.a inst.N c m y work scratch flag
      hsetup.circuit_workspace hsetup.step4_workspace) R m (MState.init (qs.ket b1))
  set v := (semiclassicalIdeal inst.a inst.N m y.active c).eval (MState.init (qs.ket b1))
  -- ℓ¹ distance of the record distributions (only `m` enters)
  have hdist := semiclassical_dist_le_sum_errors_finite inst.a inst.N m y.active c
    (semiclassicalSide y work scratch flag) hN1 hNy ha hc
    (fun b w hb => semiclassicalSide_writeNat_ctrl hsetup.layout b w hb)
    (fun b w hb => semiclassicalSide_writeNat_data hsetup.circuit_workspace
      hsetup.step4_workspace b w hb)
    (qs.ket b1) hin hnorm _ R (fun _ => stepErr K η) ρ
    (fun j _ => semiclassicalMultiplier_dist_le_ghostfree K hmodMul hsetup hN1 hNy ha m j) hR hRc
  -- success is stable under that distance
  have hstab := probability_of_success_M_ge_sub T verify m r (2 ^ m) rfl u v
  -- the ideal semiclassical success is the pure number `successMass` …
  have hideal_eq : probability_of_success_M T verify m r (2 ^ m) v
      = successMass T verify inst.a inst.N m r :=
    semiclassical_success_eq_mass T verify inst.a inst.N m r y.active c b1 hN1 hNy ha hc hy1 hc1
  -- … which is at least the ideal bound
  have hideal := successMass_ge_of_semantics qs T hT inst
  linarith

/-- **Semiclassical order finding (the `MGate`), no exponent register, at a given `K`.**
Hypotheses of `Shor_correct_semiclassical_impl_ghostfree_of_modMul_bound` without the
rotations (the `MGate`'s phases are exact, ρ = 0). Success of `orderFindingSemiclassical`
with `m = log₂(2N²)` rounds from `|b0⟩` is `≥ κ / log(log₂ N + 1) - 2 · m · √(2Kη)`. -/
theorem Shor_correct_semiclassical_ghostfree_of_modMul_bound (K : ℝ)
    (hmodMul : ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
      ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        ((orderFindingSemiclassical inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work scratch
            flag hsetup.circuit_workspace hsetup.step4_workspace).eval (MState.init (qs.ket b0)))
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * ((Nat.log2 (2 * inst.N ^ 2) : ℕ) : ℝ) * Real.sqrt (2 * (K * η)) := by
  have hRc : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖exactPhase c j r φ‖ ≤ ‖φ‖ := fun j _ r _ φ => by
    simp only [exactPhase, lowL_apply]
    rw [norm_evalL_phase]
  have hR : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖exactPhase c j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖
        ≤ (fun _ => (0 : ℝ)) j * ‖φ‖ := fun j _ r _ φ => by
    simp [exactPhase]
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hy : 0 < regSize y.active := regSize_pos_of_log2 inst.N hN _ hn
  have h := Shor_correct_semiclassical_impl_ghostfree_of_modMul_bound K hmodMul T hT inst c y
    work scratch flag b0 hn η hsetup (fun j => exactPhase c j) (fun _ => 0) hR hRc
  rw [eval_initY1_start y b0 hy hsetup.clean_input.1] at h
  rw [orderFindingSemiclassical_eval _ _ _ _ _ _ _ _ _ _ b0 hy hsetup.clean_input.1]
  have hsum : ∑ j ∈ Finset.range (Nat.log2 (2 * inst.N ^ 2)),
      (stepErr K η + (fun _ => (0 : ℝ)) j)
      = ((Nat.log2 (2 * inst.N ^ 2) : ℕ) : ℝ) * Real.sqrt (2 * (K * η)) := by
    simp [stepErr]
  rw [hsum] at h
  linarith

-- `hn` is a binder name in the statement (read by the caller), not used by the proof term.
set_option linter.unusedVariables false in
/-- **Semiclassical order finding, no exponent register, uniform constant.** There is a
constant `0 ≤ K ≤ 1600`, chosen before the instance, the registers and the precision, such
that for every instance and every `SemiclassicalGhostFreeSetup` (with
`regSize y.active = log₂(2N)`) the success probability of `orderFindingSemiclassical` with
`m = log₂(2N²)` rounds is at least `κ / log(log₂ N + 1) - 2 · m · √(2Kη)`. -/
theorem Shor_correct_semiclassical_ghostfree (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ∃ K : ℝ, 0 ≤ K ∧ K ≤ 1600 ∧
      ∀ (inst : ShorOrderFindingInstance) (c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
        (b0 : qs.Basis) (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
        (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0),
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        ((orderFindingSemiclassical inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work scratch
            flag hsetup.circuit_workspace hsetup.step4_workspace).eval (MState.init (qs.ket b0)))
          ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
            - 2 * ((Nat.log2 (2 * inst.N ^ 2) : ℕ) : ℝ) * Real.sqrt (2 * (K * η)) := by
  obtain ⟨K, hK0, hK, hmodMul⟩ := modMul_approx_valid_dist_uniform qs
  exact ⟨K, hK0, hK, fun inst c y work scratch flag b0 hn η hsetup =>
    Shor_correct_semiclassical_ghostfree_of_modMul_bound K hmodMul T hT inst c y work scratch
      flag b0 hn η hsetup⟩

/-- **Semiclassical order finding with implemented rotations, no exponent register, at
`shorPrecisionRounds`.** Hypotheses of
`Shor_correct_semiclassical_impl_ghostfree_of_modMul_bound` without `K`, `hmodMul` (the
proved per-step bound at `K = 1600` is used), and `η ≤ shorPrecisionRounds N m`,
`m = log₂(2N²)`. Success `≥ κ / (2 log(log₂ N + 1)) - 2 ∑_{j<m} ρ j`. -/
theorem Shor_correct_semiclassical_impl_ghostfree_at_shorPrecision
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)))
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hR : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work scratch
            flag hsetup.circuit_workspace hsetup.step4_workspace)
          R (Nat.log2 (2 * inst.N ^ 2)) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))
        - 2 * ∑ j ∈ Finset.range (Nat.log2 (2 * inst.N ^ 2)), ρ j := by
  have h := Shor_correct_semiclassical_impl_ghostfree_of_modMul_bound 1600
    (modMul_approx_valid_dist_1600 qs) T hT inst c y work scratch flag b0 hn η hsetup R ρ hR hRc
  set m := Nat.log2 (2 * inst.N ^ 2) with hmdef
  have hsplit : ∑ j ∈ Finset.range m, (stepErr 1600 η + ρ j)
      = 2 * (m : ℝ) * Real.sqrt (2 * (1600 * η)) / 2 + ∑ j ∈ Finset.range m, ρ j := by
    rw [Finset.sum_add_distrib]
    simp [stepErr]
    ring
  rw [hsplit] at h
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hx : 1 ≤ regSize (Reg.interval 0 m) := by
    rw [regSize_interval, hmdef, Nat.log2_eq_log_two]
    exact Nat.log_pos Nat.one_lt_two (by nlinarith)
  have hloss := lowering_loss_le_half η inst.N hN (Reg.interval 0 m) hx
    (by rw [shorPrecision_eq_rounds, regSize_interval]; exact hη)
  rw [regSize_interval] at hloss
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

/-- **Semiclassical order finding, no exponent register, at `shorPrecisionRounds`.** For
every instance, every `SemiclassicalGhostFreeSetup` with `regSize y.active = log₂(2N)`, and
every `η ≤ shorPrecisionRounds N m` (`m = log₂(2N²)`), the success probability of
`orderFindingSemiclassical` with `m` rounds run from `|b0⟩` is at least
`κ / (2 log(log₂ N + 1))`. -/
theorem Shor_correct_semiclassical_ghostfree_at_shorPrecision
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)))
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        ((orderFindingSemiclassical inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work scratch
            flag hsetup.circuit_workspace hsetup.step4_workspace).eval (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  have hRc : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖exactPhase c j r φ‖ ≤ ‖φ‖ := fun j _ r _ φ => by
    simp only [exactPhase, lowL_apply]
    rw [norm_evalL_phase]
  have hR : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖exactPhase c j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖
        ≤ (fun _ => (0 : ℝ)) j * ‖φ‖ := fun j _ r _ φ => by
    simp [exactPhase]
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hy : 0 < regSize y.active := regSize_pos_of_log2 inst.N hN _ hn
  have h := Shor_correct_semiclassical_impl_ghostfree_at_shorPrecision T hT inst c y work scratch
    flag b0 hn η hη hsetup (fun j => exactPhase c j) (fun _ => 0) hR hRc
  rw [eval_initY1_start y b0 hy hsetup.clean_input.1] at h
  rw [orderFindingSemiclassical_eval _ _ _ _ _ _ _ _ _ _ b0 hy hsetup.clean_input.1]
  simpa using h

/-- **`Shor_correct_semiclassical_impl_ghostfree_of_modMul_bound`, rotations exact only up
to global phase**: `hR` replaced by `hRg` (for each `j < m` and record `r` of length `j`
some phase `α` with `‖exp(iα) • R j r φ - Phase c (ffAngle j r) φ‖ ≤ ρ j · ‖φ‖`). -/
theorem Shor_correct_semiclassical_impl_ghostfree_of_modMul_bound_up_to_phase (K : ℝ)
    (hmodMul : ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
      ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hRg : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∃ α : ℝ,
      ∀ φ : qs.State, ‖Complex.exp ((α : ℂ) * Complex.I) • R j r φ
          - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work scratch
            flag hsetup.circuit_workspace hsetup.step4_workspace)
          R (Nat.log2 (2 * inst.N ^ 2)) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * ∑ j ∈ Finset.range (Nat.log2 (2 * inst.N ^ 2)), (stepErr K η + ρ j) := by
  obtain ⟨α, hR', hRc'⟩ := exists_phaseCorrection c _ R ρ hRg hRc
  have h := Shor_correct_semiclassical_impl_ghostfree_of_modMul_bound K hmodMul T hT inst c y work
    scratch flag b0 hn η hsetup (phaseCorrect α R) ρ hR' hRc'
  rwa [probability_of_success_M_congr _ _ _ _ _ (recordProb_phaseCorrect _ _ R α _ _)] at h

/-- **`Shor_correct_semiclassical_impl_ghostfree_at_shorPrecision`, rotations exact only up
to global phase** (hypothesis `hRg`). Success `≥ κ / (2 log(log₂ N + 1)) - 2 ∑_{j<m} ρ j`. -/
theorem Shor_correct_semiclassical_impl_ghostfree_at_shorPrecision_up_to_phase
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)))
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hRg : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∃ α : ℝ,
      ∀ φ : qs.State, ‖Complex.exp ((α : ℂ) * Complex.I) • R j r φ
          - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < Nat.log2 (2 * inst.N ^ 2), ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work scratch
            flag hsetup.circuit_workspace hsetup.step4_workspace)
          R (Nat.log2 (2 * inst.N ^ 2)) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))
        - 2 * ∑ j ∈ Finset.range (Nat.log2 (2 * inst.N ^ 2)), ρ j := by
  obtain ⟨α, hR', hRc'⟩ := exists_phaseCorrection c _ R ρ hRg hRc
  have h := Shor_correct_semiclassical_impl_ghostfree_at_shorPrecision T hT inst c y work scratch
    flag b0 hn η hη hsetup (phaseCorrect α R) ρ hR' hRc'
  rwa [probability_of_success_M_congr _ _ _ _ _ (recordProb_phaseCorrect _ _ R α _ _)] at h

/-! ## The lowered programs -/

/-- **The lowered semiclassical program, no exponent register** (the statement; proved by
`Shor_correct_semiclassical_lowered_ghostfree_at_shorPrecision`). For every instance,
admissible policy `P`, control `c`, `regSize y.active = log₂(2N)`, `η ≤ shorPrecisionRounds N m`
(`m = log₂(2N²)`), `SemiclassicalGhostFreeSetup`, zero data/work/scratch reserves
(`SemiclassicalWorkspaceCleanInput`) and lowering workspace `hws`: the lowered program
`orderFindingSemiclassicalLow` with `m` rounds, run by `MLowGate.eval` from
`MState.init |b0⟩`, finds the order with probability at least `κ / (2 log(log₂ N + 1))`. -/
def ShorCorrectSemiclassicalLoweredGhostFree (T : ℕ → ℕ)
    (_hT : ContinuedFractionSearchComplete T) : Prop :=
  ∀ (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (_hP : P.Admissible)
    (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
    (_hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (_hη : η ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)))
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0)
    (_hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N c
      (Nat.log2 (2 * inst.N ^ 2)) y work scratch flag hsetup.circuit_workspace
      hsetup.step4_workspace)),
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        ((orderFindingSemiclassicalLow P inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work
            scratch flag hsetup.circuit_workspace hsetup.step4_workspace hws).eval
          (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))

/-- **Semiclassical order finding, LOWERED, no exponent register, at `shorPrecisionRounds`.** -/
theorem Shor_correct_semiclassical_lowered_ghostfree_at_shorPrecision (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectSemiclassicalLoweredGhostFree (qs := qs) T hT := by
  intro inst P hP c y work scratch flag b0 hn η hη hsetup hzero hws
  rw [orderFindingSemiclassicalLow, semiclassical_lowerM_eval hP _ _ _ _ _ _ _ _ _ _ hws
    hsetup.layout b0 hzero hsetup.clean_input.2.2.2.2.1]
  exact Shor_correct_semiclassical_ghostfree_at_shorPrecision T hT inst c y work scratch flag b0
    hn η hη hsetup

/-- **The balanced lowered semiclassical program, no exponent register** (the statement).
Hypotheses of `ShorCorrectSemiclassicalLoweredGhostFree`, for every rule `R` (no hypothesis
on `R`); program `orderFindingSemiclassicalLowBalanced P R …`. -/
def ShorCorrectSemiclassicalLoweredBalancedGhostFree (R : Balanced.Rule) (T : ℕ → ℕ)
    (_hT : ContinuedFractionSearchComplete T) : Prop :=
  ∀ (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (_hP : P.Admissible)
    (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
    (_hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (_hη : η ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)))
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0)
    (_hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N c
      (Nat.log2 (2 * inst.N ^ 2)) y work scratch flag hsetup.circuit_workspace
      hsetup.step4_workspace)),
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        ((orderFindingSemiclassicalLowBalanced P R inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2))
            y work scratch flag hsetup.circuit_workspace hsetup.step4_workspace hws).eval
          (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))

/-- **The unconditionally balanced lowered program, no exponent register** (the statement).
Hypotheses of `ShorCorrectSemiclassicalLoweredBalancedGhostFree` plus `MGate.Fits P R` of the
circuit; program `orderFindingSemiclassicalLowBalancedU P R …`. -/
def ShorCorrectSemiclassicalLoweredBalancedUGhostFree (R : Balanced.Rule) (T : ℕ → ℕ)
    (_hT : ContinuedFractionSearchComplete T) : Prop :=
  ∀ (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (_hP : P.Admissible)
    (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
    (_hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (_hη : η ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)))
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0)
    (_hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N c
      (Nat.log2 (2 * inst.N ^ 2)) y work scratch flag hsetup.circuit_workspace
      hsetup.step4_workspace))
    (hf : MGate.Fits P R (orderFindingSemiclassical inst.a inst.N c
      (Nat.log2 (2 * inst.N ^ 2)) y work scratch flag hsetup.circuit_workspace
      hsetup.step4_workspace)),
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        ((orderFindingSemiclassicalLowBalancedU P R inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2))
            y work scratch flag hsetup.circuit_workspace hsetup.step4_workspace hws hf).eval
          (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))

/-- **BALANCED lowering, no exponent register, at `shorPrecisionRounds`**, every rule `R`. -/
theorem Shor_correct_semiclassical_lowered_balanced_ghostfree_at_shorPrecision
    (R : Balanced.Rule) (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectSemiclassicalLoweredBalancedGhostFree (qs := qs) R T hT := by
  intro inst P hP c y work scratch flag b0 hn η hη hsetup hzero hws
  rw [semiclassical_lowerMBalanced_eval hP R _ _ _ _ _ _ _ _ _ _ hws hsetup.layout b0 hzero
    hsetup.clean_input.2.2.2.2.1]
  exact Shor_correct_semiclassical_ghostfree_at_shorPrecision T hT inst c y work scratch flag b0
    hn η hη hsetup

/-- **Every site split, no exponent register, at `shorPrecisionRounds`**, every rule `R`. -/
theorem Shor_correct_semiclassical_lowered_balancedU_ghostfree_at_shorPrecision
    (R : Balanced.Rule) (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectSemiclassicalLoweredBalancedUGhostFree (qs := qs) R T hT := by
  intro inst P hP c y work scratch flag b0 hn η hη hsetup hzero hws hf
  rw [semiclassical_lowerMBalancedU_eval hP R _ _ _ _ _ _ _ _ _ _ hws hf hsetup.layout b0 hzero
    hsetup.clean_input.2.2.2.2.1]
  exact Shor_correct_semiclassical_ghostfree_at_shorPrecision T hT inst c y work scratch flag b0
    hn η hη hsetup


/-! ## Success and peak of one lowered circuit, for every ghost-free setup -/

/-- `m = log₂(2N²) ≥ 1` for an order-finding instance. -/
theorem ghostfree_rounds_pos (inst : ShorOrderFindingInstance) :
    1 ≤ Nat.log2 (2 * inst.N ^ 2) := by
  rw [Nat.log2_eq_log_two]
  have := inst.range
  exact Nat.log_pos Nat.one_lt_two (by nlinarith)

/-- **Plain lowering, no exponent register: success AND peak of the same circuit term**,
for EVERY ghost-free setup. Hypotheses (all of them): `T` makes the continued-fraction
search complete; `inst` an order-finding instance; `P` an admissible policy; control `c`,
registers `y`, `work`, `scratch`, flag, start ket `b0`; `regSize y.active = log₂(2N)`;
`η ≤ shorPrecisionRounds N m` (`m = log₂(2N²)`); `SemiclassicalGhostFreeSetup` (layout of
`c`, multiplier workspaces, work precision, clean input, `c = 0`); zero data/work/scratch
reserves; the lowering workspace `hws`. Conclusions: the lowered program
`orderFindingSemiclassicalLow` succeeds with probability `≥ κ / (2 log(log₂ N + 1))`, and
its proved peak from `orderFindingBaseSetSC c y work scratch flag` is
`Policy.orderFindingQubitsSC P y.width work.width scratch.width` (the
`semiclassical_peak_formula`, whose hypotheses `P.Admissible`, the workspaces, `hws`,
`SemiclassicalLayout`, `1 ≤ m` are all carried here). -/
theorem Shor_correct_semiclassical_lowered_ghostfree_success_and_peak
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (hP : P.Admissible)
    (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)))
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N c
      (Nat.log2 (2 * inst.N ^ 2)) y work scratch flag hsetup.circuit_workspace
      hsetup.step4_workspace)) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        ((orderFindingSemiclassicalLow P inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work
          scratch flag hsetup.circuit_workspace hsetup.step4_workspace hws).eval
          (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
    (orderFindingSemiclassicalLow P inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work
          scratch flag hsetup.circuit_workspace hsetup.step4_workspace hws).peakQubitsFor P.negation
        (orderFindingBaseSetSC c y work scratch flag)
      = Policy.orderFindingQubitsSC P y.width work.width scratch.width :=
  ⟨Shor_correct_semiclassical_lowered_ghostfree_at_shorPrecision T hT inst P hP c y work scratch
      flag b0 hn η hη hsetup hzero hws,
    semiclassical_peak_formula P hP _ _ _ _ _ _ _ _ _ _ hws hsetup.layout
      (ghostfree_rounds_pos inst)⟩

/-- **Balanced lowering (any rule `R`), no exponent register: success AND peak of the same
circuit term**, for every ghost-free setup. Hypotheses of
`Shor_correct_semiclassical_lowered_ghostfree_success_and_peak`; the peak is
`Policy.orderFindingQubitsBalancedSC` at the widths and spare capacities. -/
theorem Shor_correct_semiclassical_lowered_balanced_ghostfree_success_and_peak (R : Balanced.Rule)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (hP : P.Admissible)
    (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)))
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N c
      (Nat.log2 (2 * inst.N ^ 2)) y work scratch flag hsetup.circuit_workspace
      hsetup.step4_workspace)) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        ((orderFindingSemiclassicalLowBalanced P R inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work
          scratch flag hsetup.circuit_workspace hsetup.step4_workspace hws).eval
          (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
    (orderFindingSemiclassicalLowBalanced P R inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work
          scratch flag hsetup.circuit_workspace hsetup.step4_workspace hws).peakQubitsFor P.negation
        (orderFindingBaseSetSC c y work scratch flag)
      = Policy.orderFindingQubitsBalancedSC P R y.width y.capacity work.width work.capacity
          scratch.width scratch.capacity :=
  ⟨Shor_correct_semiclassical_lowered_balanced_ghostfree_at_shorPrecision R T hT inst P hP c y
      work scratch flag b0 hn η hη hsetup hzero hws,
    semiclassical_peak_formula_balanced P R hP _ _ _ _ _ _ _ _ _ _ hws hsetup.layout
      (ghostfree_rounds_pos inst)⟩

/-- **Every site split (rule `R`), no exponent register: success AND peak of the same circuit
term**, for every ghost-free setup. Hypotheses of
`Shor_correct_semiclassical_lowered_ghostfree_success_and_peak` plus `hf : MGate.Fits P R`
of the circuit; the peak is `Policy.orderFindingQubitsUSC` at the widths. -/
theorem Shor_correct_semiclassical_lowered_balancedU_ghostfree_success_and_peak (R : Balanced.Rule)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (hP : P.Admissible)
    (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)))
    (hsetup : SemiclassicalGhostFreeSetup qs η inst.N c y work scratch flag b0)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N c
      (Nat.log2 (2 * inst.N ^ 2)) y work scratch flag hsetup.circuit_workspace
      hsetup.step4_workspace))
    (hf : MGate.Fits P R (orderFindingSemiclassical inst.a inst.N c
      (Nat.log2 (2 * inst.N ^ 2)) y work scratch flag hsetup.circuit_workspace
      hsetup.step4_workspace)) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
        (2 ^ Nat.log2 (2 * inst.N ^ 2))
        ((orderFindingSemiclassicalLowBalancedU P R inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work
          scratch flag hsetup.circuit_workspace hsetup.step4_workspace hws hf).eval
          (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
    (orderFindingSemiclassicalLowBalancedU P R inst.a inst.N c (Nat.log2 (2 * inst.N ^ 2)) y work
          scratch flag hsetup.circuit_workspace hsetup.step4_workspace hws hf).peakQubitsFor P.negation
        (orderFindingBaseSetSC c y work scratch flag)
      = Policy.orderFindingQubitsUSC P R y.width work.width scratch.width :=
  ⟨Shor_correct_semiclassical_lowered_balancedU_ghostfree_at_shorPrecision R T hT inst P hP c y
      work scratch flag b0 hn η hη hsetup hzero hws hf,
    semiclassical_peak_formula_balanced_u P R hP _ _ _ _ _ _ _ _ _ _ hws hf hsetup.layout
      (ghostfree_rounds_pos inst)⟩

end Shor
