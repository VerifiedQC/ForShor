import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Assertions
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Correctness
import FastMultiplication.ShorVerification.Framework.Math.Factoring_Reduction.ProbabilityBound
import FastMultiplication.ShorVerification.Framework.Math.Factoring_Reduction.Reduction

/-!
# Shor Main Theorems

The three final Shor correctness theorems, each typed by its named proposition
from `Assertions.lean` and proven here.  These are the public results the
Reference implementation consumes; all supporting lemmas live under
`Shor.Proofs`.
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]

/-- End-to-end statement combining the classical choice probability, ideal
quantum order-finding, and the classical factor extraction theorem. -/
theorem Shor_end_to_end_factoring
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    (fact : ShorFactoringInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hinput : IdealOrderFindingInput qs x y b0)
    (hm : regSize x.active = Nat.log2 (2 * fact.N^2))
    (hn : regSize y.active = Nat.log2 (2 * fact.N)) :
    ShorEndToEndFactoring T hT fact x y b0 hinput hm hn := by {
  let N := fact.N
  have h_odd : Odd N := fact.odd
  have h_N : N > 2 := fact.gt_two
  have h_not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k :=
    fact.not_prime_power
  constructor
  { exact shors_probability_bound N h_odd (by omega) h_not_prime_power }
  {
    intro a h_a_in_successful
    obtain ⟨⟨ha1, ha2⟩, hgcd⟩ := success_eq_conditions a N h_a_in_successful
    have hvalid_N : a ∈ valid_choices N := by
      simp [valid_choices, ha1, ha2, hgcd]
    have hvalid_fact : a ∈ valid_choices fact.N := by
      simpa [N] using hvalid_N

    have h_succ : shor_success_conditions a (ord a N hgcd) N := by {
      have h_a_in_successful_N : a ∈ successful_choices N := by
        simpa [N] using h_a_in_successful
      have h_a_is_succ : is_successful_choice a N := by {
        unfold successful_choices at h_a_in_successful_N
        simp_all
      }
      unfold is_successful_choice is_period at h_a_is_succ
      obtain ⟨r, h_per, h_cond⟩ := h_a_is_succ
      have h_r_eq : r = ord a N hgcd := by {
        have h_bridge := is_period_ord a N hgcd
        subst h_per
        simpa
      }
      rwa [h_r_eq] at h_cond
    }

    exists hgcd
    let inst : ShorOrderFindingInstance :=
      { a := a
        N := N
        range := ⟨by omega, ha2⟩
        coprime := hgcd
        }
    exact ⟨
      by
        simpa [N, inst] using
          (Shor_correct (qs := qs) T hT inst x y b0 hm hn hinput),
      shors_classical_reduction
        a
        (ord a N hgcd)
        N
        h_N
        ⟨ha1, ha2⟩
        hgcd
        (is_period_ord a N hgcd)
        h_succ
    ⟩
  }
}

/--
Uniform correctness of the fully lowered approximate Shor
order-finding circuit.

The lowering introduces no additional approximation error: its success
probability is exactly that of `orderFindingApprox`.
-/
theorem Shor_correct_approx_lowered_uniform
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectApproxLoweredUniform T hT := by
  -- `K` is the single hoisted constant from the gate-level theorem; it is
  -- independent of `inst`/`lowering`/`work`/`flag`, so one `K` serves every
  -- instance and precision level.
  obtain ⟨K, hK, happrox⟩ := Shor_correct_approx_uniform (qs := qs) T hT

  refine ⟨K, hK, ?_⟩
  intro inst lowering x y work scratch flag b0 hm hn η hready

  calc
    probability_of_success
        (qs := qs)
        (T := T)
        (verify :=
          fun d =>
            decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)
        (evalC := LowerGateClass.evalL (qs := qs))
        (C :=
          orderFindingApproxLow lowering.k lowering.hk lowering.ops lowering.pts lowering.hpts
            inst.a inst.N x y work
            scratch flag
            (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
            (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace
            hready.workspace)
        (ψ := qs.ket b0)
        =
      probability_of_success
        (qs := qs)
        (T := T)
        (verify :=
          fun d =>
            decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)
        (evalC := qs.eval)
        (C := orderFindingApprox inst.a inst.N x y work scratch flag
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace)
        (ψ := qs.ket b0) := by
          exact
            orderFindingApproxLow_probability_eq
              (qs := qs)
              (lowering := lowering)
              (T := T)
              (verify :=
                fun d =>
                  decide ((inst.a ^ d) % inst.N = 1))
              (a := inst.a) (N := inst.N) (x := x) (y := y)
              (work := work) (scratch := scratch) (flag := flag)
              (hmodWorkspace := (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace)
              (hstep4 := (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace)
              (hLowerWorkspace := hready.workspace)
              (ψ := qs.ket b0)
              (hclean := hready.workspace_clean)
              (r := ord inst.a inst.N inst.coprime)
              (Q := ASize x.active)

    _ ≥
        κ / (Nat.log2 inst.N : ℝ) ^ 4
          -
        2 * (tbits x.active : ℝ) *
          Real.sqrt (2 * (K * η)) := by
          exact happrox inst x y work scratch flag b0 hm hn η
            (ShorApproxSetupMinimal.toShorApproxSetup hready.approx)

/--
The lowered circuit's success bound at a caller-supplied constant `K`,
against an assumed uniform modular-exponentiation distance bound at that `K`.

`Shor_correct_approx_lowered_uniform` hoists `K` into an existential, which
suits a headline statement but not a caller that has already fixed its own
constant. `Reference` has: it takes `K = 2048`, justified by
`modExpApprox_correct`'s `K ≤ 2048` and monotonicity of `stepErr`, and needs
the conclusion at that constant. This is the theorem it consumes.
-/
theorem Shor_correct_approx_lowered_of_modExp_bound_assertion
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [IdealCtrlModMulExactSemantics qs]
    (K : ℝ)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectApproxLoweredOfModExpBound K T hT := by
  intro hmodExp inst lowering x y work scratch flag b0 hm hn η hready
  exact Shor_correct_approx_lowered_of_modExp_bound (qs := qs) K hmodExp T hT
    inst lowering x y work scratch flag b0 hm hn η hready

/--
Correctness of the fully lowered approximate Shor order-finding circuit at a
precision chosen from `N`.

`Shor_correct_approx_lowered_uniform` leaves `η` free, and its right-hand side
is informative only once `η` is tied to `N`: the subtracted term
`2 · tbits(x) · √(2Kη)` does not shrink with `N` on its own, so a fixed `η`
makes the bound negative for large `N`. At any `η ≤ shorPrecision N x` the loss
is at most half of the ideal bound, and half of it survives.

`shorPrecision` is a closed form, not a threshold behind an existential: the
proof runs at the explicit constant `2048` (`modExpApprox_valid_dist_2048`), so
a circuit builder can compute the precision it needs before building anything.

The precision this asks for is `Θ(n⁻¹⁰)`, costing `O(log n)` work bits, so it
composes with `shorGateCountBound_of_setup`, whose budget for
`algorithm1ExtraBits` is linear in `n`.
-/
theorem Shor_correct_approx_lowered
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectApproxLowered T hT := by
  intro inst lowering x y work scratch flag b0 hm hn η hη hready
  have hmain :=
    Shor_correct_approx_lowered_of_modExp_bound_assertion (qs := qs) 2048 T hT
      (modExpApprox_valid_dist_2048 (qs := qs))
      inst lowering x y work scratch flag b0 hm hn η hready
  have hN : 2 ≤ inst.N := by
    have := inst.range
    omega
  have hlogNat : 0 < Nat.log2 inst.N := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_pos Nat.one_lt_two hN
  have hx : 1 ≤ tbits x.active := by
    unfold tbits
    rw [hm, Nat.log2_eq_log_two]
    exact Nat.log_pos Nat.one_lt_two (by nlinarith)
  have hloss := lowering_loss_le_half η inst.N hN x.active hx hη
  -- `linarith` sees `κ / L⁴` and `κ / (2L⁴)` as unrelated atoms, so relate them.
  have hLpos : (0 : ℝ) < (Nat.log2 inst.N : ℝ) := by exact_mod_cast hlogNat
  have hhalf :
      κ / (Nat.log2 inst.N : ℝ) ^ 4 - κ / (2 * (Nat.log2 inst.N : ℝ) ^ 4)
        = κ / (2 * (Nat.log2 inst.N : ℝ) ^ 4) := by
    field_simp
    ring
  linarith [hmain, hloss, hhalf]

end Shor
