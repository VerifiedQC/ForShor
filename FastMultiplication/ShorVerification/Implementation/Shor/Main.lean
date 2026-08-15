import FastMultiplication.ShorVerification.Implementation.Shor.Assertions
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Correctness

/-!
# Shor Main Theorems

This module exposes the end-to-end factoring theorem and uniform correctness of
the lowered approximate circuit. Their named propositions live in
`Assertions.lean`; supporting results, including ideal `Shor_correct`, live
under `Shor.Proofs`.
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [ContinuedFractionPost]
variable [Spec]

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
    (hm : Reg.width x.active = Nat.log2 (2 * fact.N^2))
    (hn : Reg.width y.active = Nat.log2 (2 * fact.N)) :
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
    [LowerGateGateBridge qs]
    [IdealCtrlModMulExactSemantics qs]
    [ModMulPrimitiveGateSemantics qs]
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectApproxLoweredUniform T hT := by
  -- `K` is the single hoisted constant from the gate-level theorem; it is
  -- independent of `inst`/`lowering`/`work`/`flag`, so one `K` serves every
  -- instance and precision level.
  obtain ⟨K, hK, happrox⟩ := Shor_correct_approx_uniform (qs := qs) T hT

  refine ⟨K, hK, ?_⟩
  intro inst lowering x y work flag b0 hm hn η hready

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
          orderFindingApproxLow
            qs lowering.k lowering.hk lowering.ops inst.a inst.N x y work flag
            (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
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
        (C := orderFindingApprox qs inst.a inst.N x y work flag (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace)
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
              (work := work) (flag := flag)
              (hmodWorkspace := (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace)
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
          exact happrox inst x y work flag b0 hm hn η (ShorApproxSetupMinimal.toShorApproxSetup hready.approx)

end Shor
