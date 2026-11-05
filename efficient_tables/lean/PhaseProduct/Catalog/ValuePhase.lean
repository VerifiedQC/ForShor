import Model.Defs
import PhaseProduct.Identity.GenericPhase
import PhaseProduct.Catalog.BestKnownPhase
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Value-level phase identities

Defines the arithmetic of the phase character (`phaseCharacter_add`,
`phaseCharacter_sum`, `phaseCharacter_fin_sum`) and diagonal application facts.
A fixed pair or triple certificate yields the phase identity for every real
scale and input (`source_pair_phase_product`, `source_triple_phase_product`),
with weights fixed in advance (`source_pair_phase_product_exists`) and the
best-known generator instance `bestKnown_pair_phase_product`.
-/

open scoped BigOperators

namespace Paper.ValuePhase

theorem phaseAngle_add (theta : ℝ) (a b : ℚ) :
    phaseAngle theta (a + b) = phaseAngle theta a + phaseAngle theta b := by
  unfold phaseAngle
  push_cast
  ring

theorem phaseCharacter_zero (theta : ℝ) : phaseCharacter theta 0 = 1 := by
  simp [phaseCharacter, phaseAngle]

theorem phaseCharacter_add (theta : ℝ) (a b : ℚ) :
    phaseCharacter theta (a + b) =
      phaseCharacter theta a * phaseCharacter theta b := by
  unfold phaseCharacter
  rw [phaseAngle_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem phaseCharacter_sum {α : Type} (theta : ℝ) (s : Finset α)
    (f : α → ℚ) :
    phaseCharacter theta (∑ a ∈ s, f a) =
      ∏ a ∈ s, phaseCharacter theta (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phaseCharacter_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, phaseCharacter_add, ih]

theorem phaseCharacter_fin_sum {n : Nat} (theta : ℝ) (f : Fin n → ℚ) :
    phaseCharacter theta (∑ i, f i) = ∏ i, phaseCharacter theta (f i) := by
  classical
  simpa using phaseCharacter_sum theta (Finset.univ : Finset (Fin n)) f

theorem phaseCharacter_unit (theta : ℝ) (q : ℚ) :
    ‖phaseCharacter theta q‖ = 1 := by
  unfold phaseCharacter
  exact Complex.norm_exp_ofReal_mul_I (phaseAngle theta q)

theorem diagonalApply_pointwise_norm {Basis : Type}
    (phase : Basis → ℂ) (amplitude : Amplitude Basis)
    (hunit : ∀ b, ‖phase b‖ = 1) (b : Basis) :
    ‖diagonalApply phase amplitude b‖ = ‖amplitude b‖ := by
  simp [diagonalApply, hunit b]

theorem diagonalApply_pointwise_inverse {Basis : Type}
    (phase : Basis → ℂ) (amplitude : Amplitude Basis)
    (hunit : ∀ b, ‖phase b‖ = 1) (b : Basis) :
    (phase b)⁻¹ * diagonalApply phase amplitude b = amplitude b := by
  rw [diagonalApply]
  have hne : phase b ≠ 0 := by
    intro hz
    have hh := hunit b
    simp [hz] at hh
  calc
    (phase b)⁻¹ * (phase b * amplitude b) =
        ((phase b)⁻¹ * phase b) * amplitude b := by rw [← mul_assoc]
    _ = amplitude b := by rw [inv_mul_cancel₀ hne, one_mul]

theorem diagonalApply_eq_of_exponent_eq {Basis : Type}
    (theta : ℝ) (sourceExponent targetExponent : Basis → ℚ)
    (amplitude : Amplitude Basis)
    (h : ∀ b, sourceExponent b = targetExponent b) :
    diagonalApply (fun b => phaseCharacter theta (sourceExponent b)) amplitude =
      diagonalApply (fun b => phaseCharacter theta (targetExponent b)) amplitude := by
  funext b
  simp [diagonalApply, h b]

/-- A fixed pair certificate yields the phase identity for every real scale and
integer input pair, retaining actual source value traces as witnesses. -/
theorem source_pair_phase_product {k q : Nat} (hk : k > 0)
    (ops : TableGeneration.Prog k)
    (pts : Fin q → TableGeneration.Operations.Point)
    (weight : Fin q → ℚ) (base : Fin k → ℚ)
    (hcontract : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops (List.ofFn pts))
    (hcert : PhaseIdentity.PairCertificate weight
      (GenericPhase.indexedSourceRows pts) base)
    (theta : ℝ) (x z : ValueSemantics.Values k) :
    ∃ xs zs : List Int,
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) x = some (x, xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) z = some (z, zs) ∧
      xs.length = q ∧ zs.length = q ∧
      (∏ l : Fin q, phaseCharacter theta
        (weight l * (xs.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ))) =
      phaseCharacter theta
        (PhaseIdentity.linearForm base (fun j => (x j : ℚ)) *
         PhaseIdentity.linearForm base (fun j => (z j : ℚ))) := by
  obtain ⟨xs, zs, hx, hz, hxl, hzl, hsum⟩ :=
    GenericPhase.source_pair_trace_phase_product hk ops pts weight base hcontract hcert x z
  refine ⟨xs, zs, hx, hz, hxl, hzl, ?_⟩
  rw [← phaseCharacter_fin_sum theta]
  apply congrArg (phaseCharacter theta)
  simpa using hsum

/-- A fixed triple certificate yields the phase identity for every real scale
and integer input triple, retaining source value traces as witnesses. -/
theorem source_triple_phase_product {k q : Nat} (hk : k > 0)
    (ops : TableGeneration.Prog k)
    (pts : Fin q → TableGeneration.Operations.Point)
    (weight : Fin q → ℚ) (base : Fin k → ℚ)
    (hcontract : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops (List.ofFn pts))
    (hcert : PhaseIdentity.TripleCertificate weight
      (GenericPhase.indexedSourceRows pts) base)
    (theta : ℝ) (x y z : ValueSemantics.Values k) :
    ∃ xs ys zs : List Int,
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) x = some (x, xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) y = some (y, ys) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) z = some (z, zs) ∧
      xs.length = q ∧ ys.length = q ∧ zs.length = q ∧
      (∏ l : Fin q, phaseCharacter theta
        (weight l * (xs.getD l.val 0 : ℚ) *
          (ys.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ))) =
      phaseCharacter theta
        (PhaseIdentity.linearForm base (fun j => (x j : ℚ)) *
         PhaseIdentity.linearForm base (fun j => (y j : ℚ)) *
         PhaseIdentity.linearForm base (fun j => (z j : ℚ))) := by
  obtain ⟨xs, ys, zs, hx, hy, hz, hxl, hyl, hzl, hsum⟩ :=
    GenericPhase.source_triple_trace_phase_product hk ops pts weight base hcontract hcert x y z
  refine ⟨xs, ys, zs, hx, hy, hz, hxl, hyl, hzl, ?_⟩
  rw [← phaseCharacter_fin_sum theta]
  apply congrArg (phaseCharacter theta)
  simpa using hsum

/-- Certificate weights are fixed before all real scales and all inputs. -/
theorem source_pair_phase_product_exists {k q : Nat} (hk : k > 0)
    (ops : TableGeneration.Prog k)
    (pts : Fin q → TableGeneration.Operations.Point)
    (base : Fin k → ℚ)
    (hcontract : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops (List.ofFn pts))
    (hweights : ∃ weight : Fin q → ℚ,
      PhaseIdentity.PairCertificate weight (GenericPhase.indexedSourceRows pts) base) :
    ∃ weight : Fin q → ℚ, ∀ theta : ℝ, ∀ x z : ValueSemantics.Values k,
      ∃ xs zs : List Int,
        ValueSemantics.valueTrace (SourceBridge.mapToFull ops) x = some (x, xs) ∧
        ValueSemantics.valueTrace (SourceBridge.mapToFull ops) z = some (z, zs) ∧
        xs.length = q ∧ zs.length = q ∧
        (∏ l : Fin q, phaseCharacter theta
          (weight l * (xs.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ))) =
        phaseCharacter theta
          (PhaseIdentity.linearForm base (fun j => (x j : ℚ)) *
           PhaseIdentity.linearForm base (fun j => (z j : ℚ))) := by
  obtain ⟨weight, hcert⟩ := hweights
  refine ⟨weight, ?_⟩
  intro theta x z
  exact source_pair_phase_product hk ops pts weight base hcontract hcert theta x z

/-- Certificate weights are fixed before all real scales and all inputs. -/
theorem source_triple_phase_product_exists {k q : Nat} (hk : k > 0)
    (ops : TableGeneration.Prog k)
    (pts : Fin q → TableGeneration.Operations.Point)
    (base : Fin k → ℚ)
    (hcontract : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops (List.ofFn pts))
    (hweights : ∃ weight : Fin q → ℚ,
      PhaseIdentity.TripleCertificate weight (GenericPhase.indexedSourceRows pts) base) :
    ∃ weight : Fin q → ℚ, ∀ theta : ℝ, ∀ x y z : ValueSemantics.Values k,
      ∃ xs ys zs : List Int,
        ValueSemantics.valueTrace (SourceBridge.mapToFull ops) x = some (x, xs) ∧
        ValueSemantics.valueTrace (SourceBridge.mapToFull ops) y = some (y, ys) ∧
        ValueSemantics.valueTrace (SourceBridge.mapToFull ops) z = some (z, zs) ∧
        xs.length = q ∧ ys.length = q ∧ zs.length = q ∧
        (∏ l : Fin q, phaseCharacter theta
          (weight l * (xs.getD l.val 0 : ℚ) *
            (ys.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ))) =
        phaseCharacter theta
          (PhaseIdentity.linearForm base (fun j => (x j : ℚ)) *
           PhaseIdentity.linearForm base (fun j => (y j : ℚ)) *
           PhaseIdentity.linearForm base (fun j => (z j : ℚ))) := by
  obtain ⟨weight, hcert⟩ := hweights
  refine ⟨weight, ?_⟩
  intro theta x y z
  exact source_triple_phase_product hk ops pts weight base hcontract hcert theta x y z


/-- Nontrivial-scale regression: at theta = pi the unit rational exponent is -1,
so the phase scale is not silently fixed to 2*pi. -/
theorem phaseCharacter_pi_one : phaseCharacter Real.pi 1 = -1 := by
  simp [phaseCharacter, phaseAngle, Complex.exp_pi_mul_I]

/-- Actual BestKnown pair generator: its single existential weight works at
all real scales and all inputs, with source traces and lengths retained. -/
theorem bestKnown_pair_phase_product (k : Nat) (hk : 2 ≤ k) (b : ℚ) :
    ∃ (w : Fin (2*(k-1)+1) → ℚ), ∀ theta : ℝ,
      ∀ (x z : ValueSemantics.Values k),
      ∃ (xs zs : List Int),
        ValueSemantics.valueTrace (SourceBridge.mapToFull
          (TableGeneration.bestKnownGenerate .PhaseProduct k hk)) x = some (x,xs) ∧
        ValueSemantics.valueTrace (SourceBridge.mapToFull
          (TableGeneration.bestKnownGenerate .PhaseProduct k hk)) z = some (z,zs) ∧
        xs.length = 2*k-1 ∧ zs.length = 2*k-1 ∧
        (∏ l, phaseCharacter theta
          (w l * (xs.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ))) =
        phaseCharacter theta
          ((∑ j : Fin k, b^j.val * (x j : ℚ)) *
           (∑ j : Fin k, b^j.val * (z j : ℚ))) := by
  obtain ⟨w, hall⟩ := BestKnownPhase.bestKnown_pair_phase k hk b
  refine ⟨w, ?_⟩
  intro theta x z
  obtain ⟨xs, zs, hx, hz, hxl, hzl, hsum⟩ := hall x z
  refine ⟨xs, zs, hx, hz, hxl, hzl, ?_⟩
  rw [← phaseCharacter_fin_sum theta]
  apply congrArg (phaseCharacter theta)
  simpa using hsum

/-- Actual BestKnown triple generator: its single existential weight works at
all real scales and all inputs, with source traces and lengths retained. -/
theorem bestKnown_triple_phase_product (k : Nat) (hk : 2 ≤ k) (b : ℚ) :
    ∃ (w : Fin (3*(k-1)+1) → ℚ), ∀ theta : ℝ,
      ∀ (x y z : ValueSemantics.Values k),
      ∃ (xs ys zs : List Int),
        ValueSemantics.valueTrace (SourceBridge.mapToFull
          (TableGeneration.bestKnownGenerate .PhaseTripleProduct k hk)) x = some (x,xs) ∧
        ValueSemantics.valueTrace (SourceBridge.mapToFull
          (TableGeneration.bestKnownGenerate .PhaseTripleProduct k hk)) y = some (y,ys) ∧
        ValueSemantics.valueTrace (SourceBridge.mapToFull
          (TableGeneration.bestKnownGenerate .PhaseTripleProduct k hk)) z = some (z,zs) ∧
        xs.length = 3*k-2 ∧ ys.length = 3*k-2 ∧ zs.length = 3*k-2 ∧
        (∏ l, phaseCharacter theta
          (w l * (xs.getD l.val 0 : ℚ) * (ys.getD l.val 0 : ℚ) *
            (zs.getD l.val 0 : ℚ))) =
        phaseCharacter theta
          ((∑ j : Fin k, b^j.val * (x j : ℚ)) *
           (∑ j : Fin k, b^j.val * (y j : ℚ)) *
           (∑ j : Fin k, b^j.val * (z j : ℚ))) := by
  obtain ⟨w, hall⟩ := BestKnownPhase.bestKnown_triple_phase k hk b
  refine ⟨w, ?_⟩
  intro theta x y z
  obtain ⟨xs, ys, zs, hx, hy, hz, hxl, hyl, hzl, hsum⟩ := hall x y z
  refine ⟨xs, ys, zs, hx, hy, hz, hxl, hyl, hzl, ?_⟩
  rw [← phaseCharacter_fin_sum theta]
  apply congrArg (phaseCharacter theta)
  simpa using hsum
end Paper.ValuePhase