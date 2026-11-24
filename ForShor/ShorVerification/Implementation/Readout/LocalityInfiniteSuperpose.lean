import ForShor.ShorVerification.Implementation.Readout.LocalityInfinite
import ForShor.ShorVerification.Implementation.Readout.LocalitySpectator

/-!
# Readout: superpositions of start kets that differ from `b0` at infinitely many qubits

The infinite-agreement theorem combined with superposition.

* `MGate.recordProb_superpose_inf`: for a program `P` without `idealCtrlModMul`, a finite
  family of PAIRWISE DISTINCT start kets `b i` (`Set.InjOn b s`), each agreeing with `b0` on
  `P.qubitSupport` (they may differ from `b0`, and from each other, at infinitely many unnamed
  qubits), and any weights `α i`:
  `recordProb (P.eval (init (∑ i ∈ s, α i • |b i⟩))) r = (∑ i ∈ s, ‖α i‖²) * recordProb (P.eval (init |b0⟩)) r`.
* the same for the real circuit (`orderFindingSemiclassical_recordProb_superpose_inf`, agreement
  on `semiclassicalQubits`, no other hypothesis) and the lowered circuit
  (`orderFindingSemiclassicalLow_recordProb_superpose_inf`, clean hypotheses on `b0`; they are
  derived for each `b i` from agreement on `semiclassicalQubits`).

## Why distinct kets give orthogonal branches (the fact used)

Two distinct kets `b i ≠ b j` that both agree with `b0` on the support register `R` agree with
each other on `R`; by `basis_ext` they must then differ at some qubit OUTSIDE `R`
(`eq_of_agreeOff_agreeOn`). Every branch map `L` of the program is `LocalWith R`
(`mgate_mlocal`): its matrix element between kets that differ outside `R` is `0`, i.e. `L|b⟩`
lies in the span of kets that agree with `b` outside `R` (`LocalWith.expand`). The two blocks
are disjoint sets of kets, so `⟪L|b i⟩, L|b j⟩⟫ = 0` (`LocalWith.inner_eq_zero_of_not_agreeOff`,
by ket orthonormality). The squared norms then add, and each equals `‖L|b0⟩‖²`
(`LocalWith.norm_sq_eq`).
-/

namespace Shor
namespace Readout

/-! ## Orthogonality of distinct blocks -/

section Local
variable {qs : QSemantics} [RegEncoding qs.Basis]

/-- A local map sends kets that differ outside `R` to orthogonal states. -/
theorem LocalWith.inner_eq_zero_of_not_agreeOff {R : Reg} {L : qs.State →ₗ[ℂ] qs.State}
    {h : ℕ → ℕ → ℂ} (hL : LocalWith R L h) {b b' : qs.Basis} (hne : ¬ AgreeOff R b b') :
    inner ℂ (L (qs.ket b)) (L (qs.ket b')) = 0 := by
  classical
  rw [hL.expand b, hL.expand b', sum_inner]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [inner_sum]
  refine Finset.sum_eq_zero fun w' _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_ket_ket, ite_eq_right, mul_zero, mul_zero]
  intro e
  exact hne ((agreeOff_writeNat R _ b).symm.trans (e ▸ agreeOff_writeNat R _ b'))

omit [RegEncoding qs.Basis] in
/-- Pythagoras for a finite pairwise-orthogonal family. -/
theorem norm_sq_sum_of_orthogonal {ι : Type*} (s : Finset ι) (v : ι → qs.State)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner]
  simp_rw [inner_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji))
    (fun h => absurd hi h), norm_sq_eq_re_inner (𝕜 := ℂ)]

end Local

section MGates
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- **Superposition of infinitely-different kets, general programs.** -/
theorem MGate.recordProb_superpose_inf (P : MGate) (hP : P.NoIdeal) {ι : Type*}
    (s : Finset ι) (α : ι → ℂ) (b : ι → qs.Basis) (b0 : qs.Basis) (hinj : Set.InjOn b s)
    (hagree : ∀ i ∈ s, ∀ p ∈ P.qubitSupport, RegEncoding.bit p (b i) = RegEncoding.bit p b0)
    (r : Record) :
    recordProb (P.eval (MState.init (∑ i ∈ s, α i • qs.ket (b i)))) r
      = (∑ i ∈ s, ‖α i‖ ^ 2) * recordProb (P.eval (MState.init (qs.ket b0))) r := by
  have hS : P.qubitSupport ⊆ regSet P.supportReg := fun q hq => (MGate.mem_supportReg P q).2 hq
  have hon : ∀ i ∈ s, AgreeOn P.supportReg (b i) b0 := fun i hi p hp =>
    hagree i hi p ((MGate.mem_supportReg P p).1 hp)
  obtain ⟨pre, L, ⟨h, hL⟩, he⟩ := mgate_mlocal (qs := qs) P hP hS r
  rw [recordProb, recordProb, he, he]
  unfold MState.init
  by_cases hp : pre = []
  · simp only [hp, ↓reduceIte]
    rw [map_sum, norm_sq_sum_of_orthogonal, Finset.sum_mul]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_smul, norm_smul, mul_pow, hL.norm_sq_eq (hon i hi)]
    · intro i hi j hj hij
      rw [map_smul, map_smul, inner_smul_left, inner_smul_right,
        hL.inner_eq_zero_of_not_agreeOff, mul_zero, mul_zero]
      intro hoff
      exact hij (hinj hi hj (eq_of_agreeOff_agreeOn hoff ((hon i hi).trans (hon j hj).symm)))
  · simp [hp]

/-- **Real circuit.** Any registers; distinct kets `b i` agreeing with `b0` on
`semiclassicalQubits` (infinitely many differences allowed). -/
theorem orderFindingSemiclassical_recordProb_superpose_inf (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) {ι : Type*} (s : Finset ι)
    (α : ι → ℂ) (b : ι → qs.Basis) (b0 : qs.Basis) (hinj : Set.InjOn b s)
    (hagree : ∀ i ∈ s, ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p (b i) = RegEncoding.bit p b0) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (∑ i ∈ s, α i • qs.ket (b i)))) r
      = (∑ i ∈ s, ‖α i‖ ^ 2) * recordProb ((orderFindingSemiclassical a N c m y work scratch
          flag hw hs4).eval (MState.init (qs.ket b0))) r := by
  exact MGate.recordProb_superpose_inf _ (orderFindingSemiclassical_noIdeal a N c m hw hs4) s α b b0
      hinj (fun i hi p hp => hagree i hi p (orderFindingSemiclassical_support a N m hw hs4 hp)) r

/-- A lowered program that agrees with a high-level one on each of finitely many start kets
agrees with it on every combination of them (both evaluations are linear). -/
theorem MLowGate.eval_init_sum_eq (L : MLowGate) (G : MGate) {ι : Type*} (s : Finset ι)
    (α : ι → ℂ) (b : ι → qs.Basis)
    (h : ∀ i ∈ s, L.eval (MState.init (qs.ket (b i))) = G.eval (MState.init (qs.ket (b i)))) :
    L.eval (MState.init (∑ i ∈ s, α i • qs.ket (b i)))
      = G.eval (MState.init (∑ i ∈ s, α i • qs.ket (b i))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : MState.init (0 : qs.State) = (0 : ℂ) • MState.init (0 : qs.State) := by
      funext r; simp [MState.init]
    rw [Finset.sum_empty, h0, MLowGate.eval_smul, MGate.eval_smul, zero_smul, zero_smul]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, MState.init_add, MState.init_smul, MLowGate.eval_add,
      MGate.eval_add, MLowGate.eval_smul, MGate.eval_smul, h i (Finset.mem_insert_self i s),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

/-- **Lowered circuit.** Hypotheses of `semiclassical_lowerM_eval` for `b0` (admissible
policy, workspace, layout, zero reserves, zero active scratch); distinct kets `b i` agreeing with
`b0` on `semiclassicalQubits` (infinitely many differences allowed; the clean hypotheses for
each `b i` are derived). -/
theorem orderFindingSemiclassicalLow_recordProb_superpose_inf {P : ShorLoweringPolicy}
    (hP : P.Admissible) (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0) {ι : Type*} (s : Finset ι)
    (α : ι → ℂ) (b : ι → qs.Basis) (hinj : Set.InjOn b s)
    (hagree : ∀ i ∈ s, ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p (b i) = RegEncoding.bit p b0) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (∑ i ∈ s, α i • qs.ket (b i)))) r
      = (∑ i ∈ s, ‖α i‖ ^ 2) * recordProb ((orderFindingSemiclassicalLow P a N c m y work
          scratch flag hw hs4 hws).eval (MState.init (qs.ket b0))) r := by
  have key := MLowGate.eval_init_sum_eq
    (orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws)
    (orderFindingSemiclassical a N c m y work scratch flag hw hs4) s α b (fun i hi => by
      have hzero' := semiclassicalWorkspaceCleanInput_ofAgree (hagree i hi) hzero
      have hscratch' : RegEncoding.toNat scratch.active (b i) = 0 := by
        rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_scratch (active_sub p hp))
          (hagree i hi), hscratch]
      exact semiclassical_lowerM_eval hP a N c m y work scratch flag hw hs4 hws hl (b i) hzero'
        hscratch')
  rw [key, orderFindingSemiclassicalLow,
    semiclassical_lowerM_eval hP a N c m y work scratch flag hw hs4 hws hl b0 hzero hscratch]
  exact orderFindingSemiclassical_recordProb_superpose_inf a N c m y work scratch flag hw hs4 s α
    b b0 hinj hagree r

end MGates

end Readout
end Shor
