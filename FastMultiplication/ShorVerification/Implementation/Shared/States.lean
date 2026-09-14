import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics

/-!
# `QSemantics` state algebra: evaluator laws, wrappers, norms, and clean closure

Derived laws of `Framework/Quantum/QSemantics.lean`: the zero/subtraction/
injectivity/adjoint-inverse consequences of the `GateSemanticsCore` interface,
convenient `QSemantics.*` wrapper names for the class laws, a `Finset.sum`
push-through lemma, isometry/norm/freshness transport facts, and the
`CleanClosure` predicate on `qs.State`.
-/

namespace Shor
universe u
variable {Basis : Type u} [RegEncoding Basis]
open QSemantics

attribute [instance] QSemantics.instNormed
attribute [instance] QSemantics.instIP

/-! =========================================================
    Derived Core Evaluator Laws

    `GateSemanticsCore` assumes the primitive linear/isometric interface.  These
    theorems derive the zero, subtraction, inverse-adjoint, and inner-product
    forms used for rewriting in proof files.
========================================================= -/

namespace GateSemanticsCore

@[simp] theorem eval_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate) :
    qs.eval U 0 = 0 := by
  simpa using
    (GateSemanticsCore.eval_smul
      (qs := qs) U (0 : ℂ) (0 : qs.State))

theorem hsub
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ φ : qs.State) :
    qs.eval U (ψ - φ) =
      qs.eval U ψ - qs.eval U φ := by
  change
    GateSemanticsCore.eval (qs := qs) U (ψ - φ) =
      GateSemanticsCore.eval (qs := qs) U ψ -
        GateSemanticsCore.eval (qs := qs) U φ
  rw [sub_eq_add_neg]
  rw [GateSemanticsCore.eval_add]
  have hneg :
      GateSemanticsCore.eval (qs := qs) U (-φ) =
        -GateSemanticsCore.eval (qs := qs) U φ := by
    simpa using
      (GateSemanticsCore.eval_smul
        (qs := qs) U (-1 : ℂ) φ)
  rw [hneg]
  rw [sub_eq_add_neg]

theorem eval_injective
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate) :
    Function.Injective (qs.eval U) := by
  intro ψ φ h

  have hmap :
      qs.eval U (ψ - φ) = 0 := by
    rw [GateSemanticsCore.hsub (qs := qs), h]
    simp

  have hinner :=
    GateSemanticsCore.inner_preserved
      (qs := qs) U (ψ - φ) (ψ - φ)

  change
    inner ℂ (qs.eval U (ψ - φ)) (qs.eval U (ψ - φ)) =
      inner ℂ (ψ - φ) (ψ - φ) at hinner
  rw [hmap] at hinner

  have hzero :
      inner ℂ (ψ - φ) (ψ - φ) = 0 := by
    simpa using hinner.symm

  have hdiff :
      ψ - φ = 0 := by
    exact (inner_self_eq_zero.mp hzero)

  exact sub_eq_zero.mp hdiff

theorem eval_apply_adj
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ : qs.State) :
    qs.eval U (qs.eval (Gate.adj U) ψ) = ψ := by
  apply
    GateSemanticsCore.eval_injective
      (qs := qs) (U := Gate.adj U)

  exact
    GateSemanticsCore.eval_adj_apply
      (qs := qs)
      U
      (qs.eval (Gate.adj U) ψ)

theorem inner_eval_adj
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ φ : qs.State) :
    inner ℂ (qs.eval (Gate.adj U) ψ) φ =
      inner ℂ ψ (qs.eval U φ) := by
  have h :=
    GateSemanticsCore.inner_preserved
      (qs := qs)
      U
      (qs.eval (Gate.adj U) ψ)
      φ

  simp [eval_apply_adj] at h
  exact h.symm

theorem state_eq_of_inner_ket_eq
    (qs : QSemantics)
    (ψ φ : qs.State)
    (h :
      ∀ b : qs.Basis,
        inner ℂ ψ (qs.ket b) =
          inner ℂ φ (qs.ket b)) :
    ψ = φ := by
  have hzero :
      ∀ χ : qs.State,
        inner ℂ (ψ - φ) χ = 0 := by
    intro χ

    apply qs.state_induction
      (P := fun χ =>
        inner ℂ (ψ - φ) χ = 0)

    · simp

    · intro χ₁ χ₂ h₁ h₂
      simp[inner_add_right]
      simp [h₁, h₂]

    · intro a χ hχ
      simp[inner_smul_right]
      simp [hχ]

    · intro b
      have hb := h b
      simpa [inner_sub_left] using
        sub_eq_zero.mpr hb

  have hself :
      inner ℂ (ψ - φ) (ψ - φ) = 0 :=
    hzero (ψ - φ)

  have :
      ψ - φ = 0 :=
    inner_self_eq_zero.mp hself

  exact sub_eq_zero.mp this

end GateSemanticsCore


/-! =========================================================
    QSemantics Projection Wrappers

    These wrappers expose the class laws as ordinary theorem names so the later
    proof files can rewrite with a uniform `QSemantics.*` vocabulary.
========================================================= -/

namespace QSemantics

theorem eval_id
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (ψ : qs.State) :
    qs.eval Gate.id ψ = ψ :=
  GateSemanticsCore.eval_id (qs := qs) ψ

theorem eval_seq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U V : Gate)
    (ψ : qs.State) :
    qs.eval (U ;; V) ψ = qs.eval V (qs.eval U ψ) :=
  GateSemanticsCore.eval_seq (qs := qs) U V ψ

theorem inner_preserved
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ φ : qs.State) :
    inner ℂ (qs.eval U ψ) (qs.eval U φ) = inner ℂ ψ φ :=
  GateSemanticsCore.inner_preserved (qs := qs) U ψ φ

theorem eval_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate) :
    qs.eval U 0 = 0 :=
  GateSemanticsCore.eval_zero (qs := qs) U

theorem eval_add
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ φ : qs.State) :
    qs.eval U (ψ + φ) = qs.eval U ψ + qs.eval U φ :=
  GateSemanticsCore.eval_add (qs := qs) U ψ φ

theorem eval_smul
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (a : ℂ)
    (ψ : qs.State) :
    qs.eval U (a • ψ) = a • qs.eval U ψ :=
  GateSemanticsCore.eval_smul (qs := qs) U a ψ

theorem hsub
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ φ : qs.State) :
    qs.eval U (ψ - φ) = qs.eval U ψ - qs.eval U φ :=
  GateSemanticsCore.hsub (qs := qs) U ψ φ

theorem eval_adj_apply
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ : qs.State) :
    qs.eval (Gate.adj U) (qs.eval U ψ) = ψ :=
  GateSemanticsCore.eval_adj_apply (qs := qs) U ψ

theorem eval_apply_adj
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ : qs.State) :
    qs.eval U (qs.eval (Gate.adj U) ψ) = ψ :=
  GateSemanticsCore.eval_apply_adj (qs := qs) U ψ

end QSemantics


/-! =========================================================
    Evaluation Sums
========================================================= -/

lemma eval_sum
    {α : Type}
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (s : Finset α)
    (f : α → qs.State) :
    qs.eval U (∑ a ∈ s, f a) = ∑ a ∈ s, qs.eval U (f a) := by
  classical
  refine Finset.induction_on s ?h0 ?hs
  · simp
  · intro a s ha hs
    simp [Finset.sum_insert ha, QSemantics.eval_add, hs]


/-! =========================================================
    Norms, Isometry, And Freshness Transport
========================================================= -/

/-- `eval U` is an isometry if it preserves inner products. -/
lemma eval_isometry
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs]
  (U : Gate)
  (hU : ∀ ψ φ : qs.State, inner ℂ (qs.eval U ψ) (qs.eval U φ) = inner ℂ ψ φ) :
  ∀ ψ φ : qs.State, ‖qs.eval U ψ - qs.eval U φ‖ = ‖ψ - φ‖ := by
  intro ψ φ
  have hnorm : ‖qs.eval U (ψ - φ)‖ = ‖ψ - φ‖ := by
    have : ‖qs.eval U (ψ - φ)‖ ^ 2 = ‖ψ - φ‖ ^ 2 := by
      simpa [sq] using congrArg Complex.re (hU (ψ - φ) (ψ - φ))
    aesop
  simpa [qs.hsub U ψ φ] using hnorm

@[simp] lemma eval_seq_simp
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs]
  (U V : Gate) (ψ : qs.State) :
  qs.eval (U ;; V) ψ = qs.eval V (qs.eval U ψ) := by
  simpa using (qs.eval_seq U V ψ)

lemma eval_norm_preserved
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ : qs.State) :
  ‖qs.eval U ψ‖ = ‖ψ‖ := by
  have h := eval_isometry qs U (by intro ψ φ; simpa using qs.inner_preserved U ψ φ) ψ 0
  simpa [qs.eval_zero U] using h

lemma FreshZero.of_eq_on_bits
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (b₁ b₂ : Basis)
    (hbits :
      ∀ q : ℕ,
        q ∈ r.qubits →
        RegEncoding.bit q b₂ =
          RegEncoding.bit q b₁)
    (hzero : FreshZero r b₁) :
    FreshZero r b₂ := by
  unfold FreshZero at hzero ⊢

  apply Nat.zero_of_testBit_eq_false
  intro j

  by_cases hj : j < regSize r

  · let i : Fin (regSize r) :=
      ⟨j, hj⟩

    let q : ℕ :=
      r.get i

    have hq :
        q ∈ r.qubits := by
      dsimp [q, i, Reg.get]
      exact List.get_mem r.qubits _

    calc
      Nat.testBit
          (RegEncoding.toNat r b₂)
          j
          =
        RegEncoding.bit q b₂ := by
          symm
          simpa [q, i] using
            RegEncoding.bit_eq_testBit_toNat
              r b₂ i

      _ =
        RegEncoding.bit q b₁ :=
          hbits q hq

      _ =
        Nat.testBit
          (RegEncoding.toNat r b₁)
          j := by
            simpa [q, i] using
              RegEncoding.bit_eq_testBit_toNat
                r b₁ i

      _ = false := by
        rw [hzero]
        simp

  · have hwidth :
        regSize r ≤ j :=
      Nat.le_of_not_gt hj

    have hToNat :
        RegEncoding.toNat r b₂
          <
        2 ^ regSize r := by
      simpa [ASize] using
        RegEncoding.toNat_lt_ASize
          (r := r)
          (b := b₂)

    have hpow :
        2 ^ regSize r ≤ 2 ^ j := by
      exact
        Nat.pow_le_pow_right
          (by omega)
          hwidth

    exact
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hToNat hpow)








/-! ### Basis-clean linear closure -/

/-- The set of states reachable from `P`-clean basis kets by `+` and `•`:
    a `zero/ket/add/smul` linear closure parameterized by the per-basis
    predicate `P`. -/
inductive CleanClosure {qs : QSemantics} [RegEncoding qs.Basis]
    (P : qs.Basis → Prop) : qs.State → Prop
  | zero : CleanClosure P 0
  | ket (b : qs.Basis) (h : P b) : CleanClosure P (qs.ket b)
  | add {ψ φ : qs.State} (hψ : CleanClosure P ψ) (hφ : CleanClosure P φ) :
      CleanClosure P (ψ + φ)
  | smul (a : ℂ) {ψ : qs.State} (hψ : CleanClosure P ψ) :
      CleanClosure P (a • ψ)

end Shor
