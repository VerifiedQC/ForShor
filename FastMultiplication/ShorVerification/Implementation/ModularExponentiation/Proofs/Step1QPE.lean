import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.Algorithm1Expansion
import FastMultiplication.ShorVerification.Implementation.RegisterLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.Semantics.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.MacroSemantics
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Math.QPETail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semiring

/-! =========================================================
    Step-1 Quantum Phase Estimation Bounds

This file contains the setup and analytic estimates needed to view the
fractional work-register load in Step 1 as a QPE kernel, then bound its tail
uniformly over valid basis inputs.

The development runs in three stages.

* *Trace bookkeeping.* The abstract coefficients carried by an `Alg1Trace` are
  identified with the canonical `alg1PhaseCoeff`, the Step-1 error is exhibited
  as the discarded packet `tr.badStep1`, and its squared norm is shown to be
  `alg1TraceBadMass`.
* *Packet algebra.* Hadamards, the controlled phase product, and the inverse
  QFT are evaluated exactly on a work packet, which rewrites the canonical
  coefficient as the explicit Fourier coefficient `alg1FractionalLoadCoeff`,
  and finally as the standard finite QPE kernel `qpeKernel`.
* *Analysis.* A purely numerical study of `qpeKernel` bounds the mass it places
  outside a precision window of width `δ` by `128 / (M * δ)`.

The two endpoints are `alg1_step1_error_sq_eq_trace_bad_mass`, which turns the
Step-1 error into a bad-mass computation, and `alg1_qpe_tail_basis_uniform`,
which bounds that bad mass by `512 * η` uniformly over good basis inputs.
========================================================= -/

open Shor

universe u v

/-! =========================================================
    Shared linear-algebra and register helpers

Generic facts reused throughout the file: splitting a finite sum along a
decidable predicate, Pythagoras for a finite orthogonal family, idempotence of
repeated writes to one register, and invariance of the norm of a ket expansion
under any injective reindexing of its basis labels. The section closes with the
register-level statement that undoing the Step-5 cleanup writes restores a good
input basis state exactly.
========================================================= -/

section SharedHelpers

/-- Splitting a finite sum along a decidable predicate recovers the whole sum. -/
lemma sum_filter_add_sum_filter_not {α β : Type*} [AddCommMonoid β] (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f : α → β) : (∑ x ∈ s.filter p, f x) + ∑ x ∈ s.filter (fun x => ¬ p x), f x =
    ∑ x ∈ s, f x := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : p x <;> simp [hp]

/-- Pythagoras: the squared norm of a pairwise-orthogonal finite family adds. -/
lemma norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe {qs : QSemantics} {ι : Type v} (s : Finset ι) (f : ι → qs.State)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (f i) (f j) = 0) : ‖∑ i ∈ s, f i‖ ^ 2 =
    ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  revert horth
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | insert a s ha ih =>
      intro horth

      have horth_s : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
            inner ℂ (f i) (f j) = 0 := by
        intro i hi j hj hij
        exact horth i
          (Finset.mem_insert_of_mem hi)
          j
          (Finset.mem_insert_of_mem hj)
          hij

      have hih : ‖∑ i ∈ s, f i‖ ^ 2 =
          ∑ i ∈ s, ‖f i‖ ^ 2 :=
        ih horth_s

      have hcross :
          inner ℂ (f a) (∑ b ∈ s, f b) = 0 := by
        rw [inner_sum]
        refine Finset.sum_eq_zero ?_
        intro b hb
        apply horth a (by simp) b (Finset.mem_insert_of_mem hb)
        intro hab
        subst b
        exact ha hb

      calc
        ‖∑ i ∈ insert a s, f i‖ ^ 2
            =
          ‖f a + ∑ i ∈ s, f i‖ ^ 2 := by
            rw [Finset.sum_insert ha]
        _ =
          ‖f a‖ ^ 2
            + 2 * Complex.re (inner ℂ (f a) (∑ i ∈ s, f i))
            + ‖∑ i ∈ s, f i‖ ^ 2 := by
              exact norm_add_sq (𝕜 := ℂ) _ _
        _ =
          ‖f a‖ ^ 2 + ‖∑ i ∈ s, f i‖ ^ 2 := by
            rw [hcross]
            simp
        _ =
          ‖f a‖ ^ 2 + ∑ i ∈ s, ‖f i‖ ^ 2 := by
            rw [hih]
        _ =
          ∑ i ∈ insert a s, ‖f i‖ ^ 2 := by
            rw [Finset.sum_insert ha]

/--
The norm of a ket expansion depends only on its coefficients.

Any two injective labellings of the support give orthonormal families, so both
sums have the same termwise squared norms.
-/
lemma norm_sum_reindex_ket_eq (qs : QSemantics) {ι : Type v} (s : Finset ι) (α : ι → ℂ) (f g : ι → qs.Basis) (hf :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ≠ f j) (hg : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → g i ≠ g j) :
    ‖∑ i ∈ s, α i • qs.ket (f i)‖ =
    ‖∑ i ∈ s, α i • qs.ket (g i)‖ := by
  classical
  have horth_f : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        inner ℂ (α i • qs.ket (f i)) (α j • qs.ket (f j)) = 0 := by
    intro i hi j hj hij
    rw [inner_smul_left, inner_smul_right,
      qs.ket_inner_eq_zero_of_ne (hf i hi j hj hij)]
    simp
  have horth_g : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        inner ℂ (α i • qs.ket (g i)) (α j • qs.ket (g j)) = 0 := by
    intro i hi j hj hij
    rw [inner_smul_left, inner_smul_right,
      qs.ket_inner_eq_zero_of_ne (hg i hi j hj hij)]
    simp
  have hsq_f :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
      (qs := qs) s (fun i => α i • qs.ket (f i)) horth_f
  have hsq_g :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
      (qs := qs) s (fun i => α i • qs.ket (g i)) horth_g
  have hterms : (∑ i ∈ s, ‖α i • qs.ket (f i)‖ ^ 2) =
      ∑ i ∈ s, ‖α i • qs.ket (g i)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [norm_smul, ket_norm_one qs]
  have hsquares : ‖∑ i ∈ s, α i • qs.ket (f i)‖ ^ 2 =
      ‖∑ i ∈ s, α i • qs.ket (g i)‖ ^ 2 := by
    rw [hsq_f, hsq_g, hterms]
  have hn1 : 0 ≤ ‖∑ i ∈ s, α i • qs.ket (f i)‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖∑ i ∈ s, α i • qs.ket (g i)‖ := norm_nonneg _
  nlinarith

/--
Clearing the work register and restoring the data register returns a good input
basis state unchanged.

The two registers are disjoint, so the intermediate writes commute and collapse;
freshness of the grown data bit is what lets the grown write be undone by the
original data value.
-/
lemma alg1_reset_extendHi_work_write (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModMulConfig η)
    (z : qs.Basis) (w y : ℕ) (hz : GoodModMulBasisInput qs cfg.env.N cfg.env.data cfg.env.work cfg.flag z) :
    RegEncoding.writeNat ((cfg.env.data.grow 1).active) (RegEncoding.toNat cfg.env.data.active z)
      (RegEncoding.writeNat cfg.env.work.active 0 (RegEncoding.writeNat ((cfg.env.data.grow 1).active) y
          (RegEncoding.writeNat cfg.env.work.active w z))) =
    z := by
  have hfresh1 : cfg.env.data.FreshFor 1 z :=
    ExtReg.freshFor_one_of_two
      cfg.env.data
      z
      cfg.env.circuit_workspace.1
      hz.2.1

  have hgrown_toNat : RegEncoding.toNat (cfg.env.data.grow 1).active z =
        RegEncoding.toNat cfg.env.data.active z := by
    simpa [ExtReg.toNat] using
      (Gate.ExtReg.toNat_grow_of_fresh cfg.env.data 1 z hfresh1)

  have hrestore_ext : RegEncoding.writeNat ((cfg.env.data.grow 1).active) (RegEncoding.toNat cfg.env.data.active z)
        z =
      z := by
    rw [← hgrown_toNat]
    exact RegEncoding.writeNat_toNat (cfg.env.data.grow 1).active z

  have hdata_work :
      Shor.Disjoint (cfg.env.data.grow 1).active cfg.env.work.active := by
    rw [Shor.Disjoint, List.disjoint_left]
    intro q hqData hqWork
    have h := cfg.env.circuit_workspace.dataCarry_work_disjoint
    rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h
    exact h
      (List.mem_append_left _ hqData)
      (List.mem_append_left _ hqWork)

  calc
    RegEncoding.writeNat
        ((cfg.env.data.grow 1).active)
        (RegEncoding.toNat cfg.env.data.active z)
        (RegEncoding.writeNat
          cfg.env.work.active
          0
          (RegEncoding.writeNat
            ((cfg.env.data.grow 1).active)
            y
            (RegEncoding.writeNat cfg.env.work.active w z)))
        =
      RegEncoding.writeNat
        ((cfg.env.data.grow 1).active)
        (RegEncoding.toNat cfg.env.data.active z)
        (RegEncoding.writeNat
          ((cfg.env.data.grow 1).active)
          y
          (RegEncoding.writeNat
            cfg.env.work.active
            0
            (RegEncoding.writeNat cfg.env.work.active w z))) := by
        rw [← writeNat_comm_of_disjoint
          ((cfg.env.data.grow 1).active)
          cfg.env.work.active
          hdata_work
          y
          0
          (RegEncoding.writeNat cfg.env.work.active w z)]
    _ =
      RegEncoding.writeNat
        ((cfg.env.data.grow 1).active)
        (RegEncoding.toNat cfg.env.data.active z)
        (RegEncoding.writeNat cfg.env.work.active 0 z) := by
        rw [writeNat_overwrite_same_reg]
        rw [writeNat_overwrite_same_reg]
    _ =
      RegEncoding.writeNat
        cfg.env.work.active
        0
        (RegEncoding.writeNat
          ((cfg.env.data.grow 1).active)
          (RegEncoding.toNat cfg.env.data.active z)
          z) :=
        writeNat_comm_of_disjoint
          ((cfg.env.data.grow 1).active)
          cfg.env.work.active
          hdata_work
          (RegEncoding.toNat cfg.env.data.active z)
          0
          z
    _ = RegEncoding.writeNat cfg.env.work.active 0 z := by
        rw [hrestore_ext]
    _ = z := by
        simpa [hz.2.2.1] using
          RegEncoding.writeNat_toNat cfg.env.work.active z

end SharedHelpers

/-! =========================================================
    Trace coefficients and their identification

An `Alg1Trace` carries abstract Step-1 coefficients; nothing in the record
forces them to be the canonical ones. This section pins them down. A normalized
valid state has total input mass one, distinct good branches paired with
distinct work labels give distinct basis states, and projecting a trace-shaped
packet onto a single label reads off exactly one product of coefficients. The
endpoint `alg1_trace_phaseCoeff_eq_alg1PhaseCoeff` uses these to identify
`tr.phaseCoeff` with `alg1PhaseCoeff` on every branch of nonzero weight.
========================================================= -/

section TraceCoefficientIdentification

/--
A normalized valid trace has total input probability one.
-/
lemma alg1_trace_input_mass_one (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs] {η : ℝ}
    (cfg : ModMulConfig η) (ψ : qs.State) (tr : Alg1Trace qs cfg ψ) : cfg.ValidUnitState qs ψ →
      ∑ b ∈ tr.support, ‖tr.inputCoeff b‖ ^ 2 = 1 := by
  classical
  intro hunit

  have horth : ∀ b ∈ tr.support, ∀ b' ∈ tr.support, b ≠ b' → inner ℂ (tr.inputCoeff b • qs.ket b)
          (tr.inputCoeff b' • qs.ket b') =
        0 := by
    intro b hb b' hb' hne
    rw [
      inner_smul_left,
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne hne
    ]
    simp

  have hsq : ‖∑ b ∈ tr.support, tr.inputCoeff b • qs.ket b‖ ^ 2 =
      ∑ b ∈ tr.support, ‖tr.inputCoeff b • qs.ket b‖ ^ 2 :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
      (qs := qs)
      tr.support
      (fun b => tr.inputCoeff b • qs.ket b)
      horth

  calc
    ∑ b ∈ tr.support, ‖tr.inputCoeff b‖ ^ 2
        =
      ∑ b ∈ tr.support, ‖tr.inputCoeff b • qs.ket b‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        simp [norm_smul, ket_norm_one qs]
    _ =
      ‖∑ b ∈ tr.support, tr.inputCoeff b • qs.ket b‖ ^ 2 :=
        hsq.symm
    _ = ‖ψ‖ ^ 2 := by
      exact (congrArg (fun φ : qs.State => ‖φ‖ ^ 2) tr.input_eq).symm
    _ = 1 := by
      rw [hunit.2]
      norm_num

/-- Section-local restatement of `writeNat_overwrite_same_reg`. -/
private lemma qpe_writeNat_overwrite_same_reg {Basis : Type u} [RegEncoding Basis] (r : Reg) (v w : ℕ) (b : Basis) :
    RegEncoding.writeNat r v (RegEncoding.writeNat r w b) =
    RegEncoding.writeNat r v b :=
  writeNat_overwrite_same_reg r v w b

/--
Writing work labels over good inputs is injective in both arguments.

Good inputs have a zero work register, so the written label can be read back;
that recovers `t = u`, and clearing the work register again recovers `b = b'`.
-/
private lemma qpe_work_write_injective_of_good (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ}
    (cfg : ModMulConfig η) (b b' : qs.Basis) (hb : GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) (hb' : GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b') (t u : Fin (ASize cfg.env.work.active)) (hEq :
      RegEncoding.writeNat cfg.env.work.active t.1 b = RegEncoding.writeNat cfg.env.work.active u.1 b') :
    b = b' ∧ t = u := by
  have htu_val : t.1 = u.1 := by
    calc
      t.1
          =
        RegEncoding.toNat cfg.env.work.active
          (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
            symm
            exact
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work.active t.1 b t.isLt
      _ =
        RegEncoding.toNat cfg.env.work.active
          (RegEncoding.writeNat cfg.env.work.active u.1 b') := by
            rw [hEq]
      _ = u.1 :=
        RegEncoding.toNat_writeNat_of_lt
          cfg.env.work.active u.1 b' u.isLt

  have htu : t = u :=
    Fin.ext htu_val

  have hb_work : RegEncoding.toNat cfg.env.work.active b = 0 :=
    hb.2.2.1

  have hb'_work : RegEncoding.toNat cfg.env.work.active b' = 0 :=
    hb'.2.2.1

  have hb_zero :
      RegEncoding.writeNat cfg.env.work.active 0 b = b := by
    simpa [hb_work] using
      (RegEncoding.writeNat_toNat cfg.env.work.active b)

  have hb'_zero :
      RegEncoding.writeNat cfg.env.work.active 0 b' = b' := by
    simpa [hb'_work] using
      (RegEncoding.writeNat_toNat cfg.env.work.active b')

  have hbb : b = b' := by
    calc
      b =
          RegEncoding.writeNat cfg.env.work.active 0 b := hb_zero.symm
      _ =
          RegEncoding.writeNat cfg.env.work.active 0
            (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
              symm
              exact
                qpe_writeNat_overwrite_same_reg
                  cfg.env.work.active 0 t.1 b
      _ =
          RegEncoding.writeNat cfg.env.work.active 0
            (RegEncoding.writeNat cfg.env.work.active u.1 b') := by
              exact congrArg (RegEncoding.writeNat cfg.env.work.active 0) hEq
      _ =
          RegEncoding.writeNat cfg.env.work.active 0 b' := by
              exact
                qpe_writeNat_overwrite_same_reg
                  cfg.env.work.active 0 u.1 b'
      _ = b' := hb'_zero

  exact ⟨hbb, htu⟩

/--
Projecting a trace-shaped work packet onto one basis label reads off the single
coefficient `inputCoeff b * coeff b t`.

All other terms of the double sum are orthogonal to the chosen label by
`qpe_work_write_injective_of_good`.
-/
private lemma qpe_inner_trace_work_packet (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs] {η : ℝ}
    (cfg : ModMulConfig η) (ψ : qs.State) (tr : Alg1Trace qs cfg ψ)
    (coeff : qs.Basis → Fin (ASize cfg.env.work.active) → ℂ) (b : qs.Basis) (hb : b ∈ tr.support)
    (t : Fin (ASize cfg.env.work.active)) : inner ℂ (qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b))
      (∑ b' ∈ tr.support, tr.inputCoeff b' • ∑ u : Fin (ASize cfg.env.work.active), coeff b' u • qs.ket
                (RegEncoding.writeNat cfg.env.work.active u.1 b')) =
    tr.inputCoeff b * coeff b t := by
  classical

  rw [inner_sum]
  rw [Finset.sum_eq_single b]
  ·
    rw [inner_smul_right, inner_sum]
    rw [Finset.sum_eq_single t]
    ·
      rw [inner_smul_right, ket_inner_self]
      simp
    ·
      intro u _hu hut
      have hneq : RegEncoding.writeNat cfg.env.work.active t.1 b ≠
          RegEncoding.writeNat cfg.env.work.active u.1 b := by
        intro hEq
        rcases
            qpe_work_write_injective_of_good
              qs cfg b b
              (tr.input_good b hb)
              (tr.input_good b hb)
              t u hEq with
          ⟨_, htu⟩
        exact hut htu.symm
      rw [inner_smul_right, qs.ket_inner_eq_zero_of_ne hneq]
      simp
    ·
      intro ht
      simp at ht
  ·
    intro b' hb' hne
    rw [inner_smul_right, inner_sum]
    have hsum : ∑ i : Fin (ASize cfg.env.work.active), inner ℂ
            (qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b)) (coeff b' i •
              qs.ket (RegEncoding.writeNat cfg.env.work.active i.1 b')) =
        0 := by
      apply Finset.sum_eq_zero
      intro u hu
      have hneq : RegEncoding.writeNat cfg.env.work.active t.1 b ≠
          RegEncoding.writeNat cfg.env.work.active u.1 b' := by
        intro hEq
        rcases
            qpe_work_write_injective_of_good
              qs cfg b b'
              (tr.input_good b hb)
              (tr.input_good b' hb')
              t u hEq with
          ⟨hbb, _⟩
        exact hne hbb.symm
      rw [inner_smul_right, qs.ket_inner_eq_zero_of_ne hneq]
      simp
    rw [hsum, mul_zero]
  ·
    intro hnot
    exact False.elim (hnot hb)

/--
The abstract trace coefficients are the canonical Step-1 coefficients.

Both `tr.phaseCoeff` and `alg1PhaseCoeff` describe the same Step-1 packet, so
projecting that packet onto `ket (writeNat work t b)` computes each of them as
`tr.inputCoeff b * -` by `qpe_inner_trace_work_packet`. Cancelling the nonzero
input coefficient identifies the two. This is what licenses replacing an
arbitrary trace by the canonical QPE data in every later estimate.
-/
lemma alg1_trace_phaseCoeff_eq_alg1PhaseCoeff (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    {η : ℝ} (cfg : ModMulConfig η) (ψ : qs.State) (tr : Alg1Trace qs cfg ψ) (b : qs.Basis) (hb : b ∈ tr.support)
    (hcoeff : tr.inputCoeff b ≠ 0) (t : Fin (ASize cfg.env.work.active)) :
    tr.phaseCoeff b t = alg1PhaseCoeff qs cfg b t := by
  classical

  have htrace :
      qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
        =
      ∑ b' ∈ tr.support,
        tr.inputCoeff b' •
          ∑ u : Fin (ASize cfg.env.work.active),
            tr.phaseCoeff b' u •
              qs.ket
                (RegEncoding.writeNat cfg.env.work.active u.1 b') := by
    simpa [ModMulConfig.U1] using tr.full_step1_eq

  have hcanonical :
      qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
        =
      ∑ b' ∈ tr.support,
        tr.inputCoeff b' •
          ∑ u : Fin (ASize cfg.env.work.active),
            alg1PhaseCoeff qs cfg b' u •
              qs.ket
                (RegEncoding.writeNat cfg.env.work.active u.1 b') := by
    calc
      qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
          =
        qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg)
          (∑ b' ∈ tr.support, tr.inputCoeff b' • qs.ket b') := by
          exact
            congrArg
              (fun φ : qs.State =>
                qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) φ)
              tr.input_eq
      _ =
        ∑ b' ∈ tr.support,
          tr.inputCoeff b' •
            ∑ u : Fin (ASize cfg.env.work.active),
              alg1PhaseCoeff qs cfg b' u •
                qs.ket
                  (RegEncoding.writeNat cfg.env.work.active u.1 b') := by
          rw [eval_finset_sum]
          apply Finset.sum_congr rfl
          intro b' hb'
          rw [
            qs.eval_smul,
            alg1_step1_ket_qpe_expansion
              qs cfg b' (tr.input_good b' hb')
          ]

  have hpackets : (∑ b' ∈ tr.support, tr.inputCoeff b' • ∑ u : Fin (ASize cfg.env.work.active), tr.phaseCoeff b' u •
              qs.ket (RegEncoding.writeNat cfg.env.work.active u.1 b')) = ∑ b' ∈ tr.support, tr.inputCoeff b' •
          ∑ u : Fin (ASize cfg.env.work.active), alg1PhaseCoeff qs cfg b' u • qs.ket
                (RegEncoding.writeNat cfg.env.work.active u.1 b') :=
    htrace.symm.trans hcanonical

  have hprojected :=
    congrArg
      (fun ξ : qs.State =>
        inner ℂ
          (qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b))
          ξ)
      hpackets

  have hmul : tr.inputCoeff b * tr.phaseCoeff b t =
      tr.inputCoeff b * alg1PhaseCoeff qs cfg b t := by
    calc
      tr.inputCoeff b * tr.phaseCoeff b t
          =
        inner ℂ
          (qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b))
          (∑ b' ∈ tr.support,
            tr.inputCoeff b' •
              ∑ u : Fin (ASize cfg.env.work.active),
                tr.phaseCoeff b' u •
                  qs.ket
                    (RegEncoding.writeNat cfg.env.work.active u.1 b')) := by
              symm
              exact
                qpe_inner_trace_work_packet
                  qs cfg ψ tr tr.phaseCoeff b hb t
      _ =
        inner ℂ
          (qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b))
          (∑ b' ∈ tr.support,
            tr.inputCoeff b' •
              ∑ u : Fin (ASize cfg.env.work.active),
                alg1PhaseCoeff qs cfg b' u •
                  qs.ket
                    (RegEncoding.writeNat cfg.env.work.active u.1 b')) :=
        hprojected
      _ =
        tr.inputCoeff b * alg1PhaseCoeff qs cfg b t :=
        qpe_inner_trace_work_packet
          qs cfg ψ tr
          (fun b' u => alg1PhaseCoeff qs cfg b' u)
          b hb t

  exact mul_left_cancel₀ hcoeff hmul

end TraceCoefficientIdentification

/-! =========================================================
    Trace bad mass and the Step-1 error

Step 1 is only approximate because the inverse QFT spreads amplitude onto
labels outside the precision window. This section isolates that amplitude. The
difference between the true Step-1 state and the idealized `tr.goodStep1` is
exactly the discarded packet `tr.badStep1`, whose squared norm is
`alg1TraceBadMass`. Since the trace bad mass is a convex combination of the
per-basis-input masses, a uniform tail estimate on basis inputs lifts to the
whole trace.
========================================================= -/

section TraceBadMassAndStep1Error

/--
Rewrite the trace bad mass using canonical QPE coefficients.

Branches with zero input coefficient contribute zero, so canonicality is only
needed on nonzero branches.
-/
lemma alg1_trace_bad_mass_eq_weighted_qpe_bad_mass (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    {η : ℝ} (cfg : ModMulConfig η) (ψ : qs.State) (tr : Alg1Trace qs cfg ψ) : alg1TraceBadMass qs cfg tr =
    ∑ b ∈ tr.support,
      ‖tr.inputCoeff b‖ ^ 2 * alg1QpeBadMass qs cfg b := by
  classical
  unfold alg1TraceBadMass alg1QpeBadMass
  apply Finset.sum_congr rfl
  intro b hb

  by_cases hzero : tr.inputCoeff b = 0
  · simp [hzero]
  ·
    apply congrArg (fun r : ℝ => ‖tr.inputCoeff b‖ ^ 2 * r)
    apply Finset.sum_congr rfl
    intro t ht
    rw [alg1_trace_phaseCoeff_eq_alg1PhaseCoeff
      qs cfg ψ tr b hb hzero t]

/--
Lift the basis tail estimate coherently across a normalized valid trace.

This is just finite weighted averaging: all weights are nonnegative and sum
to one by `alg1_trace_input_mass_one`.
-/
lemma alg1_trace_bad_mass_le_of_basis_tail (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    {Ctail : ℝ} (hTail : ∀ (η : ℝ) (cfg : ModMulConfig η) (b : qs.Basis), GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b → alg1QpeBadMass qs cfg b ≤ Ctail * η) {η : ℝ}
    (cfg : ModMulConfig η) (ψ : qs.State) (tr : Alg1Trace qs cfg ψ) : cfg.ValidUnitState qs ψ →
      alg1TraceBadMass qs cfg tr ≤ Ctail * η := by
  intro hunit
  rw [alg1_trace_bad_mass_eq_weighted_qpe_bad_mass qs cfg ψ tr]

  have hmass :
      ∑ b ∈ tr.support, ‖tr.inputCoeff b‖ ^ 2 = 1 :=
    alg1_trace_input_mass_one qs cfg ψ tr hunit

  have hpoint : ∀ b ∈ tr.support, ‖tr.inputCoeff b‖ ^ 2 * alg1QpeBadMass qs cfg b ≤
        ‖tr.inputCoeff b‖ ^ 2 * (Ctail * η) := by
    intro b hb
    exact
      mul_le_mul_of_nonneg_left
        (hTail η cfg b (tr.input_good b hb))
        (sq_nonneg _)

  calc
    ∑ b ∈ tr.support,
      ‖tr.inputCoeff b‖ ^ 2 * alg1QpeBadMass qs cfg b
        ≤
      ∑ b ∈ tr.support,
        ‖tr.inputCoeff b‖ ^ 2 * (Ctail * η) := by
          exact Finset.sum_le_sum fun b hb => hpoint b hb
    _ =
      (∑ b ∈ tr.support, ‖tr.inputCoeff b‖ ^ 2) * (Ctail * η) := by
        rw [Finset.sum_mul]
    _ = Ctail * η := by rw [hmass, one_mul]

/--
The Step-1 difference is exactly the discarded QPE packet.

Proof: expand `tr.full_step1_eq`, partition `Finset.univ` into good and bad
labels, and subtract the definition of `tr.goodStep1`.
-/
lemma alg1_step1_error_eq_bad_packet (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] {η : ℝ}
    (cfg : ModMulConfig η) (ψ : qs.State) (tr : Alg1Trace qs cfg ψ) :
    qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
      - tr.goodStep1
      =
    tr.badStep1 := by
  classical

  change
    qs.eval
        (step1
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
        ψ
      -
      tr.goodStep1
      =
      tr.badStep1

  rw [tr.full_step1_eq]
  simp only [Alg1Trace.goodStep1, Alg1Trace.badStep1]

  have hsplit : ∀ b : qs.Basis, (∑ t : Fin (ASize cfg.env.work.active), tr.phaseCoeff b t •
            qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b)) = (∑ t ∈ alg1GoodLabels cfg b,
          tr.phaseCoeff b t • qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b)) + ∑ t ∈ Finset.univ.filter
            (fun t => t ∉ alg1GoodLabels cfg b), tr.phaseCoeff b t •
            qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
    intro b

    let p : Fin (ASize cfg.env.work.active) → Prop :=
      fun t => t ∈ alg1GoodLabels cfg b

    have hgood :
        Finset.univ.filter p = alg1GoodLabels cfg b := by
      ext t
      simp [p]

    have h :=
      sum_filter_add_sum_filter_not
        Finset.univ
        p
        (fun t =>
          tr.phaseCoeff b t •
            qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b))

    rw [hgood] at h
    exact h.symm

  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [hsplit b, smul_add]
  abel

/--
Canonical form of the state after Steps 3 and 4.

Each branch is the ideal output value written into the grown data register on
top of the corresponding Step-1 work label, weighted by the canonical phase
coefficient.
-/
lemma alg1_trace_afterStep34Full_eq_canonical (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    {η : ℝ} (cfg : ModMulConfig η) (ψ : qs.State) (tr : Alg1Trace qs cfg ψ) : tr.afterStep34Full = ∑ b ∈ tr.support,
      tr.inputCoeff b • ∑ t : Fin (ASize cfg.env.work.active), alg1PhaseCoeff qs cfg b t • qs.ket
              (RegEncoding.writeNat ((cfg.env.data.grow 1).active) (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work.active t.1 b)) := by
  classical
  simp only [Alg1Trace.afterStep34Full]
  apply Finset.sum_congr rfl
  intro b hb

  by_cases hzero : tr.inputCoeff b = 0
  · simp [hzero]
  ·
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [alg1_trace_phaseCoeff_eq_alg1PhaseCoeff
      qs cfg ψ tr b hb hzero t]

/-- Section-local restatement of the orthogonal Pythagoras lemma. -/
private lemma qpe_norm_sq_sum_eq_sum_norm_sq_of_orthogonal {qs : QSemantics} {ι : Type v} (s : Finset ι)
    (f : ι → qs.State) (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (f i) (f j) = 0) : ‖∑ i ∈ s, f i‖ ^ 2 =
    ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  revert horth
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | insert a s ha ih =>
      intro horth

      have horth_s : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
            inner ℂ (f i) (f j) = 0 := by
        intro i hi j hj hij
        exact horth i
          (Finset.mem_insert_of_mem hi)
          j
          (Finset.mem_insert_of_mem hj)
          hij

      have hih : ‖∑ i ∈ s, f i‖ ^ 2 =
          ∑ i ∈ s, ‖f i‖ ^ 2 :=
        ih horth_s

      have hcross :
          inner ℂ (f a) (∑ i ∈ s, f i) = 0 := by
        rw [inner_sum]
        refine Finset.sum_eq_zero ?_
        intro b hb
        apply horth a (by simp) b (Finset.mem_insert_of_mem hb)
        intro hab
        subst b
        exact ha hb

      calc
        ‖∑ i ∈ insert a s, f i‖ ^ 2
            =
          ‖f a + ∑ i ∈ s, f i‖ ^ 2 := by
            rw [Finset.sum_insert ha]
        _ =
          ‖f a‖ ^ 2
            + 2 * Complex.re (inner ℂ (f a) (∑ i ∈ s, f i))
            + ‖∑ i ∈ s, f i‖ ^ 2 := by
              exact norm_add_sq (𝕜 := ℂ) _ _
        _ =
          ‖f a‖ ^ 2 + ‖∑ i ∈ s, f i‖ ^ 2 := by
            rw [hcross]
            simp
        _ =
          ‖f a‖ ^ 2 + ∑ i ∈ s, ‖f i‖ ^ 2 := by
            rw [hih]
        _ =
          ∑ i ∈ insert a s, ‖f i‖ ^ 2 := by
            rw [Finset.sum_insert ha]

/--
The squared norm of the discarded packet is the trace bad mass.

The packet is a double sum over branches and bad labels. Injectivity of the
work writes makes all of these basis states pairwise distinct, hence
orthogonal, so Pythagoras turns the norm into the weighted sum of squared
coefficients that defines `alg1TraceBadMass`.
-/
lemma alg1_badStep1_norm_sq_eq_trace_bad_mass (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs]
    {η : ℝ} (cfg : ModMulConfig η) (ψ : qs.State) (tr : Alg1Trace qs cfg ψ) :
    ‖tr.badStep1‖ ^ 2 = alg1TraceBadMass qs cfg tr := by
  classical

  let Sbad : Finset (Σ b : qs.Basis, Fin (ASize cfg.env.work.active)) :=
    tr.support.sigma fun b =>
      Finset.univ.filter (fun t => t ∉ alg1GoodLabels cfg b)

  let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work.active)) → ℂ :=
    fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2

  let label : (Σ _b : qs.Basis, Fin (ASize cfg.env.work.active)) → qs.Basis :=
    fun i =>
      RegEncoding.writeNat cfg.env.work.active i.2.1 i.1

  have hflat : tr.badStep1 =
      ∑ i ∈ Sbad, α i • qs.ket (label i) := by
    simp [
      Sbad, α, label,
      Alg1Trace.badStep1,
      Finset.sum_sigma,
      Finset.smul_sum,
      smul_smul
    ]

  have hwrite_inj : ∀ i ∈ Sbad, ∀ j ∈ Sbad,
        label i = label j → i = j := by
    intro i hi j hj hEq

    rcases Finset.mem_sigma.mp hi with ⟨hi_b, _hi_t⟩
    rcases Finset.mem_sigma.mp hj with ⟨hj_b, _hj_t⟩

    have ht_val : i.2.1 = j.2.1 := by
      calc
        i.2.1
            =
          RegEncoding.toNat cfg.env.work.active
            (RegEncoding.writeNat cfg.env.work.active i.2.1 i.1) := by
              symm
              exact
                RegEncoding.toNat_writeNat_of_lt
                  cfg.env.work.active i.2.1 i.1 i.2.isLt
        _ =
          RegEncoding.toNat cfg.env.work.active
            (RegEncoding.writeNat cfg.env.work.active j.2.1 j.1) := by
              simpa [label] using
                congrArg (RegEncoding.toNat cfg.env.work.active) hEq
        _ = j.2.1 := by
              exact
                RegEncoding.toNat_writeNat_of_lt
                  cfg.env.work.active j.2.1 j.1 j.2.isLt

    have ht : i.2 = j.2 :=
      Fin.ext ht_val

    have hi_work :
        RegEncoding.toNat cfg.env.work.active i.1 = 0 :=
      (tr.input_good i.1 hi_b).2.2.1

    have hj_work :
        RegEncoding.toNat cfg.env.work.active j.1 = 0 :=
      (tr.input_good j.1 hj_b).2.2.1

    have hi_zero :
        RegEncoding.writeNat cfg.env.work.active 0 i.1 = i.1 := by
      simpa [hi_work] using
        (RegEncoding.writeNat_toNat cfg.env.work.active i.1)

    have hj_zero :
        RegEncoding.writeNat cfg.env.work.active 0 j.1 = j.1 := by
      simpa [hj_work] using
        (RegEncoding.writeNat_toNat cfg.env.work.active j.1)

    have hb : i.1 = j.1 := by
      calc
        i.1
            =
          RegEncoding.writeNat cfg.env.work.active 0 i.1 := hi_zero.symm
        _ =
          RegEncoding.writeNat cfg.env.work.active 0
            (RegEncoding.writeNat cfg.env.work.active i.2.1 i.1) := by
              symm
              exact
                qpe_writeNat_overwrite_same_reg
                  cfg.env.work.active 0 i.2.1 i.1
        _ =
          RegEncoding.writeNat cfg.env.work.active 0
            (RegEncoding.writeNat cfg.env.work.active j.2.1 j.1) := by
              exact
                congrArg (RegEncoding.writeNat cfg.env.work.active 0) hEq
        _ =
          RegEncoding.writeNat cfg.env.work.active 0 j.1 := by
              exact
                qpe_writeNat_overwrite_same_reg
                  cfg.env.work.active 0 j.2.1 j.1
        _ = j.1 := hj_zero

    cases i
    cases j
    simp at hb ht ⊢
    exact ⟨hb, ht⟩

  have hlabel_inj : ∀ i ∈ Sbad, ∀ j ∈ Sbad, i ≠ j →
        label i ≠ label j := by
    intro i hi j hj hij hEq
    exact hij (hwrite_inj i hi j hj hEq)

  have horth : ∀ i ∈ Sbad, ∀ j ∈ Sbad, i ≠ j → inner ℂ (α i • qs.ket (label i)) (α j • qs.ket (label j)) =
        0 := by
    intro i hi j hj hij
    rw [
      inner_smul_left,
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne (hlabel_inj i hi j hj hij)
    ]
    simp

  have hsq : ‖∑ i ∈ Sbad, α i • qs.ket (label i)‖ ^ 2 =
      ∑ i ∈ Sbad, ‖α i • qs.ket (label i)‖ ^ 2 :=
    qpe_norm_sq_sum_eq_sum_norm_sq_of_orthogonal
      (qs := qs)
      Sbad
      (fun i => α i • qs.ket (label i))
      horth

  calc
    ‖tr.badStep1‖ ^ 2
        =
      ‖∑ i ∈ Sbad, α i • qs.ket (label i)‖ ^ 2 := by
        rw [hflat]
    _ =
      ∑ i ∈ Sbad, ‖α i • qs.ket (label i)‖ ^ 2 :=
        hsq
    _ =
      ∑ i ∈ Sbad,
        ‖tr.inputCoeff i.1‖ ^ 2
          *
        ‖tr.phaseCoeff i.1 i.2‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [α, norm_smul, ket_norm_one qs, mul_one]
        rw [norm_mul]
        ring
    _ = alg1TraceBadMass qs cfg tr := by
        unfold alg1TraceBadMass
        simp only [Sbad, Finset.sum_sigma]
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.mul_sum]

/--
Main endpoint of this section: the squared Step-1 error is the trace bad mass.

Combining `alg1_step1_error_eq_bad_packet` with
`alg1_badStep1_norm_sq_eq_trace_bad_mass` reduces the operator-level question
"how far is Step 1 from its idealization" to the purely numerical question
bounded in the rest of the file.
-/
lemma alg1_step1_error_sq_eq_trace_bad_mass (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] {η : ℝ}
    (cfg : ModMulConfig η) (ψ : qs.State) (tr : Alg1Trace qs cfg ψ) :
    ‖qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
        - tr.goodStep1‖ ^ 2
      =
    alg1TraceBadMass qs cfg tr := by
  rw [
    alg1_step1_error_eq_bad_packet qs cfg ψ tr,
    alg1_badStep1_norm_sq_eq_trace_bad_mass qs cfg ψ tr
  ]

end TraceBadMassAndStep1Error

/-! =========================================================
    Step-5 cleanup residue

Step 5 uncomputes the Step-1 load by loading the constant `step5Constant c N`
against the already-multiplied data register. These two lemmas check that the
composite residue is exactly `alg1TargetResidue`, so the cleanup phase is the
inverse of the load phase modulo `N`.
========================================================= -/

section Step5CleanupResidue

/--
The Step-5 constant multiplied against the Step-1 output residue reproduces the
target residue modulo `N`.

Coprimality of `c` with `N` is what makes `step5Constant c N` act as the
required inverse factor.
-/
private lemma step5Constant_mul_output_mod_eq_target (c N x : ℕ) (hN : 1 < N) (hcoprime : Nat.Coprime c N) :
    (step5Constant c N * ((c * x) % N)) % N =
    (((c + N - 1) % N) * x) % N := by
  classical

  rcases step5Constant_ok c N hN hcoprime with
    ⟨cinv, hcinv_lt, hcinv, hk⟩

  let k : ℕ := step5Constant c N
  let d : ℕ := (c + N - 1) % N

  have hNpos : 0 < N :=
    Nat.lt_trans Nat.zero_lt_one hN

  have hcinv_mod :
      Nat.ModEq N (c * cinv) 1 := by
    change (c * cinv) % N = 1 % N
    exact hcinv

  have hk_mod :
      Nat.ModEq N k (1 + N - cinv) := by
    change k % N = (1 + N - cinv) % N
    exact hk

  have hsum :
      Nat.ModEq N (k + cinv) 1 := by
    calc
      k + cinv
          ≡ (1 + N - cinv) + cinv [MOD N] :=
        Nat.ModEq.add_right cinv hk_mod
      _ = 1 + N := by
        omega
      _ ≡ 1 [MOD N] := by
        change (1 + N) % N = 1 % N
        simp

  have hsum_mul :
      Nat.ModEq N (k * c + cinv * c) c := by
    have h := Nat.ModEq.mul_right c hsum
    simpa [Nat.add_mul, Nat.mul_one] using h

  have hcinv_comm :
      Nat.ModEq N (cinv * c) 1 := by
    simpa [Nat.mul_comm] using hcinv_mod

  have hk_mul_add_one :
      Nat.ModEq N (k * c + 1) c := by
    calc
      k * c + 1
          ≡ k * c + cinv * c [MOD N] :=
        Nat.ModEq.add_left (k * c) hcinv_comm.symm
      _ ≡ c [MOD N] := hsum_mul

  have hd_add_one :
      Nat.ModEq N (d + 1) c := by
    calc
      d + 1
          ≡ (c + N - 1) + 1 [MOD N] :=
        Nat.ModEq.add_right 1 (Nat.mod_modEq (c + N - 1) N)
      _ = c + N := by
        omega
      _ ≡ c [MOD N] := by
        change (c + N) % N = c % N
        simp

  have hkc :
      Nat.ModEq N (k * c) d := by
    apply Nat.ModEq.add_right_cancel' 1
    calc
      k * c + 1
          ≡ c [MOD N] := hk_mul_add_one
      _ ≡ d + 1 [MOD N] := hd_add_one.symm

  have hfinal :
      Nat.ModEq N (k * ((c * x) % N)) (d * x) := by
    calc
      k * ((c * x) % N)
          ≡ k * (c * x) [MOD N] :=
        Nat.ModEq.mul_left k (Nat.mod_modEq (c * x) N)
      _ = (k * c) * x := by
        ring
      _ ≡ d * x [MOD N] :=
        Nat.ModEq.mul_right x hkc

  change Nat.ModEq N (k * ((c * x) % N)) (d * x)
  exact hfinal

/--
The controlled Step-5 cleanup residue equals `alg1TargetResidue`.

Uncontrolled branches contribute residue zero, which is also the value of
`alg1TargetResidue` there.
-/
lemma alg1_step5_cleanup_residue_eq_target (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModMulConfig η)
    (b : qs.Basis): (if RegEncoding.bit cfg.ctrl b then
        (step5Constant cfg.c cfg.env.N * alg1OutputValue cfg b) % cfg.env.N else 0) =
    alg1TargetResidue cfg b := by
  classical
  by_cases hctrl : RegEncoding.bit cfg.ctrl b
  ·
    simpa [alg1OutputValue, alg1TargetResidue, hctrl] using
      step5Constant_mul_output_mod_eq_target
        cfg.c
        cfg.env.N
        (RegEncoding.toNat cfg.env.data.active b)
        cfg.env.modulus_gt_one
        cfg.coprime
  ·
    simp [alg1TargetResidue, hctrl]

end Step5CleanupResidue

/-! =========================================================
    Atomic encoding and phase lemmas

The smallest rewrites used by every packet computation below, split into a
register half and a scalar half. On the register side, writing the output value
into `data` agrees with writing it into the grown register, and the ideal gate
produces precisely that basis state. On the scalar side, the Step-1 and Step-5
phase scalars both collapse to the common `alg1TargetPhaseScalar`, which is the
statement that Step 5 undoes Step 1 at the level of phases.
========================================================= -/

section AtomicEncodingAndPhase

/--
On good inputs, writing the output value into `data` agrees with writing it into
the grown data register.

The extra high bit is fresh and the output value is below `N`, so it never
reaches that bit.
-/
lemma alg1_write_data_eq_extendHi_output (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModMulConfig η)
    (b : qs.Basis) (hb : GoodModMulBasisInput qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    RegEncoding.writeNat cfg.env.data.active (alg1OutputValue cfg b) b = RegEncoding.writeNat
        ((cfg.env.data.grow 1).active) (alg1OutputValue cfg b)
        b := by
  let m : SplitPoint ((cfg.env.data.grow 1).active) :=
    ⟨regSize cfg.env.data.active, by
      simp [ExtReg.grow, Reg.append, regSize, Reg.width]⟩

  have hout_data :
      alg1OutputValue cfg b < ASize cfg.env.data.active :=
    alg1OutputValue_lt_data_capacity cfg b hb

  have hout_left : alg1OutputValue cfg b <
      ASize (splitLeft ((cfg.env.data.grow 1).active) m) := by
    simpa [m, splitLeft, ExtReg.grow, Reg.append, Reg.take, regSize,
      Reg.width, ASize] using hout_data

  have hzero_right :
      0 < ASize (splitRight ((cfg.env.data.grow 1).active) m) := by
    simp [m, splitRight, ExtReg.grow, Reg.append, Reg.drop, ExtReg.newBits,
      regSize, Reg.width, ASize]

  have hsplit_raw :=
    RegEncoding.writeNat_split
      ((cfg.env.data.grow 1).active)
      m
      0
      (alg1OutputValue cfg b)
      b
      hout_left
      hzero_right

  have hsplit : RegEncoding.writeNat ((cfg.env.data.grow 1).active) (alg1OutputValue cfg b) b = RegEncoding.writeNat
          (cfg.env.data.newBits 1) 0 (RegEncoding.writeNat cfg.env.data.active (alg1OutputValue cfg b)
            b) := by
    simpa [m, splitLeft, splitRight, ExtReg.grow, ExtReg.newBits,
      ExtReg.remainingReserve, Reg.append, Reg.take, Reg.drop, regSize,
      Reg.width, ASize] using hsplit_raw

  have hfresh1 : cfg.env.data.FreshFor 1 b :=
    ExtReg.freshFor_one_of_two
      cfg.env.data
      b
      cfg.env.circuit_workspace.1
      hb.2.1

  have hfresh_after : cfg.env.data.FreshFor 1 (RegEncoding.writeNat cfg.env.data.active (alg1OutputValue cfg b)
          b) :=
    ExtReg.freshFor_write_active
      cfg.env.data
      1
      (alg1OutputValue cfg b)
      b
      hfresh1

  have hclear : RegEncoding.writeNat (cfg.env.data.newBits 1) 0 (RegEncoding.writeNat cfg.env.data.active
            (alg1OutputValue cfg b) b) = RegEncoding.writeNat cfg.env.data.active (alg1OutputValue cfg b)
        b := by
    rw [← hfresh_after]
    exact
      RegEncoding.writeNat_toNat
        (cfg.env.data.newBits 1)
        (RegEncoding.writeNat
          cfg.env.data.active
          (alg1OutputValue cfg b)
          b)

  rw [hsplit, hclear]

/--
The ideal controlled modular multiplication sends a good basis state to the
basis state holding `alg1OutputValue` in the grown data register.
-/
lemma alg1_ideal_ket_eq_extended_output (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs]
    [IdealCtrlModMulExactSemantics qs] {η : ℝ} (cfg : ModMulConfig η) (b : qs.Basis) (hb : GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) : qs.eval (ModMulConfig.idealGate cfg) (qs.ket b) =
    qs.ket (RegEncoding.writeNat ((cfg.env.data.grow 1).active) (alg1OutputValue cfg b)
        b) := by
  rw [IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_cfg qs cfg b hb]
  congr 1
  exact alg1_write_data_eq_extendHi_output qs cfg b hb

/--
The modular load phase only depends on the loaded value modulo `N`.

Congruent values differ by a multiple of `N`, which contributes a full turn of
`2 * π` per unit of the work label.
-/
lemma alg1_exp_phase_eq_of_modEq (N u v z : ℕ) (hN : 0 < N) (huv : Nat.ModEq N u v) : Complex.exp
      (((2 * Real.pi) / (N : ℝ)) * Complex.I * ((u : ℂ) * (z : ℂ))) = Complex.exp
      (((2 * Real.pi) / (N : ℝ)) * Complex.I *
        ((v : ℂ) * (z : ℂ))) := by
  have hphase (x y : ℕ) : Complex.exp (((2 * Real.pi) / (N : ℝ)) * Complex.I * ((x : ℂ) * (y : ℂ))) =
      qftPhase N x y := by
    simp [qftPhase, ωPow, ω, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

  have hroot : (ω N) ^ N = 1 := by
    have hN0 : (N : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hN
    unfold ω
    rw [← Complex.exp_nat_mul]
    have harg : (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) =
        Complex.I * ((Real.pi : ℂ) * 2) := by
      field_simp [hN0, mul_assoc, mul_left_comm, mul_comm]
    rw [harg]
    simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.exp_two_pi_mul_I

  have hpow_mod :
      ∀ a b : ℕ, Nat.ModEq N a b → (ω N) ^ a = (ω N) ^ b := by
    intro a b hab
    have hrem : a % N = b % N := by
      simpa [Nat.ModEq] using hab
    calc
      (ω N) ^ a
          =
        (ω N) ^ (a % N + N * (a / N)) := by
          rw [Nat.mod_add_div a N]
      _ =
        (ω N) ^ (a % N) := by
          rw [pow_add, pow_mul, hroot]
          simp
      _ =
        (ω N) ^ (b % N) := by
          rw [hrem]
      _ =
        (ω N) ^ (b % N + N * (b / N)) := by
          rw [pow_add, pow_mul, hroot]
          simp
      _ =
        (ω N) ^ b := by
          rw [Nat.mod_add_div b N]

  have hpow :
      (ω N) ^ (u * z) = (ω N) ^ (v * z) :=
    hpow_mod (u * z) (v * z) (Nat.ModEq.mul_right z huv)

  calc
    Complex.exp
        (((2 * Real.pi) / (N : ℝ)) * Complex.I *
          ((u : ℂ) * (z : ℂ)))
      =
    qftPhase N u z := hphase u z
    _ =
    qftPhase N v z := by
      simpa [qftPhase, ωPow] using hpow
    _ =
    Complex.exp
        (((2 * Real.pi) / (N : ℝ)) * Complex.I *
          ((v : ℂ) * (z : ℂ))) :=
      (hphase v z).symm

/-- The Step-1 phase scalar is the target phase scalar. -/
lemma alg1_step1_phase_scalar_eq_target (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModMulConfig η)
    (b : qs.Basis) (z : Fin (ASize cfg.env.work.active)) : alg1Step1PhaseScalar cfg b z =
    alg1TargetPhaseScalar cfg b z := by
  classical
  by_cases hctrl : RegEncoding.bit cfg.ctrl b
  ·
    let a : ℕ := (cfg.c + cfg.env.N - 1) % cfg.env.N
    let x : ℕ := RegEncoding.toNat cfg.env.data.active b
    let r : ℕ := alg1TargetResidue cfg b
    let N : ℕ := cfg.env.N

    have hNpos : 0 < N := by
      dsimp [N]
      exact Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

    have hr :
        r = (a * x) % N := by
      simp [r, a, x, N, alg1TargetResidue, hctrl]

    have hmod :
        Nat.ModEq N (a * x) r := by
      rw [hr]
      exact (Nat.mod_modEq (a * x) N).symm

    have hphase : Angle.toReal (alg1Step1Phase cfg) =
        (2 * Real.pi * (a : ℝ)) / (N : ℝ) := by
      simp only [alg1Step1Phase, Angle.toReal, a, N]
      push_cast
      ring

    simp only [
      alg1Step1PhaseScalar,
      alg1TargetPhaseScalar,
      hctrl,
      if_true
    ]

    calc
      Complex.exp
          (((Angle.toReal (alg1Step1Phase cfg) : ℝ) : ℂ) * Complex.I *
            ((RegEncoding.toNat cfg.env.data.active b : ℂ) * (z.1 : ℂ)))
        =
      Complex.exp
        (((2 * Real.pi) / (N : ℝ)) *
          Complex.I *
          (((a * x : ℕ) : ℂ) * (z.1 : ℂ))) := by
          congr 1
          rw [hphase]
          dsimp [x]
          push_cast
          ring
      _ =
      Complex.exp
        (((2 * Real.pi) / (N : ℝ)) *
          Complex.I *
          ((r : ℂ) * (z.1 : ℂ))) :=
        alg1_exp_phase_eq_of_modEq N (a * x) r z.1 hNpos hmod

  ·
    simp [
      alg1Step1PhaseScalar,
      alg1TargetPhaseScalar,
      hctrl
    ]

/-- The forward Step-5 phase scalar is also the target phase scalar. -/
lemma alg1_step5_phase_scalar_eq_target (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModMulConfig η)
    (b : qs.Basis) (_hb : GoodModMulBasisInput qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (z : Fin (ASize cfg.env.work.active)) : (if RegEncoding.bit cfg.ctrl b then Complex.exp
        (((Angle.toReal (alg1Step5Phase cfg) : ℝ) : ℂ) * Complex.I * ((alg1OutputValue cfg b : ℂ) * (z.1 : ℂ))) else
      1) =
    alg1TargetPhaseScalar cfg b z := by
  classical
  by_cases hctrl : RegEncoding.bit cfg.ctrl b
  ·
    let k : ℕ := step5Constant cfg.c cfg.env.N
    let x : ℕ := alg1OutputValue cfg b
    let r : ℕ := alg1TargetResidue cfg b
    let N : ℕ := cfg.env.N

    have hNpos : 0 < N := by
      dsimp [N]
      exact Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

    have hr_lt : r < N := by
      dsimp [r, N]
      exact alg1TargetResidue_lt_N cfg b

    have hcleanup :
        (k * x) % N = r := by
      have h :=
        alg1_step5_cleanup_residue_eq_target
          qs
          cfg
          b
      simpa [k, x, r, N, hctrl] using h

    have hraw :
        Nat.ModEq N (k * x) r := by
      change (k * x) % N = r % N
      rw [hcleanup, Nat.mod_eq_of_lt hr_lt]

    have hmod_left :
        Nat.ModEq N ((k % N) * x) (k * x) :=
      Nat.ModEq.mul_right x (Nat.mod_modEq k N)

    have hmod :
        Nat.ModEq N ((k % N) * x) r :=
      hmod_left.trans hraw

    have hphase : Angle.toReal (alg1Step5Phase cfg) =
        (2 * Real.pi * ((k % N : ℕ) : ℝ)) / (N : ℝ) := by
      simp only [alg1Step5Phase, Angle.toReal, k, N]
      push_cast
      ring

    simp only [
      alg1TargetPhaseScalar,
      hctrl,
      if_true
    ]

    calc
      Complex.exp
          (((Angle.toReal (alg1Step5Phase cfg) : ℝ) : ℂ) * Complex.I *
            ((alg1OutputValue cfg b : ℂ) * (z.1 : ℂ)))
        =
      Complex.exp
        (((2 * Real.pi) / (N : ℝ)) *
          Complex.I *
          ((((k % N) * x : ℕ) : ℂ) * (z.1 : ℂ))) := by
          congr 1
          rw [hphase]
          dsimp [x]
          push_cast
          ring
      _ =
      Complex.exp
        (((2 * Real.pi) / (N : ℝ)) *
          Complex.I *
          ((r : ℂ) * (z.1 : ℂ))) :=
        alg1_exp_phase_eq_of_modEq N ((k % N) * x) r z.1 hNpos hmod

  ·
    simp [
      alg1TargetPhaseScalar,
      hctrl
    ]

/--
Step 5 reproduces the Step-1 phase scalar exactly.

Immediate from the previous two lemmas, both sides being
`alg1TargetPhaseScalar`. This is the phase-level form of "Step 5 uncomputes
Step 1".
-/
lemma alg1_step5_phase_scalar_eq_step1 (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModMulConfig η)
    (b : qs.Basis) (hb : GoodModMulBasisInput qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (z : Fin (ASize cfg.env.work.active)) : (if RegEncoding.bit cfg.ctrl b then Complex.exp
        (((Angle.toReal (alg1Step5Phase cfg) : ℝ) : ℂ) * Complex.I * ((alg1OutputValue cfg b : ℂ) * (z.1 : ℂ))) else
      1) =
    alg1Step1PhaseScalar cfg b z := by
  rw [
    alg1_step5_phase_scalar_eq_target qs cfg b hb z,
    alg1_step1_phase_scalar_eq_target qs cfg b z
  ]

end AtomicEncodingAndPhase

/-! =========================================================
    Local diagonal semantics

The controlled phase product is diagonal in the work label, but only once the
relevant registers are known to be disjoint and its workspace is known to be
clean. The private lemmas here discharge those layout side conditions from the
`ModMulConfig` workspace data; the two public lemmas then evaluate the Step-1
and forward Step-5 phase gates on a single work basis label, in both cases
producing the scalar `alg1Step1PhaseScalar`.
========================================================= -/

section LocalDiagonalSemantics

/-- The data and work registers are disjoint. -/
private lemma alg1_data_work_active_disjoint {η : ℝ} (cfg : ModMulConfig η) :
    Shor.Disjoint cfg.env.data.active cfg.env.work.active := by
  rw [Shor.Disjoint, List.disjoint_left]
  intro q hqData hqWork
  have h := cfg.layout.1
  rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h
  exact h
    (List.mem_append_left _ hqData)
    (List.mem_append_left _ hqWork)

/-- The grown data register is still disjoint from the work register. -/
private lemma alg1_dataCarry_work_active_disjoint {η : ℝ} (cfg : ModMulConfig η) :
    Shor.Disjoint (cfg.env.data.grow 1).active cfg.env.work.active := by
  rw [Shor.Disjoint, List.disjoint_left]
  intro q hqData hqWork
  have h := cfg.env.circuit_workspace.dataCarry_work_disjoint
  rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h
  exact h
    (List.mem_append_left _ hqData)
    (List.mem_append_left _ hqWork)

/-- The control qubit lies outside the work register. -/
private lemma alg1_ctrl_notin_work_active {η : ℝ} (cfg : ModMulConfig η) :
    cfg.ctrl ∉ cfg.env.work.active.qubits := by
  intro hq
  exact cfg.layout.2.2.2.2.1 (List.mem_append_left _ hq)

/-- The control qubit lies outside the grown data register. -/
private lemma alg1_ctrl_notin_dataCarry_active {η : ℝ} (cfg : ModMulConfig η) :
    cfg.ctrl ∉ (cfg.env.data.grow 1).active.qubits := by
  intro hq
  apply cfg.layout.2.2.2.1
  have howned : cfg.ctrl ∈ (cfg.env.data.grow 1).ownedQubits :=
    List.mem_append_left _ hq
  simpa [Gate.ExtReg.ownedQubits_grow] using howned

/-- List identity relating the two ways of naming the second fresh bit. -/
private lemma qpe_take_two_tail_eq_tail_take_one {α : Type*} (xs : List α) :
    (xs.take 2).tail = xs.tail.take 1 := by
  cases xs with
  | nil => simp
  | cons a xs =>
      cases xs <;> simp

/--
Two fresh bits minus one consumed bit leaves one fresh bit.

Step 5 runs on the register already grown by the Step-1 carry, so it needs the
freshness hypothesis transported across that growth.
-/
private lemma alg1_grow_one_freshFor_one_of_two {Basis : Type u} [RegEncoding Basis] (e : ExtReg) (b : Basis)
    (hcap : e.CanGrow 2) (hfresh : e.FreshFor 2 b) :
    (e.grow 1).FreshFor 1 b := by
  unfold ExtReg.FreshFor FreshZero at hfresh ⊢

  let r2 : Reg := e.newBits 2
  have hr2 : regSize r2 = 2 := by
    simp [r2, ExtReg.newBits, Reg.take, regSize, Reg.width,
      ExtReg.CanGrow, ExtReg.capacity] at hcap ⊢
    omega

  let m : SplitPoint r2 := ⟨1, by omega⟩

  have hsplit :=
    RegEncoding.toNat_split
      (r := r2)
      (m := m)
      (b := b)

  have hright :
      splitRight r2 m = (e.grow 1).newBits 1 := by
    cases e
    simp [r2, m, splitRight, ExtReg.grow, ExtReg.newBits,
      ExtReg.remainingReserve, Reg.drop, Reg.take,
      qpe_take_two_tail_eq_tail_take_one]

  have hr2zero : RegEncoding.toNat r2 b = 0 := by
    simpa [r2] using hfresh

  dsimp at hsplit
  rw [hr2zero] at hsplit

  have hzero : RegEncoding.toNat (splitRight r2 m) b = 0 := by
    have hmul :
        ASize (splitLeft r2 m) * RegEncoding.toNat (splitRight r2 m) b = 0 := by
      omega
    rcases Nat.mul_eq_zero.mp hmul with hleft | hrightZero
    · have hpos : 0 < ASize (splitLeft r2 m) := by
        simp [ASize]
      omega
    · exact hrightZero

  simpa [hright] using hzero

/--
The Step-1 CPhaseProd action on one work basis label.

Proof: apply `GateSemanticsFacts.eval_CPhaseProd_ket`, then use:
* `data` and `work` disjoint;
* `ctrl` outside `work`;
* `toNat work (write work z b) = z`.
-/
lemma alg1_step1_cphase_on_work_label (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] {η : ℝ}
    (cfg : ModMulConfig η) (b : qs.Basis) (hb : GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) (z : Fin (ASize cfg.env.work.active)) : qs.eval
        (Gate.CPhaseProdUsing cfg.ctrl (alg1Step1Phase cfg) cfg.env.data.active cfg.env.work.active
          cfg.env.circuit_workspace.step1Workspace) (qs.ket (RegEncoding.writeNat cfg.env.work.active z.1 b)) =
    alg1Step1PhaseScalar cfg b z • qs.ket
        (RegEncoding.writeNat cfg.env.work.active z.1 b) := by
  have hdatawork := alg1_data_work_active_disjoint cfg

  have hctrl : RegEncoding.bit cfg.ctrl (RegEncoding.writeNat cfg.env.work.active z.1 b) =
      RegEncoding.bit cfg.ctrl b :=
    RegEncoding.bit_writeNat_out
      (r := cfg.env.work.active)
      (v := z.1)
      (b := b)
      (q := cfg.ctrl)
      (alg1_ctrl_notin_work_active cfg)

  have hdata : RegEncoding.toNat cfg.env.data.active (RegEncoding.writeNat cfg.env.work.active z.1 b) =
      RegEncoding.toNat cfg.env.data.active b :=
    RegEncoding.toNat_left_write_right
      cfg.env.data.active
      cfg.env.work.active
      hdatawork
      b
      z.1

  have hwork : RegEncoding.toNat cfg.env.work.active (RegEncoding.writeNat cfg.env.work.active z.1 b) =
      z.1 :=
    RegEncoding.toNat_writeNat_of_lt
      cfg.env.work.active
      z.1
      b
      z.isLt

  rw [
    GateSemanticsFacts.eval_CPhaseProdUsing_ket
      qs
      cfg.ctrl
      (alg1Step1Phase cfg)
      cfg.env.data.active
      cfg.env.work.active
      cfg.env.circuit_workspace.step1Workspace
      (RegEncoding.writeNat cfg.env.work.active z.1 b)
      (step1Workspace_clean_write qs cfg b hb z)
  ]
  simp [alg1Step1PhaseScalar, hctrl, hdata, hwork]

/--
The forward Step-5 CPhaseProd action on one work label.

The output basis has the desired modular result in the grown data register; this
lemma identifies its diagonal scalar with the original Step-1 scalar. -/
lemma alg1_step5_cphase_on_output_work_label (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    {η : ℝ} (cfg : ModMulConfig η) (b : qs.Basis) (hb : GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) (z : Fin (ASize cfg.env.work.active)) : qs.eval
        (Gate.CPhaseProdUsing cfg.ctrl (alg1Step5Phase cfg) ((cfg.env.data.grow 1).active) cfg.env.work.active
          cfg.env.circuit_workspace.step5Workspace) (qs.ket (RegEncoding.writeNat cfg.env.work.active z.1
            (RegEncoding.writeNat ((cfg.env.data.grow 1).active) (alg1OutputValue cfg b) b))) =
    alg1Step1PhaseScalar cfg b z • qs.ket (RegEncoding.writeNat cfg.env.work.active z.1 (RegEncoding.writeNat
            ((cfg.env.data.grow 1).active) (alg1OutputValue cfg b)
            b)) := by
  let bData : qs.Basis :=
    RegEncoding.writeNat
      ((cfg.env.data.grow 1).active)
      (alg1OutputValue cfg b)
      b

  have hdatawork := alg1_dataCarry_work_active_disjoint cfg

  have hout_lt :
      alg1OutputValue cfg b < ASize ((cfg.env.data.grow 1).active) := by
    have hout_data :
        alg1OutputValue cfg b < ASize cfg.env.data.active :=
      alg1OutputValue_lt_data_capacity cfg b hb
    have hle :
        ASize cfg.env.data.active ≤ ASize ((cfg.env.data.grow 1).active) := by
      simpa [ASize, ExtReg.grow, Reg.append, regSize, Reg.width] using
        (Nat.pow_le_pow_right
          (by norm_num : 0 < 2)
          (Nat.le_add_right
            cfg.env.data.active.qubits.length
            (cfg.env.data.newBits 1).qubits.length))
    exact lt_of_lt_of_le hout_data hle

  have hctrl_ext :
      RegEncoding.bit cfg.ctrl bData = RegEncoding.bit cfg.ctrl b := by
    dsimp [bData]
    exact
      RegEncoding.bit_writeNat_out
        (r := (cfg.env.data.grow 1).active)
        (v := alg1OutputValue cfg b)
        (b := b)
        (q := cfg.ctrl)
        (alg1_ctrl_notin_dataCarry_active cfg)

  have hctrl : RegEncoding.bit cfg.ctrl (RegEncoding.writeNat cfg.env.work.active z.1 bData) =
      RegEncoding.bit cfg.ctrl b := by
    calc
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat cfg.env.work.active z.1 bData)
          = RegEncoding.bit cfg.ctrl bData :=
            RegEncoding.bit_writeNat_out
              (r := cfg.env.work.active)
              (v := z.1)
              (b := bData)
              (q := cfg.ctrl)
              (alg1_ctrl_notin_work_active cfg)
      _ = RegEncoding.bit cfg.ctrl b := hctrl_ext

  have hdata : RegEncoding.toNat ((cfg.env.data.grow 1).active) (RegEncoding.writeNat cfg.env.work.active z.1 bData)
        =
      alg1OutputValue cfg b := by
    calc
      RegEncoding.toNat ((cfg.env.data.grow 1).active)
          (RegEncoding.writeNat cfg.env.work.active z.1 bData)
          = RegEncoding.toNat ((cfg.env.data.grow 1).active) bData := by
            exact
              RegEncoding.toNat_left_write_right
                ((cfg.env.data.grow 1).active)
                cfg.env.work.active
                hdatawork
                bData
                z.1
      _ = alg1OutputValue cfg b := by
            dsimp [bData]
            exact
              RegEncoding.toNat_writeNat_of_lt
                ((cfg.env.data.grow 1).active)
                (alg1OutputValue cfg b)
                b
                hout_lt

  have hwork : RegEncoding.toNat cfg.env.work.active (RegEncoding.writeNat cfg.env.work.active z.1 bData) =
      z.1 :=
    RegEncoding.toNat_writeNat_of_lt
      cfg.env.work.active
      z.1
      bData
      z.isLt

  have hdataFresh0 : (cfg.env.data.grow 1).FreshFor 1 b :=
    alg1_grow_one_freshFor_one_of_two
      cfg.env.data
      b
      cfg.env.circuit_workspace.1
      hb.2.1

  have hdataFresh1 : (cfg.env.data.grow 1).FreshFor 1 bData := by
    dsimp [bData]
    exact
      ExtReg.freshFor_write_active
        (cfg.env.data.grow 1)
        1
        (alg1OutputValue cfg b)
        b
        hdataFresh0

  have hdataFresh2 : (cfg.env.data.grow 1).FreshFor 1
        (RegEncoding.writeNat cfg.env.work.active z.1 bData) :=
    ExtReg.freshFor_write_active_of_ownedDisjoint
      (cfg.env.data.grow 1)
      cfg.env.work
      1
      z.1
      bData
      cfg.env.circuit_workspace.dataCarry_work_disjoint
      hdataFresh1

  have hworkFresh1 : cfg.env.work.FreshFor 1 bData := by
    dsimp [bData]
    exact
      ExtReg.freshFor_write_active_of_ownedDisjoint
        cfg.env.work
        (cfg.env.data.grow 1)
        1
        (alg1OutputValue cfg b)
        b
        cfg.env.circuit_workspace.work_dataCarry_disjoint
        hb.2.2.2.1

  have hworkFresh2 : cfg.env.work.FreshFor 1
        (RegEncoding.writeNat cfg.env.work.active z.1 bData) :=
    ExtReg.freshFor_write_active
      cfg.env.work
      1
      z.1
      bData
      hworkFresh1

  have hclean : cfg.env.circuit_workspace.step5Workspace.Clean
        (RegEncoding.writeNat cfg.env.work.active z.1 bData) := by
    change
      (cfg.env.data.grow 1).FreshFor 1
          (RegEncoding.writeNat cfg.env.work.active z.1 bData)
        ∧
      cfg.env.work.FreshFor 1
          (RegEncoding.writeNat cfg.env.work.active z.1 bData)
    exact ⟨hdataFresh2, hworkFresh2⟩

  rw [
    GateSemanticsFacts.eval_CPhaseProdUsing_ket
      qs
      cfg.ctrl
      (alg1Step5Phase cfg)
      ((cfg.env.data.grow 1).active)
      cfg.env.work.active
      cfg.env.circuit_workspace.step5Workspace
      (RegEncoding.writeNat cfg.env.work.active z.1 bData)
      hclean
  ]

  have hphase : (if RegEncoding.bit cfg.ctrl (RegEncoding.writeNat cfg.env.work.active z.1 bData) then Complex.exp
          (((Angle.toReal (alg1Step5Phase cfg) : ℝ) : ℂ) * Complex.I *
            ((RegEncoding.toNat ((cfg.env.data.grow 1).active)
                (RegEncoding.writeNat cfg.env.work.active z.1 bData) : ℂ) * (RegEncoding.toNat cfg.env.work.active
                (RegEncoding.writeNat cfg.env.work.active z.1 bData) : ℂ))) else 1) =
      alg1Step1PhaseScalar cfg b z := by
    rw [hctrl, hdata, hwork]
    exact alg1_step5_phase_scalar_eq_step1 qs cfg b hb z

  rw [hphase]

end LocalDiagonalSemantics

/-! =========================================================
    Exact packet algebra

Everything needed to run Step 1 forward on a basis state with no estimates. The
register Hadamards produce the uniform work superposition, the controlled phase
product multiplies each label by its diagonal scalar, and the inverse QFT mixes
the labels with the explicit coefficient `alg1IQFTCoeff`. Composing the three
identifies the canonical `alg1PhaseCoeff` with the closed-form Fourier
coefficient `alg1FractionalLoadCoeff`, which is the last step before the
analysis becomes purely numerical.
========================================================= -/

section ExactPacketAlgebra

/-- Section-local restatement of `writeNat_overwrite_same_reg`. -/
private lemma writeNat_overwrite_same_reg_step5 {Basis : Type*} [RegEncoding Basis]
    (r : Reg) (v w : ℕ) (b : Basis) : RegEncoding.writeNat r v (RegEncoding.writeNat r w b) =
    RegEncoding.writeNat r v b :=
  writeNat_overwrite_same_reg r v w b

/--
Explicit inverse-QFT evaluation on an arbitrary finite work packet.

Unlike `eval_iqft_work_expansion`, this specifies the coefficient exactly.
-/
lemma eval_IQFT_work_packet (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] (work : ExtReg)
    (base : qs.Basis) (β : Fin (ASize work.active) → ℂ) : qs.eval (IQFT work) (∑ z : Fin (ASize work.active),
        β z • qs.ket (RegEncoding.writeNat work.active z.1 base)) = ∑ t : Fin (ASize work.active),
      (∑ z : Fin (ASize work.active), β z * alg1IQFTCoeff work.active z t) •
        qs.ket (RegEncoding.writeNat work.active t.1 base) := by
  classical

  have hsingle : ∀ z : Fin (ASize work.active), qs.eval (IQFT work)
          (qs.ket (RegEncoding.writeNat work.active z.1 base)) = ∑ t : Fin (ASize work.active),
          alg1IQFTCoeff work.active z t •
            qs.ket (RegEncoding.writeNat work.active t.1 base) := by
    intro z
    rw [IQFT, QFTSemantics.eval_adj_QFT_ket]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [smul_smul]
    have hz_toNat : RegEncoding.toNat work.active (RegEncoding.writeNat work.active z.1 base)
          = z.1 :=
      RegEncoding.toNat_writeNat_of_lt work.active z.1 base z.isLt
    simp [
      alg1IQFTCoeff, ExtReg.toNat, hz_toNat,
      writeNat_overwrite_same_reg_step5
    ]

  calc
    qs.eval (IQFT work)
        (∑ z : Fin (ASize work.active),
          β z • qs.ket (RegEncoding.writeNat work.active z.1 base))
      =
    ∑ z : Fin (ASize work.active),
      β z •
        qs.eval (IQFT work)
          (qs.ket (RegEncoding.writeNat work.active z.1 base)) := by
        rw [eval_finset_sum]
        apply Finset.sum_congr rfl
        intro z hz
        rw [qs.eval_smul]

    _ =
    ∑ z : Fin (ASize work.active),
      β z •
        ∑ t : Fin (ASize work.active),
          alg1IQFTCoeff work.active z t •
            qs.ket (RegEncoding.writeNat work.active t.1 base) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hsingle z]

    _ =
    ∑ t : Fin (ASize work.active),
      (∑ z : Fin (ASize work.active),
        β z * alg1IQFTCoeff work.active z t) •
        qs.ket (RegEncoding.writeNat work.active t.1 base) := by
        calc
          ∑ z : Fin (ASize work.active),
            β z •
              ∑ t : Fin (ASize work.active),
                alg1IQFTCoeff work.active z t •
                  qs.ket (RegEncoding.writeNat work.active t.1 base)
              =
            ∑ z : Fin (ASize work.active),
              ∑ t : Fin (ASize work.active),
                (β z * alg1IQFTCoeff work.active z t) •
                  qs.ket (RegEncoding.writeNat work.active t.1 base) := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [Finset.smul_sum]
              apply Finset.sum_congr rfl
              intro t ht
              rw [smul_smul]
          _ =
            ∑ t : Fin (ASize work.active),
              ∑ z : Fin (ASize work.active),
                (β z * alg1IQFTCoeff work.active z t) •
                  qs.ket (RegEncoding.writeNat work.active t.1 base) := by
              rw [Finset.sum_comm]
          _ =
            ∑ t : Fin (ASize work.active),
              (∑ z : Fin (ASize work.active),
                β z * alg1IQFTCoeff work.active z t) •
                qs.ket (RegEncoding.writeNat work.active t.1 base) := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [← Finset.sum_smul]

/-- The QFT phase with zero left input is trivial. -/
private lemma qpe_qftPhase_zero_left (N y : ℕ) :
    qftPhase N 0 y = 1 := by
  simp [qftPhase, ωPow]

lemma eval_Hreg_zero_uniform_sum_ext (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (work : ExtReg) (b : qs.Basis) (hzero : RegEncoding.toNat work.active b = 0) :
    qs.eval (H_reg work.active) (qs.ket b) = (1 / Real.sqrt (ASize work.active : ℝ) : ℂ) •
        ∑ y : Fin (ASize work.active),
          qs.ket (RegEncoding.writeNat work.active y.1 b) := by
  rw [_root_.eval_Hreg_zero_eq_QFT qs work b]
  · rw [QFTSemantics.eval_QFT_ket]
    simp [ExtReg.width, ExtReg.toNat, ASize, hzero, qpe_qftPhase_zero_left]
  · simpa [ExtReg.toNat] using hzero

/--
The pre-IQFT Step-1 packet.

This is proved entirely from `eval_Hreg_zero_uniform_sum`, diagonal CPhaseProd
semantics, and linearity.
-/
lemma alg1_step1_preIQFT_packet (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] {η : ℝ}
    (cfg : ModMulConfig η) (b : qs.Basis) (hb : GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) : qs.eval ((H_reg cfg.env.work.active) ;;
          (Gate.CPhaseProdUsing cfg.ctrl (alg1Step1Phase cfg) cfg.env.data.active cfg.env.work.active
            cfg.env.circuit_workspace.step1Workspace)) (qs.ket b) = ∑ z : Fin (ASize cfg.env.work.active),
      alg1LoadPreCoeff cfg b z •
        qs.ket (RegEncoding.writeNat cfg.env.work.active z.1 b) := by
  classical

  rw [qs.eval_seq, eval_Hreg_zero_uniform_sum_ext qs cfg.env.work b hb.2.2.1]
  rw [qs.eval_smul, eval_finset_sum, Finset.smul_sum]

  apply Finset.sum_congr rfl
  intro z hz
  rw [alg1_step1_cphase_on_work_label qs cfg b hb z]
  rw [smul_smul]
  rfl

/--
The pre-IQFT forward Step-5 packet, still expressed relative to the ideal
output basis state.
-/
lemma alg1_step5_forward_preIQFT_packet (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] {η : ℝ}
    (cfg : ModMulConfig η) (b : qs.Basis) (hb : GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) : qs.eval ((H_reg cfg.env.work.active) ;;
          (Gate.CPhaseProdUsing cfg.ctrl (alg1Step5Phase cfg) ((cfg.env.data.grow 1).active) cfg.env.work.active
            cfg.env.circuit_workspace.step5Workspace)) (qs.ket (RegEncoding.writeNat ((cfg.env.data.grow 1).active)
            (alg1OutputValue cfg b) b)) = ∑ z : Fin (ASize cfg.env.work.active), alg1LoadPreCoeff cfg b z • qs.ket
          (RegEncoding.writeNat cfg.env.work.active z.1 (RegEncoding.writeNat ((cfg.env.data.grow 1).active)
              (alg1OutputValue cfg b)
              b)) := by
  classical

  have hwork0 : RegEncoding.toNat cfg.env.work.active (RegEncoding.writeNat ((cfg.env.data.grow 1).active)
          (alg1OutputValue cfg b) b) =
      0 := by
    calc
      RegEncoding.toNat cfg.env.work.active
          (RegEncoding.writeNat
            ((cfg.env.data.grow 1).active)
            (alg1OutputValue cfg b)
            b)
        =
      RegEncoding.toNat cfg.env.work.active b := by
        exact
          RegEncoding.toNat_right_write_left
            ((cfg.env.data.grow 1).active)
            cfg.env.work.active
            (alg1_dataCarry_work_active_disjoint cfg)
            b
            (alg1OutputValue cfg b)
      _ = 0 := hb.2.2.1

  rw [qs.eval_seq]
  rw [
    eval_Hreg_zero_uniform_sum_ext
      qs
      cfg.env.work
      (RegEncoding.writeNat
        ((cfg.env.data.grow 1).active)
        (alg1OutputValue cfg b)
        b)
      hwork0
  ]
  rw [qs.eval_smul, eval_finset_sum, Finset.smul_sum]

  apply Finset.sum_congr rfl
  intro z hz
  rw [alg1_step5_cphase_on_output_work_label qs cfg b hb z]
  rw [smul_smul]
  rfl

/--
The original canonical QPE coefficient is the explicit Fourier coefficient.

Proof: combine `alg1_step1_preIQFT_packet` with `eval_IQFT_work_packet`, then
project both sides onto `ket (writeNat work t b)`.
-/
lemma alg1PhaseCoeff_eq_fractionalLoadCoeff (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] {η : ℝ}
    (cfg : ModMulConfig η) (b : qs.Basis) (hb : GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) (t : Fin (ASize cfg.env.work.active)) :
    alg1PhaseCoeff qs cfg b t =
    alg1FractionalLoadCoeff cfg b t := by
  classical

  have hlabel_inj : ∀ s u : Fin (ASize cfg.env.work.active), RegEncoding.writeNat cfg.env.work.active s.1 b =
        RegEncoding.writeNat cfg.env.work.active u.1 b →
        s = u := by
    intro s u hEq
    apply Fin.ext
    calc
      s.1
          =
        RegEncoding.toNat cfg.env.work.active
          (RegEncoding.writeNat cfg.env.work.active s.1 b) := by
            symm
            exact
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work.active s.1 b s.isLt
      _ =
        RegEncoding.toNat cfg.env.work.active
          (RegEncoding.writeNat cfg.env.work.active u.1 b) := by
            rw [hEq]
      _ = u.1 :=
        RegEncoding.toNat_writeNat_of_lt
          cfg.env.work.active u.1 b u.isLt

  have hU1 : qs.eval
          (ModMulConfig.U1 (Basis := qs.Basis) cfg)
          (qs.ket b)
        =
      ∑ s : Fin (ASize cfg.env.work.active),
        alg1FractionalLoadCoeff cfg b s •
          qs.ket
            (RegEncoding.writeNat cfg.env.work.active s.1 b) := by
    calc
      qs.eval
          (ModMulConfig.U1 (Basis := qs.Basis) cfg)
          (qs.ket b)
        =
      qs.eval
        (IQFT cfg.env.work)
        (qs.eval
          ((H_reg cfg.env.work.active) ;;
            Gate.CPhaseProdUsing
              cfg.ctrl
              (alg1Step1Phase cfg)
              cfg.env.data.active
              cfg.env.work.active
              cfg.env.circuit_workspace.step1Workspace)
          (qs.ket b)) := by
            simp [ModMulConfig.U1, step1, qs.eval_seq]
            congr

      _ =
      qs.eval
        (IQFT cfg.env.work)
        (∑ z : Fin (ASize cfg.env.work.active),
          alg1LoadPreCoeff cfg b z •
            qs.ket
              (RegEncoding.writeNat cfg.env.work.active z.1 b)) := by
            rw [alg1_step1_preIQFT_packet qs cfg b hb]

      _ =
      ∑ s : Fin (ASize cfg.env.work.active),
        alg1FractionalLoadCoeff cfg b s •
          qs.ket
            (RegEncoding.writeNat cfg.env.work.active s.1 b) := by
            simpa [alg1FractionalLoadCoeff] using
              (eval_IQFT_work_packet
                qs
                cfg.env.work
                b
                (alg1LoadPreCoeff cfg b))

  unfold alg1PhaseCoeff
  rw [hU1]
  rw [inner_sum]
  rw [Finset.sum_eq_single t]
  · rw [inner_smul_right, ket_inner_self]
    simp
  · intro u _hu htu
    have hneq : RegEncoding.writeNat cfg.env.work.active t.1 b ≠
        RegEncoding.writeNat cfg.env.work.active u.1 b := by
      intro hEq
      exact htu ((hlabel_inj t u hEq).symm)

    rw [
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne hneq
    ]
    simp
  · intro ht
    simp at ht

end ExactPacketAlgebra

/-! =========================================================
    From Algorithm 1 to the standard QPE kernel

This section introduces `qpeKernel`, the textbook finite QPE amplitude for a
phase `θ` sampled on an `M`-point grid, and translates the Algorithm-1 data
into it: the Step-1 phase becomes the source phase at `alg1TargetFraction`, the
conjugated QFT entries become the negative grid phase, the two normalizers
multiply to `1 / M`, and the set of discarded labels becomes the numerical
window predicate. It also converts the `Algorithm1Precision` hypothesis into
the grid-to-capacity ratio that the analytic bound consumes.
========================================================= -/

section AnalyticQpeSetup

/--
Rewrite the Step-1 phase as the continuous QPE source phase centred at
`alg1TargetFraction cfg b`.
-/
private lemma alg1Step1PhaseScalar_eq_qpe_source_phase (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ}
    (cfg : ModMulConfig η) (b : qs.Basis) (z : Fin (ASize cfg.env.work.active)) : alg1Step1PhaseScalar cfg b z =
    Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((alg1TargetFraction cfg b : ℂ) * (z.1 : ℂ))) := by
  rw [alg1_step1_phase_scalar_eq_target qs cfg b z]
  classical
  by_cases hctrl : RegEncoding.bit cfg.ctrl b
  ·
    simp only [
      alg1TargetPhaseScalar,
      alg1TargetFraction,
      alg1TargetResidue,
      hctrl,
      if_true
    ]
    congr 1
    push_cast
    simp [div_eq_mul_inv]
    ring
  ·
    simp [
      alg1TargetPhaseScalar,
      alg1TargetFraction,
      alg1TargetResidue,
      hctrl
    ]

/--
Write the QFT matrix entry as an ordinary complex exponential.

This is the same `qftPhase` expansion already used inside
`alg1_exp_phase_eq_of_modEq`.
-/
private lemma qftPhase_eq_exp_grid (M z t : ℕ) : qftPhase M z t = Complex.exp
      (((2 * Real.pi) / (M : ℝ)) * Complex.I *
        ((z : ℂ) * (t : ℂ))) := by
  simp [
    qftPhase,
    ωPow,
    ω,
    div_eq_mul_inv,
    mul_assoc,
    mul_left_comm,
    mul_comm
  ]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/--
The conjugated inverse-QFT phase is the negative grid phase.
-/
private lemma star_qftPhase_eq_negative_grid_phase (M z t : ℕ) : star (qftPhase M z t) = Complex.exp
      (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (((z : ℂ) * (t : ℂ)) / (M : ℂ)))) := by
  rw [qftPhase_eq_exp_grid]
  simp
  rw [← Complex.exp_conj]
  congr 1
  simp [div_eq_mul_inv]
  simp [starRingEnd]
  ring

/--
The two QFT/H normalizers multiply to the usual `1 / M` QPE normalizer.

This is only square-root algebra; it is independent of Algorithm 1.
-/
private lemma qpe_normalizer_sq (M : ℕ) (hM : 0 < M) : (1 / Real.sqrt (M : ℝ) : ℂ) * (1 / Real.sqrt (M : ℝ) : ℂ) =
    1 / (M : ℂ) := by
  have hMr : 0 < (M : ℝ) := by
    exact_mod_cast hM
  have hsqrt :
      (Real.sqrt (M : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hMr))
  have hM0 : (M : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hM
  field_simp [hsqrt, hM0]
  norm_cast
  nlinarith [Real.sq_sqrt (le_of_lt hMr)]

/--
One source label contributes exactly the corresponding summand of the
standard finite QPE kernel.

This is the key algebraic bridge. It contains no state semantics.
-/
private lemma alg1FractionalLoadCoeff_summand_eq_qpeKernel_summand (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ}
    (cfg : ModMulConfig η) (b : qs.Basis) (z t : Fin (ASize cfg.env.work.active)) : alg1LoadPreCoeff cfg b z *
        alg1IQFTCoeff cfg.env.work.active z t = (1 / (ASize cfg.env.work.active : ℂ)) * Complex.exp
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((alg1TargetFraction cfg b : ℂ) -
              ((t.1 : ℂ) / (ASize cfg.env.work.active : ℂ))) *
            (z.1 : ℂ))) := by
  have hM : 0 < ASize cfg.env.work.active := by
    unfold ASize
    positivity

  have hnorm : (1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ) *
        (1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ) =
      1 / (ASize cfg.env.work.active : ℂ) :=
    qpe_normalizer_sq (ASize cfg.env.work.active) hM

  rw [
    alg1LoadPreCoeff,
    alg1IQFTCoeff,
    alg1Step1PhaseScalar_eq_qpe_source_phase qs cfg b z,
    star_qftPhase_eq_negative_grid_phase
  ]

  let α : ℂ :=
    ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      ((alg1TargetFraction cfg b : ℂ) * (z.1 : ℂ))

  let β : ℂ :=
    -(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      (((z.1 : ℂ) * (t.1 : ℂ)) /
        (ASize cfg.env.work.active : ℂ)))

  let γ : ℂ :=
    ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      (((alg1TargetFraction cfg b : ℂ) -
          ((t.1 : ℂ) / (ASize cfg.env.work.active : ℂ))) *
        (z.1 : ℂ))

  change
    ((1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ) *
        Complex.exp α) *
      ((1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ) *
        Complex.exp β)
      =
    (1 / (ASize cfg.env.work.active : ℂ)) * Complex.exp γ

  calc
    ((1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ) *
        Complex.exp α) *
      ((1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ) *
        Complex.exp β)
        =
      ((1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ) *
        (1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ)) *
        (Complex.exp α * Complex.exp β) := by
          ring
    _ =
      ((1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ) *
        (1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ)) *
        Complex.exp (α + β) := by
          rw [← Complex.exp_add]
    _ =
      ((1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ) *
        (1 / Real.sqrt (ASize cfg.env.work.active : ℝ) : ℂ)) *
        Complex.exp γ := by
          congr 2
          dsimp [α, β, γ]
          simp [div_eq_mul_inv]
          ring
    _ =
      (1 / (ASize cfg.env.work.active : ℂ)) * Complex.exp γ := by
          rw [hnorm]
/--
Rewrite the set of discarded labels into the numerical QPE-window predicate.

This is just unfolding `alg1GoodLabels`; no Fourier estimate occurs here.
-/
lemma alg1_bad_label_set_eq_qpe_bad_set (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModMulConfig η)
    (b : qs.Basis) : Finset.univ.filter (fun t : Fin (ASize cfg.env.work.active) => t ∉ alg1GoodLabels cfg b) =
    Finset.univ.filter (fun t : Fin (ASize cfg.env.work.active) => ¬ |alg1TargetFraction cfg b -
              ((t.1 : ℝ) / (ASize cfg.env.work.active : ℝ))| <
          η / (ASize cfg.env.data.active : ℝ)) := by
  classical
  ext t
  simp [alg1GoodLabels, alg1WorkFraction]

/--
Convert `Algorithm1Precision` into the ratio of the actual QPE grid size
to the data-register capacity.

The nontrivial arithmetic fact is

`ASize work / ASize data = 2^(regSize work - regSize data)`,

where the precision hypothesis itself forces `regSize data ≤ regSize work`.
-/
lemma alg1_precision_grid_ratio {η : ℝ} (cfg : ModMulConfig η) : 0 < η ∧ η < (1 / 2 : ℝ) ∧
    0 < (ASize cfg.env.data.active : ℝ) ∧ 0 < (ASize cfg.env.work.active : ℝ) ∧ (2 + 1 / (2 * η)) ^ 2 ≤
    (ASize cfg.env.work.active : ℝ) /
      (ASize cfg.env.data.active : ℝ) := by
  rcases cfg.env.precision with ⟨hη, hηhalf, hprec⟩

  have hprec:= pow_bound cfg.env.precision

  let n : ℕ := regSize cfg.env.data.active
  let m : ℕ := regSize cfg.env.work.active

  have hdata_nat : 0 < ASize cfg.env.data.active := by
    unfold ASize
    positivity

  have hwork_nat : 0 < ASize cfg.env.work.active := by
    unfold ASize
    positivity

  have hdata : 0 < (ASize cfg.env.data.active : ℝ) := by
    exact_mod_cast hdata_nat

  have hwork : 0 < (ASize cfg.env.work.active : ℝ) := by
    exact_mod_cast hwork_nat

  have hinv_pos : 0 < 1 / (2 * η) := by
    positivity

  have htarget_gt_one :
      1 < (2 + 1 / (2 * η)) ^ 2 := by
    nlinarith [sq_nonneg (1 / (2 * η))]

  have hnm : n ≤ m := by
    by_contra hnot
    have hmn : m < n := Nat.lt_of_not_ge hnot
    have hsub : m - n = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_lt hmn)

    change
      (2 : ℝ) ^ (m - n)
        ≥
      (2 + 1 / (2 * η)) ^ 2 at hprec

    rw [hsub] at hprec
    norm_num at hprec
    simp_all [n, m]

  have hpow : (2 : ℝ) ^ m =
      (2 : ℝ) ^ n * (2 : ℝ) ^ (m - n) := by
    rw [← pow_add]
    congr
    omega

  have hratio : (ASize cfg.env.work.active : ℝ) / (ASize cfg.env.data.active : ℝ) =
      (2 : ℝ) ^ (m - n) := by
    calc
      (ASize cfg.env.work.active : ℝ) /
          (ASize cfg.env.data.active : ℝ)
          =
        (2 : ℝ) ^ m / (2 : ℝ) ^ n := by
          simp [ASize, m, n]
      _ =
        ((2 : ℝ) ^ n * (2 : ℝ) ^ (m - n)) /
          (2 : ℝ) ^ n := by
          rw [hpow]
      _ = (2 : ℝ) ^ (m - n) := by
          have hnz : (2 : ℝ) ^ n ≠ 0 := by positivity
          field_simp [hnz]

  refine ⟨hη, hηhalf, hdata, hwork, ?_⟩
  calc
    (2 + 1 / (2 * η)) ^ 2
        ≤
      (2 : ℝ) ^ (m - n) := by
        simpa [m, n] using hprec
    _ =
      (ASize cfg.env.work.active : ℝ) /
        (ASize cfg.env.data.active : ℝ) :=
      hratio.symm

/--
The precision hypothesis makes the tail scale linear in `η`.

Given `(2 + 1 / (2 * η)) ^ 2 ≤ M / D`, the ratio `D / (M * η)` is at most
`4 * η`; this is what turns the `128 / (M * δ)` kernel bound into a bound
proportional to `η`.
-/
lemma qpe_precision_tail_scale {η D M : ℝ} (hη : 0 < η) (hD : 0 < D) (hM : 0 < M) (hgrid :
      (2 + 1 / (2 * η)) ^ 2 ≤ M / D) :
    D / (M * η) ≤ 4 * η := by
  have h2η : 0 < 2 * η := by positivity

  have hinv : 0 < 1 / (2 * η) := by
    exact one_div_pos.mpr h2η

  have hsmall : (1 / (2 * η)) ^ 2 ≤
      (2 + 1 / (2 * η)) ^ 2 := by
    nlinarith [sq_nonneg (1 / (2 * η))]

  have hrearrange : 1 / (4 * η ^ 2) =
      (1 / (2 * η)) ^ 2 := by
    field_simp [ne_of_gt hη]
    ring

  have hquad : 1 / (4 * η ^ 2) ≤
      (2 + 1 / (2 * η)) ^ 2 := by
    rw [hrearrange]
    exact hsmall

  have hMD :
      1 / (4 * η ^ 2) ≤ M / D :=
    le_trans hquad hgrid

  have hprod :
      (1 / (4 * η ^ 2)) * D ≤ M :=
    (le_div_iff₀ hD).mp hMD

  have hscale_pos : 0 < 4 * η ^ 2 := by
    positivity

  have hmul : (4 * η ^ 2) * ((1 / (4 * η ^ 2)) * D) ≤
      (4 * η ^ 2) * M :=
    mul_le_mul_of_nonneg_left hprod (le_of_lt hscale_pos)

  have hcancel : (4 * η ^ 2) * ((1 / (4 * η ^ 2)) * D) =
      D := by
    field_simp [ne_of_gt hscale_pos]

  have hmain :
      D ≤ 4 * M * η ^ 2 := by
    calc
      D =
          (4 * η ^ 2) *
            ((1 / (4 * η ^ 2)) * D) :=
        hcancel.symm
      _ ≤ (4 * η ^ 2) * M := hmul
      _ = 4 * M * η ^ 2 := by ring

  have hden : 0 < M * η := mul_pos hM hη

  apply (div_le_iff₀ hden).2
  calc
    D ≤ 4 * M * η ^ 2 := hmain
    _ = (4 * η) * (M * η) := by ring

end AnalyticQpeSetup

/-! =========================================================
    The uniform Step-1 tail bound

The final assembly. The explicit Fourier coefficient computed in the packet
algebra is literally the standard QPE kernel at the phase
`alg1TargetFraction cfg b`, so the numerical estimate applies verbatim. The
endpoint `alg1_qpe_tail_basis_uniform` produces a single constant, `512`,
bounding `alg1QpeBadMass` by `512 * η` for every configuration and every good
basis input; `alg1_trace_bad_mass_le_of_basis_tail` then lifts it to arbitrary
valid states.
========================================================= -/

section UniformStep1TailBound

/-- The Algorithm-1 Fourier coefficient is the standard finite QPE kernel. -/
lemma alg1FractionalLoadCoeff_eq_qpeKernel (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModMulConfig η)
    (b : qs.Basis) (t : Fin (ASize cfg.env.work.active)) : alg1FractionalLoadCoeff cfg b t = qpeKernel
      (ASize cfg.env.work.active) (alg1TargetFraction cfg b)
      t := by
  classical
  unfold alg1FractionalLoadCoeff qpeKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact
    alg1FractionalLoadCoeff_summand_eq_qpeKernel_summand
      qs cfg b z t
/--
Uniform basis-input QPE-tail estimate.

For every good basis input the Step-1 mass falling outside the precision window
is at most `512 * η`, with a constant independent of the configuration, the
modulus, and the register sizes. The zero-target case is handled separately,
where the kernel is a delta and the bad mass is exactly zero; otherwise the
target fraction is an ordinary fraction `r / N` with `0 < r < N` and
`qpeKernel_bad_mass_le_grid_ratio` applies, with `qpe_precision_tail_scale`
converting the grid ratio into the linear factor `4 * η`.
-/
lemma alg1_qpe_tail_basis_uniform (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧ Ctail ≤ 512 ∧ ∀ (η : ℝ) (cfg : ModMulConfig η) (b : qs.Basis), GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b →
        alg1QpeBadMass qs cfg b ≤ Ctail * η := by
  classical
  refine ⟨512, by norm_num, by norm_num, ?_⟩
  intro η cfg b hb

  rcases alg1_precision_grid_ratio cfg with
    ⟨hη, hηhalf, hD, hM, hgrid⟩

  have hNnat : 0 < cfg.env.N :=
    Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

  have hN : 0 < (cfg.env.N : ℝ) := by
    exact_mod_cast hNnat

  have hr : alg1TargetResidue cfg b < cfg.env.N :=
    alg1TargetResidue_lt_N cfg b

  have hkernel : ∑ t ∈ Finset.univ.filter (fun t : Fin (ASize cfg.env.work.active) => ¬
              |((alg1TargetResidue cfg b : ℝ) / (cfg.env.N : ℝ)) - ((t.1 : ℝ) / (ASize cfg.env.work.active : ℝ))| <
              η / (ASize cfg.env.data.active : ℝ)), ‖qpeKernel (ASize cfg.env.work.active)
            ((alg1TargetResidue cfg b : ℝ) / (cfg.env.N : ℝ)) t‖ ^ 2 ≤ 128 * ((ASize cfg.env.data.active : ℝ) /
          ((ASize cfg.env.work.active : ℝ) * η)) := by
    exact
      qpeKernel_bad_mass_le_grid_ratio
        η
        cfg.env.N
        (ASize cfg.env.data.active)
        (ASize cfg.env.work.active)
        (alg1TargetResidue cfg b)
        hη
        hηhalf
        hN
        hD
        hM
        cfg.env.data_capacity
        hr
        hgrid

  have hscale : (ASize cfg.env.data.active : ℝ) / ((ASize cfg.env.work.active : ℝ) * η) ≤
      4 * η :=
    qpe_precision_tail_scale hη hD hM hgrid

  unfold alg1QpeBadMass
  rw [alg1_bad_label_set_eq_qpe_bad_set qs cfg b]

  calc
    ∑ t ∈ Finset.univ.filter
        (fun t : Fin (ASize cfg.env.work.active) =>
          ¬
            |alg1TargetFraction cfg b -
                ((t.1 : ℝ) / (ASize cfg.env.work.active : ℝ))|
              <
            η / (ASize cfg.env.data.active : ℝ)),
      ‖alg1PhaseCoeff qs cfg b t‖ ^ 2
        =
    ∑ t ∈ Finset.univ.filter
        (fun t : Fin (ASize cfg.env.work.active) =>
          ¬
            |alg1TargetFraction cfg b -
                ((t.1 : ℝ) / (ASize cfg.env.work.active : ℝ))|
              <
            η / (ASize cfg.env.data.active : ℝ)),
      ‖qpeKernel
          (ASize cfg.env.work.active)
          (alg1TargetFraction cfg b)
          t‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [
        alg1PhaseCoeff_eq_fractionalLoadCoeff qs cfg b hb t,
        alg1FractionalLoadCoeff_eq_qpeKernel qs cfg b t
      ]

    _ ≤
      128 *
        ((ASize cfg.env.data.active : ℝ) /
          ((ASize cfg.env.work.active : ℝ) * η)) := by
      simpa [alg1TargetFraction] using hkernel

    _ ≤ 512 * η := by
      calc
        128 *
            ((ASize cfg.env.data.active : ℝ) /
              ((ASize cfg.env.work.active : ℝ) * η))
          ≤
        128 * (4 * η) :=
          mul_le_mul_of_nonneg_left hscale (by norm_num)
        _ = 512 * η := by ring

end UniformStep1TailBound
