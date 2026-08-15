import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateLevelCorrectness.GateConstructions
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Phase-Product Gate Semantics Lemmas

Proof-support facts about evaluating gates on quantum states. The first block
contains shared register/Hadamard/evaluator facts used throughout the
implementation proofs; the second block exposes convenient `QSemantics` rewrite
lemmas and the phase-product macro semantics needed by gate-level correctness.
-/

namespace Shor

section SharedRegisterAndEvalFacts
universe u
variable {Basis : Type u} [RegEncoding Basis]
open QSemantics

/-! =========================================================
    Register And Hadamard Support

    These generic facts describe one-qubit registers, zero-valued splits,
    Hadamard uniform superpositions, and the normalization constants that appear
    in register-Hadamard proofs.
========================================================= -/

/-- A one-qubit register is the singleton register at its low qubit. -/
theorem Reg.eq_qubitReg_lowQubit
    (r : Reg)
    (hsize : regSize r = 1) :
    r = qubitReg (r.lowQubit (by omega)) := by
  cases r with
  | mk qubits nodup =>
      have hlen : qubits.length = 1 := by
        simpa [regSize, Reg.width] using hsize
      cases qubits with
      | nil =>
          simp at hlen
      | cons q qs =>
          cases qs with
          | nil =>
              simp [
                qubitReg,
                Reg.singleton,
                Reg.lowQubit]
          | cons q' qs =>
              simp at hlen

/-- The primitive second root of unity is -1. -/
theorem omega_two :
    ω 2 = (-1 : ℂ) := by
  unfold ω
  ring_nf
  exact Complex.exp_pi_mul_I

theorem toNat_split_eq_zero
    {Basis : Type u} [RegEncoding Basis]
    (r : Reg)
    (m : SplitPoint r)
    (b : Basis)
    (hzero : RegEncoding.toNat r b = 0) :
    RegEncoding.toNat (splitLeft r m) b = 0 ∧
    RegEncoding.toNat (splitRight r m) b = 0 := by

  have h :=
    RegEncoding.toNat_split r m b

  rw [hzero] at h

  have hsum :
      RegEncoding.toNat (splitLeft r m) b +
          ASize (splitLeft r m) *
            RegEncoding.toNat (splitRight r m) b =
        0 := h.symm

  constructor
  · exact Nat.eq_zero_of_add_eq_zero_right hsum
  · have hprod :
        ASize (splitLeft r m) *
            RegEncoding.toNat (splitRight r m) b =
          0 :=
      Nat.eq_zero_of_add_eq_zero_left hsum

    rcases Nat.mul_eq_zero.mp hprod with hsize | hright
    · have hpos : 0 < ASize (splitLeft r m) := by
        simp [ASize]
      omega
    · exact hright

theorem bit_lowQubit_eq_false_of_toNat_zero
    {Basis : Type u} [RegEncoding Basis]
    (r : Reg)
    (b : Basis)
    (hpos : 0 < regSize r)
    (hzero : RegEncoding.toNat r b = 0) :
    RegEncoding.bit (r.lowQubit hpos) b = false := by

  let i : Fin (regSize r) := ⟨0, hpos⟩

  have h :=
    RegEncoding.bit_eq_testBit_toNat r b i

  have hget :
      r.get i = r.lowQubit hpos := by
    rfl

  rw [hget, hzero] at h
  simpa using h

theorem inv_sqrt_two_mul_inv_sqrt_nat
    (N : ℕ) (hN : 0 < N) :
    ((1 / Real.sqrt (2 : ℝ) : ℂ) *
      (1 / Real.sqrt (N : ℝ) : ℂ))
      =
    (1 / Real.sqrt ((N + N : ℕ) : ℝ) : ℂ) := by
  have hsqrt :
      Real.sqrt (((N + N : ℕ) : ℝ)) =
        Real.sqrt (2 : ℝ) * Real.sqrt (N : ℝ) := by
    have hcast :
        (((N + N : ℕ) : ℝ)) =
          (2 : ℝ) * (N : ℝ) := by
      push_cast
      ring
    rw [hcast]
    exact Real.sqrt_mul (by norm_num) (N : ℝ)

  have h2 :
      (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'

  have hN' :
      (Real.sqrt (N : ℝ) : ℂ) ≠ 0 := by
    have hNr : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast hN
    exact_mod_cast (Real.sqrt_pos.2 hNr).ne'

  rw [hsqrt]
  push_cast
  field_simp [h2, hN']

theorem eval_Hreg_zero_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [HadamardSemantics qs]
    (r : Reg)
    (b : qs.Basis)
    (hzero : RegEncoding.toNat r b = 0) :
    qs.eval
        ((regQubits r).foldl
          (fun acc q => Gate.seq (Gate.H q) acc)
          Gate.id)
        (qs.ket b)
      =
    ((1 / Real.sqrt ((ASize r : ℕ) : ℝ) : ℂ)) •
      ∑ t : Fin (ASize r),
        qs.ket (RegEncoding.writeNat r t.1 b) := by
  classical

  have hP :
      ∀ n (r : Reg) (b : qs.Basis),
        regSize r = n →
        RegEncoding.toNat r b = 0 →
        qs.eval
            ((regQubits r).foldl
              (fun acc q => Gate.seq (Gate.H q) acc)
              Gate.id)
            (qs.ket b)
          =
        ((1 / Real.sqrt ((ASize r : ℕ) : ℝ) : ℂ)) •
          ∑ t : Fin (ASize r),
            qs.ket (RegEncoding.writeNat r t.1 b) := by

    intro n
    induction n with

    | zero =>
        intro r b hn hzero

        have hqubits : regQubits r = [] := by
          change r.qubits = []
          have hlen : r.qubits.length = 0 := by
            simpa [regSize, Reg.width] using hn
          simpa using hlen

        have hA : ASize r = 1 := by
          simp [ASize, hn]

        have hwrite :
            RegEncoding.writeNat r 0 b = b := by
          simpa [hzero] using
            (RegEncoding.writeNat_toNat r b)

        rw [hqubits]
        simp only [List.foldl_nil]
        simp [GateSemanticsCore.eval_id]
        rw [hA]
        simp [hwrite]

    | succ n ih =>
        intro r b hn hzero

        ------------------------------------------------------------
        -- Split r = left ++ right, where right is the final qubit.
        ------------------------------------------------------------

        let sp : SplitPoint r :=
          ⟨n, by omega⟩

        let left : Reg :=
          splitLeft r sp

        let right : Reg :=
          splitRight r sp

        have hleftSize :
            regSize left = n := by
          simp [left, sp]

        have hrightSize :
            regSize right = 1 := by
          simp [right, sp, hn]

        have hdisj :
            Disjoint left right := by
          exact splitLeft_splitRight_disjoint r sp

        have hzsplit :=
          toNat_split_eq_zero r sp b hzero

        have hzleft :
            RegEncoding.toNat left b = 0 := by
          simpa [left] using hzsplit.1

        have hzright :
            RegEncoding.toNat right b = 0 := by
          simpa [right] using hzsplit.2

        ------------------------------------------------------------
        -- The right side is a one-qubit register [q].
        ------------------------------------------------------------

        have hrightPos :
            0 < regSize right := by
          omega

        let q : ℕ :=
          right.lowQubit hrightPos

        have hrightQ :
            right = qubitReg q := by
          simpa [q] using
            Reg.eq_qubitReg_lowQubit
              right hrightSize

        have hbit :
            RegEncoding.bit q b = false := by
          simpa [q] using
            bit_lowQubit_eq_false_of_toNat_zero
              right b hrightPos hzright

        ------------------------------------------------------------
        -- r.qubits = left.qubits ++ [q].
        ------------------------------------------------------------

        have hqubits :
            regQubits r =
              regQubits left ++ [q] := by
          change
            r.qubits =
              left.qubits ++ [q]

          calc
            r.qubits =
                left.qubits ++ right.qubits := by
              symm
              simpa [
                left, right, sp,
                splitLeft, splitRight
              ] using
                (Gate.Reg.take_append_drop r n)

            _ = left.qubits ++ [q] := by
              rw [hrightQ]
              rfl

        ------------------------------------------------------------
        -- Consequently
        --
        -- Hreg(r) = H(q) ;; Hreg(left).
        --
        -- Recall eval_seq means H(q) is executed first.
        ------------------------------------------------------------

        have hfold :
            (regQubits r).foldl
                (fun acc q =>
                  Gate.seq (Gate.H q) acc)
                Gate.id
              =
            Gate.seq
              (Gate.H q)
              ((regQubits left).foldl
                (fun acc q =>
                  Gate.seq (Gate.H q) acc)
                Gate.id) := by
          rw [hqubits, List.foldl_append]
          rfl

        ------------------------------------------------------------
        -- Writing the high bit does not change the zero contents
        -- of `left`, so IH applies to both H branches.
        ------------------------------------------------------------

        have hzleft0 :
            RegEncoding.toNat left
                (RegEncoding.writeNat right 0 b) =
              0 := by
          rw [
            RegEncoding.toNat_left_write_right
              left right hdisj b 0
          ]
          exact hzleft

        have hzleft1 :
            RegEncoding.toNat left
                (RegEncoding.writeNat right 1 b) =
              0 := by
          rw [
            RegEncoding.toNat_left_write_right
              left right hdisj b 1
          ]
          exact hzleft

        have ih0 :=
          ih
            left
            (RegEncoding.writeNat right 0 b)
            hleftSize
            hzleft0

        have ih1 :=
          ih
            left
            (RegEncoding.writeNat right 1 b)
            hleftSize
            hzleft1

        ------------------------------------------------------------
        -- Rewrite the two half-register basis states as basis
        -- states of the full register.
        ------------------------------------------------------------

        have hzeroFits :
            0 < ASize right := by
          simp [ASize]

        have honeFits :
            1 < ASize right := by
          simp [ASize, hrightSize]

        have hwrite0
            (t : Fin (ASize left)) :
            RegEncoding.writeNat left t.1
                (RegEncoding.writeNat right 0 b)
              =
            RegEncoding.writeNat r t.1 b := by

          rw [
            RegEncoding.writeNat_comm_of_disjoint
              left right hdisj t.1 0 b
          ]

          have hs :=
            RegEncoding.writeNat_split
              r sp 0 t.1 b
              (by simp [left])
              (by simpa [right] using hzeroFits)

          simpa [left, right] using hs.symm

        have hwrite1
            (t : Fin (ASize left)) :
            RegEncoding.writeNat left t.1
                (RegEncoding.writeNat right 1 b)
              =
            RegEncoding.writeNat r
              (t.1 + ASize left) b := by

          rw [
            RegEncoding.writeNat_comm_of_disjoint
              left right hdisj t.1 1 b
          ]

          have hs :=
            RegEncoding.writeNat_split
              r sp 1 t.1 b
              (by simp [left])
              (by simpa [right] using honeFits)

          simpa [left, right] using hs.symm

        ------------------------------------------------------------
        -- Cardinality:
        --
        -- ASize r = ASize left + ASize left.
        ------------------------------------------------------------

        have hAr :
            ASize r =
              ASize left + ASize left := by
          simp [
            ASize,
            hn,
            hleftSize,
            pow_succ,
            Nat.mul_two
          ]

        ------------------------------------------------------------
        -- Split the final Fin (2N) sum into its first and second
        -- blocks.
        ------------------------------------------------------------

        have hsum :
            (∑ t : Fin (ASize left),
                qs.ket
                  (RegEncoding.writeNat r t.1 b))
              +
            (∑ t : Fin (ASize left),
                qs.ket
                  (RegEncoding.writeNat r
                    (t.1 + ASize left) b))
              =
            ∑ u : Fin
                (ASize left + ASize left),
              qs.ket
                (RegEncoding.writeNat r u.1 b) := by
          symm
          simpa [Nat.add_comm] using
            (Fin.sum_univ_add
              (fun u :
                  Fin
                    (ASize left +
                      ASize left) =>
                qs.ket
                  (RegEncoding.writeNat
                    r u.1 b)))

        ------------------------------------------------------------
        -- Normalization:
        --
        -- 1/√2 · 1/√N = 1/√(2N).
        ------------------------------------------------------------

        have hnorm :
            ((1 / Real.sqrt (2 : ℝ) : ℂ) *
              (1 /
                Real.sqrt
                  ((ASize left : ℕ) : ℝ) : ℂ))
              =
            (1 /
              Real.sqrt
                (((ASize left +
                    ASize left : ℕ)) : ℝ) : ℂ) := by
          exact
            inv_sqrt_two_mul_inv_sqrt_nat
              (ASize left)
              (by simp [ASize])

        ------------------------------------------------------------
        -- Expand H(q), then apply IH to the two branches.
        ------------------------------------------------------------

        rw [hfold]
        simp [GateSemanticsCore.eval_seq]

        simp [HadamardSemantics.eval_H_ket]
        rw [hbit]
        --simp only [if_false, one_smul]

        -- Replace the singleton qubit register by `right`.
        rw [← hrightQ]

        rw [GateSemanticsCore.eval_add (qs := qs)]
        rw [GateSemanticsCore.eval_smul (qs := qs)]
        rw [if_neg (by decide : ¬ false = true)]
        rw [GateSemanticsCore.eval_smul (qs := qs)]
        have ih0' :
            GateSemanticsCore.eval
                (List.foldl (fun acc q => Gate.H q ;; acc) Gate.id (regQubits left))
                (ket (RegEncoding.writeNat right 0 b))
              =
            (1 / Real.sqrt ((ASize left : ℕ) : ℝ) : ℂ) •
              ∑ t : Fin (ASize left),
                ket (RegEncoding.writeNat left (t : ℕ)
                  (RegEncoding.writeNat right 0 b)) := by
          simpa [QSemantics.eval] using ih0
        have ih1' :
            GateSemanticsCore.eval
                (List.foldl (fun acc q => Gate.H q ;; acc) Gate.id (regQubits left))
                (ket (RegEncoding.writeNat right 1 b))
              =
            (1 / Real.sqrt ((ASize left : ℕ) : ℝ) : ℂ) •
              ∑ t : Fin (ASize left),
                ket (RegEncoding.writeNat left (t : ℕ)
                  (RegEncoding.writeNat right 1 b)) := by
          simpa [QSemantics.eval] using ih1
        rw [ih0', ih1']

        ------------------------------------------------------------
        -- Convert both induction sums to whole-register writes.
        ------------------------------------------------------------

        simp_rw [hwrite0]
        simp_rw [hwrite1]

        ------------------------------------------------------------
        -- Rewrite the target Fin (ASize r) as two Fin N blocks.
        ------------------------------------------------------------

        rw [hAr]
        rw [← hsum]

        ------------------------------------------------------------
        -- Both sides are now the same two sums with the same
        -- coefficient.
        ------------------------------------------------------------

        simp only [smul_add, smul_smul]
        have hnorm' :
            (↑(Real.sqrt (2 : ℝ)) : ℂ)⁻¹ *
                (1 / ↑(Real.sqrt ((ASize left : ℕ) : ℝ)) : ℂ)
              =
            (↑(Real.sqrt ((ASize left + ASize left : ℕ) : ℝ)) : ℂ)⁻¹ := by
          simpa [one_div] using hnorm
        rw [hnorm']

  exact
    hP
      (regSize r)
      r b
      rfl hzero

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
    Register-Hadamard Span Closure

    Applying Hadamards over qubits of a register stays in the finite span of
    basis states obtained by writing values into that register.
========================================================= -/

namespace RegisterHadamardSemantics

def ketSpan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (r : Reg)
    (b : qs.Basis) :
    Submodule ℂ qs.State :=
  Submodule.span ℂ
    (Set.range fun t : Fin (ASize r) =>
      qs.ket (RegEncoding.writeNat r t.1 b))


/-- If `b'` agrees with `b` outside `r`, then writing the value of
`b'` on `r` into `b` reconstructs `b'`. -/
theorem writeNat_rebase
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (b b' : Basis)
    (hout :
      ∀ q, q ∉ r.qubits →
        RegEncoding.bit q b' = RegEncoding.bit q b) :
    RegEncoding.writeNat r
        (RegEncoding.toNat r b') b = b' := by
  apply RegEncoding.basis_ext
  intro q
  by_cases hq : q ∈ r.qubits
  · calc
      RegEncoding.bit q
          (RegEncoding.writeNat r
            (RegEncoding.toNat r b') b)
          =
        RegEncoding.bit q
          (RegEncoding.writeNat r
            (RegEncoding.toNat r b') b') := by
            exact RegEncoding.bit_writeNat_in
              r (RegEncoding.toNat r b') b b' q hq

      _ = RegEncoding.bit q b' := by
            have h :=
              RegEncoding.writeNat_toNat r b'
            exact congrArg (RegEncoding.bit q) h

  · calc
      RegEncoding.bit q
          (RegEncoding.writeNat r
            (RegEncoding.toNat r b') b)
          =
        RegEncoding.bit q b := by
            exact RegEncoding.bit_writeNat_out
              r (RegEncoding.toNat r b') b q hq

      _ = RegEncoding.bit q b' := by
            symm
            exact hout q hq


/-- Changing one qubit belonging to `r` keeps the resulting basis ket in
the span of states obtained by writing values to `r`. -/
theorem ket_write_qubit_mem
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (r : Reg)
    (b : qs.Basis)
    (q : ℕ)
    (hq : q ∈ r.qubits)
    (v : ℕ)
    (t : Fin (ASize r)) :
    qs.ket
        (RegEncoding.writeNat (qubitReg q) v
          (RegEncoding.writeNat r t.1 b))
      ∈ ketSpan qs r b := by
  let b' : qs.Basis :=
    RegEncoding.writeNat (qubitReg q) v
      (RegEncoding.writeNat r t.1 b)

  have hout :
      ∀ p, p ∉ r.qubits →
        RegEncoding.bit p b' = RegEncoding.bit p b := by
    intro p hp

    have hpq : p ≠ q := by
      intro hpq
      subst p
      exact hp hq

    have hpqReg : p ∉ (qubitReg q).qubits := by
      simpa [qubitReg, Reg.singleton] using hpq

    calc
      RegEncoding.bit p b'
          =
        RegEncoding.bit p
          (RegEncoding.writeNat r t.1 b) := by
            exact RegEncoding.bit_writeNat_out
              (qubitReg q) v
              (RegEncoding.writeNat r t.1 b)
              p hpqReg

      _ = RegEncoding.bit p b := by
            exact RegEncoding.bit_writeNat_out
              r t.1 b p hp

  have hrebase :
      RegEncoding.writeNat r
          (RegEncoding.toNat r b') b = b' :=
    writeNat_rebase r b b' hout

  let u : Fin (ASize r) :=
    ⟨RegEncoding.toNat r b',
      RegEncoding.toNat_lt_ASize r b'⟩

  have hu :
      qs.ket (RegEncoding.writeNat r u.1 b)
        ∈ ketSpan qs r b := by
    apply Submodule.subset_span
    exact Set.mem_range.mpr ⟨u, rfl⟩

  simpa [u, hrebase] using hu


/-- A single Hadamard on a qubit belonging to `r` preserves the finite
register span. -/
theorem eval_H_mem
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [HadamardSemantics qs]
    (r : Reg)
    (b : qs.Basis)
    (q : ℕ)
    (hq : q ∈ r.qubits)
    {ψ : qs.State}
    (hψ : ψ ∈ ketSpan qs r b) :
    qs.eval (Gate.H q) ψ ∈ ketSpan qs r b := by

  let S := ketSpan qs r b

  change ψ ∈ S at hψ
  change qs.eval (Gate.H q) ψ ∈ S

  refine Submodule.span_induction
    (p := fun φ _ => qs.eval (Gate.H q) φ ∈ S)
    ?_ ?_ ?_ ?_ hψ

  · intro φ hφ
    rcases hφ with ⟨t, rfl⟩

    rw [HadamardSemantics.eval_H_ket]

    apply S.smul_mem

    apply S.add_mem

    · exact
        ket_write_qubit_mem
          qs r b q hq 0 t

    · apply S.smul_mem
      exact
        ket_write_qubit_mem
          qs r b q hq 1 t

  · simp

  · intro φ χ _ _ hφ hχ
    simp [GateSemanticsCore.eval_add]
    exact S.add_mem hφ hχ

  · intro a φ _ hφ
    simp [GateSemanticsCore.eval_smul]
    exact S.smul_mem a hφ


/-- Any fold of Hadamards whose qubits all belong to `r` preserves the same
register span. The accumulator form is chosen to match the actual `foldl`
definition of the H-register circuit. -/
theorem eval_foldl_H_mem
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [HadamardSemantics qs]
    (r : Reg)
    (b : qs.Basis)
    (l : List ℕ)
    (hl : ∀ q, q ∈ l → q ∈ r.qubits)
    (acc : Gate)
    (hacc :
      ∀ ψ : qs.State,
        ψ ∈ ketSpan qs r b →
        qs.eval acc ψ ∈ ketSpan qs r b) :
    ∀ ψ : qs.State,
      ψ ∈ ketSpan qs r b →
      qs.eval
          (l.foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            acc)
          ψ
        ∈ ketSpan qs r b := by
  induction l generalizing acc with
  | nil =>
      simpa using hacc

  | cons q l ih =>
      simp only [List.foldl_cons]

      apply ih

      · intro p hp
        exact hl p (by simp [hp])

      · intro ψ hψ
        simp [GateSemanticsCore.eval_seq]

        apply hacc

        exact eval_H_mem
          qs r b q
          (hl q (by simp))
          hψ



end RegisterHadamardSemantics

end SharedRegisterAndEvalFacts
end Shor


/-!
## Evaluator Projection Wrappers And Phase-Product Macros

The generic `eval` / algebra / encoding / norm lemmas built on the
`GateSemantics` classes.  These are used only in the lowering and correctness
proofs, so they live on the implementation side; Framework keeps just the
classes.
-/

universe u

namespace Shor

variable {Basis : Type u} [RegEncoding Basis]

open QSemantics

attribute [instance] QSemantics.instNormed
attribute [instance] QSemantics.instIP

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
    Bit And Basis Transport Helpers

    Local facts for comparing low-qubit writes with whole-register writes. They
    feed the Pauli-X and unsigned phase-product macro semantics below.
========================================================= -/

private theorem bit_writeNat_qubitReg
    {Basis : Type u}
    [RegEncoding Basis]
    (q v : ℕ)
    (b : Basis)
    (hv : v < 2) :
    RegEncoding.bit q
        (RegEncoding.writeNat (qubitReg q) v b)
      =
    Nat.testBit v 0 := by
  let i : Fin (regSize (qubitReg q)) := ⟨0, by simp⟩

  have hbit :=
    RegEncoding.bit_eq_testBit_toNat
      (qubitReg q)
      (RegEncoding.writeNat (qubitReg q) v b)
      i

  have hget : (qubitReg q).get i = q := by
    rfl

  rw [hget] at hbit

  have hv' : v < ASize (qubitReg q) := by
    simpa [ASize] using hv

  rw [
    RegEncoding.toNat_writeNat_of_lt
      (qubitReg q)
      v
      b
      hv'
  ] at hbit

  exact hbit

private theorem bit_of_toNat_zero_of_mem
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (b : Basis)
    (hzero : RegEncoding.toNat r b = 0)
    {q : ℕ}
    (hq : q ∈ r.qubits) :
    RegEncoding.bit q b = false := by
  rcases List.get_of_mem hq with ⟨j, hj⟩

  let i : Fin (regSize r) :=
    ⟨j.1, by simp [regSize, Reg.width]⟩

  have hget : r.get i = q := by
    dsimp [i, Reg.get]
    simpa [Reg.width] using hj

  have hbit :=
    RegEncoding.bit_eq_testBit_toNat r b i

  rw [hget, hzero] at hbit
  simpa using hbit

private theorem bit_writeNat_reg_one_of_mem
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (b : Basis)
    (hpos : 0 < regSize r)
    {q : ℕ}
    (hq : q ∈ r.qubits) :
    RegEncoding.bit q (RegEncoding.writeNat r 1 b)
      =
    if q = r.lowQubit hpos then true else false := by
  rcases List.get_of_mem hq with ⟨j, hj⟩

  let i : Fin (regSize r) :=
    ⟨j.1, by simp [regSize, Reg.width]⟩

  have hget : r.get i = q := by
    dsimp [i, Reg.get]
    simpa [Reg.width] using hj

  have hone_lt : 1 < ASize r := by
    simp [ASize]
    omega

  have hbit :=
    RegEncoding.bit_eq_testBit_toNat
      r
      (RegEncoding.writeNat r 1 b)
      i

  rw [
    hget,
    RegEncoding.toNat_writeNat_of_lt r 1 b hone_lt
  ] at hbit

  by_cases hq_low : q = r.lowQubit hpos

  · rw [if_pos hq_low]

    have hj_eq :
        j = ⟨0, by simpa [regSize, Reg.width] using hpos⟩ := by
      apply (r.nodup.get_inj_iff).mp
      change
        r.qubits.get j =
          r.qubits.get
            ⟨0, by simpa [regSize, Reg.width] using hpos⟩
      simpa [Reg.lowQubit] using hj.trans hq_low

    have hi0 : i.1 = 0 := by
      dsimp [i]
      simpa using congrArg Fin.val hj_eq

    simpa [hi0] using hbit

  · rw [if_neg hq_low]

    have hi_ne : i.1 ≠ 0 := by
      intro hi0
      apply hq_low
      rw [← hget]
      have ieq : i = ⟨0, hpos⟩ := Fin.ext hi0
      rw [ieq]
      rfl

    cases hi : i.1 with
    | zero =>
        contradiction
    | succ n =>
        have htb : Nat.testBit 1 (n + 1) = false := by
          change Nat.testBit (Nat.bit true 0) (Nat.succ n) = false
          rw [Nat.testBit_bit_succ]
          simp

        rw [hi] at hbit
        simpa [htb] using hbit

private theorem writeNat_lowQubit_one_of_toNat_zero
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (b : Basis)
    (hpos : 0 < regSize r)
    (hzero : RegEncoding.toNat r b = 0) :
    RegEncoding.writeNat (qubitReg (r.lowQubit hpos)) 1 b
      =
    RegEncoding.writeNat r 1 b := by
  apply RegEncoding.basis_ext
  intro q

  by_cases hqr : q ∈ r.qubits

  · rw [bit_writeNat_reg_one_of_mem r b hpos hqr]

    by_cases hq_low : q = r.lowQubit hpos

    · subst q
      simp [bit_writeNat_qubitReg]

    · rw [if_neg hq_low]

      have hqout :
          q ∉ (qubitReg (r.lowQubit hpos)).qubits := by
        simpa [qubitReg, Reg.singleton] using hq_low

      rw [
        RegEncoding.bit_writeNat_out
          (qubitReg (r.lowQubit hpos))
          1
          b
          q
          hqout
      ]

      exact bit_of_toNat_zero_of_mem r b hzero hqr

  · have hqout_r : q ∉ r.qubits := hqr

    have hqout_low :
        q ∉ (qubitReg (r.lowQubit hpos)).qubits := by
      intro hq

      have hlow_mem : r.lowQubit hpos ∈ r.qubits := by
        unfold Reg.lowQubit
        exact List.get_mem r.qubits _

      have hqeq : q = r.lowQubit hpos := by
        simpa [qubitReg, Reg.singleton] using hq

      exact hqr (by simpa [hqeq] using hlow_mem)

    rw [
      RegEncoding.bit_writeNat_out
        (qubitReg (r.lowQubit hpos))
        1
        b
        q
        hqout_low,
      RegEncoding.bit_writeNat_out
        r
        1
        b
        q
        hqout_r
    ]

/-! =========================================================
    Pauli-X And Extension Locality

    These bridge primitive register actions back to basis-state extensionality:
    one Pauli-X write on a zero register, and zero-extension preserving bits.
========================================================= -/

namespace PauliXSemantics

theorem eval_X_low_zero_reg_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [PauliXSemantics qs]
    (r : Reg)
    (b : qs.Basis)
    (hpos : 0 < regSize r)
    (hzero : RegEncoding.toNat r b = 0) :
    qs.eval (Gate.X (r.lowQubit hpos)) (qs.ket b)
      =
    qs.ket (RegEncoding.writeNat r 1 b) := by
  rw [PauliXSemantics.eval_X_ket]

  have hbit :
      RegEncoding.bit (r.lowQubit hpos) b = false :=
    bit_of_toNat_zero_of_mem r b hzero (by
      unfold Reg.lowQubit
      exact List.get_mem r.qubits _)

  rw [hbit]
  simp [writeNat_lowQubit_one_of_toNat_zero r b hpos hzero]

end PauliXSemantics


lemma zeroExtend_preserves_bit
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ExtensionSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b b' : qs.Basis)
    (q : ℕ)
    (hEval :
      qs.eval (Gate.zeroExtend r n) (qs.ket b) =
        qs.ket b') :
    RegEncoding.bit q b' =
      RegEncoding.bit q b := by
  have hket :
      qs.ket b = qs.ket b' := by
    calc
      qs.ket b
          = qs.eval (Gate.zeroExtend r n) (qs.ket b) := by
              symm
              exact ExtensionSemantics.eval_zeroExtend
                r n (qs.ket b)
      _ = qs.ket b' := hEval

  have hb : b = b' := qs.ket_inj hket
  subst b'
  rfl

/-! =========================================================
    Unsigned Phase-Product Macro Semantics

    The unsigned macros are implemented by extending the operands, invoking the
    signed phase-product gate, and deallocating the temporary sign bits.
========================================================= -/

namespace GateSemanticsFacts

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [GateSemanticsFacts qs]

private lemma zeroExtend_preserves_bit
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ExtensionSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b b' : qs.Basis)
    (q : ℕ)
    (hEval :
      qs.eval (Gate.zeroExtend r n) (qs.ket b) = qs.ket b') :
    RegEncoding.bit q b' = RegEncoding.bit q b := by
  classical
  exact Shor.zeroExtend_preserves_bit qs r n b b' q hEval

open Gate
/--
Semantic bridge for the unsigned macro: on clean workspace, `PhaseProdUsing` contributes
exactly the expected phase `exp(i * phi * x * z)` and restores the basis state.
-/
theorem eval_PhaseProdUsing_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (phi : ℝ)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (b : qs.Basis)
    (hclean : ws.Clean b) :
    qs.eval
        (Gate.PhaseProdUsing phi x z ws)
        (qs.ket b)
      =
    Complex.exp
        (phi * Complex.I *
          ((RegEncoding.toNat x b : ℂ) *
           (RegEncoding.toNat z b : ℂ))) •
      qs.ket b := by
  have hxFresh :
      ws.xExt.FreshFor 1 b :=
    hclean.1

  have hzFresh :
      ws.zExt.FreshFor 1 b :=
    hclean.2

  have hxInt :
      extToInt
          (ws.xExt.grow 1) b
        =
      (RegEncoding.toNat x b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.xExt)
        (n := 1)
        (b := b)
        ws.xExt_canGrow
        hxFresh
        (by omega))

  have hzInt :
      extToInt
          (ws.zExt.grow 1) b
        =
      (RegEncoding.toNat z b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.zExt)
        (n := 1)
        (b := b)
        ws.zExt_canGrow
        hzFresh
        (by omega))

  simp only [
    Gate.PhaseProdUsing,
    qs.eval_seq,
    ExtensionSemantics.eval_zeroExtend,
    ExtensionSemantics.eval_zeroDealloc
  ]

  rw [PhaseSemantics.eval_SignedPhaseProd_ket]
  rw [hxInt, hzInt]

  simp

/-- Controlled version of `eval_PhaseProdUsing_ket`; the phase appears only when `ctrl` is one. -/
theorem eval_CPhaseProdUsing_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (b : qs.Basis)
    (hclean : ws.Clean b):
    qs.eval
        (Gate.CPhaseProdUsing ctrl phi x z ws)
        (qs.ket b)
      =
    (if RegEncoding.bit ctrl b then
        Complex.exp
          (phi * Complex.I *
            ((RegEncoding.toNat x b : ℂ) *
             (RegEncoding.toNat z b : ℂ)))
      else
        1) •
      qs.ket b := by
  have hxFresh :
      ws.xExt.FreshFor 1 b :=
    hclean.1

  have hzFresh :
      ws.zExt.FreshFor 1 b :=
    hclean.2

  have hxInt :
      extToInt
          (ws.xExt.grow 1) b
        =
      (RegEncoding.toNat x b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.xExt)
        (n := 1)
        (b := b)
        ws.xExt_canGrow
        hxFresh
        (by omega))

  have hzInt :
      extToInt
          (ws.zExt.grow 1) b
        =
      (RegEncoding.toNat z b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.zExt)
        (n := 1)
        (b := b)
        ws.zExt_canGrow
        hzFresh
        (by omega))

  simp only [Gate.CPhaseProdUsing, qs.eval_seq, ExtensionSemantics.eval_zeroExtend,ExtensionSemantics.eval_zeroDealloc]

  rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
  rw [hxInt, hzInt]

  by_cases hc : RegEncoding.bit ctrl b
  · simp [hc]
  · simp [hc]

end GateSemanticsFacts

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
    Encoding Transport
========================================================= -/

lemma toNat_left_write_right [QSemantics] [RegEncoding (QSemantics.Basis)]
  (left right : Reg) (h : Disjoint left right) (b : QSemantics.Basis) (yR : ℕ) :
  RegEncoding.toNat left (RegEncoding.writeNat right yR b)
    = RegEncoding.toNat left b := by
  simpa using
    (RegEncoding.toNat_left_write_right
      (left := left) (right := right) (Basis:=QSemantics.Basis) (b := b) (yR := yR) h)

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






end Shor
