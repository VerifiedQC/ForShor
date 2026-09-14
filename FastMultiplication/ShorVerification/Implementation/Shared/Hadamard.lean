import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.Shared.Registers
import FastMultiplication.ShorVerification.Implementation.Shared.States

/-!
# `H_reg` on a register: uniform superposition and span closure

Generic facts about one-qubit registers, zero-valued splits, Hadamard uniform
superpositions, and the normalization constants that appear in
register-Hadamard proofs, plus the fact that applying Hadamards over qubits of
a register stays in the finite span of basis states obtained by writing values
into that register.
-/

namespace Shor
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
        simp

        simp [HadamardSemantics.eval_H_ket]
        rw [hbit]
        --simp only [if_false, one_smul]

        -- Replace the singleton qubit register by `right`.
        rw [← hrightQ]

        simp only [GateSemanticsCore.eval_add (qs := qs)]
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
        simp

        apply hacc

        exact eval_H_mem
          qs r b q
          (hl q (by simp))
          hψ



end RegisterHadamardSemantics


end Shor
