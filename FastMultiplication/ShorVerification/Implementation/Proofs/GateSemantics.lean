import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Gate semantics derived facts

Proof-side consequences of the semantic interfaces from
`Framework.Semantics.GateSemantics`. The framework file keeps only classes and
user-facing definitions; derived evaluator laws, QFT special cases, and
register-Hadamard facts live here on the implementation side.
-/

universe u

namespace Shor

variable {Basis : Type u} [RegEncoding Basis]

open QSemantics

attribute [instance] QSemantics.instNormed
attribute [instance] QSemantics.instIP

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


namespace QFTSemantics

theorem eval_QFT_size0_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [QFTSemantics qs]
    (r : ExtReg)
    (b : qs.Basis)
    (hsize : r.width = 0) :
    qs.eval (Gate.QFT r) (qs.ket b) = qs.ket b := by

  have hactive : regSize r.active = 0 := by
    simpa [ExtReg.width] using hsize

  have hread : RegEncoding.toNat r.active b = 0 := by
    have hlt := RegEncoding.toNat_lt_ASize r.active b
    simp [ASize, hactive] at hlt
    omega

  have hwrite :
      RegEncoding.writeNat r.active 0 b = b := by
    rw [← hread]
    exact RegEncoding.writeNat_toNat r.active b

  rw [QFTSemantics.eval_QFT_ket]
  rw [hsize]

  simp [qftPhase, ωPow, hwrite]

theorem eval_QFT_size0
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [QFTSemantics qs]
    (r : ExtReg)
    (ψ : qs.State)
    (hsize : r.width = 0) :
    qs.eval (Gate.QFT r) ψ = qs.eval Gate.id ψ := by

  have h :
      ∀ φ : qs.State,
        qs.eval (Gate.QFT r) φ = φ := by
    intro φ

    apply qs.state_induction
      (P := fun φ => qs.eval (Gate.QFT r) φ = φ)

    · simp [GateSemanticsCore.eval_zero]

    · intro φ χ hφ hχ
      unfold eval at *
      rw [GateSemanticsCore.eval_add]
      rw [hφ, hχ]

    · intro a φ hφ
      unfold eval at *
      rw [GateSemanticsCore.eval_smul]
      rw [hφ]

    · intro b
      exact eval_QFT_size0_ket (qs := qs) r b hsize

  rw [h ψ]
  symm
  exact GateSemanticsCore.eval_id ψ

theorem eval_adj_QFT_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [QFTSemantics qs]
    (r : ExtReg)
    (b : qs.Basis) :
    qs.eval (Gate.adj (Gate.QFT r)) (qs.ket b)
      =
    ((1 / Real.sqrt ((ASize r.active : ℕ) : ℝ) : ℂ)) •
      ∑ y : Fin (ASize r.active),
        star
            (qftPhase
              (ASize r.active)
              (ExtReg.toNat r b)
              y.1) •
          qs.ket
            (RegEncoding.writeNat
              r.active y.1 b) := by
  classical

  let N : ℕ := ASize r.active
  let c : ℂ := (1 / Real.sqrt (N : ℝ) : ℂ)
  let x : ℕ := ExtReg.toNat r b

  have hxlt : x < N := by
    simpa [x, N, ExtReg.toNat] using
      (RegEncoding.toNat_lt_ASize r.active b)

  let ix : Fin N := ⟨x, hxlt⟩

  apply GateSemanticsCore.state_eq_of_inner_ket_eq qs
  intro d

  let t : ℕ := ExtReg.toNat r d

  have htlt : t < N := by
    simpa [t, N, ExtReg.toNat] using
      (RegEncoding.toNat_lt_ASize r.active d)

  let it : Fin N := ⟨t, htlt⟩

  have hN :
      2 ^ r.width = N := by
    simp [N, ASize, ExtReg.width]

  rw [GateSemanticsCore.inner_eval_adj (qs := qs)]
  rw [QFTSemantics.eval_QFT_ket]
  rw [hN]

  change
    inner ℂ
        (qs.ket b)
        (c •
          ∑ z : Fin N,
            qftPhase N t z.1 •
              qs.ket
                (RegEncoding.writeNat r.active z.1 d))
      =
    inner ℂ
        (c •
          ∑ y : Fin N,
            star (qftPhase N x y.1) •
              qs.ket
                (RegEncoding.writeNat r.active y.1 b))
        (qs.ket d)

  have hc :
      (starRingEnd ℂ) c = c := by
    simp [c]

  by_cases hdb :
      RegEncoding.writeNat r.active t b = d

  · ----------------------------------------------------------------
    -- GOOD CASE:
    -- d differs from b only on the active register.
    ----------------------------------------------------------------

    have hxb :
        RegEncoding.writeNat r.active x d = b := by
      calc
        RegEncoding.writeNat r.active x d
            =
          RegEncoding.writeNat r.active x
            (RegEncoding.writeNat r.active t b) := by
              rw [hdb]

        _ =
          RegEncoding.writeNat r.active x b := by
            exact
              RegEncoding.writeNat_overwrite
                r.active x t b

        _ = b := by
          simpa [x, ExtReg.toNat] using
            (RegEncoding.writeNat_toNat r.active b)

    ------------------------------------------------------------
    -- Collapse the forward-QFT inner-product sum at z = x.
    ------------------------------------------------------------

    have hforward :
        (∑ z : Fin N,
          inner ℂ
            (qs.ket b)
            (qftPhase N t z.1 •
              qs.ket
                (RegEncoding.writeNat
                  r.active z.1 d)))
          =
        qftPhase N t x := by

      calc
        (∑ z : Fin N,
          inner ℂ
            (qs.ket b)
            (qftPhase N t z.1 •
              qs.ket
                (RegEncoding.writeNat
                  r.active z.1 d)))
            =
          inner ℂ
            (qs.ket b)
            (qftPhase N t ix.1 •
              qs.ket
                (RegEncoding.writeNat
                  r.active ix.1 d)) := by

            apply Fintype.sum_eq_single ix
            intro z hz

            have hwrite_ne :
                RegEncoding.writeNat r.active z.1 d ≠ b := by
              intro hwrite

              have hread :=
                congrArg
                  (RegEncoding.toNat r.active)
                  hwrite

              have hzlt :
                  z.1 < ASize r.active := by
                simp[N]

              rw [
                RegEncoding.toNat_writeNat_of_lt
                  r.active z.1 d hzlt
              ] at hread

              apply hz
              apply Fin.ext

              simpa [ix, x, ExtReg.toNat] using hread

            rw [inner_smul_right]

            have horth :
                inner ℂ
                    (qs.ket b)
                    (qs.ket
                      (RegEncoding.writeNat
                        r.active z.1 d))
                  =
                0 := by
              exact
                qs.ket_inner_eq_zero_of_ne
                  (Ne.symm hwrite_ne)

            rw [horth]
            simp

        _ = qftPhase N t x := by
          rw [inner_smul_right]

          have hket :
              inner ℂ
                  (qs.ket b)
                  (qs.ket
                    (RegEncoding.writeNat
                      r.active ix.1 d))
                =
              1 := by
            apply qs.ket_inner_eq_of_eq
            simpa [ix] using hxb.symm

          rw [hket]
          simp [ix]

    ------------------------------------------------------------
    -- Collapse the proposed inverse-QFT sum at y = t.
    ------------------------------------------------------------

    have hinverse :
        (∑ y : Fin N,
          inner ℂ
            (star (qftPhase N x y.1) •
              qs.ket
                (RegEncoding.writeNat
                  r.active y.1 b))
            (qs.ket d))
          =
        qftPhase N x t := by

      calc
        (∑ y : Fin N,
          inner ℂ
            (star (qftPhase N x y.1) •
              qs.ket
                (RegEncoding.writeNat
                  r.active y.1 b))
            (qs.ket d))
            =
          inner ℂ
            (star (qftPhase N x it.1) •
              qs.ket
                (RegEncoding.writeNat
                  r.active it.1 b))
            (qs.ket d) := by

            apply Fintype.sum_eq_single it
            intro y hy

            have hwrite_ne :
                RegEncoding.writeNat r.active y.1 b ≠ d := by
              intro hwrite

              have hread :=
                congrArg
                  (RegEncoding.toNat r.active)
                  hwrite

              have hylt :
                  y.1 < ASize r.active := by
                simp[N]

              rw [
                RegEncoding.toNat_writeNat_of_lt
                  r.active y.1 b hylt
              ] at hread

              apply hy
              apply Fin.ext

              simpa [it, t, ExtReg.toNat] using hread

            rw [inner_smul_left]

            have horth :
                inner ℂ
                    (qs.ket
                      (RegEncoding.writeNat
                        r.active y.1 b))
                    (qs.ket d)
                  =
                0 := by
              exact
                qs.ket_inner_eq_zero_of_ne
                  hwrite_ne

            rw [horth]
            simp

        _ = qftPhase N x t := by
          rw [inner_smul_left]

          have hket :
              inner ℂ
                  (qs.ket
                    (RegEncoding.writeNat
                      r.active it.1 b))
                  (qs.ket d)
                =
              1 := by
            apply qs.ket_inner_eq_of_eq
            simpa [it] using hdb

          rw [hket]
          simp [it]

    ------------------------------------------------------------
    -- Both sides now have the same single Fourier coefficient.
    ------------------------------------------------------------

    rw [inner_smul_right, inner_smul_left]
    rw [inner_sum, sum_inner]
    rw [hforward, hinverse]
    rw [hc]
    rw [qftPhase_comm N t x]

  · ----------------------------------------------------------------
    -- BAD CASE:
    -- d does not agree with b outside the active register.
    -- No basis term on either side can survive.
    ----------------------------------------------------------------

    have hforward :
        (∑ z : Fin N,
          inner ℂ
            (qs.ket b)
            (qftPhase N t z.1 •
              qs.ket
                (RegEncoding.writeNat
                  r.active z.1 d)))
          =
        0 := by

      apply Fintype.sum_eq_zero
      intro z

      have hwrite_ne :
          RegEncoding.writeNat r.active z.1 d ≠ b := by
        intro hwrite

        have hcontr :
            RegEncoding.writeNat r.active t b = d := by
          calc
            RegEncoding.writeNat r.active t b
                =
              RegEncoding.writeNat r.active t
                (RegEncoding.writeNat
                  r.active z.1 d) := by
                    rw [hwrite]

            _ =
              RegEncoding.writeNat r.active t d := by
                exact
                  RegEncoding.writeNat_overwrite
                    r.active t z.1 d

            _ = d := by
              simpa [t, ExtReg.toNat] using
                (RegEncoding.writeNat_toNat
                  r.active d)

        exact hdb hcontr

      rw [inner_smul_right]

      have horth :
          inner ℂ
              (qs.ket b)
              (qs.ket
                (RegEncoding.writeNat
                  r.active z.1 d))
            =
          0 := by
        exact
          qs.ket_inner_eq_zero_of_ne
            (Ne.symm hwrite_ne)

      rw [horth]
      simp

    have hinverse :
        (∑ y : Fin N,
          inner ℂ
            (star (qftPhase N x y.1) •
              qs.ket
                (RegEncoding.writeNat
                  r.active y.1 b))
            (qs.ket d))
          =
        0 := by

      apply Fintype.sum_eq_zero
      intro y

      have hwrite_ne :
          RegEncoding.writeNat r.active y.1 b ≠ d := by
        intro hwrite

        have hread :=
          congrArg
            (RegEncoding.toNat r.active)
            hwrite

        have hylt :
            y.1 < ASize r.active := by
          simp[N]
        rw [
          RegEncoding.toNat_writeNat_of_lt
            r.active y.1 b hylt
        ] at hread

        have hy_t : y.1 = t := by
          simpa [t, ExtReg.toNat] using hread

        apply hdb
        simpa [hy_t] using hwrite

      rw [inner_smul_left]

      have horth :
          inner ℂ
              (qs.ket
                (RegEncoding.writeNat
                  r.active y.1 b))
              (qs.ket d)
            =
          0 := by
        exact
          qs.ket_inner_eq_zero_of_ne
            hwrite_ne

      rw [horth]
      simp

    rw [inner_smul_right, inner_smul_left]
    rw [inner_sum, sum_inner]
    rw [hforward, hinverse]
    simp

end QFTSemantics


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

namespace QFTSemantics

theorem eval_QFT_size1_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [QFTSemantics qs]
    [HadamardSemantics qs]
    (r : ExtReg)
    (b : qs.Basis)
    (hsize : r.width = 1) :
    qs.eval (Gate.QFT r) (qs.ket b) =
      qs.eval
        (Gate.H
          (r.active.lowQubit (by
            simp [ExtReg.width] at hsize
            omega)))
        (qs.ket b) := by

  have hactive_size : regSize r.active = 1 := by
    simpa [ExtReg.width] using hsize

  let hpos : 0 < regSize r.active := by
    omega

  let q : ℕ := r.active.lowQubit hpos

  change qs.eval (Gate.QFT r) (qs.ket b) = qs.eval (Gate.H q) (qs.ket b)

  have hactive :
      r.active = qubitReg q := by
    simpa [q] using
      Reg.eq_qubitReg_lowQubit r.active hactive_size

  -- The value stored in the one-bit register is either 0 or 1.
  have hxlt :
      ExtReg.toNat r b < 2 := by
    have h := ExtReg.toNat_lt r b
    simpa [hsize] using h

  -- Logical bit 0 of the active register is precisely physical qubit q.
  have hbit :
      RegEncoding.bit q b =
        Nat.testBit (ExtReg.toNat r b) 0 := by
    have h :=
      RegEncoding.bit_eq_testBit_toNat
        (qubitReg q)
        b
        (⟨0, by simp⟩ : Fin (regSize (qubitReg q)))

    simpa [
      ExtReg.toNat,
      hactive,
      qubitReg,
      Reg.singleton,
      Reg.get,
      regSize,
      Reg.width
    ] using h

  -- Hence the numeric value of this one-bit register is exactly its bit.
  have hx :
      ExtReg.toNat r b =
        if RegEncoding.bit q b then 1 else 0 := by
    have hx_cases :
        ExtReg.toNat r b = 0 ∨
          ExtReg.toNat r b = 1 := by
      omega

    rcases hx_cases with hx0 | hx1
    · have hb :
          RegEncoding.bit q b = false := by
        simpa [hx0] using hbit
      simp [hx0, hb]

    · have hb :
          RegEncoding.bit q b = true := by
        simpa [hx1] using hbit
      simp [hx1, hb]

  -- y = 0 contributes phase 1.
  have hphase0 :
      qftPhase 2 (ExtReg.toNat r b) 0 = 1 := by
    simp [qftPhase, ωPow]

  -- y = 1 contributes +1 or -1 according to the input bit.
  have hphase1 :
      qftPhase 2 (ExtReg.toNat r b) 1 =
        if RegEncoding.bit q b then (-1 : ℂ) else 1 := by
    rw [hx]
    cases hb : RegEncoding.bit q b <;> simp [qftPhase, ωPow, omega_two]
  rw [QFTSemantics.eval_QFT_ket, HadamardSemantics.eval_H_ket]
  rw [hsize]
  simp [pow_one]
  simp at *
  rw [hactive, hphase0, hphase1]
  simp

theorem eval_QFT_size1
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [QFTSemantics qs]
    [HadamardSemantics qs]
    (r : ExtReg)
    (ψ : qs.State)
    (hsize : r.width = 1) :
    qs.eval (Gate.QFT r) ψ =
      qs.eval
        (Gate.H
          (r.active.lowQubit (by
            simp [ExtReg.width] at hsize
            omega)))
        ψ := by

  have h :
      ∀ φ : qs.State,
        qs.eval (Gate.QFT r) φ =
          qs.eval
            (Gate.H
              (r.active.lowQubit (by
                simp [ExtReg.width] at hsize
                omega)))
            φ := by
    intro φ

    apply qs.state_induction
      (P := fun φ =>
        qs.eval (Gate.QFT r) φ =
          qs.eval
            (Gate.H
              (r.active.lowQubit (by
                simp [ExtReg.width] at hsize
                omega)))
            φ)

    · simp [GateSemanticsCore.eval_zero]

    · intro φ χ hφ hχ
      unfold QSemantics.eval at *
      rw [
        GateSemanticsCore.eval_add,
        GateSemanticsCore.eval_add,
        hφ,
        hχ
      ]

    · intro a φ hφ
      unfold QSemantics.eval at *
      rw [
        GateSemanticsCore.eval_smul,
        GateSemanticsCore.eval_smul,
        hφ
      ]

    · intro b
      exact eval_QFT_size1_ket (qs := qs) r b hsize

  exact h ψ

end QFTSemantics


namespace RegisterHadamardSemantics

private def ketSpan
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
private theorem writeNat_rebase
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
private theorem ket_write_qubit_mem
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
private theorem eval_H_mem
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
private theorem eval_foldl_H_mem
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


/-- The original `RegisterHadamardSemantics` result, derived solely from
ordinary one-qubit Hadamard semantics and the generic evaluator laws. -/
theorem eval_Hreg_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [HadamardSemantics qs]
    (r : Reg)
    (b : qs.Basis) :
    ∃ α : Fin (ASize r) → ℂ,
      qs.eval
          ((regQubits r).foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            Gate.id)
          (qs.ket b)
        =
      ∑ t : Fin (ASize r),
        α t •
          qs.ket
            (RegEncoding.writeNat r t.1 b) := by
  classical

  let S := ketSpan qs r b

  -- The initial ket is already one of the generators:
  -- choose the value currently stored in r.
  let t₀ : Fin (ASize r) :=
    ⟨RegEncoding.toNat r b,
      RegEncoding.toNat_lt_ASize r b⟩

  have hstart :
      qs.ket b ∈ S := by
    have hmem :
        qs.ket (RegEncoding.writeNat r t₀.1 b)
          ∈ S := by
      change
        qs.ket (RegEncoding.writeNat r t₀.1 b)
          ∈ Submodule.span ℂ
              (Set.range fun t : Fin (ASize r) =>
                qs.ket
                  (RegEncoding.writeNat r t.1 b))

      apply Submodule.subset_span
      exact Set.mem_range.mpr ⟨t₀, rfl⟩

    simpa [t₀, RegEncoding.writeNat_toNat] using hmem

  -- Every H in the fold acts on a qubit of r, hence the entire folded
  -- circuit stays inside S.
  have hout :
      qs.eval
          ((regQubits r).foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            Gate.id)
          (qs.ket b)
        ∈ S := by

    apply
      eval_foldl_H_mem
        qs r b
        (regQubits r)

    · intro q hq
      exact hq

    · intro ψ hψ
      simp [GateSemanticsCore.eval_id]
      exact hψ

    · exact hstart

  -- Membership in the span of a finite family is exactly existence of
  -- finite coefficients indexed by that family.
  have hout' :
      qs.eval
          ((regQubits r).foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            Gate.id)
          (qs.ket b)
        ∈
      Submodule.span ℂ
        (Set.range fun t : Fin (ASize r) =>
          qs.ket
            (RegEncoding.writeNat r t.1 b)) := by
    exact hout

  rcases
      (Submodule.mem_span_range_iff_exists_fun ℂ).mp hout'
    with ⟨α, hα⟩

  refine ⟨α, ?_⟩

  exact hα.symm

end RegisterHadamardSemantics


theorem splitLeft_one_eq_qubitReg_low
    (r : Reg)
    (h : 0 < regSize r) :
    splitLeft r ⟨1, by omega⟩ =
      qubitReg (r.lowQubit h) := by
  cases r with
  | mk qs hnd =>
      cases qs with
      | nil =>
          simp [regSize, Reg.width] at h
      | cons q qs =>
          simp [
            splitLeft, Reg.take,
            qubitReg, Reg.singleton,
            Reg.lowQubit]

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

theorem eval_foldl_H_acc
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (l : List ℕ)
    (acc : Gate)
    (ψ : qs.State) :
    qs.eval
        (l.foldl
          (fun acc q => Gate.seq (Gate.H q) acc)
          acc)
        ψ
      =
    qs.eval acc
      (qs.eval
        (l.foldl
          (fun acc q => Gate.seq (Gate.H q) acc)
          Gate.id)
        ψ) := by
  induction l generalizing acc ψ with
  | nil =>
      simp [GateSemanticsCore.eval_id]

  | cons q l ih =>
      simp only [List.foldl_cons]
      calc
        qs.eval
            (l.foldl
              (fun acc q => Gate.seq (Gate.H q) acc)
              (Gate.seq (Gate.H q) acc))
            ψ
          =
        qs.eval (Gate.seq (Gate.H q) acc)
            (qs.eval
              (l.foldl
                (fun acc q => Gate.seq (Gate.H q) acc)
                Gate.id)
              ψ) := by
            exact ih (Gate.seq (Gate.H q) acc) ψ
        _ =
        qs.eval acc
            (qs.eval (Gate.H q)
              (qs.eval
                (l.foldl
                  (fun acc q => Gate.seq (Gate.H q) acc)
                  Gate.id)
                ψ)) := by
            exact
              GateSemanticsCore.eval_seq
                (qs := qs)
                (Gate.H q)
                acc
                (qs.eval
                  (l.foldl
                    (fun acc q => Gate.seq (Gate.H q) acc)
                    Gate.id)
                  ψ)
        _ =
        qs.eval acc
            (qs.eval
              (l.foldl
                (fun acc q => Gate.seq (Gate.H q) acc)
                (Gate.seq (Gate.H q) Gate.id))
              ψ) := by
            have hfold :=
              ih (Gate.seq (Gate.H q) Gate.id) ψ
            rw [hfold]
            have hid :
                qs.eval (Gate.seq (Gate.H q) Gate.id)
                    (qs.eval
                      (l.foldl
                        (fun acc q => Gate.seq (Gate.H q) acc)
                        Gate.id)
                      ψ)
                  =
                qs.eval (Gate.H q)
                    (qs.eval
                      (l.foldl
                        (fun acc q => Gate.seq (Gate.H q) acc)
                        Gate.id)
                      ψ) := by
              calc
                qs.eval (Gate.seq (Gate.H q) Gate.id)
                    (qs.eval
                      (l.foldl
                        (fun acc q => Gate.seq (Gate.H q) acc)
                        Gate.id)
                      ψ)
                    =
                  qs.eval Gate.id
                    (qs.eval (Gate.H q)
                      (qs.eval
                        (l.foldl
                          (fun acc q => Gate.seq (Gate.H q) acc)
                          Gate.id)
                        ψ)) := by
                    exact
                      GateSemanticsCore.eval_seq
                        (qs := qs)
                        (Gate.H q)
                        Gate.id
                        (qs.eval
                          (l.foldl
                            (fun acc q => Gate.seq (Gate.H q) acc)
                            Gate.id)
                          ψ)
                _ =
                  qs.eval (Gate.H q)
                    (qs.eval
                      (l.foldl
                        (fun acc q => Gate.seq (Gate.H q) acc)
                        Gate.id)
                      ψ) := by
                    exact
                      GateSemanticsCore.eval_id
                        (qs := qs)
                        (qs.eval (Gate.H q)
                          (qs.eval
                            (l.foldl
                              (fun acc q => Gate.seq (Gate.H q) acc)
                              Gate.id)
                            ψ))
            rw [hid]

private theorem inv_sqrt_two_mul_inv_sqrt_nat
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

theorem eval_Hreg_zero_eq_QFT
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [QFTSemantics qs]
    [HadamardSemantics qs]
    (r : ExtReg)
    (b : qs.Basis)
    (hzero : ExtReg.toNat r b = 0) :
    qs.eval
        ((regQubits r.active).foldl
          (fun acc q => Gate.seq (Gate.H q) acc)
          Gate.id)
        (qs.ket b)
      =
    qs.eval (Gate.QFT r) (qs.ket b) := by

  rw [
    eval_Hreg_zero_uniform
      qs r.active b
      (by simpa [ExtReg.toNat] using hzero)
  ]

  rw [QFTSemantics.eval_QFT_ket]

  have hN :
      2 ^ r.width = ASize r.active := by
    rfl

  rw [hN]

  have hx :
      ExtReg.toNat r b = 0 := hzero

  rw [hx]

  simp [qftPhase, ωPow]


namespace GateSemanticsFacts

/-- Bundled-interface spelling of `eval_Hreg_zero_eq_QFT`. -/
theorem eval_Hreg_zero_eq_QFT
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (r : ExtReg)
    (b : qs.Basis)
    (hzero : ExtReg.toNat r b = 0) :
    qs.eval
        ((regQubits r.active).foldl
          (fun acc q => Gate.seq (Gate.H q) acc)
          Gate.id)
        (qs.ket b)
      =
    qs.eval (Gate.QFT r) (qs.ket b) := by
  exact Shor.eval_Hreg_zero_eq_QFT qs r b hzero

end GateSemanticsFacts

end Shor
