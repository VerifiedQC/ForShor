import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.GateConstructions
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# GateSemantics eval lemmas (implementation proof-support)

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

namespace GateSemanticsFacts

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [GateSemanticsFacts qs]

theorem eval_RadixReverse_split_ket
  (r : Reg) (m : ℕ) (hm : m ≤ regSize r) (b : qs.Basis)
  (kL kH : ℕ)
  (hkL : kL < ASize (splitLeft r ⟨m, hm⟩))
  (hkH : kH < ASize (splitRight r ⟨m, hm⟩)) :
  qs.eval (Gate.RadixReverse r m)
    (qs.ket
      (RegEncoding.writeNat (splitLeft r ⟨m, hm⟩) kL
        (RegEncoding.writeNat (splitRight r ⟨m, hm⟩) kH b)))
  =
  qs.ket
    (RegEncoding.writeNat r
      (radixReverseIndex r m hm kL kH)
      b) := by
  simpa [radixReverseIndex] using
    (RadixReverseSemantics.eval_RadixReverse_ket
      (qs := qs)
      (r := r) (m := m) (hm := hm) (b := b)
      (kL := kL) (kH := kH)
      hkL
      hkH)


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

lemma eval_CSignedPhaseProd_ket_as_if_SignedPhaseProd
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [PhaseSemantics qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (b : qs.Basis) :
    qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b)
      =
    if RegEncoding.bit ctrl b then
      qs.eval (Gate.SignedPhaseProd phi x z) (qs.ket b)
    else
      qs.ket b := by
  by_cases hctrl : RegEncoding.bit ctrl b
  ·
    rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
    rw [if_pos hctrl, if_pos hctrl]
    exact
      (PhaseSemantics.eval_SignedPhaseProd_ket
        (qs := qs) phi x z b).symm
  ·
    rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
    rw [if_neg hctrl, if_neg hctrl]

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
    Section 8: General algebraic lemmas for `eval`
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
  · simp [QSemantics.eval_zero]
  · intro a s ha hs
    simp [Finset.sum_insert ha, QSemantics.eval_add, hs]

lemma eval_sum_univ
    {α : Type}
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [Fintype α]
    (U : Gate)
    (f : α → qs.State) :
    qs.eval U (∑ a : α, f a) = ∑ a : α, qs.eval U (f a) := by
  have := (eval_sum qs U Finset.univ f)
  aesop

/-! =========================================================
    Section 9: Encoding transport lemmas
========================================================= -/

lemma toNat_left_write_right [QSemantics] [RegEncoding (QSemantics.Basis)]
  (left right : Reg) (h : Disjoint left right) (b : QSemantics.Basis) (yR : ℕ) :
  RegEncoding.toNat left (RegEncoding.writeNat right yR b)
    = RegEncoding.toNat left b := by
  simpa using
    (RegEncoding.toNat_left_write_right
      (left := left) (right := right) (Basis:=QSemantics.Basis) (b := b) (yR := yR) h)

/-! =========================================================
    Section 10: Norm, isometry, and overlap inequalities
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
