import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.Semantics.GateSemanticsLemmas

/-!
# Phase-Product Macro Semantics

The `PhaseProdUsing` / `CPhaseProdUsing` semantic bridge theorems: on a clean
workspace, the unsigned/controlled phase-product macros contribute exactly the
expected phase and restore the basis state.
-/

namespace Shor
namespace GateSemanticsFacts

open Gate
/--
Semantic bridge for the unsigned macro: on clean workspace, `PhaseProdUsing` contributes
exactly the expected phase `exp(i * phi * x * z)` and restores the basis state.
-/
theorem eval_PhaseProdUsing_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (phi : Angle)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (b : qs.Basis)
    (hclean : ws.Clean b) :
    qs.eval
        (Gate.PhaseProdUsing phi x z ws)
        (qs.ket b)
      =
    Complex.exp
        (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
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
    (phi : Angle)
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
          (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
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

end Shor
