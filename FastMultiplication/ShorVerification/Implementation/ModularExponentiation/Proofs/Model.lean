import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Config
import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Shor

universe u

namespace Shor

/-! =========================================================
    Algorithm 1 precision and arithmetic constants

This section packages the concrete precision schedule for Algorithm 1 and the
Step-5 inverse constant used by the cleanup phase.
========================================================= -/

section Algorithm1PrecisionAndConstants

/--
The Step-5 constant represents `1 - c⁻¹ mod N`.

The concrete `step5Constant` above chooses such an inverse with `Nat.find`
when coprimality guarantees one exists.
-/
def Step5ConstantOK (c N k5val : ℕ) : Prop :=
  ∃ cinv : ℕ,
    cinv < N ∧
    (c * cinv) % N = 1 % N ∧
    k5val % N = (1 + N - cinv) % N

end Algorithm1PrecisionAndConstants

section SharedConfigurations

namespace ModExpConfig

end ModExpConfig

namespace ModMulConfig

/-! =========================================================
    Algorithm 1 staged gates

These names expose the five-step core as stage-level gates used throughout the
Step 1/2/3/4/5 correctness and error-bound files.
========================================================= -/

/-- Stage name for the exact Step 3/4 comparator block. -/
noncomputable def U34
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  step3 cfg.env.N (cfg.env.data.grow 1) cfg.env.scratch cfg.flag ;;
  step4 cfg.env.N (cfg.env.data.grow 1) cfg.env.work
    cfg.env.scratch cfg.flag cfg.step4_workspace

/-- Stage name for Algorithm 1 Step 1. -/
noncomputable def U1
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  step1 cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace

/-- Stage name for Algorithm 1 Step 2. -/
noncomputable def U2
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  step2 cfg.env.N cfg.env.data cfg.env.work cfg.env.circuit_workspace

/-- Stage name for Algorithm 1 Step 5 cleanup. -/
noncomputable def U5
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  step5
    (step5Constant cfg.c cfg.env.N)
    cfg.env.N cfg.ctrl
    cfg.env.data cfg.env.work
    cfg.env.circuit_workspace

/-- The staged form of the full five-step modular-multiplication core. -/
noncomputable def stagedGate
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  U1 (Basis := Basis) cfg ;;
  U2 (Basis := Basis) cfg ;;
  U34 (Basis := Basis) cfg ;;
  U5 (Basis := Basis) cfg

end ModMulConfig

end SharedConfigurations

/-! =========================================================
    Algorithm 1 reference arithmetic

These scalar definitions describe the intended residues, fractional work labels,
good QPE labels, and exact Step-2 integer shift used by the error proof.
========================================================= -/

section Algorithm1ReferenceArithmetic

/-- Target residue loaded by the Step-1 fractional phase, before final multiplication cleanup. -/
noncomputable def alg1TargetResidue
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℕ :=
  if RegEncoding.bit cfg.ctrl b then
    (((cfg.c + cfg.env.N - 1) % cfg.env.N)
      * RegEncoding.toNat cfg.env.data.active b) % cfg.env.N
  else
    0

/-- Target residue as a normalized real fraction of the modulus. -/
noncomputable def alg1TargetFraction
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℝ :=
  (alg1TargetResidue cfg b : ℝ) / (cfg.env.N : ℝ)

/-- Work-register label as a normalized real fraction. -/
noncomputable def alg1WorkFraction
    {η : ℝ}
    (cfg : ModMulConfig η)
    (t : Fin (ASize cfg.env.work.active)) : ℝ :=
  (t.1 : ℝ) / (ASize cfg.env.work.active : ℝ)

/-- QPE labels whose work fractions are close enough to the target fraction. -/
noncomputable def alg1GoodLabels
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) :
    Finset (Fin (ASize cfg.env.work.active)) :=
  Finset.univ.filter fun t =>
    |alg1TargetFraction cfg b - alg1WorkFraction cfg t|
      < η / (ASize cfg.env.data.active : ℝ)

/-- Exact data-carry value that Step 2 should produce for a retained good label. -/
noncomputable def alg1Step2Value
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℕ :=
  RegEncoding.toNat cfg.env.data.active b + alg1TargetResidue cfg b

end Algorithm1ReferenceArithmetic

/-! =========================================================
    Step-2 Fourier coefficient scaffolding

The Step-2 proof compares the actual Fourier coefficient produced by the
PhaseProduct with the ideal coefficient for the exact integer shift. These
definitions name the relevant phases, index types, labels, and multipliers.
========================================================= -/

section Step2FourierScaffolding

/--
The Step-2 phase angle, written independently of the `let`s in `step2`.
-/
def alg1Step2Phase
    {η : ℝ}
    (cfg : ModMulConfig η) : Angle :=
  (2 * (cfg.env.N : ℚ)) /
    (2 : ℚ) ^
      (regSize cfg.env.work.active + regSize (cfg.env.data.grow 1).active)

/--
The normalizing scalar in the QFT on `data.grow 1`.
-/
noncomputable def alg1Step2QFTScale
    {η : ℝ}
    (cfg : ModMulConfig η) : ℂ :=
  (1 / Real.sqrt ((ASize (cfg.env.data.grow 1).active : ℕ) : ℝ) : ℂ)

/--
The Fourier coefficient after the first QFT and the actual Step-2
`PhaseProd`, before the final inverse QFT.
-/
noncomputable def alg1Step2ActualFourierCoeff
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work.active))
    (y : Fin (ASize (cfg.env.data.grow 1).active)) : ℂ :=
  alg1Step2QFTScale cfg *
    qftPhase
      (ASize (cfg.env.data.grow 1).active)
      (RegEncoding.toNat cfg.env.data.active b)
      y.1 *
    Complex.exp
      (((Angle.toReal (alg1Step2Phase cfg) : ℝ) : ℂ) * Complex.I *
        ((t.1 : ℂ) * (y.1 : ℂ)))

/--
The Fourier coefficient of the exact desired integer shift
`alg1Step2Value cfg b`.
-/
noncomputable def alg1Step2IdealFourierCoeff
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (y : Fin (ASize (cfg.env.data.grow 1).active)) : ℂ :=
  alg1Step2QFTScale cfg *
    qftPhase
      (ASize (cfg.env.data.grow 1).active)
      (alg1Step2Value cfg b)
      y.1

/--
The real difference between the fractional Step-2 shift produced by work
label `t` and the desired integer residue.

The actual shift is `N * t / ASize work`; the ideal one is the target
residue.
-/
noncomputable def alg1Step2ShiftDiscrepancy
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work.active)) : ℝ :=
  (cfg.env.N : ℝ) * alg1WorkFraction cfg t
    - (alg1TargetResidue cfg b : ℝ)

/-- Source index for Step-2 packets: an input basis branch plus a work label. -/
abbrev Alg1Step2SourceIndex
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η) :=
  Σ _b : qs.Basis, Fin (ASize cfg.env.work.active)

/-- Fourier-expanded Step-2 index: a source index plus a data-carry Fourier label. -/
abbrev Alg1Step2FourierIndex
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η) :=
  Σ _i : Alg1Step2SourceIndex qs cfg,
    Fin (ASize (cfg.env.data.grow 1).active)

/-- Expand every retained source index over all data-carry Fourier labels. -/
noncomputable def alg1Step2FourierIndices
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Alg1Step2SourceIndex qs cfg)) :
    Finset (Alg1Step2FourierIndex qs cfg) := by
  classical
  exact S.sigma fun _ => Finset.univ

/-- Basis label associated with one Step-2 Fourier-expanded index. -/
noncomputable def alg1Step2FourierLabel
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (p : Alg1Step2FourierIndex qs cfg) : qs.Basis :=
  RegEncoding.writeNat
    (cfg.env.data.grow 1).active
    p.2.1
    (RegEncoding.writeNat cfg.env.work.active p.1.2.1 p.1.1)

/-- Base Fourier coefficient before applying the actual-vs-ideal multiplier discrepancy. -/
noncomputable def alg1Step2FourierBaseCoeff
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (α : Alg1Step2SourceIndex qs cfg → ℂ)
    (p : Alg1Step2FourierIndex qs cfg) : ℂ :=
  α p.1 *
    alg1Step2QFTScale cfg *
    qftPhase
      (ASize (cfg.env.data.grow 1).active)
      (RegEncoding.toNat cfg.env.data.active p.1.1)
      p.2.1

/-- Difference between the actual Step-2 phase multiplier and the ideal Fourier multiplier. -/
noncomputable def alg1Step2FourierMultiplier
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (r : ℕ)
    (p : Alg1Step2FourierIndex qs cfg) : ℂ :=
  Complex.exp
    (((Angle.toReal (alg1Step2Phase cfg) : ℝ) : ℂ) * Complex.I *
      ((p.1.2.1 : ℂ) * (p.2.1 : ℂ)))
    -
  qftPhase
    (ASize (cfg.env.data.grow 1).active)
    r
    p.2.1

/--
The one-label Step-2 error vector.
-/
noncomputable def alg1Step2Error
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work.active)) : qs.State :=
  qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
      (qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b))
    -
  qs.ket
    (RegEncoding.writeNat
      (cfg.env.data.grow 1).active
      (alg1Step2Value cfg b)
      (RegEncoding.writeNat cfg.env.work.active t.1 b))

end Step2FourierScaffolding

/-! =========================================================
    Step-3/4 labels and trace packets

This section records the exact data values after the comparator/subtractor
stages and packages the finite trace expansions used by the Appendix-E-style
Algorithm 1 error decomposition.
========================================================= -/

section Step34LabelsAndTracePackets

/-- Final data value expected after exact Steps 3 and 4. -/
def alg1OutputValue
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℕ :=
  if RegEncoding.bit cfg.ctrl b then
    (cfg.c * RegEncoding.toNat cfg.env.data.active b) % cfg.env.N
  else
    RegEncoding.toNat cfg.env.data.active b

/-- Comparator condition used by Step 4 to decide whether the flag should clear. -/
def alg1Step4CrossCondition
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work.active)) : Prop :=
  alg1OutputValue cfg b * ASize cfg.env.work.active < cfg.env.N * t.1

/-- Whether the pre-reduction Step-2 value overflows the modulus. -/
abbrev alg1Overflow
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : Prop :=
  cfg.env.N ≤ alg1Step2Value cfg b

/-- Finite trace data for a valid input superposition through Step 1. -/
structure Alg1Trace
    {η : ℝ}
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (cfg : ModMulConfig η)
    (ψ : qs.State) where
  support : Finset qs.Basis
  inputCoeff : qs.Basis → ℂ
  phaseCoeff : qs.Basis → Fin (ASize cfg.env.work.active) → ℂ
  input_eq :
    ψ = ∑ b ∈ support, inputCoeff b • qs.ket b
  input_good :
    ∀ b ∈ support,
      GoodModMulBasisInput qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b
  scratch_zero : ∀ b ∈ support, RegEncoding.toNat cfg.env.scratch.active b = 0
  scratch_fresh : ∀ b ∈ support, cfg.env.scratch.FreshFor 1 b
  full_step1_eq :
    qs.eval
        (step1 cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
        ψ
      =
    ∑ b ∈ support,
      inputCoeff b •
        ∑ t : Fin (ASize cfg.env.work.active),
          phaseCoeff b t • qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b)
  step34_support :
    ∀ b ∈ support, ∀ t ∈ alg1GoodLabels cfg b,
      phaseCoeff b t ≠ 0 →
        (alg1Step4CrossCondition cfg b t ↔ alg1Overflow cfg b)

/-! =========================================================
    Concrete reference states used in the Appendix-E proof
========================================================= -/

namespace Alg1Trace

/-- The retained good-label packet after Step 1. -/
noncomputable def goodStep1
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ alg1GoodLabels cfg b,
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work.active t.1 b)

/--
The reference state after Step 2.

For every retained good label `t`, replace the approximate Fourier addition
with the exact integer value `alg1Step2Value cfg b`.
-/
noncomputable def afterStep2Ref
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ alg1GoodLabels cfg b,
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1Step2Value cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b))

/--
The reference state after exact Steps 3 and 4.

The data/carry register now contains the desired residue, while the work
register still contains the good phase-estimation label.
-/
noncomputable def afterStep34Ref
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ alg1GoodLabels cfg b,
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b))

end Alg1Trace

end Step34LabelsAndTracePackets

/-! =========================================================
    Step-1 and Step-5 coefficient packets

The Step-5 cleanup proof compares the original Step-1 fractional load with the
forward circuit whose adjoint is Step 5. These definitions name the QPE
bad-label mass, bad-label packets, shared phase scalars, and inverse-QFT
coefficients for that comparison.
========================================================= -/

section Step1Step5CoefficientPackets

/--
Canonical Step-1 phase-estimation coefficient.

This is the actual amplitude of the work-label basis vector in the Step-1
output.
-/
noncomputable def alg1PhaseCoeff
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work.active)) : ℂ :=
  inner ℂ
    (qs.ket (RegEncoding.writeNat cfg.env.work.active t.1 b))
    (qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) (qs.ket b))

/-- The QPE probability mass outside the retained good-label set for one basis input. -/
noncomputable def alg1QpeBadMass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis) : ℝ :=
  ∑ t ∈ Finset.univ.filter
      (fun t => t ∉ alg1GoodLabels cfg b),
    ‖alg1PhaseCoeff qs cfg b t‖ ^ 2

/--
The bad-label mass of a whole finite trace.

This is the squared input amplitude of each basis branch times that branch's
discarded QPE probability.
-/
noncomputable def alg1TraceBadMass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : ℝ :=
  ∑ b ∈ tr.support,
    ‖tr.inputCoeff b‖ ^ 2 *
      ∑ t ∈ Finset.univ.filter
          (fun t => t ∉ alg1GoodLabels cfg b),
        ‖tr.phaseCoeff b t‖ ^ 2

namespace Alg1Trace

/-- The Step-1 packet consisting only of the discarded QPE labels. -/
noncomputable def badStep1
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ Finset.univ.filter
          (fun t => t ∉ alg1GoodLabels cfg b),
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work.active t.1 b)

/--
The formal post-Step-3/4 packet with all QPE labels retained.

This is not the operational output of Steps 3–4 on bad labels. It is the
reference packet used to identify the inverse cleanup with the QPE tail.
-/
noncomputable def afterStep34Full
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t : Fin (ASize cfg.env.work.active),
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b))

/-- The discarded part of `afterStep34Full`. -/
noncomputable def afterStep34Bad
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ Finset.univ.filter
          (fun t => t ∉ alg1GoodLabels cfg b),
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b))

end Alg1Trace

/-- The Step-1 controlled phase angle. -/
def alg1Step1Phase {η : ℝ} (cfg : ModMulConfig η) : Angle :=
  (2 * (((cfg.c + cfg.env.N - 1) % cfg.env.N : ℕ) : ℚ)) / (cfg.env.N : ℚ)

/-- The forward Step-5 controlled phase angle. -/
def alg1Step5Phase {η : ℝ} (cfg : ModMulConfig η) : Angle :=
  (2 * ((step5Constant cfg.c cfg.env.N % cfg.env.N : ℕ) : ℚ)) / (cfg.env.N : ℚ)

/--
The forward circuit whose adjoint is `ModMulConfig.U5`.

Keeping this named avoids repeatedly unfolding `step5`.
-/
noncomputable def alg1Step5Forward
    {η : ℝ}
    {Basis : Type*}
    [RegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  (H_reg cfg.env.work.active) ;;
  (Gate.CPhaseProdUsing
    cfg.ctrl
    (alg1Step5Phase cfg)
    (cfg.env.data.grow 1).active
    cfg.env.work.active cfg.env.circuit_workspace.step5Workspace) ;;
  (IQFT cfg.env.work)

/--
The diagonal phase acquired by work label `z` during the original Step-1
fractional load.
-/
noncomputable def alg1Step1PhaseScalar
    {Basis : Type*}
    [RegEncoding Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : Basis)
    (z : Fin (ASize cfg.env.work.active)) : ℂ :=
  if RegEncoding.bit cfg.ctrl b then
    Complex.exp
      (((Angle.toReal (alg1Step1Phase cfg) : ℝ) : ℂ) * Complex.I *
        ((RegEncoding.toNat cfg.env.data.active b : ℂ) * (z.1 : ℂ)))
  else
    1

/--
The common target-residue form of a phase scalar.

Both Step 1 and the forward Step-5 fractional load reduce to this scalar.
-/
noncomputable def alg1TargetPhaseScalar
    [QSemantics]
    [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (z : Fin (ASize cfg.env.work.active)) : ℂ :=
  if RegEncoding.bit cfg.ctrl b then
    Complex.exp
      (((2 * Real.pi) / (cfg.env.N : ℝ)) * Complex.I *
        ((alg1TargetResidue cfg b : ℂ) * (z.1 : ℂ)))
  else
    1

/--
The uniform-H coefficient multiplied by the Step-1 diagonal phase.
-/
noncomputable def alg1LoadPreCoeff
    {Basis : Type*}
    [RegEncoding Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : Basis)
    (z : Fin (ASize cfg.env.work.active)) : ℂ :=
  (1 / Real.sqrt ((ASize cfg.env.work.active : ℕ) : ℝ) : ℂ) *
    alg1Step1PhaseScalar cfg b z

/-- The adjoint-QFT matrix entry from source work label `z` to target `t`. -/
noncomputable def alg1IQFTCoeff
    (work : Reg)
    (z t : Fin (ASize work)) : ℂ :=
  (1 / Real.sqrt ((ASize work : ℕ) : ℝ) : ℂ) *
    star (qftPhase (ASize work) z.1 t.1)

/--
The explicit final QPE / fractional-load coefficient.

This is the coefficient after H, diagonal phase, and inverse QFT.
-/
noncomputable def alg1FractionalLoadCoeff
    {Basis : Type*}
    [RegEncoding Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : Basis)
    (t : Fin (ASize cfg.env.work.active)) : ℂ :=
  ∑ z : Fin (ASize cfg.env.work.active),
    alg1LoadPreCoeff cfg b z *
      alg1IQFTCoeff cfg.env.work.active z t

end Step1Step5CoefficientPackets

end Shor
