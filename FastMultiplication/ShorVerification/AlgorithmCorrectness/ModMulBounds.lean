import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModExpBounds

open Shor
/-- `q` is not a qubit of register `r`. -/
def QubitOutside (q : ℕ) (r : Reg) : Prop :=
  q < r.lo ∨ r.hi ≤ q

/--
Layout assumptions for one invocation of `CmodMulInPlaceCore`.

`extendHi data` is used because Algorithm 1 temporarily uses the qubit
immediately above `data` as its carry/high bit.
-/
def ModMulCoreLayout
    (data work : Reg) (flag ctrl : ℕ) : Prop :=
  Disjoint (extendHi data) work ∧
  QubitOutside flag (extendHi data) ∧
  QubitOutside flag work ∧
  QubitOutside ctrl (extendHi data) ∧
  QubitOutside ctrl work ∧
  ctrl ≠ flag

/--
A computational-basis input on which Algorithm 1 is allowed to be called.

The data register contains a canonical residue; the carry bit added by
`extendHi`, the fractional/work register, and the comparator flag are clean.
All other qubits, including the control and exponent registers, are arbitrary.
-/
def GoodModMulBasisInput
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data work : Reg) (flag : ℕ)
    (b : qs.Basis) : Prop :=
  RegEncoding.toNat data b < N ∧
  RegEncoding.toNat (qubitReg data.hi) b = 0 ∧
  RegEncoding.toNat work b = 0 ∧
  RegEncoding.toNat (qubitReg flag) b = 0

/--
The full valid-input subspace.

This is the span of *all* computational-basis states satisfying
`GoodModMulBasisInput`; hence it includes arbitrary superpositions over
the control register, exponent register, and valid modular data values.
-/
def ValidModMulState
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data work : Reg) (flag : ℕ) :
    Submodule ℂ qs.State :=
  Submodule.span ℂ
    ({ ψ : qs.State |
        ∃ b : qs.Basis,
          GoodModMulBasisInput qs N data work flag b ∧
          ψ = qs.ket b } : Set qs.State)

/--
Concrete basis semantics required of the ideal controlled modular multiplier.

This is stronger than merely saying that its output is valid: it records the
exact controlled modular multiplication rule on `data`.
-/
class IdealCtrlModMulSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec] : Prop where

  eval_idealCtrlModMul_good_ket :
    ∀ (c N : ℕ) (data work : Reg) (flag ctrl : ℕ) (b : qs.Basis),
      1 < N →
      N ≤ ASize data →
      Nat.Coprime c N →
      ModMulCoreLayout data work flag ctrl →
      GoodModMulBasisInput qs N data work flag b →
      ∃ b' : qs.Basis,
        qs.eval (Spec.idealCtrlModMul c N data ctrl) (qs.ket b)
          = qs.ket b' ∧
        GoodModMulBasisInput qs N data work flag b' ∧
        RegEncoding.bit ctrl b' = RegEncoding.bit ctrl b ∧
        RegEncoding.toNat data b'
          =
          if RegEncoding.bit ctrl b then
            (c * RegEncoding.toNat data b) % N
          else
            RegEncoding.toNat data b

class IdealCtrlModMulExactSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec] : Prop extends IdealCtrlModMulSemantics qs where

  eval_idealCtrlModMul_good_ket_exact :
    ∀ (c N : ℕ) (data work : Reg) (flag ctrl : ℕ) (b : qs.Basis),
      1 < N →
      N ≤ ASize data →
      Nat.Coprime c N →
      ModMulCoreLayout data work flag ctrl →
      GoodModMulBasisInput qs N data work flag b →
      qs.eval (Spec.idealCtrlModMul c N data ctrl) (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat data
          (if RegEncoding.bit ctrl b then
            (c * RegEncoding.toNat data b) % N
          else
            RegEncoding.toNat data b)
          b)



/--
(ii) The ideal controlled multiplier maps the entire valid subspace back into
the same valid subspace.

-/
theorem idealCtrlModMul_preserves_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    (c N : ℕ) (data work : Reg) (flag ctrl : ℕ)
    (hN : 1 < N)
    (hsize : N ≤ ASize data)
    (hcoprime : Nat.Coprime c N)
    (hlayout : ModMulCoreLayout data work flag ctrl)
    (ψ : qs.State)
    (hvalid : ψ ∈ ValidModMulState qs N data work flag) :
    qs.eval (Spec.idealCtrlModMul c N data ctrl) ψ
      ∈ ValidModMulState qs N data work flag := by
  sorry

/-! =========================================================
    Concrete Algorithm-1 side conditions
========================================================= -/

/--
A sufficient precision condition for the work register.

If `n = regSize data` and `m = regSize work`, this says

  2^(m - n) ≥ (2 + 1 / (2η))^2,

which is implied by the paper's choice
`m = n + ceil (2 * log₂ (2 + 1 / (2η)))`.
-/
def Algorithm1Precision
    (η : ℝ) (data work : Reg) : Prop :=
  0 < η ∧
  η < (1 / 2 : ℝ) ∧
  (2 : ℝ) ^ (regSize work - regSize data)
    ≥ (2 + 1 / (2 * η)) ^ 2

/--
The Step-5 constant represents `1 - c⁻¹ mod N`.

We do not commit to a particular implementation of modular inversion.
Instead, we require a witness `cinv` satisfying `c * cinv = 1 mod N`.
-/
def Step5ConstantOK (c N k5val : ℕ) : Prop :=
  ∃ cinv : ℕ,
    cinv < N ∧
    (c * cinv) % N = 1 % N ∧
    k5val % N = (1 + N - cinv) % N

/--
All controls used by the tail beginning at `q` are distinct from the
data/work/flag locations and lie in the exponent register interval.
-/
def ModExpTailLayout
    (x data work : Reg) (flag q n : ℕ) : Prop :=
  x.lo ≤ q ∧
  q + n ≤ x.hi ∧
  ∀ j : ℕ, j < n →
    ModMulCoreLayout data work flag (q + j)

/--
For every controlled multiplication in a tail, the multiplier is invertible
modulo `N` and the selected Step-5 constant is correct.
-/
def ModExpTailArithmeticOK
    (a N : ℕ) (x : Reg)
    (k5 : ℕ → ℕ → ℕ)
    (q n : ℕ) : Prop :=
  ∀ j : ℕ, j < n →
    let e : ℕ := (q + j) - x.lo
    let c : ℕ := (a ^ (2 ^ e)) % N
    Nat.Coprime c N ∧
    Step5ConstantOK c N (k5 c N)


/--
The layout condition for the complete modular-exponentiation circuit.
-/
def ModExpLayout
    (x data work : Reg) (flag : ℕ) : Prop :=
  ModExpTailLayout x data work flag x.lo (tbits x)

/--
The arithmetic side condition for the complete modular-exponentiation circuit.
-/
def ModExpArithmeticOK
    (a N : ℕ) (x : Reg)
    (k5 : ℕ → ℕ → ℕ) : Prop :=
  ModExpTailArithmeticOK a N x k5 x.lo (tbits x)

noncomputable def modExpApproxStepsValid
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (k5 : ℕ → ℕ → ℕ)
    (a N : ℕ) (x data work : Reg) (flag : ℕ) :
    ℕ → ℕ → Gate
  | _q, 0 =>
      Gate.id
  | q, n + 1 =>
      let e : ℕ := q - x.lo
      let c : ℕ := (a ^ (2 ^ e)) % N
      CmodMulInPlaceCore
        (Basis := Basis)
        c N (k5 c N) q data work flag
      ;;
      modExpApproxStepsValid
        (Basis := Basis)
        k5 a N x data work flag (q + 1) n

noncomputable def modExpApproxValid
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (k5 : ℕ → ℕ → ℕ)
    (a N : ℕ) (x data work : Reg) (flag : ℕ) : Gate :=
  modExpApproxStepsValid
    (Basis := Basis)
    k5 a N x data work flag x.lo (tbits x)


/-! =========================================================
    Shared Algorithm-1 environment
========================================================= -/

structure Algorithm1Env (η : ℝ) where
  N : ℕ
  data : Reg
  work : Reg
  modulus_gt_one : 1 < N
  data_capacity  : N ≤ ASize data
  precision      : Algorithm1Precision η data work

/-! =========================================================
    One controlled modular multiplication
========================================================= -/

structure ModMulConfig (η : ℝ) (k5 : ℕ → ℕ → ℕ) where
  env : Algorithm1Env η
  c : ℕ
  flag : ℕ
  ctrl : ℕ
  coprime  : Nat.Coprime c env.N
  step5_ok : Step5ConstantOK c env.N (k5 c env.N)
  layout   : ModMulCoreLayout env.data env.work flag ctrl

namespace ModMulConfig

noncomputable def approxGate
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (cfg : ModMulConfig η k5) : Gate :=
  CmodMulInPlaceCore
    (Basis := Basis)
    cfg.c cfg.env.N (k5 cfg.c cfg.env.N)
    cfg.ctrl cfg.env.data cfg.env.work cfg.flag

def idealGate
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    [Spec]
    (cfg : ModMulConfig η k5) : Gate :=
  Spec.idealCtrlModMul cfg.c cfg.env.N cfg.env.data cfg.ctrl

def ValidState
    (qs : QSemantics) [RegEncoding qs.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5) (ψ : qs.State) : Prop :=
  ψ ∈ ValidModMulState qs cfg.env.N cfg.env.data cfg.env.work cfg.flag

def ValidUnitState
    (qs : QSemantics) [RegEncoding qs.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5) (ψ : qs.State) : Prop :=
  cfg.ValidState qs ψ ∧ ‖ψ‖ = 1

end ModMulConfig

theorem IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_cfg
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5) (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval (ModMulConfig.idealGate cfg) (qs.ket b)
      =
    qs.ket
      (RegEncoding.writeNat cfg.env.data
        (if RegEncoding.bit cfg.ctrl b then
          (cfg.c * RegEncoding.toNat cfg.env.data b) % cfg.env.N
        else
          RegEncoding.toNat cfg.env.data b)
        b) := by
  simpa [ModMulConfig.idealGate] using
    (IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket_exact
      (qs := qs)
      cfg.c
      cfg.env.N
      cfg.env.data
      cfg.env.work
      cfg.flag
      cfg.ctrl
      b
      cfg.env.modulus_gt_one
      cfg.env.data_capacity
      cfg.coprime
      cfg.layout
      hb)


noncomputable def alg1TargetResidue
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis) : ℕ :=
  if RegEncoding.bit cfg.ctrl b then
    (((cfg.c + cfg.env.N - 1) % cfg.env.N)
      * RegEncoding.toNat cfg.env.data b) % cfg.env.N
  else
    0

noncomputable def alg1TargetFraction
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis) : ℝ :=
  (alg1TargetResidue cfg b : ℝ) / (cfg.env.N : ℝ)

noncomputable def alg1WorkFraction
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (t : Fin (ASize cfg.env.work)) : ℝ :=
  (t.1 : ℝ) / (ASize cfg.env.work : ℝ)

noncomputable def alg1GoodLabels
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis) :
    Finset (Fin (ASize cfg.env.work)) :=
  Finset.univ.filter fun t =>
    |alg1TargetFraction cfg b - alg1WorkFraction cfg t|
      < η / (ASize cfg.env.data : ℝ)

noncomputable def alg1Step2Value
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis) : ℕ :=
  RegEncoding.toNat cfg.env.data b + alg1TargetResidue cfg b

def alg1OutputValue
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis) : ℕ :=
  if RegEncoding.bit cfg.ctrl b then
    (cfg.c * RegEncoding.toNat cfg.env.data b) % cfg.env.N
  else
    RegEncoding.toNat cfg.env.data b

def alg1Step4CrossCondition
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work)) : Prop :=
  alg1OutputValue cfg b * ASize cfg.env.work < cfg.env.N * t.1

abbrev alg1Overflow
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis) : Prop :=
  cfg.env.N ≤ alg1Step2Value cfg b

noncomputable def alg1OverflowBit
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis) : Bool := by
  classical
  exact decide (alg1Overflow cfg b)

structure Alg1Trace
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    (cfg : ModMulConfig η k5)
    (ψ : qs.State) where

  support : Finset qs.Basis

  inputCoeff :
    qs.Basis → ℂ

  phaseCoeff :
    qs.Basis →
      Fin (ASize cfg.env.work) →
        ℂ

  input_eq :
    ψ =
      ∑ b ∈ support,
        inputCoeff b • qs.ket b

  input_good :
    ∀ b ∈ support,
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b

  full_step1_eq :
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        ψ
      =
    ∑ b ∈ support,
      inputCoeff b •
        ∑ t : Fin (ASize cfg.env.work),
          phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat
                cfg.env.work t.1 b)

  step34_support :
    ∀ b ∈ support,
      ∀ t ∈ alg1GoodLabels cfg b,
        phaseCoeff b t ≠ 0 →
          (alg1Step4CrossCondition cfg b t ↔
            alg1Overflow cfg b)

lemma alg1TargetResidue_lt_N
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis) :
    alg1TargetResidue cfg b < cfg.env.N := by
  have hNpos : 0 < cfg.env.N :=
    Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one
  unfold alg1TargetResidue
  split
  · exact Nat.mod_lt _ hNpos
  · exact hNpos

lemma alg1Step2Value_lt_extendHi_capacity
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis)
    (hb :
      GoodModMulBasisInput
        (inferInstance : QSemantics)
        cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    alg1Step2Value cfg b < ASize (extendHi cfg.env.data) := by
  have hdata_lt_N :
      RegEncoding.toNat cfg.env.data b < cfg.env.N := hb.1
  have htarget_lt_N :
      alg1TargetResidue cfg b < cfg.env.N :=
    alg1TargetResidue_lt_N cfg b
  have hsum_lt :
      alg1Step2Value cfg b < 2 * cfg.env.N := by
    unfold alg1Step2Value
    omega
  have hcap :
      2 * cfg.env.N ≤ ASize (extendHi cfg.env.data) := by
    have hNcap : cfg.env.N ≤ ASize cfg.env.data :=
      cfg.env.data_capacity
    have hpow :
        ASize (extendHi cfg.env.data) = 2 * ASize cfg.env.data := by
      simp [ASize, regSize, extendHi, Nat.pow_succ, Nat.mul_comm]
    omega
  exact lt_of_lt_of_le hsum_lt hcap

lemma alg1OutputValue_lt_data_capacity
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis)
    (hb :
      GoodModMulBasisInput
        (inferInstance : QSemantics)
        cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    alg1OutputValue cfg b < ASize cfg.env.data := by
  have hNpos : 0 < cfg.env.N :=
    Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one
  unfold alg1OutputValue
  split
  · exact lt_of_lt_of_le (Nat.mod_lt _ hNpos) cfg.env.data_capacity
  · exact lt_of_lt_of_le hb.1 cfg.env.data_capacity




/-! =========================================================
    Concrete reference states used in the Appendix-E proof
========================================================= -/

namespace Alg1Trace

noncomputable def goodStep1
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {cfg : ModMulConfig η k5}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ alg1GoodLabels cfg b,
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b)

/--
The reference state after Step 2.

For every retained good label `t`, replace the approximate Fourier addition
with the exact integer value `alg1Step2Value cfg b`.
-/
noncomputable def afterStep2Ref
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {cfg : ModMulConfig η k5}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ alg1GoodLabels cfg b,
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1Step2Value cfg b)
              (RegEncoding.writeNat cfg.env.work t.1 b))

/--
The reference state after exact Steps 3 and 4.

The data/carry register now contains the desired residue, while the work
register still contains the good phase-estimation label.
-/
noncomputable def afterStep34Ref
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {cfg : ModMulConfig η k5}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ alg1GoodLabels cfg b,
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work t.1 b))


end Alg1Trace

theorem modExp_multiplier_coprime
    (a N e : ℕ)
    (hcoprime : Nat.Coprime a N) :
    Nat.Coprime ((a ^ (2 ^ e)) % N) N := by
  sorry

/-! =========================================================
    Algorithm-1 stages
========================================================= -/

namespace ModMulConfig

noncomputable def U1
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    (cfg : ModMulConfig η k5) : Gate :=
  step1
    (Basis := Basis)
    cfg.c
    cfg.env.N
    cfg.ctrl
    cfg.env.data
    cfg.env.work

noncomputable def U2
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    (cfg : ModMulConfig η k5) : Gate :=
  (step2
    (Basis := Basis)
    cfg.env.N
    cfg.env.data
    cfg.env.work).2

noncomputable def U34
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    (cfg : ModMulConfig η k5) : Gate :=
  step3 cfg.env.N (extendHi cfg.env.data) cfg.flag ;;
  step4 cfg.env.N (extendHi cfg.env.data) cfg.env.work cfg.flag

noncomputable def U5
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    (cfg : ModMulConfig η k5) : Gate :=
  step5
    (Basis := Basis)
    (k5 cfg.c cfg.env.N)
    cfg.env.N
    cfg.ctrl
    (extendHi cfg.env.data)
    cfg.env.work

noncomputable def stagedGate
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    (cfg : ModMulConfig η k5) : Gate :=
  U1 (Basis := Basis) cfg ;;
  U2 (Basis := Basis) cfg ;;
  U34 (Basis := Basis) cfg ;;
  U5 (Basis := Basis) cfg

lemma eval_approxGate_eq_staged
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (ψ : qs.State) :
    qs.eval (ModMulConfig.approxGate (Basis := qs.Basis) cfg) ψ
      =
    qs.eval (ModMulConfig.stagedGate (Basis := qs.Basis) cfg) ψ := by
  simp [ModMulConfig.approxGate,CmodMulInPlaceCore,
    ModMulConfig.stagedGate, ModMulConfig.U1,ModMulConfig.U2,
    ModMulConfig.U34,ModMulConfig.U5,qs.eval_seq,step2]

end ModMulConfig

/--
Narrow semantics for the raw primitive gates used by Algorithm 1 Steps 3
and 4. These facts are intentionally separate from `GateSemanticsFacts`,
which only describes the structured gate families.
-/
class ModMulPrimitiveSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis] : Prop where

  /-- Step 3, restricted to the clean-flag regime used by Algorithm 1. -/
  eval_step3_clean_ket :
    ∀ (N : ℕ) (x_ext : Reg) (flag : ℕ) (b : qs.Basis),
      QubitOutside flag x_ext →
      RegEncoding.toNat (qubitReg flag) b = 0 →
      RegEncoding.toNat x_ext b < 2 * N →
      qs.eval (step3 N x_ext flag) (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat
          (qubitReg flag)
          (if N ≤ RegEncoding.toNat x_ext b then 1 else 0)
          (RegEncoding.writeNat
            x_ext
            (if N ≤ RegEncoding.toNat x_ext b then
              RegEncoding.toNat x_ext b - N
            else
              RegEncoding.toNat x_ext b)
            b))

  /--
  Step 4 clears a flag exactly when that flag already contains the
  comparison result. This is the reversible/XOR form needed here.
  -/
  eval_step4_cancels_ket :
    ∀ (N : ℕ) (x_ext w_reg : Reg) (flag : ℕ) (b : qs.Basis),
      QubitOutside flag x_ext →
      QubitOutside flag w_reg →
      RegEncoding.toNat (qubitReg flag) b
        =
      (if RegEncoding.toNat x_ext b * ASize w_reg
            < N * RegEncoding.toNat w_reg b then
          1
        else
          0) →
      qs.eval (step4 N x_ext w_reg flag) (qs.ket b)
        =
      qs.ket (RegEncoding.writeNat (qubitReg flag) 0 b)

/-! =========================================================
    Appendix-E proof lemmas
========================================================= -/

lemma eval_finset_sum
    (qs : QSemantics)
    (U : Gate)
    {ι : Type*}
    (s : Finset ι)
    (f : ι → qs.State) :
    qs.eval U (∑ i ∈ s, f i)
      =
    ∑ i ∈ s, qs.eval U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using qs.eval_zero U
  | insert a s ha ih =>
      simp [Finset.sum_insert, ha, qs.eval_add, ih]


lemma eval_iqft_work_expansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [QFTSemantics qs]
    (work : Reg)
    (b : qs.Basis) :
    ∃ α : Fin (ASize work) → ℂ,
      qs.eval (IQFT work) (qs.ket b)
        =
      ∑ t : Fin (ASize work),
        α t • qs.ket (RegEncoding.writeNat work t.1 b) := by
  refine ⟨
    fun t =>
      ((1 / Real.sqrt ((ASize work : ℕ) : ℝ) : ℂ) *
        star (qftPhase (ASize work) (RegEncoding.toNat work b) t.1)),
    ?_
  ⟩
  rw [IQFT]
  rw [QFTSemantics.eval_adj_QFT_ket]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [smul_smul]

lemma eval_CPhaseProd_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (data work : Reg)
    (b : qs.Basis)
    (hdisj : Disjoint data work) :
    qs.eval (Gate.CPhaseProd ctrl phi data work) (qs.ket b)
      =
    (if RegEncoding.bit ctrl b then
        Complex.exp
          (phi * Complex.I *
            ((RegEncoding.toNat data b : ℂ) *
             (RegEncoding.toNat work b : ℂ)))
      else
        1) •
      qs.ket b := by
  sorry

lemma eval_cphaseprod_work_diagonal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (ctrl : ℕ)
    (φ : ℝ)
    (data work : Reg)
    (b : qs.Basis)
    (z : Fin (ASize work))
    (hdisj : Disjoint data work) :
    ∃ L : ℂ,
      qs.eval (Gate.CPhaseProd ctrl φ data work)
          (qs.ket (RegEncoding.writeNat work z.1 b))
        =
      L • qs.ket (RegEncoding.writeNat work z.1 b) := by
  let b' := RegEncoding.writeNat work z.1 b

  refine ⟨
    if RegEncoding.bit ctrl b' then
      Complex.exp
        (φ * Complex.I *
          ((RegEncoding.toNat data b' : ℂ) *
           (RegEncoding.toNat work b' : ℂ)))
    else
      1,
    ?_
  ⟩

  simpa [b'] using
    eval_CPhaseProd_ket qs ctrl φ data work b' hdisj

open QSemantics

/-- States supported entirely on `work`, relative to an unchanged base state. -/
private def HRegWorkSpan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (ψ : qs.State) : Prop :=
  ∃ α : Fin (ASize work) → ℂ,
    ψ =
      ∑ t : Fin (ASize work),
        α t •
          qs.ket (RegEncoding.writeNat work t.1 base)


private lemma hregWorkSpan_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis) :
    HRegWorkSpan qs work base (0 : qs.State) := by
  refine ⟨fun _ => 0, ?_⟩
  simp


private lemma hregWorkSpan_add
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (ψ φ : qs.State) :
    HRegWorkSpan qs work base ψ →
    HRegWorkSpan qs work base φ →
    HRegWorkSpan qs work base (ψ + φ) := by
  rintro ⟨α, hα⟩ ⟨β, hβ⟩
  refine ⟨fun t => α t + β t, ?_⟩

  rw [hα, hβ, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  simp [add_smul]


private lemma hregWorkSpan_smul
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (a : ℂ)
    (ψ : qs.State) :
    HRegWorkSpan qs work base ψ →
    HRegWorkSpan qs work base (a • ψ) := by
  rintro ⟨α, hα⟩
  refine ⟨fun t => a * α t, ?_⟩

  rw [hα, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [smul_smul]


private lemma hregWorkSpan_sum
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    {ι : Type*}
    (s : Finset ι)
    (f : ι → qs.State)
    (hf : ∀ i ∈ s, HRegWorkSpan qs work base (f i)) :
    HRegWorkSpan qs work base (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hregWorkSpan_zero qs work base

  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply hregWorkSpan_add qs work base
      · exact hf a (by simp)
      · apply ih
        intro i hi
        exact hf i (by simp [hi])


private lemma hregWorkSpan_ket_write
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (z : Fin (ASize work)) :
    HRegWorkSpan qs work base
      (qs.ket (RegEncoding.writeNat work z.1 base)) := by
  classical
  refine ⟨fun t => if t = z then 1 else 0, ?_⟩
  simp


/--
Writing qubit `q` inside `work` can be represented as one whole-register
write to `work`, relative to the original `base`.
-/
private lemma qubit_write_eq_work_write
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (q : ℕ)
    (hqlo : work.lo ≤ q)
    (hqhi : q < work.hi)
    (z : Fin (ASize work))
    (v : ℕ) :
    ∃ t : Fin (ASize work),
      RegEncoding.writeNat
          (qubitReg q)
          v
          (RegEncoding.writeNat work z.1 base)
        =
      RegEncoding.writeNat work t.1 base := by
  classical

  let bout : qs.Basis :=
    RegEncoding.writeNat
      (qubitReg q)
      v
      (RegEncoding.writeNat work z.1 base)

  let t : Fin (ASize work) :=
    ⟨RegEncoding.toNat work bout,
      RegEncoding.toNat_lt_ASize work bout⟩

  refine ⟨t, ?_⟩
  change bout = RegEncoding.writeNat work t.1 base

  apply RegEncoding.basis_ext
  intro p

  by_cases hp : work.lo ≤ p ∧ p < work.hi

  ·
    have hrewrite :
        RegEncoding.writeNat work t.1 bout = bout := by
      simpa [t] using
        (RegEncoding.writeNat_toNat work bout)

    have hin :
        RegEncoding.bit p
            (RegEncoding.writeNat work t.1 base)
          =
        RegEncoding.bit p
            (RegEncoding.writeNat work t.1 bout) :=
      RegEncoding.bit_writeNat_in
        (r := work)
        (v := t.1)
        (b1 := base)
        (b2 := bout)
        (q := p)
        hp.1
        hp.2

    calc
      RegEncoding.bit p bout
          =
        RegEncoding.bit p
          (RegEncoding.writeNat work t.1 bout) := by
            rw [hrewrite]
      _ =
        RegEncoding.bit p
          (RegEncoding.writeNat work t.1 base) := by
            symm
            exact hin

  ·
    have hpout : p < work.lo ∨ work.hi ≤ p := by
      by_cases hplow : p < work.lo
      · exact Or.inl hplow
      · right
        omega

    have hqout :
        p < (qubitReg q).lo ∨ (qubitReg q).hi ≤ p := by
      unfold qubitReg Reg.hi
      rcases hpout with hpout | hpout
      · left
        simp_all
        omega
      · right
        simp_all
        omega

    have hout_qubit :
        RegEncoding.bit p bout
          =
        RegEncoding.bit p
          (RegEncoding.writeNat work z.1 base) := by
      simpa [bout] using
        (RegEncoding.bit_writeNat_out
          (r := qubitReg q)
          (v := v)
          (b := RegEncoding.writeNat work z.1 base)
          (q := p)
          hqout)

    have hout_work_z :
        RegEncoding.bit p
            (RegEncoding.writeNat work z.1 base)
          =
        RegEncoding.bit p base :=
      RegEncoding.bit_writeNat_out
        (r := work)
        (v := z.1)
        (b := base)
        (q := p)
        hpout

    have hout_work_t :
        RegEncoding.bit p
            (RegEncoding.writeNat work t.1 base)
          =
        RegEncoding.bit p base :=
      RegEncoding.bit_writeNat_out
        (r := work)
        (v := t.1)
        (b := base)
        (q := p)
        hpout

    calc
      RegEncoding.bit p bout
          =
        RegEncoding.bit p
          (RegEncoding.writeNat work z.1 base) :=
            hout_qubit
      _ =
        RegEncoding.bit p base :=
            hout_work_z
      _ =
        RegEncoding.bit p
          (RegEncoding.writeNat work t.1 base) := by
            symm
            exact hout_work_t


private lemma hregWorkSpan_qubit_write
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (q : ℕ)
    (hqlo : work.lo ≤ q)
    (hqhi : q < work.hi)
    (z : Fin (ASize work))
    (v : ℕ) :
    HRegWorkSpan qs work base
      (qs.ket
        (RegEncoding.writeNat
          (qubitReg q)
          v
          (RegEncoding.writeNat work z.1 base))) := by
  rcases
      qubit_write_eq_work_write
        qs work base q hqlo hqhi z v with
    ⟨t, ht⟩

  rw [ht]
  exact hregWorkSpan_ket_write qs work base t


private lemma eval_H_preserves_hregWorkSpan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [HadamardSemantics qs]
    (work : Reg)
    (base : qs.Basis)
    (q : ℕ)
    (hqlo : work.lo ≤ q)
    (hqhi : q < work.hi)
    (ψ : qs.State) :
    HRegWorkSpan qs work base ψ →
    HRegWorkSpan qs work base (qs.eval (Gate.H q) ψ) := by
  intro hψ
  rcases hψ with ⟨α, hα⟩

  have heval :
      qs.eval (Gate.H q) ψ
        =
      ∑ t : Fin (ASize work),
        α t •
          qs.eval
            (Gate.H q)
            (qs.ket (RegEncoding.writeNat work t.1 base)) := by
    calc
      qs.eval (Gate.H q) ψ
          =
        qs.eval (Gate.H q)
          (∑ t : Fin (ASize work),
            α t •
              qs.ket (RegEncoding.writeNat work t.1 base)) := by
            rw [hα]

      _ =
        ∑ t : Fin (ASize work),
          qs.eval
            (Gate.H q)
            (α t •
              qs.ket (RegEncoding.writeNat work t.1 base)) := by
            simpa using
              eval_finset_sum
                qs
                (Gate.H q)
                Finset.univ
                (fun t =>
                  α t •
                    qs.ket
                      (RegEncoding.writeNat work t.1 base))

      _ =
        ∑ t : Fin (ASize work),
          α t •
            qs.eval
              (Gate.H q)
              (qs.ket (RegEncoding.writeNat work t.1 base)) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [qs.eval_smul]

  have hterm :
      ∀ t : Fin (ASize work),
        HRegWorkSpan qs work base
          (α t •
            qs.eval
              (Gate.H q)
              (qs.ket (RegEncoding.writeNat work t.1 base))) := by
    intro t

    apply hregWorkSpan_smul qs work base

    rw [HadamardSemantics.eval_H_ket
      (qs := qs)
      (q := q)
      (b := RegEncoding.writeNat work t.1 base)]

    apply hregWorkSpan_smul qs work base
    apply hregWorkSpan_add qs work base

    · exact
        hregWorkSpan_qubit_write
          qs work base q hqlo hqhi t 0

    ·
      apply hregWorkSpan_smul qs work base
      exact
        hregWorkSpan_qubit_write
          qs work base q hqlo hqhi t 1

  have hsum :
      HRegWorkSpan qs work base
        (∑ t : Fin (ASize work),
          α t •
            qs.eval
              (Gate.H q)
              (qs.ket (RegEncoding.writeNat work t.1 base))) := by
    apply hregWorkSpan_sum qs work base
    intro t ht
    exact hterm t

  rw [heval]
  exact hsum


private lemma mem_regQubits_bounds
    (work : Reg)
    {q : ℕ}
    (hq : q ∈ regQubits work) :
    work.lo ≤ q ∧ q < work.hi := by
  unfold regQubits at hq
  rcases List.mem_map.mp hq with ⟨i, hi, rfl⟩
  have hi' : i < work.size := List.mem_range.mp hi

  constructor
  · omega
  · unfold Reg.hi
    omega


private lemma eval_foldl_H_preserves_hregWorkSpan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [HadamardSemantics qs]
    (work : Reg)
    (base : qs.Basis)
    (qsList : List ℕ) :
    (∀ q, q ∈ qsList → work.lo ≤ q ∧ q < work.hi) →
    ∀ (acc : Gate),
      (∀ ξ : qs.State,
        HRegWorkSpan qs work base ξ →
        HRegWorkSpan qs work base (qs.eval acc ξ)) →
      ∀ ξ : qs.State,
        HRegWorkSpan qs work base ξ →
        HRegWorkSpan qs work base
          (qs.eval
            (qsList.foldl
              (fun acc q => Gate.seq (Gate.H q) acc)
              acc)
            ξ) := by
  induction qsList with
  | nil =>
      intro _ acc hacc ξ hξ
      simpa using hacc ξ hξ

  | cons q qsList ih =>
      intro hbounds acc hacc ξ hξ

      have hq : work.lo ≤ q ∧ q < work.hi :=
        hbounds q (by simp)

      have htail :
          ∀ r, r ∈ qsList → work.lo ≤ r ∧ r < work.hi := by
        intro r hr
        exact hbounds r (by simp [hr])

      have hacc' :
          ∀ ξ : qs.State,
            HRegWorkSpan qs work base ξ →
            HRegWorkSpan qs work base
              (qs.eval (Gate.seq (Gate.H q) acc) ξ) := by
        intro ξ hξ

        have hH :
            HRegWorkSpan qs work base
              (qs.eval (Gate.H q) ξ) :=
          eval_H_preserves_hregWorkSpan
            qs work base q hq.1 hq.2 ξ hξ

        simpa [qs.eval_seq] using
          hacc (qs.eval (Gate.H q) ξ) hH

      simpa [List.foldl] using
        ih
          htail
          (Gate.seq (Gate.H q) acc)
          hacc'
          ξ
          hξ


lemma eval_Hreg_work_expansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [HadamardSemantics qs]
    (work : Reg)
    (b : qs.Basis)
    (z : Fin (ASize work)) :
    ∃ β : Fin (ASize work) → ℂ,
      qs.eval (H_reg work)
          (qs.ket (RegEncoding.writeNat work z.1 b))
        =
      ∑ t : Fin (ASize work),
        β t •
          qs.ket (RegEncoding.writeNat work t.1 b) := by
  classical

  have hstart :
      HRegWorkSpan qs work b
        (qs.ket (RegEncoding.writeNat work z.1 b)) :=
    hregWorkSpan_ket_write qs work b z

  have hbounds :
      ∀ q, q ∈ regQubits work → work.lo ≤ q ∧ q < work.hi := by
    intro q hq
    exact mem_regQubits_bounds work hq

  have hid :
      ∀ ξ : qs.State,
        HRegWorkSpan qs work b ξ →
        HRegWorkSpan qs work b (qs.eval Gate.id ξ) := by
    intro ξ hξ
    simpa [qs.eval_id] using hξ

  have hfinal :
      HRegWorkSpan qs work b
        (qs.eval
          ((regQubits work).foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            Gate.id)
          (qs.ket (RegEncoding.writeNat work z.1 b))) :=
    eval_foldl_H_preserves_hregWorkSpan
      qs
      work
      b
      (regQubits work)
      hbounds
      Gate.id
      hid
      (qs.ket (RegEncoding.writeNat work z.1 b))
      hstart

  rcases hfinal with ⟨β, hβ⟩
  refine ⟨β, ?_⟩
  simpa [H_reg] using hβ

lemma alg1_step1_ket_expansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    ∃ α : Fin (ASize cfg.env.work) → ℂ,
      qs.eval
          (step1
            (Basis := qs.Basis)
            cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
          (qs.ket b)
        =
      ∑ t : Fin (ASize cfg.env.work),
        α t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b) := by
  classical

  let φ : ℝ :=
    (2 * Real.pi * ((cfg.c + cfg.env.N - 1) % cfg.env.N))
      / (cfg.env.N : ℝ)

  have hwork_zero : RegEncoding.toNat cfg.env.work b = 0 := hb.2.2.1

  have hdatawork : Disjoint cfg.env.data cfg.env.work := by
    rcases cfg.layout.1 with h | h
    · left
      apply le_trans ?_ h
      change cfg.env.data.lo + cfg.env.data.size
        ≤ cfg.env.data.lo + (cfg.env.data.size + 1)
      omega
    · exact Or.inr h

  have hwrite_overwrite :
      ∀ v w : ℕ,
        RegEncoding.writeNat cfg.env.work v
            (RegEncoding.writeNat cfg.env.work w b)
          =
        RegEncoding.writeNat cfg.env.work v b := by
    intro v w
    apply RegEncoding.basis_ext
    intro q
    by_cases hqlo : cfg.env.work.lo ≤ q
    · by_cases hqhi : q < cfg.env.work.hi
      · exact
          RegEncoding.bit_writeNat_in
            (r := cfg.env.work) (v := v)
            (b1 := RegEncoding.writeNat cfg.env.work w b)
            (b2 := b) (q := q) hqlo hqhi
      · have hout : q < cfg.env.work.lo ∨ cfg.env.work.hi ≤ q :=
          Or.inr (Nat.le_of_not_gt hqhi)
        rw [RegEncoding.bit_writeNat_out
              (r := cfg.env.work) (v := v)
              (b := RegEncoding.writeNat cfg.env.work w b)
              (q := q) hout,
            RegEncoding.bit_writeNat_out
              (r := cfg.env.work) (v := v)
              (b := b) (q := q) hout,
            RegEncoding.bit_writeNat_out
              (r := cfg.env.work) (v := w)
              (b := b) (q := q) hout]
    · have hout : q < cfg.env.work.lo ∨ cfg.env.work.hi ≤ q :=
        Or.inl (Nat.lt_of_not_ge hqlo)
      rw [RegEncoding.bit_writeNat_out
            (r := cfg.env.work) (v := v)
            (b := RegEncoding.writeNat cfg.env.work w b)
            (q := q) hout,
          RegEncoding.bit_writeNat_out
            (r := cfg.env.work) (v := v)
            (b := b) (q := q) hout,
          RegEncoding.bit_writeNat_out
            (r := cfg.env.work) (v := w)
            (b := b) (q := q) hout]

  let z0 : Fin (ASize cfg.env.work) :=
    ⟨0, by
      simpa [← hwork_zero] using
        RegEncoding.toNat_lt_ASize cfg.env.work b⟩

  have hz0 : RegEncoding.writeNat cfg.env.work z0.1 b = b := by
    change RegEncoding.writeNat cfg.env.work 0 b = b
    rw [← hwork_zero]
    exact RegEncoding.writeNat_toNat (r := cfg.env.work) (b := b)

  rcases eval_Hreg_work_expansion qs cfg.env.work b z0 with
    ⟨a, ha⟩

  let L : Fin (ASize cfg.env.work) → ℂ :=
    fun z =>
      Classical.choose
        (eval_cphaseprod_work_diagonal
          qs cfg.ctrl φ cfg.env.data cfg.env.work b z hdatawork)

  have hL :
      ∀ z : Fin (ASize cfg.env.work),
        qs.eval
            (Gate.CPhaseProd
              cfg.ctrl φ cfg.env.data cfg.env.work)
            (qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b))
          =
        L z •
          qs.ket
            (RegEncoding.writeNat cfg.env.work z.1 b) := by
    intro z
    exact Classical.choose_spec
      (eval_cphaseprod_work_diagonal
        qs cfg.ctrl φ cfg.env.data cfg.env.work b z hdatawork)

  let γ :
      Fin (ASize cfg.env.work) →
        Fin (ASize cfg.env.work) →
          ℂ :=
    fun z =>
      Classical.choose
        (eval_iqft_work_expansion qs cfg.env.work
          (RegEncoding.writeNat cfg.env.work z.1 b))

  have hγ :
      ∀ z : Fin (ASize cfg.env.work),
        qs.eval (IQFT cfg.env.work)
            (qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b))
          =
        ∑ t : Fin (ASize cfg.env.work),
          γ z t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
    intro z
    have hraw := Classical.choose_spec
      (eval_iqft_work_expansion qs cfg.env.work
        (RegEncoding.writeNat cfg.env.work z.1 b))
    calc
      qs.eval (IQFT cfg.env.work)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work z.1 b))
          =
        ∑ t : Fin (ASize cfg.env.work),
          γ z t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1
                (RegEncoding.writeNat cfg.env.work z.1 b)) := hraw
      _ =
        ∑ t : Fin (ASize cfg.env.work),
          γ z t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hwrite_overwrite t.1 z.1]

  refine ⟨fun t => ∑ z, a z * L z * γ z t, ?_⟩

  have hH :
      qs.eval (H_reg cfg.env.work) (qs.ket b)
        =
      ∑ z : Fin (ASize cfg.env.work),
        a z •
          qs.ket
            (RegEncoding.writeNat cfg.env.work z.1 b) := by
    calc
      qs.eval (H_reg cfg.env.work) (qs.ket b)
          =
        qs.eval (H_reg cfg.env.work)
          (qs.ket (RegEncoding.writeNat cfg.env.work z0.1 b)) := by
            rw [hz0]
      _ =
        ∑ z : Fin (ASize cfg.env.work),
          a z •
            qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b) := ha

  have hphase :
      qs.eval
          (Gate.CPhaseProd
            cfg.ctrl φ cfg.env.data cfg.env.work)
          (qs.eval (H_reg cfg.env.work) (qs.ket b))
        =
      ∑ z : Fin (ASize cfg.env.work),
        (a z * L z) •
          qs.ket
            (RegEncoding.writeNat cfg.env.work z.1 b) := by
    rw [hH]
    calc
      qs.eval
          (Gate.CPhaseProd
            cfg.ctrl φ cfg.env.data cfg.env.work)
          (∑ z : Fin (ASize cfg.env.work),
            a z •
              qs.ket
                (RegEncoding.writeNat cfg.env.work z.1 b))
          =
        ∑ z : Fin (ASize cfg.env.work),
          qs.eval
            (Gate.CPhaseProd
              cfg.ctrl φ cfg.env.data cfg.env.work)
            (a z •
              qs.ket
                (RegEncoding.writeNat cfg.env.work z.1 b)) := by
            simpa using
              eval_finset_sum
                qs
                (Gate.CPhaseProd
                  cfg.ctrl φ cfg.env.data cfg.env.work)
                Finset.univ
                (fun z =>
                  a z •
                    qs.ket
                      (RegEncoding.writeNat cfg.env.work z.1 b))
      _ =
        ∑ z : Fin (ASize cfg.env.work),
          a z •
            qs.eval
              (Gate.CPhaseProd
                cfg.ctrl φ cfg.env.data cfg.env.work)
              (qs.ket
                (RegEncoding.writeNat cfg.env.work z.1 b)) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [qs.eval_smul]
      _ =
        ∑ z : Fin (ASize cfg.env.work),
          (a z * L z) •
            qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hL z, smul_smul]

  have hfubini :
      (∑ z : Fin (ASize cfg.env.work),
        (a z * L z) •
          ∑ t : Fin (ASize cfg.env.work),
            γ z t •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b))
      =
      ∑ t : Fin (ASize cfg.env.work),
        (∑ z : Fin (ASize cfg.env.work),
          a z * L z * γ z t) •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
    calc
      (∑ z : Fin (ASize cfg.env.work),
        (a z * L z) •
          ∑ t : Fin (ASize cfg.env.work),
            γ z t •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b))
          =
        ∑ z : Fin (ASize cfg.env.work),
          ∑ t : Fin (ASize cfg.env.work),
            ((a z * L z) * γ z t) •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro t ht
            rw [smul_smul]
      _ =
        ∑ t : Fin (ASize cfg.env.work),
          ∑ z : Fin (ASize cfg.env.work),
            ((a z * L z) * γ z t) •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b) := by
            rw [Finset.sum_comm]
      _ =
        ∑ t : Fin (ASize cfg.env.work),
          (∑ z : Fin (ASize cfg.env.work),
            a z * L z * γ z t) •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b) := by
            simp [Finset.sum_smul, mul_assoc]

  have hmain :
      qs.eval (IQFT cfg.env.work)
      (qs.eval
        (Gate.CPhaseProd
          cfg.ctrl φ cfg.env.data cfg.env.work)
        (qs.eval (H_reg cfg.env.work) (qs.ket b)))
      =
      ∑ t : Fin (ASize cfg.env.work),
        (∑ z : Fin (ASize cfg.env.work),
          a z * L z * γ z t) •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
    rw [hphase]
    calc
      qs.eval (IQFT cfg.env.work)
        (∑ z : Fin (ASize cfg.env.work),
          (a z * L z) •
            qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b))
        =
      ∑ z : Fin (ASize cfg.env.work),
        qs.eval (IQFT cfg.env.work)
          ((a z * L z) •
            qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b)) := by
          simpa using
            eval_finset_sum
              qs
              (IQFT cfg.env.work)
              Finset.univ
              (fun z =>
                (a z * L z) •
                  qs.ket
                    (RegEncoding.writeNat cfg.env.work z.1 b))
      _ =
        ∑ z : Fin (ASize cfg.env.work),
          (a z * L z) •
            qs.eval (IQFT cfg.env.work)
              (qs.ket
                (RegEncoding.writeNat cfg.env.work z.1 b)) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [qs.eval_smul]
      _ =
        ∑ z : Fin (ASize cfg.env.work),
          (a z * L z) •
            ∑ t : Fin (ASize cfg.env.work),
              γ z t •
                qs.ket
                  (RegEncoding.writeNat cfg.env.work t.1 b) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hγ z]
      _ =
        ∑ t : Fin (ASize cfg.env.work),
          (∑ z : Fin (ASize cfg.env.work),
            a z * L z * γ z t) •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b) := hfubini

  simpa [step1, qs.eval_seq, φ] using hmain

private def HasGoodInputExpansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (φ : qs.State) : Prop :=
  ∃ (s : Finset qs.Basis) (α : qs.Basis → ℂ),
    φ =
      ∑ b ∈ s,
        α b • qs.ket b
    ∧
    ∀ b ∈ s,
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b


private lemma good_input_expansion_of_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (ψ : qs.State)
    (hψ : cfg.ValidState qs ψ) :
    HasGoodInputExpansion qs cfg ψ := by
  classical

  dsimp [
    ModMulConfig.ValidState,
    ValidModMulState
  ] at hψ

  let P : qs.State → Prop :=
    HasGoodInputExpansion qs cfg

  change P ψ

  refine Submodule.span_induction
    (s := ({ φ : qs.State |
        ∃ b : qs.Basis,
          GoodModMulBasisInput qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b ∧
          φ = qs.ket b } : Set qs.State))
    (p := fun φ _ => P φ)
    ?_ ?_ ?_ ?_ hψ

  · intro φ hφ
    rcases hφ with ⟨b, hb, rfl⟩
    refine ⟨{b}, fun b' => if b' = b then 1 else 0, ?_, ?_⟩
    · simp
    · intro b' hb'
      have hb_eq : b' = b := by
        simpa using hb'
      subst hb_eq
      exact hb

  · refine ⟨∅, fun _ => 0, ?_, ?_⟩
    · simp
    · simp

  · intro φ χ _hφmem _hχmem hφ hχ
    rcases hφ with ⟨sφ, αφ, hφeq, hφgood⟩
    rcases hχ with ⟨sχ, αχ, hχeq, hχgood⟩

    let α : qs.Basis → ℂ :=
      fun b =>
        (if b ∈ sφ then αφ b else 0)
          +
        (if b ∈ sχ then αχ b else 0)

    refine ⟨sφ ∪ sχ, α, ?_, ?_⟩

    · have hsumφ :
          (∑ b ∈ sφ ∪ sχ,
            (if b ∈ sφ then αφ b else 0) • qs.ket b)
            =
          ∑ b ∈ sφ,
            αφ b • qs.ket b := by
          have h :
              (∑ b ∈ sφ,
                (if b ∈ sφ then αφ b else 0) • qs.ket b)
                =
              ∑ b ∈ sφ ∪ sχ,
                (if b ∈ sφ then αφ b else 0) • qs.ket b := by
            refine Finset.sum_subset Finset.subset_union_left ?_
            intro b hb_union hb_not_mem
            simp [hb_not_mem]
          calc
            (∑ b ∈ sφ ∪ sχ,
              (if b ∈ sφ then αφ b else 0) • qs.ket b)
                =
              ∑ b ∈ sφ,
                (if b ∈ sφ then αφ b else 0) • qs.ket b := h.symm
            _ =
              ∑ b ∈ sφ,
                αφ b • qs.ket b := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  simp [hb]

      have hsumχ :
          (∑ b ∈ sφ ∪ sχ,
            (if b ∈ sχ then αχ b else 0) • qs.ket b)
            =
          ∑ b ∈ sχ,
            αχ b • qs.ket b := by
          have h :
              (∑ b ∈ sχ,
                (if b ∈ sχ then αχ b else 0) • qs.ket b)
                =
              ∑ b ∈ sφ ∪ sχ,
                (if b ∈ sχ then αχ b else 0) • qs.ket b := by
            refine Finset.sum_subset Finset.subset_union_right ?_
            intro b hb_union hb_not_mem
            simp [hb_not_mem]
          calc
            (∑ b ∈ sφ ∪ sχ,
              (if b ∈ sχ then αχ b else 0) • qs.ket b)
                =
              ∑ b ∈ sχ,
                (if b ∈ sχ then αχ b else 0) • qs.ket b := h.symm
            _ =
              ∑ b ∈ sχ,
                αχ b • qs.ket b := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  simp [hb]

      calc
        φ + χ
            =
          (∑ b ∈ sφ, αφ b • qs.ket b)
            +
          (∑ b ∈ sχ, αχ b • qs.ket b) := by
            rw [hφeq, hχeq]
        _ =
          (∑ b ∈ sφ ∪ sχ,
            (if b ∈ sφ then αφ b else 0) • qs.ket b)
            +
          (∑ b ∈ sφ ∪ sχ,
            (if b ∈ sχ then αχ b else 0) • qs.ket b) := by
            rw [hsumφ, hsumχ]
        _ =
          ∑ b ∈ sφ ∪ sχ,
            ((if b ∈ sφ then αφ b else 0) • qs.ket b
              +
             (if b ∈ sχ then αχ b else 0) • qs.ket b) := by
            rw [← Finset.sum_add_distrib]
        _ =
          ∑ b ∈ sφ ∪ sχ,
            α b • qs.ket b := by
            apply Finset.sum_congr rfl
            intro b hb
            simp [α, add_smul]

    · intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact hφgood b hb
      · exact hχgood b hb

  · intro a φ _hφmem hφ
    rcases hφ with ⟨s, α, hφeq, hφgood⟩
    refine ⟨s, fun b => a * α b, ?_, hφgood⟩
    calc
      a • φ
          =
        a • (∑ b ∈ s, α b • qs.ket b) := by
          rw [hφeq]
      _ =
        ∑ b ∈ s, a • (α b • qs.ket b) := by
          rw [Finset.smul_sum]
      _ =
        ∑ b ∈ s, (a * α b) • qs.ket b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [smul_smul]

private lemma qftPhase_zero_left
    (N y : ℕ) :
    qftPhase N 0 y = 1 := by
  simp [qftPhase, ωPow]

private lemma regQubits_succ_eq_append
    (lo n : ℕ) :
    regQubits ({ lo := lo, size := n + 1 } : Reg)
      =
    regQubits ({ lo := lo, size := n } : Reg) ++ [lo + n] := by
  simp [regQubits, List.range_succ, List.map_append]

private lemma H_reg_succ_eval
    (qs : QSemantics)
    (lo n : ℕ)
    (ψ : qs.State) :
    qs.eval (H_reg ({ lo := lo, size := n + 1 } : Reg)) ψ
      =
    qs.eval (H_reg ({ lo := lo, size := n } : Reg))
      (qs.eval (Gate.H (lo + n)) ψ) := by
  simp [
    H_reg,
    regQubits_succ_eq_append,
    List.foldl_append,
    qs.eval_seq
  ]

private lemma Hreg_QFT_scalar_succ
    (n : ℕ) :
    ((1 / Real.sqrt (2 : ℝ) : ℂ) *
        (1 / Real.sqrt (((2 ^ n : ℕ) : ℝ)) : ℂ))
      =
    (1 / Real.sqrt (((2 ^ (n + 1) : ℕ) : ℝ)) : ℂ) := by
  norm_num [Nat.pow_succ]

private lemma uniform_sum_succ_split
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (lo n : ℕ)
    (b : qs.Basis) :
    (∑ y : Fin (ASize ({ lo := lo, size := n + 1 } : Reg)),
        qs.ket
          (RegEncoding.writeNat
            ({ lo := lo, size := n + 1 } : Reg) y.1 b))
      =
    (∑ y : Fin (ASize ({ lo := lo, size := n } : Reg)),
        qs.ket
          (RegEncoding.writeNat
            ({ lo := lo, size := n } : Reg) y.1
            (RegEncoding.writeNat
              ({ lo := lo + n, size := 1 } : Reg) 0 b)))
      +
    (∑ y : Fin (ASize ({ lo := lo, size := n } : Reg)),
        qs.ket
          (RegEncoding.writeNat
            ({ lo := lo, size := n } : Reg) y.1
            (RegEncoding.writeNat
              ({ lo := lo + n, size := 1 } : Reg) 1 b))) :=
  by
  classical

  let r : Reg := { lo := lo, size := n + 1 }
  let low : Reg := { lo := lo, size := n }
  let high : Reg := { lo := lo + n, size := 1 }
  let M : ℕ := ASize low

  let m : SplitPoint r :=
    ⟨n, by simp [r, regSize]⟩

  have hleft : splitLeft r m = low := by
    simp [r, low, m, splitLeft]

  have hright : splitRight r m = high := by
    simp [r, high, m, splitRight]

  have hdisj : Disjoint low high := by
    unfold Shor.Disjoint
    left
    simp [low, high, Reg.hi]

  have hsize : ASize r = M + M := by
    simp [r, low, M, ASize, regSize, Nat.pow_succ, Nat.mul_two]

  have hhigh_zero : 0 < ASize high := by
    norm_num [high, ASize, regSize]

  have hhigh_one : 1 < ASize high := by
    norm_num [high, ASize, regSize]

  let f : ℕ → qs.State :=
    fun y => qs.ket (RegEncoding.writeNat r y b)

  let g0 : ℕ → qs.State :=
    fun y =>
      qs.ket
        (RegEncoding.writeNat low y
          (RegEncoding.writeNat high 0 b))

  let g1 : ℕ → qs.State :=
    fun y =>
      qs.ket
        (RegEncoding.writeNat low y
          (RegEncoding.writeNat high 1 b))

  have hlow :
      ∀ y : ℕ, y < M → f y = g0 y := by
    intro y hy

    have hs :=
      RegEncoding.writeNat_split
        r m 0 y b
        (by simpa [hleft, M] using hy)
        (by simpa [hright] using hhigh_zero)

    have hs' :
        RegEncoding.writeNat r y b
          =
        RegEncoding.writeNat high 0
          (RegEncoding.writeNat low y b) := by
      simpa [hleft, hright, M] using hs

    have hcomm :
        RegEncoding.writeNat low y
            (RegEncoding.writeNat high 0 b)
          =
        RegEncoding.writeNat high 0
            (RegEncoding.writeNat low y b) :=
      writeNat_comm_of_disjoint low high hdisj y 0 b

    dsimp [f, g0]
    exact congrArg qs.ket (hs'.trans hcomm.symm)

  have hhigh :
      ∀ y : ℕ, y < M → f (M + y) = g1 y := by
    intro y hy

    have hs :=
      RegEncoding.writeNat_split
        r m 1 y b
        (by simpa [hleft, M] using hy)
        (by simpa [hright] using hhigh_one)

    have hs' :
        RegEncoding.writeNat r (M + y) b
          =
        RegEncoding.writeNat high 1
          (RegEncoding.writeNat low y b) := by
      simpa [hleft, hright, M, Nat.add_comm] using hs

    have hcomm :
        RegEncoding.writeNat low y
            (RegEncoding.writeNat high 1 b)
          =
        RegEncoding.writeNat high 1
            (RegEncoding.writeNat low y b) :=
      writeNat_comm_of_disjoint low high hdisj y 1 b

    dsimp [f, g1]
    exact congrArg qs.ket (hs'.trans hcomm.symm)

  have htail :
      (∑ y ∈ Finset.range M, f (M + y))
        =
      ∑ y ∈ Finset.Ico M (M + M), f y := by
    symm
    simpa [Nat.add_sub_cancel] using
      (Finset.sum_Ico_eq_sum_range f M (M + M))

  have hsplit :
      (∑ y ∈ Finset.range M, f y)
        +
      (∑ y ∈ Finset.range M, f (M + y))
        =
      ∑ y ∈ Finset.range (ASize r), f y := by
    calc
      (∑ y ∈ Finset.range M, f y)
          +
        (∑ y ∈ Finset.range M, f (M + y))
          =
        (∑ y ∈ Finset.range M, f y)
          +
        (∑ y ∈ Finset.Ico M (M + M), f y) := by
          rw [htail]

      _ =
        ∑ y ∈ Finset.range (M + M), f y := by
          exact Finset.sum_range_add_sum_Ico f (by omega)

      _ =
        ∑ y ∈ Finset.range (ASize r), f y := by
          rw [hsize]

  have hsum0 :
      (∑ y ∈ Finset.range M, f y)
        =
      ∑ y ∈ Finset.range M, g0 y := by
    apply Finset.sum_congr rfl
    intro y hy
    exact hlow y (Finset.mem_range.mp hy)

  have hsum1 :
      (∑ y ∈ Finset.range M, f (M + y))
        =
      ∑ y ∈ Finset.range M, g1 y := by
    apply Finset.sum_congr rfl
    intro y hy
    exact hhigh y (Finset.mem_range.mp hy)

  have hmain :
      (∑ y : Fin (ASize r), f y.1)
        =
      (∑ y : Fin M, g0 y.1)
        +
      (∑ y : Fin M, g1 y.1) := by
    calc
      (∑ y : Fin (ASize r), f y.1)
          =
        ∑ y ∈ Finset.range (ASize r), f y := by
          simpa using
            (Fin.sum_univ_eq_sum_range f (ASize r))

      _ =
        (∑ y ∈ Finset.range M, f y)
          +
        (∑ y ∈ Finset.range M, f (M + y)) := by
          exact hsplit.symm

      _ =
        (∑ y ∈ Finset.range M, g0 y)
          +
        (∑ y ∈ Finset.range M, g1 y) := by
          rw [hsum0, hsum1]

      _ =
        (∑ y : Fin M, g0 y.1)
          +
        (∑ y : Fin M, g1 y.1) := by
          rw [Fin.sum_univ_eq_sum_range g0 M]
          rw [Fin.sum_univ_eq_sum_range g1 M]

  simpa [r, low, high, M, f, g0, g1] using hmain

lemma eval_Hreg_zero_uniform_sum
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (work : Reg)
    (b : qs.Basis)
    (hwork0 : RegEncoding.toNat work b = 0) :
    qs.eval (H_reg work) (qs.ket b)
      =
    ((1 / Real.sqrt ((ASize work : ℕ) : ℝ) : ℂ)) •
      ∑ y : Fin (ASize work),
        qs.ket (RegEncoding.writeNat work y.1 b) := by
  classical
  rcases work with ⟨lo, n⟩
  induction n generalizing b with
  | zero =>
      have hwrite :
          RegEncoding.writeNat ({ lo := lo, size := 0 } : Reg) 0 b = b := by
        exact
          (congrArg
            (fun v =>
              RegEncoding.writeNat
                ({ lo := lo, size := 0 } : Reg) v b)
            hwork0.symm).trans
            (RegEncoding.writeNat_toNat
              (r := ({ lo := lo, size := 0 } : Reg)) (b := b))
      simp [H_reg, regQubits, ASize, regSize, qs.eval_id, hwrite]
  | succ n ih =>
      let r : Reg := { lo := lo, size := n + 1 }
      let low : Reg := { lo := lo, size := n }
      let high : Reg := { lo := lo + n, size := 1 }
      let q : ℕ := lo + n

      have hsplit0 :
          RegEncoding.toNat low b
            + ASize low * RegEncoding.toNat high b = 0 := by
        have hright_size : n + 1 - n = 1 := by
          omega
        have hsplit :=
          RegEncoding.toNat_split
            (r := r)
            (m := ⟨n, by simp [r, regSize]⟩)
            (b := b)
        rw [hwork0] at hsplit
        have hsplit' :
            0 =
              RegEncoding.toNat low b
                + ASize low * RegEncoding.toNat high b := by
          simpa only [
            r, low, high, splitLeft, splitRight, regSize, ASize,
            hright_size
          ] using hsplit
        exact hsplit'.symm

      have hlow_b : RegEncoding.toNat low b = 0 := by
        omega

      have hdisj : Shor.Disjoint low high := by
        unfold Shor.Disjoint low high Reg.hi
        simp

      have hlow0 :
          RegEncoding.toNat low (RegEncoding.writeNat high 0 b) = 0 := by
        rw [RegEncoding.toNat_left_write_right low high hdisj b 0]
        exact hlow_b

      have hlow1 :
          RegEncoding.toNat low (RegEncoding.writeNat high 1 b) = 0 := by
        rw [RegEncoding.toNat_left_write_right low high hdisj b 1]
        exact hlow_b

      have hqlo : r.lo ≤ q := by
        simp [r, q]

      have hqhi : q < r.hi := by
        simp [r, q, Reg.hi]

      have hbit : RegEncoding.bit q b = false := by
        rw [RegEncoding.bit_eq_testBit_toNat (r := r) (b := b) (q := q) hqlo hqhi]
        rw [hwork0]
        simp [r, q]

      have hHq :
          qs.eval (Gate.H q) (qs.ket b)
            =
          ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
            (qs.ket (RegEncoding.writeNat high 0 b)
              + qs.ket (RegEncoding.writeNat high 1 b)) := by
        have hqh : qubitReg q = high := by
          simp [qubitReg, high, q]
        rw [HadamardSemantics.eval_H_ket]
        simp [hqh, hbit, smul_add]

      have ih0 :=
        ih (RegEncoding.writeNat high 0 b) hlow0

      have ih1 :=
        ih (RegEncoding.writeNat high 1 b) hlow1

      have hleft :
          qs.eval (H_reg r) (qs.ket b)
            =
          ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
            ((((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                ∑ y : Fin (ASize low),
                  qs.ket (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 0 b)))
              +
              (((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                ∑ y : Fin (ASize low),
                  qs.ket (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 1 b)))) := by
        calc
          qs.eval (H_reg r) (qs.ket b)
              =
            qs.eval (H_reg low)
              (qs.eval (Gate.H q) (qs.ket b)) := by
                simpa [r, low, q] using
                  H_reg_succ_eval qs lo n (qs.ket b)
          _ =
            qs.eval (H_reg low)
              (((1 / Real.sqrt (2 : ℝ) : ℂ)) •
                (qs.ket (RegEncoding.writeNat high 0 b)
                  + qs.ket (RegEncoding.writeNat high 1 b))) := by
                rw [hHq]
          _ =
            ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
              (qs.eval (H_reg low)
                  (qs.ket (RegEncoding.writeNat high 0 b))
                +
                qs.eval (H_reg low)
                  (qs.ket (RegEncoding.writeNat high 1 b))) := by
                rw [qs.eval_smul, qs.eval_add]
          _ =
            ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
              ((((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                  ∑ y : Fin (ASize low),
                    qs.ket (RegEncoding.writeNat low y.1
                      (RegEncoding.writeNat high 0 b)))
                +
                (((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                  ∑ y : Fin (ASize low),
                    qs.ket (RegEncoding.writeNat low y.1
                      (RegEncoding.writeNat high 1 b)))) := by
                rw [ih0, ih1]

      have hsum :
          (∑ y : Fin (ASize r),
              qs.ket (RegEncoding.writeNat r y.1 b))
            =
          (∑ y : Fin (ASize low),
              qs.ket
                (RegEncoding.writeNat low y.1
                  (RegEncoding.writeNat high 0 b)))
            +
          (∑ y : Fin (ASize low),
              qs.ket
                (RegEncoding.writeNat low y.1
                  (RegEncoding.writeNat high 1 b))) := by
        simpa [r, low, high] using
          uniform_sum_succ_split qs lo n b

      have hscalar :
          ((1 / Real.sqrt (2 : ℝ) : ℂ) *
              (1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ))
            =
          (1 / Real.sqrt ((ASize r : ℕ) : ℝ) : ℂ) := by
        simpa [r, low, ASize, regSize] using
          Hreg_QFT_scalar_succ n

      calc
        qs.eval (H_reg { lo := lo, size := n + 1 }) (qs.ket b)
            =
          ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
            ((((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                ∑ y : Fin (ASize low),
                  qs.ket (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 0 b)))
              +
              (((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                ∑ y : Fin (ASize low),
                  qs.ket (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 1 b)))) := by
              simpa [r] using hleft
        _ =
          (((1 / Real.sqrt (2 : ℝ) : ℂ) *
              (1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ))) •
            ((∑ y : Fin (ASize low),
                qs.ket
                  (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 0 b)))
              +
              (∑ y : Fin (ASize low),
                qs.ket
                  (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 1 b)))) := by
              simp [smul_add, smul_smul]
        _ =
          ((1 / Real.sqrt ((ASize r : ℕ) : ℝ) : ℂ)) •
            ∑ y : Fin (ASize r),
              qs.ket (RegEncoding.writeNat r y.1 b) := by
              rw [hscalar, hsum]

lemma eval_Hreg_zero_eq_QFT
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (work : Reg)
    (b : qs.Basis)
    (hwork0 : RegEncoding.toNat work b = 0) :
    qs.eval (H_reg work) (qs.ket b)
      =
    qs.eval (Gate.QFT work) (qs.ket b) := by
  rw [eval_Hreg_zero_uniform_sum qs work b hwork0]
  rw [QFTSemantics.eval_QFT_ket]
  simp [ASize, qftPhase_zero_left, hwork0]

lemma eval_IQFT_Hreg_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (work : Reg)
    (b : qs.Basis)
    (hwork0 : RegEncoding.toNat work b = 0) :
    qs.eval (IQFT work)
      (qs.eval (H_reg work) (qs.ket b))
      =
    qs.ket b := by
  rw [eval_Hreg_zero_eq_QFT qs work b hwork0]
  simpa [IQFT] using
    qs.eval_adj_apply (Gate.QFT work) (qs.ket b)


lemma eval_CPhaseProd_fixes_work_of_target_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : qs.Basis) :
    qs.eval
        (Gate.CPhaseProd
          cfg.ctrl
          ((2 * Real.pi * ((cfg.c + cfg.env.N - 1) % cfg.env.N))
            / (cfg.env.N : ℝ))
          cfg.env.data
          cfg.env.work)
        (qs.eval (H_reg cfg.env.work) (qs.ket b))
      =
    qs.eval (H_reg cfg.env.work) (qs.ket b) := by
  classical

  let a : ℕ :=
    (cfg.c + cfg.env.N - 1) % cfg.env.N

  let φ : ℝ :=
    (2 * Real.pi * (a : ℝ)) / (cfg.env.N : ℝ)

  have hNpos : 0 < cfg.env.N :=
    Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

  have hdatawork : Disjoint cfg.env.data cfg.env.work := by
    rcases cfg.layout.1 with h | h
    · left
      change cfg.env.data.lo + cfg.env.data.size ≤ cfg.env.work.lo
      have h' :
          cfg.env.data.lo + (cfg.env.data.size + 1)
            ≤ cfg.env.work.lo := by
        simpa [extendHi, Reg.hi] using h
      omega
    · exact Or.inr h

  have hNneR : (cfg.env.N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hNpos

  have hphase_zero :
      ((2 * Real.pi * ((cfg.c + cfg.env.N - 1 : ℝ) % (cfg.env.N : ℝ)))
          / (cfg.env.N : ℝ)) = 0 := by
    have hmod_zero_expanded :
        (cfg.c + cfg.env.N - 1 : ℝ)
            - (cfg.env.N : ℝ)
              * ((cfg.c + cfg.env.N - 1 : ℝ) / (cfg.env.N : ℝ))
          = 0 := by
      field_simp [hNneR]
      ring
    have hmod_zero :
        ((cfg.c + cfg.env.N - 1 : ℝ) % (cfg.env.N : ℝ)) = 0 := by
      rw [EuclideanDomain.mod_eq_sub_mul_div]
      exact hmod_zero_expanded
    rw [hmod_zero]
    simp

  have hphase_zero_expanded :
      (2 * Real.pi *
            ((cfg.c + cfg.env.N - 1 : ℝ)
              - (cfg.c + cfg.env.N - 1 : ℝ)
                * (cfg.env.N : ℝ) / (cfg.env.N : ℝ))
          / (cfg.env.N : ℝ)) = 0 := by
    field_simp [hNneR]
    ring

  have hterm :
      ∀ t : Fin (ASize cfg.env.work),
        qs.eval
            (Gate.CPhaseProd
              cfg.ctrl
              ((2 * Real.pi * ((cfg.c + cfg.env.N - 1 : ℝ) % (cfg.env.N : ℝ)))
                / (cfg.env.N : ℝ))
              cfg.env.data cfg.env.work)
            (qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b))
          =
        qs.ket
          (RegEncoding.writeNat cfg.env.work t.1 b) := by
    intro t
    rw [
      eval_CPhaseProd_ket
        qs cfg.ctrl
        ((2 * Real.pi * ((cfg.c + cfg.env.N - 1 : ℝ) % (cfg.env.N : ℝ)))
          / (cfg.env.N : ℝ))
        cfg.env.data cfg.env.work
        (RegEncoding.writeNat cfg.env.work t.1 b)
        hdatawork
    ]
    by_cases hctrl :
        RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat cfg.env.work t.1 b)
    · simp [hctrl, hphase_zero_expanded]
    · simp [hctrl]

  let z0 : Fin (ASize cfg.env.work) :=
    ⟨RegEncoding.toNat cfg.env.work b,
      RegEncoding.toNat_lt_ASize cfg.env.work b⟩

  have hz0 :
      RegEncoding.writeNat cfg.env.work z0.1 b = b := by
    simpa [z0] using
      (RegEncoding.writeNat_toNat cfg.env.work b)

  rcases eval_Hreg_work_expansion qs cfg.env.work b z0 with
    ⟨β, hβ⟩

  have hH :
      qs.eval (H_reg cfg.env.work) (qs.ket b)
        =
      ∑ t : Fin (ASize cfg.env.work),
        β t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b) := by
    calc
      qs.eval (H_reg cfg.env.work) (qs.ket b)
          =
        qs.eval (H_reg cfg.env.work)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work z0.1 b)) := by
              rw [hz0]
      _ =
        ∑ t : Fin (ASize cfg.env.work),
          β t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := hβ

  calc
    qs.eval
        (Gate.CPhaseProd
          cfg.ctrl
          ((2 * Real.pi * ((cfg.c + cfg.env.N - 1) % cfg.env.N))
            / (cfg.env.N : ℝ))
          cfg.env.data
          cfg.env.work)
        (qs.eval (H_reg cfg.env.work) (qs.ket b))
      =
    qs.eval
        (Gate.CPhaseProd
          cfg.ctrl
          ((2 * Real.pi * ((cfg.c + cfg.env.N - 1 : ℝ) % (cfg.env.N : ℝ)))
            / (cfg.env.N : ℝ))
          cfg.env.data cfg.env.work)
        (∑ t : Fin (ASize cfg.env.work),
          β t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b)) := by
          rw [hH]

    _ =
    ∑ t : Fin (ASize cfg.env.work),
      qs.eval
        (Gate.CPhaseProd
          cfg.ctrl
          ((2 * Real.pi * ((cfg.c + cfg.env.N - 1 : ℝ) % (cfg.env.N : ℝ)))
            / (cfg.env.N : ℝ))
          cfg.env.data cfg.env.work)
        (β t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b)) := by
          simpa using
            eval_finset_sum
              qs
              (Gate.CPhaseProd
                cfg.ctrl
                ((2 * Real.pi * ((cfg.c + cfg.env.N - 1 : ℝ) % (cfg.env.N : ℝ)))
                  / (cfg.env.N : ℝ))
                cfg.env.data cfg.env.work)
              Finset.univ
              (fun t =>
                β t •
                  qs.ket
                    (RegEncoding.writeNat cfg.env.work t.1 b))

    _ =
    ∑ t : Fin (ASize cfg.env.work),
      β t •
        qs.eval
          (Gate.CPhaseProd
            cfg.ctrl
            ((2 * Real.pi * ((cfg.c + cfg.env.N - 1 : ℝ) % (cfg.env.N : ℝ)))
              / (cfg.env.N : ℝ))
            cfg.env.data cfg.env.work)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [qs.eval_smul]

    _ =
    ∑ t : Fin (ASize cfg.env.work),
      β t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work t.1 b) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hterm t]

    _ =
    qs.eval (H_reg cfg.env.work) (qs.ket b) :=
      hH.symm

lemma alg1_step1_zero_target_exact
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b):
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        (qs.ket b)
      =
    qs.ket b := by
  let φ : ℝ :=
    (2 * Real.pi * ((cfg.c + cfg.env.N - 1) % cfg.env.N))
      / (cfg.env.N : ℝ)

  have hphase :
      qs.eval
          (Gate.CPhaseProd
            cfg.ctrl φ cfg.env.data cfg.env.work)
          (qs.eval (H_reg cfg.env.work) (qs.ket b))
        =
      qs.eval (H_reg cfg.env.work) (qs.ket b) := by
    simpa [φ] using
      eval_CPhaseProd_fixes_work_of_target_zero qs cfg b

  calc
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        (qs.ket b)
      =
    qs.eval (IQFT cfg.env.work)
      (qs.eval
        (Gate.CPhaseProd cfg.ctrl φ cfg.env.data cfg.env.work)
        (qs.eval (H_reg cfg.env.work) (qs.ket b))) := by
          simp [step1, qs.eval_seq, φ]


    _ =
    qs.eval (IQFT cfg.env.work)
      (qs.eval (H_reg cfg.env.work) (qs.ket b)) := by
        rw [hphase]

    _ = qs.ket b :=
      eval_IQFT_Hreg_zero
        (qs := qs)
        cfg.env.work
        b
        hb.2.2.1
private lemma alg1_output_mod
    (c N x : ℕ)
    (hN : 0 < N) :
    (c * x) % N
      =
    (x + ((((c + N - 1) % N) * x) % N)) % N := by
  let a : ℕ := (c + N - 1) % N

  have ha :
      a ≡ c + N - 1 [MOD N] := by
    dsimp [a]
    exact Nat.mod_modEq (c + N - 1) N

  have hsucc :
      a + 1 ≡ c [MOD N] := by
    have h := Nat.ModEq.add_right 1 ha
    have hsum : (c + N - 1) + 1 = c + N := by
      omega
    rw [hsum] at h
    calc
      a + 1 ≡ c + N [MOD N] := h
      _ ≡ c [MOD N] := by
        simp [Nat.ModEq]

  have hcx :
      c * x ≡ (a + 1) * x [MOD N] :=
    Nat.ModEq.mul_right x hsucc.symm

  have hax :
      (a + 1) * x = x + a * x := by
    calc
      (a + 1) * x = a * x + 1 * x := Nat.add_mul a 1 x
      _ = a * x + x := by simp
      _ = x + a * x := Nat.add_comm _ _

  have hxr :
      x + ((a * x) % N) ≡ x + a * x [MOD N] :=
    Nat.ModEq.add_left x (Nat.mod_modEq (a * x) N)

  have hmod :
      c * x ≡ x + ((a * x) % N) [MOD N] := by
    calc
      c * x ≡ (a + 1) * x [MOD N] := hcx
      _ ≡ x + a * x [MOD N] := by rw [hax]
      _ ≡ x + ((a * x) % N) [MOD N] := hxr.symm

  simpa [Nat.ModEq, a] using hmod


private lemma nat_fraction_lt_iff_cross
    (a n t m : ℕ)
    (hn : 0 < n)
    (hm : 0 < m) :
    (a : ℝ) / (n : ℝ) < (t : ℝ) / (m : ℝ)
      ↔
    a * m < t * n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm

  constructor
  · intro h
    have h' :=
      (div_lt_div_iff₀ hnR hmR).mp h
    exact_mod_cast h'
  · intro h
    apply (div_lt_div_iff₀ hnR hmR).mpr
    exact_mod_cast h

lemma alg1_step4_cross_iff_overflow_of_good
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work))
    (hb :
      GoodModMulBasisInput
        (inferInstance : QSemantics)
        cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (ht : t ∈ alg1GoodLabels cfg b)
    (hzero :
      alg1TargetResidue cfg b = 0 →
      t.1 = 0) :
    alg1Step4CrossCondition cfg b t
      ↔
    alg1Overflow cfg b := by
  classical

  let N : ℕ := cfg.env.N
  let A : ℕ := ASize cfg.env.data
  let M : ℕ := ASize cfg.env.work
  let x : ℕ := RegEncoding.toNat cfg.env.data b
  let r : ℕ := alg1TargetResidue cfg b
  let y : ℕ := alg1OutputValue cfg b
  let s : ℕ := x + r

  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

  have hApos : 0 < A := by
    dsimp [A, ASize]
    positivity

  have hMpos : 0 < M := by
    dsimp [M, ASize]
    positivity

  have hxlt : x < N := by
    simpa [x, N] using hb.1

  have hrlt : r < N := by
    simpa [r, N] using alg1TargetResidue_lt_N cfg b

  have hslt : s < 2 * N := by
    dsimp [s]
    omega

  have hNposR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hNpos

  have hAposR : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast hApos

  have hMposR : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hMpos

  have hNleA : (N : ℝ) ≤ (A : ℝ) := by
    dsimp [N, A]
    exact_mod_cast cfg.env.data_capacity

  have heta :
      η < (1 / 2 : ℝ) :=
    cfg.env.precision.2.1

  have hetaN :
      η * (N : ℝ) < (1 / 2 : ℝ) * (N : ℝ) :=
    mul_lt_mul_of_pos_right heta hNposR

  have hhalfNleA :
      (1 / 2 : ℝ) * (N : ℝ) ≤ (A : ℝ) := by
    nlinarith

  have hdelta :
      η / (A : ℝ) < 1 / (N : ℝ) := by
    apply (div_lt_div_iff₀ hAposR hNposR).mpr
    nlinarith

  have hgood :
      |(r : ℝ) / (N : ℝ) - (t.1 : ℝ) / (M : ℝ)|
        <
      η / (A : ℝ) := by
    have hraw := (Finset.mem_filter.mp ht).2
    simpa [
      alg1GoodLabels,
      alg1TargetFraction,
      alg1WorkFraction,
      r, N, M, A
    ] using hraw

  rcases abs_lt.mp hgood with ⟨hgood_left, hgood_right⟩

  have hbelow :
      (r : ℝ) / (N : ℝ) - η / (A : ℝ)
        <
      (t.1 : ℝ) / (M : ℝ) := by
    linarith

  have habove :
      (t.1 : ℝ) / (M : ℝ)
        <
      (r : ℝ) / (N : ℝ) + η / (A : ℝ) := by
    linarith

  have hy_mod :
      y = s % N := by
    dsimp [y, s, r, x, N]
    by_cases hctrl : RegEncoding.bit cfg.ctrl b
    ·
      simp only [
        alg1OutputValue,
        alg1TargetResidue,
        hctrl,
        if_true
      ]
      exact
        alg1_output_mod
          cfg.c
          cfg.env.N
          (RegEncoding.toNat cfg.env.data b)
          (Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one)
    ·
      simp [
        alg1OutputValue,
        alg1TargetResidue,
        hctrl,
        Nat.mod_eq_of_lt hb.1
      ]

  change y * M < N * t.1 ↔ N ≤ s

  by_cases hover : N ≤ s
  ·
    have hy_over :
        y = s - N := by
      calc
        y = s % N := hy_mod
        _ = (s - N) % N := Nat.mod_eq_sub_mod hover
        _ = s - N := Nat.mod_eq_of_lt (by omega)

    have hylt :
        y < r := by
      rw [hy_over]
      dsimp [s]
      omega

    have hgapNat :
        y + 1 ≤ r :=
      Nat.succ_le_iff.mpr hylt

    have hgapR :
        (y : ℝ) + 1 ≤ (r : ℝ) := by
      exact_mod_cast hgapNat

    have hmul :
        ((y : ℝ) + 1) * (N : ℝ)
          ≤
        (r : ℝ) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hgapR (le_of_lt hNposR)

    have hdiv :
        ((y : ℝ) + 1) / (N : ℝ)
          ≤
        (r : ℝ) / (N : ℝ) :=
      (div_le_div_iff₀ hNposR hNposR).mpr <| by
        simpa [mul_comm] using hmul

    have hsplit :
        ((y : ℝ) + 1) / (N : ℝ)
          =
        (y : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
      ring

    rw [hsplit] at hdiv

    have hyfrac :
        (y : ℝ) / (N : ℝ)
          <
        (r : ℝ) / (N : ℝ) - η / (A : ℝ) := by
      linarith

    have hcrossfrac :
        (y : ℝ) / (N : ℝ)
          <
        (t.1 : ℝ) / (M : ℝ) :=
      lt_trans hyfrac hbelow

    have hcross :
        y * M < N * t.1 := by
      have hraw :=
        (nat_fraction_lt_iff_cross y N t.1 M hNpos hMpos).mp
          hcrossfrac
      simpa [Nat.mul_comm] using hraw

    constructor
    · intro _
      exact hover
    · intro _
      exact hcross

  ·
    have hy_no :
        y = s := by
      calc
        y = s % N := hy_mod
        _ = s := Nat.mod_eq_of_lt (lt_of_not_ge hover)

    by_cases hxzero : x = 0
    ·
      have hrzero :
          r = 0 := by
        dsimp [r]
        unfold alg1TargetResidue
        by_cases hctrl : RegEncoding.bit cfg.ctrl b
        · simp [hctrl]; simp_all only [Nat.cast_pos, Nat.cast_le, one_div, mul_lt_mul_iff_left₀,
          neg_lt_sub_iff_lt_add, not_le, mul_zero, Nat.zero_mod, N, A, M, x, r, s, y]
        · simp [hctrl]

      have hyzero :
          y = 0 := by
        rw [hy_no]
        dsimp [s]
        simp [hxzero, hrzero]

      have htzero :
          t.1 = 0 := by
        apply hzero
        simpa [r] using hrzero

      have hnotcross :
          ¬ y * M < N * t.1 := by
        simp [hyzero, htzero]

      constructor
      · intro h
        exact False.elim (hnotcross h)
      · intro h
        exact False.elim (hover h)

    ·
      have hxpos : 0 < x :=
        Nat.pos_of_ne_zero hxzero

      have hgapNat :
          r + 1 ≤ y := by
        rw [hy_no]
        dsimp [s]
        omega

      have hgapR :
          (r : ℝ) + 1 ≤ (y : ℝ) := by
        exact_mod_cast hgapNat

      have hmul :
          ((r : ℝ) + 1) * (N : ℝ)
            ≤
          (y : ℝ) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hgapR (le_of_lt hNposR)

      have hdiv :
          ((r : ℝ) + 1) / (N : ℝ)
            ≤
          (y : ℝ) / (N : ℝ) :=
        (div_le_div_iff₀ hNposR hNposR).mpr <| by
          simpa [mul_comm] using hmul

      have hsplit :
          ((r : ℝ) + 1) / (N : ℝ)
            =
          (r : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
        ring

      rw [hsplit] at hdiv

      have hyr :
          (r : ℝ) / (N : ℝ) + η / (A : ℝ)
            <
          (y : ℝ) / (N : ℝ) := by
        linarith

      have hfrac :
          (t.1 : ℝ) / (M : ℝ)
            <
          (y : ℝ) / (N : ℝ) :=
        lt_trans habove hyr

      have hreverse :
          N * t.1 < y * M := by
        have hraw :=
          (nat_fraction_lt_iff_cross t.1 M y N hMpos hNpos).mp
            hfrac
        simpa [Nat.mul_comm] using hraw

      have hnotcross :
          ¬ y * M < N * t.1 := by
        intro hcross
        omega

      constructor
      · intro h
        exact False.elim (hnotcross h)
      · intro h
        exact False.elim (hover h)

lemma alg1_trace_of_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (ψ : qs.State)
    (hψ : cfg.ValidState qs ψ) :
    ∃ _tr : Alg1Trace qs cfg ψ, True := by
  classical

  rcases good_input_expansion_of_valid qs cfg ψ hψ with
    ⟨support, inputCoeff, hinput, hgood⟩

  let zeroWork : Fin (ASize cfg.env.work) :=
    ⟨0, by simp[ASize]⟩

  let phaseCoeff :
      qs.Basis →
        Fin (ASize cfg.env.work) →
        ℂ :=
    fun b =>
      if hb :
          GoodModMulBasisInput
            qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b
      then
        if hz : alg1TargetResidue cfg b = 0 then
          fun t => if t = zeroWork then (1 : ℂ) else 0
        else
          Classical.choose
            (alg1_step1_ket_expansion qs cfg b hb)
      else
        fun _ => 0

  have hzero_support :
      ∀ b,
        GoodModMulBasisInput
            qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b →
        ∀ t,
          phaseCoeff b t ≠ 0 →
          alg1TargetResidue cfg b = 0 →
          t.1 = 0 := by
    intro b hb t hcoeff hz
    by_contra ht0

    have ht_ne : t ≠ zeroWork := by
      intro ht
      apply ht0
      have hval : t.1 = zeroWork.1 :=
        congrArg Fin.val ht
      simpa [zeroWork] using hval

    have hcoeff_zero : phaseCoeff b t = 0 := by
      simp [phaseCoeff, hb, hz, ht_ne]

    exact hcoeff hcoeff_zero

  have hphase :
      ∀ b,
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b →
        qs.eval
            (step1
              (Basis := qs.Basis)
              cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
            (qs.ket b)
          =
        ∑ t : Fin (ASize cfg.env.work),
          phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
    intro b hb
    by_cases hz : alg1TargetResidue cfg b = 0
    ·
      have hstep1 :
          qs.eval
              (step1
                (Basis := qs.Basis)
                cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
              (qs.ket b)
            =
          qs.ket b :=
        alg1_step1_zero_target_exact qs cfg b hb

      have hwrite0 :
          RegEncoding.writeNat cfg.env.work zeroWork.1 b = b := by
        change RegEncoding.writeNat cfg.env.work 0 b = b
        rw [← hb.2.2.1]
        exact RegEncoding.writeNat_toNat cfg.env.work b

      have hdelta :
          (∑ t : Fin (ASize cfg.env.work),
            (if t = zeroWork then (1 : ℂ) else 0) •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b))
            =
          qs.ket
            (RegEncoding.writeNat cfg.env.work zeroWork.1 b) := by
        rw [Finset.sum_eq_single zeroWork]
        · simp
        · intro t _ ht
          simp [ht]
        · simp

      calc
        qs.eval
            (step1
              (Basis := qs.Basis)
              cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
            (qs.ket b)
          =
          qs.ket b := hstep1

        _ =
          qs.ket
            (RegEncoding.writeNat cfg.env.work zeroWork.1 b) := by
              simp [hwrite0]

        _ =
          ∑ t : Fin (ASize cfg.env.work),
            (if t = zeroWork then (1 : ℂ) else 0) •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b) := hdelta.symm

        _ =
          ∑ t : Fin (ASize cfg.env.work),
            phaseCoeff b t •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b) := by
              apply Finset.sum_congr rfl
              intro t ht
              simp [phaseCoeff, hb, hz]

    ·
      simpa [phaseCoeff, hb, hz] using
        Classical.choose_spec
          (alg1_step1_ket_expansion qs cfg b hb)

  refine ⟨{
    support := support
    inputCoeff := inputCoeff
    phaseCoeff := phaseCoeff
    input_eq := hinput
    input_good := hgood

    step34_support := by
      intro b hbmem t ht hcoeff
      apply alg1_step4_cross_iff_overflow_of_good
        cfg b t (hgood b hbmem) ht
      intro hz
      exact
        hzero_support
          b
          (hgood b hbmem)
          t
          hcoeff
          hz

    full_step1_eq := ?_
  }, trivial⟩

  calc
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        ψ
      =
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        (∑ b ∈ support,
          inputCoeff b • qs.ket b) := by
        rw [hinput]

    _ =
    ∑ b ∈ support,
      qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        (inputCoeff b • qs.ket b) := by
        simpa using
          eval_finset_sum
            qs
            (step1
              (Basis := qs.Basis)
              cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
            support
            (fun b => inputCoeff b • qs.ket b)

    _ =
    ∑ b ∈ support,
      inputCoeff b •
        qs.eval
          (step1
            (Basis := qs.Basis)
            cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
          (qs.ket b) := by
        apply Finset.sum_congr rfl
        intro b hb
        simpa using
          qs.eval_smul
            (step1
              (Basis := qs.Basis)
              cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
            (inputCoeff b)
            (qs.ket b)

    _ =
    ∑ b ∈ support,
      inputCoeff b •
        ∑ t : Fin (ASize cfg.env.work),
          phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hphase b (hgood b hb)]

/--
Step 1: discard phase-estimation outcomes outside `alg1GoodLabels`.

This is the quantum phase-estimation tail estimate, lifted coherently to an
arbitrary valid superposition.
-/
lemma alg1_step1_good_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    (η : ℝ)
    (k5 : ℕ → ℕ → ℕ) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧
      ∀ (cfg : ModMulConfig η k5)
        (ψ : qs.State)
        (tr : Alg1Trace qs cfg ψ),
        cfg.ValidUnitState qs ψ →
        ‖ qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
            - tr.goodStep1‖
          ≤ stepErr K₁ η := by
  sorry

/--
Step 2: on good labels, replace multiplication by the approximate fraction
with exact addition of `alg1TargetResidue`.
-/
lemma alg1_step2_phase_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    (η : ℝ)
    (k5 : ℕ → ℕ → ℕ) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧
      ∀ (cfg : ModMulConfig η k5)
        (ψ : qs.State)
        (tr : Alg1Trace qs cfg ψ),
        cfg.ValidUnitState qs ψ →
        ‖ qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
              tr.goodStep1
            - tr.afterStep2Ref‖
          ≤ stepErr K₂ η := by
  sorry



lemma alg1_step3_reduces_to_modmul
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (b : QSemantics.Basis)
    (hb :
      GoodModMulBasisInput
        (inferInstance : QSemantics)
        cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    (if (alg1Overflow cfg b) then
      alg1Step2Value cfg b - cfg.env.N
    else
      alg1Step2Value cfg b)
      =
    alg1OutputValue cfg b := by
  sorry


/--
Steps 3 and 4 are exact on the Step-2 reference state.

This is where:
* `alg1_step3_reduces_to_modmul`,
* `alg1_step4_comparison_recovers_overflow`,
* register-locality lemmas for the primitive comparator/subtractor

are used.
-/
lemma alg1_step34_reference_exact
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [ModMulPrimitiveSemantics qs]
    {η : ℝ}
    {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
        tr.afterStep2Ref
      =
    tr.afterStep34Ref := by
  sorry

/--
Step 5: the inverse fractional load uncomputes the retained good estimate.

This uses `alg1_step5_inverse_residue`, plus the same discarded-tail
estimate as Step 1.
-/
lemma alg1_step5_cleanup_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (η : ℝ)
    (k5 : ℕ → ℕ → ℕ) :
    ∃ K₅ : ℝ, 0 ≤ K₅ ∧
      ∀ (cfg : ModMulConfig η k5)
        (ψ : qs.State)
        (tr : Alg1Trace qs cfg ψ),
        cfg.ValidUnitState qs ψ →
        ‖ qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
              tr.afterStep34Ref
            -
            qs.eval (ModMulConfig.idealGate cfg) ψ‖
          ≤ stepErr K₅ η := by
  sorry

lemma three_stepErr_le
    {K₁ K₂ K₅ η : ℝ}
    (hη : 0 ≤ η)
    (hK₁ : 0 ≤ K₁)
    (hK₂ : 0 ≤ K₂)
    (hK₅ : 0 ≤ K₅) :
    stepErr K₁ η + stepErr K₂ η + stepErr K₅ η
      ≤
    stepErr (3 * (K₁ + K₂ + K₅)) η := by
  sorry

lemma norm_chain_three
    {E : Type*}
    [NormedAddCommGroup E]
    (x₀ x₁ x₂ x₃ : E) :
    ‖x₀ - x₃‖
      ≤
    ‖x₀ - x₁‖
      + ‖x₁ - x₂‖
      + ‖x₂ - x₃‖ := by
  calc
    ‖x₀ - x₃‖
        =
      ‖(x₀ - x₁) + (x₁ - x₂) + (x₂ - x₃)‖ := by
        congr 1
        abel
    _ ≤
      ‖(x₀ - x₁) + (x₁ - x₂)‖ + ‖x₂ - x₃‖ := by
        simpa using
          norm_add_le
            ((x₀ - x₁) + (x₁ - x₂))
            (x₂ - x₃)
    _ ≤
      (‖x₀ - x₁‖ + ‖x₁ - x₂‖) + ‖x₂ - x₃‖ := by
        gcongr
        exact norm_add_le _ _
    _ =
      ‖x₀ - x₁‖ + ‖x₁ - x₂‖ + ‖x₂ - x₃‖ := by
        ring


theorem modMul_approx_valid_dist
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    [ModMulPrimitiveSemantics qs]
    (η : ℝ)
    (k5 : ℕ → ℕ → ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (cfg : ModMulConfig η k5) (ψ : qs.State),
        ModMulConfig.ValidUnitState qs cfg ψ →
        ‖qs.eval
            (ModMulConfig.approxGate (Basis := qs.Basis) cfg) ψ
          -
          qs.eval
            (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η := by

  rcases alg1_step1_good_bound qs η k5 with
    ⟨K₁, hK₁, hStep1⟩

  rcases alg1_step2_phase_bound qs η k5 with
    ⟨K₂, hK₂, hStep2⟩

  rcases alg1_step5_cleanup_bound qs η k5 with
    ⟨K₅, hK₅, hStep5⟩

  refine ⟨3 * (K₁ + K₂ + K₅), ?_, ?_⟩
  · nlinarith

  intro cfg ψ hψ
  rcases hψ with ⟨hValid, hNorm⟩

  have hη : 0 ≤ η :=
    le_of_lt cfg.env.precision.1

  rcases alg1_trace_of_valid qs cfg ψ hValid with
    ⟨tr, _⟩

  let U1 := ModMulConfig.U1 (Basis := qs.Basis) cfg
  let U2 := ModMulConfig.U2 (Basis := qs.Basis) cfg
  let U34 := ModMulConfig.U34 (Basis := qs.Basis) cfg
  let U5 := ModMulConfig.U5 (Basis := qs.Basis) cfg

  let post1 : Gate := U2 ;; U34 ;; U5
  let post2 : Gate := U34 ;; U5

  let ψ0 : qs.State :=
    qs.eval post1 (qs.eval U1 ψ)

  let ψ1 : qs.State :=
    qs.eval post1 tr.goodStep1

  let ψ2 : qs.State :=
    qs.eval post2 tr.afterStep2Ref

  let ψI : qs.State :=
    qs.eval (ModMulConfig.idealGate cfg) ψ

  have h1 :
      ‖ψ0 - ψ1‖ ≤ stepErr K₁ η := by
    have hIso :
        ‖ qs.eval post1 (qs.eval U1 ψ)
            - qs.eval post1 tr.goodStep1‖
          =
        ‖ qs.eval U1 ψ - tr.goodStep1‖ := by
      exact
        eval_isometry
          qs
          post1
          (by
            intro φ χ
            simpa using qs.inner_preserved post1 φ χ)
          (qs.eval U1 ψ)
          tr.goodStep1

    calc
      ‖ψ0 - ψ1‖
          =
        ‖qs.eval U1 ψ - tr.goodStep1‖ := by
          simpa [ψ0, ψ1] using hIso
      _ ≤ stepErr K₁ η := by
          simpa [U1] using hStep1 cfg ψ tr ⟨hValid, hNorm⟩

  have h2 :
      ‖ψ1 - ψ2‖ ≤ stepErr K₂ η := by
    have hIso :
        ‖ qs.eval post2
              (qs.eval U2 tr.goodStep1)
            -
            qs.eval post2 tr.afterStep2Ref‖
          =
        ‖ qs.eval U2 tr.goodStep1
            - tr.afterStep2Ref‖ := by
      exact
        eval_isometry
          qs
          post2
          (by
            intro φ χ
            simpa using qs.inner_preserved post2 φ χ)
          (qs.eval U2 tr.goodStep1)
          tr.afterStep2Ref

    calc
      ‖ψ1 - ψ2‖
          =
        ‖ qs.eval post2
              (qs.eval U2 tr.goodStep1)
            -
            qs.eval post2 tr.afterStep2Ref‖ := by
          simp [ψ1, ψ2, post1, post2, qs.eval_seq]
      _ =
        ‖ qs.eval U2 tr.goodStep1
            - tr.afterStep2Ref‖ := hIso
      _ ≤ stepErr K₂ η := by
          simpa [U2] using hStep2 cfg ψ tr ⟨hValid, hNorm⟩

  have h34 :
      qs.eval U34 tr.afterStep2Ref
        =
      tr.afterStep34Ref := by
    simpa [U34] using
      alg1_step34_reference_exact qs cfg ψ tr

  have h3 :
      ‖ψ2 - ψI‖ ≤ stepErr K₅ η := by
    calc
      ‖ψ2 - ψI‖
          =
        ‖ qs.eval U5 tr.afterStep34Ref
            -
            qs.eval (ModMulConfig.idealGate cfg) ψ‖ := by
          simp [ψ2, ψI, post2, qs.eval_seq, h34]
      _ ≤ stepErr K₅ η := by
          simpa [U5] using hStep5 cfg ψ tr ⟨hValid, hNorm⟩

  have hChain :
      ‖ψ0 - ψI‖
        ≤
      stepErr K₁ η
        + stepErr K₂ η
        + stepErr K₅ η := by
    calc
      ‖ψ0 - ψI‖
          ≤ ‖ψ0 - ψ1‖ + ‖ψ1 - ψ2‖ + ‖ψ2 - ψI‖ :=
            norm_chain_three ψ0 ψ1 ψ2 ψI
      _ ≤
        stepErr K₁ η
          + stepErr K₂ η
          + stepErr K₅ η := by
            gcongr

  have hBudget :
      stepErr K₁ η + stepErr K₂ η + stepErr K₅ η
        ≤
      stepErr (3 * (K₁ + K₂ + K₅)) η :=
    three_stepErr_le hη hK₁ hK₂ hK₅

  have hCore :
      qs.eval
          (ModMulConfig.approxGate (Basis := qs.Basis) cfg)
          ψ
        =
      ψ0 := by
    rw [ModMulConfig.eval_approxGate_eq_staged qs cfg ψ]
    simp [
      ModMulConfig.stagedGate,
      ψ0,
      post1,
      U1,
      U2,
      U34,
      U5,
      qs.eval_seq
    ]

  calc
    ‖qs.eval
        (ModMulConfig.approxGate (Basis := qs.Basis) cfg) ψ
      -
      qs.eval (ModMulConfig.idealGate cfg) ψ‖
        =
      ‖ψ0 - ψI‖ := by
        rw [hCore]
    _ ≤
      stepErr K₁ η
        + stepErr K₂ η
        + stepErr K₅ η := hChain
    _ ≤
      stepErr (3 * (K₁ + K₂ + K₅)) η := hBudget
/--
A convenient constructor for the coprimality portion of
`ModExpTailArithmeticOK`.

The remaining `Step5ConstantOK` portion is supplied separately because it
depends on the chosen classical implementation of `k5`.
-/
theorem modExp_tail_coprime
    (a N : ℕ) (x : Reg) (q n : ℕ)
    (hcoprime : Nat.Coprime a N) :
    ∀ j : ℕ, j < n →
      Nat.Coprime (a ^ (2 ^ ((q + j) - x.lo)) % N) N := by
  intro j _hj
  exact modExp_multiplier_coprime
    a N ((q + j) - x.lo) hcoprime

/-! =========================================================
    Tail side-condition reindexing
========================================================= -/

lemma modExpTailLayout_tail
    (x data work : Reg) (flag q n : ℕ)
    (h : ModExpTailLayout x data work flag q (n + 1)) :
    ModExpTailLayout x data work flag (q + 1) n := by
  rcases h with ⟨hxq, hqhi, hctrl⟩
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · intro j hj
    have h' := hctrl (j + 1) (by omega)
    have hq :
        q + (j + 1) = (q + 1) + j := by
      omega
    simpa [hq] using h'

lemma modExpTailArithmeticOK_tail
    (a N : ℕ) (x : Reg) (k5 : ℕ → ℕ → ℕ)
    (q n : ℕ)
    (h : ModExpTailArithmeticOK a N x k5 q (n + 1)) :
    ModExpTailArithmeticOK a N x k5 (q + 1) n := by
  intro j hj
  have h' := h (j + 1) (by omega)
  dsimp at h' ⊢
  have hq :
      q + (j + 1) = (q + 1) + j := by
    omega
  simpa [hq] using h'

/--
The ideal controlled multiplication preserves the valid modular-input
subspace described by this configuration.
-/
theorem ideal_preserves_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    {k5 : ℕ → ℕ → ℕ}
    (cfg : ModMulConfig η k5)
    (ψ : qs.State)
    (hψ : cfg.ValidState qs ψ) :
    cfg.ValidState qs
      (qs.eval (ModMulConfig.idealGate cfg) ψ) := by
  simpa [ModMulConfig.ValidState, ModMulConfig.idealGate] using
    (idealCtrlModMul_preserves_valid
      qs
      cfg.c
      cfg.env.N
      cfg.env.data
      cfg.env.work
      cfg.flag
      cfg.ctrl
      cfg.env.modulus_gt_one
      cfg.env.data_capacity
      cfg.coprime
      cfg.layout
      ψ
      hψ)

/-! =========================================================
    Hybrid bound for a tail of modular exponentiation
========================================================= -/

theorem modExpApproxSteps_valid_dist
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    [GateSemanticsFacts qs]
    [ModMulPrimitiveSemantics qs]
    (η : ℝ)
    (k5 : ℕ → ℕ → ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (a N : ℕ) (x data work : Reg) (flag q n : ℕ) (ψ : qs.State),
        1 < N →
        N ≤ ASize data →
        Algorithm1Precision η data work →
        ModExpTailLayout x data work flag q n →
        ModExpTailArithmeticOK a N x k5 q n →
        ψ ∈ ValidModMulState qs N data work flag →
        ‖ψ‖ = 1 →
        ‖
          qs.eval
            (modExpApproxStepsValid
              (Basis := qs.Basis)
              k5 a N x data work flag q n)
            ψ
          -
          qs.eval
            (modExpIdealSteps qs a N x data q n)
            ψ‖
          ≤ (n : ℝ) * stepErr K η := by
  rcases modMul_approx_valid_dist (qs := qs) η k5 with
    ⟨K, hK_nonneg, hmodMul⟩

  refine ⟨K, hK_nonneg, ?_⟩
  intro a N x data work flag q n ψ
    hN hsize hprecision hLayout hArithmetic hValid hNorm

  revert q ψ
  induction n with
  | zero =>
      intro q ψ hLayout hArithmetic hValid hNorm
      simp [modExpApproxStepsValid, modExpIdealSteps, qs.eval_id]

  | succ n ih =>
      intro q ψ hLayout hArithmetic hValid hNorm

      have hTailLayout :
          ModExpTailLayout x data work flag (q + 1) n :=
        modExpTailLayout_tail x data work flag q n hLayout

      have hTailArithmetic :
          ModExpTailArithmeticOK a N x k5 (q + 1) n :=
        modExpTailArithmeticOK_tail a N x k5 q n hArithmetic

      rcases hLayout with ⟨hxq, hqhi, hControls⟩

      let e : ℕ := q - x.lo
      let c : ℕ := (a ^ (2 ^ e)) % N

      have hHeadLayout :
          ModMulCoreLayout data work flag q :=
        hControls 0 (by omega)

      have hHeadArithmetic :
          Nat.Coprime c N ∧
            Step5ConstantOK c N (k5 c N) := by
        have h0 := hArithmetic 0 (by omega)
        simpa [c, e] using h0

      let headEnv : Algorithm1Env η :=
        { N := N
          data := data
          work := work
          modulus_gt_one := hN
          data_capacity := hsize
          precision := hprecision }

      let headCfg : ModMulConfig η k5 :=
        { env := headEnv
          c := c
          flag := flag
          ctrl := q
          coprime := hHeadArithmetic.1
          step5_ok := hHeadArithmetic.2
          layout := hHeadLayout }

      let A : Gate :=
        CmodMulInPlaceCore
          (Basis := qs.Basis)
          c N (k5 c N) q data work flag

      let I : Gate :=
        Spec.idealCtrlModMul c N data q

      let RA : Gate :=
        modExpApproxStepsValid
          (Basis := qs.Basis)
          k5 a N x data work flag (q + 1) n

      let RI : Gate :=
        modExpIdealSteps qs a N x data (q + 1) n

      have hApprox :
          modExpApproxStepsValid
              (Basis := qs.Basis)
              k5 a N x data work flag q (n + 1)
            =
          A ;; RA := by
        simp [modExpApproxStepsValid, A, RA, c, e]

      have hIdeal :
          modExpIdealSteps qs a N x data q (n + 1)
            =
          I ;; RI := by
        simp [modExpIdealSteps, I, RI, c, e]

      let ψA0 : qs.State := qs.eval A ψ
      let ψI0 : qs.State := qs.eval I ψ

      have hHeadValid :
          ModMulConfig.ValidState qs headCfg ψ := by
        simpa [
          ModMulConfig.ValidState,
          headCfg,
          headEnv
        ] using hValid

      have hHeadUnit :
          ModMulConfig.ValidUnitState qs headCfg ψ :=
        ⟨hHeadValid, hNorm⟩

      have hHead :
          ‖ψA0 - ψI0‖ ≤ stepErr K η := by
        simpa [
          ψA0,
          ψI0,
          A,
          I,
          ModMulConfig.approxGate,
          ModMulConfig.idealGate,
          headCfg,
          headEnv
        ] using
          (hmodMul headCfg ψ hHeadUnit)

      have hψI0Norm : ‖ψI0‖ = 1 := by
        calc
          ‖ψI0‖ = ‖ψ‖ := by
            simpa [ψI0] using
              (eval_norm_preserved qs I ψ)
          _ = 1 := hNorm

      have hψI0ValidCfg :
          ModMulConfig.ValidState qs headCfg ψI0 := by
        simpa [
          ψI0,
          I,
          ModMulConfig.idealGate,
          headCfg,
          headEnv
        ] using
          (ideal_preserves_valid qs headCfg ψ hHeadValid)

      have hψI0Valid :
          ψI0 ∈ ValidModMulState qs N data work flag := by
        simpa [
          ModMulConfig.ValidState,
          headCfg,
          headEnv
        ] using hψI0ValidCfg

      have hTail :
          ‖qs.eval RA ψI0 - qs.eval RI ψI0‖
            ≤ (n : ℝ) * stepErr K η := by
        have h :=
          ih
            (q := q + 1)
            (ψ := ψI0)
            hTailLayout
            hTailArithmetic
            hψI0Valid
            hψI0Norm
        simpa [RA, RI] using h

      have hIso :
          ‖qs.eval RA ψA0 - qs.eval RA ψI0‖
            =
          ‖ψA0 - ψI0‖ := by
        exact
          eval_isometry
            qs
            RA
            (by
              intro φ χ
              simpa using qs.inner_preserved RA φ χ)
            ψA0
            ψI0

      have hTriangle :
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
            ≤
          ‖qs.eval RA ψA0 - qs.eval RA ψI0‖
            +
          ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
        rw [
          show
            qs.eval RA ψA0 - qs.eval RI ψI0
              =
            (qs.eval RA ψA0 - qs.eval RA ψI0)
              +
            (qs.eval RA ψI0 - qs.eval RI ψI0)
          by abel
        ]
        exact norm_add_le _ _

      have hMain :
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
            ≤ ((n + 1 : ℕ) : ℝ) * stepErr K η := by
        calc
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
              ≤
            ‖qs.eval RA ψA0 - qs.eval RA ψI0‖
              +
            ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := hTriangle
          _ =
            ‖ψA0 - ψI0‖
              +
            ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
              rw [hIso]
          _ ≤
            stepErr K η
              +
            (n : ℝ) * stepErr K η := by
              exact add_le_add hHead hTail
          _ =
            ((n + 1 : ℕ) : ℝ) * stepErr K η := by
              push_cast
              ring

      simpa [
        hApprox,
        hIdeal,
        ψA0,
        ψI0,
        qs.eval_seq
      ] using hMain


structure ModExpConfig (η : ℝ) (k5 : ℕ → ℕ → ℕ) where
  env : Algorithm1Env η

  a : ℕ
  x : Reg
  flag : ℕ

  layout :
    ModExpLayout x env.data env.work flag

  arithmetic :
    ModExpArithmeticOK a env.N x k5


structure ModExpTailConfig (η : ℝ) (k5 : ℕ → ℕ → ℕ) where
  env : Algorithm1Env η

  a : ℕ
  x : Reg
  flag : ℕ

  q     : ℕ
  steps : ℕ

  layout :
    ModExpTailLayout x env.data env.work flag q steps

  arithmetic :
    ModExpTailArithmeticOK a env.N x k5 q steps

namespace ModExpConfig

def toTail
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModExpConfig η k5) :
    ModExpTailConfig η k5 :=
  { env := cfg.env
    a := cfg.a
    x := cfg.x
    flag := cfg.flag
    q := cfg.x.lo
    steps := tbits cfg.x
    layout := by
      simpa [ModExpLayout] using cfg.layout
    arithmetic := by
      simpa [ModExpArithmeticOK] using cfg.arithmetic }

noncomputable def approxGate
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (cfg : ModExpConfig η k5) : Gate :=
  modExpApproxValid
    (Basis := Basis)
    k5 cfg.a cfg.env.N cfg.x cfg.env.data cfg.env.work cfg.flag

def idealGate
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModExpConfig η k5) : Gate :=
  modExpIdeal' qs cfg.a cfg.env.N cfg.x cfg.env.data

def ValidUnitState
    (qs : QSemantics) [RegEncoding qs.Basis]
    {η : ℝ} {k5 : ℕ → ℕ → ℕ}
    (cfg : ModExpConfig η k5) (ψ : qs.State) : Prop :=
  ψ ∈ ValidModMulState
      qs cfg.env.N cfg.env.data cfg.env.work cfg.flag
    ∧ ‖ψ‖ = 1

end ModExpConfig

/-! =========================================================
    Final approximation theorem for complete modular exponentiation
========================================================= -/

theorem modExpApprox_valid_dist
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    [GateSemanticsFacts qs]
    [ModMulPrimitiveSemantics qs]
    (η : ℝ)
    (k5 : ℕ → ℕ → ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (cfg : ModExpConfig η k5) (ψ : qs.State),
        ModExpConfig.ValidUnitState qs cfg ψ →
        ‖ qs.eval
            (ModExpConfig.approxGate
              (Basis := qs.Basis) cfg) ψ
          -
          qs.eval
            (ModExpConfig.idealGate qs cfg) ψ‖
        ≤ (tbits cfg.x : ℝ) * stepErr K η := by
  rcases modExpApproxSteps_valid_dist (qs := qs) η k5 with
    ⟨K, hK_nonneg, hSteps⟩

  refine ⟨K, hK_nonneg, ?_⟩
  intro cfg ψ hψ
  rcases hψ with ⟨hValid, hNorm⟩

  have hTailLayout :
      ModExpTailLayout
        cfg.x
        cfg.env.data
        cfg.env.work
        cfg.flag
        cfg.x.lo
        (tbits cfg.x) := by
    simpa [ModExpLayout] using cfg.layout

  have hTailArithmetic :
      ModExpTailArithmeticOK
        cfg.a
        cfg.env.N
        cfg.x
        k5
        cfg.x.lo
        (tbits cfg.x) := by
    simpa [ModExpArithmeticOK] using cfg.arithmetic

  have h :=
    hSteps
      cfg.a
      cfg.env.N
      cfg.x
      cfg.env.data
      cfg.env.work
      cfg.flag
      cfg.x.lo
      (tbits cfg.x)
      ψ
      cfg.env.modulus_gt_one
      cfg.env.data_capacity
      cfg.env.precision
      hTailLayout
      hTailArithmetic
      hValid
      hNorm

  simpa [
    ModExpConfig.approxGate,
    ModExpConfig.idealGate,
    modExpApproxValid,
    modExpIdeal'
  ] using h
