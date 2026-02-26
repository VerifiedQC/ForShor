import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

universe u
namespace Shor

structure Reg where
  lo : ℕ
  hi : ℕ

class RegEncoding (Basis : Type u) where
  toNat    : Reg → Basis → ℕ
  writeNat : Reg → ℕ → Basis → Basis
  bit      : ℕ → Basis → Bool
  toNat_writeNat : ∀ r v b, toNat r (writeNat r v b) = v
  writeNat_toNat : ∀ r b, writeNat r (toNat r b) b = b

namespace Reg
variable {Basis : Type u} [RegEncoding Basis]
def toInt (r : Reg) (b : Basis) : ℕ := RegEncoding.toNat r b
def writeInt (r : Reg) (v : ℕ) (b : Basis) : Basis := RegEncoding.writeNat r v b
end Reg

/--
Gate language.
-/
inductive Gate : Type
  | id : Gate
  | seq : Gate → Gate → Gate
  | adj : Gate → Gate
  | H : ℕ → Gate
  | X : ℕ → Gate
  | QFT : Reg → Gate
  | PhaseProd  : (phi : Real) → (x z : Reg) → Gate
  | CPhaseProd : (ctrl : ℕ) → (phi : Real) → (x z : Reg) → Gate
  | Prim : String → List ℕ → Gate

namespace Gate
infixr:80 " ;; " => Gate.seq
prefix:90 "†" => Gate.adj
end Gate

/--
Abstract quantum semantics.
-/
class QSemantics where
  Basis : Type u
  State : Type u

  [instNormed : NormedAddCommGroup State]
  [instIP     : InnerProductSpace ℂ State]

  ket   : Basis → State
  eval  : Gate → State → State

  eval_id  : ∀ ψ, eval Gate.id ψ = ψ
  eval_seq : ∀ U V ψ, eval (U ;; V) ψ = eval V (eval U ψ)

  inner_preserved : ∀ U ψ φ, inner ℂ (eval U ψ) (eval U φ) = inner ℂ ψ φ

  eval_zero : ∀ U, eval U 0 = 0
  eval_add  : ∀ U ψ φ, eval U (ψ + φ) = eval U ψ + eval U φ
  eval_smul : ∀ U (a : ℂ) ψ, eval U (a • ψ) = a • eval U ψ

  hsub : ∀ U ψ φ, eval U (ψ - φ) = eval U ψ - eval U φ

open QSemantics
attribute [instance] QSemantics.instNormed
attribute [instance] QSemantics.instIP

/-- A convenient lemma: `eval U` is an isometry if it preserves inner products. -/
lemma eval_isometry
  (qs : QSemantics)
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
  (qs : QSemantics) (U V : Gate) (ψ : qs.State) :
  qs.eval (U ;; V) ψ = qs.eval V (qs.eval U ψ) := by
  simpa using (qs.eval_seq U V ψ)

lemma eval_norm_preserved (qs : QSemantics) (U : Gate) (ψ : qs.State) :
  ‖qs.eval U ψ‖ = ‖ψ‖ := by
  have h := eval_isometry qs U (by intro ψ φ; simpa using qs.inner_preserved U ψ φ) ψ 0
  simpa [qs.eval_zero U] using h

/-- Overlap error invariance under a common post-gate. -/
lemma overlap_err_invariant
  (qs : QSemantics) (W : Gate) (ψ φ : qs.State) :
    ‖ (1 : ℂ) - inner ℂ (qs.eval W ψ) (qs.eval W φ)‖
      =
    ‖ (1 : ℂ) - inner ℂ ψ φ‖ := by
  simp [qs.inner_preserved W ψ φ]

/-- `‖1 - inner ψ φ‖ ≤ ‖ψ - φ‖` when `‖ψ‖=1`. -/
lemma overlap_le_dist
  (qs : QSemantics) (ψ φ : qs.State) :
  ‖ψ‖ = 1 →
  ‖ (1 : ℂ) - inner ℂ ψ φ‖ ≤ ‖ψ - φ‖ := by
  intro hψ
  have hψψ : inner ℂ ψ ψ = (1 : ℂ) := by
    simp [hψ]
  have h1 : (1 : ℂ) = inner ℂ ψ ψ := by
    simpa using hψψ.symm

  calc
    ‖ (1 : ℂ) - inner ℂ ψ φ‖
        = ‖ inner ℂ ψ ψ - inner ℂ ψ φ‖ := by simp [h1]
    _   = ‖ inner ℂ ψ (ψ - φ)‖ := by
            simp [inner_sub_right]
    _   ≤ ‖ψ‖ * ‖ψ - φ‖ := by
            simpa using (norm_inner_le_norm ψ (ψ - φ))
    _   = ‖ψ - φ‖ := by simp [hψ]

/-- distance ≤ sqrt(2 * overlap error) for unit vectors. -/
lemma dist_le_sqrt_two_mul_overlap
  (qs : QSemantics) (ψ φ : qs.State) :
  ‖ψ‖ = 1 → ‖φ‖ = 1 →
  ‖ψ - φ‖ ≤ Real.sqrt (2 * ‖(1 : ℂ) - inner ℂ ψ φ‖) := by
  intro hψ hφ
  have hmain : ‖ψ - φ‖ ^ 2 ≤ 2 * ‖(1 : ℂ) - inner ℂ ψ φ‖ := by
    have hnormsub :
        ‖ψ - φ‖ ^ 2
          = ‖ψ‖ ^ 2 + ‖φ‖ ^ 2 - 2 * Complex.re (inner ℂ ψ φ) := by
      have := (norm_sub_sq (𝕜 := ℂ) ψ φ)
      simp_all only [one_pow, RCLike.re_to_complex]
      ring
    have hnorms : ‖ψ‖ ^ 2 + ‖φ‖ ^ 2 = (2 : ℝ) := by
      simp [hψ, hφ]
      ring
    have hnormsub' :
        ‖ψ - φ‖ ^ 2 = (2 : ℝ) - 2 * Complex.re (inner ℂ ψ φ) := by
      simpa [hnorms] using hnormsub

    have hre :
        (1 - Complex.re (inner ℂ ψ φ)) ≤ ‖(1 : ℂ) - inner ℂ ψ φ‖ := by
      have h : Complex.re ((1 : ℂ) - inner ℂ ψ φ) ≤ ‖(1 : ℂ) - inner ℂ ψ φ‖ := by
        simpa using (Complex.re_le_norm ((1 : ℂ) - inner ℂ ψ φ))
      -- expand `re(1 - z) = 1 - re(z)`
      simpa [Complex.sub_re, Complex.one_re] using h

    calc
      ‖ψ - φ‖ ^ 2
          = 2 * (1 - Complex.re (inner ℂ ψ φ)) := by
              have : (2 : ℝ) - 2 * Complex.re (inner ℂ ψ φ)
                      = 2 * (1 - Complex.re (inner ℂ ψ φ)) := by ring
              simp [hnormsub', this]
      _   ≤ 2 * ‖(1 : ℂ) - inner ℂ ψ φ‖ := by
              have h2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
              exact mul_le_mul_of_nonneg_left hre h2

  apply Real.le_sqrt_of_sq_le
  exact hmain

/-- A Spec is relative to a given semantics instance. -/
class Spec (qs : QSemantics) [RegEncoding qs.Basis] where
  idealModMul     : (c N : ℕ) → (x : Reg) → Gate
  idealCtrlModMul : (c N : ℕ) → (x : Reg) → (ctrl : ℕ) → Gate

open QSemantics
open Gate




------------------------------------------------------------------------------------
--Defining Modular multiplication and exponentiation
------------------------------------------------------------------------------------


/-- Register length (#qubits) as a Nat. -/
def regSize (r : Reg) : ℕ := r.hi - r.lo

def IQFT (r : Reg) : Gate := †(Gate.QFT r)
def extendHi (r : Reg) : Reg := ⟨r.lo, r.hi + 1⟩

def regQubits (r : Reg) : List ℕ :=
  (List.range (regSize r)).map (fun k => r.lo + k)

def H_reg (r : Reg) : Gate :=
  (regQubits r).foldl (fun acc q => (Gate.H q) ;; acc) Gate.id

def PrimN (tag : String) (args : List ℕ) : Gate := Gate.Prim tag args

noncomputable def step1 (c N : ℕ) (ctrl:ℕ) (x_reg w_reg : Reg) : Gate :=
  let phi : ℝ := (2 * Real.pi * ((c + N - 1) % N)) / (N : ℝ)
  (IQFT w_reg) ;;
  (Gate.CPhaseProd ctrl phi x_reg w_reg) ;;
  (H_reg w_reg)

noncomputable def step2 (N : ℕ) (x_reg w_reg : Reg) : (Reg × Gate) :=
  let x_ext : Reg := extendHi x_reg
  let n1 : ℕ := regSize x_ext
  let m  : ℕ := regSize w_reg
  let phi : ℝ := (2 * Real.pi * (N : ℝ)) / ((2 : ℝ) ^ (m + n1))
  (x_ext,
    (IQFT x_ext) ;;
    (Gate.PhaseProd phi w_reg x_ext) ;;
    (Gate.QFT x_ext))

def step3 (N : ℕ) (x_ext : Reg) (flag : ℕ) : Gate :=
  (PrimN "CMP_GE_CONST" [x_ext.lo, x_ext.hi, N, flag]) ;;
  (PrimN "CSUB_CONST"   [flag, x_ext.lo, x_ext.hi, N])

def step4 (N : ℕ) (x_ext w_reg : Reg) (flag : ℕ) : Gate :=
  PrimN "CMP_LT_NW" [x_ext.lo, x_ext.hi, w_reg.lo, w_reg.hi, N, flag]

noncomputable def frac_load (k N : ℕ) (ctrl:ℕ) (x_reg w_reg : Reg) : Gate :=
  let phi : ℝ := (2 * Real.pi * ((k % N) : ℝ)) / (N : ℝ)
  (IQFT w_reg) ;;
  (Gate.CPhaseProd ctrl phi x_reg w_reg) ;;
  (QFT w_reg)

/-- Step 5: uncompute w using the provided k5 = (1 - c^{-1}) mod N. -/
noncomputable def step5 (k5 N : ℕ) (ctrl:ℕ) (x_ext w_reg : Reg) : Gate :=
  †(frac_load k5 N ctrl x_ext w_reg)

/--
In-place mod-mul circuit
-/
noncomputable def CmodMulInPlaceCore
  (c N k5 : ℕ) (ctrl: ℕ) (x_reg w_reg : Reg) (flag : ℕ)  : Gate :=
  let U1 : Gate := step1 c N ctrl x_reg w_reg
  let (x_ext, U2) := step2 N x_reg w_reg
  let U3 : Gate := step3 N x_ext flag
  let U4 : Gate := step4 N x_ext w_reg flag
  let U5 : Gate := step5 k5 N ctrl x_ext w_reg
  U5 ;; U4 ;; U3 ;; U2 ;; U1

/-- Final function for in-place mod mul -/
noncomputable def CmodMulInPlace
  (base n m c N k5 ctrl: ℕ) : Gate :=
  let x_reg : Reg := ⟨base, base + n⟩
  let w_reg : Reg := ⟨base + n + 1, base + n + m + 1⟩
  let flag  : ℕ := base + n + m + 1
  CmodMulInPlaceCore c N ctrl k5 x_reg w_reg flag



class ModMul (qs : QSemantics) [RegEncoding qs.Basis] [Spec qs] where
  η : ℝ
  η_nonneg : 0 ≤ η

  k5 : ℕ → ℕ → ℕ

  theorem1_ctrl_gen :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (c N : ℕ) (x_reg w_reg : Reg) (flag ctrl : ℕ) (ψ : qs.State),
        ‖ (1 : ℂ) - inner ℂ
            (qs.eval (CmodMulInPlaceCore c N (k5 c N) ctrl x_reg w_reg flag) ψ)
            (qs.eval (Spec.idealCtrlModMul (qs := qs) c N x_reg ctrl) ψ)‖
        ≤ K * η



-- helper: number of control qubits = x.hi - x.lo
def tbits (x : Reg) : ℕ := x.hi - x.lo

/-- Ideal modexp as a sequence of ideal controlled modmuls. -/
def modExpIdealSteps (qs : QSemantics) [RegEncoding qs.Basis] [Spec qs]
    (a N : ℕ) (x y : Reg) : ℕ → ℕ → Gate
  | _q, 0     => Gate.id
  | q, n+1   =>
      let k : ℕ := q - x.lo
      (Spec.idealCtrlModMul (qs := qs) ((a ^ (2 ^ k)) % N) N y q) ;;
      modExpIdealSteps qs a N x y (q+1) n

def modExpIdeal' (qs : QSemantics) [RegEncoding qs.Basis] [Spec qs]
    (a N : ℕ) (x y : Reg) : Gate :=
  modExpIdealSteps qs a N x y x.lo (tbits x)

/-- Approximate modexp uses the *concrete* in-place circuit each step. -/
noncomputable def modExpApproxSteps (qs : QSemantics) [RegEncoding qs.Basis] [Spec qs] [ModMul qs]
    (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) : ℕ → ℕ → Gate
  | _q, 0     => Gate.id
  | q, n+1   =>
      let k : ℕ := q - x.lo
      let c : ℕ := ((a ^ (2 ^ k)) % N)
      (CmodMulInPlaceCore c N (ModMul.k5 (qs := qs) c N) q y w_reg flag) ;;
      modExpApproxSteps qs a N x y w_reg flag (q+1) n

noncomputable def modExpApprox' (qs : QSemantics) [RegEncoding qs.Basis] [Spec qs] [ModMul qs]
    (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) : Gate :=
  modExpApproxSteps qs a N x y w_reg flag x.lo (tbits x)

noncomputable def stepErr (K η : ℝ) : ℝ := Real.sqrt (2 * (K * η))

lemma ctrlMul_step_dist_bound
  (qs : QSemantics) [RegEncoding qs.Basis] [Spec qs] [ModMul qs] :
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c N : ℕ) (x_reg w_reg : Reg) (flag ctrl : ℕ) (ψ : qs.State),
      ‖ψ‖ = 1 →
      ‖ qs.eval (CmodMulInPlaceCore c N (ModMul.k5 (qs := qs) c N) ctrl x_reg w_reg flag) ψ
        - qs.eval (Spec.idealCtrlModMul (qs := qs) c N x_reg ctrl) ψ‖
      ≤ stepErr K (ModMul.η (qs := qs)) :=
by
  rcases ModMul.theorem1_ctrl_gen (qs := qs) with ⟨K, K_nonneg, hK⟩
  refine ⟨K, K_nonneg, ?_⟩
  intro c N x_reg w_reg flag ctrl ψ hψ

  set ψA : qs.State :=
    qs.eval (CmodMulInPlaceCore c N (ModMul.k5 (qs := qs) c N) ctrl x_reg w_reg flag) ψ
  set ψI : qs.State :=
    qs.eval (Spec.idealCtrlModMul (qs := qs) c N x_reg ctrl) ψ

  have hψA : ‖ψA‖ = 1 := by
    simpa [ψA, hψ] using
      (eval_norm_preserved (qs := qs)
        (CmodMulInPlaceCore c N (ModMul.k5 (qs := qs) c N) ctrl x_reg w_reg flag) ψ)

  have hψI : ‖ψI‖ = 1 := by
    simpa [ψI, hψ] using
      (eval_norm_preserved (qs := qs)
        (Spec.idealCtrlModMul (qs := qs) c N x_reg ctrl) ψ)

  have hdist :
      ‖ψA - ψI‖ ≤ Real.sqrt (2 * ‖(1 : ℂ) - inner ℂ ψA ψI‖) :=
    dist_le_sqrt_two_mul_overlap (qs := qs) ψA ψI hψA hψI

  have hov :
      ‖(1 : ℂ) - inner ℂ ψA ψI‖ ≤ K * ModMul.η (qs := qs) := by
    simpa [ψA, ψI] using (hK c N x_reg w_reg flag ctrl ψ)

  have hsqrt :
      Real.sqrt (2 * ‖(1 : ℂ) - inner ℂ ψA ψI‖)
      ≤ Real.sqrt (2 * (K * ModMul.η (qs := qs))) := by
    have hmul :
        2 * ‖(1 : ℂ) - inner ℂ ψA ψI‖ ≤ 2 * (K * ModMul.η (qs := qs)) := by
      have : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      exact mul_le_mul_of_nonneg_left hov this
    exact Real.sqrt_le_sqrt hmul

  have : ‖ψA - ψI‖ ≤ Real.sqrt (2 * (K * ModMul.η (qs := qs))) :=
    le_trans hdist hsqrt

  simpa [ψA, ψI, stepErr] using this

theorem modExpSteps_dist_bound
  (qs : QSemantics) [RegEncoding qs.Basis] [Spec qs] [ModMul qs] :
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) (q n : ℕ) (ψ : qs.State),
      ‖ψ‖ = 1 →
      ‖ qs.eval (modExpApproxSteps (qs := qs) a N x y w_reg flag q n) ψ
        - qs.eval (modExpIdealSteps  (qs := qs) a N x y q n) ψ‖
      ≤ (n : ℝ) * stepErr K (ModMul.η (qs := qs)) :=
by
  rcases ctrlMul_step_dist_bound (qs := qs) with ⟨K, K_nonneg, hstep⟩
  refine ⟨K, K_nonneg, ?_⟩
  intro a N x y w_reg flag q n ψ hψ
  revert q ψ
  induction n with
  | zero =>
      intro q ψ hψ
      simp [modExpApproxSteps, modExpIdealSteps, qs.eval_id]
    | succ n ih =>
      intro q ψ hψ
      set k : ℕ := q - x.lo with hk
      set c : ℕ := ((a ^ (2 ^ k)) % N) with hc

      set A : Gate := CmodMulInPlaceCore c N (ModMul.k5 (qs := qs) c N) q y w_reg flag with hA
      set I : Gate := Spec.idealCtrlModMul (qs := qs) c N y q with hI
      set RA : Gate := modExpApproxSteps (qs := qs) a N x y w_reg flag (q+1) n with hRA
      set RI : Gate := modExpIdealSteps  (qs := qs) a N x y (q+1) n with hRI

      have hApprox :
        modExpApproxSteps (qs := qs) a N x y w_reg flag q (n+1) = A ;; RA := by
        simp [modExpApproxSteps, hk, hc, hA, hRA]

      have hIdeal :
        modExpIdealSteps (qs := qs) a N x y q (n+1) = I ;; RI := by
        simp [modExpIdealSteps, hk, hc, hI, hRI]

      -- states *after the head gate*
      set ψA0 : qs.State := qs.eval A ψ
      set ψI0 : qs.State := qs.eval I ψ

      have hψA0_unit : ‖ψA0‖ = 1 := by
        simpa [ψA0, hψ] using (eval_norm_preserved (qs := qs) A ψ)

      have hψI0_unit : ‖ψI0‖ = 1 := by
        simpa [ψI0, hψ] using (eval_norm_preserved (qs := qs) I ψ)

      -- head error: A vs I on the same input ψ
      have h_head :
        ‖ψA0 - ψI0‖ ≤ stepErr K (ModMul.η (qs := qs)) := by
        have := hstep c N y w_reg flag q ψ hψ
        simpa [ψA0, ψI0, hA, hI] using this

      -- IH applied to the *same* input ψI0 (important!)
      have h_tail :
        ‖ qs.eval RA ψI0 - qs.eval RI ψI0‖
          ≤ (n : ℝ) * stepErr K (ModMul.η (qs := qs)) := by

        have := ih (q := q+1) (ψ := ψI0) hψI0_unit
        simpa [hRA, hRI] using this

      have h_iso_RA :
        ‖ qs.eval RA ψA0 - qs.eval RA ψI0‖ = ‖ ψA0 - ψI0‖ := by
        simpa using
          (eval_isometry qs RA
            (by intro ψ φ; simpa using qs.inner_preserved RA ψ φ) ψA0 ψI0)
      have tri :
        ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
          ≤ ‖qs.eval RA ψA0 - qs.eval RA ψI0‖ + ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
        -- rewrite the LHS as ‖(RA ψA0 - RA ψI0) + (RA ψI0 - RI ψI0)‖
        have hdecomp :
          qs.eval RA ψA0 - qs.eval RI ψI0
            = (qs.eval RA ψA0 - qs.eval RA ψI0) + (qs.eval RA ψI0 - qs.eval RI ψI0) := by
          aesop
        calc
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
              = ‖(qs.eval RA ψA0 - qs.eval RA ψI0) + (qs.eval RA ψI0 - qs.eval RI ψI0)‖ := by
                  simp_all
          _ ≤ ‖qs.eval RA ψA0 - qs.eval RA ψI0‖ + ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
                  simpa using (norm_add_le
                    (qs.eval RA ψA0 - qs.eval RA ψI0)
                    (qs.eval RA ψI0 - qs.eval RI ψI0))
      have hmain :
        ‖ qs.eval (modExpApproxSteps (qs := qs) a N x y w_reg flag q (n+1)) ψ
          - qs.eval (modExpIdealSteps  (qs := qs) a N x y q (n+1)) ψ‖
          ≤ (n+1 : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
        have : ‖ qs.eval RA ψA0 - qs.eval RI ψI0‖
            ≤ (n+1 : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
          calc
            ‖ qs.eval RA ψA0 - qs.eval RI ψI0‖
                ≤ ‖ qs.eval RA ψA0 - qs.eval RA ψI0‖
                  + ‖ qs.eval RA ψI0 - qs.eval RI ψI0‖ := tri
            _ = ‖ ψA0 - ψI0‖ + ‖ qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
                  simp [h_iso_RA]
            _ ≤ stepErr K (ModMul.η (qs := qs)) + (n : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
                  gcongr
            _ = (n+1 : ℝ) * stepErr K (ModMul.η (qs := qs)) := by ring
        -- rewrite goals to the sequenced forms
        simpa [hApprox, hIdeal, ψA0, ψI0, eval_seq_simp] using this
      aesop

theorem modExp_dist_bound
  (qs : QSemantics) [RegEncoding qs.Basis] [Spec qs] [ModMul qs] :
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) (ψ : qs.State),
      ‖ψ‖ = 1 →
      ‖ qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ
        - qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ‖
      ≤ (tbits x : ℝ) * stepErr K (ModMul.η (qs := qs)) :=
by
  rcases modExpSteps_dist_bound (qs := qs) with ⟨K, K_nonneg, h⟩
  refine ⟨K, K_nonneg, ?_⟩
  intro a N x y w_reg flag ψ hψ
  simpa [modExpApprox', modExpIdeal', tbits] using
    (h a N x y w_reg flag x.lo (tbits x) ψ hψ)

theorem modExp_overlap_bound_sqrt
  (qs : QSemantics) [RegEncoding qs.Basis] [Spec qs] [ModMul qs] :
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) (ψ : qs.State),
      ‖ψ‖ = 1 →
      ‖ (1 : ℂ) - inner ℂ
          (qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ)
          (qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ)‖
      ≤ ((tbits x : ℕ) : ℝ) * Real.sqrt (2 * (K * ModMul.η (qs := qs))) :=
by
  rcases modExp_dist_bound (qs := qs) with ⟨K, K_nonneg, hdist⟩
  refine ⟨K, K_nonneg, ?_⟩
  intro a N x y w_reg flag ψ hψ

  have hA_unit :
      ‖qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ‖ = 1 := by
    simpa [hψ] using
      (eval_norm_preserved (qs := qs) (modExpApprox' (qs := qs) a N x y w_reg flag) ψ)

  have hov_le_dist :
      ‖ (1 : ℂ) - inner ℂ
          (qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ)
          (qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ)‖
      ≤ ‖ qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ
          - qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ‖ := by
    have h :=
      overlap_le_dist (qs := qs)
        (ψ := qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ)
        (φ := qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ)
    exact h hA_unit

  have hdist' :
      ‖ qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ
          - qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ‖
      ≤ ((tbits x : ℕ) : ℝ) * stepErr K (ModMul.η (qs := qs)) :=
    hdist a N x y w_reg flag ψ hψ

  have : ‖ (1 : ℂ) - inner ℂ
          (qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ)
          (qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ)‖
      ≤ ((tbits x : ℕ) : ℝ) * stepErr K (ModMul.η (qs := qs)) :=
    le_trans hov_le_dist hdist'

  simpa [stepErr] using this


end Shor
