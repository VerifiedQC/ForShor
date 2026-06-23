import FastMultiplication.ShorVerification.Basic

universe u
namespace Shor

open QSemantics
open Gate


/-!
# Modular Exponentiation Approximation Bounds

This file isolates the modular-multiplication / modular-exponentiation circuit
definitions and the corresponding approximation-bound development from
`ShorVerification.Basic`.

It depends on the abstract semantic interfaces from `Basic`, but keeps the
error-propagation machinery separate so the semantic core stays focused.
-/

/-- Overlap error invariance under a common post-gate. -/
lemma overlap_err_invariant
  (qs : QSemantics) (W : Gate) (ψ φ : qs.State) :
    ‖ (1 : ℂ) - inner ℂ (qs.eval W ψ) (qs.eval W φ)‖
      =
    ‖ (1 : ℂ) - inner ℂ ψ φ‖ := by
  simp [qs.inner_preserved W ψ φ]

/-- `‖1 - inner ψ φ‖ ≤ ‖ψ - φ‖` when `‖ψ‖ = 1`. -/
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

/-- Distance is bounded by the square root of twice the overlap error for unit vectors. -/
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

class Spec where
  idealModMul     : (c N : ℕ) → (x : Reg) → Gate
  idealCtrlModMul : (c N : ℕ) → (x : Reg) → (ctrl : ℕ) → Gate


/-! =========================================================
    Section 1: Modular multiplication and exponentiation circuits
========================================================= -/

/-- Inverse QFT. -/
def IQFT (r : Reg) : Gate :=
  †(Gate.QFT r)

/-- Apply Hadamards across all qubits of a register. -/
def H_reg (r : Reg) : Gate :=
  (regQubits r).foldl (fun acc q => (Gate.H q) ;; acc) Gate.id

/-- Primitive gate wrapper. -/
def PrimN (tag : String) (args : List ℕ) : Gate :=
  Gate.Prim tag args

noncomputable def step1
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (c N : ℕ) (ctrl : ℕ) (x_reg w_reg : Reg) : Gate :=
  let phi : ℝ := (2 * Real.pi * ((c + N - 1) % N)) / (N : ℝ)
  (H_reg w_reg) ;;
  (Gate.CPhaseProd ctrl phi x_reg w_reg) ;;
  (IQFT w_reg)

noncomputable def step2
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (N : ℕ) (x_reg w_reg : Reg) : Reg × Gate :=
  let x_ext : Reg := extendHi x_reg
  let n1 : ℕ := regSize x_ext
  let m  : ℕ := regSize w_reg
  let phi : ℝ := (2 * Real.pi * (N : ℝ)) / ((2 : ℝ) ^ (m + n1))
  (x_ext,
    (Gate.QFT x_ext) ;;
    (Gate.PhaseProd phi w_reg x_ext) ;;
    (IQFT x_ext))

noncomputable def frac_load
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (k N : ℕ) (ctrl : ℕ) (x_reg w_reg : Reg) : Gate :=
  let phi : ℝ := (2 * Real.pi * ((k % N) : ℝ)) / (N : ℝ)
  (H_reg w_reg) ;;
  (Gate.CPhaseProd ctrl phi x_reg w_reg) ;;
  (IQFT w_reg)

def step3 (N : ℕ) (x_ext : Reg) (flag : ℕ) : Gate :=
  (PrimN "CMP_GE_CONST" [x_ext.lo, x_ext.hi, N, flag]) ;;
  (PrimN "CSUB_CONST"   [flag, x_ext.lo, x_ext.hi, N])

def step4 (N : ℕ) (x_ext w_reg : Reg) (flag : ℕ) : Gate :=
  PrimN "CMP_LT_NW" [x_ext.lo, x_ext.hi, w_reg.lo, w_reg.hi, N, flag]

noncomputable def step5
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (k5 N : ℕ) (ctrl : ℕ) (x_ext w_reg : Reg) : Gate :=
  †(frac_load (Basis := Basis) k5 N ctrl x_ext w_reg)

noncomputable def CmodMulInPlaceCore
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (c N k5 : ℕ) (ctrl : ℕ) (x_reg w_reg : Reg) (flag : ℕ) : Gate :=
  let U1 : Gate := step1 (Basis := Basis) c N ctrl x_reg w_reg
  let pair := step2 (Basis := Basis) N x_reg w_reg
  let x_ext : Reg := pair.1
  let U2 : Gate := pair.2
  let U3 : Gate := step3 N x_ext flag
  let U4 : Gate := step4 N x_ext w_reg flag
  let U5 : Gate := step5 (Basis := Basis) k5 N ctrl x_ext w_reg
  U1 ;; U2 ;; U3 ;; U4 ;; U5

noncomputable def CmodMulInPlace
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (base n m c N k5 ctrl : ℕ) : Gate :=
  let x_reg : Reg := { lo := base, size := n }
  let w_reg : Reg := { lo := base + n + 1, size := m }
  let flag  : ℕ := base + n + m + 1
  CmodMulInPlaceCore (Basis := Basis) c N k5 ctrl x_reg w_reg flag

def tbits (x : Reg) : ℕ :=
  regSize x

/--
Approximate controlled modular multiplication assumption used to derive the
modular-exponentiation error bound.
-/
class ModMul (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] where
  η : ℝ
  η_nonneg : 0 ≤ η
  k5 : ℕ → ℕ → ℕ
  theorem1_ctrl_gen :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (c N : ℕ) (x_reg w_reg : Reg) (flag ctrl : ℕ) (ψ : qs.State),
        ‖ (1 : ℂ) - inner ℂ
            (qs.eval (CmodMulInPlaceCore (Basis := qs.Basis) c N (k5 c N) ctrl x_reg w_reg flag) ψ)
            (qs.eval (Spec.idealCtrlModMul c N x_reg ctrl) ψ)‖
        ≤ K * η

noncomputable def modExpApproxSteps
    (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs]
    (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) : ℕ → ℕ → Gate
  | _q, 0   => Gate.id
  | q, n+1 =>
      let k : ℕ := q - x.lo
      let c : ℕ := ((a ^ (2 ^ k)) % N)
      (CmodMulInPlaceCore (Basis := qs.Basis) c N (ModMul.k5 (qs := qs) c N) q y w_reg flag) ;;
      modExpApproxSteps qs a N x y w_reg flag (q+1) n

noncomputable def modExpApprox'
    (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs]
    (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) : Gate :=
  modExpApproxSteps qs a N x y w_reg flag x.lo (tbits x)

def modExpIdealSteps (qs : QSemantics) [RegEncoding qs.Basis] [Spec]
    (a N : ℕ) (x y : Reg) : ℕ → ℕ → Gate
  | _q, 0   => Gate.id
  | q, n+1  =>
      let k : ℕ := q - x.lo
      (Spec.idealCtrlModMul ((a ^ (2 ^ k)) % N) N y q) ;;
      modExpIdealSteps qs a N x y (q+1) n

def modExpIdeal' (qs : QSemantics) [RegEncoding qs.Basis] [Spec]
    (a N : ℕ) (x y : Reg) : Gate :=
  modExpIdealSteps qs a N x y x.lo (tbits x)

noncomputable def stepErr (K η : ℝ) : ℝ :=
  Real.sqrt (2 * (K * η))

/-! =========================================================
    Section 2: Modular exponentiation error propagation
========================================================= -/

lemma ctrlMul_step_dist_bound
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs] :
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c N : ℕ) (x_reg w_reg : Reg) (flag ctrl : ℕ) (ψ : qs.State),
      ‖ψ‖ = 1 →
      ‖ qs.eval (CmodMulInPlaceCore (Basis := qs.Basis) c N (ModMul.k5 (qs := qs) c N) ctrl x_reg w_reg flag) ψ
        - qs.eval (Spec.idealCtrlModMul c N x_reg ctrl) ψ‖
      ≤ stepErr K (ModMul.η (qs := qs)) :=
by
  rcases ModMul.theorem1_ctrl_gen (qs := qs) with ⟨K, K_nonneg, hK⟩
  refine ⟨K, K_nonneg, ?_⟩
  intro c N x_reg w_reg flag ctrl ψ hψ

  set ψA : qs.State :=
    qs.eval (CmodMulInPlaceCore (Basis := qs.Basis) c N (ModMul.k5 (qs := qs) c N) ctrl x_reg w_reg flag) ψ
  set ψI : qs.State :=
    qs.eval (Spec.idealCtrlModMul c N x_reg ctrl) ψ

  have hψA : ‖ψA‖ = 1 := by
    simpa [ψA, hψ] using
      (eval_norm_preserved (qs := qs)
        (CmodMulInPlaceCore (Basis := qs.Basis) c N (ModMul.k5 (qs := qs) c N) ctrl x_reg w_reg flag) ψ)

  have hψI : ‖ψI‖ = 1 := by
    simpa [ψI, hψ] using
      (eval_norm_preserved (qs := qs)
        (Spec.idealCtrlModMul c N x_reg ctrl) ψ)

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
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs] :
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

      set A : Gate := CmodMulInPlaceCore (Basis := qs.Basis) c N (ModMul.k5 (qs := qs) c N) q y w_reg flag with hA
      set I : Gate := Spec.idealCtrlModMul c N y q with hI
      set RA : Gate := modExpApproxSteps (qs := qs) a N x y w_reg flag (q+1) n with hRA
      set RI : Gate := modExpIdealSteps  (qs := qs) a N x y (q+1) n with hRI

      have hApprox :
        modExpApproxSteps (qs := qs) a N x y w_reg flag q (n+1) = A ;; RA := by
        simp [modExpApproxSteps, hk, hc, hA, hRA]

      have hIdeal :
        modExpIdealSteps (qs := qs) a N x y q (n+1) = I ;; RI := by
        simp [modExpIdealSteps, hk, hc, hI, hRI]

      set ψA0 : qs.State := qs.eval A ψ
      set ψI0 : qs.State := qs.eval I ψ

      have hψA0_unit : ‖ψA0‖ = 1 := by
        simpa [ψA0, hψ] using (eval_norm_preserved (qs := qs) A ψ)

      have hψI0_unit : ‖ψI0‖ = 1 := by
        simpa [ψI0, hψ] using (eval_norm_preserved (qs := qs) I ψ)

      have h_head :
        ‖ψA0 - ψI0‖ ≤ stepErr K (ModMul.η (qs := qs)) := by
        have := hstep c N y w_reg flag q ψ hψ
        simpa [ψA0, ψI0, hA, hI] using this

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
        have hdecomp :
          qs.eval RA ψA0 - qs.eval RI ψI0
            = (qs.eval RA ψA0 - qs.eval RA ψI0) + (qs.eval RA ψI0 - qs.eval RI ψI0) := by
          aesop
        calc
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
              = ‖(qs.eval RA ψA0 - qs.eval RA ψI0) + (qs.eval RA ψI0 - qs.eval RI ψI0)‖ := by
                  rw [hdecomp]
          _ ≤ ‖qs.eval RA ψA0 - qs.eval RA ψI0‖ + ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
                  simpa using
                    (norm_add_le
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
        simpa [hApprox, hIdeal, ψA0, ψI0, eval_seq_simp] using this
      aesop

theorem modExp_dist_bound
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs] :
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
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs] :
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
