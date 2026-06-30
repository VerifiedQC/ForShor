import FastMultiplication.ShorVerification.Basic
import Mathlib.Data.Int.GCD

open Shor

universe v

namespace Shor

/-- Ideal modular multiplication specifications used by the correctness layer. -/
class Spec where
  idealModMul     : (c N : ℕ) → (x : Reg) → Gate
  idealCtrlModMul : (c N : ℕ) → (x : Reg) → (ctrl : ℕ) → Gate

/-! =========================================================
    Shared modular-multiplication/exponentiation circuit definitions
========================================================= -/

/-- Inverse QFT. -/
def IQFT (r : Reg) : Gate :=
  †(Gate.QFT r)

/-- Apply Hadamards across all qubits of a register. -/
def H_reg (r : Reg) : Gate :=
  (regQubits r).foldl (fun acc q => (Gate.H q) ;; acc) Gate.id

noncomputable def step1
    {Basis : Type v} [RegEncoding Basis] [ExtRegEncoding Basis]
    (c N : ℕ) (ctrl : ℕ) (x_reg w_reg : Reg) : Gate :=
  let phi : ℝ := (2 * Real.pi * (((c + N - 1) % N : ℕ) : ℝ)) / (N : ℝ)
  (H_reg w_reg) ;;
  (Gate.CPhaseProd ctrl phi x_reg w_reg) ;;
  (IQFT w_reg)

noncomputable def step2
    {Basis : Type v} [RegEncoding Basis] [ExtRegEncoding Basis]
    (N : ℕ) (x_reg w_reg : Reg) : Reg × Gate :=
  let x_ext : Reg := extendHi x_reg
  let n1 : ℕ := regSize x_ext
  let m  : ℕ := regSize w_reg
  let phi : ℝ := (2 * Real.pi * (N : ℝ)) / ((2 : ℝ) ^ (m + n1))
  (x_ext,
    (Gate.QFT x_ext) ;;
    (Gate.PhaseProd phi w_reg x_ext) ;;
    (IQFT x_ext))

def step3 (N : ℕ) (x_ext : Reg) (flag : ℕ) : Gate :=
  (Gate.Prim "CMP_GE_CONST" [x_ext.lo, x_ext.hi, N, flag]) ;;
  (Gate.Prim "CSUB_CONST"   [flag, x_ext.lo, x_ext.hi, N])

def step4 (N : ℕ) (x_ext w_reg : Reg) (flag : ℕ) : Gate :=
  Gate.Prim "CMP_LT_NW" [x_ext.lo, x_ext.hi, w_reg.lo, w_reg.hi, N, flag]

noncomputable def step5
    {Basis : Type v} [RegEncoding Basis] [ExtRegEncoding Basis]
    (k5val N : ℕ) (ctrl : ℕ) (x_ext w_reg : Reg) : Gate :=
  let phi : ℝ := (2 * Real.pi * ((k5val % N : ℕ) : ℝ)) / (N : ℝ)
  †((H_reg w_reg) ;;
    (Gate.CPhaseProd ctrl phi x_ext w_reg) ;;
    (IQFT w_reg))

/--
The Step-5 cleanup constant `1 - c⁻¹ mod N`, with the inverse chosen from
the finite modular-inverse existence theorem when it applies.
-/
noncomputable def step5Constant (c N : ℕ) : ℕ :=
  if h : ∃ cinv : ℕ, cinv < N ∧ (c * cinv) % N = 1 then
    (1 + N - Nat.find h) % N
  else
    0

noncomputable def CmodMulInPlaceCore
    {Basis : Type v} [RegEncoding Basis] [ExtRegEncoding Basis]
    (c N : ℕ) (ctrl : ℕ) (x_reg w_reg : Reg) (flag : ℕ) : Gate :=
  let U1 : Gate := step1 (Basis := Basis) c N ctrl x_reg w_reg
  let pair := step2 (Basis := Basis) N x_reg w_reg
  let x_ext : Reg := pair.1
  let U2 : Gate := pair.2
  let U3 : Gate := step3 N x_ext flag
  let U4 : Gate := step4 N x_ext w_reg flag
  let U5 : Gate := step5 (Basis := Basis) (step5Constant c N) N ctrl x_ext w_reg
  U1 ;; U2 ;; U3 ;; U4 ;; U5

def tbits (x : Reg) : ℕ :=
  regSize x

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

end Shor

/-!
# Core Modular-Multiplication Bounds Infrastructure

Focus theorem: `idealCtrlModMul_preserves_valid`.

This file contains the shared validity predicates, semantic interfaces,
Algorithm-1 and modular-exponentiation side conditions, core configurations,
reference traces, and elementary arithmetic facts used by the later bounds.
-/

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
Exact basis semantics required of the ideal controlled modular multiplier.

The ideal gate writes the controlled modular-product value to `data` and
leaves all other qubits unchanged. The weaker existential formulation is
derived below as `IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket`.
-/
class IdealCtrlModMulExactSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec] : Prop where

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

theorem IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    (c N : ℕ) (data work : Reg) (flag ctrl : ℕ) (b : qs.Basis)
    (hN : 1 < N)
    (hsize : N ≤ ASize data)
    (hcoprime : Nat.Coprime c N)
    (hlayout : ModMulCoreLayout data work flag ctrl)
    (hb : GoodModMulBasisInput qs N data work flag b) :
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
          RegEncoding.toNat data b := by
  classical

  let out : ℕ :=
    if RegEncoding.bit ctrl b then
      (c * RegEncoding.toNat data b) % N
    else
      RegEncoding.toNat data b
  let b' : qs.Basis := RegEncoding.writeNat data out b

  have hNpos : 0 < N :=
    Nat.lt_trans Nat.zero_lt_one hN

  rcases hlayout with
    ⟨hext_work, hflag_ext, _hflag_work, hctrl_ext, _hctrl_work, _hctrl_ne⟩

  have hdata_work : Disjoint data work := by
    rcases hext_work with h | h
    · left
      exact le_trans
        (show data.hi ≤ (extendHi data).hi by
          simp [Reg.hi, extendHi])
        h
    · right
      simpa [extendHi] using h

  have hwork_data : Disjoint work data := by
    rcases hdata_work with h | h
    · exact Or.inr h
    · exact Or.inl h

  have hcarry_data : Disjoint (qubitReg data.hi) data := by
    right
    simp [qubitReg]

  have hflag_data : Disjoint (qubitReg flag) data := by
    unfold QubitOutside at hflag_ext
    rcases hflag_ext with h | h
    · left
      change flag + 1 ≤ data.lo
      exact Nat.succ_le_of_lt h
    · right
      exact le_trans
        (show data.hi ≤ (extendHi data).hi by
          simp [Reg.hi, extendHi])
        h

  have hctrl_data : ctrl < data.lo ∨ data.hi ≤ ctrl := by
    unfold QubitOutside at hctrl_ext
    rcases hctrl_ext with h | h
    · exact Or.inl h
    · exact Or.inr
        (le_trans
          (show data.hi ≤ (extendHi data).hi by
            simp [Reg.hi, extendHi])
          h)

  have hout_lt_N : out < N := by
    by_cases hctrl : RegEncoding.bit ctrl b
    · simpa [out, hctrl] using
        (Nat.mod_lt (c * RegEncoding.toNat data b) hNpos)
    · simpa [out, hctrl] using hb.1

  have hout_lt_cap : out < ASize data :=
    lt_of_lt_of_le hout_lt_N hsize

  have hdata_out :
      RegEncoding.toNat data b' = out := by
    exact
      RegEncoding.toNat_writeNat_of_lt
        data out b hout_lt_cap

  have hcarry_out :
      RegEncoding.toNat (qubitReg data.hi) b' = 0 := by
    calc
      RegEncoding.toNat (qubitReg data.hi) b'
        =
          RegEncoding.toNat (qubitReg data.hi) b := by
            exact
              RegEncoding.toNat_left_write_right
                (qubitReg data.hi) data hcarry_data b out
      _ = 0 := hb.2.1

  have hwork_out :
      RegEncoding.toNat work b' = 0 := by
    calc
      RegEncoding.toNat work b'
        =
          RegEncoding.toNat work b := by
            exact
              RegEncoding.toNat_left_write_right
                work data hwork_data b out
      _ = 0 := hb.2.2.1

  have hflag_out :
      RegEncoding.toNat (qubitReg flag) b' = 0 := by
    calc
      RegEncoding.toNat (qubitReg flag) b'
        =
          RegEncoding.toNat (qubitReg flag) b := by
            exact
              RegEncoding.toNat_left_write_right
                (qubitReg flag) data hflag_data b out
      _ = 0 := hb.2.2.2

  have hgood_out :
      GoodModMulBasisInput qs N data work flag b' := by
    refine ⟨?_, hcarry_out, hwork_out, hflag_out⟩
    calc
      RegEncoding.toNat data b' = out := hdata_out
      _ < N := hout_lt_N

  have hctrl_out :
      RegEncoding.bit ctrl b' = RegEncoding.bit ctrl b := by
    simpa [b'] using
      RegEncoding.bit_writeNat_out
        (r := data)
        (v := out)
        (b := b)
        (q := ctrl)
        hctrl_data

  have heval :
      qs.eval (Spec.idealCtrlModMul c N data ctrl) (qs.ket b)
        = qs.ket b' := by
    simpa [b', out] using
      (IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket_exact
        (qs := qs)
        c N data work flag ctrl b
        hN hsize hcoprime
        ⟨hext_work, hflag_ext, _hflag_work, hctrl_ext, _hctrl_work, _hctrl_ne⟩
        hb)

  refine ⟨b', heval, hgood_out, hctrl_out, ?_⟩
  simpa [out] using hdata_out



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
  classical

  have hNpos : 0 < N :=
    Nat.lt_trans Nat.zero_lt_one hN

  have hlayout_exact := hlayout
  rcases hlayout with
    ⟨hext_work, hflag_ext, _hflag_work, _hctrl_ext, _hctrl_work, _hctrl_ne⟩

  unfold QubitOutside at hflag_ext

  have hdata_work : Disjoint data work := by
    rcases hext_work with h | h
    · left
      exact le_trans
        (show data.hi ≤ (extendHi data).hi by
          simp [Reg.hi, extendHi])
        h
    · right
      simpa [extendHi] using h

  have hwork_data : Disjoint work data := by
    rcases hdata_work with h | h
    · exact Or.inr h
    · exact Or.inl h

  have hcarry_data : Disjoint (qubitReg data.hi) data := by
    right
    simp [qubitReg]

  have hflag_data : Disjoint (qubitReg flag) data := by
    rcases hflag_ext with h | h
    · left
      change flag + 1 ≤ data.lo
      exact Nat.succ_le_of_lt h
    · right
      exact le_trans
        (show data.hi ≤ (extendHi data).hi by
          simp [Reg.hi, extendHi])
        h

  let validSet : Set qs.State :=
    { ξ : qs.State |
      ∃ b : qs.Basis,
        GoodModMulBasisInput qs N data work flag b ∧
        ξ = qs.ket b }

  change ψ ∈ Submodule.span ℂ validSet at hvalid
  change
    qs.eval (Spec.idealCtrlModMul c N data ctrl) ψ
      ∈ Submodule.span ℂ validSet

  refine
    Submodule.span_induction
      (s := validSet)
      (p := fun ξ _ =>
        qs.eval (Spec.idealCtrlModMul c N data ctrl) ξ
          ∈ Submodule.span ℂ validSet)
      ?_ ?_ ?_ ?_
      hvalid
  · intro ξ hξ
    change
      ∃ b : qs.Basis,
        GoodModMulBasisInput qs N data work flag b ∧
        ξ = qs.ket b at hξ
    rcases hξ with ⟨b, hb, rfl⟩

    let out : ℕ :=
      if RegEncoding.bit ctrl b then
        (c * RegEncoding.toNat data b) % N
      else
        RegEncoding.toNat data b

    have hout_lt_N : out < N := by
      by_cases hctrl : RegEncoding.bit ctrl b
      · simpa [out, hctrl] using
          (Nat.mod_lt (c * RegEncoding.toNat data b) hNpos)
      · simpa [out, hctrl] using hb.1

    have hout_lt_cap : out < ASize data :=
      lt_of_lt_of_le hout_lt_N hsize

    have hdata_out :
        RegEncoding.toNat data
          (RegEncoding.writeNat data out b)
          =
        out := by
      exact
        RegEncoding.toNat_writeNat_of_lt
          data out b hout_lt_cap

    have hcarry_out :
        RegEncoding.toNat (qubitReg data.hi)
          (RegEncoding.writeNat data out b)
          =
        0 := by
      calc
        RegEncoding.toNat (qubitReg data.hi)
            (RegEncoding.writeNat data out b)
          =
            RegEncoding.toNat (qubitReg data.hi) b := by
              exact
                RegEncoding.toNat_left_write_right
                  (qubitReg data.hi) data hcarry_data b out
        _ = 0 := hb.2.1

    have hwork_out :
        RegEncoding.toNat work
          (RegEncoding.writeNat data out b)
          =
        0 := by
      calc
        RegEncoding.toNat work
            (RegEncoding.writeNat data out b)
          =
            RegEncoding.toNat work b := by
              exact
                RegEncoding.toNat_left_write_right
                  work data hwork_data b out
        _ = 0 := hb.2.2.1

    have hflag_out :
        RegEncoding.toNat (qubitReg flag)
          (RegEncoding.writeNat data out b)
          =
        0 := by
      calc
        RegEncoding.toNat (qubitReg flag)
            (RegEncoding.writeNat data out b)
          =
            RegEncoding.toNat (qubitReg flag) b := by
              exact
                RegEncoding.toNat_left_write_right
                  (qubitReg flag) data hflag_data b out
        _ = 0 := hb.2.2.2

    have hgood_out :
        GoodModMulBasisInput qs N data work flag
          (RegEncoding.writeNat data out b) := by
      refine ⟨?_, hcarry_out, hwork_out, hflag_out⟩
      calc
        RegEncoding.toNat data
            (RegEncoding.writeNat data out b)
          = out := hdata_out
        _ < N := hout_lt_N

    have heval :
        qs.eval (Spec.idealCtrlModMul c N data ctrl) (qs.ket b)
          =
        qs.ket (RegEncoding.writeNat data out b) := by
      simpa [out] using
        (IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket_exact
          (qs := qs)
          c N data work flag ctrl b
          hN hsize hcoprime hlayout_exact hb)

    rw [heval]

    exact Submodule.subset_span
      (show qs.ket (RegEncoding.writeNat data out b) ∈ validSet from
        ⟨_, hgood_out, rfl⟩)

  ·
    change
      qs.eval (Spec.idealCtrlModMul c N data ctrl) 0
        ∈ Submodule.span ℂ validSet
    rw [qs.eval_zero]
    exact (Submodule.span ℂ validSet).zero_mem

  · intro ξ ζ _hξ _hζ hξ_eval hζ_eval
    change
      qs.eval (Spec.idealCtrlModMul c N data ctrl) (ξ + ζ)
        ∈ Submodule.span ℂ validSet
    rw [qs.eval_add]
    exact (Submodule.span ℂ validSet).add_mem hξ_eval hζ_eval

  · intro a ξ _hξ hξ_eval
    change
      qs.eval (Spec.idealCtrlModMul c N data ctrl) (a • ξ)
        ∈ Submodule.span ℂ validSet
    rw [qs.eval_smul]
    exact (Submodule.span ℂ validSet).smul_mem a hξ_eval
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

The concrete `step5Constant` above chooses such an inverse with `Nat.find`
when coprimality guarantees one exists.
-/
def Step5ConstantOK (c N k5val : ℕ) : Prop :=
  ∃ cinv : ℕ,
    cinv < N ∧
    (c * cinv) % N = 1 % N ∧
    k5val % N = (1 + N - cinv) % N

theorem step5Constant_ok
    (c N : ℕ)
    (hN : 1 < N)
    (hcoprime : Nat.Coprime c N) :
    Step5ConstantOK c N (step5Constant c N) := by
  classical
  have hExists : ∃ cinv : ℕ, cinv < N ∧ (c * cinv) % N = 1 :=
    Nat.exists_mul_mod_eq_one_of_coprime hcoprime hN
  let cinv : ℕ := Nat.find hExists
  have hcinv : cinv < N ∧ (c * cinv) % N = 1 := by
    simpa [cinv] using Nat.find_spec hExists
  refine ⟨cinv, hcinv.1, ?_, ?_⟩
  · have h1lt : 1 < N := hN
    simpa [Nat.mod_eq_of_lt h1lt] using hcinv.2
  · unfold step5Constant
    rw [dif_pos hExists]
    simp [cinv]

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

/-- For every controlled multiplication in a tail, the multiplier is invertible modulo `N`. -/
def ModExpTailArithmeticOK
    (a N : ℕ) (x : Reg)
    (q n : ℕ) : Prop :=
  ∀ j : ℕ, j < n →
    let e : ℕ := (q + j) - x.lo
    let c : ℕ := (a ^ (2 ^ e)) % N
    Nat.Coprime c N


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
    (a N : ℕ) (x : Reg) : Prop :=
  ModExpTailArithmeticOK a N x x.lo (tbits x)

noncomputable def modExpApproxStepsValid
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (a N : ℕ) (x data work : Reg) (flag : ℕ) :
    ℕ → ℕ → Gate
  | _q, 0 =>
      Gate.id
  | q, n + 1 =>
      let e : ℕ := q - x.lo
      let c : ℕ := (a ^ (2 ^ e)) % N
      CmodMulInPlaceCore
        (Basis := Basis)
        c N q data work flag
      ;;
      modExpApproxStepsValid
        (Basis := Basis)
        a N x data work flag (q + 1) n

noncomputable def modExpApproxValid
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (a N : ℕ) (x data work : Reg) (flag : ℕ) : Gate :=
  modExpApproxStepsValid
    (Basis := Basis)
    a N x data work flag x.lo (tbits x)


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

structure ModExpConfig (η : ℝ) where
  env : Algorithm1Env η

  a : ℕ
  x : Reg
  flag : ℕ

  layout :
    ModExpLayout x env.data env.work flag

  arithmetic :
    ModExpArithmeticOK a env.N x


namespace ModExpConfig

noncomputable def approxGate
    {η : ℝ}
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (cfg : ModExpConfig η) : Gate :=
  modExpApproxValid
    (Basis := Basis)
    cfg.a cfg.env.N cfg.x cfg.env.data cfg.env.work cfg.flag

def idealGate
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec]
    {η : ℝ}
    (cfg : ModExpConfig η) : Gate :=
  modExpIdeal' qs cfg.a cfg.env.N cfg.x cfg.env.data

def ValidUnitState
    (qs : QSemantics) [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModExpConfig η) (ψ : qs.State) : Prop :=
  ψ ∈ ValidModMulState
      qs cfg.env.N cfg.env.data cfg.env.work cfg.flag
    ∧ ‖ψ‖ = 1

end ModExpConfig



/-! =========================================================
    One controlled modular multiplication
========================================================= -/

structure ModMulConfig (η : ℝ) where
  env : Algorithm1Env η
  c : ℕ
  flag : ℕ
  ctrl : ℕ
  coprime  : Nat.Coprime c env.N
  layout   : ModMulCoreLayout env.data env.work flag ctrl

namespace ModMulConfig

noncomputable def approxGate
    {η : ℝ}
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  CmodMulInPlaceCore
    (Basis := Basis)
    cfg.c cfg.env.N
    cfg.ctrl cfg.env.data cfg.env.work cfg.flag

def idealGate
    {η : ℝ}
    [Spec]
    (cfg : ModMulConfig η) : Gate :=
  Spec.idealCtrlModMul cfg.c cfg.env.N cfg.env.data cfg.ctrl

def ValidState
    (qs : QSemantics) [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η) (ψ : qs.State) : Prop :=
  ψ ∈ ValidModMulState qs cfg.env.N cfg.env.data cfg.env.work cfg.flag

def ValidUnitState
    (qs : QSemantics) [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η) (ψ : qs.State) : Prop :=
  cfg.ValidState qs ψ ∧ ‖ψ‖ = 1


/-! =========================================================
    Algorithm-1 staged gates
========================================================= -/

noncomputable def U1
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  step1
    (Basis := Basis)
    cfg.c
    cfg.env.N
    cfg.ctrl
    cfg.env.data
    cfg.env.work

noncomputable def U2
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  (step2
    (Basis := Basis)
    cfg.env.N
    cfg.env.data
    cfg.env.work).2

noncomputable def U34
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  step3 cfg.env.N (extendHi cfg.env.data) cfg.flag ;;
  step4 cfg.env.N (extendHi cfg.env.data) cfg.env.work cfg.flag

noncomputable def U5
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  step5
    (Basis := Basis)
    (step5Constant cfg.c cfg.env.N)
    cfg.env.N
    cfg.ctrl
    (extendHi cfg.env.data)
    cfg.env.work

noncomputable def stagedGate
    {η : ℝ}
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  U1 (Basis := Basis) cfg ;;
  U2 (Basis := Basis) cfg ;;
  U34 (Basis := Basis) cfg ;;
  U5 (Basis := Basis) cfg

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
    Ideal controlled multiplication on a configuration
========================================================= -/

theorem IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_cfg
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η) (b : qs.Basis)
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
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℕ :=
  if RegEncoding.bit cfg.ctrl b then
    (((cfg.c + cfg.env.N - 1) % cfg.env.N)
      * RegEncoding.toNat cfg.env.data b) % cfg.env.N
  else
    0

noncomputable def alg1TargetFraction
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℝ :=
  (alg1TargetResidue cfg b : ℝ) / (cfg.env.N : ℝ)

noncomputable def alg1WorkFraction
    {η : ℝ}
    (cfg : ModMulConfig η)
    (t : Fin (ASize cfg.env.work)) : ℝ :=
  (t.1 : ℝ) / (ASize cfg.env.work : ℝ)

noncomputable def alg1GoodLabels
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) :
    Finset (Fin (ASize cfg.env.work)) :=
  Finset.univ.filter fun t =>
    |alg1TargetFraction cfg b - alg1WorkFraction cfg t|
      < η / (ASize cfg.env.data : ℝ)

noncomputable def alg1Step2Value
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℕ :=
  RegEncoding.toNat cfg.env.data b + alg1TargetResidue cfg b


/-! =========================================================
    Step-2 Fourier coefficient definitions
========================================================= -/

/-! =========================================================
    Step-2 one-label Fourier stability
========================================================= -/

/--
The Step-2 phase angle, written independently of the `let`s in `step2`.
-/
noncomputable def alg1Step2Phase
    {η : ℝ}
    (cfg : ModMulConfig η) : ℝ :=
  (2 * Real.pi * (cfg.env.N : ℝ)) /
    ((2 : ℝ) ^
      (regSize cfg.env.work + regSize (extendHi cfg.env.data)))

/--
The normalizing scalar in the QFT on `extendHi data`.
-/
noncomputable def alg1Step2QFTScale
    {η : ℝ}
    (cfg : ModMulConfig η) : ℂ :=
  (1 / Real.sqrt ((ASize (extendHi cfg.env.data) : ℕ) : ℝ) : ℂ)

/--
The Fourier coefficient after the first QFT and the actual Step-2
`PhaseProd`, before the final inverse QFT.
-/
noncomputable def alg1Step2ActualFourierCoeff
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work))
    (y : Fin (ASize (extendHi cfg.env.data))) : ℂ :=
  alg1Step2QFTScale cfg *
    qftPhase
      (ASize (extendHi cfg.env.data))
      (RegEncoding.toNat cfg.env.data b)
      y.1 *
    Complex.exp
      (alg1Step2Phase cfg * Complex.I *
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
    (y : Fin (ASize (extendHi cfg.env.data))) : ℂ :=
  alg1Step2QFTScale cfg *
    qftPhase
      (ASize (extendHi cfg.env.data))
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
    (t : Fin (ASize cfg.env.work)) : ℝ :=
  (cfg.env.N : ℝ) * alg1WorkFraction cfg t
    - (alg1TargetResidue cfg b : ℝ)


/--
The index set obtained by expanding every source branch after the QFT on
`extendHi data`.
-/
abbrev Alg1Step2SourceIndex
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η) :=
  Σ _b : qs.Basis, Fin (ASize cfg.env.work)

abbrev Alg1Step2FourierIndex
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η) :=
  Σ _i : Alg1Step2SourceIndex qs cfg,
    Fin (ASize (extendHi cfg.env.data))

noncomputable def alg1Step2FourierIndices
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Alg1Step2SourceIndex qs cfg)) :
    Finset (Alg1Step2FourierIndex qs cfg) := by
  classical
  exact S.sigma fun _ => Finset.univ

noncomputable def alg1Step2FourierLabel
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (p : Alg1Step2FourierIndex qs cfg) : qs.Basis :=
  RegEncoding.writeNat
    (extendHi cfg.env.data)
    p.2.1
    (RegEncoding.writeNat cfg.env.work p.1.2.1 p.1.1)

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
      (ASize (extendHi cfg.env.data))
      (RegEncoding.toNat cfg.env.data p.1.1)
      p.2.1

noncomputable def alg1Step2FourierMultiplier
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (r : ℕ)
    (p : Alg1Step2FourierIndex qs cfg) : ℂ :=
  Complex.exp
    (alg1Step2Phase cfg * Complex.I *
      ((p.1.2.1 : ℂ) * (p.2.1 : ℂ)))
    -
  qftPhase
    (ASize (extendHi cfg.env.data))
    r
    p.2.1




/-! =========================================================
    Coherent Step-2 error vector
========================================================= -/

/--
The one-label Step-2 error vector.
-/
noncomputable def alg1Step2Error
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work)) : qs.State :=
  qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
      (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
    -
  qs.ket
    (RegEncoding.writeNat
      (extendHi cfg.env.data)
      (alg1Step2Value cfg b)
      (RegEncoding.writeNat cfg.env.work t.1 b))


/-! =========================================================
    Step-3/4 output labels
========================================================= -/

def alg1OutputValue
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : ℕ :=
  if RegEncoding.bit cfg.ctrl b then
    (cfg.c * RegEncoding.toNat cfg.env.data b) % cfg.env.N
  else
    RegEncoding.toNat cfg.env.data b

def alg1Step4CrossCondition
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work)) : Prop :=
  alg1OutputValue cfg b * ASize cfg.env.work < cfg.env.N * t.1

abbrev alg1Overflow
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis) : Prop :=
  cfg.env.N ≤ alg1Step2Value cfg b

structure Alg1Trace
    {η : ℝ}
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    (cfg : ModMulConfig η)
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
    {η : ℝ}
    (cfg : ModMulConfig η)
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
    {η : ℝ}
    (cfg : ModMulConfig η)
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
    {η : ℝ}
    (cfg : ModMulConfig η)
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
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {cfg : ModMulConfig η}
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
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {cfg : ModMulConfig η}
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
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {cfg : ModMulConfig η}
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


/-! =========================================================
    Step-1 and Step-5 coefficient definitions
========================================================= -/

/--
Canonical Step-1 phase-estimation coefficient.

This is the actual amplitude of the work-label basis vector in the Step-1
output. 
-/
noncomputable def alg1PhaseCoeff
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work)) : ℂ :=
  inner ℂ
    (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
    (qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) (qs.ket b))

/-- The QPE probability mass outside the retained good-label set for one basis input. -/
noncomputable def alg1QpeBadMass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
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
    [ExtRegEncoding qs.Basis]
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
    [ExtRegEncoding qs.Basis]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t ∈ Finset.univ.filter
          (fun t => t ∉ alg1GoodLabels cfg b),
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b)

/--
The formal post-Step-3/4 packet with all QPE labels retained.

This is not the operational output of Steps 3–4 on bad labels. It is the
reference packet used to identify the inverse cleanup with the QPE tail.
-/
noncomputable def afterStep34Full
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {cfg : ModMulConfig η}
    {ψ : qs.State}
    (tr : Alg1Trace qs cfg ψ) : qs.State :=
  ∑ b ∈ tr.support,
    tr.inputCoeff b •
      ∑ t : Fin (ASize cfg.env.work),
        tr.phaseCoeff b t •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work t.1 b))

/-- The discarded part of `afterStep34Full`. -/
noncomputable def afterStep34Bad
    {η : ℝ}
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
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
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work t.1 b))

end Alg1Trace

/-! =========================================================
    Step-5 forward fractional-load packet
========================================================= -/

/--
The forward circuit whose adjoint is `ModMulConfig.U5`.

Keeping this named avoids repeatedly unfolding `step5`.
-/
noncomputable def alg1Step5Forward
    {η : ℝ}
    {Basis : Type*}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
  (cfg : ModMulConfig η) : Gate :=
  (H_reg cfg.env.work) ;;
  (Gate.CPhaseProd
    cfg.ctrl
    ((2 * Real.pi *
        ((step5Constant cfg.c cfg.env.N % cfg.env.N : ℕ) : ℝ))
      / (cfg.env.N : ℝ))
    (extendHi cfg.env.data)
    cfg.env.work) ;;
  (IQFT cfg.env.work)

/-- The Step-1 controlled phase angle. -/
noncomputable def alg1Step1Phase
  {η : ℝ}
  (cfg : ModMulConfig η) : ℝ :=
  (2 * Real.pi *
      (((cfg.c + cfg.env.N - 1) % cfg.env.N : ℕ) : ℝ))
    / (cfg.env.N : ℝ)

/-- The forward Step-5 controlled phase angle. -/
noncomputable def alg1Step5Phase
  {η : ℝ}
  (cfg : ModMulConfig η) : ℝ :=
  (2 * Real.pi *
      ((step5Constant cfg.c cfg.env.N % cfg.env.N : ℕ) : ℝ))
    / (cfg.env.N : ℝ)

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
    (z : Fin (ASize cfg.env.work)) : ℂ :=
  if RegEncoding.bit cfg.ctrl b then
    Complex.exp
      (alg1Step1Phase cfg * Complex.I *
        ((RegEncoding.toNat cfg.env.data b : ℂ) * (z.1 : ℂ)))
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
    (z : Fin (ASize cfg.env.work)) : ℂ :=
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
    (z : Fin (ASize cfg.env.work)) : ℂ :=
  (1 / Real.sqrt ((ASize cfg.env.work : ℕ) : ℝ) : ℂ) *
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
    (t : Fin (ASize cfg.env.work)) : ℂ :=
  ∑ z : Fin (ASize cfg.env.work),
    alg1LoadPreCoeff cfg b z *
      alg1IQFTCoeff cfg.env.work z t



/-! =========================================================
    Modular-exponentiation arithmetic helpers
========================================================= -/

theorem modExp_multiplier_coprime
    (a N e : ℕ)
    (hcoprime : Nat.Coprime a N) :
    Nat.Coprime ((a ^ (2 ^ e)) % N) N := by
  have hpow : Nat.Coprime (a ^ (2 ^ e)) N :=
    hcoprime.pow_left (2 ^ e)
  rw [Nat.coprime_iff_gcd_eq_one]
  calc
    Nat.gcd ((a ^ (2 ^ e)) % N) N
        = Nat.gcd (a ^ (2 ^ e)) N :=
          Nat.ModEq.gcd_eq (by simp [Nat.ModEq])
    _ = 1 := hpow.gcd_eq_one

/-- A convenient constructor for the arithmetic condition in `ModExpTailArithmeticOK`. -/
theorem modExp_tail_coprime
    (a N : ℕ) (x : Reg) (q n : ℕ)
    (hcoprime : Nat.Coprime a N) :
    ∀ j : ℕ, j < n →
      Nat.Coprime (a ^ (2 ^ ((q + j) - x.lo)) % N) N := by
  intro j _hj
  exact modExp_multiplier_coprime
    a N ((q + j) - x.lo) hcoprime
