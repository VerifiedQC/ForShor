import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.Shared.Registers
import FastMultiplication.ShorVerification.Implementation.Shared.States

/-!
# `GateSemantics` classes: Pauli-X, extension, radix reverse, arithmetic basis functions

Derived laws of `Framework/Semantics/GateSemantics.lean`'s per-gate classes:
Pauli-X and zero-extension locality, the unsigned phase-product macro
semantics, the proof declarations moved out of the framework file for radix
reverse / extension / arithmetic basis functions, and the generic
basis-write arithmetic lemmas for `ArithmeticSemantics`.
-/

universe u

namespace Shor

variable {Basis : Type u} [RegEncoding Basis]

open QSemantics

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

end GateSemanticsFacts


/-! =========================================================
    Framework Gate Semantics Proofs

    Proof declarations moved out of `Framework.Semantics.GateSemantics` so the
    framework file remains definitions/classes only.
========================================================= -/

theorem radixReverseBasis_writeNat
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (m : ℕ)
    (hm : m ≤ regSize r)
    (b : Basis)
    (kL kH : ℕ) :
    let sp : SplitPoint r := ⟨m, hm⟩
    let left  : Reg := splitLeft r sp
    let right : Reg := splitRight r sp
    kL < ASize left →
    kH < ASize right →
    radixReverseBasis r m
        (RegEncoding.writeNat left kL
          (RegEncoding.writeNat right kH b))
      =
    RegEncoding.writeNat r
      (radixReverseIndex r m hm kL kH)
      b := by
  dsimp
  intro hkL hkH

  let sp : SplitPoint r := ⟨m, hm⟩
  let left  : Reg := splitLeft r sp
  let right : Reg := splitRight r sp
  let b' :=
    RegEncoding.writeNat left kL
      (RegEncoding.writeNat right kH b)

  have hdisj : Disjoint left right := by
    exact splitLeft_splitRight_disjoint r sp

  have hleft :
      RegEncoding.toNat left b' = kL := by
    dsimp [b']
    exact RegEncoding.toNat_writeNat_of_lt
      left kL _ hkL

  have hright :
      RegEncoding.toNat right b' = kH := by
    dsimp [b']
    rw [RegEncoding.toNat_right_write_left
      left right hdisj]
    exact RegEncoding.toNat_writeNat_of_lt
      right kH b hkH

  have hcomm :
      RegEncoding.writeNat left kL
          (RegEncoding.writeNat right kH b)
        =
      RegEncoding.writeNat right kH
          (RegEncoding.writeNat left kL b) :=
    RegEncoding.writeNat_comm_of_disjoint
      left right hdisj kL kH b

  have hsplit :
      RegEncoding.writeNat r
          (kL + ASize left * kH) b
        =
      RegEncoding.writeNat right kH
          (RegEncoding.writeNat left kL b) := by
    simpa [left, right, sp] using
      RegEncoding.writeNat_split
        r sp kH kL b hkL hkH

  have hb' :
      b' =
        RegEncoding.writeNat r
          (kL + ASize left * kH) b := by
    dsimp [b']
    calc
      RegEncoding.writeNat left kL
          (RegEncoding.writeNat right kH b)
          =
        RegEncoding.writeNat right kH
          (RegEncoding.writeNat left kL b) :=
        hcomm
      _ =
        RegEncoding.writeNat r
          (kL + ASize left * kH) b :=
        hsplit.symm

  have hoverwrite (v : ℕ) :
      RegEncoding.writeNat r v b' =
        RegEncoding.writeNat r v b := by
    rw [hb']
    exact RegEncoding.writeNat_overwrite r v _ b

  simp only [radixReverseBasis, dif_pos hm]

  change
    RegEncoding.writeNat r
        (radixReverseIndex r m hm
          (RegEncoding.toNat left b')
          (RegEncoding.toNat right b'))
        b'
      =
    RegEncoding.writeNat r
      (radixReverseIndex r m hm kL kH)
      b

  rw [hleft, hright]
  exact hoverwrite _

namespace RadixReverseSemantics

theorem eval_RadixReverse_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [RadixReverseSemantics qs]
    (r : Reg)
    (m : ℕ)
    (hm : m ≤ regSize r)
    (b : qs.Basis)
    (kL kH : ℕ) :
    let sp : SplitPoint r := ⟨m, hm⟩
    let left  : Reg := splitLeft r sp
    let right : Reg := splitRight r sp
    kL < ASize left →
    kH < ASize right →
    qs.eval (Gate.RadixReverse r m)
      (qs.ket
        (RegEncoding.writeNat left kL
          (RegEncoding.writeNat right kH b)))
    =
    qs.ket
      (RegEncoding.writeNat r
        (radixReverseIndex r m hm kL kH)
        b) := by
  dsimp
  intro hkL hkH

  rw [RadixReverseSemantics.eval_RadixReverse_ket_total]

  exact congrArg qs.ket
    (radixReverseBasis_writeNat
      r m hm b kL kH hkL hkH)

end RadixReverseSemantics

theorem ExtReg.active_newBits_disjoint
    (r : ExtReg)
    (n : ℕ) :
    Disjoint r.active (r.newBits n) := by
  have h := r.active_reserve_disjoint
  rw [Disjoint, List.disjoint_left] at h ⊢
  intro q hqA hqN
  exact h hqA (List.mem_of_mem_take hqN)


theorem signExtendNewValue_lt
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    signExtendNewValue r n b <
      ASize (r.newBits n) := by
  have hhi :=
    RegEncoding.toNat_lt_ASize
      (r := r.newBits n) (b := b)

  unfold signExtendNewValue
  dsimp

  by_cases hneg : extToInt r b < 0
  · simp only [if_pos hneg]
    omega
  · simp only [if_neg hneg]
    exact hhi

@[simp]
theorem toNat_newBits_signExtendBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    RegEncoding.toNat (r.newBits n)
        (signExtendBasis r n b)
      =
    signExtendNewValue r n b := by
  unfold signExtendBasis
  exact RegEncoding.toNat_writeNat_of_lt
    (r.newBits n)
    (signExtendNewValue r n b)
    b
    (signExtendNewValue_lt r n b)

@[simp]
theorem toNat_signExtendBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    ExtReg.toNat r (signExtendBasis r n b) =
      ExtReg.toNat r b := by
  unfold signExtendBasis ExtReg.toNat
  exact
    RegEncoding.toNat_left_write_right
      r.active
      (r.newBits n)
      (ExtReg.active_newBits_disjoint r n)
      b
      (signExtendNewValue r n b)


@[simp]
theorem extToInt_signExtendBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    extToInt r (signExtendBasis r n b) =
      extToInt r b := by
  unfold extToInt
  rw [toNat_signExtendBasis]

theorem signExtendNewValue_signExtendBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    signExtendNewValue r n
        (signExtendBasis r n b)
      =
    RegEncoding.toNat (r.newBits n) b := by
  have hlt :=
    RegEncoding.toNat_lt_ASize
      (r := r.newBits n) (b := b)

  unfold signExtendNewValue
  rw [extToInt_signExtendBasis]
  rw [toNat_newBits_signExtendBasis]

  unfold signExtendNewValue
  dsimp

  by_cases hneg : extToInt r b < 0
  · simp only [if_pos hneg]
    omega
  · simp only [if_neg hneg]

@[simp]
theorem signExtendBasis_involutive
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    signExtendBasis r n
        (signExtendBasis r n b)
      =
    b := by
  change
    RegEncoding.writeNat
        (r.newBits n)
        (signExtendNewValue r n
          (signExtendBasis r n b))
        (signExtendBasis r n b)
      =
    b

  rw [signExtendNewValue_signExtendBasis]
  unfold signExtendBasis
  rw [RegEncoding.writeNat_overwrite]
  exact
    RegEncoding.writeNat_toNat
      (r.newBits n) b

theorem signExtendNewValue_of_fresh
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis)
    (hfresh : r.FreshFor n b) :
    signExtendNewValue r n b =
      if extToInt r b < 0 then
        ASize (r.newBits n) - 1
      else
        0 := by
  have hz :
      RegEncoding.toNat (r.newBits n) b = 0 := by
    simpa [ExtReg.FreshFor, FreshZero] using hfresh

  unfold signExtendNewValue
  rw [hz]
  by_cases hneg : extToInt r b < 0 <;>
    simp [hneg]

lemma tcDecodeWidth_signExtend
    (w n u : ℕ)
    (hu : u < 2 ^ w) :
    tcDecodeWidth (w + n)
        (u +
          2 ^ w *
            (if tcDecodeWidth w u < 0 then
              2 ^ n - 1
            else
              0))
      =
    tcDecodeWidth w u := by
  cases n with
  | zero =>
      simp

  | succ n =>
      cases w with
      | zero =>
          have hu0 : u = 0 := by
            simpa using hu
          subst u
          simp [tcDecodeWidth]

      | succ w =>
          by_cases hsign : u < 2 ^ w

          · -- nonnegative old value
            have hwide :
                u < 2 ^ (w + n + 1) := by
              have hp :
                  2 ^ w ≤ 2 ^ (w + n + 1) :=
                Nat.pow_le_pow_right
                  (by omega)
                  (by omega)
              exact lt_of_lt_of_le hsign hp

            have hnonneg :
                ¬ tcDecodeWidth (w + 1) u < 0 := by
              simp [tcDecodeWidth, hsign]

            have hwidth :
                (w + 1) + (n + 1) =
                  (w + n + 1) + 1 := by
              omega

            rw [hwidth]
            simp [tcDecodeWidth, hsign]
            aesop

          · -- negative old value
            have huZ :
                (u : ℤ) <
                  ((2 ^ (w + 1) : ℕ) : ℤ) := by
              exact_mod_cast hu

            have hneg :
                tcDecodeWidth (w + 1) u < 0 := by
              simp [tcDecodeWidth, hsign]
              linarith

            let M : ℕ := 2 ^ (w + 1)
            let q : ℕ := 2 ^ (n + 1)

            have hq : 1 ≤ q := by
              exact Nat.pow_pos (by omega)

            have hpow :
                2 ^ ((w + 1) + (n + 1)) =
                  M * q := by
              simp [M, q, pow_add]

            have hhalf :
                2 ^ (w + n + 1) =
                  M * 2 ^ n := by
              simp [M, pow_add]
              ring

            have hcoef :
                2 ^ n ≤ q - 1 := by
              simp [q, pow_succ]
              have hp : 0 < 2 ^ n := by positivity
              omega

            have hnotlt :
                ¬
                  u + M * (q - 1) <
                    2 ^ (w + n + 1) := by
              rw [hhalf]
              have :=
                Nat.mul_le_mul_left M hcoef
              omega

            have hadd :
                u + M * (q - 1) + M =
                  u + M * q := by
              calc
                u + M * (q - 1) + M
                    =
                  u + (M * (q - 1) + M * 1) := by
                    simp [Nat.add_assoc]
                _ =
                  u + M * ((q - 1) + 1) := by
                    rw [Nat.mul_add]
                _ =
                  u + M * q := by
                    rw [Nat.sub_add_cancel hq]

            have hwidth :
                (w + 1) + (n + 1) =
                  (w + n + 1) + 1 := by
              omega

            rw [if_pos hneg]
            rw [hwidth]
            simp only [tcDecodeWidth]

            have hnotlt' :
                ¬
                  u + 2 ^ (w + 1) * (2 ^ (n + 1) - 1) <
                    2 ^ (w + n + 1) := by
              simpa [M, q] using hnotlt

            simp [hnotlt', hsign]

            have haddZ :
                ((u + M * (q - 1) : ℕ) : ℤ) =
                  (u : ℤ) + (M * q : ℕ) - (M : ℤ) := by
              have hcast :
                  ((u + M * (q - 1) : ℕ) : ℤ) + (M : ℤ)
                    =
                  (u : ℤ) + (M * q : ℕ) := by
                exact_mod_cast hadd
              linarith

            have hpowZ :
                ((2 : ℤ) ^ (w + n + 1 + 1)) =
                  ((M * q : ℕ) : ℤ) := by
              have hpowNat :
                  2 ^ (w + n + 1 + 1) = M * q := by
                rw [← hpow]
                congr 1
                omega
              exact_mod_cast hpowNat

            have hsumZ :
                (u : ℤ) + (M : ℤ) * ((q : ℤ) - 1) =
                  (u : ℤ) + (M * q : ℕ) - (M : ℤ) := by
              rw [← haddZ]
              norm_num [Nat.cast_sub hq]

            have hcalc :
                (u : ℤ) + (M : ℤ) * ((q : ℤ) - 1) -
                  ((M * q : ℕ) : ℤ)
                =
                (u : ℤ) - (M : ℤ) := by
              rw [hsumZ]
              ring

            simpa [M, q, hpowZ] using hcalc

theorem extToInt_grow_signExtendBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis)
    (hcap : r.CanGrow n)
    (hfresh : r.FreshFor n b) :
    extToInt (r.grow n)
        (signExtendBasis r n b)
      =
    extToInt r b := by
  unfold extToInt
  rw [ExtReg.width_grow r n hcap]
  rw [Gate.ExtReg.toNat_grow]
  rw [toNat_signExtendBasis]
  rw [toNat_newBits_signExtendBasis]
  rw [signExtendNewValue_of_fresh r n b hfresh]

  have hsize :
      ASize (r.newBits n) = 2 ^ n := by
    simp [
      ASize,
      Gate.ExtReg.newBits_size r n hcap
    ]

  rw [hsize]

  exact
    tcDecodeWidth_signExtend
      r.width
      n
      (ExtReg.toNat r b)
      (ExtReg.toNat_lt r b)

theorem toNat_signExtendBasis_of_activeDisjoint
    {Basis : Type u}
    [RegEncoding Basis]
    (r e : ExtReg)
    (n : ℕ)
    (b : Basis)
    (hdisj :
      ExtReg.ActiveDisjoint e (r.grow n)) :
    ExtReg.toNat e
        (signExtendBasis r n b)
      =
    ExtReg.toNat e b := by

  have hnew :
      Disjoint e.active (r.newBits n) := by
    simp [
      ExtReg.ActiveDisjoint,
      Disjoint,
      List.disjoint_left
    ] at hdisj ⊢

    intro q hqe hqn

    apply hdisj hqe

    rw [Gate.ExtReg.active_grow_qubits]
    exact List.mem_append_right _ hqn

  unfold signExtendBasis ExtReg.toNat

  exact
    RegEncoding.toNat_left_write_right
      e.active
      (r.newBits n)
      hnew
      b
      (signExtendNewValue r n b)

namespace GateSemanticsCore

theorem eval_eq_of_ket_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U V : Gate)
    (hket :
      ∀ b : qs.Basis,
        qs.eval U (qs.ket b) =
          qs.eval V (qs.ket b)) :
    ∀ ψ : qs.State,
      qs.eval U ψ = qs.eval V ψ := by

  apply qs.state_induction
    (fun ψ => qs.eval U ψ = qs.eval V ψ)

  · rw [eval_zero, eval_zero]

  · intro ψ φ hψ hφ
    calc
      qs.eval U (ψ + φ)
          = qs.eval U ψ + qs.eval U φ :=
            GateSemanticsCore.eval_add (qs := qs) U ψ φ
      _ = qs.eval V ψ + qs.eval V φ := by
            rw [hψ, hφ]
      _ = qs.eval V (ψ + φ) :=
            (GateSemanticsCore.eval_add (qs := qs) V ψ φ).symm

  · intro a ψ hψ
    calc
      qs.eval U (a • ψ)
          = a • qs.eval U ψ :=
            GateSemanticsCore.eval_smul (qs := qs) U a ψ
      _ = a • qs.eval V ψ := by
            rw [hψ]
      _ = qs.eval V (a • ψ) :=
            (GateSemanticsCore.eval_smul (qs := qs) V a ψ).symm

  · intro b
    exact hket b

end GateSemanticsCore

namespace ExtensionSemantics

theorem eval_signExtend_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ExtensionSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b : qs.Basis)
    (hcap : r.CanGrow n)
    (hfresh : ExtReg.FreshFor r n b) :
    ∃ b' : qs.Basis,
      qs.eval (Gate.signExtend r n) (qs.ket b) =
        qs.ket b'
      ∧
      ExtReg.toNat r b' =
        ExtReg.toNat r b
      ∧
      extToInt (r.grow n) b' =
        extToInt r b
      ∧
      (∀ e : ExtReg,
        ExtReg.ActiveDisjoint e (r.grow n) →
        ExtReg.toNat e b' =
          ExtReg.toNat e b) := by

  refine ⟨signExtendBasis r n b, ?_, ?_, ?_, ?_⟩

  · exact
      ExtensionSemantics.eval_signExtend_ket_total
        (qs := qs) r n b

  · exact
      toNat_signExtendBasis r n b

  · exact
      extToInt_grow_signExtendBasis
        r n b hcap hfresh

  · intro e he
    exact
      toNat_signExtendBasis_of_activeDisjoint
        r e n b he

theorem eval_signDealloc_eq_adj
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ExtensionSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (ψ : qs.State) :
    qs.eval (Gate.signDealloc r n) ψ =
      qs.eval
        (Gate.adj (Gate.signExtend r n))
        ψ := by

  apply
    GateSemanticsCore.eval_eq_of_ket_eq
      qs
      (Gate.signDealloc r n)
      (Gate.adj (Gate.signExtend r n))

  intro b

  rw [
    ExtensionSemantics.eval_signDealloc_ket_total
  ]

  have hadj :=
    GateSemanticsCore.eval_adj_apply
      (qs := qs)
      (Gate.signExtend r n)
      (qs.ket (signExtendBasis r n b))

  simp [
    ExtensionSemantics.eval_signExtend_ket_total,
    signExtendBasis_involutive
  ] at hadj

  simpa [signDeallocBasis] using hadj.symm

end ExtensionSemantics


/-! =========================================================
    Generic basis-write arithmetic lemmas
========================================================= -/

lemma tcModWidth_lt_pow
    (w : ℕ) (z : ℤ) :
    tcModWidth w z < 2 ^ w := by
  unfold tcModWidth

  have hM :
      (0 : ℤ) < ((2 ^ w : ℕ) : ℤ) := by
    positivity

  have hnonneg :
      0 ≤ z % ((2 ^ w : ℕ) : ℤ) :=
    Int.emod_nonneg z (ne_of_gt hM)

  have hlt :
      z % ((2 ^ w : ℕ) : ℤ) <
        ((2 ^ w : ℕ) : ℤ) :=
    Int.emod_lt_of_pos z hM

  have hcast :
      ((Int.toNat
        (z % ((2 ^ w : ℕ) : ℤ)) : ℕ) : ℤ)
        =
      z % ((2 ^ w : ℕ) : ℤ) :=
    Int.toNat_of_nonneg hnonneg

  have hlt' :
      ((Int.toNat
        (z % ((2 ^ w : ℕ) : ℤ)) : ℕ) : ℤ)
        <
      ((2 ^ w : ℕ) : ℤ) := by
    rw [hcast]
    exact hlt

  exact_mod_cast hlt'


lemma tcModWidth_lt_ASize_active
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (z : ℤ) :
    tcModWidth r.width z < ASize r.active := by
  simpa [ASize, ExtReg.width] using
    tcModWidth_lt_pow r.width z

lemma shiftLBasis_of_fits
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis)
    (hfit :
      FitsSignedWidth r.width
        ((2 : ℤ) ^ n * extToInt r b)) :
    shiftLBasis r n b =
      RegEncoding.writeNat
        r.active
        (tcModWidth r.width
          ((2 : ℤ) ^ n * extToInt r b))
        b := by
  classical
  simp [shiftLBasis, hfit]

lemma extToInt_writeNat_tcModWidth
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (z : ℤ)
    (b : Basis) :
    extToInt r
        (RegEncoding.writeNat
          r.active
          (tcModWidth r.width z)
          b)
      =
    tcWrapInt r.width z := by

  have hlt :
      tcModWidth r.width z < ASize r.active := by
    simpa [ASize, ExtReg.width] using
      tcModWidth_lt_pow r.width z

  unfold extToInt tcWrapInt ExtReg.toNat

  rw [
    RegEncoding.toNat_writeNat_of_lt
      r.active
      (tcModWidth r.width z)
      b
      hlt
  ]
lemma extToInt_writeNat_active_of_disjoint
    {Basis : Type u}
    [RegEncoding Basis]
    (written observed : ExtReg)
    (v : ℕ)
    (b : Basis)
    (hdisj :
      ExtReg.ActiveDisjoint observed written) :
    extToInt observed
        (RegEncoding.writeNat written.active v b)
      =
    extToInt observed b := by
  unfold extToInt ExtReg.toNat
  rw [
    RegEncoding.toNat_left_write_right
      observed.active written.active
      hdisj b v
  ]

@[simp]
lemma extToInt_negateBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (b : Basis) :
    extToInt r (negateBasis r b)
      =
    tcWrapInt r.width (- extToInt r b) := by
  unfold negateBasis
  exact
    extToInt_writeNat_tcModWidth
      r (- extToInt r b) b


lemma extToInt_negateBasis_of_activeDisjoint
    {Basis : Type u}
    [RegEncoding Basis]
    (r e : ExtReg)
    (b : Basis)
    (hdisj : ExtReg.ActiveDisjoint e r) :
    extToInt e (negateBasis r b) =
      extToInt e b := by
  unfold negateBasis
  exact
    extToInt_writeNat_active_of_disjoint
      r e _ b hdisj

def addScaledValue
    {Basis : Type u}
    [RegEncoding Basis]
    (dst src : ExtReg)
    (negSrc : Bool)
    (sh : ℕ)
    (b : Basis) : ℤ :=
  extToInt dst b
    + (if negSrc then (-1 : ℤ) else 1)
        * (2 : ℤ) ^ sh
        * extToInt src b

lemma addScaledBasis_eq
    {Basis : Type u}
    [RegEncoding Basis]
    (dst src : ExtReg)
    (negSrc : Bool)
    (sh : ℕ)
    (b : Basis)
    (hdisj : ExtReg.ActiveDisjoint dst src) :
    addScaledBasis dst src negSrc sh b
      =
    RegEncoding.writeNat
      dst.active
      (tcModWidth dst.width
        (addScaledValue dst src negSrc sh b))
      b := by
  simp [addScaledBasis, addScaledValue, hdisj]


lemma extToInt_addScaledBasis_dst
    {Basis : Type u}
    [RegEncoding Basis]
    (dst src : ExtReg)
    (negSrc : Bool)
    (sh : ℕ)
    (b : Basis)
    (hdisj : ExtReg.ActiveDisjoint dst src) :
    extToInt dst
        (addScaledBasis dst src negSrc sh b)
      =
    tcWrapInt dst.width
      (addScaledValue dst src negSrc sh b) := by
  rw [addScaledBasis_eq _ _ _ _ _ hdisj]
  exact
    extToInt_writeNat_tcModWidth
      dst (addScaledValue dst src negSrc sh b) b

lemma extToInt_addScaledBasis_src
    {Basis : Type u}
    [RegEncoding Basis]
    (dst src : ExtReg)
    (negSrc : Bool)
    (sh : ℕ)
    (b : Basis)
    (hdisj : ExtReg.ActiveDisjoint dst src) :
    extToInt src
        (addScaledBasis dst src negSrc sh b)
      =
    extToInt src b := by
  rw [addScaledBasis_eq _ _ _ _ _ hdisj]

  apply
    extToInt_writeNat_active_of_disjoint
      dst src

  exact Disjoint.symm hdisj

lemma extToInt_addScaledBasis_of_activeDisjoint
    {Basis : Type u}
    [RegEncoding Basis]
    (dst src e : ExtReg)
    (negSrc : Bool)
    (sh : ℕ)
    (b : Basis)
    (hds : ExtReg.ActiveDisjoint dst src)
    (hed : ExtReg.ActiveDisjoint e dst) :
    extToInt e
        (addScaledBasis dst src negSrc sh b)
      =
    extToInt e b := by
  rw [addScaledBasis_eq _ _ _ _ _ hds]
  exact
    extToInt_writeNat_active_of_disjoint
      dst e _ b hed

lemma extToInt_shiftLBasis_of_activeDisjoint
    {Basis : Type u}
    [RegEncoding Basis]
    (r e : ExtReg)
    (n : ℕ)
    (b : Basis)
    (hdisj : ExtReg.ActiveDisjoint e r) :
    extToInt e (shiftLBasis r n b) =
      extToInt e b := by
  classical

  by_cases hfit :
      FitsSignedWidth r.width
        ((2 : ℤ) ^ n * extToInt r b)

  · rw [shiftLBasis_of_fits r n b hfit]
    exact
      extToInt_writeNat_active_of_disjoint
        r e _ b hdisj

  · have hraw :
        shiftLBasis r n b =
          shiftLBasisRaw r n b := by
      simp [shiftLBasis, hfit]

    rw [hraw]
    unfold shiftLBasisRaw

    exact
      extToInt_writeNat_active_of_disjoint
        r e _ b hdisj

lemma extToInt_shiftRBasis_of_activeDisjoint
    {Basis : Type u}
    [RegEncoding Basis]
    (r e : ExtReg)
    (n : ℕ)
    (b : Basis)
    (hdisj : ExtReg.ActiveDisjoint e r) :
    extToInt e (shiftRBasis r n b) =
      extToInt e b := by
  classical

  by_cases h :
      ∃ q : ℤ,
        extToInt r b = (2 : ℤ) ^ n * q ∧
        FitsSignedWidth r.width q

  · have hbranch :
        shiftRBasis r n b =
          RegEncoding.writeNat
            r.active
            (tcModWidth r.width (Classical.choose h))
            b := by
      simp [shiftRBasis, h]

    rw [hbranch]

    exact
      extToInt_writeNat_active_of_disjoint
        r e _ b hdisj

  · have hraw :
        shiftRBasis r n b =
          shiftRBasisRaw r n b := by
      simp [shiftRBasis, h]

    rw [hraw]
    unfold shiftRBasisRaw

    exact
      extToInt_writeNat_active_of_disjoint
        r e _ b hdisj

lemma extToInt_shiftLBasis_of_fits
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis)
    (hfit :
      FitsSignedWidth r.width
        ((2 : ℤ) ^ n * extToInt r b)) :
    extToInt r (shiftLBasis r n b)
      =
    (2 : ℤ) ^ n * extToInt r b := by
  rw [shiftLBasis_of_fits r n b hfit]

  calc
    extToInt r
        (RegEncoding.writeNat
          r.active
          (tcModWidth r.width
            ((2 : ℤ) ^ n * extToInt r b))
          b)
        =
      tcWrapInt r.width
        ((2 : ℤ) ^ n * extToInt r b) := by
      exact
        extToInt_writeNat_tcModWidth
          r
          ((2 : ℤ) ^ n * extToInt r b)
          b

    _ = (2 : ℤ) ^ n * extToInt r b := by
      exact tcWrapInt_eq_of_fits hfit.1 hfit

lemma shiftRBasis_of_exact
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis)
    (q : ℤ)
    (hexact :
      extToInt r b = (2 : ℤ) ^ n * q)
    (hfit :
      FitsSignedWidth r.width q) :
    shiftRBasis r n b =
      RegEncoding.writeNat
        r.active
        (tcModWidth r.width q)
        b := by
  classical

  have hEx :
      ∃ q' : ℤ,
        extToInt r b = (2 : ℤ) ^ n * q' ∧
        FitsSignedWidth r.width q' :=
    ⟨q, hexact, hfit⟩

  have hchosen :
      extToInt r b =
        (2 : ℤ) ^ n * Classical.choose hEx :=
    (Classical.choose_spec hEx).1

  have hpow :
      (0 : ℤ) < (2 : ℤ) ^ n := by
    positivity

  have hchoose :
      Classical.choose hEx = q := by
    nlinarith [hchosen, hexact]

  simp only [shiftRBasis, dif_pos hEx]
  rw [hchoose]

lemma extToInt_shiftRBasis_of_exact
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis)
    (q : ℤ)
    (hexact :
      extToInt r b = (2 : ℤ) ^ n * q)
    (hfit :
      FitsSignedWidth r.width q) :
    extToInt r (shiftRBasis r n b) = q := by
  rw [shiftRBasis_of_exact r n b q hexact hfit]

  calc
    extToInt r
        (RegEncoding.writeNat
          r.active
          (tcModWidth r.width q)
          b)
        =
      tcWrapInt r.width q := by
        exact extToInt_writeNat_tcModWidth r q b

    _ = q := by
      exact tcWrapInt_eq_of_fits hfit.1 hfit
namespace ArithmeticSemantics

theorem eval_Negate_ket_mod
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ArithmeticSemantics qs]
    (r : ExtReg)
    (b : qs.Basis) :
    ∃ b' : qs.Basis,
      qs.eval (Gate.Negate r) (qs.ket b) =
        qs.ket b'
      ∧
      extToInt r b' =
        tcWrapInt r.width (- extToInt r b)
      ∧
      (∀ e : ExtReg,
        ExtReg.ActiveDisjoint e r →
        extToInt e b' = extToInt e b) := by
  refine ⟨negateBasis r b, ?_, ?_, ?_⟩
  · exact
      ArithmeticSemantics.eval_Negate_ket_total
        (qs := qs) r b
  · exact extToInt_negateBasis r b
  · intro e he
    exact
      extToInt_negateBasis_of_activeDisjoint
        r e b he

theorem eval_AddScaled_ket_mod
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ArithmeticSemantics qs]
    (dst src : ExtReg)
    (negSrc : Bool)
    (sh : ℕ)
    (b : qs.Basis)
    (hdisj : ExtReg.ActiveDisjoint dst src) :
    ∃ b' : qs.Basis,
      qs.eval
          (Gate.AddScaled dst src negSrc sh)
          (qs.ket b)
        =
      qs.ket b'
      ∧
      extToInt dst b' =
        tcWrapInt dst.width
          (extToInt dst b
            + (if negSrc then (-1 : ℤ) else 1)
                * (2 : ℤ) ^ sh
                * extToInt src b)
      ∧
      extToInt src b' = extToInt src b
      ∧
      (∀ e : ExtReg,
        ExtReg.ActiveDisjoint e dst →
        ExtReg.ActiveDisjoint e src →
        extToInt e b' = extToInt e b) := by

  refine
    ⟨addScaledBasis dst src negSrc sh b,
      ?_, ?_, ?_, ?_⟩

  · exact
      ArithmeticSemantics.eval_AddScaled_ket_total
        (qs := qs)
        dst src negSrc sh b

  · simpa [addScaledValue] using
      extToInt_addScaledBasis_dst
        dst src negSrc sh b hdisj

  · exact
      extToInt_addScaledBasis_src
        dst src negSrc sh b hdisj

  · intro e hed _hes
    exact
      extToInt_addScaledBasis_of_activeDisjoint
        dst src e negSrc sh b hdisj hed

theorem eval_ShiftL_ket_exact
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ArithmeticSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b : qs.Basis)
    (hfit :
      FitsSignedWidth r.width
        ((2 : ℤ) ^ n * extToInt r b)) :
    ∃ b' : qs.Basis,
      qs.eval (Gate.ShiftL r n) (qs.ket b) =
        qs.ket b'
      ∧
      extToInt r b' =
        (2 : ℤ) ^ n * extToInt r b
      ∧
      (∀ e : ExtReg,
        ExtReg.ActiveDisjoint e r →
        extToInt e b' = extToInt e b) := by

  refine ⟨shiftLBasis r n b, ?_, ?_, ?_⟩

  · exact
      ArithmeticSemantics.eval_ShiftL_ket_total
        (qs := qs) r n b

  · exact
      extToInt_shiftLBasis_of_fits
        r n b hfit

  · intro e he
    exact
      extToInt_shiftLBasis_of_activeDisjoint
        r e n b he

theorem eval_ShiftR_ket_exact
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ArithmeticSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b : qs.Basis)
    (q : ℤ)
    (hexact :
      extToInt r b = (2 : ℤ) ^ n * q)
    (hfit :
      FitsSignedWidth r.width q) :
    ∃ b' : qs.Basis,
      qs.eval (Gate.ShiftR r n) (qs.ket b) =
        qs.ket b'
      ∧
      extToInt r b' = q
      ∧
      (∀ e : ExtReg,
        ExtReg.ActiveDisjoint e r →
        extToInt e b' = extToInt e b) := by

  refine ⟨shiftRBasis r n b, ?_, ?_, ?_⟩

  · exact
      ArithmeticSemantics.eval_ShiftR_ket_total
        (qs := qs) r n b

  · exact
      extToInt_shiftRBasis_of_exact
        r n b q hexact hfit

  · intro e he
    exact
      extToInt_shiftRBasis_of_activeDisjoint
        r e n b he

end ArithmeticSemantics

end Shor
