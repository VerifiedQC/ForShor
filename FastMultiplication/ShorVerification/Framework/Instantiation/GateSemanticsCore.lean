import FastMultiplication.ShorVerification.Framework.Instantiation.RegEncoding
import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.ZMod.Basic

namespace Shor

namespace ConcreteQSemantics

open QSemantics
open scoped BigOperators

noncomputable local instance concreteRegEncoding :
    RegEncoding concreteQSemantics.Basis := by
  change RegEncoding Basis
  exact instRegEncoding

/-! =========================================================
    Linear extension from computational-basis states
========================================================= -/

noncomputable def extendBasis
    (f : Basis → State) :
    State →ₗ[ℂ] State :=
  Finsupp.linearCombination ℂ f

@[simp]
theorem extendBasis_ket
    (f : Basis → State)
    (b : Basis) :
    extendBasis f (ket b) = f b := by
  simp [extendBasis, ket]

/-! =========================================================
    Concrete basis actions
========================================================= -/

def xBasis
    (q : ℕ)
    (b : Basis) :
    Basis :=
  RegEncoding.writeNat
    (qubitReg q)
    (if RegEncoding.bit q b then 0 else 1)
    b

noncomputable def idealCtrlModMulBasisConcrete
    (c N : ℕ)
    (data : Reg)
    (ctrl : ℕ)
    (b : Basis) :
    Basis := by
  classical
  exact
    if h :
        1 < N ∧
        N ≤ ASize data ∧
        Nat.Coprime c N ∧
        ctrl ∉ data.qubits
    then
      if hx : RegEncoding.toNat data b < N then
        RegEncoding.writeNat data
          (if RegEncoding.bit ctrl b then
            (c * RegEncoding.toNat data b) % N
          else
            RegEncoding.toNat data b)
          b
      else
        b
    else
      b

noncomputable def atomBasisMap
    (U : Gate)
    (b : Basis) :
    Basis :=
  match U with
  | .X q =>
      xBasis q b
  | .CNOT ctrl target =>
      cnotBasis ctrl target b
  | .Toffoli c₁ c₂ target =>
      toffoliBasis c₁ c₂ target b
  | .RadixReverse r m =>
      radixReverseBasis r m b
  | .CmpGeConst N data _ flag =>
      cmpGeConstBasis N data.active flag b
  | .CSubConst N data _ flag =>
      csubConstBasis N data.active flag b
  | .ShiftL r n =>
      shiftLBasis r n b
  | .ShiftR r n =>
      shiftRBasis r n b
  | .Negate r =>
      negateBasis r b
  | .AddScaled dst src negSrc sh =>
      addScaledBasis dst src negSrc sh b
  | .zeroExtend _ _ =>
      b
  | .signExtend r n =>
      signExtendBasis r n b
  | .zeroDealloc _ _ =>
      b
  | .signDealloc r n =>
      signDeallocBasis r n b
  | .idealCtrlModMul c N data ctrl =>
      idealCtrlModMulBasisConcrete c N data ctrl b
  | _ =>
      b

/-!
For basis-permutation gates we define the adjoint using the inverse
permutation.  This definition is total even before bijectivity has been
proved; the primitive inverse theorem below proves that all the concrete
basis maps used by gates are in fact bijective.
-/

noncomputable def inverseBasisMap
    (f : Basis → Basis)
    (b : Basis) :
    Basis := by
  classical
  exact
    if h : ∃ a, f a = b then
      Classical.choose h
    else
      b

/-! =========================================================
    H and QFT basis actions
========================================================= -/

noncomputable def hadamardKet
    (q : ℕ)
    (b : Basis) :
    State :=
  ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
    (
      ket (RegEncoding.writeNat (qubitReg q) 0 b)
      +
      (if RegEncoding.bit q b then (-1 : ℂ) else 1) •
        ket (RegEncoding.writeNat (qubitReg q) 1 b)
    )

noncomputable def qftKet
    (r : ExtReg)
    (b : Basis) :
    State :=
  ((1 / Real.sqrt ((2 ^ r.width : ℕ) : ℝ) : ℂ)) •
    ∑ y : Fin (2 ^ r.width),
      qftPhase (2 ^ r.width) (ExtReg.toNat r b) y.1 •
        ket (RegEncoding.writeNat r.active y.1 b)

noncomputable def iqftKet
    (r : ExtReg)
    (b : Basis) :
    State :=
  ((1 / Real.sqrt ((2 ^ r.width : ℕ) : ℝ) : ℂ)) •
    ∑ y : Fin (2 ^ r.width),
      (starRingEnd ℂ)
          (qftPhase
            (2 ^ r.width)
            (ExtReg.toNat r b)
            y.1) •
        ket (RegEncoding.writeNat r.active y.1 b)

/-! =========================================================
    Diagonal phase gates
========================================================= -/

noncomputable def signedPhaseKet
    (phi : ℝ)
    (x z : ExtReg)
    (b : Basis) :
    State :=
  Complex.exp
      (phi * Complex.I *
        (((extToInt x b : ℤ) : ℂ) *
         (((extToInt z b : ℤ) : ℂ)))) •
    ket b

noncomputable def cSignedPhaseKet
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (b : Basis) :
    State :=
  if RegEncoding.bit ctrl b then
    signedPhaseKet phi x z b
  else
    ket b

/-! =========================================================
    Atomic gate action and atomic adjoint action
========================================================= -/

noncomputable def atomKet
    (U : Gate)
    (b : Basis) :
    State :=
  match U with
  | .H q =>
      hadamardKet q b
  | .QFT r =>
      qftKet r b
  | .SignedPhaseProd phi x z =>
      signedPhaseKet phi x z b
  | .CSignedPhaseProd ctrl phi x z =>
      cSignedPhaseKet ctrl phi x z b
  | _ =>
      ket (atomBasisMap U b)

noncomputable def atomAdjKet
    (U : Gate)
    (b : Basis) :
    State :=
  match U with
  | .H q =>
      hadamardKet q b
  | .QFT r =>
      iqftKet r b
  | .SignedPhaseProd phi x z =>
      signedPhaseKet (-phi) x z b
  | .CSignedPhaseProd ctrl phi x z =>
      cSignedPhaseKet ctrl (-phi) x z b
  | _ =>
      ket (inverseBasisMap (atomBasisMap U) b)

noncomputable def atomEvalLinear
    (U : Gate) :
    State →ₗ[ℂ] State :=
  extendBasis (atomKet U)

noncomputable def atomAdjEvalLinear
    (U : Gate) :
    State →ₗ[ℂ] State :=
  extendBasis (atomAdjKet U)

@[simp]
theorem atomEvalLinear_ket
    (U : Gate)
    (b : Basis) :
    atomEvalLinear U (ket b) = atomKet U b := by
  simp [atomEvalLinear]

@[simp]
theorem atomAdjEvalLinear_ket
    (U : Gate)
    (b : Basis) :
    atomAdjEvalLinear U (ket b) = atomAdjKet U b := by
  simp [atomAdjEvalLinear]

/-! =========================================================
    Full evaluator

    `evalGateAdjLinear U` is the semantic adjoint of `evalGateLinear U`.

    In particular:
      (U ;; V)† = V† ;; U†
    and therefore its evaluator acts in the reverse order.
========================================================= -/

mutual

noncomputable def evalGateLinear :
    Gate → State →ₗ[ℂ] State
  | .id =>
      LinearMap.id
  | .seq U V =>
      (evalGateLinear V).comp (evalGateLinear U)
  | .adj U =>
      evalGateAdjLinear U
  | U =>
      atomEvalLinear U

noncomputable def evalGateAdjLinear :
    Gate → State →ₗ[ℂ] State
  | .id =>
      LinearMap.id
  | .seq U V =>
      (evalGateAdjLinear U).comp (evalGateAdjLinear V)
  | .adj U =>
      evalGateLinear U
  | U =>
      atomAdjEvalLinear U

end

noncomputable def evalGate
    (U : Gate)
    (ψ : State) :
    State :=
  evalGateLinear U ψ

@[simp]
theorem evalGate_id
    (ψ : State) :
    evalGate Gate.id ψ = ψ := by
  rfl

@[simp]
theorem evalGate_seq
    (U V : Gate)
    (ψ : State) :
    evalGate (U ;; V) ψ =
      evalGate V (evalGate U ψ) := by
  rfl

theorem evalGate_add
    (U : Gate)
    (ψ φ : State) :
    evalGate U (ψ + φ) =
      evalGate U ψ + evalGate U φ := by
  exact (evalGateLinear U).map_add ψ φ

theorem evalGate_smul
    (U : Gate)
    (a : ℂ)
    (ψ : State) :
    evalGate U (a • ψ) =
      a • evalGate U ψ := by
  exact (evalGateLinear U).map_smul a ψ

/-! =========================================================
    Genuine primitive-gate proof obligations
========================================================= -/
theorem ket_map_inner_preserved_of_injective
    (f : Basis → Basis)
    (hf : Function.Injective f)
    (b c : Basis) :
    inner ℂ (ket (f b)) (ket (f c)) =
      inner ℂ (ket b) (ket c) := by
  by_cases h : b = c
  · subst c
    have hleft :
        inner ℂ (ket (f b)) (ket (f b)) = (1 : ℂ) := by
      change
        inner ℂ
          (concreteQSemantics.ket (f b))
          (concreteQSemantics.ket (f b)) = (1 : ℂ)
      exact concreteQSemantics.ket_inner_eq_of_eq rfl
    have hright :
        inner ℂ (ket b) (ket b) = (1 : ℂ) := by
      change
        inner ℂ
          (concreteQSemantics.ket b)
          (concreteQSemantics.ket b) = (1 : ℂ)
      exact concreteQSemantics.ket_inner_eq_of_eq rfl
    rw [hleft, hright]
  · have hfc : f b ≠ f c := by
      intro h'
      exact h (hf h')
    have hleft :
        inner ℂ (ket (f b)) (ket (f c)) = (0 : ℂ) := by
      change
        inner ℂ
          (concreteQSemantics.ket (f b))
          (concreteQSemantics.ket (f c)) = (0 : ℂ)
      exact concreteQSemantics.ket_inner_eq_zero_of_ne hfc
    have hright :
        inner ℂ (ket b) (ket c) = (0 : ℂ) := by
      change
        inner ℂ
          (concreteQSemantics.ket b)
          (concreteQSemantics.ket c) = (0 : ℂ)
      exact concreteQSemantics.ket_inner_eq_zero_of_ne h
    rw [hleft, hright]

theorem linearMap_inner_preserved_of_ket
    (L : State →ₗ[ℂ] State)
    (hket :
      ∀ b c : Basis,
        inner ℂ (L (ket b)) (L (ket c)) =
          inner ℂ (ket b) (ket c)) :
    ∀ ψ φ : State,
      inner ℂ (L ψ) (L φ) = inner ℂ ψ φ := by
  intro ψ
  refine concreteQSemantics.state_induction
    (fun ψ =>
      ∀ φ : State,
        inner ℂ (L ψ) (L φ) = inner ℂ ψ φ)
    ?_ ?_ ?_ ?_ ψ
  · intro φ
    simp
  · intro ψ₁ ψ₂ h₁ h₂ φ
    rw [L.map_add, inner_add_left, inner_add_left,
      h₁ φ, h₂ φ]
  · intro a ψ hψ φ
    rw [L.map_smul, inner_smul_left, inner_smul_left,
      hψ φ]
  · intro b
    refine concreteQSemantics.state_induction
      (fun φ =>
        inner ℂ (L (ket b)) (L φ) =
          inner ℂ (ket b) φ)
      ?_ ?_ ?_ ?_
    · simp
    · intro φ₁ φ₂ h₁ h₂
      rw [L.map_add, inner_add_right, inner_add_right,
        h₁, h₂]
    · intro a φ hφ
      rw [L.map_smul, inner_smul_right, inner_smul_right,
        hφ]
    · intro c
      exact hket b c

private theorem inner_ket_self_concrete
    (b : Basis) :
    inner ℂ (ket b) (ket b) = (1 : ℂ) := by
  change
    inner ℂ
      (concreteQSemantics.ket b)
      (concreteQSemantics.ket b) = (1 : ℂ)
  exact concreteQSemantics.ket_inner_eq_of_eq rfl

private theorem inner_ket_ne_concrete
    {b c : Basis}
    (h : b ≠ c) :
    inner ℂ (ket b) (ket c) = (0 : ℂ) := by
  change
    inner ℂ
      (concreteQSemantics.ket b)
      (concreteQSemantics.ket c) = (0 : ℂ)
  exact concreteQSemantics.ket_inner_eq_zero_of_ne h

private lemma signedPhaseScalar_star_mul_self
    (phi : ℝ)
    (x z : ExtReg)
    (b : Basis) :
    (starRingEnd ℂ)
        ((Complex.exp
          (phi * Complex.I *
            (((extToInt x b : ℤ) : ℂ) *
             (((extToInt z b : ℤ) : ℂ)))))) *
      Complex.exp
        (phi * Complex.I *
          (((extToInt x b : ℤ) : ℂ) *
           (((extToInt z b : ℤ) : ℂ)))) =
      1 := by
  let t : ℝ :=
    phi * (extToInt x b : ℝ) * (extToInt z b : ℝ)

  have harg :
      phi * Complex.I *
          (((extToInt x b : ℤ) : ℂ) *
           (((extToInt z b : ℤ) : ℂ)))
        =
      (t : ℂ) * Complex.I := by
    dsimp [t]
    push_cast
    ring

  rw [harg]
  rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.normSq_eq_norm_sq]
  rw [Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem signedPhaseKet_inner_preserved
    (phi : ℝ)
    (x z : ExtReg)
    (b c : Basis) :
    inner ℂ
        (signedPhaseKet phi x z b)
        (signedPhaseKet phi x z c) =
      inner ℂ (ket b) (ket c) := by
  unfold signedPhaseKet

  by_cases hbc : b = c
  · subst c
    rw [inner_smul_left, inner_smul_right, inner_ket_self_concrete]
    rw [mul_one]
    simpa [mul_assoc] using signedPhaseScalar_star_mul_self phi x z b

  · rw [inner_smul_left, inner_smul_right]
    rw [inner_ket_ne_concrete hbc]
    simp

def SameOutside
    (r : Reg)
    (b c : Basis) : Prop :=
  ∀ q, q ∉ r.qubits →
    RegEncoding.bit q b = RegEncoding.bit q c

theorem basis_eq_of_toNat_eq_of_sameOutside
    (r : Reg)
    {b c : Basis}
    (hread :
      RegEncoding.toNat r b =
        RegEncoding.toNat r c)
    (hout : SameOutside r b c) :
    b = c := by
  apply RegEncoding.basis_ext
  intro q

  by_cases hq : q ∈ r.qubits
  · obtain ⟨i, hi⟩ := List.get_of_mem hq

    let j : Fin (regSize r) :=
      ⟨i.1, by
        simp [regSize, Reg.width]⟩

    have hget : r.get j = q := by
      simpa [j, Reg.get, regSize, Reg.width] using hi

    rw [← hget]
    rw [RegEncoding.bit_eq_testBit_toNat]
    rw [RegEncoding.bit_eq_testBit_toNat]
    rw [hread]

  · exact hout q hq

theorem writeNat_sameOutside
    (r : Reg)
    (v : ℕ)
    (b : Basis) :
    SameOutside r (RegEncoding.writeNat r v b) b := by
  intro q hq
  exact RegEncoding.bit_writeNat_out r v b q hq

private lemma sameOutside_refl
    (r : Reg)
    (b : Basis) :
    SameOutside r b b :=
  fun _ _ => rfl

private lemma sameOutside_symm
    (r : Reg)
    {b c : Basis}
    (h : SameOutside r b c) :
    SameOutside r c b :=
  fun q hq => (h q hq).symm

private lemma sameOutside_trans
    (r : Reg)
    {a b c : Basis}
    (h1 : SameOutside r a b)
    (h2 : SameOutside r b c) :
    SameOutside r a c :=
  fun q hq => (h1 q hq).trans (h2 q hq)

private lemma inverseBasisMap_left
    (f : Basis → Basis)
    (hinj : Function.Injective f)
    (b : Basis) :
    inverseBasisMap f (f b) = b := by
  unfold inverseBasisMap
  have hex : ∃ a, f a = f b := ⟨b, rfl⟩
  rw [dif_pos hex]
  exact hinj (Classical.choose_spec hex)

private lemma inverseBasisMap_right
    (f : Basis → Basis)
    {b : Basis}
    (hex : ∃ a, f a = b) :
    f (inverseBasisMap f b) = b := by
  unfold inverseBasisMap
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/--
If `f : Basis → Basis` is injective and only ever changes the bits inside
register `r` (leaving everything outside `r` untouched), then `f` is in
fact surjective: fixing everything outside `r` restricts `f` to a
self-map of a finite set (the basis elements agreeing with `b` outside
`r`), and an injective self-map of a finite set is bijective.
-/
private lemma exists_preimage_of_injective_of_sameOutside
    (f : Basis → Basis)
    (r : Reg)
    (hinj : Function.Injective f)
    (hout : ∀ x, SameOutside r (f x) x)
    (b : Basis) :
    ∃ a, f a = b := by
  classical
  set s : Set Basis :=
    (fun v => RegEncoding.writeNat r v b) '' {i | i < ASize r} with hs_def
  have hsfin : s.Finite :=
    Set.Finite.image (fun v => RegEncoding.writeNat r v b)
      (Set.finite_lt_nat (ASize r))
  have hbmem : b ∈ s := by
    refine ⟨RegEncoding.toNat r b, RegEncoding.toNat_lt_ASize r b, ?_⟩
    apply basis_eq_of_toNat_eq_of_sameOutside r
    · exact RegEncoding.toNat_writeNat_of_lt r _ b (RegEncoding.toNat_lt_ASize r b)
    · exact writeNat_sameOutside r (RegEncoding.toNat r b) b
  have hmaps : Set.MapsTo f s s := by
    rintro x ⟨v, hv, rfl⟩
    have hxb : SameOutside r (RegEncoding.writeNat r v b) b :=
      writeNat_sameOutside r v b
    have hfxb : SameOutside r (f (RegEncoding.writeNat r v b)) b :=
      sameOutside_trans r (hout _) hxb
    refine ⟨RegEncoding.toNat r (f (RegEncoding.writeNat r v b)),
      RegEncoding.toNat_lt_ASize r _, ?_⟩
    apply basis_eq_of_toNat_eq_of_sameOutside r
    · exact RegEncoding.toNat_writeNat_of_lt r _ b (RegEncoding.toNat_lt_ASize r _)
    · exact sameOutside_trans r (writeNat_sameOutside r _ b) (sameOutside_symm r hfxb)
  have hinjOn : Set.InjOn f s := by
    intro x1 _ x2 _ h
    exact hinj h
  have hbij : Set.BijOn f s s :=
    (Set.Finite.injOn_iff_bijOn_of_mapsTo hsfin hmaps).mp hinjOn
  obtain ⟨a, _, hfa⟩ := hbij.surjOn hbmem
  exact ⟨a, hfa⟩

private lemma ket_inner_eq_ite
    (b c : Basis) :
    inner ℂ (ket b) (ket c) =
      if b = c then 1 else 0 := by
  by_cases h : b = c
  · subst c
    simpa using inner_ket_self_concrete b
  · simpa [h] using inner_ket_ne_concrete h

@[simp]
private lemma concrete_bit
    (q : ℕ)
    (b : Basis) :
    RegEncoding.bit q b = b.testBit q := by
  rfl

@[simp]
private lemma concrete_write_qubit_zero
    (q : ℕ)
    (b : Basis) :
    RegEncoding.writeNat (qubitReg q) 0 b =
      writeBit q false b := by
  change writeReg (qubitReg q) 0 b =
    writeBit q false b
  rfl

@[simp]
private lemma concrete_write_qubit_one
    (q : ℕ)
    (b : Basis) :
    RegEncoding.writeNat (qubitReg q) 1 b =
      writeBit q true b := by
  change writeReg (qubitReg q) 1 b =
    writeBit q true b
  rfl

private lemma writeBit_false_ne_true
    (q : ℕ)
    (b c : Basis) :
    writeBit q false b ≠
      writeBit q true c := by
  intro h
  have h' :=
    congrArg (fun n : ℕ => n.testBit q) h
  simp at h'

private lemma writeBit_false_eq_iff_true_eq
    (q : ℕ)
    (b c : Basis) :
    writeBit q false b = writeBit q false c ↔
      writeBit q true b = writeBit q true c := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hp : p = q
    · subst p
      simp
    · have h' :=
        congrArg (fun n : ℕ => n.testBit p) h
      simpa [testBit_writeBit_ne, hp] using h'

  · intro h
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hp : p = q
    · subst p
      simp
    · have h' :=
        congrArg (fun n : ℕ => n.testBit p) h
      simpa [testBit_writeBit_ne, hp] using h'

private lemma eq_of_writeBit_false_eq_of_testBit_eq
    (q : ℕ)
    {b c : Basis}
    (hw :
      writeBit q false b =
        writeBit q false c)
    (hb : b.testBit q = c.testBit q) :
    b = c := by
  apply Nat.eq_of_testBit_eq
  intro p

  by_cases hp : p = q
  · subst p
    exact hb

  · have h' :=
      congrArg (fun n : ℕ => n.testBit p) hw
    simpa [testBit_writeBit_ne, hp] using h'

private lemma hadamard_scale_star_mul
    :
    (starRingEnd ℂ)
        ((1 / Real.sqrt (2 : ℝ) : ℝ) : ℂ) *
      ((1 / Real.sqrt (2 : ℝ) : ℝ) : ℂ) =
      (1 / 2 : ℂ) := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by
    positivity

  have hr :
      (1 / Real.sqrt (2 : ℝ)) *
          (1 / Real.sqrt (2 : ℝ)) =
        (1 / 2 : ℝ) := by
    field_simp [hs]
    nlinarith [
      Real.sq_sqrt
        (show 0 ≤ (2 : ℝ) by norm_num)
    ]

  rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.normSq_ofReal]
  simpa using congrArg (fun x : ℝ => (x : ℂ)) hr

private lemma hadamard_scale_mul :
    ((1 / Real.sqrt (2 : ℝ) : ℂ) *
      (1 / Real.sqrt (2 : ℝ) : ℂ)) =
      (1 / 2 : ℂ) := by
  simpa using hadamard_scale_star_mul

private lemma hadamard_scale_mul_two :
    ((Real.sqrt (2 : ℝ) : ℂ)⁻¹ *
        ((Real.sqrt (2 : ℝ) : ℂ)⁻¹ * (2 : ℂ))) =
      1 := by
  have h :=
    congrArg
      (fun z : ℂ => z * (2 : ℂ))
      hadamard_scale_mul
  norm_num at h
  simpa [one_div, mul_assoc] using h

theorem hadamardKet_inner_preserved
    (q : ℕ)
    (b c : Basis) :
    inner ℂ (hadamardKet q b) (hadamardKet q c) =
      inner ℂ (ket b) (ket c) := by
  rw [show hadamardKet q b =
      ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
        (ket (writeBit q false b) +
          (if b.testBit q then (-1 : ℂ) else 1) •
            ket (writeBit q true b)) by
        simp [hadamardKet]]

  rw [show hadamardKet q c =
      ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
        (ket (writeBit q false c) +
          (if c.testBit q then (-1 : ℂ) else 1) •
            ket (writeBit q true c)) by
        simp [hadamardKet]]

  rw [inner_smul_left, inner_smul_right]
  simp only [
    inner_add_left,
    inner_add_right,
    inner_smul_left,
    inner_smul_right
  ]

  have hcross₁ :
      writeBit q false b ≠
        writeBit q true c :=
    writeBit_false_ne_true q b c

  have hcross₂ :
      writeBit q true b ≠
        writeBit q false c := by
    exact Ne.symm (writeBit_false_ne_true q c b)

  by_cases h0 :
      writeBit q false b =
        writeBit q false c

  · have h1 :
        writeBit q true b =
          writeBit q true c :=
      (writeBit_false_eq_iff_true_eq q b c).1 h0

    by_cases hbc : b = c
    · subst c
      rw [
        ket_inner_eq_ite,
        ket_inner_eq_ite,
        ket_inner_eq_ite,
        ket_inner_eq_ite,
        ket_inner_eq_ite
      ]

      cases hb : b.testBit q
      · simp [writeBit_false_ne_true, Ne.symm hcross₁]
        norm_num
        exact hadamard_scale_mul_two
      · simp [writeBit_false_ne_true, Ne.symm hcross₁]
        norm_num
        exact hadamard_scale_mul_two

    · have hbit :
          b.testBit q ≠ c.testBit q := by
        intro heq
        exact hbc
          (eq_of_writeBit_false_eq_of_testBit_eq
            q h0 heq)

      rw [
        ket_inner_eq_ite,
        ket_inner_eq_ite,
        ket_inner_eq_ite,
        ket_inner_eq_ite,
        ket_inner_eq_ite
      ]

      cases hb : b.testBit q <;>
        cases hc : c.testBit q <;>
        simp_all

  · have h1 :
        writeBit q true b ≠
          writeBit q true c := by
      intro heq
      exact h0
        ((writeBit_false_eq_iff_true_eq q b c).2 heq)

    have hbc : b ≠ c := by
      intro h
      subst c
      exact h0 rfl

    rw [
      ket_inner_eq_ite,
      ket_inner_eq_ite,
      ket_inner_eq_ite,
      ket_inner_eq_ite,
      ket_inner_eq_ite
    ]

    simp [
      h0,
      h1,
      hcross₁,
      hcross₂,
      hbc
    ]

theorem xBasis_injective
    (q : ℕ) :
    Function.Injective (xBasis q) := by
  intro b c h
  unfold xBasis at h

  have hx_b :
      RegEncoding.writeNat
          (qubitReg q)
          (if RegEncoding.bit q b = true then 0 else 1)
          b =
        writeBit q (!b.testBit q) b := by
    change
      writeReg (qubitReg q)
          (if b.testBit q = true then 0 else 1)
          b =
        writeBit q (!b.testBit q) b
    simp [writeReg, writeBits, qubitReg, Reg.singleton]
    by_cases hb : b.testBit q <;> simp [hb]

  have hx_c :
      RegEncoding.writeNat
          (qubitReg q)
          (if RegEncoding.bit q c = true then 0 else 1)
          c =
        writeBit q (!c.testBit q) c := by
    change
      writeReg (qubitReg q)
          (if c.testBit q = true then 0 else 1)
          c =
        writeBit q (!c.testBit q) c
    simp [writeReg, writeBits, qubitReg, Reg.singleton]
    by_cases hc : c.testBit q <;> simp [hc]

  rw [hx_b, hx_c] at h

  apply Nat.eq_of_testBit_eq
  intro p

  by_cases hp : p = q
  · subst p

    have hq :=
      congrArg (fun n : ℕ => n.testBit q) h

    change
      (writeBit q (!b.testBit q) b).testBit q =
        (writeBit q (!c.testBit q) c).testBit q at hq
    simp at hq
    simpa using congrArg (!·) hq

  · have h' :=
      congrArg (fun n : ℕ => n.testBit p) h

    change
      (writeBit q (!b.testBit q) b).testBit p =
        (writeBit q (!c.testBit q) c).testBit p at h'
    simpa [testBit_writeBit_ne, hp] using h'

private lemma cnotBasis_bit_ctrl
    (ctrl target : ℕ)
    (b : Basis) :
    RegEncoding.bit ctrl
        (cnotBasis ctrl target b) =
      RegEncoding.bit ctrl b := by
  by_cases hct : ctrl = target
  · simp [cnotBasis, hct]
  · by_cases hb : RegEncoding.bit ctrl b
    · simp only [cnotBasis, hct, if_false, hb, if_true]
      have hout :=
        RegEncoding.bit_writeNat_out
          (qubitReg target)
          (if RegEncoding.bit target b = true then 0 else 1)
          b ctrl
          (by simpa [qubitReg, Reg.singleton] using hct)
      simpa [hb] using hout
    · simp [cnotBasis, hct, hb]

private lemma toffoliBasis_bit_c₁
    (c₁ c₂ target : ℕ)
    (b : Basis)
    (hbad :
      ¬ (c₁ = c₂ ∨ c₁ = target ∨ c₂ = target)) :
    RegEncoding.bit c₁
        (toffoliBasis c₁ c₂ target b) =
      RegEncoding.bit c₁ b := by
  have hct : c₁ ≠ target := by
    intro h
    exact hbad (Or.inr (Or.inl h))
  by_cases hc :
      RegEncoding.bit c₁ b ∧
        RegEncoding.bit c₂ b
  · simp only [toffoliBasis, hbad, if_false, hc]
    have hout :=
      RegEncoding.bit_writeNat_out
        (qubitReg target)
        (if RegEncoding.bit target b = true then 0 else 1)
        b c₁
        (by simpa [qubitReg, Reg.singleton] using hct)
    simpa [hc.1] using hout
  · have hc' :
        ¬ (b.testBit c₁ = true ∧ b.testBit c₂ = true) := by
      simpa using hc
    simp [toffoliBasis, hbad, hc']

private lemma toffoliBasis_bit_c₂
    (c₁ c₂ target : ℕ)
    (b : Basis)
    (hbad :
      ¬ (c₁ = c₂ ∨ c₁ = target ∨ c₂ = target)) :
    RegEncoding.bit c₂
        (toffoliBasis c₁ c₂ target b) =
      RegEncoding.bit c₂ b := by
  have hct : c₂ ≠ target := by
    intro h
    exact hbad (Or.inr (Or.inr h))
  by_cases hc :
      RegEncoding.bit c₁ b ∧
        RegEncoding.bit c₂ b
  · simp only [toffoliBasis, hbad, if_false, hc]
    have hout :=
      RegEncoding.bit_writeNat_out
        (qubitReg target)
        (if RegEncoding.bit target b = true then 0 else 1)
        b c₂
        (by simpa [qubitReg, Reg.singleton] using hct)
    simpa [hc.2] using hout
  · have hc' :
        ¬ (b.testBit c₁ = true ∧ b.testBit c₂ = true) := by
      simpa using hc
    simp [toffoliBasis, hbad, hc']

theorem cnotBasis_injective_concrete
    (ctrl target : ℕ) :
    Function.Injective
      (cnotBasis
        (Basis := Basis) ctrl target) := by
  intro b c hbc
  by_cases hct : ctrl = target
  · simpa [cnotBasis, hct] using hbc

  have hctrl :
      RegEncoding.bit ctrl b =
        RegEncoding.bit ctrl c := by
    have h :=
      congrArg (RegEncoding.bit ctrl) hbc
    rw [
      cnotBasis_bit_ctrl ctrl target b,
      cnotBasis_bit_ctrl ctrl target c
    ] at h
    exact h

  cases hb : RegEncoding.bit ctrl b <;>
    cases hc : RegEncoding.bit ctrl c

  · simpa [cnotBasis, hct, hb, hc] using hbc

  · simp [hb, hc] at hctrl

  · simp [hb, hc] at hctrl

  · apply xBasis_injective target
    simpa [cnotBasis, hct, hb, hc, xBasis] using hbc

theorem toffoliBasis_injective_concrete
    (c₁ c₂ target : ℕ) :
    Function.Injective
      (toffoliBasis
        (Basis := Basis) c₁ c₂ target) := by
  intro b c hbc

  by_cases hbad :
      c₁ = c₂ ∨ c₁ = target ∨ c₂ = target
  · simpa [toffoliBasis, hbad] using hbc

  have h₁ :
      RegEncoding.bit c₁ b =
        RegEncoding.bit c₁ c := by
    have h :=
      congrArg (RegEncoding.bit c₁) hbc
    rw [
      toffoliBasis_bit_c₁ c₁ c₂ target b hbad,
      toffoliBasis_bit_c₁ c₁ c₂ target c hbad
    ] at h
    exact h

  have h₂ :
      RegEncoding.bit c₂ b =
        RegEncoding.bit c₂ c := by
    have h :=
      congrArg (RegEncoding.bit c₂) hbc
    rw [
      toffoliBasis_bit_c₂ c₁ c₂ target b hbad,
      toffoliBasis_bit_c₂ c₁ c₂ target c hbad
    ] at h
    exact h

  have hcond :
      (RegEncoding.bit c₁ b ∧
          RegEncoding.bit c₂ b) ↔
        (RegEncoding.bit c₁ c ∧
          RegEncoding.bit c₂ c) := by
    constructor
    · rintro ⟨hb₁, hb₂⟩
      constructor
      · rw [← h₁]
        exact hb₁
      · rw [← h₂]
        exact hb₂
    · rintro ⟨hc₁, hc₂⟩
      constructor
      · rw [h₁]
        exact hc₁
      · rw [h₂]
        exact hc₂

  by_cases hb :
      RegEncoding.bit c₁ b ∧
        RegEncoding.bit c₂ b

  · have hc :
        RegEncoding.bit c₁ c ∧
          RegEncoding.bit c₂ c :=
      hcond.mp hb

    apply xBasis_injective target
    have hb' :
        b.testBit c₁ = true ∧ b.testBit c₂ = true := by
      simpa using hb
    have hc' :
        c.testBit c₁ = true ∧ c.testBit c₂ = true := by
      simpa using hc
    simpa [toffoliBasis, hbad, hb', hc', xBasis] using hbc

  · have hc :
        ¬ (RegEncoding.bit c₁ c ∧
          RegEncoding.bit c₂ c) := by
      intro hc
      exact hb (hcond.mpr hc)

    have hb' :
        ¬ (b.testBit c₁ = true ∧ b.testBit c₂ = true) := by
      simpa using hb
    have hc' :
        ¬ (c.testBit c₁ = true ∧ c.testBit c₂ = true) := by
      simpa using hc
    simpa [toffoliBasis, hbad, hb', hc'] using hbc

private lemma disjoint_symm
    {a b : Reg}
    (h : Disjoint a b) :
    Disjoint b a := by
  exact List.Disjoint.symm h

private lemma writeNat_comm_of_disjoint_concrete
    (left right : Reg)
    (hdisj : Disjoint left right)
    (yL yR : ℕ)
    (b : Basis) :
    RegEncoding.writeNat left yL
        (RegEncoding.writeNat right yR b) =
      RegEncoding.writeNat right yR
        (RegEncoding.writeNat left yL b) := by
  apply RegEncoding.basis_ext
  intro q

  have hd := hdisj
  rw [Disjoint, List.disjoint_left] at hd

  by_cases hqL : q ∈ left.qubits
  · have hqR : q ∉ right.qubits := by
      intro hqR
      exact hd hqL hqR

    calc
      RegEncoding.bit q
          (RegEncoding.writeNat left yL
            (RegEncoding.writeNat right yR b))
          =
        RegEncoding.bit q
          (RegEncoding.writeNat left yL b) := by
            exact
              RegEncoding.bit_writeNat_in
                left yL
                (RegEncoding.writeNat right yR b)
                b q hqL
      _ =
        RegEncoding.bit q
          (RegEncoding.writeNat right yR
            (RegEncoding.writeNat left yL b)) := by
            symm
            exact
              RegEncoding.bit_writeNat_out
                right yR
                (RegEncoding.writeNat left yL b)
                q hqR

  · by_cases hqR : q ∈ right.qubits
    · calc
        RegEncoding.bit q
            (RegEncoding.writeNat left yL
              (RegEncoding.writeNat right yR b))
            =
          RegEncoding.bit q
            (RegEncoding.writeNat right yR b) := by
              exact
                RegEncoding.bit_writeNat_out
                  left yL
                  (RegEncoding.writeNat right yR b)
                  q hqL
        _ =
          RegEncoding.bit q
            (RegEncoding.writeNat right yR
              (RegEncoding.writeNat left yL b)) := by
              exact
                RegEncoding.bit_writeNat_in
                  right yR
                  b
                  (RegEncoding.writeNat left yL b)
                  q hqR

    · calc
        RegEncoding.bit q
            (RegEncoding.writeNat left yL
              (RegEncoding.writeNat right yR b))
            =
          RegEncoding.bit q
            (RegEncoding.writeNat right yR b) := by
              exact
                RegEncoding.bit_writeNat_out
                  left yL
                  (RegEncoding.writeNat right yR b)
                  q hqL
        _ = RegEncoding.bit q b := by
              exact
                RegEncoding.bit_writeNat_out
                  right yR b q hqR
        _ =
          RegEncoding.bit q
            (RegEncoding.writeNat left yL b) := by
              symm
              exact
                RegEncoding.bit_writeNat_out
                  left yL b q hqL
        _ =
          RegEncoding.bit q
            (RegEncoding.writeNat right yR
              (RegEncoding.writeNat left yL b)) := by
              symm
              exact
                RegEncoding.bit_writeNat_out
                  right yR
                  (RegEncoding.writeNat left yL b)
                  q hqR

private lemma writeNat_toNat_concrete
    (r : Reg)
    (b : Basis) :
    RegEncoding.writeNat r
        (RegEncoding.toNat r b) b =
      b := by
  apply RegEncoding.basis_ext
  intro q

  by_cases hq : q ∈ r.qubits
  · obtain ⟨i, hi⟩ := List.get_of_mem hq

    let j : Fin (regSize r) :=
      ⟨i.1, by
        simp [regSize, Reg.width]⟩

    have hj : r.get j = q := by
      simpa [Reg.get, j, regSize, Reg.width] using hi

    have hread :
        RegEncoding.toNat r
            (RegEncoding.writeNat r
              (RegEncoding.toNat r b) b)
          =
        RegEncoding.toNat r b := by
      apply RegEncoding.toNat_writeNat_of_lt
      exact RegEncoding.toNat_lt_ASize r b

    calc
      RegEncoding.bit q
          (RegEncoding.writeNat r
            (RegEncoding.toNat r b) b)
          =
        RegEncoding.bit (r.get j)
          (RegEncoding.writeNat r
            (RegEncoding.toNat r b) b) := by
            rw [hj]
      _ =
        Nat.testBit
          (RegEncoding.toNat r
            (RegEncoding.writeNat r
              (RegEncoding.toNat r b) b))
          j.1 :=
            RegEncoding.bit_eq_testBit_toNat
              r
              (RegEncoding.writeNat r
                (RegEncoding.toNat r b) b)
              j
      _ =
        Nat.testBit (RegEncoding.toNat r b) j.1 := by
          rw [hread]
      _ =
        RegEncoding.bit (r.get j) b := by
          symm
          exact RegEncoding.bit_eq_testBit_toNat r b j
      _ = RegEncoding.bit q b := by
          rw [hj]

  · exact
      RegEncoding.bit_writeNat_out
        r (RegEncoding.toNat r b) b q hq

private lemma toNat_left_write_right_concrete
    (left right : Reg)
    (hdisj : Disjoint left right)
    (b : Basis)
    (yR : ℕ) :
    RegEncoding.toNat left
        (RegEncoding.writeNat right yR b) =
      RegEncoding.toNat left b := by
  have hlt :
      RegEncoding.toNat left b < ASize left :=
    RegEncoding.toNat_lt_ASize left b

  have hcomm :=
    writeNat_comm_of_disjoint_concrete
      left right hdisj
      (RegEncoding.toNat left b) yR b

  rw [writeNat_toNat_concrete left b] at hcomm

  have hread :=
    congrArg (RegEncoding.toNat left) hcomm

  have hwritten :
      RegEncoding.toNat left
          (RegEncoding.writeNat left
            (RegEncoding.toNat left b)
            (RegEncoding.writeNat right yR b))
        =
      RegEncoding.toNat left b :=
    RegEncoding.toNat_writeNat_of_lt
      left
      (RegEncoding.toNat left b)
      (RegEncoding.writeNat right yR b)
      hlt

  exact hread.symm.trans hwritten

private lemma tcModWidth_lt_two_pow
    (w : ℕ)
    (z : ℤ) :
    tcModWidth w z < 2 ^ w := by
  unfold tcModWidth
  have hp : (0 : ℤ) < ((2 ^ w : ℕ) : ℤ) := by
    positivity
  have hn :
      0 ≤ z % ((2 ^ w : ℕ) : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hp)
  have hl :
      z % ((2 ^ w : ℕ) : ℤ) <
        ((2 ^ w : ℕ) : ℤ) :=
    Int.emod_lt_of_pos _ hp
  have hcast :
      ((Int.toNat
        (z % ((2 ^ w : ℕ) : ℤ)) : ℕ) : ℤ) =
        z % ((2 ^ w : ℕ) : ℤ) := by
    exact Int.toNat_of_nonneg hn
  exact_mod_cast (hcast ▸ hl)

private lemma tcModWidth_cast_zmod
    (w : ℕ)
    (z : ℤ) :
    ((tcModWidth w z : ℕ) : ZMod (2 ^ w)) =
      (z : ZMod (2 ^ w)) := by
  unfold tcModWidth
  have hp : (0 : ℤ) < ((2 ^ w : ℕ) : ℤ) := by
    positivity
  have hn :
      0 ≤ z % ((2 ^ w : ℕ) : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hp)
  rw [ZMod.natCast_toNat (2 ^ w) hn]
  exact ZMod.intCast_mod z (2 ^ w)

private lemma tcDecodeWidth_cast_zmod
    (w u : ℕ)
    (hu : u < 2 ^ w) :
    ((tcDecodeWidth w u : ℤ) : ZMod (2 ^ w)) =
      (u : ZMod (2 ^ w)) := by
  cases w with
  | zero =>
      have hu0 : u = 0 := by omega
      subst u
      simp [tcDecodeWidth]
  | succ w =>
      by_cases h : u < 2 ^ w
      · simp [tcDecodeWidth, h]
      · rw [
          show tcDecodeWidth (w + 1) u =
              (u : ℤ) - ((2 ^ (w + 1) : ℕ) : ℤ) by
            simp [tcDecodeWidth, h]
        ]
        rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
        rw [ZMod.natCast_self]
        simp

private lemma sameOutside_of_writeNat_eq
    (r : Reg)
    (v w : ℕ)
    (b c : Basis)
    (h :
      RegEncoding.writeNat r v b =
        RegEncoding.writeNat r w c) :
    SameOutside r b c := by
  intro q hq
  calc
    RegEncoding.bit q b =
        RegEncoding.bit q
          (RegEncoding.writeNat r v b) := by
            symm
            exact
              RegEncoding.bit_writeNat_out
                r v b q hq
    _ =
        RegEncoding.bit q
          (RegEncoding.writeNat r w c) := by
            rw [h]
    _ = RegEncoding.bit q c := by
          exact
            RegEncoding.bit_writeNat_out
              r w c q hq

private lemma writeNat_map_injective
    (r : Reg)
    (f : ℕ → ℕ)
    (hbound :
      ∀ u, u < ASize r → f u < ASize r)
    (hinj :
      ∀ u v,
        u < ASize r →
        v < ASize r →
        f u = f v →
        u = v) :
    Function.Injective
      (fun b : Basis =>
        RegEncoding.writeNat r
          (f (RegEncoding.toNat r b)) b) := by
  intro b c h

  have hb :
      RegEncoding.toNat r b < ASize r :=
    RegEncoding.toNat_lt_ASize r b
  have hc :
      RegEncoding.toNat r c < ASize r :=
    RegEncoding.toNat_lt_ASize r c

  have hout :
      f (RegEncoding.toNat r b) =
        f (RegEncoding.toNat r c) := by
    have h' :=
      congrArg (RegEncoding.toNat r) h
    rw [
      RegEncoding.toNat_writeNat_of_lt
        r _ b (hbound _ hb),
      RegEncoding.toNat_writeNat_of_lt
        r _ c (hbound _ hc)
    ] at h'
    exact h'

  have hread :
      RegEncoding.toNat r b =
        RegEncoding.toNat r c :=
    hinj _ _ hb hc hout

  apply basis_eq_of_toNat_eq_of_sameOutside r hread
  exact sameOutside_of_writeNat_eq r _ _ b c h

private lemma active_newBits_disjoint
    (r : ExtReg)
    (n : ℕ) :
    Disjoint r.active (r.newBits n) := by
  have h := r.active_reserve_disjoint
  rw [Disjoint, List.disjoint_left] at h ⊢
  intro q hqa hqn
  exact h hqa (List.mem_of_mem_take hqn)

private lemma writeNat_writeNat_same
    (r : Reg)
    (v w : ℕ)
    (b : Basis) :
    RegEncoding.writeNat r v
        (RegEncoding.writeNat r w b) =
      RegEncoding.writeNat r v b := by
  apply RegEncoding.basis_ext
  intro q
  by_cases hq : q ∈ r.qubits
  · exact
      RegEncoding.bit_writeNat_in
        r v
        (RegEncoding.writeNat r w b)
        b q hq
  · rw [
      RegEncoding.bit_writeNat_out
        r v (RegEncoding.writeNat r w b) q hq,
      RegEncoding.bit_writeNat_out r w b q hq,
      RegEncoding.bit_writeNat_out r v b q hq
    ]

private lemma basis_eq_of_split_reads
    (r : Reg)
    (m : ℕ)
    (hm : m ≤ regSize r)
    {b c : Basis}
    (hL :
      RegEncoding.toNat
          (splitLeft r ⟨m, hm⟩) b =
        RegEncoding.toNat
          (splitLeft r ⟨m, hm⟩) c)
    (hR :
      RegEncoding.toNat
          (splitRight r ⟨m, hm⟩) b =
        RegEncoding.toNat
          (splitRight r ⟨m, hm⟩) c)
    (hout : SameOutside r b c) :
    b = c := by
  apply RegEncoding.basis_ext
  intro q

  by_cases hq : q ∈ r.qubits
  · have hsplit :
        q ∈ (r.qubits.take m) ∨
          q ∈ (r.qubits.drop m) := by
      rw [← List.mem_append]
      simpa using hq

    rcases hsplit with hqL | hqR
    · let left := splitLeft r ⟨m, hm⟩

      have hqL' : q ∈ left.qubits := by
        simpa [left, splitLeft, Reg.take] using hqL

      obtain ⟨i, hi⟩ := List.get_of_mem hqL'

      let j : Fin (regSize left) :=
        ⟨i.1, by simp[regSize, Reg.width] ⟩

      have hget : left.get j = q := by
        simpa [left, j, Reg.get, regSize, Reg.width] using hi

      rw [← hget]
      rw [
        RegEncoding.bit_eq_testBit_toNat,
        RegEncoding.bit_eq_testBit_toNat,
        hL
      ]

    · let right := splitRight r ⟨m, hm⟩

      have hqR' : q ∈ right.qubits := by
        simpa [right, splitRight, Reg.drop] using hqR

      obtain ⟨i, hi⟩ := List.get_of_mem hqR'

      let j : Fin (regSize right) :=
        ⟨i.1, by simp[regSize, Reg.width]⟩

      have hget : right.get j = q := by
        simpa [right, j, Reg.get, regSize, Reg.width] using hi

      rw [← hget]
      rw [
        RegEncoding.bit_eq_testBit_toNat,
        RegEncoding.bit_eq_testBit_toNat,
        hR
      ]

  · exact hout q hq

private lemma radixPacked_injective
    (M : ℕ)
    (hM : 0 < M)
    {a b c d : ℕ}
    (hb : b < M)
    (hd : d < M)
    (h : M * a + b = M * c + d) :
    a = c ∧ b = d := by
  have hmod :=
    congrArg (fun x : ℕ => x % M) h

  have hbd : b = d := by
    simpa [
      Nat.add_mod,
      Nat.mul_mod,
      Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt hd
    ] using hmod

  subst d

  have hmul : M * a = M * c :=
    Nat.add_right_cancel h

  exact ⟨Nat.eq_of_mul_eq_mul_left hM hmul, rfl⟩

private lemma radixReverseIndex_lt
    (r : Reg)
    (m : ℕ)
    (hm : m ≤ regSize r)
    (b : Basis) :
    radixReverseIndex r m hm
        (RegEncoding.toNat
          (splitLeft r ⟨m, hm⟩) b)
        (RegEncoding.toNat
          (splitRight r ⟨m, hm⟩) b)
      <
    ASize r := by
  let sp : SplitPoint r := ⟨m, hm⟩
  let left := splitLeft r sp
  let right := splitRight r sp

  have hL :
      RegEncoding.toNat left b < ASize left :=
    RegEncoding.toNat_lt_ASize left b

  have hR :
      RegEncoding.toNat right b < ASize right :=
    RegEncoding.toNat_lt_ASize right b

  have hwidthL : regSize left = m := by
    simp[regSize, Reg.width] at hm
    simp [left, sp, splitLeft, Reg.take, regSize, Reg.width,hm]

  have hwidthR :
      regSize right = regSize r - m := by
    simp [right, sp, splitRight, Reg.drop, regSize, Reg.width]

  have hsize :
      ASize right * ASize left = ASize r := by
    unfold ASize
    rw [hwidthR, hwidthL, ← pow_add, Nat.sub_add_cancel hm]

  unfold radixReverseIndex
  dsimp [sp, left, right]

  calc
    ASize right * RegEncoding.toNat left b +
          RegEncoding.toNat right b
        <
      ASize right * RegEncoding.toNat left b +
          ASize right :=
      Nat.add_lt_add_left hR _
    _ =
      ASize right *
        (RegEncoding.toNat left b + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
    _ ≤
      ASize right * ASize left := by
        apply Nat.mul_le_mul_left
        exact Nat.succ_le_iff.mpr hL
    _ = ASize r := hsize

theorem radixReverseBasis_injective_concrete
    (r : Reg)
    (m : ℕ) :
    Function.Injective
      (radixReverseBasis
        (Basis := Basis) r m) := by
  intro b c hbc

  by_cases hm : m ≤ regSize r
  · let sp : SplitPoint r := ⟨m, hm⟩
    let left := splitLeft r sp
    let right := splitRight r sp

    have hform :
        RegEncoding.writeNat r
            (radixReverseIndex r m hm
              (RegEncoding.toNat left b)
              (RegEncoding.toNat right b))
            b =
          RegEncoding.writeNat r
            (radixReverseIndex r m hm
              (RegEncoding.toNat left c)
              (RegEncoding.toNat right c))
            c := by
      simpa [radixReverseBasis, hm, sp, left, right] using hbc

    have hidx :
        radixReverseIndex r m hm
            (RegEncoding.toNat left b)
            (RegEncoding.toNat right b)
          =
        radixReverseIndex r m hm
            (RegEncoding.toNat left c)
            (RegEncoding.toNat right c) := by
      have h :=
        congrArg (RegEncoding.toNat r) hform

      rw [
        RegEncoding.toNat_writeNat_of_lt
          r _ b
          (by
            simpa [sp, left, right] using
              radixReverseIndex_lt r m hm b),
        RegEncoding.toNat_writeNat_of_lt
          r _ c
          (by
            simpa [sp, left, right] using
              radixReverseIndex_lt r m hm c)
      ] at h

      exact h

    have hrightPos : 0 < ASize right := by
      simp [ASize]

    have hbR :
        RegEncoding.toNat right b < ASize right :=
      RegEncoding.toNat_lt_ASize right b

    have hcR :
        RegEncoding.toNat right c < ASize right :=
      RegEncoding.toNat_lt_ASize right c

    have hpairs :
        RegEncoding.toNat left b =
            RegEncoding.toNat left c ∧
          RegEncoding.toNat right b =
            RegEncoding.toNat right c := by
      apply radixPacked_injective
        (ASize right) hrightPos hbR hcR

      simpa [radixReverseIndex, sp, left, right] using hidx

    apply basis_eq_of_split_reads r m hm
    · simpa [sp, left] using hpairs.1
    · simpa [sp, right] using hpairs.2
    · exact sameOutside_of_writeNat_eq r _ _ b c hform

  · simpa [radixReverseBasis, hm] using hbc

private lemma extToInt_signExtend_write_eq
    (r : ExtReg)
    (n v : ℕ)
    (b : Basis) :
    extToInt r
        (RegEncoding.writeNat (r.newBits n) v b) =
      extToInt r b := by
  unfold extToInt ExtReg.toNat

  rw [
    toNat_left_write_right_concrete
      r.active
      (r.newBits n)
      (active_newBits_disjoint r n)
      b v
  ]

private lemma signExtendNewValue_lt
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

private lemma toNat_newBits_signExtendBasis
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    RegEncoding.toNat (r.newBits n)
        (signExtendBasis r n b)
      =
    signExtendNewValue r n b := by
  unfold signExtendBasis
  exact
    RegEncoding.toNat_writeNat_of_lt
      (r.newBits n)
      (signExtendNewValue r n b)
      b
      (signExtendNewValue_lt r n b)

private lemma extToInt_signExtendBasis
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    extToInt r (signExtendBasis r n b) =
      extToInt r b := by
  unfold signExtendBasis
  exact extToInt_signExtend_write_eq r n _ b

private lemma signExtendNewValue_signExtendBasis
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

private lemma signExtendBasis_involutive
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    signExtendBasis r n
        (signExtendBasis r n b) =
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
  rw [writeNat_writeNat_same]
  exact writeNat_toNat_concrete (r.newBits n) b

theorem signExtendBasis_injective_concrete
    (r : ExtReg)
    (n : ℕ) :
    Function.Injective
      (signExtendBasis
        (Basis := Basis) r n) := by
  exact
    (show Function.LeftInverse
        (signExtendBasis r n)
        (signExtendBasis r n) from
      fun b => signExtendBasis_involutive r n b).injective

private lemma shiftMask_lt_two_pow
    (n : ℕ)
    (s : Bool) :
    (if s then 2 ^ n - 1 else 0) < 2 ^ n := by
  cases s
  · simp
  · have h := Nat.two_pow_pos n
    simp only [if_true]
    omega

private lemma packed_div
    (n low high : ℕ)
    (hlow : low < 2 ^ n) :
    (low + 2 ^ n * high) / 2 ^ n = high := by
  rw [Nat.add_mul_div_left low high (Nat.two_pow_pos n)]
  rw [Nat.div_eq_of_lt hlow]
  simp

private lemma packed_mod
    (n low high : ℕ)
    (hlow : low < 2 ^ n) :
    (low + 2 ^ n * high) % 2 ^ n = low := by
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hlow

private lemma testBit_packed_high
    (n k low high : ℕ)
    (hk : 0 < k)
    (hlow : low < 2 ^ n) :
    Nat.testBit
        (low + 2 ^ n * high)
        (n + k - 1) =
      Nat.testBit high (k - 1) := by
  rw [Nat.add_comm]
  rw [Nat.testBit_two_pow_mul_add high hlow (n + k - 1)]
  rw [if_neg (by omega)]
  congr 1
  omega

private lemma testBit_packed_low
    (k low high : ℕ)
    (hk : 0 < k)
    (hlow : low < 2 ^ k) :
    Nat.testBit
        (low + 2 ^ k * high)
        (k - 1) =
      Nat.testBit low (k - 1) := by
  rw [Nat.add_comm]
  rw [Nat.testBit_two_pow_mul_add high hlow (k - 1)]
  rw [if_pos (by omega)]

private lemma testBit_mod_two_pow_pred
    (u k : ℕ)
    (hk : 0 < k) :
    Nat.testBit (u % 2 ^ k) (k - 1) =
      Nat.testBit u (k - 1) := by
  rw [Nat.testBit_mod_two_pow]
  simp [show k - 1 < k by omega]

private lemma testBit_div_two_pow_pred
    (u n k : ℕ)
    (hk : 0 < k) :
    Nat.testBit (u / 2 ^ n) (k - 1) =
      Nat.testBit u (n + k - 1) := by
  rw [Nat.testBit_div_two_pow]
  congr 1
  omega

private theorem signedShiftRWord_signedShiftLWord
    (w n u : ℕ)
    (hu : u < 2 ^ w) :
    signedShiftRWord w n
        (signedShiftLWord w n u) =
      u := by
  by_cases hn : n < w
  · let k := w - n
    let kept := u % 2 ^ k
    let dropped := u / 2 ^ k
    let sign := Nat.testBit u (k - 1)
    let mask := if sign then 2 ^ n - 1 else 0

    have hk : 0 < k := by
      dsimp [k]
      omega

    have hw : w = n + k := by
      dsimp [k]
      omega

    have hkept : kept < 2 ^ k := by
      dsimp [kept]
      exact Nat.mod_lt _ (Nat.two_pow_pos k)

    have hdropped : dropped < 2 ^ n := by
      dsimp [dropped]
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).2
      calc
        u < 2 ^ w := hu
        _ = 2 ^ n * 2 ^ k := by
          rw [hw, Nat.pow_add]

    have hmask : mask < 2 ^ n := by
      exact shiftMask_lt_two_pow n sign

    have hxor : Nat.xor dropped mask < 2 ^ n := by
      exact Nat.xor_lt_two_pow hdropped hmask

    have hL :
        signedShiftLWord w n u =
          Nat.xor dropped mask + 2 ^ n * kept := by
      simp [signedShiftLWord, hn, k, kept, dropped, sign, mask]

    have hdiv :
        signedShiftLWord w n u / 2 ^ n = kept := by
      rw [hL]
      exact packed_div n (Nat.xor dropped mask) kept hxor

    have hmod :
        signedShiftLWord w n u % 2 ^ n =
          Nat.xor dropped mask := by
      rw [hL]
      exact packed_mod n (Nat.xor dropped mask) kept hxor

    have hsign :
        Nat.testBit
            (signedShiftLWord w n u)
            (w - 1) =
          sign := by
      rw [hL, hw]
      rw [testBit_packed_high n k
        (Nat.xor dropped mask) kept hk hxor]
      dsimp [kept, sign]
      exact testBit_mod_two_pow_pred u k hk

    rw [signedShiftRWord]
    simp[if_pos hn]
    rw [hdiv, hmod, hsign]

    change
      kept +
          2 ^ k *
            Nat.xor (Nat.xor dropped mask) mask =
        u

    rw [
      show Nat.xor (Nat.xor dropped mask) mask = dropped by
        exact Nat.xor_xor_cancel_right dropped mask
    ]
    dsimp [kept, dropped]
    exact Nat.mod_add_div u (2 ^ k)

  · have hmod : u % 2 ^ w = u :=
      Nat.mod_eq_of_lt hu
    simp [signedShiftLWord, signedShiftRWord, hn, hmod]

private theorem signedShiftLWord_signedShiftRWord
    (w n u : ℕ)
    (hu : u < 2 ^ w) :
    signedShiftLWord w n
        (signedShiftRWord w n u) =
      u := by
  by_cases hn : n < w
  · let k := w - n
    let kept := u / 2 ^ n
    let syndrome := u % 2 ^ n
    let sign := Nat.testBit u (w - 1)
    let mask := if sign then 2 ^ n - 1 else 0

    have hk : 0 < k := by
      dsimp [k]
      omega

    have hw : w = n + k := by
      dsimp [k]
      omega

    have hkept : kept < 2 ^ k := by
      dsimp [kept]
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).2
      calc
        u < 2 ^ w := hu
        _ = 2 ^ k * 2 ^ n := by
          rw [hw, Nat.pow_add, Nat.mul_comm]

    have hsyndrome : syndrome < 2 ^ n := by
      dsimp [syndrome]
      exact Nat.mod_lt _ (Nat.two_pow_pos n)

    have hmask : mask < 2 ^ n := by
      exact shiftMask_lt_two_pow n sign

    have hxor :
        Nat.xor syndrome mask < 2 ^ n := by
      exact Nat.xor_lt_two_pow hsyndrome hmask

    have hR :
        signedShiftRWord w n u =
          kept + 2 ^ k * Nat.xor syndrome mask := by
      simp [signedShiftRWord, hn, k, kept, syndrome, sign, mask]

    have hmod :
        signedShiftRWord w n u % 2 ^ k =
          kept := by
      rw [hR]
      exact packed_mod k kept (Nat.xor syndrome mask) hkept

    have hdiv :
        signedShiftRWord w n u / 2 ^ k =
          Nat.xor syndrome mask := by
      rw [hR]
      exact packed_div k kept (Nat.xor syndrome mask) hkept

    have hsign :
        Nat.testBit
            (signedShiftRWord w n u)
            (k - 1) =
          sign := by
      rw [hR]
      rw [testBit_packed_low k kept
        (Nat.xor syndrome mask) hk hkept]
      dsimp [kept, sign]
      rw [testBit_div_two_pow_pred u n k hk]
      congr 1
      omega

    rw [signedShiftLWord]
    simp [if_pos hn]
    rw [hmod, hdiv, hsign]

    change
      Nat.xor (Nat.xor syndrome mask) mask +
          2 ^ n * kept =
        u

    rw [
      show Nat.xor (Nat.xor syndrome mask) mask = syndrome by
        exact Nat.xor_xor_cancel_right syndrome mask
    ]
    dsimp [syndrome, kept]
    exact Nat.mod_add_div u (2 ^ n)

  · have hmod : u % 2 ^ w = u :=
      Nat.mod_eq_of_lt hu
    simp [signedShiftLWord, signedShiftRWord, hn, hmod]

private lemma extReg_toNat_lt_concrete
    (r : ExtReg)
    (b : Basis) :
    ExtReg.toNat r b < 2 ^ r.width := by
  simpa [ExtReg.toNat, ExtReg.width, ASize] using
    RegEncoding.toNat_lt_ASize r.active b

private lemma tcWrapInt_eq_of_fits
    {w : ℕ}
    {z : ℤ}
    (hw : 0 < w)
    (hfit : FitsSignedWidth w z) :
    tcWrapInt w z = z := by
  rcases Nat.exists_eq_succ_of_ne_zero
      (Nat.pos_iff_ne_zero.mp hw) with ⟨w', rfl⟩
  rcases hfit with ⟨_, hlo, hhi⟩
  unfold signedMin signedMax at *

  have hlo' : -((2 : ℤ) ^ w') ≤ z := by
    have := hlo
    push_cast at this
    simpa using this

  have hhi' : z < (2 : ℤ) ^ w' := by
    have := hhi
    push_cast at this
    simpa using this

  have hpow_pos : (0 : ℤ) < (2 : ℤ) ^ (w' + 1) := by
    positivity

  have h2pow_split :
      (2 : ℤ) ^ (w' + 1) =
        2 * (2 : ℤ) ^ w' := by
    rw [pow_succ]
    ring

  unfold tcWrapInt tcModWidth
  by_cases hz : 0 ≤ z
  · have hz_lt_pow : z < (2 : ℤ) ^ (w' + 1) := by
      rw [h2pow_split]
      linarith

    have hmod :
        z % ((2 ^ (w' + 1) : ℕ) : ℤ) = z := by
      push_cast
      exact Int.emod_eq_of_lt hz hz_lt_pow

    rw [hmod]

    have htoNat : (Int.toNat z : ℤ) = z :=
      Int.toNat_of_nonneg hz

    have htoNat_lt : Int.toNat z < 2 ^ w' := by
      have :
          (Int.toNat z : ℤ) < (2 : ℤ) ^ w' := by
        rw [htoNat]
        exact hhi'
      exact_mod_cast this

    unfold tcDecodeWidth
    simp [htoNat_lt, htoNat]

  · push_neg at hz

    set M : ℤ := (2 : ℤ) ^ (w' + 1) with hM_def

    have hzM_nonneg : 0 ≤ z + M := by
      rw [h2pow_split] at *
      linarith

    have hzM_lt : z + M < M := by
      linarith

    have hmod :
        z % ((2 ^ (w' + 1) : ℕ) : ℤ) = z + M := by
      have hcast :
          ((2 ^ (w' + 1) : ℕ) : ℤ) = M := by
        push_cast
        rfl
      rw [hcast]
      rw [show z = (z + M) + (-1) * M by ring]
      simp
      have := Int.emod_eq_of_lt hzM_nonneg hzM_lt
      simp at this
      exact this

    rw [hmod]

    have htoNat_val :
        (Int.toNat (z + M) : ℤ) = z + M :=
      Int.toNat_of_nonneg hzM_nonneg

    have htoNat_ge :
        ¬ Int.toNat (z + M) < 2 ^ w' := by
      intro hcontra
      have hcontra' :
          (Int.toNat (z + M) : ℤ) < (2 : ℤ) ^ w' := by
        exact_mod_cast hcontra
      rw [htoNat_val] at hcontra'
      rw [h2pow_split] at hcontra'
      linarith

    unfold tcDecodeWidth
    simp [htoNat_ge, htoNat_val]

    have hcast :
        ((2 ^ (w' + 1) : ℕ) : ℤ) = M := by
      push_cast
      rfl

    ring

private lemma extToInt_writeNat_tcModWidth
    (r : ExtReg)
    (z : ℤ)
    (hz : FitsSignedWidth r.width z)
    (b : Basis) :
    extToInt r
        (RegEncoding.writeNat r.active
          (tcModWidth r.width z) b) =
      z := by
  have hwrap :
      extToInt r
          (RegEncoding.writeNat r.active
            (tcModWidth r.width z) b)
        =
      tcWrapInt r.width z := by
    unfold extToInt tcWrapInt ExtReg.toNat
    rw [
      RegEncoding.toNat_writeNat_of_lt
        r.active
        (tcModWidth r.width z)
        b
        (by
          simpa [ASize, ExtReg.width] using
            tcModWidth_lt_two_pow r.width z)
    ]

  exact hwrap.trans (tcWrapInt_eq_of_fits hz.1 hz)


private lemma tcModWidth_extToInt
    (r : ExtReg)
    (b : Basis) :
    tcModWidth r.width (extToInt r b) =
      ExtReg.toNat r b := by
  have hu := extReg_toNat_lt_concrete r b

  unfold extToInt

  cases hw : r.width with
  | zero =>
      have hu0 : ExtReg.toNat r b < 2 ^ 0 := by
        simpa [hw] using hu
      have hzeroNat : ExtReg.toNat r b = 0 := by
        omega
      have hzero :
          RegEncoding.toNat r.active b = 0 := by
        simpa [ExtReg.toNat] using hzeroNat
      simpa [hw, tcDecodeWidth, tcModWidth] using hzeroNat.symm

  | succ w =>
      have hu' : ExtReg.toNat r b < 2 ^ (w + 1) := by
        simpa [hw] using hu
      change
        tcModWidth (w + 1)
            (if _h : ExtReg.toNat r b < 2 ^ w then
              (ExtReg.toNat r b : ℤ)
            else
              (ExtReg.toNat r b : ℤ) -
                ((2 ^ (w + 1) : ℕ) : ℤ))
          =
        ExtReg.toNat r b
      split_ifs with hsign
      · unfold tcModWidth
        have hlt :
            (ExtReg.toNat r b : ℤ) <
              ((2 ^ (w + 1) : ℕ) : ℤ) := by
          exact_mod_cast hu'
        have hn :
            0 ≤
              ((ExtReg.toNat r b : ℤ) %
                ((2 ^ (w + 1) : ℕ) : ℤ)) := by
          exact Int.emod_nonneg _ (by positivity)

        have hmod :
            (ExtReg.toNat r b : ℤ) %
                ((2 ^ (w + 1) : ℕ) : ℤ)
              =
            ExtReg.toNat r b := by
          exact
            Int.emod_eq_of_lt
              (by exact_mod_cast Nat.zero_le (ExtReg.toNat r b))
              hlt

        rw [hmod]
        simp

      · unfold tcModWidth

        have hmod :
            ((ExtReg.toNat r b : ℤ) -
                ((2 ^ (w + 1) : ℕ) : ℤ)) %
                ((2 ^ (w + 1) : ℕ) : ℤ)
              =
            ExtReg.toNat r b := by
          rw [Int.sub_emod]
          have hbase :
              (ExtReg.toNat r b : ℤ) %
                  ((2 ^ (w + 1) : ℕ) : ℤ)
                =
              ExtReg.toNat r b :=
            Int.emod_eq_of_lt
              (by exact_mod_cast Nat.zero_le (ExtReg.toNat r b))
              (by exact_mod_cast hu')
          rw [hbase]
          simp
          simp_all only [not_lt, Nat.cast_pow, Nat.cast_ofNat]

        rw [hmod]
        simp

private theorem shiftRBasisRaw_shiftLBasisRaw
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    shiftRBasisRaw r n
        (shiftLBasisRaw r n b) =
      b := by
  have hu :
      r.toNat b < 2 ^ r.width := by
    simpa [ExtReg.toNat, ExtReg.width, ASize] using
      RegEncoding.toNat_lt_ASize r.active b

  have hL :
      signedShiftLWord r.width n (r.toNat b) <
        2 ^ r.width := by
    by_cases hn : n < r.width
    · let k := r.width - n
      let kept := r.toNat b % 2 ^ k
      let dropped := r.toNat b / 2 ^ k
      let sign := (r.toNat b).testBit (k - 1)
      let mask := if sign then 2 ^ n - 1 else 0

      have hk : 0 < k := by
        dsimp [k]
        omega

      have hw : r.width = n + k := by
        dsimp [k]
        omega

      have hkept : kept < 2 ^ k := by
        dsimp [kept]
        exact Nat.mod_lt _ (Nat.two_pow_pos k)

      have hdropped : dropped < 2 ^ n := by
        dsimp [dropped]
        apply Nat.div_lt_of_lt_mul
        calc
          r.toNat b < 2 ^ r.width := hu
          _ = 2 ^ k * 2 ^ n := by
            rw [hw, Nat.pow_add, Nat.mul_comm]

      have hmask : mask < 2 ^ n := by
        have hp : 0 < 2 ^ n := Nat.two_pow_pos n
        cases hs : sign <;> simp [mask, hs]

      have hxor :
          Nat.xor dropped mask < 2 ^ n :=
        Nat.xor_lt_two_pow hdropped hmask

      have hform :
          signedShiftLWord r.width n (r.toNat b) =
            Nat.xor dropped mask + 2 ^ n * kept := by
        simp [
          signedShiftLWord, hn, k, kept,
          dropped, sign, mask
        ]

      rw [hform, hw, Nat.pow_add]

      calc
        Nat.xor dropped mask + 2 ^ n * kept
            < 2 ^ n + 2 ^ n * kept :=
          Nat.add_lt_add_right hxor _
        _ = 2 ^ n * (kept + 1) := by
          simp [Nat.mul_add, Nat.add_comm]
        _ ≤ 2 ^ n * 2 ^ k := by
          exact Nat.mul_le_mul_left _
            (Nat.succ_le_iff.mpr hkept)

    · simp only [signedShiftLWord, hn]
      exact Nat.mod_lt _ (Nat.two_pow_pos r.width)

  have hL' :
      signedShiftLWord r.width n
          (RegEncoding.toNat r.active b) <
        ASize r.active := by
    simpa [ExtReg.toNat, ExtReg.width, ASize] using hL

  have hu' :
      RegEncoding.toNat r.active b <
        2 ^ r.width := by
    simpa [ExtReg.toNat] using hu

  unfold shiftRBasisRaw shiftLBasisRaw

  change
    RegEncoding.writeNat r.active
        (signedShiftRWord r.width n
          (RegEncoding.toNat r.active
            (RegEncoding.writeNat r.active
              (signedShiftLWord r.width n
                (RegEncoding.toNat r.active b))
              b)))
        (RegEncoding.writeNat r.active
          (signedShiftLWord r.width n
            (RegEncoding.toNat r.active b))
          b)
      =
    b

  rw [
    RegEncoding.toNat_writeNat_of_lt
      r.active
      (signedShiftLWord r.width n
        (RegEncoding.toNat r.active b))
      b
      hL'
  ]

  rw [
    signedShiftRWord_signedShiftLWord
      r.width n
      (RegEncoding.toNat r.active b)
      hu'
  ]

  rw [writeNat_writeNat_same]

  exact writeNat_toNat_concrete r.active b

private theorem shiftLBasisRaw_shiftRBasisRaw
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    shiftLBasisRaw r n
        (shiftRBasisRaw r n b) =
      b := by
  have hu :
      r.toNat b < 2 ^ r.width := by
    simpa [ExtReg.toNat, ExtReg.width, ASize] using
      RegEncoding.toNat_lt_ASize r.active b

  have hR :
      signedShiftRWord r.width n (r.toNat b) <
        2 ^ r.width := by
    by_cases hn : n < r.width
    · let k := r.width - n
      let kept := r.toNat b / 2 ^ n
      let syndrome := r.toNat b % 2 ^ n
      let sign := (r.toNat b).testBit (r.width - 1)
      let mask := if sign then 2 ^ n - 1 else 0

      have hk : 0 < k := by
        dsimp [k]
        omega

      have hw : r.width = n + k := by
        dsimp [k]
        omega

      have hkept : kept < 2 ^ k := by
        dsimp [kept]
        apply Nat.div_lt_of_lt_mul
        calc
          r.toNat b < 2 ^ r.width := hu
          _ = 2 ^ n * 2 ^ k := by
            rw [hw, Nat.pow_add]

      have hsyndrome : syndrome < 2 ^ n := by
        dsimp [syndrome]
        exact Nat.mod_lt _ (Nat.two_pow_pos n)

      have hmask : mask < 2 ^ n := by
        have hp : 0 < 2 ^ n := Nat.two_pow_pos n
        cases hs : sign <;> simp [mask, hs]

      have hxor :
          Nat.xor syndrome mask < 2 ^ n :=
        Nat.xor_lt_two_pow hsyndrome hmask

      have hform :
          signedShiftRWord r.width n (r.toNat b) =
            kept + 2 ^ k * Nat.xor syndrome mask := by
        simp [
          signedShiftRWord, hn, k, kept,
          syndrome, sign, mask
        ]

      rw [hform, hw, Nat.pow_add]

      calc
        kept + 2 ^ k * Nat.xor syndrome mask
            <
          2 ^ k + 2 ^ k * Nat.xor syndrome mask :=
            Nat.add_lt_add_right hkept _
        _ =
          2 ^ k * (Nat.xor syndrome mask + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            omega
        _ ≤
          2 ^ k * 2 ^ n := by
            exact Nat.mul_le_mul_left _
              (Nat.succ_le_iff.mpr hxor)
        _ =
          2 ^ n * 2 ^ k := by
            exact Nat.mul_comm _ _

    · simp only [signedShiftRWord, hn]
      exact Nat.mod_lt _ (Nat.two_pow_pos r.width)

  have hR' :
      signedShiftRWord r.width n
          (RegEncoding.toNat r.active b) <
        ASize r.active := by
    simpa [ExtReg.toNat, ExtReg.width, ASize] using hR

  have hu' :
      RegEncoding.toNat r.active b <
        2 ^ r.width := by
    simpa [ExtReg.toNat] using hu

  unfold shiftLBasisRaw shiftRBasisRaw

  change
    RegEncoding.writeNat r.active
        (signedShiftLWord r.width n
          (RegEncoding.toNat r.active
            (RegEncoding.writeNat r.active
              (signedShiftRWord r.width n
                (RegEncoding.toNat r.active b))
              b)))
        (RegEncoding.writeNat r.active
          (signedShiftRWord r.width n
            (RegEncoding.toNat r.active b))
          b)
      =
    b

  rw [
    RegEncoding.toNat_writeNat_of_lt
      r.active
      (signedShiftRWord r.width n
        (RegEncoding.toNat r.active b))
      b
      hR'
  ]

  rw [
    signedShiftLWord_signedShiftRWord
      r.width n
      (RegEncoding.toNat r.active b)
      hu'
  ]

  rw [writeNat_writeNat_same]

  exact writeNat_toNat_concrete r.active b


private lemma testBit_pred_iff_ge
    (k m : ℕ) (hk : 0 < k) (hm : m < 2 ^ k) :
    Nat.testBit m (k - 1) = true ↔ 2 ^ (k - 1) ≤ m := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  have hred : k' + 1 - 1 = k' := by omega
  simp only [hred]
  have hlow : m % 2 ^ k' < 2 ^ k' :=
    Nat.mod_lt _ (Nat.two_pow_pos k')
  have hsplit : m % 2 ^ k' + 2 ^ k' * (m / 2 ^ k') = m :=
    Nat.mod_add_div m (2 ^ k')
  have h2pow : (2 : ℕ) ^ (k' + 1) = 2 * 2 ^ k' := pow_succ' 2 k'
  have hhigh : m / 2 ^ k' < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k'), ← h2pow]
    exact hm
  have hbit : Nat.testBit m k' = Nat.testBit (m / 2 ^ k') 0 := by
    conv_lhs => rw [← hsplit]
    have h :=
      testBit_packed_high k' 1 (m % 2 ^ k') (m / 2 ^ k') (by norm_num) hlow
    simpa using h
  rw [hbit]
  constructor
  · intro h
    by_contra hge
    push_neg at hge
    rw [Nat.div_eq_of_lt hge] at h
    exact absurd h (by decide)
  · intro hge
    have h1 : ¬ (m / 2 ^ k' < 1) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k'), one_mul]
      omega
    have hq : m / 2 ^ k' = 1 := by omega
    rw [hq]; decide

private lemma tcDecodeWidth_eq_of_pos (w u : ℕ) (hw : 0 < w) :
    tcDecodeWidth w u =
      if u < 2 ^ (w - 1) then (u : ℤ) else (u : ℤ) - ((2 ^ w : ℕ) : ℤ) := by
  obtain ⟨w', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hw)
  simp [tcDecodeWidth]

private lemma tcDecodeWidth_fitsSignedWidth
    {w u : ℕ} (hw : 0 < w) (hu : u < 2 ^ w) :
    FitsSignedWidth w (tcDecodeWidth w u) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hw)
  have hpow_pos : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by
    exact_mod_cast Nat.two_pow_pos k
  have huZ : (u : ℤ) < ((2 ^ (k + 1) : ℕ) : ℤ) := by
    exact_mod_cast hu
  have hpow_succZ : ((2 ^ (k + 1) : ℕ) : ℤ) = ((2 ^ k : ℕ) : ℤ) * 2 := by
    have hpow_succNat : (2 ^ (k + 1) : ℕ) = 2 ^ k * 2 := by
      rw [pow_succ]
    exact_mod_cast hpow_succNat
  refine ⟨Nat.succ_pos k, ?_, ?_⟩
  · rw [tcDecodeWidth_eq_of_pos (k + 1) u (Nat.succ_pos k)]
    simp only [signedMin, Nat.add_sub_cancel_right]
    split_ifs with hsign
    · have h0 : (0 : ℤ) ≤ (u : ℤ) := Nat.cast_nonneg u
      change -((2 ^ k : ℕ) : ℤ) ≤ (u : ℤ)
      linarith
    · push_neg at hsign
      have hge : ((2 ^ k : ℕ) : ℤ) ≤ (u : ℤ) := by
        exact_mod_cast hsign
      rw [hpow_succZ]
      change -((2 ^ k : ℕ) : ℤ) ≤ (u : ℤ) - ((2 ^ k : ℕ) : ℤ) * 2
      linarith
  · rw [tcDecodeWidth_eq_of_pos (k + 1) u (Nat.succ_pos k)]
    simp only [signedMax, Nat.add_sub_cancel_right]
    split_ifs with hsign
    · exact_mod_cast hsign
    · rw [hpow_succZ] at huZ
      linarith

private lemma tcModWidth_natCast_of_lt (w v : ℕ) (hv : v < 2 ^ w) :
    tcModWidth w (v : ℤ) = v := by
  unfold tcModWidth
  rw [Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le v) (by exact_mod_cast hv)]
  simp

private lemma tcModWidth_natCast_sub_two_pow_of_lt (w v : ℕ) (hv : v < 2 ^ w) :
    tcModWidth w ((v : ℤ) - ((2 ^ w : ℕ) : ℤ)) = v := by
  unfold tcModWidth
  have heq :
      (v : ℤ) - ((2 ^ w : ℕ) : ℤ) =
        (v : ℤ) + ((2 ^ w : ℕ) : ℤ) * (-1) := by ring
  rw [heq, Int.add_mul_emod_self_left]
  rw [Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le v) (by exact_mod_cast hv)]
  simp

private lemma key_shiftL
    (w n u : ℕ)
    (hu : u < 2 ^ w)
    (hfit : FitsSignedWidth w ((2 : ℤ) ^ n * tcDecodeWidth w u)) :
    tcModWidth w ((2 : ℤ) ^ n * tcDecodeWidth w u) =
      signedShiftLWord w n u := by
  have hw : 0 < w := hfit.1
  by_cases hn : n < w
  · obtain ⟨k, hk_def⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : 0 < k := by omega
    have hu_split : u / 2 ^ k * 2 ^ k + u % 2 ^ k = u := by
      rw [mul_comm]
      exact Nat.div_add_mod u (2 ^ k)
    set kept := u % 2 ^ k with hkept_def
    set dropped := u / 2 ^ k with hdropped_def
    have hu_split' : u = dropped * 2 ^ k + kept := hu_split.symm
    have hkept_lt : kept < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have hdropped_lt : dropped < 2 ^ n := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).2
      calc u < 2 ^ w := hu
        _ = 2 ^ n * 2 ^ k := by rw [hk_def, Nat.pow_add]
    have hsigneq : Nat.testBit u (k - 1) = true ↔ 2 ^ (k - 1) ≤ kept := by
      rw [← testBit_mod_two_pow_pred u k hk]
      exact testBit_pred_iff_ge k kept hk hkept_lt
    set sign := Nat.testBit u (k - 1) with hsign_def
    set mask : ℕ := if sign then 2 ^ n - 1 else 0 with hmask_def
    have hmask_lt : mask < 2 ^ n := shiftMask_lt_two_pow n sign
    have hxor_lt : Nat.xor dropped mask < 2 ^ n :=
      Nat.xor_lt_two_pow hdropped_lt hmask_lt
    have hwn : w - n = k := by omega
    have hLraw :
        signedShiftLWord w n u = Nat.xor dropped mask + 2 ^ n * kept := by
      simp [signedShiftLWord, hn, hwn, hkept_def, hdropped_def, hsign_def, hmask_def]
    rw [tcDecodeWidth_eq_of_pos w u hw] at hfit
    rw [hLraw, tcDecodeWidth_eq_of_pos w u hw]
    have hw1eq : (2 : ℤ) ^ (w - 1) = (2 : ℤ) ^ n * 2 ^ (k - 1) := by
      rw [show w - 1 = n + (k - 1) from by omega, pow_add]
    have hw1eq_nat : (2 : ℕ) ^ (w - 1) = 2 ^ n * 2 ^ (k - 1) := by
      rw [show w - 1 = n + (k - 1) from by omega, Nat.pow_add]
    have hwkeq : (2 : ℤ) ^ w = (2 : ℤ) ^ n * 2 ^ k := by rw [hk_def, pow_add]
    have hwkeq_nat : (2 : ℕ) ^ w = 2 ^ n * 2 ^ k := by rw [hk_def, Nat.pow_add]
    have hcast_u : (u : ℤ) = (dropped : ℤ) * 2 ^ k + (kept : ℤ) := by
      exact_mod_cast hu_split'
    by_cases hcmp : u < 2 ^ (w - 1)
    · rw [if_pos hcmp] at hfit ⊢
      have hub := hfit.2.2
      unfold signedMax at hub
      rw [hw1eq_nat] at hub
      push_cast at hub
      have hupos : (0 : ℤ) < 2 ^ n := by positivity
      have hult : (u : ℤ) < 2 ^ (k - 1) := by nlinarith [hcast_u]
      have hult' : u < 2 ^ (k - 1) := by exact_mod_cast hult
      have hdropped0 : dropped = 0 := by
        by_contra hne
        have h1 : 1 ≤ dropped := Nat.one_le_iff_ne_zero.mpr hne
        have hge : 2 ^ k ≤ u := by
          calc (2 : ℕ) ^ k = 1 * 2 ^ k := (one_mul _).symm
            _ ≤ dropped * 2 ^ k := Nat.mul_le_mul_right _ h1
            _ ≤ u := by rw [hu_split']; omega
        have h2k : (2 : ℕ) ^ (k - 1) < 2 ^ k :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      have hueq : u = kept := by
        have := hu_split'; rw [hdropped0] at this; omega
      have hkeptlt : kept < 2 ^ (k - 1) := by rw [← hueq]; exact hult'
      have hsignfalse : sign = false := by
        rw [hsign_def, Bool.eq_false_iff]
        intro hcontra
        exact absurd (hsigneq.mp hcontra) (by omega)
      have hmaskeq : mask = dropped := by
        simp [hmask_def, hsignfalse, hdropped0]
      have hxor_self : Nat.xor dropped dropped = 0 := by
        exact Nat.xor_self dropped
      rw [hmaskeq, hxor_self, zero_add]
      rw [hueq]
      have hbound : 2 ^ n * kept < 2 ^ w := by
        have hstep2 : 2 ^ n * (kept + 1) ≤ 2 ^ n * 2 ^ k :=
          Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hkept_lt)
        have hexpand : 2 ^ n * (kept + 1) = 2 ^ n * kept + 2 ^ n := by ring
        have hpos2 : 0 < 2 ^ n := Nat.two_pow_pos n
        rw [hwkeq_nat]
        omega
      have hcastgoal : (2 : ℤ) ^ n * (kept : ℤ) = ((2 ^ n * kept : ℕ) : ℤ) := by
        push_cast; ring
      rw [hcastgoal]
      exact tcModWidth_natCast_of_lt w (2 ^ n * kept) hbound
    · rw [if_neg hcmp] at hfit ⊢
      have hlb := hfit.2.1
      unfold signedMin at hlb
      rw [hw1eq_nat] at hlb
      push_cast at hlb
      have hnpos : (0 : ℤ) < 2 ^ n := by positivity
      have hu_lb : (2 : ℤ) ^ w ≤ (u : ℤ) + 2 ^ (k - 1) := by
        nlinarith [hlb, hwkeq, hcast_u]
      have hu_lb' : 2 ^ w ≤ u + 2 ^ (k - 1) := by exact_mod_cast hu_lb
      have hdropped_eq : dropped = 2 ^ n - 1 := by
        have hpos2 : 0 < 2 ^ n := Nat.two_pow_pos n
        by_contra hne
        have hcon : dropped + 1 ≤ 2 ^ n - 1 := by omega
        have hstep : (dropped + 1) * 2 ^ k ≤ (2 ^ n - 1) * 2 ^ k :=
          Nat.mul_le_mul_right _ hcon
        have hexpand1 : (dropped + 1) * 2 ^ k = dropped * 2 ^ k + 2 ^ k := by ring
        have hexpand2 :
            (2 ^ n - 1) * 2 ^ k + 2 ^ k = 2 ^ n * 2 ^ k := by
          calc
            (2 ^ n - 1) * 2 ^ k + 2 ^ k =
                (2 ^ n - 1 + 1) * 2 ^ k := by ring
            _ = 2 ^ n * 2 ^ k := by
              congr 1
              omega
        have h2k1 : (2 : ℕ) ^ (k - 1) < 2 ^ k :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
        rw [← hwkeq_nat] at hexpand2
        omega
      have hu_eq2 : u = (2 ^ n - 1) * 2 ^ k + kept := by rw [hu_split', hdropped_eq]
      have hkept_ge : 2 ^ (k - 1) ≤ kept := by
        have heq2k : (2 : ℕ) ^ k = 2 ^ (k - 1) * 2 := by
          have hk1 : 1 ≤ k := Nat.succ_le_iff.mpr hk
          calc
            (2 : ℕ) ^ k = 2 ^ ((k - 1) + 1) := by
              exact (congrArg (fun e => (2 : ℕ) ^ e) (Nat.sub_add_cancel hk1)).symm
            _ = 2 ^ (k - 1) * 2 := by
              rw [pow_succ]
        have hexpand2 :
            (2 ^ n - 1) * 2 ^ k + 2 ^ k = 2 ^ n * 2 ^ k := by
          calc
            (2 ^ n - 1) * 2 ^ k + 2 ^ k =
                (2 ^ n - 1 + 1) * 2 ^ k := by ring
            _ = 2 ^ n * 2 ^ k := by
              congr 1
              have hpos2 : 0 < 2 ^ n := Nat.two_pow_pos n
              omega
        have hbound := hu_lb'
        rw [hu_eq2, hwkeq_nat, ← hexpand2] at hbound
        omega
      have hsigntrue : sign = true := by
        rw [hsign_def]; exact hsigneq.mpr hkept_ge
      have hmaskeq2 : mask = dropped := by
        simp [hmask_def, hsigntrue, hdropped_eq]
      have hxor_self : Nat.xor dropped dropped = 0 := by
        exact Nat.xor_self dropped
      rw [hmaskeq2, hxor_self, zero_add]
      have hn1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
      have hcast_eq :
          (2 : ℤ) ^ n * ((u : ℤ) - ((2 ^ w : ℕ) : ℤ)) =
            ((2 ^ n * kept : ℕ) : ℤ) - ((2 ^ w : ℕ) : ℤ) := by
        have hcast_u2 :
            (u : ℤ) = ((2 ^ n - 1 : ℕ) : ℤ) * 2 ^ k + (kept : ℤ) := by
          have := hu_eq2
          exact_mod_cast this
        have hn1cast : ((2 ^ n - 1 : ℕ) : ℤ) = (2 : ℤ) ^ n - 1 := by
          push_cast [Nat.cast_sub hn1]
          ring
        rw [hcast_u2, hn1cast]
        push_cast
        rw [hwkeq]
        ring
      rw [hcast_eq]
      have hbound2 : 2 ^ n * kept < 2 ^ w := by
        have hstep2 : 2 ^ n * (kept + 1) ≤ 2 ^ n * 2 ^ k :=
          Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hkept_lt)
        have hexpand : 2 ^ n * (kept + 1) = 2 ^ n * kept + 2 ^ n := by ring
        have hpos2 : 0 < 2 ^ n := Nat.two_pow_pos n
        rw [hwkeq_nat]
        omega
      exact tcModWidth_natCast_sub_two_pow_of_lt w (2 ^ n * kept) hbound2
  · push_neg at hn
    have hLraw : signedShiftLWord w n u = u := by
      simp [signedShiftLWord, not_lt.mpr hn, Nat.mod_eq_of_lt hu]
    rw [hLraw]
    have h2n : (2 : ℤ) ^ w ≤ (2 : ℤ) ^ n := by
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
      exact_mod_cast this
    have h2w : (2 : ℤ) ^ (w - 1) < (2 : ℤ) ^ w := by
      have : (2 : ℕ) ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
      exact_mod_cast this
    set z := tcDecodeWidth w u with hz_def
    have hfit1 : -(2 : ℤ) ^ (w - 1) ≤ (2 : ℤ) ^ n * z := by
      have := hfit.2.1; simpa [signedMin] using this
    have hfit2 : (2 : ℤ) ^ n * z < (2 : ℤ) ^ (w - 1) := by
      have := hfit.2.2; simpa [signedMax] using this
    have hz0 : z = 0 := by
      by_contra hzne
      rcases lt_or_gt_of_ne hzne with hneg | hpos
      · have hz1 : z ≤ -1 := by omega
        have hb : (2 : ℤ) ^ n * z ≤ (2 : ℤ) ^ n * (-1) :=
          mul_le_mul_of_nonneg_left hz1 (by positivity)
        have hb2 : (2 : ℤ) ^ n * (-1) = -(2 : ℤ) ^ n := by ring
        linarith [hfit1, hb, hb2, h2n, h2w]
      · have hz1 : (1 : ℤ) ≤ z := by omega
        have hb : (2 : ℤ) ^ n * 1 ≤ (2 : ℤ) ^ n * z :=
          mul_le_mul_of_nonneg_left hz1 (by positivity)
        have hb2 : (2 : ℤ) ^ n * 1 = (2 : ℤ) ^ n := by ring
        linarith [hfit2, hb, hb2, h2n, h2w]
    have hu0 : u = 0 := by
      by_contra hune
      have h1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hune
      rw [hz_def, tcDecodeWidth_eq_of_pos w u hw] at hz0
      by_cases hcmp : u < 2 ^ (w - 1)
      · rw [if_pos hcmp] at hz0
        have : u = 0 := by exact_mod_cast hz0
        omega
      · rw [if_neg hcmp] at hz0
        have heq : (u : ℤ) = ((2 ^ w : ℕ) : ℤ) := by linarith [hz0]
        have : u = 2 ^ w := by exact_mod_cast heq
        omega
    rw [hz0, hu0]
    simp [tcModWidth]

private lemma shiftLBasis_eq_shiftLBasisRaw_concrete
    (r : ExtReg) (n : ℕ) (b : Basis) :
    shiftLBasis r n b = shiftLBasisRaw r n b := by
  classical
  by_cases hfit : FitsSignedWidth r.width ((2 : ℤ) ^ n * extToInt r b)
  · have hLdef :
        shiftLBasis r n b =
          RegEncoding.writeNat r.active
            (tcModWidth r.width ((2 : ℤ) ^ n * extToInt r b)) b := by
      simp [shiftLBasis, hfit]
    rw [hLdef]
    unfold shiftLBasisRaw
    congr 1
    have hu : ExtReg.toNat r b < 2 ^ r.width := extReg_toNat_lt_concrete r b
    have hzeq : extToInt r b = tcDecodeWidth r.width (ExtReg.toNat r b) := rfl
    rw [hzeq] at hfit ⊢
    exact key_shiftL r.width n (ExtReg.toNat r b) hu hfit
  · simp [shiftLBasis, hfit]

private lemma key_shiftR
    (w n u : ℕ)
    (hu : u < 2 ^ w)
    (q : ℤ)
    (hq_eq : tcDecodeWidth w u = (2 : ℤ) ^ n * q)
    (hq_fit : FitsSignedWidth w q) :
    tcModWidth w q = signedShiftRWord w n u := by
  have hw : 0 < w := hq_fit.1
  by_cases hn : n < w
  · obtain ⟨k, hk_def⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : 0 < k := by omega
    rw [tcDecodeWidth_eq_of_pos w u hw] at hq_eq
    have hwk : (2 : ℤ) ^ w = 2 ^ n * 2 ^ k := by rw [hk_def, pow_add]
    have hwk' : (2 : ℤ) ^ k * 2 ^ n = 2 ^ w := by rw [hwk]; ring
    have hsigneq : Nat.testBit u (w - 1) = true ↔ 2 ^ (w - 1) ≤ u :=
      testBit_pred_iff_ge w u hw hu
    have hRraw :
        signedShiftRWord w n u =
          u / 2 ^ n +
            2 ^ k *
              Nat.xor (u % 2 ^ n)
                (if Nat.testBit u (w - 1) then 2 ^ n - 1 else 0) := by
      have hwn : w - n = k := by omega
      simp [signedShiftRWord, hn, hwn]
    rw [hRraw]
    by_cases hcmp0 : u < 2 ^ (w - 1)
    · rw [if_pos hcmp0] at hq_eq
      have hq0 : 0 ≤ q := by
        by_contra hqneg
        push_neg at hqneg
        have hq1 : q ≤ -1 := by omega
        have hp : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
        have hb : (2 : ℤ) ^ n * q ≤ (2 : ℤ) ^ n * (-1) :=
          mul_le_mul_of_nonneg_left hq1 (le_of_lt hp)
        have hb2 : (2 : ℤ) ^ n * (-1) = -(2 : ℤ) ^ n := by ring
        have h0u : (0 : ℤ) ≤ (u : ℤ) := Nat.cast_nonneg u
        linarith [hq_eq, hb, hb2, h0u, hp]
      have hm : (u : ℤ) = (2 : ℤ) ^ n * (q.toNat : ℤ) := by
        rw [Int.toNat_of_nonneg hq0]; exact hq_eq
      have hm' : u = 2 ^ n * q.toNat := by exact_mod_cast hm
      have hmod0 : u % 2 ^ n = 0 := by
        rw [hm']; exact Nat.mul_mod_right _ _
      have hdiv : u / 2 ^ n = q.toNat := by
        rw [hm']; exact Nat.mul_div_cancel_left _ (Nat.two_pow_pos n)
      have hsignf : Nat.testBit u (w - 1) = false := by
        rw [Bool.eq_false_iff]
        intro hcontra
        exact absurd (hsigneq.mp hcontra) (by omega)
      rw [hmod0, hsignf, hdiv]
      have hxor0 : Nat.xor 0 (if false = true then 2 ^ n - 1 else 0) = 0 := by
        exact Nat.zero_xor 0
      rw [hxor0]
      simp
      have hqn_lt_w : q.toNat < 2 ^ w := by
        have hqfit_hi := hq_fit.2.2
        have hsx : signedMax w = (2 : ℤ) ^ (w - 1) := by simp [signedMax]
        rw [hsx] at hqfit_hi
        have hlt2 : (2 : ℤ) ^ (w - 1) < (2 : ℤ) ^ w := by
          have hh : (2 : ℕ) ^ (w - 1) < 2 ^ w :=
            Nat.pow_lt_pow_right (by norm_num) (by omega)
          exact_mod_cast hh
        have hqcast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq0
        have hlt3 : (q.toNat : ℤ) < (2 : ℤ) ^ w := by
          rw [hqcast]; linarith [hqfit_hi, hlt2]
        exact_mod_cast hlt3
      have hfinal := tcModWidth_natCast_of_lt w q.toNat hqn_lt_w
      rwa [Int.toNat_of_nonneg hq0] at hfinal
    · rw [if_neg hcmp0] at hq_eq
      have heq2 : (u : ℤ) = 2 ^ n * (q + 2 ^ k) := by
        have hstep : (u : ℤ) = 2 ^ n * q + ((2 ^ w : ℕ) : ℤ) := by
          linarith [hq_eq]
        have hpow_cast : ((2 ^ w : ℕ) : ℤ) = (2 : ℤ) ^ w := by norm_num
        rw [hstep, hpow_cast, hwk]
        ring
      have hqneg : q < 0 := by
        have h2npos : (0 : ℤ) < 2 ^ n := by positivity
        by_contra hqpos
        push_neg at hqpos
        have hnn2 : (0 : ℤ) ≤ 2 ^ n * q := mul_nonneg (le_of_lt h2npos) hqpos
        have hnn2' : ((2 ^ w : ℕ) : ℤ) ≤ (u : ℤ) := by
          linarith [hq_eq, hnn2]
        have hult : (u : ℤ) < ((2 ^ w : ℕ) : ℤ) := by exact_mod_cast hu
        linarith
      have hnn : 0 ≤ q + (2 : ℤ) ^ k := by
        by_contra hneg
        push_neg at hneg
        have hp : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
        have hlt : (2 : ℤ) ^ n * (q + 2 ^ k) < 0 :=
          mul_neg_of_pos_of_neg hp hneg
        rw [← heq2] at hlt
        have h0u : (0 : ℤ) ≤ (u : ℤ) := Nat.cast_nonneg u
        linarith
      have hm : (u : ℤ) = (2 : ℤ) ^ n * ((q + 2 ^ k).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg hnn]; exact heq2
      have hm' : u = 2 ^ n * (q + 2 ^ k).toNat := by exact_mod_cast hm
      have hmod0 : u % 2 ^ n = 0 := by
        rw [hm']; exact Nat.mul_mod_right _ _
      have hdiv : u / 2 ^ n = (q + 2 ^ k).toNat := by
        rw [hm']; exact Nat.mul_div_cancel_left _ (Nat.two_pow_pos n)
      have hsignt : Nat.testBit u (w - 1) = true := by
        push_neg at hcmp0
        exact hsigneq.mpr hcmp0
      rw [hmod0, hsignt, hdiv]
      have hxor0 : Nat.xor 0 (if true = true then 2 ^ n - 1 else 0) = 2 ^ n - 1 := by
        exact Nat.zero_xor (2 ^ n - 1)
      rw [hxor0]
      have h2 : (1 : ℕ) ≤ 2 ^ n := Nat.two_pow_pos n
      have hcast : (((q + 2 ^ k).toNat + 2 ^ k * (2 ^ n - 1) : ℕ) : ℤ) = q + 2 ^ w := by
        push_cast [Nat.cast_sub h2]
        rw [Int.toNat_of_nonneg hnn]
        linear_combination hwk'
      have hcastNat : (((q + 2 ^ k).toNat + 2 ^ k * (2 ^ n - 1) : ℕ) : ℤ) =
          q + ((2 ^ w : ℕ) : ℤ) := by
        rw [hcast]
        norm_num
      have hbound : (q + 2 ^ k).toNat + 2 ^ k * (2 ^ n - 1) < 2 ^ w := by
        have hlt4 :
            (((q + 2 ^ k).toNat + 2 ^ k * (2 ^ n - 1) : ℕ) : ℤ) < 2 ^ w := by
          rw [hcast]; linarith [hqneg]
        exact_mod_cast hlt4
      have hq_repr : q =
          (((q + 2 ^ k).toNat + 2 ^ k * (2 ^ n - 1 : ℕ) : ℕ) : ℤ) -
            ((2 ^ w : ℕ) : ℤ) := by
        rw [hcastNat]
        ring
      calc
        tcModWidth w q =
            tcModWidth w
              ((((q + 2 ^ k).toNat + 2 ^ k * (2 ^ n - 1 : ℕ) : ℕ) : ℤ) -
                ((2 ^ w : ℕ) : ℤ)) := congrArg (tcModWidth w) hq_repr
        _ = (q + 2 ^ k).toNat + 2 ^ k * (2 ^ n - 1) :=
          tcModWidth_natCast_sub_two_pow_of_lt w
            ((q + 2 ^ k).toNat + 2 ^ k * (2 ^ n - 1)) hbound
  · push_neg at hn
    have h2n : (2 : ℤ) ^ w ≤ (2 : ℤ) ^ n := by
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
      exact_mod_cast this
    have h2w : (2 : ℤ) ^ (w - 1) < (2 : ℤ) ^ w := by
      have : (2 : ℕ) ^ (w - 1) < 2 ^ w :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      exact_mod_cast this
    have hzfit := tcDecodeWidth_fitsSignedWidth hw hu
    have hz_lo : -(2 : ℤ) ^ (w - 1) ≤ tcDecodeWidth w u := by
      have := hzfit.2.1; simpa [signedMin] using this
    have hz_hi : tcDecodeWidth w u < (2 : ℤ) ^ (w - 1) := by
      have := hzfit.2.2; simpa [signedMax] using this
    rw [hq_eq] at hz_lo hz_hi
    have hq0 : q = 0 := by
      by_contra hqne
      rcases lt_or_gt_of_ne hqne with hneg | hpos
      · have hq1 : q ≤ -1 := by omega
        have hb : (2 : ℤ) ^ n * q ≤ (2 : ℤ) ^ n * (-1) :=
          mul_le_mul_of_nonneg_left hq1 (by positivity)
        have hb2 : (2 : ℤ) ^ n * (-1) = -(2 : ℤ) ^ n := by ring
        linarith [hz_lo, hb, hb2, h2n, h2w]
      · have hq1 : (1 : ℤ) ≤ q := by omega
        have hb : (2 : ℤ) ^ n * 1 ≤ (2 : ℤ) ^ n * q :=
          mul_le_mul_of_nonneg_left hq1 (by positivity)
        have hb2 : (2 : ℤ) ^ n * 1 = (2 : ℤ) ^ n := by ring
        linarith [hz_hi, hb, hb2, h2n, h2w]
    have hz0 : tcDecodeWidth w u = 0 := by rw [hq_eq, hq0]; ring
    have hu0 : u = 0 := by
      by_contra hune
      have h1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hune
      rw [tcDecodeWidth_eq_of_pos w u hw] at hz0
      by_cases hcmp : u < 2 ^ (w - 1)
      · rw [if_pos hcmp] at hz0
        have : u = 0 := by exact_mod_cast hz0
        omega
      · rw [if_neg hcmp] at hz0
        have heq : (u : ℤ) = ((2 ^ w : ℕ) : ℤ) := by linarith [hz0]
        have : u = 2 ^ w := by exact_mod_cast heq
        omega
    have hRraw : signedShiftRWord w n u = u := by
      simp [signedShiftRWord, not_lt.mpr hn, Nat.mod_eq_of_lt hu]
    rw [hRraw, hq0, hu0]
    simp [tcModWidth]

private lemma shiftRBasis_eq_shiftRBasisRaw_concrete
    (r : ExtReg) (n : ℕ) (b : Basis) :
    shiftRBasis r n b = shiftRBasisRaw r n b := by
  classical
  by_cases hex :
      ∃ q : ℤ, extToInt r b = (2 : ℤ) ^ n * q ∧ FitsSignedWidth r.width q
  · have hRdef :
        shiftRBasis r n b =
          RegEncoding.writeNat r.active
            (tcModWidth r.width (Classical.choose hex)) b := by
      simp [shiftRBasis, hex]
    rw [hRdef]
    unfold shiftRBasisRaw
    congr 1
    obtain ⟨hzeq, hqfit⟩ := Classical.choose_spec hex
    have hu : ExtReg.toNat r b < 2 ^ r.width := extReg_toNat_lt_concrete r b
    have hzeq' : extToInt r b = tcDecodeWidth r.width (ExtReg.toNat r b) := rfl
    have hdecode_eq :
        tcDecodeWidth r.width (ExtReg.toNat r b) =
          (2 : ℤ) ^ n * Classical.choose hex :=
      hzeq'.symm.trans hzeq
    exact
      key_shiftR r.width n (ExtReg.toNat r b) hu (Classical.choose hex) hdecode_eq hqfit
  · simp [shiftRBasis, hex]

private theorem shiftRBasis_shiftLBasis_concrete
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    shiftRBasis r n (shiftLBasis r n b) = b := by
  rw [shiftLBasis_eq_shiftLBasisRaw_concrete, shiftRBasis_eq_shiftRBasisRaw_concrete]
  exact shiftRBasisRaw_shiftLBasisRaw r n b

private theorem shiftLBasis_shiftRBasis_concrete
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) :
    shiftLBasis r n (shiftRBasis r n b) = b := by
  rw [shiftRBasis_eq_shiftRBasisRaw_concrete, shiftLBasis_eq_shiftLBasisRaw_concrete]
  exact shiftLBasisRaw_shiftRBasisRaw r n b

theorem shiftLBasis_injective_concrete
    (r : ExtReg)
    (n : ℕ) :
    Function.Injective
      (shiftLBasis
        (Basis := Basis) r n) := by
  intro b c h
  have h' :=
    congrArg (shiftRBasis r n) h
  rw [
    shiftRBasis_shiftLBasis_concrete r n b,
    shiftRBasis_shiftLBasis_concrete r n c
  ] at h'
  exact h'

theorem shiftRBasis_injective_concrete
    (r : ExtReg)
    (n : ℕ) :
    Function.Injective
      (shiftRBasis
        (Basis := Basis) r n) := by
  intro b c h
  have h' :=
    congrArg (shiftLBasis r n) h
  rw [
    shiftLBasis_shiftRBasis_concrete r n b,
    shiftLBasis_shiftRBasis_concrete r n c
  ] at h'
  exact h'

private lemma key_negate_step
    (w v : ℕ) (hv : v < 2 ^ w) :
    tcModWidth w (- tcDecodeWidth w v) =
      if v = 0 then 0 else 2 ^ w - v := by
  by_cases hw : w = 0
  · subst hw
    simp only [pow_zero] at hv
    have hv0 : v = 0 := by omega
    subst hv0
    simp [tcDecodeWidth, tcModWidth]
  · have hwpos : 0 < w := Nat.pos_of_ne_zero hw
    by_cases hv0 : v = 0
    · rw [if_pos hv0]
      subst hv0
      have hz0 : tcDecodeWidth w 0 = 0 := by
        rw [tcDecodeWidth_eq_of_pos w 0 hwpos]
        rw [if_pos (Nat.two_pow_pos (w-1))]
        norm_num
      rw [hz0]
      simp [tcModWidth]
    · rw [if_neg hv0]
      rw [tcDecodeWidth_eq_of_pos w v hwpos]
      by_cases hcmp : v < 2 ^ (w - 1)
      · rw [if_pos hcmp]
        have hVlt : 2 ^ w - v < 2 ^ w := by omega
        have hle : v ≤ 2 ^ w := by omega
        have hcast : -(v:ℤ) = ((2 ^ w - v : ℕ):ℤ) - ((2 ^ w:ℕ):ℤ) := by
          push_cast [Nat.cast_sub hle]
          ring
        rw [hcast]
        exact tcModWidth_natCast_sub_two_pow_of_lt w (2 ^ w - v) hVlt
      · push_neg at hcmp
        have hVlt : 2 ^ w - v < 2 ^ w := by omega
        have hle : v ≤ 2 ^ w := by omega
        have hcast : -((v:ℤ) - ((2^w:ℕ):ℤ)) = ((2 ^ w - v : ℕ):ℤ) := by
          push_cast [Nat.cast_sub hle]
          ring
        rw [if_neg (not_lt.mpr hcmp)]
        rw [hcast]
        exact tcModWidth_natCast_of_lt w (2 ^ w - v) hVlt

private lemma key_negate
    (w u : ℕ) (hu : u < 2 ^ w) :
    tcModWidth w (- tcDecodeWidth w (tcModWidth w (- tcDecodeWidth w u))) = u := by
  have hv_lt : tcModWidth w (- tcDecodeWidth w u) < 2 ^ w :=
    tcModWidth_lt_two_pow w (- tcDecodeWidth w u)
  have h2 := key_negate_step w (tcModWidth w (- tcDecodeWidth w u)) hv_lt
  have h1 := key_negate_step w u hu
  rw [h2, h1]
  split_ifs <;> omega

private lemma negateBasis_negateBasis_concrete
    (r : ExtReg) (b : Basis) :
    negateBasis r (negateBasis r b) = b := by
  have hu : ExtReg.toNat r b < 2 ^ r.width := extReg_toNat_lt_concrete r b
  have hVlt :
      tcModWidth r.width (- extToInt r b) < ASize r.active := by
    simpa [ASize, ExtReg.width] using
      tcModWidth_lt_two_pow r.width (- extToInt r b)
  have htoNat2 :
      ExtReg.toNat r (negateBasis r b) =
        tcModWidth r.width (- extToInt r b) := by
    unfold ExtReg.toNat negateBasis
    exact RegEncoding.toNat_writeNat_of_lt r.active _ b hVlt
  have hzeq : extToInt r b = tcDecodeWidth r.width (ExtReg.toNat r b) := rfl
  have hextToInt2 :
      extToInt r (negateBasis r b) =
        tcDecodeWidth r.width (tcModWidth r.width (- extToInt r b)) := by
    unfold extToInt
    rw [htoNat2]
    rw [hzeq]
  have hkey :
      tcModWidth r.width
          (- tcDecodeWidth r.width
              (tcModWidth r.width (- tcDecodeWidth r.width (ExtReg.toNat r b))))
        = ExtReg.toNat r b :=
    key_negate r.width (ExtReg.toNat r b) hu
  have houter :
      negateBasis r (negateBasis r b) =
        RegEncoding.writeNat r.active
          (tcModWidth r.width (- extToInt r (negateBasis r b)))
          (negateBasis r b) := rfl
  rw [houter, hextToInt2, hzeq, hkey]
  unfold negateBasis
  rw [writeNat_writeNat_same]
  exact writeNat_toNat_concrete r.active b

theorem negateBasis_injective_concrete
    (r : ExtReg) :
    Function.Injective
      (negateBasis (Basis := Basis) r) := by
  intro b c h
  have h' := congrArg (negateBasis r) h
  rw [negateBasis_negateBasis_concrete r b, negateBasis_negateBasis_concrete r c] at h'
  exact h'

private lemma toNat_eq_of_sameOutside_of_disjoint
    (r r' : Reg)
    (hdisj : Disjoint r r')
    {b c : Basis}
    (hout : SameOutside r b c) :
    RegEncoding.toNat r' b = RegEncoding.toNat r' c := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < regSize r'
  · let j : Fin (regSize r') := ⟨p, hp⟩
    have hgetb :
        RegEncoding.bit (r'.get j) b =
          Nat.testBit (RegEncoding.toNat r' b) p :=
      RegEncoding.bit_eq_testBit_toNat r' b j
    have hgetc :
        RegEncoding.bit (r'.get j) c =
          Nat.testBit (RegEncoding.toNat r' c) p :=
      RegEncoding.bit_eq_testBit_toNat r' c j
    have hdisj' : Disjoint r' r := disjoint_symm hdisj
    rw [Disjoint, List.disjoint_left] at hdisj'
    have hqmem : r'.get j ∈ r'.qubits := by
      dsimp [Reg.get]
      exact List.get_mem r'.qubits _
    have hqnot : r'.get j ∉ r.qubits := hdisj' hqmem
    have hbiteq :
        RegEncoding.bit (r'.get j) b =
          RegEncoding.bit (r'.get j) c :=
      hout _ hqnot
    rw [← hgetb, ← hgetc]
    exact hbiteq
  · push_neg at hp
    have hb : RegEncoding.toNat r' b < 2 ^ p := by
      have hlt : RegEncoding.toNat r' b < ASize r' :=
        RegEncoding.toNat_lt_ASize r' b
      have hle : ASize r' ≤ 2 ^ p := by
        unfold ASize
        exact Nat.pow_le_pow_right (by norm_num) hp
      omega
    have hc : RegEncoding.toNat r' c < 2 ^ p := by
      have hlt : RegEncoding.toNat r' c < ASize r' :=
        RegEncoding.toNat_lt_ASize r' c
      have hle : ASize r' ≤ 2 ^ p := by
        unfold ASize
        exact Nat.pow_le_pow_right (by norm_num) hp
      omega
    rw [Nat.testBit_eq_false_of_lt hb, Nat.testBit_eq_false_of_lt hc]

private lemma tcModWidth_add_right_cancel
    (w : ℕ) (x y k : ℤ)
    (h : tcModWidth w (x + k) = tcModWidth w (y + k)) :
    tcModWidth w x = tcModWidth w y := by
  have hz : ((x + k : ℤ) : ZMod (2 ^ w)) = ((y + k : ℤ) : ZMod (2 ^ w)) := by
    rw [← tcModWidth_cast_zmod w (x + k), ← tcModWidth_cast_zmod w (y + k), h]
  push_cast at hz
  have hxy : (x : ZMod (2 ^ w)) = (y : ZMod (2 ^ w)) := add_right_cancel hz
  have hz2 :
      ((tcModWidth w x : ℕ) : ZMod (2 ^ w)) =
        ((tcModWidth w y : ℕ) : ZMod (2 ^ w)) := by
    rw [tcModWidth_cast_zmod, tcModWidth_cast_zmod]
    exact hxy
  have hxlt : tcModWidth w x < 2 ^ w := tcModWidth_lt_two_pow w x
  have hylt : tcModWidth w y < 2 ^ w := tcModWidth_lt_two_pow w y
  have hval := congrArg ZMod.val hz2
  rwa [ZMod.val_cast_of_lt hxlt, ZMod.val_cast_of_lt hylt] at hval

theorem addScaledBasis_injective_concrete
    (dst src : ExtReg)
    (negSrc : Bool)
    (sh : ℕ) :
    Function.Injective
      (addScaledBasis (Basis := Basis) dst src negSrc sh) := by
  classical
  intro b c h
  by_cases hdisj : ExtReg.ActiveDisjoint dst src
  · have hbdef :
        addScaledBasis dst src negSrc sh b =
          RegEncoding.writeNat
            dst.active
            (tcModWidth dst.width
              (extToInt dst b
                + (if negSrc then (-1 : ℤ) else 1)
                    * (2 : ℤ) ^ sh
                    * extToInt src b)) b := by
      simp [addScaledBasis, hdisj]
    have hcdef :
        addScaledBasis dst src negSrc sh c =
          RegEncoding.writeNat
            dst.active
            (tcModWidth dst.width
              (extToInt dst c
                + (if negSrc then (-1 : ℤ) else 1)
                    * (2 : ℤ) ^ sh
                    * extToInt src c)) c := by
      simp [addScaledBasis, hdisj]
    rw [hbdef, hcdef] at h
    have hdisj' : Disjoint dst.active src.active := hdisj
    have hout : SameOutside dst.active b c :=
      sameOutside_of_writeNat_eq dst.active _ _ b c h
    have hsrc :
        RegEncoding.toNat src.active b =
          RegEncoding.toNat src.active c :=
      toNat_eq_of_sameOutside_of_disjoint
        dst.active src.active hdisj' hout
    have hextSrc : extToInt src b = extToInt src c := by
      unfold extToInt
      simpa [ExtReg.toNat] using congrArg (tcDecodeWidth src.width) hsrc
    have hvb :
        tcModWidth dst.width
            (extToInt dst b
              + (if negSrc then (-1 : ℤ) else 1)
                  * (2 : ℤ) ^ sh
                  * extToInt src b)
          < ASize dst.active := by
      simpa [ASize, ExtReg.width] using
        tcModWidth_lt_two_pow dst.width _
    have hvc :
        tcModWidth dst.width
            (extToInt dst c
              + (if negSrc then (-1 : ℤ) else 1)
                  * (2 : ℤ) ^ sh
                  * extToInt src c)
          < ASize dst.active := by
      simpa [ASize, ExtReg.width] using
        tcModWidth_lt_two_pow dst.width _
    have h' := congrArg (RegEncoding.toNat dst.active) h
    rw [
      RegEncoding.toNat_writeNat_of_lt dst.active _ b hvb,
      RegEncoding.toNat_writeNat_of_lt dst.active _ c hvc
    ] at h'
    rw [hextSrc] at h'
    have hcancel :
        tcModWidth dst.width (extToInt dst b) =
          tcModWidth dst.width (extToInt dst c) :=
      tcModWidth_add_right_cancel
        dst.width
        (extToInt dst b) (extToInt dst c)
        ((if negSrc then (-1 : ℤ) else 1) * (2 : ℤ) ^ sh * extToInt src c)
        h'
    rw [tcModWidth_extToInt, tcModWidth_extToInt] at hcancel
    exact basis_eq_of_toNat_eq_of_sameOutside dst.active hcancel hout
  · have hbeq : addScaledBasis dst src negSrc sh b = b := by
      simp [addScaledBasis, hdisj]
    have hceq : addScaledBasis dst src negSrc sh c = c := by
      simp [addScaledBasis, hdisj]
    rw [hbeq, hceq] at h
    exact h

private lemma cmpGeConstBasis_flag_eq
    (N : ℕ) (data : Reg) (flag : ℕ) (b : Basis)
    (hflag : flag ∉ data.qubits) :
    cmpGeConstBasis N data flag b =
      RegEncoding.writeNat (qubitReg flag)
        (if RegEncoding.bit flag b then
          if N ≤ RegEncoding.toNat data b then 0 else 1
        else if N ≤ RegEncoding.toNat data b then 1 else 0) b := by
  simp [cmpGeConstBasis, hflag]

theorem cmpGeConstBasis_injective_concrete
    (N : ℕ)
    (data : Reg)
    (flag : ℕ) :
    Function.Injective
      (cmpGeConstBasis (Basis := Basis) N data flag) := by
  intro b c h
  by_cases hflag : flag ∈ data.qubits
  · simpa [cmpGeConstBasis, hflag] using h
  · rw [cmpGeConstBasis_flag_eq N data flag b hflag,
        cmpGeConstBasis_flag_eq N data flag c hflag] at h
    have hdisj : Disjoint data (qubitReg flag) := by
      rw [Disjoint, List.disjoint_left]
      intro a ha hmem
      have haeq : a = flag := by simpa [qubitReg, Reg.singleton] using hmem
      rw [haeq] at ha
      exact hflag ha
    have hout : SameOutside (qubitReg flag) b c :=
      sameOutside_of_writeNat_eq (qubitReg flag) _ _ b c h
    have hdisj' : Disjoint (qubitReg flag) data := disjoint_symm hdisj
    have hdata :
        RegEncoding.toNat data b = RegEncoding.toNat data c :=
      toNat_eq_of_sameOutside_of_disjoint (qubitReg flag) data hdisj' hout
    have hASize2 : ASize (qubitReg flag) = 2 := by
      simp [ASize, regSize, Reg.width, qubitReg, Reg.singleton]
    have hvb_lt :
        (if RegEncoding.bit flag b then
          if N ≤ RegEncoding.toNat data b then 0 else 1
        else if N ≤ RegEncoding.toNat data b then 1 else 0)
          < ASize (qubitReg flag) := by
      rw [hASize2]; split_ifs <;> norm_num
    have hvc_lt :
        (if RegEncoding.bit flag c then
          if N ≤ RegEncoding.toNat data c then 0 else 1
        else if N ≤ RegEncoding.toNat data c then 1 else 0)
          < ASize (qubitReg flag) := by
      rw [hASize2]; split_ifs <;> norm_num
    have h' := congrArg (RegEncoding.toNat (qubitReg flag)) h
    rw [
      RegEncoding.toNat_writeNat_of_lt (qubitReg flag) _ b hvb_lt,
      RegEncoding.toNat_writeNat_of_lt (qubitReg flag) _ c hvc_lt
    ] at h'
    rw [hdata] at h'
    have hbitflag : RegEncoding.bit flag b = RegEncoding.bit flag c := by
      by_cases hcond : N ≤ RegEncoding.toNat data c <;>
        cases hb : RegEncoding.bit flag b <;>
        cases hc : RegEncoding.bit flag c <;>
        simp_all
    apply RegEncoding.basis_ext
    intro q
    by_cases hq : q = flag
    · rw [hq]; exact hbitflag
    · exact hout q (by simpa [qubitReg, Reg.singleton] using hq)

private lemma nat_sub_mod_right_cancel
    (M x y k : ℕ)
    (hxM : x < M) (hyM : y < M) (hkM : k ≤ M)
    (h : (x + M - k) % M = (y + M - k) % M) :
    x = y := by
  have hrw1 : x + M - k = x + (M - k) := by omega
  have hrw2 : y + M - k = y + (M - k) := by omega
  rw [hrw1, hrw2] at h
  have hmod : x ≡ y [MOD M] := Nat.ModEq.add_right_cancel' (M - k) h
  have hxmod : x % M = x := Nat.mod_eq_of_lt hxM
  have hymod : y % M = y := Nat.mod_eq_of_lt hyM
  simpa [Nat.ModEq, hxmod, hymod] using hmod

private lemma csubConstBasis_flag_eq
    (N : ℕ) (data : Reg) (flag : ℕ) (b : Basis)
    (hflag : flag ∉ data.qubits) :
    csubConstBasis N data flag b =
      RegEncoding.writeNat data
        (if RegEncoding.bit flag b then
          (RegEncoding.toNat data b + ASize data - N % ASize data) % ASize data
        else RegEncoding.toNat data b) b := by
  simp [csubConstBasis, hflag]

theorem csubConstBasis_injective_concrete
    (N : ℕ)
    (data : Reg)
    (flag : ℕ) :
    Function.Injective
      (csubConstBasis
        (Basis := Basis)
        N data flag) := by
  intro b c h
  by_cases hflag : flag ∈ data.qubits
  · simpa [csubConstBasis, hflag] using h
  · rw [csubConstBasis_flag_eq N data flag b hflag,
        csubConstBasis_flag_eq N data flag c hflag] at h
    have hout : SameOutside data b c :=
      sameOutside_of_writeNat_eq data _ _ b c h
    have hbitflag : RegEncoding.bit flag b = RegEncoding.bit flag c :=
      hout flag hflag
    have hASizepos : 0 < ASize data := by
      unfold ASize
      positivity
    have hNmodlt : N % ASize data < ASize data := Nat.mod_lt N hASizepos
    have hNmodle : N % ASize data ≤ ASize data := le_of_lt hNmodlt
    have hvb_lt :
        (if RegEncoding.bit flag b then
          (RegEncoding.toNat data b + ASize data - N % ASize data) % ASize data
        else RegEncoding.toNat data b)
          < ASize data := by
      split_ifs with hb
      · exact Nat.mod_lt _ hASizepos
      · exact RegEncoding.toNat_lt_ASize data b
    have hvc_lt :
        (if RegEncoding.bit flag c then
          (RegEncoding.toNat data c + ASize data - N % ASize data) % ASize data
        else RegEncoding.toNat data c)
          < ASize data := by
      split_ifs with hc
      · exact Nat.mod_lt _ hASizepos
      · exact RegEncoding.toNat_lt_ASize data c
    have h' := congrArg (RegEncoding.toNat data) h
    rw [
      RegEncoding.toNat_writeNat_of_lt data _ b hvb_lt,
      RegEncoding.toNat_writeNat_of_lt data _ c hvc_lt
    ] at h'
    rw [hbitflag] at h'
    have hread : RegEncoding.toNat data b = RegEncoding.toNat data c := by
      by_cases hc2 : RegEncoding.bit flag c
      · simp only [hc2, if_true] at h'
        exact nat_sub_mod_right_cancel
          (ASize data)
          (RegEncoding.toNat data b) (RegEncoding.toNat data c)
          (N % ASize data)
          (RegEncoding.toNat_lt_ASize data b)
          (RegEncoding.toNat_lt_ASize data c)
          hNmodle
          h'
      · simpa [hc2] using h'
    exact basis_eq_of_toNat_eq_of_sameOutside data hread hout

private lemma nat_mul_mod_cancel_of_coprime
    (N c x y : ℕ)
    (hcop : Nat.Coprime c N)
    (hxN : x < N) (hyN : y < N)
    (h : (c * x) % N = (c * y) % N) :
    x = y := by
  have hmod : c * x ≡ c * y [MOD N] := h
  have hxy : x ≡ y [MOD N] := Nat.ModEq.cancel_left_of_coprime hcop.symm hmod
  have hxmod : x % N = x := Nat.mod_eq_of_lt hxN
  have hymod : y % N = y := Nat.mod_eq_of_lt hyN
  simpa [Nat.ModEq, hxmod, hymod] using hxy

theorem idealCtrlModMulBasis_injective_concrete
    (c N : ℕ)
    (data : Reg)
    (ctrl : ℕ) :
    Function.Injective
      (idealCtrlModMulBasisConcrete
        c N data ctrl) := by
  classical
  intro b1 b2 h
  by_cases hpre :
      1 < N ∧ N ≤ ASize data ∧ Nat.Coprime c N ∧ ctrl ∉ data.qubits
  · by_cases hx1 : RegEncoding.toNat data b1 < N
    · by_cases hx2 : RegEncoding.toNat data b2 < N
      · have heq1 :
            idealCtrlModMulBasisConcrete c N data ctrl b1 =
              RegEncoding.writeNat data
                (if RegEncoding.bit ctrl b1 then
                  (c * RegEncoding.toNat data b1) % N
                else
                  RegEncoding.toNat data b1) b1 := by
          simp [idealCtrlModMulBasisConcrete, hpre, hx1]
        have heq2 :
            idealCtrlModMulBasisConcrete c N data ctrl b2 =
              RegEncoding.writeNat data
                (if RegEncoding.bit ctrl b2 then
                  (c * RegEncoding.toNat data b2) % N
                else
                  RegEncoding.toNat data b2) b2 := by
          simp [idealCtrlModMulBasisConcrete, hpre, hx2]
        rw [heq1, heq2] at h
        have hout : SameOutside data b1 b2 :=
          sameOutside_of_writeNat_eq data _ _ b1 b2 h
        have hdisj : Disjoint data (qubitReg ctrl) := by
          rw [Disjoint, List.disjoint_left]
          intro a ha hmem
          have haeq : a = ctrl := by simpa [qubitReg, Reg.singleton] using hmem
          rw [haeq] at ha
          exact hpre.2.2.2 ha
        have hbitctrl :
            RegEncoding.bit ctrl b1 = RegEncoding.bit ctrl b2 :=
          hout ctrl hpre.2.2.2
        have hNpos : 0 < N := by omega
        have hvb1_lt :
            (if RegEncoding.bit ctrl b1 then
              (c * RegEncoding.toNat data b1) % N
            else
              RegEncoding.toNat data b1) < ASize data := by
          split_ifs with hb
          · exact lt_of_lt_of_le (Nat.mod_lt _ hNpos) hpre.2.1
          · exact RegEncoding.toNat_lt_ASize data b1
        have hvb2_lt :
            (if RegEncoding.bit ctrl b2 then
              (c * RegEncoding.toNat data b2) % N
            else
              RegEncoding.toNat data b2) < ASize data := by
          split_ifs with hb
          · exact lt_of_lt_of_le (Nat.mod_lt _ hNpos) hpre.2.1
          · exact RegEncoding.toNat_lt_ASize data b2
        have h' := congrArg (RegEncoding.toNat data) h
        rw [
          RegEncoding.toNat_writeNat_of_lt data _ b1 hvb1_lt,
          RegEncoding.toNat_writeNat_of_lt data _ b2 hvb2_lt
        ] at h'
        rw [hbitctrl] at h'
        have hread :
            RegEncoding.toNat data b1 = RegEncoding.toNat data b2 := by
          by_cases hb2 : RegEncoding.bit ctrl b2
          · simp only [hb2, if_true] at h'
            exact nat_mul_mod_cancel_of_coprime N c
              (RegEncoding.toNat data b1) (RegEncoding.toNat data b2)
              hpre.2.2.1 hx1 hx2 h'
          · simpa [hb2] using h'
        exact basis_eq_of_toNat_eq_of_sameOutside data hread hout
      · exfalso
        have heq1 :
            idealCtrlModMulBasisConcrete c N data ctrl b1 =
              RegEncoding.writeNat data
                (if RegEncoding.bit ctrl b1 then
                  (c * RegEncoding.toNat data b1) % N
                else
                  RegEncoding.toNat data b1) b1 := by
          simp [idealCtrlModMulBasisConcrete, hpre, hx1]
        have heq2 :
            idealCtrlModMulBasisConcrete c N data ctrl b2 = b2 := by
          simp [idealCtrlModMulBasisConcrete, hpre, hx2]
        rw [heq1, heq2] at h
        have hNpos : 0 < N := by omega
        have hvb1_ltN :
            (if RegEncoding.bit ctrl b1 then
              (c * RegEncoding.toNat data b1) % N
            else
              RegEncoding.toNat data b1) < N := by
          split_ifs with hb
          · exact Nat.mod_lt _ hNpos
          · exact hx1
        have hvb1_ltASize :
            (if RegEncoding.bit ctrl b1 then
              (c * RegEncoding.toNat data b1) % N
            else
              RegEncoding.toNat data b1) < ASize data :=
          lt_of_lt_of_le hvb1_ltN hpre.2.1
        have h' := congrArg (RegEncoding.toNat data) h
        rw [
          RegEncoding.toNat_writeNat_of_lt data _ b1 hvb1_ltASize
        ] at h'
        omega
    · by_cases hx2 : RegEncoding.toNat data b2 < N
      · exfalso
        have heq1 :
            idealCtrlModMulBasisConcrete c N data ctrl b1 = b1 := by
          simp [idealCtrlModMulBasisConcrete, hpre, hx1]
        have heq2 :
            idealCtrlModMulBasisConcrete c N data ctrl b2 =
              RegEncoding.writeNat data
                (if RegEncoding.bit ctrl b2 then
                  (c * RegEncoding.toNat data b2) % N
                else
                  RegEncoding.toNat data b2) b2 := by
          simp [idealCtrlModMulBasisConcrete, hpre, hx2]
        rw [heq1, heq2] at h
        have hNpos : 0 < N := by omega
        have hvb2_ltN :
            (if RegEncoding.bit ctrl b2 then
              (c * RegEncoding.toNat data b2) % N
            else
              RegEncoding.toNat data b2) < N := by
          split_ifs with hb
          · exact Nat.mod_lt _ hNpos
          · exact hx2
        have hvb2_ltASize :
            (if RegEncoding.bit ctrl b2 then
              (c * RegEncoding.toNat data b2) % N
            else
              RegEncoding.toNat data b2) < ASize data :=
          lt_of_lt_of_le hvb2_ltN hpre.2.1
        have h' := congrArg (RegEncoding.toNat data) h
        rw [
          RegEncoding.toNat_writeNat_of_lt data _ b2 hvb2_ltASize
        ] at h'
        omega
      · have heq1 :
            idealCtrlModMulBasisConcrete c N data ctrl b1 = b1 := by
          simp [idealCtrlModMulBasisConcrete, hpre, hx1]
        have heq2 :
            idealCtrlModMulBasisConcrete c N data ctrl b2 = b2 := by
          simp [idealCtrlModMulBasisConcrete, hpre, hx2]
        rw [heq1, heq2] at h
        exact h
  · have heq1 :
        idealCtrlModMulBasisConcrete c N data ctrl b1 = b1 := by
      simp [idealCtrlModMulBasisConcrete, hpre]
    have heq2 :
        idealCtrlModMulBasisConcrete c N data ctrl b2 = b2 := by
      simp [idealCtrlModMulBasisConcrete, hpre]
    rw [heq1, heq2] at h
    exact h

private lemma xBasis_sameOutside
    (q : ℕ)
    (b : Basis) :
    SameOutside (qubitReg q) (xBasis q b) b := by
  unfold xBasis
  exact writeNat_sameOutside (qubitReg q) _ b

private lemma cnotBasis_sameOutside
    (ctrl target : ℕ)
    (b : Basis) :
    SameOutside (qubitReg target) (cnotBasis ctrl target b) b := by
  unfold cnotBasis
  split_ifs
  all_goals first
    | exact sameOutside_refl (qubitReg target) b
    | exact writeNat_sameOutside (qubitReg target) _ b

private lemma toffoliBasis_sameOutside
    (c₁ c₂ target : ℕ)
    (b : Basis) :
    SameOutside (qubitReg target) (toffoliBasis c₁ c₂ target b) b := by
  unfold toffoliBasis
  split_ifs
  all_goals first
    | exact sameOutside_refl (qubitReg target) b
    | exact writeNat_sameOutside (qubitReg target) _ b

private lemma radixReverseBasis_sameOutside
    (r : Reg)
    (m : ℕ)
    (b : Basis) :
    SameOutside r (radixReverseBasis r m b) b := by
  unfold radixReverseBasis
  split_ifs
  all_goals first
    | exact sameOutside_refl r b
    | exact writeNat_sameOutside r _ b

private lemma cmpGeConstBasis_sameOutside
    (N : ℕ)
    (data : Reg)
    (flag : ℕ)
    (b : Basis) :
    SameOutside (qubitReg flag) (cmpGeConstBasis N data flag b) b := by
  by_cases hflag : flag ∈ data.qubits
  · have heq : cmpGeConstBasis N data flag b = b := by
      simp [cmpGeConstBasis, hflag]
    rw [heq]
    exact sameOutside_refl (qubitReg flag) b
  · rw [cmpGeConstBasis_flag_eq N data flag b hflag]
    exact writeNat_sameOutside (qubitReg flag) _ b

private lemma csubConstBasis_sameOutside
    (N : ℕ)
    (data : Reg)
    (flag : ℕ)
    (b : Basis) :
    SameOutside data (csubConstBasis N data flag b) b := by
  by_cases hflag : flag ∈ data.qubits
  · have heq : csubConstBasis N data flag b = b := by
      simp [csubConstBasis, hflag]
    rw [heq]
    exact sameOutside_refl data b
  · rw [csubConstBasis_flag_eq N data flag b hflag]
    exact writeNat_sameOutside data _ b

private lemma addScaledBasis_sameOutside
    (dst src : ExtReg)
    (negSrc : Bool)
    (sh : ℕ)
    (b : Basis) :
    SameOutside dst.active (addScaledBasis dst src negSrc sh b) b := by
  classical
  by_cases hdisj : ExtReg.ActiveDisjoint dst src
  · have heq :
        addScaledBasis dst src negSrc sh b =
          RegEncoding.writeNat
            dst.active
            (tcModWidth dst.width
              (extToInt dst b
                + (if negSrc then (-1 : ℤ) else 1)
                    * (2 : ℤ) ^ sh
                    * extToInt src b)) b := by
      simp [addScaledBasis, hdisj]
    rw [heq]
    exact writeNat_sameOutside dst.active _ b
  · have heq : addScaledBasis dst src negSrc sh b = b := by
      simp [addScaledBasis, hdisj]
    rw [heq]
    exact sameOutside_refl dst.active b

private lemma idealCtrlModMulBasisConcrete_sameOutside
    (c N : ℕ)
    (data : Reg)
    (ctrl : ℕ)
    (b : Basis) :
    SameOutside data (idealCtrlModMulBasisConcrete c N data ctrl b) b := by
  classical
  by_cases hpre :
      1 < N ∧ N ≤ ASize data ∧ Nat.Coprime c N ∧ ctrl ∉ data.qubits
  · by_cases hx : RegEncoding.toNat data b < N
    · have heq :
          idealCtrlModMulBasisConcrete c N data ctrl b =
            RegEncoding.writeNat data
              (if RegEncoding.bit ctrl b then
                (c * RegEncoding.toNat data b) % N
              else
                RegEncoding.toNat data b) b := by
        simp [idealCtrlModMulBasisConcrete, hpre, hx]
      rw [heq]
      exact writeNat_sameOutside data _ b
    · have heq : idealCtrlModMulBasisConcrete c N data ctrl b = b := by
        simp [idealCtrlModMulBasisConcrete, hpre, hx]
      rw [heq]
      exact sameOutside_refl data b
  · have heq : idealCtrlModMulBasisConcrete c N data ctrl b = b := by
      simp [idealCtrlModMulBasisConcrete, hpre]
    rw [heq]
    exact sameOutside_refl data b

theorem atomBasisMap_injective
    (U : Gate) :
    Function.Injective (atomBasisMap U) := by
  cases U with

  | X q =>
      exact xBasis_injective q

  | CNOT ctrl target =>
      exact cnotBasis_injective_concrete ctrl target

  | Toffoli c₁ c₂ target =>
      exact toffoliBasis_injective_concrete c₁ c₂ target

  | RadixReverse r m =>
      exact radixReverseBasis_injective_concrete r m

  | CmpGeConst N data scratch flag =>
      exact
        cmpGeConstBasis_injective_concrete
          N data.active flag

  | CSubConst N data scratch flag =>
      exact
        csubConstBasis_injective_concrete
          N data.active flag

  | ShiftL r n =>
      exact shiftLBasis_injective_concrete r n

  | ShiftR r n =>
      exact shiftRBasis_injective_concrete r n

  | Negate r =>
      exact negateBasis_injective_concrete r

  | AddScaled dst src negSrc sh =>
      exact
        addScaledBasis_injective_concrete
          dst src negSrc sh

  | signExtend r n =>
      exact signExtendBasis_injective_concrete r n

  | signDealloc r n =>
      simpa [signDeallocBasis] using
        signExtendBasis_injective_concrete r n

  | idealCtrlModMul c N data ctrl =>
      exact
        idealCtrlModMulBasis_injective_concrete
          c N data ctrl

  | id =>
      intro b c h
      exact h

  | seq U V =>
      intro b c h
      exact h

  | adj U =>
      intro b c h
      exact h

  | H q =>
      intro b c h
      exact h

  | QFT r =>
      intro b c h
      exact h

  | SignedPhaseProd phi x z =>
      intro b c h
      exact h

  | CSignedPhaseProd ctrl phi x z =>
      intro b c h
      exact h

  | zeroExtend r n =>
      intro b c h
      exact h

  | zeroDealloc r n =>
      intro b c h
      exact h

private lemma writeNat_eq_writeNat_iff
    (r : Reg)
    (v w : ℕ)
    (b c : Basis)
    (hv : v < ASize r)
    (hw : w < ASize r) :
    RegEncoding.writeNat r v b =
        RegEncoding.writeNat r w c ↔
      v = w ∧ SameOutside r b c := by
  constructor
  · intro h
    have hvw : v = w := by
      have h' := congrArg (RegEncoding.toNat r) h
      rw [
        RegEncoding.toNat_writeNat_of_lt r v b hv,
        RegEncoding.toNat_writeNat_of_lt r w c hw
      ] at h'
      exact h'
    refine ⟨hvw, ?_⟩
    intro q hq
    have h' := congrArg (RegEncoding.bit q) h
    rw [
      RegEncoding.bit_writeNat_out r v b q hq,
      RegEncoding.bit_writeNat_out r w c q hq
    ] at h'
    exact h'
  · rintro ⟨rfl, hout⟩
    apply RegEncoding.basis_ext
    intro q
    by_cases hq : q ∈ r.qubits
    · exact RegEncoding.bit_writeNat_in r v b c q hq
    · rw [
        RegEncoding.bit_writeNat_out r v b q hq,
        RegEncoding.bit_writeNat_out r v c q hq
      ]
      exact hout q hq

private noncomputable def qftWriteKetInner
    (r : ExtReg)
    (b c : Basis)
    (y z : Fin (2 ^ r.width)) : ℂ := by
  classical
  exact
    if y = z ∧ SameOutside r.active b c
    then 1
    else 0

private lemma inner_qft_write_ket
    (r : ExtReg)
    (b c : Basis)
    (y z : Fin (2 ^ r.width)) :
    inner ℂ
        (ket (RegEncoding.writeNat r.active y.1 b))
        (ket (RegEncoding.writeNat r.active z.1 c))
      =
    qftWriteKetInner r b c y z := by
  classical
  unfold qftWriteKetInner
  have hy : y.1 < ASize r.active := by
    simp [ExtReg.width] at y
    exact y.2
  have hz : z.1 < ASize r.active := by
    simp [ExtReg.width] at z
    exact z.2

  by_cases h :
      y = z ∧ SameOutside r.active b c
  · have heq :
        RegEncoding.writeNat r.active y.1 b =
          RegEncoding.writeNat r.active z.1 c := by
      apply
        (writeNat_eq_writeNat_iff
          r.active y.1 z.1 b c hy hz).2
      exact ⟨congrArg Fin.val h.1, h.2⟩
    rw [heq, inner_ket_self_concrete]
    simp [h]
  · have hne :
        RegEncoding.writeNat r.active y.1 b ≠
          RegEncoding.writeNat r.active z.1 c := by
      intro heq
      apply h
      have h' :=
        (writeNat_eq_writeNat_iff
          r.active y.1 z.1 b c hy hz).1 heq
      exact ⟨Fin.ext h'.1, h'.2⟩
    rw [inner_ket_ne_concrete hne]
    simp [h]

private noncomputable def qftChar
    (N x : ℕ)
    [NeZero N] :
    AddChar (ZMod N) ℂ :=
  (ZMod.stdAddChar (N := N)).mulShift (x : ZMod N)

private lemma qftChar_natCast
    (N x y : ℕ)
    [NeZero N] :
    qftChar N x (y : ZMod N) =
      qftPhase N x y := by
  rw [qftChar, AddChar.mulShift_apply]

  have hmul :
      (x : ZMod N) * (y : ZMod N) =
        ((x * y : ℕ) : ZMod N) := by
    norm_num

  rw [hmul]

  have hcast :
      ((x * y : ℕ) : ZMod N) =
        (((x * y : ℕ) : ℤ) : ZMod N) := by
    norm_num

  rw [hcast, ZMod.stdAddChar_coe]

  unfold qftPhase ωPow ω
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma qftChar_eq_iff
    (N x z : ℕ)
    [NeZero N]
    (hx : x < N)
    (hz : z < N) :
    qftChar N x = qftChar N z ↔
      x = z := by
  constructor
  · intro h

    have h1 :=
      DFunLike.congr_fun h (1 : ZMod N)

    have hchar :
        ZMod.stdAddChar (x : ZMod N) =
          ZMod.stdAddChar (z : ZMod N) := by
      simpa [qftChar] using h1

    have hxz :
        (x : ZMod N) = (z : ZMod N) :=
      ZMod.injective_stdAddChar hchar

    have hv := congrArg ZMod.val hxz

    simpa [
      ZMod.val_natCast_of_lt hx,
      ZMod.val_natCast_of_lt hz
    ] using hv

  · intro h
    subst z
    rfl

private lemma zmod_finEquiv_val
    (N : ℕ)
    [NeZero N]
    (y : Fin N) :
    (ZMod.finEquiv N y).val = y.1 := by
  cases N with
  | zero =>
      exact (NeZero.ne 0 rfl).elim
  | succ n =>
      rfl

private lemma zmod_finEquiv_eq_natCast
    (N : ℕ)
    [NeZero N]
    (y : Fin N) :
    ZMod.finEquiv N y =
      (y.1 : ZMod N) := by
  calc
    ZMod.finEquiv N y =
        ((ZMod.finEquiv N y).val : ZMod N) :=
      (ZMod.natCast_zmod_val _).symm
    _ = (y.1 : ZMod N) := by
      rw [zmod_finEquiv_val]

private theorem qftPhase_orthogonality
    (N x z : ℕ)
    [NeZero N]
    (hx : x < N)
    (hz : z < N) :
    (N : ℂ)⁻¹ *
        ∑ y : Fin N,
          (starRingEnd ℂ) (qftPhase N x y.1) *
            qftPhase N z y.1
      =
    if x = z then 1 else 0 := by
  let χx := qftChar N x
  let χz := qftChar N z

  have horth :=
    AddChar.wInner_cWeight_eq_boole χx χz

  have horth' :
      (N : ℂ)⁻¹ *
          ∑ a : ZMod N,
            (starRingEnd ℂ) (χx a) * χz a
        =
      if χx = χz then 1 else 0 := by
    simpa [
      RCLike.wInner_cWeight_eq_expect,
      Fintype.expect_eq_sum_div_card,
      RCLike.inner_apply,
      ZMod.card,
      div_eq_mul_inv,
      mul_comm
    ] using horth

  have hsum :
      (∑ y : Fin N,
          (starRingEnd ℂ) (qftPhase N x y.1) *
            qftPhase N z y.1)
        =
      ∑ a : ZMod N,
        (starRingEnd ℂ) (χx a) * χz a := by
    apply Fintype.sum_equiv (ZMod.finEquiv N)
    intro y
    simp [
      χx,
      χz,
      zmod_finEquiv_eq_natCast N y,
      qftChar_natCast
    ]

  rw [hsum, horth']
  simp [χx, χz, qftChar_eq_iff N x z hx hz]

private lemma qft_normalization
    (N : ℕ)
    (hN : 0 < N) :
    (starRingEnd ℂ)
        ((1 / Real.sqrt (N : ℝ) : ℂ)) *
      ((1 / Real.sqrt (N : ℝ) : ℂ))
      =
    (N : ℂ)⁻¹ := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 := by
    positivity

  have hr :
      (1 / Real.sqrt (N : ℝ)) *
          (1 / Real.sqrt (N : ℝ))
        =
      (N : ℝ)⁻¹ := by
    field_simp [hs]
    nlinarith [
      Real.sq_sqrt
        (show 0 ≤ (N : ℝ) by positivity)
    ]

  have hcast :
      (((1 / Real.sqrt (N : ℝ)) *
          (1 / Real.sqrt (N : ℝ)) : ℝ) : ℂ)
        =
      (N : ℂ)⁻¹ := by
    rw [hr]
    norm_num

  simpa [Complex.ofReal_mul] using hcast

private noncomputable def qftSumsInner
    (r : ExtReg)
    (b c : Basis) :
    ℂ := by
  classical
  exact
    if SameOutside r.active b c then
      ∑ y : Fin (2 ^ r.width),
        (starRingEnd ℂ)
            (qftPhase
              (2 ^ r.width)
              (ExtReg.toNat r b)
              y.1) *
          qftPhase
            (2 ^ r.width)
            (ExtReg.toNat r c)
            y.1
    else
      0

private lemma inner_qft_sums
    (r : ExtReg)
    (b c : Basis) :
    inner ℂ
        (∑ y : Fin (2 ^ r.width),
          qftPhase
              (2 ^ r.width)
              (ExtReg.toNat r b)
              y.1 •
            ket
              (RegEncoding.writeNat
                r.active y.1 b))
        (∑ z : Fin (2 ^ r.width),
          qftPhase
              (2 ^ r.width)
              (ExtReg.toNat r c)
              z.1 •
            ket
              (RegEncoding.writeNat
                r.active z.1 c))
      =
    qftSumsInner r b c := by
  classical
  unfold qftSumsInner

  by_cases hout : SameOutside r.active b c
  · rw [if_pos hout, sum_inner]

    apply Finset.sum_congr rfl
    intro y hy

    rw [inner_sum]
    rw [Finset.sum_eq_single y]

    · rw [inner_smul_left, inner_smul_right]
      rw [inner_qft_write_ket]
      simp [qftWriteKetInner, hout]

    · intro z hz hzy
      rw [inner_smul_left, inner_smul_right]
      rw [inner_qft_write_ket]
      have hyz : y ≠ z := Ne.symm hzy
      simp [qftWriteKetInner, hout, hyz]

    · simp

  · rw [if_neg hout, sum_inner]

    apply Finset.sum_eq_zero
    intro y hy

    rw [inner_sum]

    apply Finset.sum_eq_zero
    intro z hz

    rw [inner_smul_left, inner_smul_right]
    rw [inner_qft_write_ket]
    simp [qftWriteKetInner, hout]

theorem qftKet_inner_preserved
    (r : ExtReg)
    (b c : Basis) :
    inner ℂ (qftKet r b) (qftKet r c) =
      inner ℂ (ket b) (ket c) := by
  classical

  let N := 2 ^ r.width

  have hN : 0 < N := by
    simp [N]

  letI : NeZero N :=
    ⟨Nat.ne_of_gt hN⟩

  have hb : ExtReg.toNat r b < N := by
    simpa [N, ExtReg.toNat, ASize, ExtReg.width] using
      RegEncoding.toNat_lt_ASize r.active b

  have hc : ExtReg.toNat r c < N := by
    simpa [N, ExtReg.toNat, ASize, ExtReg.width] using
      RegEncoding.toNat_lt_ASize r.active c

  change
    inner ℂ
      (((1 / Real.sqrt (N : ℝ) : ℂ)) •
        ∑ y : Fin N,
          qftPhase N (ExtReg.toNat r b) y.1 •
            ket
              (RegEncoding.writeNat
                r.active y.1 b))
      (((1 / Real.sqrt (N : ℝ) : ℂ)) •
        ∑ y : Fin N,
          qftPhase N (ExtReg.toNat r c) y.1 •
            ket
              (RegEncoding.writeNat
                r.active y.1 c))
      =
    inner ℂ (ket b) (ket c)

  rw [inner_smul_left, inner_smul_right]

  have hsums :=
    inner_qft_sums r b c

  change
    (starRingEnd ℂ)
        ((1 / Real.sqrt (N : ℝ) : ℂ)) *
      (((1 / Real.sqrt (N : ℝ) : ℂ)) *
        inner ℂ
          (∑ y : Fin N,
            qftPhase N (ExtReg.toNat r b) y.1 •
              ket
                (RegEncoding.writeNat
                  r.active y.1 b))
          (∑ y : Fin N,
            qftPhase N (ExtReg.toNat r c) y.1 •
              ket
                (RegEncoding.writeNat
                  r.active y.1 c)))
      =
    inner ℂ (ket b) (ket c)

  by_cases hout : SameOutside r.active b c

  · rw [show
      inner ℂ
          (∑ y : Fin N,
            qftPhase N (ExtReg.toNat r b) y.1 •
              ket
                (RegEncoding.writeNat
                  r.active y.1 b))
          (∑ y : Fin N,
            qftPhase N (ExtReg.toNat r c) y.1 •
              ket
                (RegEncoding.writeNat
                  r.active y.1 c))
        =
      ∑ y : Fin N,
        (starRingEnd ℂ)
            (qftPhase N (ExtReg.toNat r b) y.1) *
          qftPhase N (ExtReg.toNat r c) y.1 by
        simpa [qftSumsInner, N, hout] using hsums]

    rw [← mul_assoc, qft_normalization N hN]

    rw [
      qftPhase_orthogonality
        N
        (ExtReg.toNat r b)
        (ExtReg.toNat r c)
        hb hc
    ]

    have heq :
        ExtReg.toNat r b =
            ExtReg.toNat r c ↔
          b = c := by
      constructor
      · intro hread
        apply basis_eq_of_toNat_eq_of_sameOutside r.active
        · exact hread
        · exact hout
      · intro hbc
        subst c
        rfl

    rw [if_congr heq rfl rfl]

    exact (ket_inner_eq_ite b c).symm

  · have hzero :
      inner ℂ
          (∑ y : Fin N,
            qftPhase N (ExtReg.toNat r b) y.1 •
              ket
                (RegEncoding.writeNat
                  r.active y.1 b))
          (∑ y : Fin N,
            qftPhase N (ExtReg.toNat r c) y.1 •
              ket
                (RegEncoding.writeNat
                  r.active y.1 c))
        =
      0 := by
      simpa [qftSumsInner, N, hout] using hsums

    rw [hzero]
    simp

    have hbc : b ≠ c := by
      intro h
      subst c
      apply hout
      intro q hq
      rfl

    exact (inner_ket_ne_concrete hbc).symm

theorem cSignedPhaseKet_inner_preserved
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (b c : Basis) :
    inner ℂ
        (cSignedPhaseKet ctrl phi x z b)
        (cSignedPhaseKet ctrl phi x z c) =
      inner ℂ (ket b) (ket c) := by
  unfold cSignedPhaseKet

  by_cases hb : RegEncoding.bit ctrl b
  · rw [if_pos hb]

    by_cases hc : RegEncoding.bit ctrl c
    · rw [if_pos hc]
      exact signedPhaseKet_inner_preserved phi x z b c

    · rw [if_neg hc]
      have hbc : b ≠ c := by
        intro h
        subst c
        exact hc hb

      unfold signedPhaseKet
      rw [inner_smul_left]
      rw [inner_ket_ne_concrete hbc]
      simp

  · rw [if_neg hb]

    by_cases hc : RegEncoding.bit ctrl c
    · rw [if_pos hc]

      have hbc : b ≠ c := by
        intro h
        subst c
        exact hb hc

      unfold signedPhaseKet
      rw [inner_smul_right]
      rw [inner_ket_ne_concrete hbc]
      simp

    · rw [if_neg hc]
/--
Every atomic gate preserves the concrete inner product.

For basis gates this reduces to injectivity/bijectivity of `atomBasisMap`.
For H this is the usual two-dimensional Hadamard calculation.
For QFT it is finite Fourier orthogonality.
For phase gates it follows because the phase has norm one.
-/
theorem atomKet_inner_preserved
    (U : Gate)
    (b c : Basis) :
    inner ℂ (atomKet U b) (atomKet U c) =
      inner ℂ (ket b) (ket c) := by
  cases U with

  | H q =>
      exact hadamardKet_inner_preserved q b c

  | QFT r =>
      exact qftKet_inner_preserved r b c

  | SignedPhaseProd phi x z =>
      exact signedPhaseKet_inner_preserved phi x z b c

  | CSignedPhaseProd ctrl phi x z =>
      exact cSignedPhaseKet_inner_preserved ctrl phi x z b c

  | id =>
      change
        inner ℂ
            (ket (atomBasisMap Gate.id b))
            (ket (atomBasisMap Gate.id c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap Gate.id)
        (atomBasisMap_injective Gate.id)
        b c

  | seq U V =>
      let G := Gate.seq U V
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | adj U =>
      let G := Gate.adj U
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | X q =>
      let G := Gate.X q
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | CNOT ctrl target =>
      let G := Gate.CNOT ctrl target
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | Toffoli c₁ c₂ target =>
      let G := Gate.Toffoli c₁ c₂ target
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | RadixReverse r m =>
      let G := Gate.RadixReverse r m
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | CmpGeConst N data scratch flag =>
      let G := Gate.CmpGeConst N data scratch flag
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | CSubConst N data scratch flag =>
      let G := Gate.CSubConst N data scratch flag
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | ShiftL r n =>
      let G := Gate.ShiftL r n
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | ShiftR r n =>
      let G := Gate.ShiftR r n
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | Negate r =>
      let G := Gate.Negate r
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | AddScaled dst src negSrc sh =>
      let G := Gate.AddScaled dst src negSrc sh
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | zeroExtend r n =>
      let G := Gate.zeroExtend r n
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | signExtend r n =>
      let G := Gate.signExtend r n
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | zeroDealloc r n =>
      let G := Gate.zeroDealloc r n
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | signDealloc r n =>
      let G := Gate.signDealloc r n
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

  | idealCtrlModMul a N data ctrl =>
      let G := Gate.idealCtrlModMul a N data ctrl
      change
        inner ℂ
            (ket (atomBasisMap G b))
            (ket (atomBasisMap G c)) =
          inner ℂ (ket b) (ket c)
      exact ket_map_inner_preserved_of_injective
        (atomBasisMap G)
        (atomBasisMap_injective G)
        b c

theorem atomEval_inner_preserved
    (U : Gate)
    (ψ φ : State) :
    inner ℂ (atomEvalLinear U ψ) (atomEvalLinear U φ) =
      inner ℂ ψ φ := by
  apply linearMap_inner_preserved_of_ket
  intro b c
  simp [atomKet_inner_preserved U b c]

/--
Generic "glue" step for the left-inverse direction: if, for a particular
gate `U`, `atomKet`/`atomAdjKet` reduce to the basis-permutation form
(true for every gate except `H`, `QFT`, `SignedPhaseProd`,
`CSignedPhaseProd`), then the atomic adjoint undoes the atomic evaluator
on a computational basis ket, using only injectivity of `atomBasisMap U`.
-/
private lemma atomAdjEval_atomEval_ket_of_glue
    (U : Gate)
    (hU : ∀ x, atomKet U x = ket (atomBasisMap U x))
    (hUadj : ∀ x, atomAdjKet U x = ket (inverseBasisMap (atomBasisMap U) x))
    (b : Basis) :
    atomAdjEvalLinear U (atomEvalLinear U (ket b)) = ket b := by
  rw [atomEvalLinear_ket, hU, atomAdjEvalLinear_ket, hUadj,
      inverseBasisMap_left (atomBasisMap U) (atomBasisMap_injective U) b]

/--
Generic "glue" step for the right-inverse direction: same hypotheses as
above, plus existence of an `atomBasisMap U`-preimage of `b` (which for a
bijective basis map always holds).
-/
private lemma atomEval_atomAdjEval_ket_of_glue
    (U : Gate)
    (hU : ∀ x, atomKet U x = ket (atomBasisMap U x))
    (hUadj : ∀ x, atomAdjKet U x = ket (inverseBasisMap (atomBasisMap U) x))
    (b : Basis)
    (hex : ∃ a, atomBasisMap U a = b) :
    atomEvalLinear U (atomAdjEvalLinear U (ket b)) = ket b := by
  rw [atomAdjEvalLinear_ket, hUadj, atomEvalLinear_ket, hU,
      inverseBasisMap_right (atomBasisMap U) hex]

/--
The concrete atomic adjoint is a left inverse of the atomic evaluator.

This holds unconditionally for every gate except `H`, `QFT`,
`SignedPhaseProd`, and `CSignedPhaseProd` (the state-level superposition
gates), which are left as explicit `sorry`s for a follow-up pass.
-/
theorem atomAdjEval_atomEval
    (U : Gate)
    (ψ : State) :
    atomAdjEvalLinear U (atomEvalLinear U ψ) = ψ := by
  refine concreteQSemantics.state_induction
    (fun ψ => atomAdjEvalLinear U (atomEvalLinear U ψ) = ψ)
    ?_ ?_ ?_ ?_ ψ
  · simp
  · intro ψ₁ ψ₂ h₁ h₂
    rw [map_add, map_add, h₁, h₂]
  · intro a ψ hψ
    rw [map_smul, map_smul, hψ]
  · intro b
    cases U with
    | id =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | seq p q =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | adj p =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | H q =>
        sorry
    | X q =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | CNOT ctrl target =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | Toffoli c₁ c₂ target =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | QFT r =>
        sorry
    | RadixReverse r m =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | SignedPhaseProd phi x z =>
        sorry
    | CSignedPhaseProd ctrl phi x z =>
        sorry
    | CmpGeConst N data scratch flag =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | CSubConst N data scratch flag =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | ShiftL r n =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | ShiftR r n =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | Negate r =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | AddScaled dst src negSrc sh =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | zeroExtend r n =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | signExtend r n =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | zeroDealloc r n =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | signDealloc r n =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b
    | idealCtrlModMul c N data ctrl =>
        exact atomAdjEval_atomEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl) b

/--
The concrete atomic adjoint is also a right inverse of the atomic
evaluator.

As with `atomAdjEval_atomEval`, this holds unconditionally for every gate
except `H`, `QFT`, `SignedPhaseProd`, and `CSignedPhaseProd`, which are
left as explicit `sorry`s for a follow-up pass.
-/
theorem atomEval_atomAdjEval
    (U : Gate)
    (ψ : State) :
    atomEvalLinear U (atomAdjEvalLinear U ψ) = ψ := by
  refine concreteQSemantics.state_induction
    (fun ψ => atomEvalLinear U (atomAdjEvalLinear U ψ) = ψ)
    ?_ ?_ ?_ ?_ ψ
  · simp
  · intro ψ₁ ψ₂ h₁ h₂
    rw [map_add, map_add, h₁, h₂]
  · intro a ψ hψ
    rw [map_smul, map_smul, hψ]
  · intro b
    cases U with
    | id =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b ⟨b, rfl⟩
    | seq p q =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b ⟨b, rfl⟩
    | adj p =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b ⟨b, rfl⟩
    | H q =>
        sorry
    | X q =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b (exists_preimage_of_injective_of_sameOutside
            (atomBasisMap (Gate.X q)) (qubitReg q)
            (atomBasisMap_injective (Gate.X q))
            (fun x => by simpa [atomBasisMap] using xBasis_sameOutside q x) b)
    | CNOT ctrl target =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b (exists_preimage_of_injective_of_sameOutside
            (atomBasisMap (Gate.CNOT ctrl target)) (qubitReg target)
            (atomBasisMap_injective (Gate.CNOT ctrl target))
            (fun x => by simpa [atomBasisMap] using cnotBasis_sameOutside ctrl target x) b)
    | Toffoli c₁ c₂ target =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b (exists_preimage_of_injective_of_sameOutside
            (atomBasisMap (Gate.Toffoli c₁ c₂ target)) (qubitReg target)
            (atomBasisMap_injective (Gate.Toffoli c₁ c₂ target))
            (fun x => by simpa [atomBasisMap] using toffoliBasis_sameOutside c₁ c₂ target x) b)
    | QFT r =>
        sorry
    | RadixReverse r m =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b (exists_preimage_of_injective_of_sameOutside
            (atomBasisMap (Gate.RadixReverse r m)) r
            (atomBasisMap_injective (Gate.RadixReverse r m))
            (fun x => by simpa [atomBasisMap] using radixReverseBasis_sameOutside r m x) b)
    | SignedPhaseProd phi x z =>
        sorry
    | CSignedPhaseProd ctrl phi x z =>
        sorry
    | CmpGeConst N data scratch flag =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b (exists_preimage_of_injective_of_sameOutside
            (atomBasisMap (Gate.CmpGeConst N data scratch flag)) (qubitReg flag)
            (atomBasisMap_injective (Gate.CmpGeConst N data scratch flag))
            (fun x => by simpa [atomBasisMap] using cmpGeConstBasis_sameOutside N data.active flag x) b)
    | CSubConst N data scratch flag =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b (exists_preimage_of_injective_of_sameOutside
            (atomBasisMap (Gate.CSubConst N data scratch flag)) data.active
            (atomBasisMap_injective (Gate.CSubConst N data scratch flag))
            (fun x => by simpa [atomBasisMap] using csubConstBasis_sameOutside N data.active flag x) b)
    | ShiftL r n =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b ⟨shiftRBasis r n b, shiftLBasis_shiftRBasis_concrete r n b⟩
    | ShiftR r n =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b ⟨shiftLBasis r n b, shiftRBasis_shiftLBasis_concrete r n b⟩
    | Negate r =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b ⟨negateBasis r b, negateBasis_negateBasis_concrete r b⟩
    | AddScaled dst src negSrc sh =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b (exists_preimage_of_injective_of_sameOutside
            (atomBasisMap (Gate.AddScaled dst src negSrc sh)) dst.active
            (atomBasisMap_injective (Gate.AddScaled dst src negSrc sh))
            (fun x => by simpa [atomBasisMap] using addScaledBasis_sameOutside dst src negSrc sh x) b)
    | zeroExtend r n =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b ⟨b, rfl⟩
    | signExtend r n =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b ⟨signExtendBasis r n b, signExtendBasis_involutive r n b⟩
    | zeroDealloc r n =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b ⟨b, rfl⟩
    | signDealloc r n =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b ⟨signExtendBasis r n b, signExtendBasis_involutive r n b⟩
    | idealCtrlModMul c N data ctrl =>
        exact atomEval_atomAdjEval_ket_of_glue _ (fun _ => rfl) (fun _ => rfl)
          b (exists_preimage_of_injective_of_sameOutside
            (atomBasisMap (Gate.idealCtrlModMul c N data ctrl)) data
            (atomBasisMap_injective (Gate.idealCtrlModMul c N data ctrl))
            (fun x => by
              simpa [atomBasisMap] using
                idealCtrlModMulBasisConcrete_sameOutside c N data ctrl x)
            b)

/-! =========================================================
    Structural inverse theorem
========================================================= -/

theorem evalGate_inverse_pair
    (U : Gate) :
    (∀ ψ : State,
      evalGateAdjLinear U (evalGateLinear U ψ) = ψ)
    ∧
    (∀ ψ : State,
      evalGateLinear U (evalGateAdjLinear U ψ) = ψ) := by
  induction U with
  | id =>
      constructor <;> intro ψ <;> rfl

  | seq U V ihU ihV =>
      constructor
      · intro ψ
        change
          evalGateAdjLinear U
              (evalGateAdjLinear V
                (evalGateLinear V
                  (evalGateLinear U ψ))) =
            ψ
        rw [ihV.1, ihU.1]

      · intro ψ
        change
          evalGateLinear V
              (evalGateLinear U
                (evalGateAdjLinear U
                  (evalGateAdjLinear V ψ))) =
            ψ
        rw [ihU.2, ihV.2]

  | adj U ih =>
      constructor
      · exact ih.2
      · exact ih.1

  | H q =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.H q) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.H q) ψ

  | X q =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.X q) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.X q) ψ

  | CNOT ctrl target =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.CNOT ctrl target) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.CNOT ctrl target) ψ

  | Toffoli c₁ c₂ target =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.Toffoli c₁ c₂ target) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.Toffoli c₁ c₂ target) ψ

  | QFT r =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.QFT r) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.QFT r) ψ

  | RadixReverse r m =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.RadixReverse r m) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.RadixReverse r m) ψ

  | SignedPhaseProd phi x z =>
      constructor
      · intro ψ
        exact
          atomAdjEval_atomEval
            (Gate.SignedPhaseProd phi x z) ψ
      · intro ψ
        exact
          atomEval_atomAdjEval
            (Gate.SignedPhaseProd phi x z) ψ

  | CSignedPhaseProd ctrl phi x z =>
      constructor
      · intro ψ
        exact
          atomAdjEval_atomEval
            (Gate.CSignedPhaseProd ctrl phi x z) ψ
      · intro ψ
        exact
          atomEval_atomAdjEval
            (Gate.CSignedPhaseProd ctrl phi x z) ψ

  | CmpGeConst N data scratch flag =>
      constructor
      · intro ψ
        exact
          atomAdjEval_atomEval
            (Gate.CmpGeConst N data scratch flag) ψ
      · intro ψ
        exact
          atomEval_atomAdjEval
            (Gate.CmpGeConst N data scratch flag) ψ

  | CSubConst N data scratch flag =>
      constructor
      · intro ψ
        exact
          atomAdjEval_atomEval
            (Gate.CSubConst N data scratch flag) ψ
      · intro ψ
        exact
          atomEval_atomAdjEval
            (Gate.CSubConst N data scratch flag) ψ

  | ShiftL r n =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.ShiftL r n) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.ShiftL r n) ψ

  | ShiftR r n =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.ShiftR r n) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.ShiftR r n) ψ

  | Negate r =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.Negate r) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.Negate r) ψ

  | AddScaled dst src negSrc sh =>
      constructor
      · intro ψ
        exact
          atomAdjEval_atomEval
            (Gate.AddScaled dst src negSrc sh) ψ
      · intro ψ
        exact
          atomEval_atomAdjEval
            (Gate.AddScaled dst src negSrc sh) ψ

  | zeroExtend r n =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.zeroExtend r n) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.zeroExtend r n) ψ

  | signExtend r n =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.signExtend r n) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.signExtend r n) ψ

  | zeroDealloc r n =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.zeroDealloc r n) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.zeroDealloc r n) ψ

  | signDealloc r n =>
      constructor
      · intro ψ
        exact atomAdjEval_atomEval (Gate.signDealloc r n) ψ
      · intro ψ
        exact atomEval_atomAdjEval (Gate.signDealloc r n) ψ

  | idealCtrlModMul c N data ctrl =>
      constructor
      · intro ψ
        exact
          atomAdjEval_atomEval
            (Gate.idealCtrlModMul c N data ctrl) ψ
      · intro ψ
        exact
          atomEval_atomAdjEval
            (Gate.idealCtrlModMul c N data ctrl) ψ

theorem evalGate_adj_apply
    (U : Gate)
    (ψ : State) :
    evalGate (Gate.adj U) (evalGate U ψ) = ψ := by
  exact (evalGate_inverse_pair U).1 ψ

/-! =========================================================
    Structural inner-product preservation
========================================================= -/

theorem evalGate_inner_preserved
    (U : Gate)
    (ψ φ : State) :
    inner ℂ (evalGate U ψ) (evalGate U φ) =
      inner ℂ ψ φ := by
  induction U generalizing ψ φ with
  | id =>
      rfl

  | seq U V ihU ihV =>
      simpa [evalGate] using
        (ihV (evalGate U ψ) (evalGate U φ)).trans
          (ihU ψ φ)

  | adj U ih =>
      change
        inner ℂ
            (evalGateAdjLinear U ψ)
            (evalGateAdjLinear U φ)
          =
        inner ℂ ψ φ

      have h :=
        ih
          (evalGateAdjLinear U ψ)
          (evalGateAdjLinear U φ)

      have hinv := evalGate_inverse_pair U

      have h' :
          inner ℂ ψ φ =
            inner ℂ
              (evalGateAdjLinear U ψ)
              (evalGateAdjLinear U φ) := by
        simpa [evalGate, hinv.2 ψ, hinv.2 φ] using h

      exact h'.symm

  | H q =>
      exact atomEval_inner_preserved (Gate.H q) ψ φ

  | X q =>
      exact atomEval_inner_preserved (Gate.X q) ψ φ

  | CNOT ctrl target =>
      exact
        atomEval_inner_preserved
          (Gate.CNOT ctrl target) ψ φ

  | Toffoli c₁ c₂ target =>
      exact
        atomEval_inner_preserved
          (Gate.Toffoli c₁ c₂ target) ψ φ

  | QFT r =>
      exact atomEval_inner_preserved (Gate.QFT r) ψ φ

  | RadixReverse r m =>
      exact
        atomEval_inner_preserved
          (Gate.RadixReverse r m) ψ φ

  | SignedPhaseProd phi x z =>
      exact
        atomEval_inner_preserved
          (Gate.SignedPhaseProd phi x z) ψ φ

  | CSignedPhaseProd ctrl phi x z =>
      exact
        atomEval_inner_preserved
          (Gate.CSignedPhaseProd ctrl phi x z) ψ φ

  | CmpGeConst N data scratch flag =>
      exact
        atomEval_inner_preserved
          (Gate.CmpGeConst N data scratch flag) ψ φ

  | CSubConst N data scratch flag =>
      exact
        atomEval_inner_preserved
          (Gate.CSubConst N data scratch flag) ψ φ

  | ShiftL r n =>
      exact
        atomEval_inner_preserved
          (Gate.ShiftL r n) ψ φ

  | ShiftR r n =>
      exact
        atomEval_inner_preserved
          (Gate.ShiftR r n) ψ φ

  | Negate r =>
      exact
        atomEval_inner_preserved
          (Gate.Negate r) ψ φ

  | AddScaled dst src negSrc sh =>
      exact
        atomEval_inner_preserved
          (Gate.AddScaled dst src negSrc sh) ψ φ

  | zeroExtend r n =>
      exact
        atomEval_inner_preserved
          (Gate.zeroExtend r n) ψ φ

  | signExtend r n =>
      exact
        atomEval_inner_preserved
          (Gate.signExtend r n) ψ φ

  | zeroDealloc r n =>
      exact
        atomEval_inner_preserved
          (Gate.zeroDealloc r n) ψ φ

  | signDealloc r n =>
      exact
        atomEval_inner_preserved
          (Gate.signDealloc r n) ψ φ

  | idealCtrlModMul c N data ctrl =>
      exact
        atomEval_inner_preserved
          (Gate.idealCtrlModMul c N data ctrl) ψ φ

/-! =========================================================
    Concrete GateSemanticsCore instance
========================================================= -/

noncomputable instance instGateSemanticsCore :
    GateSemanticsCore concreteQSemantics where

  eval := evalGate

  eval_id := by
    intro ψ
    exact evalGate_id ψ

  eval_seq := by
    intro U V ψ
    exact evalGate_seq U V ψ

  inner_preserved := by
    intro U ψ φ
    exact evalGate_inner_preserved U ψ φ

  eval_add := by
    intro U ψ φ
    exact evalGate_add U ψ φ

  eval_smul := by
    intro U a ψ
    exact evalGate_smul U a ψ

  eval_adj_apply := by
    intro U ψ
    exact evalGate_adj_apply U ψ

end ConcreteQSemantics

end Shor
