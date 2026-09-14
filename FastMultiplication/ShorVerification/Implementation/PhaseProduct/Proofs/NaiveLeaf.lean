import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.NaiveLeaf
import FastMultiplication.ShorVerification.Implementation.Shared.Registers

/-!
# Naive phase-product leaf: correctness

Correctness lemmas for the naive (reference) signed/controlled phase-product
circuits defined in `Gates/NaiveLeaf.lean`. The apex theorems
(`evalL_naive_signedPhaseProd_ket`, `gateCount_Naive_SignedPhaseProd`,
`evalL_naive_csignedPhaseProd_ket`, `gateCount_Naive_CSignedPhaseProd`) stay
here rather than in `Main.lean`: they are consumed by
`Proofs/Lowering/EvalL.lean` and `GateCount/PhaseProduct/Lemmas.lean`.
-/

namespace Shor

namespace LowerGateClass

@[simp] theorem bit_writeNat_qubitReg_zero
    {Basis : Type u} [RegEncoding Basis] (q : ℕ) (b : Basis) :
    RegEncoding.bit q (RegEncoding.writeNat (qubitReg q) 0 b) = false := by
  have h := RegEncoding.bit_writeNat_of_lt
    (qubitReg q) 0 b (by simp [ASize]) (⟨0, by simp⟩ : Fin (regSize (qubitReg q)))
  simpa [qubitReg, Reg.singleton, Reg.get, regSize, Reg.width] using h

@[simp] theorem bit_writeNat_qubitReg_one
    {Basis : Type u} [RegEncoding Basis] (q : ℕ) (b : Basis) :
    RegEncoding.bit q (RegEncoding.writeNat (qubitReg q) 1 b) = true := by
  have h := RegEncoding.bit_writeNat_of_lt
    (qubitReg q) 1 b (by simp [ASize]) (⟨0, by simp⟩ : Fin (regSize (qubitReg q)))
  simpa [qubitReg, Reg.singleton, Reg.get, regSize, Reg.width] using h

theorem bit_cnotBasis_of_ne_target
    {Basis : Type u} [RegEncoding Basis] (ctrl target q : ℕ) (b : Basis) (hq : q ≠ target) :
    RegEncoding.bit q (cnotBasis ctrl target b) = RegEncoding.bit q b := by
  by_cases hct : ctrl = target
  · simp [cnotBasis, hct]
  · cases hc : RegEncoding.bit ctrl b
    · simp [cnotBasis, hct, hc]
    · calc
        RegEncoding.bit q (cnotBasis ctrl target b)
            = RegEncoding.bit q
                (RegEncoding.writeNat
                  (qubitReg target) (if RegEncoding.bit target b then 0 else 1) b) := by
              simp [cnotBasis, hct, hc]
        _ = RegEncoding.bit q b := by
          apply RegEncoding.bit_writeNat_out
          simpa [qubitReg, Reg.singleton] using hq

@[simp] theorem bit_cnotBasis_ctrl
    {Basis : Type u} [RegEncoding Basis] (ctrl target : ℕ) (b : Basis) :
    RegEncoding.bit ctrl (cnotBasis ctrl target b) = RegEncoding.bit ctrl b := by
  by_cases hct : ctrl = target
  · simp [cnotBasis, hct]
  · exact bit_cnotBasis_of_ne_target ctrl target ctrl b hct

theorem bit_cnotBasis_target_of_ne
    {Basis : Type u} [RegEncoding Basis] (ctrl target : ℕ) (b : Basis) (hct : ctrl ≠ target) :
    RegEncoding.bit target (cnotBasis ctrl target b) =
      if RegEncoding.bit ctrl b then !RegEncoding.bit target b else RegEncoding.bit target b := by
  cases hc : RegEncoding.bit ctrl b
  · simp [cnotBasis, hct, hc]
  · cases ht : RegEncoding.bit target b
    · simp [cnotBasis, hct, hc, ht]
    · simp [cnotBasis, hct, hc, ht]

@[simp] theorem cnotBasis_involutive
    {Basis : Type u}
    [RegEncoding Basis]
    (ctrl target : ℕ)
    (b : Basis) :
    cnotBasis ctrl target (cnotBasis ctrl target b) = b := by
  by_cases hct : ctrl = target
  · simp [cnotBasis, hct]
  · apply RegEncoding.basis_ext
    intro q
    by_cases hqt : q = target
    · subst q
      rw [
        bit_cnotBasis_target_of_ne
          ctrl target (cnotBasis ctrl target b) hct,
        bit_cnotBasis_ctrl,
        bit_cnotBasis_target_of_ne ctrl target b hct
      ]
      cases RegEncoding.bit ctrl b <;>
        cases RegEncoding.bit target b <;>
        rfl
    · rw [
        bit_cnotBasis_of_ne_target
          ctrl target q (cnotBasis ctrl target b) hqt,
        bit_cnotBasis_of_ne_target
          ctrl target q b hqt
      ]

lemma complex_exp_half_cancel
    (theta : ℝ) :
    Complex.exp (((theta / 2 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((-theta / 2 : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [← Complex.exp_add]
  have h : (((theta / 2 : ℝ) : ℂ) * Complex.I) + (((-theta / 2 : ℝ) : ℂ) * Complex.I) = 0 := by
    push_cast
    ring
  rw [h]
  simp

lemma complex_exp_neg_half_cancel
    (theta : ℝ) :
    Complex.exp (((-theta / 2 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((theta / 2 : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [mul_comm]
  exact complex_exp_half_cancel theta

lemma complex_exp_half_square
    (theta : ℝ) :
    Complex.exp (((theta / 2 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((theta / 2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((theta : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem evalL_CPhase_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (ctrl target : ℕ) (theta : Angle) (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs) (LowGate.CPhase ctrl target theta) (qs.ket b)
      = Complex.exp
          (((Angle.toReal theta : ℝ) : ℂ) * Complex.I *
            ((((basisBitInt ctrl b : ℤ) : ℂ) * (((basisBitInt target b : ℤ) : ℂ))))) •
        qs.ket b := by
  by_cases hct : ctrl = target
  · subst target
    cases hb : RegEncoding.bit ctrl b <;>
      simp [LowGate.CPhase, basisBitInt, hb, LowerGateClass.evalL_Phase_ket]
  · cases hc : RegEncoding.bit ctrl b <;>
      cases ht : RegEncoding.bit target b
    · simp [
        LowGate.CPhase,
        hct,
        hc,
        ht,
        basisBitInt,
        LowerGateClass.evalL_seq,
        LowerGateClass.evalL_Phase_ket,
        LowerGateClass.evalL_CNOT_ket,
        cnotBasis
      ]
    · simp [
        LowGate.CPhase,
        hct,
        hc,
        ht,
        basisBitInt,
        LowerGateClass.evalL_seq,
        LowerGateClass.evalL_Phase_ket,
        LowerGateClass.evalL_CNOT_ket,
        LowerGateClass.evalL_smul,
        cnotBasis
      ]
      have hcancel :
          Complex.exp ((Angle.toReal (theta / 2) : ℝ) * Complex.I) *
            Complex.exp ((Angle.toReal (-theta / 2) : ℝ) * Complex.I) = 1 := by
        rw [Angle.toReal_div, Angle.toReal_div, Angle.toReal_neg]
        simpa using complex_exp_half_cancel (Angle.toReal theta)
      rw [smul_smul]
      rw [hcancel]
      simp
    · simp [
        LowGate.CPhase,
        hct,
        hc,
        ht,
        basisBitInt,
        LowerGateClass.evalL_seq,
        LowerGateClass.evalL_Phase_ket,
        LowerGateClass.evalL_CNOT_ket,
        LowerGateClass.evalL_smul,
        bit_cnotBasis_target_of_ne,
        cnotBasis_involutive,
        smul_smul
      ]
      have hcancel :
          Complex.exp ((Angle.toReal (theta / 2) : ℝ) * Complex.I) *
            Complex.exp ((Angle.toReal (-theta / 2) : ℝ) * Complex.I) = 1 := by
        rw [Angle.toReal_div, Angle.toReal_div, Angle.toReal_neg]
        simpa using complex_exp_half_cancel (Angle.toReal theta)
      rw [hcancel]
      simp
    · simp [
        LowGate.CPhase,
        hct,
        hc,
        ht,
        basisBitInt,
        LowerGateClass.evalL_seq,
        LowerGateClass.evalL_Phase_ket,
        LowerGateClass.evalL_CNOT_ket,
        LowerGateClass.evalL_smul,
        bit_cnotBasis_target_of_ne,
        cnotBasis_involutive,
        smul_smul
      ]
      have hsquare :
          Complex.exp ((Angle.toReal (theta / 2) : ℝ) * Complex.I) *
            Complex.exp ((Angle.toReal (theta / 2) : ℝ) * Complex.I)
            = Complex.exp ((Angle.toReal theta : ℝ) * Complex.I) := by
        rw [Angle.toReal_div]
        simpa using complex_exp_half_square (Angle.toReal theta)
      rw [hsquare]

theorem evalL_signedPairPhase_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (phi : Angle) (xTerm zTerm : ℕ × ℤ) (b : qs.Basis) :
    LowerGateClass.evalL
        (qs := qs) (LowGate.CPhase xTerm.1 zTerm.1 (signedPairAngle phi xTerm zTerm)) (qs.ket b)
      = Complex.exp (signedPairExponent phi b xTerm zTerm) • qs.ket b := by
  rw [evalL_CPhase_ket]
  congr 2
  simp only [signedPairExponent, signedPairAngle, signedTermValue, Angle.toReal]
  push_cast
  ring

theorem evalL_sequence_of_diagonal
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (b : qs.Basis) (gs : List LowGate) (es : List ℂ)
    (hdiag :
      List.Forall₂
        (fun g e => LowerGateClass.evalL (qs := qs) g (qs.ket b) = Complex.exp e • qs.ket b)
        gs es) :
    LowerGateClass.evalL (qs := qs) (LowGate.sequence gs) (qs.ket b)
      = Complex.exp es.sum • qs.ket b := by
  induction hdiag with
  | nil =>
      simp [LowGate.sequence, LowerGateClass.evalL_id]
  | @cons g e gs es hge hrest ih =>
      simp only [LowGate.sequence, List.sum_cons]
      rw [LowerGateClass.evalL_seq, hge, LowerGateClass.evalL_smul, ih]
      simp [Complex.exp_add, smul_smul]

private theorem forall₂_append
    {α β : Type*} {R : α → β → Prop} {xs us : List α} {ys vs : List β}
    (hxs : List.Forall₂ R xs ys) (hus : List.Forall₂ R us vs) :
    List.Forall₂ R (xs ++ us) (ys ++ vs) := by
  induction hxs with
  | nil =>
      simpa using hus
  | cons hxy _ ih =>
      simp
      exact ⟨hxy, ih⟩

theorem naiveSignedPhaseGates_diagonal
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (phi : Angle) (x z : ExtReg) (b : qs.Basis) :
    List.Forall₂
      (fun g e => LowerGateClass.evalL (qs := qs) g (qs.ket b) = Complex.exp e • qs.ket b)
      (LowGate.naiveSignedPhaseGates phi x z)
      (naiveSignedPhaseExponents phi x z b) := by
  unfold LowGate.naiveSignedPhaseGates naiveSignedPhaseExponents
  induction signedTerms x with
  | nil =>
      simp
  | cons xTerm xs ih =>
      have hhead :
          List.Forall₂
            (fun g e => LowerGateClass.evalL (qs := qs) g (qs.ket b) = Complex.exp e • qs.ket b)
            ((signedTerms z).map fun zTerm =>
              LowGate.CPhase xTerm.1 zTerm.1 (signedPairAngle phi xTerm zTerm))
            ((signedTerms z).map fun zTerm => signedPairExponent phi b xTerm zTerm) := by
        induction signedTerms z with
        | nil =>
            simp
        | cons zTerm zs ihz =>
            simp [evalL_signedPairPhase_ket, ihz]
      exact forall₂_append hhead ih

theorem evalL_naiveSignedPhaseGates_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (phi : Angle) (x z : ExtReg) (b : qs.Basis) :
    LowerGateClass.evalL
        (qs := qs) (LowGate.sequence (LowGate.naiveSignedPhaseGates phi x z)) (qs.ket b)
      = Complex.exp (naiveSignedPhaseExponents phi x z b).sum • qs.ket b := by
  exact evalL_sequence_of_diagonal
    b (LowGate.naiveSignedPhaseGates phi x z) (naiveSignedPhaseExponents phi x z b)
    (naiveSignedPhaseGates_diagonal phi x z b)

theorem toNat_qubitReg_eq_bit
    {Basis : Type*} [RegEncoding Basis] (q : ℕ) (b : Basis) :
    RegEncoding.toNat (qubitReg q) b = (RegEncoding.bit q b).toNat := by
  let n := RegEncoding.toNat (qubitReg q) b
  have hn : n < 2 := by
    simpa [n, ASize] using RegEncoding.toNat_lt_ASize (r := qubitReg q) (b := b)
  have hbit :
      RegEncoding.bit q b = Nat.testBit n 0 := by
    simpa [
      n,
      qubitReg,
      Reg.singleton,
      Reg.get,
      regSize,
      Reg.width
    ] using
      RegEncoding.bit_eq_testBit_toNat
        (qubitReg q) b
        (⟨0, by simp⟩ : Fin (regSize (qubitReg q)))
  change n = (RegEncoding.bit q b).toNat
  rw [hbit]
  interval_cases n <;> simp

lemma signedBitWeight_shift
    (width i : ℕ) :
    signedBitWeight (width + 1) (i + 1) =
      2 * signedBitWeight width i := by
    unfold signedBitWeight
    by_cases h : i + 1 = width
    · subst width
      simp [pow_succ, mul_comm]
    · have h' : i + 1 + 1 ≠ width + 1 := by
        omega
      simp [h, pow_succ, mul_comm]

lemma signedTermsAux_shift_sum
    {Basis : Type*}
    [RegEncoding Basis]
    (b : Basis)
    (width i : ℕ)
    (qs : List ℕ) :
    ((signedTermsAux (width + 1) (i + 1) qs).map
        (signedTermValue b)).sum
      =
    2 *
      ((signedTermsAux width i qs).map
        (signedTermValue b)).sum := by
  induction qs generalizing i with
  | nil =>
      simp [signedTermsAux]
  | cons q qs ih =>
      simp only [
        signedTermsAux,
        List.map_cons,
        List.sum_cons
      ]
      rw [signedBitWeight_shift]
      rw [ih (i := i + 1)]
      simp [signedTermValue]
      ring

lemma tcDecodeWidth_bit_cons
    (w n : ℕ) (a : Bool) (hw : 0 < w) :
    tcDecodeWidth (w + 1) (a.toNat + 2 * n) = (a.toNat : ℤ) + 2 * tcDecodeWidth w n := by
  cases w with
  | zero =>
      omega
  | succ w =>
      by_cases h : n < 2 ^ w
      · have ha : a.toNat ≤ 1 := by
          cases a <;> simp
        have hfull : a.toNat + 2 * n < 2 ^ (w + 1) := by
          rw [pow_succ]
          omega
        have hfull' : a.toNat + 2 * n < 2 ^ w * 2 := by
          simpa [pow_succ] using hfull
        simp [tcDecodeWidth, h, hfull', pow_succ]
      · have hn : 2 ^ w ≤ n := Nat.le_of_not_gt h
        have hfull : ¬ a.toNat + 2 * n < 2 ^ (w + 1) := by
          rw [pow_succ]
          omega
        have hfull' : ¬ a.toNat + 2 * n < 2 ^ w * 2 := by
          simpa [pow_succ] using hfull
        simp [tcDecodeWidth, h, hfull', pow_succ]
        ring_nf

lemma tcDecodeWidth_toNat_eq_signedTermsAux
    {Basis : Type*} [RegEncoding Basis] (b : Basis) :
    ∀ (qs : List ℕ) (hnd : qs.Nodup),
      tcDecodeWidth qs.length (RegEncoding.toNat (⟨qs, hnd⟩ : Reg) b)
        = ((signedTermsAux qs.length 0 qs).map (signedTermValue b)).sum := by
  intro qs
  induction qs with
  | nil =>
      intro hnd
      have hlt : RegEncoding.toNat (⟨[], hnd⟩ : Reg) b < 1 := by
        simpa [ASize, regSize, Reg.width] using
          RegEncoding.toNat_lt_ASize (r := (⟨[], hnd⟩ : Reg)) (b := b)
      have hz : RegEncoding.toNat (⟨[], hnd⟩ : Reg) b = 0 := by omega
      simp [tcDecodeWidth, signedTermsAux, hz]

  | cons q qs ih =>
      intro hnd
      have hnd' := List.nodup_cons.mp hnd
      have hq : q ∉ qs := hnd'.1
      have hqs : qs.Nodup := hnd'.2

      by_cases hempty : qs = []
      · subst qs
        have hr : (⟨[q], hnd⟩ : Reg) = qubitReg q := by simp [qubitReg, Reg.singleton]
        rw [hr, toNat_qubitReg_eq_bit]
        cases hb : RegEncoding.bit q b <;>
          simp [tcDecodeWidth, signedTermsAux, signedBitWeight, signedTermValue, basisBitInt, hb]

      · let tail : Reg := ⟨qs, hqs⟩
        have hdisj : Disjoint (qubitReg q) tail := by
          rw [Disjoint, List.disjoint_left]
          intro a ha hat
          have haq : a = q := by simpa [qubitReg, Reg.singleton] using ha
          subst a
          exact hq hat

        have happ : Reg.append (qubitReg q) tail hdisj = (⟨q :: qs, hnd⟩ : Reg) := by
          simp [Reg.append, qubitReg, Reg.singleton, tail]

        have hread := RegEncoding.toNat_append (qubitReg q) tail hdisj b

        rw [happ] at hread

        have hread' :
            RegEncoding.toNat (⟨q :: qs, hnd⟩ : Reg) b
              = (RegEncoding.bit q b).toNat + 2 * RegEncoding.toNat tail b := by
          calc
            RegEncoding.toNat (⟨q :: qs, hnd⟩ : Reg) b
                = RegEncoding.toNat (qubitReg q) b + ASize (qubitReg q) * RegEncoding.toNat tail b :=
              hread
            _ = (RegEncoding.bit q b).toNat + 2 * RegEncoding.toNat tail b := by
              rw [toNat_qubitReg_eq_bit]
              simp [ASize]

        have hpos : 0 < qs.length := by
          exact Nat.pos_of_ne_zero (fun hlen => hempty (List.length_eq_zero_iff.mp hlen))

        have htail :
            tcDecodeWidth qs.length (RegEncoding.toNat tail b)
              = ((signedTermsAux qs.length 0 qs).map (signedTermValue b)).sum := by
          simpa [tail] using ih hqs

        have hshift :
            ((signedTermsAux (qs.length + 1) 1 qs).map (signedTermValue b)).sum
              = 2 * ((signedTermsAux qs.length 0 qs).map (signedTermValue b)).sum := by
          simpa using signedTermsAux_shift_sum b qs.length 0 qs

        have hhead : signedBitWeight (qs.length + 1) 0 = 1 := by
          simp [signedBitWeight, hempty]

        simp only [List.length_cons]
        rw [hread']
        rw [tcDecodeWidth_bit_cons qs.length (RegEncoding.toNat tail b) (RegEncoding.bit q b) hpos]
        rw [htail]
        simp only [signedTermsAux, List.map_cons, List.sum_cons]
        rw [hhead, hshift]
        cases hb : RegEncoding.bit q b <;>
          simp [signedTermValue, basisBitInt, hb]

theorem extToInt_eq_signedTerms_sum
    {Basis : Type*} [RegEncoding Basis] (r : ExtReg) (b : Basis) :
    extToInt r b = ((signedTerms r).map (signedTermValue b)).sum := by
  unfold extToInt signedTerms ExtReg.toNat ExtReg.width
  exact tcDecodeWidth_toNat_eq_signedTermsAux b r.active.qubits r.active.nodup

private theorem sum_signedPairExponent_fixed
    {Basis : Type*} [RegEncoding Basis]
    (phi : Angle) (b : Basis) (xTerm : ℕ × ℤ) (zs : List (ℕ × ℤ)) :
    (zs.map fun zTerm => signedPairExponent phi b xTerm zTerm).sum
      = ((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
          (((signedTermValue b xTerm : ℤ) : ℂ) * ((((zs.map (signedTermValue b)).sum : ℤ) : ℂ))) := by
  induction zs with
  | nil =>
      simp [signedPairExponent]
  | cons zTerm zs ih =>
      rw [List.map_cons, List.sum_cons, ih]
      simp [signedPairExponent]
      ring_nf

theorem sum_signedPairExponent
    {Basis : Type*} [RegEncoding Basis] (phi : Angle) (b : Basis) (xs zs : List (ℕ × ℤ)) :
    (xs.flatMap fun xTerm => zs.map fun zTerm => signedPairExponent phi b xTerm zTerm).sum
      = ((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
          (((((xs.map (signedTermValue b)).sum : ℤ) : ℂ) *
            ((((zs.map (signedTermValue b)).sum : ℤ) : ℂ)))) := by
  induction xs with
  | nil =>
      simp
  | cons xTerm xs ih =>
      simp [sum_signedPairExponent_fixed, ih]
      ring_nf

theorem naiveSignedPhaseExponents_sum
    {Basis : Type*} [RegEncoding Basis] (phi : Angle) (x z : ExtReg) (b : Basis) :
    (naiveSignedPhaseExponents phi x z b).sum
      = ((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
          (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ))) := by
  unfold naiveSignedPhaseExponents
  rw [sum_signedPairExponent]
  rw [← extToInt_eq_signedTerms_sum x b, ← extToInt_eq_signedTerms_sum z b]

theorem evalL_naive_signedPhaseProd_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (phi : Angle) (x z : ExtReg) (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs) (LowGate.Naive_SignedPhaseProd phi x z) (qs.ket b)
      = (Complex.exp
          (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
            (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ))))) • qs.ket b := by
  unfold LowGate.Naive_SignedPhaseProd
  rw [evalL_naiveSignedPhaseGates_ket, naiveSignedPhaseExponents_sum]

lemma signedTermsAux_fst_mem
    {width i : ℕ} {qs : List ℕ} {t : ℕ × ℤ} (ht : t ∈ signedTermsAux width i qs) :
    t.1 ∈ qs := by
  induction qs generalizing i with
  | nil =>
      simp [signedTermsAux] at ht
  | cons q qs ih =>
      simp only [signedTermsAux, List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp
      · exact List.mem_cons_of_mem q (ih ht)

lemma signedTerms_fst_mem {r : ExtReg} {t : ℕ × ℤ} (ht : t ∈ signedTerms r) :
    t.1 ∈ r.active.qubits := by
  exact signedTermsAux_fst_mem (width := r.width) (i := 0) ht

@[simp] lemma signedTermsAux_length (width i : ℕ) (qs : List ℕ) :
    (signedTermsAux width i qs).length = qs.length := by
  induction qs generalizing i with
  | nil =>
      rfl
  | cons q qs ih =>
      simp [signedTermsAux, ih]

@[simp] lemma signedTerms_length (r : ExtReg) :
    (signedTerms r).length = r.width := by
  simp [signedTerms, ExtReg.width, regSize, Reg.width]

namespace LowGate

lemma gateCount_CPhase_of_ne
    (M : LowGateCostModel) (ctrl target : ℕ) (theta : Angle) (hne : ctrl ≠ target) :
    LowGate.gateCount M (LowGate.CPhase ctrl target theta) = 5 := by
  simp [LowGate.CPhase, hne, LowGate.gateCount]

lemma gateCount_sequence (M : LowGateCostModel) (gs : List LowGate) :
    LowGate.gateCount M (LowGate.sequence gs) = (gs.map (LowGate.gateCount M)).sum := by
  induction gs with
  | nil =>
      simp [LowGate.sequence, LowGate.gateCount]
  | cons g gs ih =>
      simp [LowGate.sequence, LowGate.gateCount, ih]

end LowGate

lemma list_sum_map_eq_mul_length_of_constant
    {α : Type*} (f : α → ℕ) (c : ℕ) (xs : List α) (h : ∀ x ∈ xs, f x = c) :
    (xs.map f).sum = c * xs.length := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : f x = c := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = c := by
        intro y hy
        exact h y (by simp [hy])
      rw [List.map_cons, List.sum_cons, hx, ih hxs]
      simp [Nat.mul_succ, Nat.add_comm]

lemma flatMap_map_length {α β γ : Type*} (xs : List α) (zs : List β) (f : α → β → γ) :
    (xs.flatMap fun x => zs.map fun z => f x z).length = xs.length * zs.length := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.succ_mul, Nat.add_comm]

lemma naiveSignedPhaseGates_length (phi : Angle) (x z : ExtReg) :
    (LowGate.naiveSignedPhaseGates phi x z).length = x.width * z.width := by
  unfold LowGate.naiveSignedPhaseGates
  rw [flatMap_map_length]
  simp

lemma signedTerms_ne_of_ownedDisjoint
    (x z : ExtReg) (hdisjoint : ExtReg.OwnedDisjoint x z)
    {xt zt : ℕ × ℤ} (hxt : xt ∈ signedTerms x) (hzt : zt ∈ signedTerms z) :
    xt.1 ≠ zt.1 := by
  have hxactive : xt.1 ∈ x.active.qubits := signedTerms_fst_mem hxt
  have hzactive : zt.1 ∈ z.active.qubits := signedTerms_fst_mem hzt
  have hxowned : xt.1 ∈ x.ownedQubits := by simp [ExtReg.ownedQubits, hxactive]
  have hzowned : zt.1 ∈ z.ownedQubits := by simp [ExtReg.ownedQubits, hzactive]
  rw [ExtReg.OwnedDisjoint, List.disjoint_left] at hdisjoint
  intro heq
  rw [← heq] at hzowned
  exact hdisjoint hxowned hzowned

theorem gateCount_Naive_SignedPhaseProd
    (M : LowGateCostModel) (phi : Angle) (x z : ExtReg) (hdisjoint : ExtReg.OwnedDisjoint x z) :
    LowGate.gateCount M (LowGate.Naive_SignedPhaseProd phi x z)
      = 5 * ExtReg.width x * ExtReg.width z := by
  have hgate : ∀ g ∈ LowGate.naiveSignedPhaseGates phi x z, LowGate.gateCount M g = 5 := by
    intro g hg
    simp only [LowGate.naiveSignedPhaseGates, List.mem_flatMap, List.mem_map] at hg
    rcases hg with ⟨xTerm, hxTerm, zTerm, hzTerm, rfl⟩
    apply LowGate.gateCount_CPhase_of_ne
    exact signedTerms_ne_of_ownedDisjoint x z hdisjoint hxTerm hzTerm

  unfold LowGate.Naive_SignedPhaseProd
  rw [LowGate.gateCount_sequence]
  rw [list_sum_map_eq_mul_length_of_constant
    (LowGate.gateCount M) 5 (LowGate.naiveSignedPhaseGates phi x z) hgate]
  rw [naiveSignedPhaseGates_length]
  simp [Nat.mul_assoc]

end LowerGateClass

namespace LowerGateClass

theorem bit_toffoliBasis_of_ne_target
    {Basis : Type u} [RegEncoding Basis] (c₁ c₂ target q : ℕ) (b : Basis) (hq : q ≠ target) :
    RegEncoding.bit q (toffoliBasis c₁ c₂ target b) = RegEncoding.bit q b := by
  by_cases hbad : c₁ = c₂ ∨ c₁ = target ∨ c₂ = target
  · simp [toffoliBasis, hbad]
  · by_cases hctrl : RegEncoding.bit c₁ b ∧ RegEncoding.bit c₂ b
    · calc
        RegEncoding.bit q (toffoliBasis c₁ c₂ target b)
            = RegEncoding.bit q
                (RegEncoding.writeNat
                  (qubitReg target) (if RegEncoding.bit target b then 0 else 1) b) := by
              simp [toffoliBasis, hbad, hctrl]
        _ = RegEncoding.bit q b := by
          apply RegEncoding.bit_writeNat_out
          simpa [qubitReg, Reg.singleton] using hq
    · simp [toffoliBasis, hbad, hctrl]

theorem bit_toffoliBasis_target_of_distinct
    {Basis : Type u} [RegEncoding Basis]
    (c₁ c₂ target : ℕ) (b : Basis) (h12 : c₁ ≠ c₂) (h1t : c₁ ≠ target) (h2t : c₂ ≠ target) :
    RegEncoding.bit target (toffoliBasis c₁ c₂ target b) =
      if RegEncoding.bit c₁ b ∧ RegEncoding.bit c₂ b
      then !RegEncoding.bit target b else RegEncoding.bit target b := by
  have hbad : ¬ (c₁ = c₂ ∨ c₁ = target ∨ c₂ = target) := by
    intro h
    rcases h with h | h | h
    · exact h12 h
    · exact h1t h
    · exact h2t h
  by_cases hctrl :
      RegEncoding.bit c₁ b ∧ RegEncoding.bit c₂ b
  · cases ht : RegEncoding.bit target b <;>
      simp [toffoliBasis, hbad, hctrl, ht]
  · simp [toffoliBasis, hbad, hctrl]

@[simp] theorem bit_toffoliBasis_ctrl_left
    {Basis : Type u}
    [RegEncoding Basis]
    (c₁ c₂ target : ℕ)
    (b : Basis)
    (h1t : c₁ ≠ target) :
    RegEncoding.bit c₁ (toffoliBasis c₁ c₂ target b) =
      RegEncoding.bit c₁ b :=
  bit_toffoliBasis_of_ne_target c₁ c₂ target c₁ b h1t

@[simp] theorem bit_toffoliBasis_ctrl_right
    {Basis : Type u}
    [RegEncoding Basis]
    (c₁ c₂ target : ℕ)
    (b : Basis)
    (h2t : c₂ ≠ target) :
    RegEncoding.bit c₂ (toffoliBasis c₁ c₂ target b) =
      RegEncoding.bit c₂ b :=
  bit_toffoliBasis_of_ne_target c₁ c₂ target c₂ b h2t

@[simp] theorem toffoliBasis_involutive
    {Basis : Type u}
    [RegEncoding Basis]
    (c₁ c₂ target : ℕ)
    (b : Basis) :
    toffoliBasis c₁ c₂ target
      (toffoliBasis c₁ c₂ target b) = b := by
  by_cases hbad : c₁ = c₂ ∨ c₁ = target ∨ c₂ = target
  · simp [toffoliBasis, hbad]
  · have h12 : c₁ ≠ c₂ := by
      intro h
      exact hbad (Or.inl h)
    have h1t : c₁ ≠ target := by
      intro h
      exact hbad (Or.inr (Or.inl h))
    have h2t : c₂ ≠ target := by
      intro h
      exact hbad (Or.inr (Or.inr h))
    apply RegEncoding.basis_ext
    intro q
    by_cases hqt : q = target
    · subst q
      rw [
        bit_toffoliBasis_target_of_distinct
          c₁ c₂ target
          (toffoliBasis c₁ c₂ target b)
          h12 h1t h2t,
        bit_toffoliBasis_ctrl_left c₁ c₂ target b h1t,
        bit_toffoliBasis_ctrl_right c₁ c₂ target b h2t,
        bit_toffoliBasis_target_of_distinct
          c₁ c₂ target b h12 h1t h2t
      ]
      cases RegEncoding.bit c₁ b <;>
        cases RegEncoding.bit c₂ b <;>
        cases RegEncoding.bit target b <;>
        rfl
    · rw [
        bit_toffoliBasis_of_ne_target
          c₁ c₂ target q
          (toffoliBasis c₁ c₂ target b)
          hqt,
        bit_toffoliBasis_of_ne_target
          c₁ c₂ target q b hqt
      ]

private theorem forall₂_append_cSignedPhase
    {α β : Type*} {R : α → β → Prop} {xs us : List α} {ys vs : List β}
    (hxs : List.Forall₂ R xs ys) (hus : List.Forall₂ R us vs) :
    List.Forall₂ R (xs ++ us) (ys ++ vs) := by
  induction hxs with
  | nil =>
      simpa using hus
  | cons hxy _ ih =>
      simp
      exact ⟨hxy, ih⟩

theorem evalL_CCPhase_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (a c d : ℕ) (theta : Angle) (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs) (LowGate.CCPhase a c d theta) (qs.ket b)
      = Complex.exp
          (((Angle.toReal theta : ℝ) : ℂ) * Complex.I *
            (((basisBitInt a b : ℤ) : ℂ) *
              (((basisBitInt c b : ℤ) : ℂ) * (((basisBitInt d b : ℤ) : ℂ))))) •
        qs.ket b := by
    by_cases hac : a = c
    · subst c
      cases ha : RegEncoding.bit a b <;>
        cases hd : RegEncoding.bit d b <;>
        simp [LowGate.CCPhase, evalL_CPhase_ket, basisBitInt, ha, hd]
    · by_cases had : a = d
      · subst d
        cases ha : RegEncoding.bit a b <;>
          cases hc : RegEncoding.bit c b <;>
          simp [LowGate.CCPhase, hac, evalL_CPhase_ket, basisBitInt, ha, hc]
      · by_cases hcd : c = d
        · subst d
          cases ha : RegEncoding.bit a b <;>
            cases hc : RegEncoding.bit c b <;>
            simp [LowGate.CCPhase, hac, evalL_CPhase_ket, basisBitInt, ha, hc]
        · cases ha : RegEncoding.bit a b <;>
            cases hc : RegEncoding.bit c b <;>
            cases hd : RegEncoding.bit d b <;>
            simp [
              LowGate.CCPhase,
              hac,
              had,
              hcd,
              evalL_CPhase_ket,
              LowerGateClass.evalL_seq,
              LowerGateClass.evalL_Phase_ket,
              LowerGateClass.evalL_Toffoli_ket,
              LowerGateClass.evalL_smul,
              basisBitInt,
              bit_toffoliBasis_target_of_distinct,
              toffoliBasis_involutive,
              ha,
              hc,
              hd,
              smul_smul
            ] <;>
            first
            | rw [
                show
                  Complex.exp ((Angle.toReal (theta / 2) : ℝ) * Complex.I) *
                      Complex.exp ((Angle.toReal (-theta / 2) : ℝ) * Complex.I) =
                    1 by
                  rw [Angle.toReal_div, Angle.toReal_div, Angle.toReal_neg]
                  simpa using complex_exp_half_cancel (Angle.toReal theta)
              ]
              simp
            | rw [
                show
                  Complex.exp ((Angle.toReal (theta / 2) : ℝ) * Complex.I) *
                      Complex.exp ((Angle.toReal (theta / 2) : ℝ) * Complex.I) =
                    Complex.exp ((Angle.toReal theta : ℝ) * Complex.I) by
                  rw [Angle.toReal_div]
                  simpa using complex_exp_half_square (Angle.toReal theta)
              ]

theorem evalL_cSignedPairPhase_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (ctrl : ℕ) (phi : Angle) (xTerm zTerm : ℕ × ℤ) (b : qs.Basis) :
    LowerGateClass.evalL
        (qs := qs) (LowGate.CCPhase ctrl xTerm.1 zTerm.1 (signedPairAngle phi xTerm zTerm)) (qs.ket b)
      = Complex.exp (cSignedPairExponent ctrl phi b xTerm zTerm) • qs.ket b := by
  rw [evalL_CCPhase_ket]
  by_cases hc : RegEncoding.bit ctrl b
  · simp only [
      cSignedPairExponent, hc, if_true, signedPairExponent, signedPairAngle, signedTermValue,
      basisBitInt, Angle.toReal
    ]
    push_cast
    ring_nf
  · simp [cSignedPairExponent, hc, signedPairAngle, basisBitInt]

theorem naiveCSignedPhaseGates_diagonal
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (ctrl : ℕ) (phi : Angle) (x z : ExtReg) (b : qs.Basis) :
    List.Forall₂
      (fun g e => LowerGateClass.evalL (qs := qs) g (qs.ket b) = Complex.exp e • qs.ket b)
        (LowGate.naiveCSignedPhaseGates ctrl phi x z)
        (naiveCSignedPhaseExponents ctrl phi x z b) := by
    unfold LowGate.naiveCSignedPhaseGates naiveCSignedPhaseExponents
    induction signedTerms x with
    | nil =>
        simp
    | cons xTerm xs ih =>
        have hhead :
            List.Forall₂
              (fun g e => LowerGateClass.evalL (qs := qs) g (qs.ket b) = Complex.exp e • qs.ket b)
              ((signedTerms z).map fun zTerm =>
                LowGate.CCPhase ctrl xTerm.1 zTerm.1 (signedPairAngle phi xTerm zTerm))
              ((signedTerms z).map fun zTerm => cSignedPairExponent ctrl phi b xTerm zTerm) := by
          induction signedTerms z with
          | nil =>
              simp
          | cons zTerm zs ihz =>
              simp [evalL_cSignedPairPhase_ket, ihz]
        exact forall₂_append_cSignedPhase hhead ih

theorem evalL_naiveCSignedPhaseGates_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (ctrl : ℕ) (phi : Angle) (x z : ExtReg) (b : qs.Basis) :
    LowerGateClass.evalL
        (qs := qs) (LowGate.sequence (LowGate.naiveCSignedPhaseGates ctrl phi x z)) (qs.ket b)
      = Complex.exp (naiveCSignedPhaseExponents ctrl phi x z b).sum • qs.ket b := by
    exact evalL_sequence_of_diagonal
      b (LowGate.naiveCSignedPhaseGates ctrl phi x z) (naiveCSignedPhaseExponents ctrl phi x z b)
      (naiveCSignedPhaseGates_diagonal ctrl phi x z b)

private lemma sum_map_zero {α : Type*} (xs : List α) :
    (xs.map fun _ => (0 : ℂ)).sum = 0 := by
  induction xs with
  | nil =>
      rfl
  | cons _ xs ih =>
      simp

private lemma sum_flatMap_map_zero {α β : Type*} (xs : List α) (ys : List β) :
    (xs.flatMap fun _ => ys.map fun _ => (0 : ℂ)).sum = 0 := by
  induction xs with
  | nil =>
      rfl
  | cons _ xs ih =>
      change ((ys.map fun _ => (0 : ℂ)) ++ (xs.flatMap fun _ => ys.map fun _ => (0 : ℂ))).sum = 0
      rw [List.sum_append, sum_map_zero ys, ih]
      simp

theorem naiveCSignedPhaseExponents_sum
    {Basis : Type*} [RegEncoding Basis] (ctrl : ℕ) (phi : Angle) (x z : ExtReg) (b : Basis) :
    (naiveCSignedPhaseExponents ctrl phi x z b).sum
      = if RegEncoding.bit ctrl b then
          ((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
            (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ)))
        else 0 := by
  by_cases hc : RegEncoding.bit ctrl b
  · have h : naiveCSignedPhaseExponents ctrl phi x z b = naiveSignedPhaseExponents phi x z b := by
      simp [naiveCSignedPhaseExponents, naiveSignedPhaseExponents, cSignedPairExponent, hc]
    rw [h, naiveSignedPhaseExponents_sum]
    simp [hc]
  · have h : (naiveCSignedPhaseExponents ctrl phi x z b).sum = 0 := by
      unfold naiveCSignedPhaseExponents
      simpa [cSignedPairExponent, hc] using
        sum_flatMap_map_zero (signedTerms x) (signedTerms z)
    rw [h]
    simp [hc]

theorem evalL_naive_csignedPhaseProd_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (ctrl : ℕ) (phi : Angle) (x z : ExtReg) (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs) (LowGate.Naive_CSignedPhaseProd ctrl phi x z) (qs.ket b)
      = if RegEncoding.bit ctrl b then
          (Complex.exp
            (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
              (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ))))) • qs.ket b
        else qs.ket b := by
  unfold LowGate.Naive_CSignedPhaseProd
  rw [evalL_naiveCSignedPhaseGates_ket, naiveCSignedPhaseExponents_sum]
  by_cases hc : RegEncoding.bit ctrl b
  · simp [hc]
  · simp [hc]

end LowerGateClass

namespace LowGate

lemma gateCount_CCPhase_of_distinct
    (M : LowGateCostModel) (a b c : ℕ) (theta : Angle)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LowGate.gateCount M (LowGate.CCPhase a b c theta) = 9 := by
  simp [LowGate.CCPhase, LowGate.CPhase, LowGate.gateCount, hab, hac, hbc]

lemma naiveCSignedPhaseGates_length (ctrl : ℕ) (phi : Angle) (x z : ExtReg) :
    (LowGate.naiveCSignedPhaseGates ctrl phi x z).length = x.width * z.width := by
  unfold LowGate.naiveCSignedPhaseGates
  rw [LowerGateClass.flatMap_map_length]
  simp

theorem gateCount_Naive_CSignedPhaseProd
    (M : LowGateCostModel) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (hdisjoint : ExtReg.OwnedDisjoint x z)
    (hctrlX : ctrl ∉ x.ownedQubits) (hctrlZ : ctrl ∉ z.ownedQubits) :
    LowGate.gateCount M (LowGate.Naive_CSignedPhaseProd ctrl phi x z)
      = 9 * ExtReg.width x * ExtReg.width z := by
  have hgate : ∀ g ∈ LowGate.naiveCSignedPhaseGates ctrl phi x z, LowGate.gateCount M g = 9 := by
    intro g hg
    simp only [LowGate.naiveCSignedPhaseGates, List.mem_flatMap, List.mem_map] at hg
    rcases hg with ⟨xTerm, hxTerm, zTerm, hzTerm, rfl⟩
    have hxactive : xTerm.1 ∈ x.active.qubits := LowerGateClass.signedTerms_fst_mem hxTerm
    have hzactive : zTerm.1 ∈ z.active.qubits := LowerGateClass.signedTerms_fst_mem hzTerm
    have hxowned : xTerm.1 ∈ x.ownedQubits := by simp [ExtReg.ownedQubits, hxactive]
    have hzowned : zTerm.1 ∈ z.ownedQubits := by simp [ExtReg.ownedQubits, hzactive]
    have hctrlXTerm : ctrl ≠ xTerm.1 := by
      intro h
      rw [← h] at hxowned
      exact hctrlX hxowned
    have hctrlZTerm : ctrl ≠ zTerm.1 := by
      intro h
      rw [← h] at hzowned
      exact hctrlZ hzowned
    have hxz : xTerm.1 ≠ zTerm.1 :=
      LowerGateClass.signedTerms_ne_of_ownedDisjoint x z hdisjoint hxTerm hzTerm
    exact LowGate.gateCount_CCPhase_of_distinct
      M ctrl xTerm.1 zTerm.1 (signedPairAngle phi xTerm zTerm) hctrlXTerm hctrlZTerm hxz

  unfold LowGate.Naive_CSignedPhaseProd
  rw [LowerGateClass.LowGate.gateCount_sequence]
  rw [LowerGateClass.list_sum_map_eq_mul_length_of_constant
    (LowGate.gateCount M) 9 (LowGate.naiveCSignedPhaseGates ctrl phi x z) hgate]
  rw [LowGate.naiveCSignedPhaseGates_length]
  simp [Nat.mul_assoc]

end LowGate
end Shor
