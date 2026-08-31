import FastMultiplication.ShorVerification.Implementation.PhaseProduct.NaivePhaseProduct

namespace Shor

namespace LowGate

noncomputable def CCPhase
    (a b c : ℕ)
    (theta : ℝ) : LowGate :=
  if a = b then
    LowGate.CPhase a c theta
  else if a = c then
    LowGate.CPhase a b theta
  else if b = c then
    LowGate.CPhase a b theta
  else
    LowGate.CPhase a b (theta / 2) ;;
    LowGate.Phase c (theta / 2) ;;
    LowGate.Toffoli a b c ;;
    LowGate.Phase c (-theta / 2) ;;
    LowGate.Toffoli a b c

noncomputable def naiveCSignedPhaseGates
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg) : List LowGate :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm =>
      LowGate.CCPhase
        ctrl
        xTerm.1
        zTerm.1
        (signedPairAngle phi xTerm zTerm)

noncomputable def Naive_CSignedPhaseProd
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg) : LowGate :=
  LowGate.sequence
    (naiveCSignedPhaseGates ctrl phi x z)

end LowGate

namespace LowerGateClass

theorem bit_toffoliBasis_of_ne_target
    {Basis : Type u}
    [RegEncoding Basis]
    (c₁ c₂ target q : ℕ)
    (b : Basis)
    (hq : q ≠ target) :
    RegEncoding.bit q (toffoliBasis c₁ c₂ target b) =
      RegEncoding.bit q b := by
  by_cases hbad : c₁ = c₂ ∨ c₁ = target ∨ c₂ = target
  · simp [toffoliBasis, hbad]
  · by_cases hctrl :
        RegEncoding.bit c₁ b ∧ RegEncoding.bit c₂ b
    · calc
        RegEncoding.bit q (toffoliBasis c₁ c₂ target b)
            =
          RegEncoding.bit q
            (RegEncoding.writeNat
              (qubitReg target)
              (if RegEncoding.bit target b then 0 else 1)
              b) := by
                simp [toffoliBasis, hbad, hctrl]
        _ = RegEncoding.bit q b := by
          apply RegEncoding.bit_writeNat_out
          simpa [qubitReg, Reg.singleton] using hq
    · simp [toffoliBasis, hbad, hctrl]

theorem bit_toffoliBasis_target_of_distinct
    {Basis : Type u}
    [RegEncoding Basis]
    (c₁ c₂ target : ℕ)
    (b : Basis)
    (h12 : c₁ ≠ c₂)
    (h1t : c₁ ≠ target)
    (h2t : c₂ ≠ target) :
    RegEncoding.bit target (toffoliBasis c₁ c₂ target b) =
      if RegEncoding.bit c₁ b ∧ RegEncoding.bit c₂ b then
        !RegEncoding.bit target b
      else
        RegEncoding.bit target b := by
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

private theorem forall₂_append
    {α β : Type*}
    {R : α → β → Prop}
    {xs us : List α}
    {ys vs : List β}
    (hxs : List.Forall₂ R xs ys)
    (hus : List.Forall₂ R us vs) :
    List.Forall₂ R (xs ++ us) (ys ++ vs) := by
  induction hxs with
  | nil =>
      simpa using hus
  | cons hxy _ ih =>
      simp
      exact ⟨hxy, ih⟩

noncomputable def cSignedPairExponent
    {Basis : Type*}
    [RegEncoding Basis]
    (ctrl : ℕ)
    (phi : ℝ)
    (b : Basis)
    (xTerm zTerm : ℕ × ℤ) : ℂ :=
  if RegEncoding.bit ctrl b then
    signedPairExponent phi b xTerm zTerm
  else
    0

noncomputable def naiveCSignedPhaseExponents
    {Basis : Type*}
    [RegEncoding Basis]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (b : Basis) : List ℂ :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm =>
      cSignedPairExponent ctrl phi b xTerm zTerm

theorem evalL_CCPhase_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (a c d : ℕ)
    (theta : ℝ)
    (b : qs.Basis) :
    LowerGateClass.evalL
        (qs := qs)
        (LowGate.CCPhase a c d theta)
        (qs.ket b)
      =
    Complex.exp
      ((theta : ℂ) * Complex.I *
        (((basisBitInt a b : ℤ) : ℂ) *
          (((basisBitInt c b : ℤ) : ℂ) *
           (((basisBitInt d b : ℤ) : ℂ))))) •
        qs.ket b := by
    by_cases hac : a = c
    · subst c
      cases ha : RegEncoding.bit a b <;>
        cases hd : RegEncoding.bit d b <;>
        simp [
          LowGate.CCPhase,
          evalL_CPhase_ket,
          basisBitInt,
          ha,
          hd
        ]
    · by_cases had : a = d
      · subst d
        cases ha : RegEncoding.bit a b <;>
          cases hc : RegEncoding.bit c b <;>
          simp [
            LowGate.CCPhase,
            hac,
            evalL_CPhase_ket,
            basisBitInt,
            ha,
            hc
          ]
      · by_cases hcd : c = d
        · subst d
          cases ha : RegEncoding.bit a b <;>
            cases hc : RegEncoding.bit c b <;>
            simp [
              LowGate.CCPhase,
              hac,
              evalL_CPhase_ket,
              basisBitInt,
              ha,
              hc
            ]
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
                  Complex.exp (↑theta / 2 * Complex.I) *
                      Complex.exp (-↑theta / 2 * Complex.I) =
                    1 by
                  simpa using complex_exp_half_cancel theta
              ]
              simp
            | rw [
                show
                  Complex.exp (↑theta / 2 * Complex.I) *
                      Complex.exp (↑theta / 2 * Complex.I) =
                    Complex.exp (↑theta * Complex.I) by
                  simpa using complex_exp_half_square theta
              ]

theorem evalL_cSignedPairPhase_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (xTerm zTerm : ℕ × ℤ)
    (b : qs.Basis) :
    LowerGateClass.evalL
        (qs := qs)
        (LowGate.CCPhase
          ctrl
          xTerm.1
          zTerm.1
          (signedPairAngle phi xTerm zTerm))
        (qs.ket b)
      =
    Complex.exp
        (cSignedPairExponent
          ctrl phi b xTerm zTerm) •
      qs.ket b := by
  rw [evalL_CCPhase_ket]
  by_cases hc : RegEncoding.bit ctrl b
  · simp [
      cSignedPairExponent,
      hc,
      signedPairExponent,
      signedPairAngle,
      signedTermValue,
      basisBitInt
    ]
    ring_nf
  · simp [
      cSignedPairExponent,
      hc,
      signedPairAngle,
      basisBitInt
    ]

theorem naiveCSignedPhaseGates_diagonal
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (b : qs.Basis) :
    List.Forall₂
      (fun g e =>
        LowerGateClass.evalL
            (qs := qs) g (qs.ket b)
          =
        Complex.exp e • qs.ket b)
        (LowGate.naiveCSignedPhaseGates ctrl phi x z)
        (naiveCSignedPhaseExponents ctrl phi x z b) := by
    unfold LowGate.naiveCSignedPhaseGates naiveCSignedPhaseExponents
    induction signedTerms x with
    | nil =>
        simp
    | cons xTerm xs ih =>
        have hhead :
            List.Forall₂
              (fun g e =>
                LowerGateClass.evalL
                    (qs := qs) g (qs.ket b)
                  =
                Complex.exp e • qs.ket b)
              ((signedTerms z).map fun zTerm =>
                LowGate.CCPhase
                  ctrl
                  xTerm.1
                  zTerm.1
                  (signedPairAngle phi xTerm zTerm))
              ((signedTerms z).map fun zTerm =>
                cSignedPairExponent
                  ctrl phi b xTerm zTerm) := by
          induction signedTerms z with
          | nil =>
              simp
          | cons zTerm zs ihz =>
              simp [evalL_cSignedPairPhase_ket, ihz]
        exact forall₂_append hhead ih

theorem evalL_naiveCSignedPhaseGates_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (b : qs.Basis) :
    LowerGateClass.evalL
        (qs := qs)
        (LowGate.sequence
          (LowGate.naiveCSignedPhaseGates
            ctrl phi x z))
        (qs.ket b)
      =
    Complex.exp
        (naiveCSignedPhaseExponents
          ctrl phi x z b).sum •
        qs.ket b := by
    exact
      evalL_sequence_of_diagonal
        b
        (LowGate.naiveCSignedPhaseGates ctrl phi x z)
        (naiveCSignedPhaseExponents ctrl phi x z b)
        (naiveCSignedPhaseGates_diagonal ctrl phi x z b)

private lemma sum_map_zero
    {α : Type*}
    (xs : List α) :
    (xs.map fun _ => (0 : ℂ)).sum = 0 := by
  induction xs with
  | nil =>
      rfl
  | cons _ xs ih =>
      simp

private lemma sum_flatMap_map_zero
    {α β : Type*}
    (xs : List α)
    (ys : List β) :
    (xs.flatMap fun _ => ys.map fun _ => (0 : ℂ)).sum = 0 := by
  induction xs with
  | nil =>
      rfl
  | cons _ xs ih =>
      change
        ((ys.map fun _ => (0 : ℂ)) ++
          (xs.flatMap fun _ => ys.map fun _ => (0 : ℂ))).sum = 0
      rw [List.sum_append, sum_map_zero ys, ih]
      simp

theorem naiveCSignedPhaseExponents_sum
    {Basis : Type*}
    [RegEncoding Basis]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (b : Basis) :
    (naiveCSignedPhaseExponents
        ctrl phi x z b).sum
      =
    if RegEncoding.bit ctrl b then
      (phi : ℂ) * Complex.I *
        (((extToInt x b : ℤ) : ℂ) *
         (((extToInt z b : ℤ) : ℂ)))
    else
      0 := by
  by_cases hc : RegEncoding.bit ctrl b
  · have h :
        naiveCSignedPhaseExponents ctrl phi x z b =
          naiveSignedPhaseExponents phi x z b := by
      simp [
        naiveCSignedPhaseExponents,
        naiveSignedPhaseExponents,
        cSignedPairExponent,
        hc
      ]
    rw [h, naiveSignedPhaseExponents_sum]
    simp [hc]
  · have h :
        (naiveCSignedPhaseExponents
          ctrl phi x z b).sum = 0 := by
      unfold naiveCSignedPhaseExponents
      simpa [cSignedPairExponent, hc] using
        sum_flatMap_map_zero (signedTerms x) (signedTerms z)
    rw [h]
    simp [hc]

theorem evalL_naive_csignedPhaseProd_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (b : qs.Basis) :
    LowerGateClass.evalL
        (qs := qs)
        (LowGate.Naive_CSignedPhaseProd ctrl phi x z)
        (qs.ket b)
      =
    if RegEncoding.bit ctrl b then
      (Complex.exp
        (phi * Complex.I *
          (((extToInt x b : ℤ) : ℂ) *
           (((extToInt z b : ℤ) : ℂ))))) •
        qs.ket b
    else
      qs.ket b := by
  unfold LowGate.Naive_CSignedPhaseProd
  rw [
    evalL_naiveCSignedPhaseGates_ket,
    naiveCSignedPhaseExponents_sum
  ]
  by_cases hc : RegEncoding.bit ctrl b
  · simp [hc]
  · simp [hc]

end LowerGateClass

namespace LowGate

lemma gateCount_CCPhase_of_distinct
    (M : LowGateCostModel)
    (a b c : ℕ)
    (theta : ℝ)
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    LowGate.gateCount M
        (LowGate.CCPhase a b c theta) = 9 := by
  simp [
    LowGate.CCPhase,
    LowGate.CPhase,
    LowGate.gateCount,
    hab,
    hac,
    hbc
  ]

lemma naiveCSignedPhaseGates_length
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg) :
    (LowGate.naiveCSignedPhaseGates ctrl phi x z).length =
      x.width * z.width := by
  unfold LowGate.naiveCSignedPhaseGates
  rw [LowerGateClass.flatMap_map_length]
  simp

theorem gateCount_Naive_CSignedPhaseProd
    (M : LowGateCostModel)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (hdisjoint : ExtReg.OwnedDisjoint x z)
    (hctrlX : ctrl ∉ x.ownedQubits)
    (hctrlZ : ctrl ∉ z.ownedQubits) :
    LowGate.gateCount M
        (LowGate.Naive_CSignedPhaseProd ctrl phi x z)
      =
    directCSignedPhaseProductGateCount x z := by
  have hgate :
      ∀ g ∈ LowGate.naiveCSignedPhaseGates ctrl phi x z,
        LowGate.gateCount M g = 9 := by
    intro g hg
    simp only [
      LowGate.naiveCSignedPhaseGates,
      List.mem_flatMap,
      List.mem_map
    ] at hg
    rcases hg with ⟨xTerm, hxTerm, zTerm, hzTerm, rfl⟩
    have hxactive :
        xTerm.1 ∈ x.active.qubits :=
      LowerGateClass.signedTerms_fst_mem hxTerm
    have hzactive :
        zTerm.1 ∈ z.active.qubits :=
      LowerGateClass.signedTerms_fst_mem hzTerm
    have hxowned :
        xTerm.1 ∈ x.ownedQubits := by
      simp [ExtReg.ownedQubits, hxactive]
    have hzowned :
        zTerm.1 ∈ z.ownedQubits := by
      simp [ExtReg.ownedQubits, hzactive]
    have hctrlXTerm : ctrl ≠ xTerm.1 := by
      intro h
      rw [← h] at hxowned
      exact hctrlX hxowned
    have hctrlZTerm : ctrl ≠ zTerm.1 := by
      intro h
      rw [← h] at hzowned
      exact hctrlZ hzowned
    have hxz :
        xTerm.1 ≠ zTerm.1 :=
      LowerGateClass.signedTerms_ne_of_ownedDisjoint
        x z hdisjoint hxTerm hzTerm
    exact
      LowGate.gateCount_CCPhase_of_distinct
        M ctrl xTerm.1 zTerm.1
        (signedPairAngle phi xTerm zTerm)
        hctrlXTerm
        hctrlZTerm
        hxz

  unfold LowGate.Naive_CSignedPhaseProd
  rw [LowerGateClass.LowGate.gateCount_sequence]
  rw [
    LowerGateClass.list_sum_map_eq_mul_length_of_constant
      (LowGate.gateCount M)
      9
      (LowGate.naiveCSignedPhaseGates ctrl phi x z)
      hgate
  ]
  rw [LowGate.naiveCSignedPhaseGates_length]
  unfold directCSignedPhaseProductGateCount
  simp [Nat.mul_assoc]

end LowGate
end Shor
