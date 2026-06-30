import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModMulBounds.Step1QPE

/-!
# Step-1 Main Bound

This file keeps the main Step-1/Step-5 packet reconstruction and uniform error
theorem. The QPE kernel analysis and basis-input tail estimate live in
`Step1QPE.lean`.
-/

open Shor

/-! ## Step-5 Packet Reconstruction From The Ideal Output -/

/--
Forward Step-5 fractional-load evaluation from the extended ideal-output
basis state.
-/
lemma alg1_step5_forward_packet_on_extended_output
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval
        (alg1Step5Forward (Basis := qs.Basis) cfg)
        (qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            b))
      =
    ∑ t : Fin (ASize cfg.env.work),
      alg1FractionalLoadCoeff cfg b t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work t.1
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b)) := by
  rw [alg1Step5Forward, qs.eval_seq, qs.eval_seq]
  have hpre := alg1_step5_forward_preIQFT_packet qs cfg b hb
  rw [qs.eval_seq] at hpre
  change
    qs.eval (IQFT cfg.env.work)
      (qs.eval
        (Gate.CPhaseProd cfg.ctrl (alg1Step5Phase cfg)
          (extendHi cfg.env.data) cfg.env.work)
        (qs.eval (H_reg cfg.env.work)
          (qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b))))
      =
    ∑ t : Fin (ASize cfg.env.work),
      alg1FractionalLoadCoeff cfg b t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work t.1
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b))
  rw [hpre]
  simpa [alg1FractionalLoadCoeff] using
    (eval_IQFT_work_packet
      qs
      cfg.env.work
      (RegEncoding.writeNat
        (extendHi cfg.env.data)
        (alg1OutputValue cfg b)
        b)
      (alg1LoadPreCoeff cfg b))


/-! =========================================================
    Final forward packet theorem
========================================================= -/

/--
The forward circuit associated with Step 5 reproduces the complete Step-1 QPE
packet, now based at the ideal modular-multiplication output.

The final proof contains no `sorry`; it only combines the proved packet,
coefficient, locality, and ideal-output lemmas.
-/
lemma alg1_step5_forward_packet_on_basis
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval
        ((H_reg cfg.env.work) ;;
          (Gate.CPhaseProd
            cfg.ctrl
            (alg1Step5Phase cfg)
            (extendHi cfg.env.data)
            cfg.env.work) ;;
          (IQFT cfg.env.work))
        (qs.eval (ModMulConfig.idealGate cfg) (qs.ket b))
      =
    ∑ t : Fin (ASize cfg.env.work),
      alg1PhaseCoeff qs cfg b t •
        qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b)) := by
  classical

  have hideal :
      qs.eval (ModMulConfig.idealGate cfg) (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          (alg1OutputValue cfg b)
          b) :=
    alg1_ideal_ket_eq_extended_output qs cfg b hb

  have hwork_ext :
      Disjoint cfg.env.work (extendHi cfg.env.data) := by
    rcases cfg.layout.1 with h | h
    · exact Or.inr h
    · exact Or.inl h

  rw [hideal]
  change
    qs.eval
        (alg1Step5Forward (Basis := qs.Basis) cfg)
        (qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            b))
      =
    _

  rw [alg1_step5_forward_packet_on_extended_output qs cfg b hb]

  apply Finset.sum_congr rfl
  intro t ht

  rw [← alg1PhaseCoeff_eq_fractionalLoadCoeff qs cfg b hb t]
  congr 1

  exact
    congrArg qs.ket
      (writeNat_comm_of_disjoint
        cfg.env.work
        (extendHi cfg.env.data)
        hwork_ext
        t.1
        (alg1OutputValue cfg b)
        b)



lemma alg1_step5_full_packet_on_basis
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
      (∑ t : Fin (ASize cfg.env.work),
        alg1PhaseCoeff qs cfg b t •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work t.1 b)))
      =
    qs.eval (ModMulConfig.idealGate cfg) (qs.ket b) := by
  rw [← alg1_step5_forward_packet_on_basis qs cfg b hb]
  simpa [ModMulConfig.U5, step5, alg1Step5Forward, alg1Step5Phase] using
    qs.eval_adj_apply
      (alg1Step5Forward (Basis := qs.Basis) cfg)
      (qs.eval (ModMulConfig.idealGate cfg) (qs.ket b))


lemma alg1_step5_full_packet_eq_ideal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
        tr.afterStep34Full
      =
    qs.eval (ModMulConfig.idealGate cfg) ψ := by
  classical
  rw [alg1_trace_afterStep34Full_eq_canonical qs cfg ψ tr]

  calc
    qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
        (∑ b ∈ tr.support,
          tr.inputCoeff b •
            ∑ t : Fin (ASize cfg.env.work),
              alg1PhaseCoeff qs cfg b t •
                qs.ket
                  (RegEncoding.writeNat
                    (extendHi cfg.env.data)
                    (alg1OutputValue cfg b)
                    (RegEncoding.writeNat cfg.env.work t.1 b)))
      =
    ∑ b ∈ tr.support,
      tr.inputCoeff b •
        qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
          (∑ t : Fin (ASize cfg.env.work),
            alg1PhaseCoeff qs cfg b t •
              qs.ket
                (RegEncoding.writeNat
                  (extendHi cfg.env.data)
                  (alg1OutputValue cfg b)
                  (RegEncoding.writeNat cfg.env.work t.1 b))) := by
        rw [eval_finset_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [qs.eval_smul]

    _ =
    ∑ b ∈ tr.support,
      tr.inputCoeff b •
        qs.eval (ModMulConfig.idealGate cfg) (qs.ket b) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [alg1_step5_full_packet_on_basis
          qs cfg b (tr.input_good b hb)]

    _ =
    qs.eval (ModMulConfig.idealGate cfg)
      (∑ b ∈ tr.support, tr.inputCoeff b • qs.ket b) := by
        symm
        rw [eval_finset_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [qs.eval_smul]

    _ =
    qs.eval (ModMulConfig.idealGate cfg) ψ := by
        exact
          (congrArg
            (fun φ : qs.State => qs.eval (ModMulConfig.idealGate cfg) φ)
            tr.input_eq).symm

lemma alg1_afterStep34Full_eq_good_add_bad
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    tr.afterStep34Full
      =
    tr.afterStep34Ref + tr.afterStep34Bad := by
  classical
  simp only [
    Alg1Trace.afterStep34Full,
    Alg1Trace.afterStep34Ref,
    Alg1Trace.afterStep34Bad
  ]

  have hsplit :
      ∀ b : qs.Basis,
        (∑ t : Fin (ASize cfg.env.work),
          tr.phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work t.1 b)))
          =
        (∑ t ∈ alg1GoodLabels cfg b,
          tr.phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work t.1 b)))
          +
        ∑ t ∈ Finset.univ.filter
            (fun t => t ∉ alg1GoodLabels cfg b),
          tr.phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work t.1 b)) := by
    intro b

    let p : Fin (ASize cfg.env.work) → Prop :=
      fun t => t ∈ alg1GoodLabels cfg b

    have hgood :
        Finset.univ.filter p = alg1GoodLabels cfg b := by
      ext t
      simp [p]

    have h :=
      sum_filter_add_sum_filter_not
        Finset.univ
        p
        (fun t =>
          tr.phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work t.1 b)))

    rw [hgood] at h
    exact h.symm

  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [hsplit b, smul_add]

/-! =========================================================
    Item 4: Step-5 residue arithmetic
========================================================= -/


lemma alg1_step34_label_injective
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b b' : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (hb' :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b')
    (t u : Fin (ASize cfg.env.work))
    (hEq :
      RegEncoding.writeNat
          (extendHi cfg.env.data)
          (alg1OutputValue cfg b)
          (RegEncoding.writeNat cfg.env.work t.1 b)
        =
      RegEncoding.writeNat
          (extendHi cfg.env.data)
          (alg1OutputValue cfg b')
          (RegEncoding.writeNat cfg.env.work u.1 b')) :
    b = b' ∧ t = u := by
  classical

  have hdisj :
      Disjoint cfg.env.work (extendHi cfg.env.data) := by
    rcases cfg.layout.1 with h | h
    · exact Or.inr h
    · exact Or.inl h

  have hout_cap :
      alg1OutputValue cfg b < ASize (extendHi cfg.env.data) := by
    have hdata := alg1OutputValue_lt_data_capacity cfg b hb
    have hle : ASize cfg.env.data ≤ ASize (extendHi cfg.env.data) := by
      simp [ASize, regSize, extendHi, Nat.pow_succ]
    exact lt_of_lt_of_le hdata hle

  have hout_cap' :
      alg1OutputValue cfg b' < ASize (extendHi cfg.env.data) := by
    have hdata := alg1OutputValue_lt_data_capacity cfg b' hb'
    have hle : ASize cfg.env.data ≤ ASize (extendHi cfg.env.data) := by
      simp [ASize, regSize, extendHi, Nat.pow_succ]
    exact lt_of_lt_of_le hdata hle

  have hout :
      alg1OutputValue cfg b = alg1OutputValue cfg b' := by
    calc
      alg1OutputValue cfg b
          =
        RegEncoding.toNat (extendHi cfg.env.data)
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b)) := by
          symm
          exact
            RegEncoding.toNat_writeNat_of_lt
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work t.1 b)
              hout_cap
      _ =
        RegEncoding.toNat (extendHi cfg.env.data)
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b')) := by
          exact congrArg (RegEncoding.toNat (extendHi cfg.env.data)) hEq
      _ =
        alg1OutputValue cfg b' :=
          RegEncoding.toNat_writeNat_of_lt
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b')
            hout_cap'

  have htu_val : t.1 = u.1 := by
    calc
      t.1
          =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b)) := by
          symm
          calc
            RegEncoding.toNat cfg.env.work
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work t.1 b))
                =
              RegEncoding.toNat cfg.env.work
                (RegEncoding.writeNat cfg.env.work t.1 b) :=
              RegEncoding.toNat_left_write_right
                cfg.env.work
                (extendHi cfg.env.data)
                hdisj
                (RegEncoding.writeNat cfg.env.work t.1 b)
                (alg1OutputValue cfg b)
            _ = t.1 :=
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work t.1 b t.isLt
      _ =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b')) := by
          exact congrArg (RegEncoding.toNat cfg.env.work) hEq
      _ = u.1 := by
          calc
            RegEncoding.toNat cfg.env.work
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1OutputValue cfg b')
                (RegEncoding.writeNat cfg.env.work u.1 b'))
                =
              RegEncoding.toNat cfg.env.work
                (RegEncoding.writeNat cfg.env.work u.1 b') :=
              RegEncoding.toNat_left_write_right
                cfg.env.work
                (extendHi cfg.env.data)
                hdisj
                (RegEncoding.writeNat cfg.env.work u.1 b')
                (alg1OutputValue cfg b')
            _ = u.1 :=
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work u.1 b' u.isLt

  have htu : t = u := Fin.ext htu_val

  have hctrl_b :
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b))
        =
      RegEncoding.bit cfg.ctrl b := by
    calc
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b))
          =
        RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat cfg.env.work t.1 b) :=
        RegEncoding.bit_writeNat_out
          (r := extendHi cfg.env.data)
          (v := alg1OutputValue cfg b)
          (b := RegEncoding.writeNat cfg.env.work t.1 b)
          (q := cfg.ctrl)
          cfg.layout.2.2.2.1
      _ = RegEncoding.bit cfg.ctrl b :=
        RegEncoding.bit_writeNat_out
          (r := cfg.env.work)
          (v := t.1)
          (b := b)
          (q := cfg.ctrl)
          cfg.layout.2.2.2.2.1

  have hctrl_b' :
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b'))
        =
      RegEncoding.bit cfg.ctrl b' := by
    calc
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b'))
          =
        RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat cfg.env.work u.1 b') :=
        RegEncoding.bit_writeNat_out
          (r := extendHi cfg.env.data)
          (v := alg1OutputValue cfg b')
          (b := RegEncoding.writeNat cfg.env.work u.1 b')
          (q := cfg.ctrl)
          cfg.layout.2.2.2.1
      _ = RegEncoding.bit cfg.ctrl b' :=
        RegEncoding.bit_writeNat_out
          (r := cfg.env.work)
          (v := u.1)
          (b := b')
          (q := cfg.ctrl)
          cfg.layout.2.2.2.2.1

  have hctrl :
      RegEncoding.bit cfg.ctrl b = RegEncoding.bit cfg.ctrl b' := by
    calc
      RegEncoding.bit cfg.ctrl b
          =
        RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b)) :=
        hctrl_b.symm
      _ =
        RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b')) := by
        exact congrArg (RegEncoding.bit cfg.ctrl) hEq
      _ = RegEncoding.bit cfg.ctrl b' := hctrl_b'

  have hdata :
      RegEncoding.toNat cfg.env.data b
        =
      RegEncoding.toNat cfg.env.data b' := by
    cases hbit : RegEncoding.bit cfg.ctrl b with
    | false =>
        have hbit' : RegEncoding.bit cfg.ctrl b' = false := by
          calc
            RegEncoding.bit cfg.ctrl b'
                = RegEncoding.bit cfg.ctrl b := hctrl.symm
            _ = false := hbit
        simpa [alg1OutputValue, hbit, hbit'] using hout
    | true =>
        have hbit' : RegEncoding.bit cfg.ctrl b' = true := by
          calc
            RegEncoding.bit cfg.ctrl b'
                = RegEncoding.bit cfg.ctrl b := hctrl.symm
            _ = true := hbit
        have hmod :
            Nat.ModEq cfg.env.N
              (cfg.c * RegEncoding.toNat cfg.env.data b)
              (cfg.c * RegEncoding.toNat cfg.env.data b') := by
          change
            (cfg.c * RegEncoding.toNat cfg.env.data b) % cfg.env.N
              =
            (cfg.c * RegEncoding.toNat cfg.env.data b') % cfg.env.N
          simpa [alg1OutputValue, hbit, hbit'] using hout
        have hcoprime :
            cfg.env.N.gcd cfg.c = 1 := by
          simpa [Nat.gcd_comm] using cfg.coprime.gcd_eq_one
        have hmod' :
            Nat.ModEq cfg.env.N
              (RegEncoding.toNat cfg.env.data b)
              (RegEncoding.toNat cfg.env.data b') :=
          Nat.ModEq.cancel_left_of_coprime hcoprime hmod
        exact hmod'.eq_of_lt_of_lt hb.1 hb'.1

  have hbb : b = b' := by
    have hpost :=
      congrArg
        (fun z : qs.Basis =>
          RegEncoding.writeNat
            (extendHi cfg.env.data)
            (RegEncoding.toNat cfg.env.data b)
            (RegEncoding.writeNat cfg.env.work 0 z))
        hEq

    calc
      b
          =
        RegEncoding.writeNat
          (extendHi cfg.env.data)
          (RegEncoding.toNat cfg.env.data b)
          (RegEncoding.writeNat
            cfg.env.work
            0
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work t.1 b))) := by
        symm
        exact alg1_reset_extendHi_work_write qs cfg b t.1
          (alg1OutputValue cfg b) hb
      _ =
        RegEncoding.writeNat
          (extendHi cfg.env.data)
          (RegEncoding.toNat cfg.env.data b)
          (RegEncoding.writeNat
            cfg.env.work
            0
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b')
              (RegEncoding.writeNat cfg.env.work u.1 b'))) :=
        hpost
      _ =
        RegEncoding.writeNat
          (extendHi cfg.env.data)
          (RegEncoding.toNat cfg.env.data b')
          (RegEncoding.writeNat
            cfg.env.work
            0
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b')
              (RegEncoding.writeNat cfg.env.work u.1 b'))) := by
        rw [hdata]
      _ = b' :=
        alg1_reset_extendHi_work_write qs cfg b' u.1
          (alg1OutputValue cfg b') hb'

  exact ⟨hbb, htu⟩


/--
The analogous injectivity for a work write. This is the `hwrite_inj` proof
already present inside `alg1_goodStep1_norm_le_one`, extracted as a reusable
lemma.
-/
lemma alg1_work_label_injective
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b b' : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (hb' :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b')
    (t u : Fin (ASize cfg.env.work))
    (hEq :
      RegEncoding.writeNat cfg.env.work t.1 b
        =
      RegEncoding.writeNat cfg.env.work u.1 b') :
    b = b' ∧ t = u := by
  have htu_val : t.1 = u.1 := by
    calc
      t.1
          =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work t.1 b) := by
            symm
            exact
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work t.1 b t.isLt
      _ =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work u.1 b') := by
            rw [hEq]
      _ = u.1 :=
        RegEncoding.toNat_writeNat_of_lt
          cfg.env.work u.1 b' u.isLt

  have htu : t = u :=
    Fin.ext htu_val

  have hbwork :
      RegEncoding.toNat cfg.env.work b = 0 :=
    hb.2.2.1

  have hb'work :
      RegEncoding.toNat cfg.env.work b' = 0 :=
    hb'.2.2.1

  have hbzero :
      RegEncoding.writeNat cfg.env.work 0 b = b := by
    simpa [hbwork] using
      (RegEncoding.writeNat_toNat cfg.env.work b)

  have hb'zero :
      RegEncoding.writeNat cfg.env.work 0 b' = b' := by
    simpa [hb'work] using
      (RegEncoding.writeNat_toNat cfg.env.work b')

  have hbb : b = b' := by
    calc
      b =
          RegEncoding.writeNat cfg.env.work 0 b := hbzero.symm
      _ =
          RegEncoding.writeNat cfg.env.work 0
            (RegEncoding.writeNat cfg.env.work t.1 b) := by
              symm
              exact
                writeNat_overwrite_same_reg
                  cfg.env.work 0 t.1 b
      _ =
          RegEncoding.writeNat cfg.env.work 0
            (RegEncoding.writeNat cfg.env.work u.1 b') := by
              rw [hEq]
      _ =
          RegEncoding.writeNat cfg.env.work 0 b' := by
              exact
                writeNat_overwrite_same_reg
                  cfg.env.work 0 u.1 b'
      _ = b' := hb'zero

  exact ⟨hbb, htu⟩


lemma alg1_afterStep34Bad_norm_sq_eq_trace_bad_mass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    ‖tr.afterStep34Bad‖ ^ 2 = alg1TraceBadMass qs cfg tr := by
  classical

  let Sbad : Finset (Σ b : qs.Basis, Fin (ASize cfg.env.work)) :=
    tr.support.sigma fun b =>
      Finset.univ.filter (fun t => t ∉ alg1GoodLabels cfg b)

  let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
    fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2

  let labelWork : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → qs.Basis :=
    fun i =>
      RegEncoding.writeNat cfg.env.work i.2.1 i.1

  let labelStep34 :
      (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → qs.Basis :=
    fun i =>
      RegEncoding.writeNat
        (extendHi cfg.env.data)
        (alg1OutputValue cfg i.1)
        (RegEncoding.writeNat cfg.env.work i.2.1 i.1)

  have hbadStep1_flat :
      tr.badStep1
        =
      ∑ i ∈ Sbad, α i • qs.ket (labelWork i) := by
    simp [
      Sbad, α, labelWork,
      Alg1Trace.badStep1,
      Finset.sum_sigma,
      Finset.smul_sum,
      smul_smul
    ]

  have hbadStep34_flat :
      tr.afterStep34Bad
        =
      ∑ i ∈ Sbad, α i • qs.ket (labelStep34 i) := by
    simp [
      Sbad, α, labelStep34,
      Alg1Trace.afterStep34Bad,
      Finset.sum_sigma,
      Finset.smul_sum,
      smul_smul
    ]

  have hwork_inj :
      ∀ i ∈ Sbad, ∀ j ∈ Sbad, i ≠ j →
        labelWork i ≠ labelWork j := by
    intro i hi j hj hij hEq
    rcases i with ⟨b, t⟩
    rcases j with ⟨b', u⟩
    rcases Finset.mem_sigma.mp hi with ⟨hbmem, _⟩
    rcases Finset.mem_sigma.mp hj with ⟨hbmem', _⟩

    rcases
      alg1_work_label_injective
        qs cfg
        b b'
        (tr.input_good b hbmem)
        (tr.input_good b' hbmem')
        t u
        (by simpa [labelWork] using hEq)
      with ⟨hbb, htu⟩

    apply hij
    cases hbb
    cases htu
    rfl

  have hstep34_inj :
      ∀ i ∈ Sbad, ∀ j ∈ Sbad, i ≠ j →
        labelStep34 i ≠ labelStep34 j := by
    intro i hi j hj hij hEq
    rcases i with ⟨b, t⟩
    rcases j with ⟨b', u⟩
    rcases Finset.mem_sigma.mp hi with ⟨hbmem, _⟩
    rcases Finset.mem_sigma.mp hj with ⟨hbmem', _⟩

    rcases
      alg1_step34_label_injective
        qs cfg
        b b'
        (tr.input_good b hbmem)
        (tr.input_good b' hbmem')
        t u
        (by simpa [labelStep34] using hEq)
      with ⟨hbb, htu⟩

    apply hij
    cases hbb
    cases htu
    rfl

  have hnorm :
      ‖∑ i ∈ Sbad, α i • qs.ket (labelStep34 i)‖
        =
      ‖∑ i ∈ Sbad, α i • qs.ket (labelWork i)‖ :=
    norm_sum_reindex_ket_eq
      qs Sbad α labelStep34 labelWork hstep34_inj hwork_inj

  calc
    ‖tr.afterStep34Bad‖ ^ 2
        =
      ‖∑ i ∈ Sbad, α i • qs.ket (labelStep34 i)‖ ^ 2 := by
        rw [hbadStep34_flat]
    _ =
      ‖∑ i ∈ Sbad, α i • qs.ket (labelWork i)‖ ^ 2 :=
        congrArg (fun r : ℝ => r ^ 2) hnorm
    _ =
      ‖tr.badStep1‖ ^ 2 := by
        rw [hbadStep1_flat]
    _ = alg1TraceBadMass qs cfg tr :=
      alg1_badStep1_norm_sq_eq_trace_bad_mass qs cfg ψ tr



/--
Subtract the exact full cleanup identity from the retained-good cleanup packet.

This is algebra only; no quantitative estimate is used here.
-/
lemma alg1_step5_cleanup_error_eq_neg_bad_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
        tr.afterStep34Ref
      -
      qs.eval (ModMulConfig.idealGate cfg) ψ
      =
    -qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
        tr.afterStep34Bad := by
  rw [← alg1_step5_full_packet_eq_ideal qs cfg ψ tr]
  rw [alg1_afterStep34Full_eq_good_add_bad qs cfg ψ tr, qs.eval_add]
  abel

lemma alg1_step5_cleanup_sq_eq_trace_bad_mass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    ‖qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
          tr.afterStep34Ref
        -
        qs.eval (ModMulConfig.idealGate cfg) ψ‖ ^ 2
      =
    alg1TraceBadMass qs cfg tr := by
  rw [
    alg1_step5_cleanup_error_eq_neg_bad_packet qs cfg ψ tr,
    norm_neg
  ]
  calc
    ‖qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
        tr.afterStep34Bad‖ ^ 2
      =
    ‖tr.afterStep34Bad‖ ^ 2 := by
      exact congrArg (fun r : ℝ => r ^ 2)
        (eval_norm_preserved
          (qs := qs)
          (ModMulConfig.U5 (Basis := qs.Basis) cfg)
          tr.afterStep34Bad)
    _ = alg1TraceBadMass qs cfg tr :=
      alg1_afterStep34Bad_norm_sq_eq_trace_bad_mass qs cfg ψ tr

/-! =========================================================
    Good Step-1 packet norm
========================================================= -/

lemma alg1_goodStep1_norm_le_one
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    cfg.ValidUnitState qs ψ →
      ‖tr.goodStep1‖ ≤ 1 := by
  classical
  intro hψ

  let Sfull : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) :=
    tr.support.sigma fun _ => Finset.univ
  let Sgood : Finset (Σ b : qs.Basis, Fin (ASize cfg.env.work)) :=
    tr.support.sigma fun b => alg1GoodLabels cfg b
  let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
    fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2
  let label : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → qs.Basis :=
    fun i => RegEncoding.writeNat cfg.env.work i.2.1 i.1

  have hSsub : Sgood ⊆ Sfull := by
    intro i hi
    rcases Finset.mem_sigma.mp hi with ⟨hb, ht⟩
    exact Finset.mem_sigma.mpr ⟨hb, by simp⟩

  have hwrite_inj :
      ∀ i ∈ Sfull, ∀ j ∈ Sfull, label i = label j → i = j := by
    intro i hi j hj hEq
    rcases Finset.mem_sigma.mp hi with ⟨hi_b, _⟩
    rcases Finset.mem_sigma.mp hj with ⟨hj_b, _⟩

    have hi_read :
        RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1)
          =
        i.2.1 :=
      RegEncoding.toNat_writeNat_of_lt
        cfg.env.work i.2.1 i.1 i.2.isLt

    have hj_read :
        RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat cfg.env.work j.2.1 j.1)
          =
        j.2.1 :=
      RegEncoding.toNat_writeNat_of_lt
        cfg.env.work j.2.1 j.1 j.2.isLt

    have ht_val : i.2.1 = j.2.1 := by
      calc
        i.2.1
            =
          RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1) := hi_read.symm
        _ =
          RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat cfg.env.work j.2.1 j.1) := by
            simpa [label] using congrArg (RegEncoding.toNat cfg.env.work) hEq
        _ = j.2.1 := hj_read

    have ht : i.2 = j.2 := Fin.ext ht_val

    have hi_work :
        RegEncoding.toNat cfg.env.work i.1 = 0 :=
      (tr.input_good i.1 hi_b).2.2.1

    have hj_work :
        RegEncoding.toNat cfg.env.work j.1 = 0 :=
      (tr.input_good j.1 hj_b).2.2.1

    have hi_zero :
        RegEncoding.writeNat cfg.env.work 0 i.1 = i.1 := by
      simpa [hi_work] using
        RegEncoding.writeNat_toNat cfg.env.work i.1

    have hj_zero :
        RegEncoding.writeNat cfg.env.work 0 j.1 = j.1 := by
      simpa [hj_work] using
        RegEncoding.writeNat_toNat cfg.env.work j.1

    have hb : i.1 = j.1 := by
      calc
        i.1 = RegEncoding.writeNat cfg.env.work 0 i.1 := hi_zero.symm
        _ =
          RegEncoding.writeNat cfg.env.work 0
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1) := by
            symm
            exact writeNat_overwrite_same_reg cfg.env.work 0 i.2.1 i.1
        _ =
          RegEncoding.writeNat cfg.env.work 0
            (RegEncoding.writeNat cfg.env.work j.2.1 j.1) := by
            exact congrArg (RegEncoding.writeNat cfg.env.work 0) hEq
        _ =
          RegEncoding.writeNat cfg.env.work 0 j.1 := by
            exact writeNat_overwrite_same_reg cfg.env.work 0 j.2.1 j.1
        _ = j.1 := hj_zero

    cases i
    cases j
    simp at hb ht ⊢
    exact ⟨hb, ht⟩

  have horth_full :
      ∀ i ∈ Sfull, ∀ j ∈ Sfull, i ≠ j →
        inner ℂ (α i • qs.ket (label i)) (α j • qs.ket (label j)) = 0 := by
    intro i hi j hj hij
    have hlabel_ne : label i ≠ label j := by
      intro hlabel
      exact hij (hwrite_inj i hi j hj hlabel)
    rw [inner_smul_left, inner_smul_right,
      qs.ket_inner_eq_zero_of_ne hlabel_ne]
    simp

  have horth_good :
      ∀ i ∈ Sgood, ∀ j ∈ Sgood, i ≠ j →
        inner ℂ (α i • qs.ket (label i)) (α j • qs.ket (label j)) = 0 := by
    intro i hi j hj hij
    exact horth_full i (hSsub hi) j (hSsub hj) hij

  have hfull_flat :
      qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
        =
      ∑ i ∈ Sfull, α i • qs.ket (label i) := by
    simp [Sfull, α, label, ModMulConfig.U1, Finset.sum_sigma] at *
    simpa [ModMulConfig.U1, Finset.smul_sum, smul_smul] using tr.full_step1_eq

  have hgood_flat :
      tr.goodStep1 =
      ∑ i ∈ Sgood, α i • qs.ket (label i) := by
    simp [Sgood, α, label, Alg1Trace.goodStep1, Finset.sum_sigma,
      Finset.smul_sum, smul_smul]

  have hfull_norm :
      ‖qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ‖ = 1 := by
    calc
      ‖qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ‖
          =
        ‖ψ‖ := by
          simpa using
            eval_norm_preserved
              qs
              (ModMulConfig.U1 (Basis := qs.Basis) cfg)
              ψ
      _ = 1 := hψ.2

  have hsq_full :
      ‖∑ i ∈ Sfull, α i • qs.ket (label i)‖ ^ 2
        =
      ∑ i ∈ Sfull, ‖α i • qs.ket (label i)‖ ^ 2 :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
      (qs := qs) Sfull (fun i => α i • qs.ket (label i)) horth_full

  have hsq_good :
      ‖∑ i ∈ Sgood, α i • qs.ket (label i)‖ ^ 2
        =
      ∑ i ∈ Sgood, ‖α i • qs.ket (label i)‖ ^ 2 :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
      (qs := qs) Sgood (fun i => α i • qs.ket (label i)) horth_good

  have hsum_le :
      (∑ i ∈ Sgood, ‖α i • qs.ket (label i)‖ ^ 2)
        ≤
      ∑ i ∈ Sfull, ‖α i • qs.ket (label i)‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      hSsub
      (by
        intro i hi_full hi_not_good
        exact sq_nonneg _)

  have hsq_le_one :
      ‖tr.goodStep1‖ ^ 2 ≤ 1 := by
    calc
      ‖tr.goodStep1‖ ^ 2
          =
        ‖∑ i ∈ Sgood, α i • qs.ket (label i)‖ ^ 2 := by
          rw [hgood_flat]
      _ =
        ∑ i ∈ Sgood, ‖α i • qs.ket (label i)‖ ^ 2 := hsq_good
      _ ≤
        ∑ i ∈ Sfull, ‖α i • qs.ket (label i)‖ ^ 2 := hsum_le
      _ =
        ‖∑ i ∈ Sfull, α i • qs.ket (label i)‖ ^ 2 := hsq_full.symm
      _ =
        ‖qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ‖ ^ 2 := by
          rw [hfull_flat]
      _ = 1 := by
          rw [hfull_norm]
          norm_num

  have hnonneg : 0 ≤ ‖tr.goodStep1‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖tr.goodStep1‖ - 1)]

/-! =========================================================
    Uniform Step-1 and Step-5 tail theorem
========================================================= -/

/--
Uniform QPE-tail theorem used by both the Step-1 and Step-5 bounds.

-/
lemma alg1_qpe_tail_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs] :
    ∃ Cpe : ℝ, 0 ≤ Cpe ∧
      (∀ (η : ℝ) (cfg : ModMulConfig η)
          (b : qs.Basis),
          GoodModMulBasisInput
            qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b →
          ∑ t ∈ Finset.univ.filter
            (fun t => t ∉ alg1GoodLabels cfg b),
            ‖alg1PhaseCoeff qs cfg b t‖ ^ 2
            ≤ Cpe * η) ∧
      (∀ (η : ℝ) (cfg : ModMulConfig η)
          (ψ : qs.State) (tr : Alg1Trace qs cfg ψ),
          cfg.ValidUnitState qs ψ →
          ‖qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
              - tr.goodStep1‖ ^ 2
            ≤ Cpe * η) ∧
      (∀ (η : ℝ) (cfg : ModMulConfig η)
          (ψ : qs.State) (tr : Alg1Trace qs cfg ψ),
          cfg.ValidUnitState qs ψ →
          ‖qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
              tr.afterStep34Ref
            - qs.eval (ModMulConfig.idealGate cfg) ψ‖ ^ 2
            ≤ Cpe * η) := by
  rcases alg1_qpe_tail_basis_uniform qs with
    ⟨Cpe, hCpe_nonneg, hTail⟩

  refine ⟨Cpe, hCpe_nonneg, ?_, ?_, ?_⟩

  · intro η cfg b hb
    simpa [alg1QpeBadMass] using hTail η cfg b hb

  · intro η cfg ψ tr hunit
    rw [alg1_step1_error_sq_eq_trace_bad_mass qs cfg ψ tr]
    exact
      alg1_trace_bad_mass_le_of_basis_tail
        qs
        hTail
        cfg ψ tr hunit

  · intro η cfg ψ tr hunit
    rw [alg1_step5_cleanup_sq_eq_trace_bad_mass qs cfg ψ tr]
    exact
      alg1_trace_bad_mass_le_of_basis_tail
        qs
        hTail
        cfg ψ tr hunit
