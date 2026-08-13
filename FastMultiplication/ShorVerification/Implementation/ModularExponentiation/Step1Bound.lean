import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Step1QPE
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs

/-!
# Step-1 Main Bound

This file assembles the main Step-1 and Step-5 error argument for approximate
controlled modular multiplication. The analytic QPE kernel estimates and the
basis-input tail bound are proved in `Step1QPE.lean`; this file lifts those
results from individual basis states to arbitrary valid unit states.

The proof is organized as follows:

* establish the register-layout facts used throughout the reconstruction;
* reconstruct the Step-5 QPE packet at the ideal modular-multiplication output;
* split the post-Step-3/4 state into its retained-good and discarded-bad parts;
* prove that Step 3/4 preserves the norm of the bad packet;
* identify both the Step-1 and Step-5 errors with the same QPE bad mass; and
* package the basis, Step-1, and Step-5 estimates into one uniform theorem.
-/

open Shor

/-! ## Register-Layout Facts -/

/--
The active work register is disjoint from the active data register after the
data register grows by one carry qubit.
-/
private lemma step1Bound_work_dataCarry_active_disjoint
    {η : ℝ}
    (cfg : ModMulConfig η) :
    Shor.Disjoint
      cfg.env.work.active
      (cfg.env.data.grow 1).active := by
  rw [Shor.Disjoint, List.disjoint_left]
  intro q hqWork hqData

  have h := cfg.env.circuit_workspace.work_dataCarry_disjoint
  rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h

  exact h
    (List.mem_append_left _ hqWork)
    (List.mem_append_left _ hqData)

/-- The control qubit lies outside the active work register. -/
private lemma step1Bound_ctrl_notin_work_active
    {η : ℝ}
    (cfg : ModMulConfig η) :
    cfg.ctrl ∉ cfg.env.work.active.qubits := by
  intro hq
  exact cfg.layout.2.2.2.2.1
    (List.mem_append_left _ hq)

/-- The control qubit lies outside the grown data-and-carry register. -/
private lemma step1Bound_ctrl_notin_dataCarry_active
    {η : ℝ}
    (cfg : ModMulConfig η) :
    cfg.ctrl ∉ (cfg.env.data.grow 1).active.qubits := by
  intro hq
  apply cfg.layout.2.2.2.1

  have howned :
      cfg.ctrl ∈ (cfg.env.data.grow 1).ownedQubits :=
    List.mem_append_left _ hq

  simpa [Gate.ExtReg.ownedQubits_grow] using howned

/--
Growing the data register by its carry qubit cannot decrease the number of
encodable natural-number values.
-/
private lemma step1Bound_data_ASize_le_dataCarry
    {η : ℝ}
    (cfg : ModMulConfig η) :
    ASize cfg.env.data.active
      ≤
    ASize (cfg.env.data.grow 1).active := by
  have hwidth :
      regSize (cfg.env.data.grow 1).active
        =
      regSize cfg.env.data.active + 1 := by
    simpa [ExtReg.width] using
      ExtReg.width_grow
        cfg.env.data
        1
        cfg.env.circuit_workspace.data_canGrow_one

  unfold ASize
  rw [hwidth, pow_succ]
  omega

/-! ## Step-5 Packet Reconstruction -/

/-! ### Forward packet on the extended ideal output -/

/--
Forward Step-5 fractional-load evaluation from the extended ideal-output
basis state.
-/
lemma alg1_step5_forward_packet_on_extended_output
    (qs : QSemantics)
    [RegEncoding qs.Basis]
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
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b)
            b))
      =
    ∑ t : Fin (ASize cfg.env.work.active),
      alg1FractionalLoadCoeff cfg b t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work.active t.1
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              b)) := by
  rw [alg1Step5Forward, qs.eval_seq, qs.eval_seq]
  have hpre := alg1_step5_forward_preIQFT_packet qs cfg b hb
  rw [qs.eval_seq] at hpre
  change
    qs.eval (IQFT cfg.env.work)
      (qs.eval
        (Gate.CPhaseProdUsing
          cfg.ctrl
          (alg1Step5Phase cfg)
          (cfg.env.data.grow 1).active
          cfg.env.work.active
          cfg.env.circuit_workspace.step5Workspace)
        (qs.eval (H_reg cfg.env.work.active)
          (qs.ket
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              b))))
      =
    ∑ t : Fin (ASize cfg.env.work.active),
      alg1FractionalLoadCoeff cfg b t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work.active t.1
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              b))
  rw [hpre]
  simpa [alg1FractionalLoadCoeff] using
    (eval_IQFT_work_packet
      qs
      cfg.env.work
      (RegEncoding.writeNat
        (cfg.env.data.grow 1).active
        (alg1OutputValue cfg b)
        b)
      (alg1LoadPreCoeff cfg b))

/-! ### Basis packets and exact cleanup -/

/--
The forward circuit associated with Step 5 reproduces the complete Step-1 QPE
packet, now based at the ideal modular-multiplication output. The proof combines
the extended-output packet formula with coefficient equality and commutation of
the disjoint work and data writes.
-/
lemma alg1_step5_forward_packet_on_basis
    (qs : QSemantics)
    [RegEncoding qs.Basis]
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
        ((H_reg cfg.env.work.active) ;;
          (Gate.CPhaseProdUsing
            cfg.ctrl
            (alg1Step5Phase cfg)
            (cfg.env.data.grow 1).active
            cfg.env.work.active
            cfg.env.circuit_workspace.step5Workspace) ;;
          (IQFT cfg.env.work))
        (qs.eval (ModMulConfig.idealGate cfg) (qs.ket b))
      =
    ∑ t : Fin (ASize cfg.env.work.active),
      alg1PhaseCoeff qs cfg b t •
        qs.ket
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work.active t.1 b)) := by
  classical

  have hideal :
      qs.eval (ModMulConfig.idealGate cfg) (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat
          (cfg.env.data.grow 1).active
          (alg1OutputValue cfg b)
          b) :=
    alg1_ideal_ket_eq_extended_output qs cfg b hb

  have hwork_ext :
      Shor.Disjoint
        cfg.env.work.active
        (cfg.env.data.grow 1).active :=
    step1Bound_work_dataCarry_active_disjoint cfg

  rw [hideal]
  change
    qs.eval
        (alg1Step5Forward (Basis := qs.Basis) cfg)
        (qs.ket
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
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
        cfg.env.work.active
        (cfg.env.data.grow 1).active
        hwork_ext
        t.1
        (alg1OutputValue cfg b)
        b)

/--
Applying the adjoint Step-5 circuit to the full QPE packet for one good basis
input exactly recovers the corresponding ideal modular-multiplication output.
-/
lemma alg1_step5_full_packet_on_basis
    (qs : QSemantics)
    [RegEncoding qs.Basis]
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
      (∑ t : Fin (ASize cfg.env.work.active),
        alg1PhaseCoeff qs cfg b t •
          qs.ket
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b)))
      =
    qs.eval (ModMulConfig.idealGate cfg) (qs.ket b) := by
  rw [← alg1_step5_forward_packet_on_basis qs cfg b hb]
  simpa [ModMulConfig.U5, step5, alg1Step5Forward, alg1Step5Phase] using
    qs.eval_adj_apply
      (alg1Step5Forward (Basis := qs.Basis) cfg)
      (qs.eval (ModMulConfig.idealGate cfg) (qs.ket b))

/--
By linearity, exact Step-5 cleanup of the full packet holds for every trace:
the result is the ideal modular-multiplication circuit applied to the original
input state.
-/
lemma alg1_step5_full_packet_eq_ideal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
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
            ∑ t : Fin (ASize cfg.env.work.active),
              alg1PhaseCoeff qs cfg b t •
                qs.ket
                  (RegEncoding.writeNat
                    (cfg.env.data.grow 1).active
                    (alg1OutputValue cfg b)
                    (RegEncoding.writeNat cfg.env.work.active t.1 b)))
      =
    ∑ b ∈ tr.support,
      tr.inputCoeff b •
        qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
          (∑ t : Fin (ASize cfg.env.work.active),
            alg1PhaseCoeff qs cfg b t •
              qs.ket
                (RegEncoding.writeNat
                  (cfg.env.data.grow 1).active
                  (alg1OutputValue cfg b)
                  (RegEncoding.writeNat cfg.env.work.active t.1 b))) := by
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

/-! ## Good/Bad Packet Decomposition -/

/--
The full post-Step-3/4 packet is the sum of the packet over good QPE labels and
the complementary packet over bad labels.
-/
lemma alg1_afterStep34Full_eq_good_add_bad
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
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

  -- Split each basis-input packet by membership in `alg1GoodLabels`.
  have hsplit :
      ∀ b : qs.Basis,
        (∑ t : Fin (ASize cfg.env.work.active),
          tr.phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat
                (cfg.env.data.grow 1).active
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work.active t.1 b)))
          =
        (∑ t ∈ alg1GoodLabels cfg b,
          tr.phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat
                (cfg.env.data.grow 1).active
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work.active t.1 b)))
          +
        ∑ t ∈ Finset.univ.filter
            (fun t => t ∉ alg1GoodLabels cfg b),
          tr.phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat
                (cfg.env.data.grow 1).active
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work.active t.1 b)) := by
    intro b

    let p : Fin (ASize cfg.env.work.active) → Prop :=
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
                (cfg.env.data.grow 1).active
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work.active t.1 b)))

    rw [hgood] at h
    exact h.symm

  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [hsplit b, smul_add]

/-! ## Label Injectivity and Bad-Mass Preservation -/

/--
The basis label produced after Steps 3 and 4 uniquely determines both the
original good basis input and its QPE work label. This prevents distinct packet
terms from colliding when their norms are compared.
-/
lemma alg1_step34_label_injective
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
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
    (t u : Fin (ASize cfg.env.work.active))
    (hEq :
      RegEncoding.writeNat
          (cfg.env.data.grow 1).active
          (alg1OutputValue cfg b)
          (RegEncoding.writeNat cfg.env.work.active t.1 b)
        =
      RegEncoding.writeNat
          (cfg.env.data.grow 1).active
          (alg1OutputValue cfg b')
          (RegEncoding.writeNat cfg.env.work.active u.1 b')) :
    b = b' ∧ t = u := by
  classical

  -- Read the independently encoded data output and work label from `hEq`.
  have hdisj :
      Shor.Disjoint
        cfg.env.work.active
        (cfg.env.data.grow 1).active :=
    step1Bound_work_dataCarry_active_disjoint cfg

  have hout_cap :
      alg1OutputValue cfg b
        <
      ASize (cfg.env.data.grow 1).active := by
    exact lt_of_lt_of_le
      (alg1OutputValue_lt_data_capacity cfg b hb)
      (step1Bound_data_ASize_le_dataCarry cfg)

  have hout_cap' :
      alg1OutputValue cfg b'
        <
      ASize (cfg.env.data.grow 1).active := by
    exact lt_of_lt_of_le
      (alg1OutputValue_lt_data_capacity cfg b' hb')
      (step1Bound_data_ASize_le_dataCarry cfg)

  have hout :
      alg1OutputValue cfg b = alg1OutputValue cfg b' := by
    calc
      alg1OutputValue cfg b
          =
        RegEncoding.toNat (cfg.env.data.grow 1).active
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work.active t.1 b)) := by
          symm
          exact
            RegEncoding.toNat_writeNat_of_lt
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b)
              hout_cap
      _ =
        RegEncoding.toNat (cfg.env.data.grow 1).active
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work.active u.1 b')) := by
          exact congrArg
            (RegEncoding.toNat (cfg.env.data.grow 1).active)
            hEq
      _ =
        alg1OutputValue cfg b' :=
          RegEncoding.toNat_writeNat_of_lt
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work.active u.1 b')
            hout_cap'

  have htu_val : t.1 = u.1 := by
    calc
      t.1
          =
        RegEncoding.toNat cfg.env.work.active
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work.active t.1 b)) := by
          symm
          calc
            RegEncoding.toNat cfg.env.work.active
              (RegEncoding.writeNat
                (cfg.env.data.grow 1).active
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work.active t.1 b))
                =
              RegEncoding.toNat cfg.env.work.active
                (RegEncoding.writeNat cfg.env.work.active t.1 b) :=
              RegEncoding.toNat_left_write_right
                cfg.env.work.active
                (cfg.env.data.grow 1).active
                hdisj
                (RegEncoding.writeNat cfg.env.work.active t.1 b)
                (alg1OutputValue cfg b)
            _ = t.1 :=
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work.active t.1 b t.isLt
      _ =
        RegEncoding.toNat cfg.env.work.active
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work.active u.1 b')) := by
          exact congrArg
            (RegEncoding.toNat cfg.env.work.active)
            hEq
      _ = u.1 := by
          calc
            RegEncoding.toNat cfg.env.work.active
              (RegEncoding.writeNat
                (cfg.env.data.grow 1).active
                (alg1OutputValue cfg b')
                (RegEncoding.writeNat cfg.env.work.active u.1 b'))
                =
              RegEncoding.toNat cfg.env.work.active
                (RegEncoding.writeNat cfg.env.work.active u.1 b') :=
              RegEncoding.toNat_left_write_right
                cfg.env.work.active
                (cfg.env.data.grow 1).active
                hdisj
                (RegEncoding.writeNat cfg.env.work.active u.1 b')
                (alg1OutputValue cfg b')
            _ = u.1 :=
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work.active u.1 b' u.isLt

  have htu : t = u := Fin.ext htu_val

  -- Writes to the work and grown-data registers preserve the control bit.
  have hctrl_b :
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work.active t.1 b))
        =
      RegEncoding.bit cfg.ctrl b := by
    calc
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work.active t.1 b))
          =
        RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat cfg.env.work.active t.1 b) :=
        RegEncoding.bit_writeNat_out
          (r := (cfg.env.data.grow 1).active)
          (v := alg1OutputValue cfg b)
          (b := RegEncoding.writeNat cfg.env.work.active t.1 b)
          (q := cfg.ctrl)
          (step1Bound_ctrl_notin_dataCarry_active cfg)
      _ = RegEncoding.bit cfg.ctrl b :=
        RegEncoding.bit_writeNat_out
          (r := cfg.env.work.active)
          (v := t.1)
          (b := b)
          (q := cfg.ctrl)
          (step1Bound_ctrl_notin_work_active cfg)

  have hctrl_b' :
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work.active u.1 b'))
        =
      RegEncoding.bit cfg.ctrl b' := by
    calc
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work.active u.1 b'))
          =
        RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat cfg.env.work.active u.1 b') :=
        RegEncoding.bit_writeNat_out
          (r := (cfg.env.data.grow 1).active)
          (v := alg1OutputValue cfg b')
          (b := RegEncoding.writeNat cfg.env.work.active u.1 b')
          (q := cfg.ctrl)
          (step1Bound_ctrl_notin_dataCarry_active cfg)
      _ = RegEncoding.bit cfg.ctrl b' :=
        RegEncoding.bit_writeNat_out
          (r := cfg.env.work.active)
          (v := u.1)
          (b := b')
          (q := cfg.ctrl)
          (step1Bound_ctrl_notin_work_active cfg)

  have hctrl :
      RegEncoding.bit cfg.ctrl b =
        RegEncoding.bit cfg.ctrl b' := by
    calc
      RegEncoding.bit cfg.ctrl b
          =
        RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b)
            (RegEncoding.writeNat cfg.env.work.active t.1 b)) :=
        hctrl_b.symm
      _ =
        RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (alg1OutputValue cfg b')
            (RegEncoding.writeNat cfg.env.work.active u.1 b')) := by
        exact congrArg (RegEncoding.bit cfg.ctrl) hEq
      _ = RegEncoding.bit cfg.ctrl b' := hctrl_b'

  -- Recover the original data value, cancelling multiplication by `cfg.c`
  -- modulo `cfg.env.N` in the controlled branch.
  have hdata :
      RegEncoding.toNat cfg.env.data.active b
        =
      RegEncoding.toNat cfg.env.data.active b' := by
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
              (cfg.c * RegEncoding.toNat cfg.env.data.active b)
              (cfg.c * RegEncoding.toNat cfg.env.data.active b') := by
          change
            (cfg.c * RegEncoding.toNat cfg.env.data.active b) % cfg.env.N
              =
            (cfg.c * RegEncoding.toNat cfg.env.data.active b') % cfg.env.N
          simpa [alg1OutputValue, hbit, hbit'] using hout
        have hcoprime :
            cfg.env.N.gcd cfg.c = 1 := by
          simpa [Nat.gcd_comm] using cfg.coprime.gcd_eq_one
        have hmod' :
            Nat.ModEq cfg.env.N
              (RegEncoding.toNat cfg.env.data.active b)
              (RegEncoding.toNat cfg.env.data.active b') :=
          Nat.ModEq.cancel_left_of_coprime hcoprime hmod
        exact hmod'.eq_of_lt_of_lt hb.1 hb'.1

  -- Resetting the temporary writes reconstructs the complete input basis state.
  have hbb : b = b' := by
    have hpost :=
      congrArg
        (fun z : qs.Basis =>
          RegEncoding.writeNat
            (cfg.env.data.grow 1).active
            (RegEncoding.toNat cfg.env.data.active b)
            (RegEncoding.writeNat cfg.env.work.active 0 z))
        hEq

    calc
      b
          =
        RegEncoding.writeNat
          (cfg.env.data.grow 1).active
          (RegEncoding.toNat cfg.env.data.active b)
          (RegEncoding.writeNat
            cfg.env.work.active
            0
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b))) := by
        symm
        exact alg1_reset_extendHi_work_write qs cfg b t.1
          (alg1OutputValue cfg b) hb
      _ =
        RegEncoding.writeNat
          (cfg.env.data.grow 1).active
          (RegEncoding.toNat cfg.env.data.active b)
          (RegEncoding.writeNat
            cfg.env.work.active
            0
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b')
              (RegEncoding.writeNat cfg.env.work.active u.1 b'))) :=
        hpost
      _ =
        RegEncoding.writeNat
          (cfg.env.data.grow 1).active
          (RegEncoding.toNat cfg.env.data.active b')
          (RegEncoding.writeNat
            cfg.env.work.active
            0
            (RegEncoding.writeNat
              (cfg.env.data.grow 1).active
              (alg1OutputValue cfg b')
              (RegEncoding.writeNat cfg.env.work.active u.1 b'))) := by
        rw [hdata]
      _ = b' :=
        alg1_reset_extendHi_work_write qs cfg b' u.1
          (alg1OutputValue cfg b') hb'

  exact ⟨hbb, htu⟩

/--
A work-register write uniquely determines both a good input basis state and
the written work label. The zero-workspace condition lets the proof recover the
original basis state by overwriting the work register with zero.
-/
lemma alg1_work_label_injective
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b b' : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (hb' :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b')
    (t u : Fin (ASize cfg.env.work.active))
    (hEq :
      RegEncoding.writeNat cfg.env.work.active t.1 b
        =
      RegEncoding.writeNat cfg.env.work.active u.1 b') :
    b = b' ∧ t = u := by
  have htu_val : t.1 = u.1 := by
    calc
      t.1
          =
        RegEncoding.toNat cfg.env.work.active
          (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
            symm
            exact
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work.active t.1 b t.isLt
      _ =
        RegEncoding.toNat cfg.env.work.active
          (RegEncoding.writeNat cfg.env.work.active u.1 b') := by
            rw [hEq]
      _ = u.1 :=
        RegEncoding.toNat_writeNat_of_lt
          cfg.env.work.active u.1 b' u.isLt

  have htu : t = u :=
    Fin.ext htu_val

  have hbwork :
      RegEncoding.toNat cfg.env.work.active b = 0 :=
    hb.2.2.1

  have hb'work :
      RegEncoding.toNat cfg.env.work.active b' = 0 :=
    hb'.2.2.1

  have hbzero :
      RegEncoding.writeNat cfg.env.work.active 0 b = b := by
    simpa [hbwork] using
      (RegEncoding.writeNat_toNat cfg.env.work.active b)

  have hb'zero :
      RegEncoding.writeNat cfg.env.work.active 0 b' = b' := by
    simpa [hb'work] using
      (RegEncoding.writeNat_toNat cfg.env.work.active b')

  have hbb : b = b' := by
    calc
      b =
          RegEncoding.writeNat cfg.env.work.active 0 b := hbzero.symm
      _ =
          RegEncoding.writeNat cfg.env.work.active 0
            (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
              symm
              exact
                writeNat_overwrite_same_reg
                  cfg.env.work.active 0 t.1 b
      _ =
          RegEncoding.writeNat cfg.env.work.active 0
            (RegEncoding.writeNat cfg.env.work.active u.1 b') := by
              rw [hEq]
      _ =
          RegEncoding.writeNat cfg.env.work.active 0 b' := by
              exact
                writeNat_overwrite_same_reg
                  cfg.env.work.active 0 u.1 b'
      _ = b' := hb'zero

  exact ⟨hbb, htu⟩

/--
Steps 3 and 4 preserve the squared norm of the bad Step-1 packet. Both packets
use the same amplitudes; injectivity of their respective basis labels allows a
norm-preserving reindexing, so their squared norm is exactly the trace bad mass.
-/
lemma alg1_afterStep34Bad_norm_sq_eq_trace_bad_mass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    ‖tr.afterStep34Bad‖ ^ 2 =
      alg1TraceBadMass qs cfg tr := by
  classical

  -- Flatten the nested basis/work sums to one finite sigma-type index set.
  let Sbad : Finset
      (Σ b : qs.Basis, Fin (ASize cfg.env.work.active)) :=
    tr.support.sigma fun b =>
      Finset.univ.filter (fun t => t ∉ alg1GoodLabels cfg b)

  -- The coefficient is unchanged by Steps 3 and 4.
  let α :
      (Σ _b : qs.Basis, Fin (ASize cfg.env.work.active)) → ℂ :=
    fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2

  -- These maps name the computational-basis labels before and after Steps 3/4.
  let labelWork :
      (Σ _b : qs.Basis, Fin (ASize cfg.env.work.active)) →
        qs.Basis :=
    fun i =>
      RegEncoding.writeNat cfg.env.work.active i.2.1 i.1

  let labelStep34 :
      (Σ _b : qs.Basis, Fin (ASize cfg.env.work.active)) →
        qs.Basis :=
    fun i =>
      RegEncoding.writeNat
        (cfg.env.data.grow 1).active
        (alg1OutputValue cfg i.1)
        (RegEncoding.writeNat cfg.env.work.active i.2.1 i.1)

  have hbadStep1_flat :
      tr.badStep1
        =
      ∑ i ∈ Sbad, α i • qs.ket (labelWork i) := by
    simp [
      Sbad,
      α,
      labelWork,
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
      Sbad,
      α,
      labelStep34,
      Alg1Trace.afterStep34Bad,
      Finset.sum_sigma,
      Finset.smul_sum,
      smul_smul
    ]

  -- Each flattened family has pairwise-distinct basis labels.
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

  -- Reindexing between the two injectively labelled ket families preserves norm.
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

/-! ## Step-5 Cleanup Error -/

/--
Subtract the exact full cleanup identity from the retained-good cleanup packet.

This is algebra only; no quantitative estimate is used here.
-/
lemma alg1_step5_cleanup_error_eq_neg_bad_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
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
  rw [
    alg1_afterStep34Full_eq_good_add_bad qs cfg ψ tr,
    qs.eval_add
  ]
  abel

/--
The squared Step-5 cleanup error is exactly the trace bad mass. This follows
from the algebraic error identity, unitarity of Step 5, and preservation of the
bad packet norm through Steps 3 and 4.
-/
lemma alg1_step5_cleanup_sq_eq_trace_bad_mass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
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
      exact congrArg
        (fun r : ℝ => r ^ 2)
        (eval_norm_preserved
          (qs := qs)
          (ModMulConfig.U5 (Basis := qs.Basis) cfg)
          tr.afterStep34Bad)
    _ = alg1TraceBadMass qs cfg tr :=
      alg1_afterStep34Bad_norm_sq_eq_trace_bad_mass qs cfg ψ tr

/-! ## Norm of the Good Step-1 Packet -/

/--
For a valid unit input state, the retained-good portion of the Step-1 packet
has norm at most one. It is a sub-sum of the orthogonal full Step-1 expansion,
whose norm is one by unitarity.
-/
lemma alg1_goodStep1_norm_le_one
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    cfg.ValidUnitState qs ψ →
      ‖tr.goodStep1‖ ≤ 1 := by
  classical
  intro hψ

  -- `Sgood` is the good-label subset of the complete basis/work index set.
  let Sfull :
      Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work.active)) :=
    tr.support.sigma fun _ => Finset.univ

  let Sgood :
      Finset (Σ b : qs.Basis, Fin (ASize cfg.env.work.active)) :=
    tr.support.sigma fun b => alg1GoodLabels cfg b

  -- Each flattened packet term is represented by its amplitude and basis label.
  let α :
      (Σ _b : qs.Basis, Fin (ASize cfg.env.work.active)) → ℂ :=
    fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2

  let label :
      (Σ _b : qs.Basis, Fin (ASize cfg.env.work.active)) →
        qs.Basis :=
    fun i =>
      RegEncoding.writeNat cfg.env.work.active i.2.1 i.1

  have hSsub : Sgood ⊆ Sfull := by
    intro i hi
    rcases Finset.mem_sigma.mp hi with ⟨hb, ht⟩
    exact Finset.mem_sigma.mpr ⟨hb, by simp⟩

  -- Good inputs have a zero work register, so their written labels are unique.
  have hwrite_inj :
      ∀ i ∈ Sfull, ∀ j ∈ Sfull,
        label i = label j → i = j := by
    intro i hi j hj hEq
    rcases Finset.mem_sigma.mp hi with ⟨hi_b, _⟩
    rcases Finset.mem_sigma.mp hj with ⟨hj_b, _⟩

    have hi_read :
        RegEncoding.toNat cfg.env.work.active
            (RegEncoding.writeNat
              cfg.env.work.active
              i.2.1
              i.1)
          =
        i.2.1 :=
      RegEncoding.toNat_writeNat_of_lt
        cfg.env.work.active i.2.1 i.1 i.2.isLt

    have hj_read :
        RegEncoding.toNat cfg.env.work.active
            (RegEncoding.writeNat
              cfg.env.work.active
              j.2.1
              j.1)
          =
        j.2.1 :=
      RegEncoding.toNat_writeNat_of_lt
        cfg.env.work.active j.2.1 j.1 j.2.isLt

    have ht_val : i.2.1 = j.2.1 := by
      calc
        i.2.1
            =
          RegEncoding.toNat cfg.env.work.active
            (RegEncoding.writeNat
              cfg.env.work.active
              i.2.1
              i.1) :=
          hi_read.symm
        _ =
          RegEncoding.toNat cfg.env.work.active
            (RegEncoding.writeNat
              cfg.env.work.active
              j.2.1
              j.1) := by
          simpa [label] using
            congrArg
              (RegEncoding.toNat cfg.env.work.active)
              hEq
        _ = j.2.1 := hj_read

    have ht : i.2 = j.2 :=
      Fin.ext ht_val

    have hi_work :
        RegEncoding.toNat cfg.env.work.active i.1 = 0 :=
      (tr.input_good i.1 hi_b).2.2.1

    have hj_work :
        RegEncoding.toNat cfg.env.work.active j.1 = 0 :=
      (tr.input_good j.1 hj_b).2.2.1

    have hi_zero :
        RegEncoding.writeNat cfg.env.work.active 0 i.1 =
          i.1 := by
      simpa [hi_work] using
        RegEncoding.writeNat_toNat cfg.env.work.active i.1

    have hj_zero :
        RegEncoding.writeNat cfg.env.work.active 0 j.1 =
          j.1 := by
      simpa [hj_work] using
        RegEncoding.writeNat_toNat cfg.env.work.active j.1

    have hb : i.1 = j.1 := by
      calc
        i.1 =
          RegEncoding.writeNat cfg.env.work.active 0 i.1 :=
          hi_zero.symm
        _ =
          RegEncoding.writeNat cfg.env.work.active 0
            (RegEncoding.writeNat
              cfg.env.work.active
              i.2.1
              i.1) := by
            symm
            exact
              writeNat_overwrite_same_reg
                cfg.env.work.active 0 i.2.1 i.1
        _ =
          RegEncoding.writeNat cfg.env.work.active 0
            (RegEncoding.writeNat
              cfg.env.work.active
              j.2.1
              j.1) := by
            exact congrArg
              (RegEncoding.writeNat cfg.env.work.active 0)
              hEq
        _ =
          RegEncoding.writeNat cfg.env.work.active 0 j.1 := by
            exact
              writeNat_overwrite_same_reg
                cfg.env.work.active 0 j.2.1 j.1
        _ = j.1 := hj_zero

    cases i
    cases j
    simp at hb ht ⊢
    exact ⟨hb, ht⟩

  -- Distinct indices therefore give orthogonal computational-basis summands.
  have horth_full :
      ∀ i ∈ Sfull, ∀ j ∈ Sfull, i ≠ j →
        inner ℂ
          (α i • qs.ket (label i))
          (α j • qs.ket (label j))
          =
        0 := by
    intro i hi j hj hij
    have hlabel_ne : label i ≠ label j := by
      intro hlabel
      exact hij (hwrite_inj i hi j hj hlabel)
    rw [
      inner_smul_left,
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne hlabel_ne
    ]
    simp

  have horth_good :
      ∀ i ∈ Sgood, ∀ j ∈ Sgood, i ≠ j →
        inner ℂ
          (α i • qs.ket (label i))
          (α j • qs.ket (label j))
          =
        0 := by
    intro i hi j hj hij
    exact horth_full i (hSsub hi) j (hSsub hj) hij

  have hfull_flat :
      qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
        =
      ∑ i ∈ Sfull, α i • qs.ket (label i) := by
    simp [
      Sfull,
      α,
      label,
      ModMulConfig.U1,
      Finset.sum_sigma
    ] at *
    simpa [
      ModMulConfig.U1,
      Finset.smul_sum,
      smul_smul
    ] using tr.full_step1_eq

  have hgood_flat :
      tr.goodStep1
        =
      ∑ i ∈ Sgood, α i • qs.ket (label i) := by
    simp [
      Sgood,
      α,
      label,
      Alg1Trace.goodStep1,
      Finset.sum_sigma,
      Finset.smul_sum,
      smul_smul
    ]

  have hfull_norm :
      ‖qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ‖ =
        1 := by
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

  -- Orthogonality turns both squared norms into sums of squared term norms.
  have hsq_full :
      ‖∑ i ∈ Sfull, α i • qs.ket (label i)‖ ^ 2
        =
      ∑ i ∈ Sfull,
        ‖α i • qs.ket (label i)‖ ^ 2 :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
      (qs := qs)
      Sfull
      (fun i => α i • qs.ket (label i))
      horth_full

  have hsq_good :
      ‖∑ i ∈ Sgood, α i • qs.ket (label i)‖ ^ 2
        =
      ∑ i ∈ Sgood,
        ‖α i • qs.ket (label i)‖ ^ 2 :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
      (qs := qs)
      Sgood
      (fun i => α i • qs.ket (label i))
      horth_good

  have hsum_le :
      (∑ i ∈ Sgood,
        ‖α i • qs.ket (label i)‖ ^ 2)
        ≤
      ∑ i ∈ Sfull,
        ‖α i • qs.ket (label i)‖ ^ 2 := by
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        hSsub
        (by
          intro i hi_full hi_not_good
          exact sq_nonneg _)

  -- The good sum is a sub-sum of the unit-norm full packet.
  have hsq_le_one :
      ‖tr.goodStep1‖ ^ 2 ≤ 1 := by
    calc
      ‖tr.goodStep1‖ ^ 2
          =
        ‖∑ i ∈ Sgood,
          α i • qs.ket (label i)‖ ^ 2 := by
            rw [hgood_flat]
      _ =
        ∑ i ∈ Sgood,
          ‖α i • qs.ket (label i)‖ ^ 2 :=
        hsq_good
      _ ≤
        ∑ i ∈ Sfull,
          ‖α i • qs.ket (label i)‖ ^ 2 :=
        hsum_le
      _ =
        ‖∑ i ∈ Sfull,
          α i • qs.ket (label i)‖ ^ 2 :=
        hsq_full.symm
      _ =
        ‖qs.eval
          (ModMulConfig.U1 (Basis := qs.Basis) cfg)
          ψ‖ ^ 2 := by
            rw [hfull_flat]
      _ = 1 := by
          rw [hfull_norm]
          norm_num

  have hnonneg : 0 ≤ ‖tr.goodStep1‖ :=
    norm_nonneg _

  nlinarith [sq_nonneg (‖tr.goodStep1‖ - 1)]

/-! ## Uniform Step-1 and Step-5 Tail Bound -/

/--
There is one nonnegative constant `Cpe` that simultaneously bounds the bad QPE
mass of every good basis input, the squared Step-1 truncation error, and the
squared Step-5 cleanup error by `Cpe * η`.

This is the main theorem of the file. It lifts the basis-input estimate from
`alg1_qpe_tail_basis_uniform` to arbitrary valid unit inputs by identifying both
state-level errors with `alg1TraceBadMass`.
-/
lemma alg1_qpe_tail_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs] :
    ∃ Cpe : ℝ, 0 ≤ Cpe ∧
      (∀ (η : ℝ) (cfg : ModMulConfig η)
          (b : qs.Basis),
          GoodModMulBasisInput
            qs
            cfg.env.N
            cfg.env.data
            cfg.env.work
            cfg.flag
            b →
          ∑ t ∈ Finset.univ.filter
            (fun t => t ∉ alg1GoodLabels cfg b),
            ‖alg1PhaseCoeff qs cfg b t‖ ^ 2
              ≤
            Cpe * η) ∧
      (∀ (η : ℝ) (cfg : ModMulConfig η)
          (ψ : qs.State) (tr : Alg1Trace qs cfg ψ),
          cfg.ValidUnitState qs ψ →
          ‖qs.eval
              (ModMulConfig.U1 (Basis := qs.Basis) cfg)
              ψ
              -
            tr.goodStep1‖ ^ 2
              ≤
            Cpe * η) ∧
      (∀ (η : ℝ) (cfg : ModMulConfig η)
          (ψ : qs.State) (tr : Alg1Trace qs cfg ψ),
          cfg.ValidUnitState qs ψ →
          ‖qs.eval
              (ModMulConfig.U5 (Basis := qs.Basis) cfg)
              tr.afterStep34Ref
              -
            qs.eval
              (ModMulConfig.idealGate cfg)
              ψ‖ ^ 2
              ≤
            Cpe * η) := by
  rcases alg1_qpe_tail_basis_uniform qs with
    ⟨Cpe, hCpe_nonneg, hTail⟩

  refine ⟨Cpe, hCpe_nonneg, ?_, ?_, ?_⟩

  -- Basis-input bad mass.
  · intro η cfg b hb
    simpa [alg1QpeBadMass] using
      hTail η cfg b hb

  -- Step-1 error on an arbitrary valid unit state.
  · intro η cfg ψ tr hunit
    rw [alg1_step1_error_sq_eq_trace_bad_mass qs cfg ψ tr]
    exact
      alg1_trace_bad_mass_le_of_basis_tail
        qs
        hTail
        cfg
        ψ
        tr
        hunit

  -- Step-5 cleanup error on an arbitrary valid unit state.
  · intro η cfg ψ tr hunit
    rw [alg1_step5_cleanup_sq_eq_trace_bad_mass qs cfg ψ tr]
    exact
      alg1_trace_bad_mass_le_of_basis_tail
        qs
        hTail
        cfg
        ψ
        tr
        hunit
