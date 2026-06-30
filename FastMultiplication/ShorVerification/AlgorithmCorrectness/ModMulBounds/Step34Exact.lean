import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModMulBounds.Step2Bound

open Shor

universe v

/-!
# Steps 3 and 4 Exactness

Focus theorem: `alg1_step34_reference_exact`.

This file reduces the Step-2 value to the ideal modular multiplication result
and proves the exactness of Steps 3 and 4 on the reference state.
-/

lemma alg1_step3_reduces_to_modmul
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
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
  let N : ℕ := cfg.env.N
  let x : ℕ := RegEncoding.toNat cfg.env.data b
  let r : ℕ := alg1TargetResidue cfg b
  let s : ℕ := alg1Step2Value cfg b

  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

  have hxlt : x < N := by
    simpa [x, N] using hb.1

  have hrlt : r < N := by
    simpa [r, N] using alg1TargetResidue_lt_N cfg b

  have hs_eq : s = x + r := by
    simp [s, x, r, alg1Step2Value]

  have hslt : s < 2 * N := by
    rw [hs_eq]
    omega

  have hy_mod :
      alg1OutputValue cfg b = s % N := by
    rw [hs_eq]
    dsimp [x, r, N]
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

  by_cases hover : alg1Overflow cfg b
  ·
    have hover' : N ≤ s := by
      simpa [alg1Overflow, s, N] using hover
    have hmod :
        s % N = s - N := by
      calc
        s % N = (s - N) % N := Nat.mod_eq_sub_mod hover'
        _ = s - N := Nat.mod_eq_of_lt (by omega)
    simp [hover, hy_mod, hmod, s, N]
  ·
    have hover' : ¬ N ≤ s := by
      simpa [alg1Overflow, s, N] using hover
    have hmod :
        s % N = s := Nat.mod_eq_of_lt (lt_of_not_ge hover')
    simp [hover, hy_mod, hmod, s, N]


private lemma writeNat_overwrite_same
    {Basis : Type u} [RegEncoding Basis]
    (r : Reg) (v w : ℕ) (b : Basis) :
    RegEncoding.writeNat r v (RegEncoding.writeNat r w b)
      =
    RegEncoding.writeNat r v b := by
  apply RegEncoding.basis_ext
  intro q
  by_cases hqin : r.lo ≤ q ∧ q < r.hi
  · exact
      RegEncoding.bit_writeNat_in
        (r := r)
        (v := v)
        (b1 := RegEncoding.writeNat r w b)
        (b2 := b)
        (q := q)
        hqin.1
        hqin.2
  ·
    have hqout : q < r.lo ∨ r.hi ≤ q := by
      rcases not_and_or.mp hqin with h | h
      · exact Or.inl (lt_of_not_ge h)
      · exact Or.inr (le_of_not_gt h)
    rw [
      RegEncoding.bit_writeNat_out
        (r := r) (v := v) (b := RegEncoding.writeNat r w b)
        (q := q) hqout,
      RegEncoding.bit_writeNat_out
        (r := r) (v := v) (b := b)
        (q := q) hqout,
      RegEncoding.bit_writeNat_out
        (r := r) (v := w) (b := b)
        (q := q) hqout
    ]

private lemma disjoint_qubitReg_of_outside
    {q : ℕ} {r : Reg}
    (h : QubitOutside q r) :
    Disjoint (qubitReg q) r := by
  rcases h with h | h
  · left
    simpa [qubitReg, Reg.hi] using Nat.succ_le_of_lt h
  · right
    simpa [qubitReg] using h

private lemma disjoint_of_qubitReg_outside
    {q : ℕ} {r : Reg}
    (h : QubitOutside q r) :
    Disjoint r (qubitReg q) := by
  rcases disjoint_qubitReg_of_outside (q := q) (r := r) h with hdisj | hdisj
  · exact Or.inr hdisj
  · exact Or.inl hdisj

/--
Steps 3 and 4 are exact on the Step-2 reference state.

This is where:
* `alg1_step3_reduces_to_modmul`,
* `alg1_step4_comparison_recovers_overflow`,
* register-locality lemmas for the primitive comparator/subtractor

are used.
-/
lemma alg1_step34_reference_exact_core
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [ModMulPrimitiveSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
        tr.afterStep2Ref
      =
    tr.afterStep34Ref := by
  classical

  let xext : Reg := extendHi cfg.env.data
  let flagReg : Reg := qubitReg cfg.flag

  have hXW : Disjoint xext cfg.env.work := by
    simpa [xext] using cfg.layout.1

  have hflagX_out : QubitOutside cfg.flag xext := by
    simpa [xext] using cfg.layout.2.1

  have hflagW_out : QubitOutside cfg.flag cfg.env.work :=
    cfg.layout.2.2.1

  have hflagX : Disjoint flagReg xext := by
    simpa [flagReg] using
      disjoint_qubitReg_of_outside
        (q := cfg.flag) (r := xext) hflagX_out

  have hXflag : Disjoint xext flagReg := by
    simpa [flagReg] using
      disjoint_of_qubitReg_outside
        (q := cfg.flag) (r := xext) hflagX_out

  have hflagW : Disjoint flagReg cfg.env.work := by
    simpa [flagReg] using
      disjoint_qubitReg_of_outside
        (q := cfg.flag) (r := cfg.env.work) hflagW_out

  have hWflag : Disjoint cfg.env.work flagReg := by
    simpa [flagReg] using
      disjoint_of_qubitReg_outside
        (q := cfg.flag) (r := cfg.env.work) hflagW_out

  have hket :
      ∀ b ∈ tr.support,
        ∀ t ∈ alg1GoodLabels cfg b,
          tr.phaseCoeff b t ≠ 0 →
          qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
            (qs.ket
              (RegEncoding.writeNat
                xext
                (alg1Step2Value cfg b)
                (RegEncoding.writeNat cfg.env.work t.1 b)))
          =
          qs.ket
            (RegEncoding.writeNat
              xext
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work t.1 b)) := by
    intro b hb t ht hphase_ne

    let s : ℕ := alg1Step2Value cfg b
    let y : ℕ := alg1OutputValue cfg b
    let w0 : qs.Basis :=
      RegEncoding.writeNat cfg.env.work t.1 b
    let b2 : qs.Basis :=
      RegEncoding.writeNat xext s w0
    let red : ℕ :=
      if alg1Overflow cfg b then s - cfg.env.N else s
    let cmp : ℕ :=
      if alg1Overflow cfg b then 1 else 0
    let b3 : qs.Basis :=
      RegEncoding.writeNat flagReg cmp
        (RegEncoding.writeNat xext red b2)

    have hb_good :
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b :=
      tr.input_good b hb

    have hs_cap : s < ASize xext := by
      simpa [s, xext] using
        alg1Step2Value_lt_extendHi_capacity cfg b hb_good

    have hy_cap : y < ASize xext := by
      have hy_data :
          y < ASize cfg.env.data := by
        simpa [y] using
          alg1OutputValue_lt_data_capacity cfg b hb_good
      have hle : ASize cfg.env.data ≤ ASize xext := by
        simp [xext, ASize, regSize, extendHi, Nat.pow_succ]
      exact lt_of_lt_of_le hy_data hle

    have hred_eq_y : red = y := by
      dsimp [red, s, y]
      exact alg1_step3_reduces_to_modmul cfg b hb_good

    have hred_cap : red < ASize xext := by
      rw [hred_eq_y]
      exact hy_cap

    have hs_lt_twoN : s < 2 * cfg.env.N := by
      have hx :
          RegEncoding.toNat cfg.env.data b < cfg.env.N :=
        hb_good.1
      have hr :
          alg1TargetResidue cfg b < cfg.env.N :=
        alg1TargetResidue_lt_N cfg b
      dsimp [s, alg1Step2Value]
      omega

    have hflag_clean_b2 :
        RegEncoding.toNat flagReg b2 = 0 := by
      calc
        RegEncoding.toNat flagReg b2
            =
          RegEncoding.toNat flagReg w0 := by
            dsimp [b2]
            exact
              RegEncoding.toNat_left_write_right
                flagReg xext hflagX w0 s
        _ =
          RegEncoding.toNat flagReg b := by
            dsimp [w0]
            exact
              RegEncoding.toNat_left_write_right
                flagReg cfg.env.work hflagW b t.1
        _ = 0 := by
            simpa [flagReg] using hb_good.2.2.2

    have hx_b2 :
        RegEncoding.toNat xext b2 = s := by
      dsimp [b2]
      exact
        RegEncoding.toNat_writeNat_of_lt
          xext s w0 hs_cap

    have hstep3 :
        qs.eval (step3 cfg.env.N xext cfg.flag) (qs.ket b2)
          =
        qs.ket b3 := by
      have hraw :=
        ModMulPrimitiveSemantics.eval_step3_clean_ket
          (qs := qs)
          cfg.env.N
          xext
          cfg.flag
          b2
          hflagX_out
          (by simpa [flagReg] using hflag_clean_b2)
          (by simpa [hx_b2] using hs_lt_twoN)
      simpa [
        b3, red, cmp, flagReg, hx_b2, s
      ] using hraw

    have hx_after_x :
        RegEncoding.toNat xext
            (RegEncoding.writeNat xext red b2)
          =
        red :=
      RegEncoding.toNat_writeNat_of_lt xext red b2 hred_cap

    have hx_b3 :
        RegEncoding.toNat xext b3 = y := by
      calc
        RegEncoding.toNat xext b3
            =
          RegEncoding.toNat xext
            (RegEncoding.writeNat xext red b2) := by
            dsimp [b3]
            exact
              RegEncoding.toNat_left_write_right
                xext flagReg hXflag
                (RegEncoding.writeNat xext red b2)
                cmp
        _ = red := hx_after_x
        _ = y := hred_eq_y

    have hwork_b2 :
        RegEncoding.toNat cfg.env.work b2 = t.1 := by
      calc
        RegEncoding.toNat cfg.env.work b2
            =
          RegEncoding.toNat cfg.env.work w0 := by
            dsimp [b2]
            exact
              RegEncoding.toNat_right_write_left
                xext cfg.env.work hXW w0 s
        _ = t.1 := by
            dsimp [w0]
            exact
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work t.1 b t.isLt

    have hwork_after_x :
        RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat xext red b2)
          =
        t.1 := by
      calc
        RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat xext red b2)
            =
          RegEncoding.toNat cfg.env.work b2 := by
            exact
              RegEncoding.toNat_right_write_left
                xext cfg.env.work hXW b2 red
        _ = t.1 := hwork_b2

    have hwork_b3 :
        RegEncoding.toNat cfg.env.work b3 = t.1 := by
      calc
        RegEncoding.toNat cfg.env.work b3
            =
          RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat xext red b2) := by
            dsimp [b3]
            exact
              RegEncoding.toNat_left_write_right
                cfg.env.work flagReg hWflag
                (RegEncoding.writeNat xext red b2)
                cmp
        _ = t.1 := hwork_after_x

    have hflag_b3 :
        RegEncoding.toNat flagReg b3 = cmp := by
      dsimp [b3]
      apply RegEncoding.toNat_writeNat_of_lt
      dsimp [cmp, flagReg, ASize, regSize, qubitReg]
      by_cases h : alg1Overflow cfg b <;> simp [h]

    have hcmp_eq_cross :
        cmp =
          (if RegEncoding.toNat xext b3 * ASize cfg.env.work
                < cfg.env.N * RegEncoding.toNat cfg.env.work b3 then
            1
          else
            0) := by
      have hcross :
          (RegEncoding.toNat xext b3 * ASize cfg.env.work
                < cfg.env.N * RegEncoding.toNat cfg.env.work b3)
            ↔
          alg1Overflow cfg b := by
        simpa [
          alg1Step4CrossCondition,
          hx_b3,
          hwork_b3,
          y
        ] using
          (tr.step34_support b hb t ht hphase_ne)
      dsimp [cmp]
      by_cases hover : alg1Overflow cfg b
      · have hcross_true :
            RegEncoding.toNat xext b3 * ASize cfg.env.work
                < cfg.env.N * RegEncoding.toNat cfg.env.work b3 :=
          hcross.mpr hover
        simp [hover, hcross_true]
      · have hcross_false :
            ¬ RegEncoding.toNat xext b3 * ASize cfg.env.work
                < cfg.env.N * RegEncoding.toNat cfg.env.work b3 := by
          intro h
          exact hover (hcross.mp h)
        simp [hover, hcross_false]

    have hstep4 :
        qs.eval (step4 cfg.env.N xext cfg.env.work cfg.flag) (qs.ket b3)
          =
        qs.ket (RegEncoding.writeNat flagReg 0 b3) := by
      have hraw :=
        ModMulPrimitiveSemantics.eval_step4_cancels_ket
          (qs := qs)
          cfg.env.N
          xext
          cfg.env.work
          cfg.flag
          b3
          hflagX_out
          hflagW_out
          (by
            rw [hflag_b3]
            exact hcmp_eq_cross)
      simpa [flagReg] using hraw

    have hfinal_clean :
        RegEncoding.toNat flagReg
          (RegEncoding.writeNat xext y w0) = 0 := by
      calc
        RegEncoding.toNat flagReg
          (RegEncoding.writeNat xext y w0)
            =
          RegEncoding.toNat flagReg w0 := by
            exact
              RegEncoding.toNat_left_write_right
                flagReg xext hflagX w0 y
        _ =
          RegEncoding.toNat flagReg b := by
            dsimp [w0]
            exact
              RegEncoding.toNat_left_write_right
                flagReg cfg.env.work hflagW b t.1
        _ = 0 := by
            simpa [flagReg] using hb_good.2.2.2

    have hwrite_x_simpl :
        RegEncoding.writeNat xext red b2
          =
        RegEncoding.writeNat xext y w0 := by
      dsimp [b2]
      rw [hred_eq_y]
      exact writeNat_overwrite_same xext y s w0

    have hclear :
        RegEncoding.writeNat flagReg 0 b3
          =
        RegEncoding.writeNat xext y w0 := by
      calc
        RegEncoding.writeNat flagReg 0 b3
            =
          RegEncoding.writeNat flagReg 0
            (RegEncoding.writeNat xext red b2) := by
            dsimp [b3]
            exact writeNat_overwrite_same flagReg 0 cmp
              (RegEncoding.writeNat xext red b2)
        _ =
          RegEncoding.writeNat flagReg 0
            (RegEncoding.writeNat xext y w0) := by
            rw [hwrite_x_simpl]
        _ =
          RegEncoding.writeNat xext y w0 := by
            rw [← hfinal_clean]
            exact RegEncoding.writeNat_toNat flagReg
              (RegEncoding.writeNat xext y w0)

    calc
      qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
          (qs.ket b2)
        =
      qs.eval (step4 cfg.env.N xext cfg.env.work cfg.flag)
          (qs.eval (step3 cfg.env.N xext cfg.flag) (qs.ket b2)) := by
        simp [ModMulConfig.U34, xext, qs.eval_seq]
      _ =
      qs.eval (step4 cfg.env.N xext cfg.env.work cfg.flag)
          (qs.ket b3) := by
        rw [hstep3]
      _ =
      qs.ket (RegEncoding.writeNat flagReg 0 b3) := hstep4
      _ =
      qs.ket (RegEncoding.writeNat xext y w0) := by
        rw [hclear]

  calc
    qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
        tr.afterStep2Ref
      =
    qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
      (∑ b ∈ tr.support,
        tr.inputCoeff b •
          ∑ t ∈ alg1GoodLabels cfg b,
            tr.phaseCoeff b t •
              qs.ket
                (RegEncoding.writeNat
                  xext
                  (alg1Step2Value cfg b)
                  (RegEncoding.writeNat cfg.env.work t.1 b))) := by
        simp [Alg1Trace.afterStep2Ref, xext]
    _ =
    ∑ b ∈ tr.support,
      qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
        (tr.inputCoeff b •
          ∑ t ∈ alg1GoodLabels cfg b,
            tr.phaseCoeff b t •
              qs.ket
                (RegEncoding.writeNat
                  xext
                  (alg1Step2Value cfg b)
                  (RegEncoding.writeNat cfg.env.work t.1 b))) := by
        simpa using
          eval_finset_sum
            qs
            (ModMulConfig.U34 (Basis := qs.Basis) cfg)
            tr.support
            (fun b =>
              tr.inputCoeff b •
                ∑ t ∈ alg1GoodLabels cfg b,
                  tr.phaseCoeff b t •
                    qs.ket
                      (RegEncoding.writeNat
                        xext
                        (alg1Step2Value cfg b)
                        (RegEncoding.writeNat cfg.env.work t.1 b)))
    _ =
    ∑ b ∈ tr.support,
      tr.inputCoeff b •
        qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
          (∑ t ∈ alg1GoodLabels cfg b,
            tr.phaseCoeff b t •
              qs.ket
                (RegEncoding.writeNat
                  xext
                  (alg1Step2Value cfg b)
                  (RegEncoding.writeNat cfg.env.work t.1 b))) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [qs.eval_smul]
    _ =
    ∑ b ∈ tr.support,
      tr.inputCoeff b •
        ∑ t ∈ alg1GoodLabels cfg b,
          qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
            (tr.phaseCoeff b t •
              qs.ket
                (RegEncoding.writeNat
                  xext
                  (alg1Step2Value cfg b)
                  (RegEncoding.writeNat cfg.env.work t.1 b))) := by
        apply Finset.sum_congr rfl
        intro b hb
        congr 1
        simpa using
          eval_finset_sum
            qs
            (ModMulConfig.U34 (Basis := qs.Basis) cfg)
            (alg1GoodLabels cfg b)
            (fun t =>
              tr.phaseCoeff b t •
                qs.ket
                  (RegEncoding.writeNat
                    xext
                    (alg1Step2Value cfg b)
                    (RegEncoding.writeNat cfg.env.work t.1 b)))
    _ =
    ∑ b ∈ tr.support,
      tr.inputCoeff b •
        ∑ t ∈ alg1GoodLabels cfg b,
          tr.phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat
                xext
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work t.1 b)) := by
        apply Finset.sum_congr rfl
        intro b hb
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hphase : tr.phaseCoeff b t = 0
        · simp [hphase, qs.eval_zero]
        · rw [qs.eval_smul, hket b hb t ht hphase]
    _ =
    tr.afterStep34Ref := by
      simp [Alg1Trace.afterStep34Ref, xext]

lemma alg1_step34_reference_exact
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [ModMulPrimitiveSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
        tr.afterStep2Ref
      =
    tr.afterStep34Ref := by
  exact alg1_step34_reference_exact_core qs cfg ψ tr

