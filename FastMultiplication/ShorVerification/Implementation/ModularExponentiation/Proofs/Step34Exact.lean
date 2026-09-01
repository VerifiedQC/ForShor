import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.Step2Bound

open Shor

universe u v

/-!
# Steps 3 and 4 Exactness

Focus theorem: `alg1_step34_reference_exact`.

This file reduces the Step-2 value to the ideal modular multiplication result
and proves the exactness of Steps 3 and 4 on the reference state.

The proof is organized into four layers:

* an arithmetic reduction from the Step-2 sum to modular multiplication;
* register-disjointness and overwrite helpers;
* exact basis-state semantics for Steps 3 and 4, lifted by linearity; and
* the public reference-state exactness theorem.
-/

/-! =========================================================
    Section 1: Step-3 arithmetic reduction

    Reduce the Step-3 comparator/subtractor stage to a plain modular
    multiplication on the relevant basis labels.
========================================================= -/

/--
Conditional subtraction of `N` from the Step-2 value produces exactly the
controlled modular-multiplication output. The proof uses that the unreduced sum
is below `2N`, so at most one subtraction is required.
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
  -- Name the modulus, input, target residue, and unreduced Step-2 sum.
  let N : ℕ := cfg.env.N
  let x : ℕ := RegEncoding.toNat cfg.env.data.active b
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
          (RegEncoding.toNat cfg.env.data.active b)
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

/-- Writing a register twice retains only the final written value. -/
private lemma writeNat_overwrite_same
    {Basis : Type u} [RegEncoding Basis]
    (r : Reg) (v w : ℕ) (b : Basis) :
    RegEncoding.writeNat r v (RegEncoding.writeNat r w b)
      =
    RegEncoding.writeNat r v b :=
  writeNat_overwrite_same_reg r v w b

/-- A qubit outside a register forms a disjoint singleton register. -/
private lemma disjoint_qubitReg_of_outside
    {q : ℕ} {r : Reg}
    (h : QubitOutside q r) :
    Shor.Disjoint (qubitReg q) r := by
  rw [Shor.Disjoint, List.disjoint_left]
  intro p hp hr

  have hpq : p = q := by
    simpa [qubitReg, Reg.singleton] using hp

  subst p
  exact h hr

private lemma freshFor_writeNat_of_disjoint
    {Basis : Type u} [RegEncoding Basis]
    (e : ExtReg) (n : ℕ)
    (r : Reg) (v : ℕ) (b : Basis)
    (hdisj : Shor.Disjoint (e.newBits n) r)
    (hfresh : e.FreshFor n b) :
    e.FreshFor n (RegEncoding.writeNat r v b) := by
  unfold ExtReg.FreshFor FreshZero at hfresh ⊢
  calc
    RegEncoding.toNat (e.newBits n)
        (RegEncoding.writeNat r v b)
      =
    RegEncoding.toNat (e.newBits n) b :=
      RegEncoding.toNat_left_write_right
        (e.newBits n) r hdisj b v
    _ = 0 := hfresh

private lemma toNat_zero_writeNat_of_disjoint
    {Basis : Type u} [RegEncoding Basis]
    (left right : Reg)
    (v : ℕ) (b : Basis)
    (hdisj : Shor.Disjoint left right)
    (hzero : RegEncoding.toNat left b = 0) :
    RegEncoding.toNat left
        (RegEncoding.writeNat right v b) = 0 := by
  calc
    RegEncoding.toNat left
        (RegEncoding.writeNat right v b)
      =
    RegEncoding.toNat left b :=
      RegEncoding.toNat_left_write_right
        left right hdisj b v
    _ = 0 := hzero

private lemma disjoint_newBits_active_self
    (e : ExtReg) (n : ℕ) :
    Shor.Disjoint (e.newBits n) e.active := by
  rw [Shor.Disjoint, List.disjoint_left]
  intro q hqNew hqActive
  have h := e.active_reserve_disjoint
  rw [Shor.Disjoint, List.disjoint_left] at h
  exact h hqActive (List.mem_of_mem_take hqNew)

private lemma disjoint_newBits_active_of_owned
    (x z : ExtReg) (n : ℕ)
    (h : ExtReg.OwnedDisjoint x z) :
    Shor.Disjoint (x.newBits n) z.active := by
    rw [Shor.Disjoint, List.disjoint_left]
    intro q hqx hqz
    rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h
    exact
      h
        (by
          rw [ExtReg.ownedQubits, List.mem_append]
          exact Or.inr (List.mem_of_mem_take hqx))
        (by
          rw [ExtReg.ownedQubits, List.mem_append]
          exact Or.inl hqz)

private lemma disjoint_active_active_of_owned
    (x z : ExtReg)
    (h : ExtReg.OwnedDisjoint x z) :
    Shor.Disjoint x.active z.active := by
  rw [Shor.Disjoint, List.disjoint_left]
  intro q hqx hqz
  rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h
  exact h
    (by
      rw [ExtReg.ownedQubits, List.mem_append]
      exact Or.inl hqx)
    (by
        rw [ExtReg.ownedQubits, List.mem_append]
        exact Or.inl hqz)

/-- Taking two list elements and dropping the first equals taking one from the tail. -/
private lemma take_two_tail_eq_tail_take_one
    {α : Type*} (xs : List α) :
    (xs.take 2).tail = xs.tail.take 1 := by
  cases xs with
  | nil =>
      simp
  | cons _ xs =>
      cases xs <;> simp

private lemma freshFor_grow_one_of_freshFor_two
    {Basis : Type u} [RegEncoding Basis]
    (e : ExtReg) (b : Basis)
    (hcap : e.CanGrow 2)
    (hfresh : e.FreshFor 2 b) :
    (e.grow 1).FreshFor 1 b := by
  unfold ExtReg.FreshFor FreshZero at hfresh ⊢
  let r2 : Reg := e.newBits 2
  have hr2 : regSize r2 = 2 := by
    simpa [r2] using Gate.ExtReg.newBits_size e 2 hcap
  let m : SplitPoint r2 := ⟨1, by omega⟩
  have hsplit :=
    RegEncoding.toNat_split
      (r := r2)
      (m := m)
      (b := b)
  have hright :
      splitRight r2 m = (e.grow 1).newBits 1 := by
    simp [
      r2,
      m,
      splitRight,
      ExtReg.grow,
      ExtReg.newBits,
      ExtReg.remainingReserve,
      Reg.drop,
      Reg.take,
      take_two_tail_eq_tail_take_one
    ]
  have hr2zero : RegEncoding.toNat r2 b = 0 := by
    simpa [r2] using hfresh
  dsimp at hsplit
  rw [hr2zero] at hsplit
  have hzero : RegEncoding.toNat (splitRight r2 m) b = 0 := by
    have hmul :
        ASize (splitLeft r2 m) *
            RegEncoding.toNat (splitRight r2 m) b = 0 := by
      omega
    rcases Nat.mul_eq_zero.mp hmul with hleft | hrightZero
    · have hpos : 0 < ASize (splitLeft r2 m) := by
        simp [ASize]
      omega
    · exact hrightZero
  simpa [hright] using hzero

/-- Symmetric form of singleton-qubit/register disjointness. -/
private lemma disjoint_of_qubitReg_outside
    {q : ℕ} {r : Reg}
    (h : QubitOutside q r) :
    Shor.Disjoint r (qubitReg q) :=
  Shor.Disjoint.symm
    (disjoint_qubitReg_of_outside (q := q) (r := r) h)

/-! =========================================================
    Section 2: Exact basis-state semantics of steps 3 and 4

    Register-disjointness helpers and the core computation giving the exact
    post-Step-3/4 basis state on a clean input.
========================================================= -/

/--
Steps 3 and 4 are exact on the Step-2 reference state.

This is where:

* `alg1_step3_reduces_to_modmul`;
* `alg1_step4_comparison_recovers_overflow`;
* register-locality lemmas for the primitive comparator/subtractor

are used.
-/
lemma alg1_step34_reference_exact_core
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
        tr.afterStep2Ref
      =
    tr.afterStep34Ref := by
  classical

  -- Abbreviate the three registers touched by Steps 3 and 4.
  let xext : Reg := (cfg.env.data.grow 1).active
  let work : Reg := cfg.env.work.active
  let flagReg : Reg := qubitReg cfg.flag

  have hXW : Shor.Disjoint xext work := by
    rw [Shor.Disjoint, List.disjoint_left]
    intro q hqX hqW

    have h :=
      cfg.env.circuit_workspace.dataCarry_work_disjoint

    rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h

    exact h
      (List.mem_append_left _ hqX)
      (List.mem_append_left _ hqW)

  have hWX : Shor.Disjoint work xext :=
    Shor.Disjoint.symm hXW

  have hflagX_out : QubitOutside cfg.flag xext := by
    intro hq

    apply cfg.layout.2.1

    have howned :
        cfg.flag ∈ (cfg.env.data.grow 1).ownedQubits :=
      List.mem_append_left _ hq

    simpa [Gate.ExtReg.ownedQubits_grow] using howned

  have hflagW_out : QubitOutside cfg.flag work := by
    intro hq
    exact cfg.layout.2.2.1
      (List.mem_append_left _ hq)

  have hflagX : Shor.Disjoint flagReg xext :=
    disjoint_qubitReg_of_outside hflagX_out

  have hXflag : Shor.Disjoint xext flagReg :=
    disjoint_of_qubitReg_outside hflagX_out

  have hflagW : Shor.Disjoint flagReg work :=
    disjoint_qubitReg_of_outside hflagW_out

  have hWflag : Shor.Disjoint work flagReg :=
    disjoint_of_qubitReg_outside hflagW_out

  have hket :
      ∀ b ∈ tr.support,
        ∀ t ∈ alg1GoodLabels cfg b,
          tr.phaseCoeff b t ≠ 0 →
          qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
            (qs.ket
              (RegEncoding.writeNat
                xext
                (alg1Step2Value cfg b)
                (RegEncoding.writeNat cfg.env.work.active t.1 b)))
          =
          qs.ket
            (RegEncoding.writeNat
              xext
              (alg1OutputValue cfg b)
              (RegEncoding.writeNat cfg.env.work.active t.1 b)) := by
    intro b hb t ht hphase_ne

    -- Name the intermediate arithmetic values and basis states.
    let s : ℕ := alg1Step2Value cfg b
    let y : ℕ := alg1OutputValue cfg b
    let w0 : qs.Basis :=
      RegEncoding.writeNat cfg.env.work.active t.1 b
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
        alg1Step2Value_lt_dataCarry_capacity cfg b hb_good

    have hy_cap : y < ASize xext := by
      have hy_data :
          y < ASize cfg.env.data.active := by
        simpa [y] using
          alg1OutputValue_lt_data_capacity cfg b hb_good

      have hwidth :
          regSize xext =
            regSize cfg.env.data.active + 1 := by
        dsimp [xext]
        simpa [ExtReg.width] using
          ExtReg.width_grow
            cfg.env.data
            1
            cfg.env.circuit_workspace.data_canGrow_one

      have hle :
          ASize cfg.env.data.active ≤ ASize xext := by
        unfold ASize
        rw [hwidth, pow_succ]
        omega

      exact lt_of_lt_of_le hy_data hle

    have hred_eq_y : red = y := by
      dsimp [red, s, y]
      exact alg1_step3_reduces_to_modmul cfg b hb_good

    have hred_cap : red < ASize xext := by
      rw [hred_eq_y]
      exact hy_cap

    have hs_lt_twoN : s < 2 * cfg.env.N := by
      have hx :
          RegEncoding.toNat cfg.env.data.active b < cfg.env.N :=
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
                flagReg cfg.env.work.active hflagW b t.1
        _ = 0 := by
            simpa [flagReg] using hb_good.2.2.2.2

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
        eval_step3_clean_ket
          (qs := qs)
          cfg.env.N
          xext
          cfg.flag
          b2
          hflagX_out
          (by simpa [flagReg] using hflag_clean_b2)
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
        RegEncoding.toNat cfg.env.work.active b2 = t.1 := by
      calc
        RegEncoding.toNat cfg.env.work.active b2
            =
          RegEncoding.toNat cfg.env.work.active w0 := by
            dsimp [b2]
            exact
              RegEncoding.toNat_right_write_left
                xext cfg.env.work.active hXW w0 s
        _ = t.1 := by
            dsimp [w0]
            exact
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work.active t.1 b t.isLt

    have hwork_after_x :
        RegEncoding.toNat cfg.env.work.active
            (RegEncoding.writeNat xext red b2)
          =
        t.1 := by
      calc
        RegEncoding.toNat cfg.env.work.active
            (RegEncoding.writeNat xext red b2)
            =
          RegEncoding.toNat cfg.env.work.active b2 := by
            exact
              RegEncoding.toNat_right_write_left
                xext cfg.env.work.active hXW b2 red
        _ = t.1 := hwork_b2

    have hwork_b3 :
        RegEncoding.toNat cfg.env.work.active b3 = t.1 := by
      calc
        RegEncoding.toNat cfg.env.work.active b3
            =
          RegEncoding.toNat cfg.env.work.active
            (RegEncoding.writeNat xext red b2) := by
            dsimp [b3]
            exact
              RegEncoding.toNat_left_write_right
                cfg.env.work.active flagReg hWflag
                (RegEncoding.writeNat xext red b2)
                cmp
        _ = t.1 := hwork_after_x

    have hflag_b3 :
        RegEncoding.toNat flagReg b3 = cmp := by
      dsimp [b3]
      apply RegEncoding.toNat_writeNat_of_lt
      dsimp [
        cmp,
        flagReg,
        ASize,
        regSize,
        qubitReg,
        Reg.singleton,
        Reg.width
      ]
      by_cases h : alg1Overflow cfg b <;> simp [h]

    have hcmp_eq_cross :
        cmp =
          (if RegEncoding.toNat xext b3 * ASize cfg.env.work.active
                < cfg.env.N * RegEncoding.toNat cfg.env.work.active b3 then
            1
          else
            0) := by
      have hcross :
          (RegEncoding.toNat xext b3 * ASize cfg.env.work.active
                < cfg.env.N * RegEncoding.toNat cfg.env.work.active b3)
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
      ·
        have hcross_true :
            RegEncoding.toNat xext b3 * ASize cfg.env.work.active
                < cfg.env.N * RegEncoding.toNat cfg.env.work.active b3 :=
          hcross.mpr hover
        simp [hover, hcross_true]
      ·
        have hcross_false :
            ¬ RegEncoding.toNat xext b3 * ASize cfg.env.work.active
                < cfg.env.N * RegEncoding.toNat cfg.env.work.active b3 := by
          intro h
          exact hover (hcross.mp h)
        simp [hover, hcross_false]

    have hDataWorkOwned :
        ExtReg.OwnedDisjoint
          (cfg.env.data.grow 1) cfg.env.work :=
      cfg.step4_workspace.data_work_disjoint

    have hWorkDataOwned :
        ExtReg.OwnedDisjoint
          cfg.env.work (cfg.env.data.grow 1) := by
      exact List.Disjoint.symm hDataWorkOwned

    have hDataScratchOwned :
        ExtReg.OwnedDisjoint
          (cfg.env.data.grow 1) cfg.env.scratch :=
      cfg.step4_workspace.data_scratch_disjoint

    have hScratchDataOwned :
        ExtReg.OwnedDisjoint
          cfg.env.scratch (cfg.env.data.grow 1) := by
      exact List.Disjoint.symm hDataScratchOwned

    have hWorkScratchOwned :
        ExtReg.OwnedDisjoint
          cfg.env.work cfg.env.scratch :=
      cfg.step4_workspace.work_scratch_disjoint

    have hScratchWorkOwned :
        ExtReg.OwnedDisjoint
          cfg.env.scratch cfg.env.work := by
      exact List.Disjoint.symm hWorkScratchOwned

    have hDataNewW :
        Shor.Disjoint
          ((cfg.env.data.grow 1).newBits 1)
          cfg.env.work.active :=
      disjoint_newBits_active_of_owned
        (cfg.env.data.grow 1) cfg.env.work 1
        hDataWorkOwned

    have hDataNewX :
        Shor.Disjoint
          ((cfg.env.data.grow 1).newBits 1)
          xext := by
      simpa [xext] using
        disjoint_newBits_active_self
          (cfg.env.data.grow 1) 1

    have hflagDataNew_out :
        QubitOutside cfg.flag
          ((cfg.env.data.grow 1).newBits 1) := by
      intro hq
      exact cfg.step4_workspace.flag_not_data
        (by
          rw [ExtReg.ownedQubits, List.mem_append]
          exact Or.inr (List.mem_of_mem_take hq))

    have hDataNewFlag :
        Shor.Disjoint
          ((cfg.env.data.grow 1).newBits 1)
          flagReg :=
      disjoint_of_qubitReg_outside hflagDataNew_out

    have hWorkNewX :
        Shor.Disjoint
          (cfg.env.work.newBits 1) xext := by
      simpa [xext] using
        disjoint_newBits_active_of_owned
          cfg.env.work
          (cfg.env.data.grow 1)
          1
          hWorkDataOwned

    have hflagWorkNew_out :
        QubitOutside cfg.flag
          (cfg.env.work.newBits 1) := by
      intro hq
      exact cfg.step4_workspace.flag_not_work
        (by
          rw [ExtReg.ownedQubits, List.mem_append]
          exact Or.inr (List.mem_of_mem_take hq))

    have hWorkNewFlag :
        Shor.Disjoint
          (cfg.env.work.newBits 1)
          flagReg :=
      disjoint_of_qubitReg_outside hflagWorkNew_out

    have hScratchNewW :
        Shor.Disjoint
          (cfg.env.scratch.newBits 1)
          cfg.env.work.active :=
      disjoint_newBits_active_of_owned
        cfg.env.scratch cfg.env.work 1
        hScratchWorkOwned

    have hScratchNewX :
        Shor.Disjoint
          (cfg.env.scratch.newBits 1)
          xext := by
      simpa [xext] using
        disjoint_newBits_active_of_owned
          cfg.env.scratch
          (cfg.env.data.grow 1)
          1
          hScratchDataOwned

    have hflagScratchNew_out :
        QubitOutside cfg.flag
          (cfg.env.scratch.newBits 1) := by
      intro hq
      exact cfg.step4_workspace.flag_not_scratch
        (by
          rw [ExtReg.ownedQubits, List.mem_append]
          exact Or.inr (List.mem_of_mem_take hq))

    have hScratchNewFlag :
        Shor.Disjoint
          (cfg.env.scratch.newBits 1)
          flagReg :=
      disjoint_of_qubitReg_outside hflagScratchNew_out

    have hScratchW :
        Shor.Disjoint
          cfg.env.scratch.active
          cfg.env.work.active :=
      disjoint_active_active_of_owned
        cfg.env.scratch cfg.env.work hScratchWorkOwned

    have hScratchX :
        Shor.Disjoint
          cfg.env.scratch.active xext := by
      simpa [xext] using
        disjoint_active_active_of_owned
          cfg.env.scratch
          (cfg.env.data.grow 1)
          hScratchDataOwned

    have hflagScratch_out :
        QubitOutside cfg.flag cfg.env.scratch.active := by
      intro hq
      exact cfg.step4_workspace.flag_not_scratch
        (by
          rw [ExtReg.ownedQubits, List.mem_append]
          exact Or.inl hq)

    have hScratchFlag :
        Shor.Disjoint cfg.env.scratch.active flagReg :=
      disjoint_of_qubitReg_outside hflagScratch_out

    have hdataFresh0 :
        (cfg.env.data.grow 1).FreshFor 1 b :=
      freshFor_grow_one_of_freshFor_two
        cfg.env.data b
        cfg.env.circuit_workspace.1
        hb_good.2.1

    have hdataFresh_w0 :
        (cfg.env.data.grow 1).FreshFor 1 w0 := by
      dsimp [w0]
      exact freshFor_writeNat_of_disjoint
        (cfg.env.data.grow 1) 1
        cfg.env.work.active t.1 b
        hDataNewW hdataFresh0

    have hdataFresh_b2 :
        (cfg.env.data.grow 1).FreshFor 1 b2 := by
      dsimp [b2]
      exact freshFor_writeNat_of_disjoint
        (cfg.env.data.grow 1) 1
        xext s w0
        hDataNewX hdataFresh_w0

    have hdataFresh_red :
        (cfg.env.data.grow 1).FreshFor 1
          (RegEncoding.writeNat xext red b2) :=
      freshFor_writeNat_of_disjoint
        (cfg.env.data.grow 1) 1
        xext red b2
        hDataNewX hdataFresh_b2

    have hdataFresh_b3 :
        (cfg.env.data.grow 1).FreshFor 1 b3 := by
      dsimp [b3]
      exact freshFor_writeNat_of_disjoint
        (cfg.env.data.grow 1) 1
        flagReg cmp
        (RegEncoding.writeNat xext red b2)
        hDataNewFlag hdataFresh_red

    have hworkFresh_w0 :
        cfg.env.work.FreshFor 1 w0 := by
      dsimp [w0]
      exact ExtReg.freshFor_write_active
        cfg.env.work 1 t.1 b
        hb_good.2.2.2.1

    have hworkFresh_b2 :
        cfg.env.work.FreshFor 1 b2 := by
      dsimp [b2]
      exact freshFor_writeNat_of_disjoint
        cfg.env.work 1
        xext s w0
        hWorkNewX hworkFresh_w0

    have hworkFresh_red :
        cfg.env.work.FreshFor 1
          (RegEncoding.writeNat xext red b2) :=
      freshFor_writeNat_of_disjoint
        cfg.env.work 1
        xext red b2
        hWorkNewX hworkFresh_b2

    have hworkFresh_b3 :
        cfg.env.work.FreshFor 1 b3 := by
      dsimp [b3]
      exact freshFor_writeNat_of_disjoint
        cfg.env.work 1
        flagReg cmp
        (RegEncoding.writeNat xext red b2)
        hWorkNewFlag hworkFresh_red

    have hscratchFresh_w0 :
        cfg.env.scratch.FreshFor 1 w0 := by
      dsimp [w0]
      exact freshFor_writeNat_of_disjoint
        cfg.env.scratch 1
        cfg.env.work.active t.1 b
        hScratchNewW
        (tr.scratch_fresh b hb)

    have hscratchFresh_b2 :
        cfg.env.scratch.FreshFor 1 b2 := by
      dsimp [b2]
      exact freshFor_writeNat_of_disjoint
        cfg.env.scratch 1
        xext s w0
        hScratchNewX hscratchFresh_w0

    have hscratchFresh_red :
        cfg.env.scratch.FreshFor 1
          (RegEncoding.writeNat xext red b2) :=
      freshFor_writeNat_of_disjoint
        cfg.env.scratch 1
        xext red b2
        hScratchNewX hscratchFresh_b2

    have hscratchFresh_b3 :
        cfg.env.scratch.FreshFor 1 b3 := by
      dsimp [b3]
      exact freshFor_writeNat_of_disjoint
        cfg.env.scratch 1
        flagReg cmp
        (RegEncoding.writeNat xext red b2)
        hScratchNewFlag hscratchFresh_red

    have hscratchZero_w0 :
        RegEncoding.toNat cfg.env.scratch.active w0 = 0 := by
      dsimp [w0]
      exact toNat_zero_writeNat_of_disjoint
        cfg.env.scratch.active
        cfg.env.work.active
        t.1 b
        hScratchW
        (tr.scratch_zero b hb)

    have hscratchZero_b2 :
        RegEncoding.toNat cfg.env.scratch.active b2 = 0 := by
      dsimp [b2]
      exact toNat_zero_writeNat_of_disjoint
        cfg.env.scratch.active
        xext
        s w0
        hScratchX hscratchZero_w0

    have hscratchZero_red :
        RegEncoding.toNat cfg.env.scratch.active
          (RegEncoding.writeNat xext red b2) = 0 :=
      toNat_zero_writeNat_of_disjoint
        cfg.env.scratch.active
        xext
        red b2
        hScratchX hscratchZero_b2

    have hscratchZero_b3 :
        RegEncoding.toNat cfg.env.scratch.active b3 = 0 := by
      dsimp [b3]
      exact toNat_zero_writeNat_of_disjoint
        cfg.env.scratch.active
        flagReg
        cmp
        (RegEncoding.writeNat xext red b2)
        hScratchFlag hscratchZero_red

    have hstep4 :
        qs.eval
            (step4
              cfg.env.N
              (cfg.env.data.grow 1)
              cfg.env.work
              cfg.env.scratch
              cfg.flag
              cfg.step4_workspace)
            (qs.ket b3)
          =
        qs.ket
          (RegEncoding.writeNat flagReg 0 b3) := by
      have hraw :=
        eval_step4_cancels_ket
          (qs := qs)
          cfg.env.N
          (cfg.env.data.grow 1)
          cfg.env.work
          cfg.env.scratch
          cfg.flag
          cfg.step4_workspace
          b3
          hdataFresh_b3
          hworkFresh_b3
          hscratchZero_b3
          hscratchFresh_b3
          (by
            rw [hflag_b3]
            simpa [xext] using hcmp_eq_cross)
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
                flagReg cfg.env.work.active hflagW b t.1
        _ = 0 := by
            simpa [flagReg] using hb_good.2.2.2.2

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
      qs.eval
          (step4
            cfg.env.N
            (cfg.env.data.grow 1)
            cfg.env.work
            cfg.env.scratch
            cfg.flag
            cfg.step4_workspace)
          (qs.eval
            (step3 cfg.env.N xext cfg.flag)
            (qs.ket b2)) := by
        simp [ModMulConfig.U34, xext, qs.eval_seq]
      _ =
      qs.eval
          (step4
            cfg.env.N
            (cfg.env.data.grow 1)
            cfg.env.work
            cfg.env.scratch
            cfg.flag
            cfg.step4_workspace)
          (qs.ket b3) := by
        rw [hstep3]
      _ =
      qs.ket (RegEncoding.writeNat flagReg 0 b3) :=
        hstep4
      _ =
      qs.ket (RegEncoding.writeNat xext y w0) := by
        rw [hclear]

  -- Extend the basis-state identity across the finite reference packet.
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
                  (RegEncoding.writeNat cfg.env.work.active t.1 b))) := by
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
                  (RegEncoding.writeNat cfg.env.work.active t.1 b))) := by
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
                        (RegEncoding.writeNat cfg.env.work.active t.1 b)))
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
                  (RegEncoding.writeNat cfg.env.work.active t.1 b))) := by
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
                  (RegEncoding.writeNat cfg.env.work.active t.1 b))) := by
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
                    (RegEncoding.writeNat cfg.env.work.active t.1 b)))
    _ =
    ∑ b ∈ tr.support,
      tr.inputCoeff b •
        ∑ t ∈ alg1GoodLabels cfg b,
          tr.phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat
                xext
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work.active t.1 b)) := by
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

/-! =========================================================
    Section 3: Public Step-3/4 exactness theorem

    The public statement: Steps 3 and 4 together act exactly as specified on the
    valid-input subspace.
========================================================= -/

/--
Steps 3 and 4 map the complete Step-2 reference state exactly to the
post-Step-3/4 reference state.
-/
lemma alg1_step34_reference_exact
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    qs.eval (ModMulConfig.U34 (Basis := qs.Basis) cfg)
        tr.afterStep2Ref
      =
    tr.afterStep34Ref := by
  exact alg1_step34_reference_exact_core qs cfg ψ tr
