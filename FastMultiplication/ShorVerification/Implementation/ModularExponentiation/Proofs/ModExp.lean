import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.FinalModMul

open Shor

universe v

/-!
# Modular-Exponentiation Approximation Bound

Focus theorem: `modExpApprox_valid_dist_uniform`.

This file lifts the uniform modular-multiplication estimate through the
recursive sequence of controlled multiplications used by modular
exponentiation. Each recursive step contributes one `stepErr K η` term, so the
total error is proportional to the number of exponent-control bits.
-/

/-! =========================================================
    Section 1: Tail side conditions and reindexing

    Layout and arithmetic well-formedness for a control-qubit tail, and the
    lemmas that peel the head control off both conditions.
========================================================= -/

/--
Layout condition required by every controlled modular-multiplication step in a
tail of exponent-control qubits.
-/
def ModExpTailLayout (data work : ExtReg) (flag : ℕ) (ctrls : List ℕ) : Prop :=
  ∀ i : Fin ctrls.length, ModMulCoreLayout data work flag (ctrls.get i)

/--
Arithmetic side condition for a modular-exponentiation tail: the multiplier
used at every remaining exponent position is coprime to `N`.
-/
def ModExpTailArithmeticOK (a N e : ℕ) (ctrls : List ℕ) : Prop :=
  ∀ i : Fin ctrls.length, Nat.Coprime ((a ^ (2 ^ (e + i.1))) % N) N

/-- Removing the head control preserves the layout condition on the tail. -/
lemma modExpTailLayout_tail
    (data work : ExtReg) (flag ctrl : ℕ) (ctrls : List ℕ)
    (h : ModExpTailLayout data work flag (ctrl :: ctrls)) :
    ModExpTailLayout data work flag ctrls := by
  intro i
  let j : Fin (ctrl :: ctrls).length := ⟨i.1 + 1, by simp⟩
  have h' := h j
  simpa [ModExpTailLayout, j, List.get_cons_succ] using h'

/--
Removing the head control and incrementing the exponent offset preserves the
tail arithmetic condition.
-/
lemma modExpTailArithmeticOK_tail
    (a N e ctrl : ℕ) (ctrls : List ℕ)
    (h : ModExpTailArithmeticOK a N e (ctrl :: ctrls)) :
    ModExpTailArithmeticOK a N (e + 1) ctrls := by
  intro i
  let j : Fin (ctrl :: ctrls).length := ⟨i.1 + 1, by simp⟩
  have h' := h j
  have hexp : e + (i.1 + 1) = e + 1 + i.1 := by
    omega
  simpa [ModExpTailArithmeticOK, j, hexp] using h'

/-! =========================================================
    Section 2: Preservation by ideal modular multiplication

    The ideal controlled multiplier keeps a valid state valid — the invariant the
    recursive hybrid argument threads through each step.
========================================================= -/

private theorem ideal_preserves_algorithm1_good_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodAlgorithm1BasisInput
        qs cfg.env.N cfg.env.data cfg.env.work
          cfg.env.scratch cfg.flag b) :
    ∃ b' : qs.Basis,
      qs.eval (ModMulConfig.idealGate cfg) (qs.ket b) = qs.ket b' ∧
      GoodAlgorithm1BasisInput
        qs cfg.env.N cfg.env.data cfg.env.work
          cfg.env.scratch cfg.flag b' := by
  classical

  have hbmod :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b :=
    hb.1

  have hscratch_zero :
      RegEncoding.toNat cfg.env.scratch.active b = 0 :=
    hb.2.1

  have hscratch_fresh :
      cfg.env.scratch.FreshFor 1 b :=
    hb.2.2

  let out : ℕ :=
    if RegEncoding.bit cfg.ctrl b then
      (cfg.c * RegEncoding.toNat cfg.env.data.active b) % cfg.env.N
    else
      RegEncoding.toNat cfg.env.data.active b

  let b' : qs.Basis :=
    RegEncoding.writeNat cfg.env.data.active out b

  have hNpos : 0 < cfg.env.N :=
    Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

  have hctrl_data :
      cfg.ctrl ∉ cfg.env.data.active.qubits := by
    intro hctrl
    exact cfg.layout.2.2.2.1
      (List.mem_append_left _ hctrl)

  have hout_lt_N : out < cfg.env.N := by
    by_cases hctrl : RegEncoding.bit cfg.ctrl b
    · simpa [out, hctrl] using
        Nat.mod_lt
          (cfg.c * RegEncoding.toNat cfg.env.data.active b)
          hNpos
    · simpa [out, hctrl] using hbmod.1

  have hout_lt_cap :
      out < ASize cfg.env.data.active :=
    lt_of_lt_of_le hout_lt_N cfg.env.data_capacity

  have hdata_out :
      RegEncoding.toNat cfg.env.data.active b' = out := by
    dsimp [b']
    exact
      RegEncoding.toNat_writeNat_of_lt
        cfg.env.data.active out b hout_lt_cap

  have hdataFresh_out :
      cfg.env.data.FreshFor 2 b' := by
    dsimp [b']
    exact
      ExtReg.freshFor_write_active
        cfg.env.data 2 out b hbmod.2.1

  have howned :
      ∀ q,
        q ∈ cfg.env.data.ownedQubits →
        q ∈ cfg.env.work.ownedQubits →
        False := by
    have h := cfg.layout.1
    rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h
    exact h

  have hwork_data :
      Disjoint cfg.env.work.active cfg.env.data.active := by
    rw [Shor.Disjoint, List.disjoint_left]
    intro q hqWork hqData
    exact howned q
      (List.mem_append_left _ hqData)
      (List.mem_append_left _ hqWork)

  have hworkNew_data :
      Disjoint (cfg.env.work.newBits 1) cfg.env.data.active := by
    rw [Shor.Disjoint, List.disjoint_left]
    intro q hqNew hqData
    exact howned q
      (List.mem_append_left _ hqData)
      (List.mem_append_right _
        (List.mem_of_mem_take hqNew))

  have hflag_data :
      Disjoint (qubitReg cfg.flag) cfg.env.data.active := by
    rw [Shor.Disjoint, List.disjoint_left]
    intro q hqFlag hqData
    have hq : q = cfg.flag := by
      simpa [qubitReg, Reg.singleton] using hqFlag
    subst q
    exact cfg.layout.2.1
      (List.mem_append_left _ hqData)

  have hwork_out :
      RegEncoding.toNat cfg.env.work.active b' = 0 := by
    calc
      RegEncoding.toNat cfg.env.work.active b'
          =
        RegEncoding.toNat cfg.env.work.active b := by
          dsimp [b']
          exact
            RegEncoding.toNat_left_write_right
              cfg.env.work.active
              cfg.env.data.active
              hwork_data
              b
              out
      _ = 0 := hbmod.2.2.1

  have hworkFresh_out :
      cfg.env.work.FreshFor 1 b' := by
    calc
      RegEncoding.toNat (cfg.env.work.newBits 1) b'
          =
      RegEncoding.toNat (cfg.env.work.newBits 1) b := by
        dsimp [b']
        exact
          RegEncoding.toNat_left_write_right
            (cfg.env.work.newBits 1)
            cfg.env.data.active
            hworkNew_data
            b
            out
      _ = 0 := by
        simpa [ExtReg.FreshFor, FreshZero] using hbmod.2.2.2.1

  have hflag_out :
      RegEncoding.toNat (qubitReg cfg.flag) b' = 0 := by
    calc
      RegEncoding.toNat (qubitReg cfg.flag) b'
          =
        RegEncoding.toNat (qubitReg cfg.flag) b := by
          dsimp [b']
          exact
            RegEncoding.toNat_left_write_right
              (qubitReg cfg.flag)
              cfg.env.data.active
              hflag_data
              b
              out
      _ = 0 := hbmod.2.2.2.2

  have hdataScratch :
      ExtReg.OwnedDisjoint
        cfg.env.data cfg.env.scratch := by
    have h :=
      cfg.step4_workspace.data_scratch_disjoint
    rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h ⊢
    intro q hqData hqScratch
    exact h
      (by
        simpa [Gate.ExtReg.ownedQubits_grow] using hqData)
      hqScratch

  have hscratch_data :
      Disjoint cfg.env.scratch.active cfg.env.data.active := by
    have h := hdataScratch
    rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h
    rw [Shor.Disjoint, List.disjoint_left]
    intro q hqScratch hqData
    exact h
      (List.mem_append_left _ hqData)
      (List.mem_append_left _ hqScratch)

  have hscratchNew_data :
      Disjoint
        (cfg.env.scratch.newBits 1)
        cfg.env.data.active := by
    have h := hdataScratch
    rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h
    rw [Shor.Disjoint, List.disjoint_left]
    intro q hqNew hqData
    exact h
      (List.mem_append_left _ hqData)
      (List.mem_append_right _
        (List.mem_of_mem_take hqNew))

  have hscratch_zero_out :
      RegEncoding.toNat cfg.env.scratch.active b' = 0 := by
    calc
      RegEncoding.toNat cfg.env.scratch.active b'
          =
        RegEncoding.toNat cfg.env.scratch.active b := by
          dsimp [b']
          exact
            RegEncoding.toNat_left_write_right
              cfg.env.scratch.active
              cfg.env.data.active
              hscratch_data
              b
              out
      _ = 0 := hscratch_zero

  have hscratch_fresh_out :
      cfg.env.scratch.FreshFor 1 b' := by
    unfold ExtReg.FreshFor FreshZero at hscratch_fresh ⊢
    calc
      RegEncoding.toNat (cfg.env.scratch.newBits 1) b'
          =
        RegEncoding.toNat (cfg.env.scratch.newBits 1) b := by
          dsimp [b']
          exact
            RegEncoding.toNat_left_write_right
              (cfg.env.scratch.newBits 1)
              cfg.env.data.active
              hscratchNew_data
              b
              out
      _ = 0 := hscratch_fresh

  have hgood_out :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b' := by
    refine
      ⟨?_,
       hdataFresh_out,
       hwork_out,
       hworkFresh_out,
       hflag_out⟩
    rw [hdata_out]
    exact hout_lt_N

  have heval :
      qs.eval (ModMulConfig.idealGate cfg) (qs.ket b)
        =
      qs.ket b' := by
    simpa [ModMulConfig.idealGate, b', out] using
      (IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact
        (qs := qs)
        cfg.c
        cfg.env.N
        cfg.env.data.active
        cfg.ctrl
        b
        cfg.env.modulus_gt_one
        cfg.env.data_capacity
        cfg.coprime
        hctrl_data
        hbmod.1)

  exact
    ⟨b',
     heval,
     hgood_out,
     hscratch_zero_out,
     hscratch_fresh_out⟩

/--
The ideal controlled multiplication preserves the valid modular-input
subspace described by its configuration.
-/
theorem ideal_preserves_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (hψ : cfg.ValidState qs ψ) :
    cfg.ValidState qs
      (qs.eval (ModMulConfig.idealGate cfg) ψ) := by
  classical

  let validSet : Set qs.State :=
    { ξ : qs.State |
      ∃ b : qs.Basis,
        GoodAlgorithm1BasisInput
          qs cfg.env.N cfg.env.data cfg.env.work
            cfg.env.scratch cfg.flag b ∧
        ξ = qs.ket b }

  change ψ ∈ Submodule.span ℂ validSet at hψ

  change
    qs.eval (ModMulConfig.idealGate cfg) ψ
      ∈ Submodule.span ℂ validSet

  refine
    Submodule.span_induction
      (s := validSet)
      (p := fun ξ _ =>
        qs.eval (ModMulConfig.idealGate cfg) ξ
          ∈ Submodule.span ℂ validSet)
      ?basis
      ?zero
      ?add
      ?smul
      hψ

  case basis =>
    intro ξ hξ
    change
      ∃ b : qs.Basis,
        GoodAlgorithm1BasisInput
          qs cfg.env.N cfg.env.data cfg.env.work
            cfg.env.scratch cfg.flag b ∧
        ξ = qs.ket b
      at hξ
    rcases hξ with ⟨b, hb, rfl⟩
    obtain ⟨b', heval, hgood⟩ :=
      ideal_preserves_algorithm1_good_ket
        qs cfg b hb
    rw [heval]
    exact
      Submodule.subset_span
        (show qs.ket b' ∈ validSet from
          ⟨b', hgood, rfl⟩)

  case zero =>
    simp [qs.eval_zero]

  case add =>
    intro ξ ζ _ _ hξ hζ
    rw [qs.eval_add]
    exact (Submodule.span ℂ validSet).add_mem hξ hζ

  case smul =>
    intro a ξ _ hξ
    rw [qs.eval_smul]
    exact (Submodule.span ℂ validSet).smul_mem a hξ

/-! =========================================================
    Section 3: Uniform recursive-tail hybrid bound

    Induction over the control list: the approximate step-list stays within
    `ctrls.length · stepErr` of the ideal step-list, uniformly.
========================================================= -/

/--
Uniform hybrid bound for a tail of modular exponentiation.

A tail with `ctrls.length` controlled multiplications differs from its ideal
counterpart by at most `ctrls.length * stepErr K η`. The proof inducts over the
controls and uses ideal-state preservation to apply the induction hypothesis.
-/
theorem modExpApproxSteps_valid_dist_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (η : ℝ)
        (a N : ℕ) (data work scratch : ExtReg) (flag : ℕ)
        (hworkspace : ModMulCircuitWorkspaceOK data work)
        (hstep4 :
          CmpLtNWWorkspace N (data.grow 1) work scratch flag)
        (e : ℕ) (ctrls : List ℕ) (ψ : qs.State),
        1 < N →
        N ≤ ASize data.active →
        Algorithm1Precision η data.active work.active →
        ModExpTailLayout data work flag ctrls →
        ModExpTailArithmeticOK a N e ctrls →
        ψ ∈ ValidAlgorithm1State qs N data work scratch flag →
        ‖ψ‖ = 1 →
        ‖qs.eval
            (modExpApproxStepsValid
              (Basis := qs.Basis)
              a N data work scratch flag
              hworkspace hstep4 e ctrls) ψ -
          qs.eval
            (modExpIdealSteps qs a N data.active e ctrls) ψ‖
          ≤ (ctrls.length : ℝ) * stepErr K η := by
  -- Reuse one uniform constant for every controlled multiplication.
  rcases modMul_approx_valid_dist_uniform (qs := qs) with
    ⟨K, hK_nonneg, hmodMul⟩

  refine ⟨K, hK_nonneg, ?_⟩
  intro η a N data work scratch flag hworkspace hstep4 e ctrls ψ
    hN hsize hprecision hLayout hArithmetic hValid hNorm

  revert e ψ hLayout hArithmetic hValid hNorm

  -- Induct over the remaining exponent-control qubits.
  induction ctrls with
  | nil =>
      intro e ψ hLayout hArithmetic hValid hNorm
      simp [modExpApproxStepsValid, modExpIdealSteps, qs.eval_id]

  | cons ctrl ctrls ih =>
      intro e ψ hLayout hArithmetic hValid hNorm

      -- Remove the head control from the layout and arithmetic conditions.
      have hTailLayout : ModExpTailLayout data work flag ctrls :=
        modExpTailLayout_tail data work flag ctrl ctrls hLayout

      have hTailArithmetic : ModExpTailArithmeticOK a N (e + 1) ctrls :=
        modExpTailArithmeticOK_tail a N e ctrl ctrls hArithmetic

      -- Multiplier implemented by the current head control.
      let c : ℕ := (a ^ (2 ^ e)) % N

      have hHeadLayout : ModMulCoreLayout data work flag ctrl := by
        have h0 := hLayout ⟨0, by simp⟩
        simpa [ModExpTailLayout] using h0

      have hHeadArithmetic : Nat.Coprime c N := by
        have h0 := hArithmetic ⟨0, by simp⟩
        simpa [ModExpTailArithmeticOK, c] using h0

      -- Package the head step as a modular-multiplication configuration.
      let headEnv : Algorithm1Env η :=
        { N := N
          data := data
          work := work
          scratch := scratch
          modulus_gt_one := hN
          data_capacity := hsize
          precision := hprecision
          circuit_workspace := hworkspace }

      let headCfg : ModMulConfig η :=
        { env := headEnv
          c := c
          flag := flag
          ctrl := ctrl
          coprime := hHeadArithmetic
          layout := hHeadLayout
          step4_workspace := hstep4 }

      -- Approximate/ideal head gates and approximate/ideal recursive tails.
      let A : Gate := CmodMulInPlaceCore (Basis := qs.Basis)
          c N ctrl data work scratch flag hworkspace hstep4
      let I : Gate := Gate.idealCtrlModMul c N data.active ctrl
      let RA : Gate := modExpApproxStepsValid (Basis := qs.Basis)
          a N data work scratch flag hworkspace hstep4 (e + 1) ctrls
      let RI : Gate := modExpIdealSteps qs a N data.active (e + 1) ctrls

      have hApprox :
          modExpApproxStepsValid
            (Basis := qs.Basis)
            a N data work scratch flag
            hworkspace hstep4 e (ctrl :: ctrls)
            =
          A ;; RA := by
        simp [modExpApproxStepsValid, A, RA, c]

      have hIdeal :
          modExpIdealSteps qs a N data.active e (ctrl :: ctrls) = I ;; RI := by
        simp [modExpIdealSteps, I, RI, c]

      let ψA0 : qs.State := qs.eval A ψ
      let ψI0 : qs.State := qs.eval I ψ

      have hHeadValid : ModMulConfig.ValidState qs headCfg ψ := by
        simpa [ModMulConfig.ValidState, headCfg, headEnv] using hValid
      have hHeadUnit : ModMulConfig.ValidUnitState qs headCfg ψ :=
        ⟨hHeadValid, hNorm⟩

      -- Apply the one-step modular-multiplication estimate.
      have hHead : ‖ψA0 - ψI0‖ ≤ stepErr K η := by
        simpa [ψA0, ψI0, A, I, ModMulConfig.approxGate,
          ModMulConfig.idealGate, headCfg, headEnv] using
          (hmodMul η headCfg ψ hHeadUnit)

      have hψI0Norm : ‖ψI0‖ = 1 := by
        calc
          ‖ψI0‖ = ‖ψ‖ := by
            simpa [ψI0] using (eval_norm_preserved qs I ψ)
          _ = 1 := hNorm

      have hψI0ValidCfg : ModMulConfig.ValidState qs headCfg ψI0 := by
        simpa [ψI0, I, ModMulConfig.idealGate, headCfg, headEnv] using
          (ideal_preserves_valid qs headCfg ψ hHeadValid)

      have hψI0Valid :
          ψI0 ∈ ValidAlgorithm1State qs N data work scratch flag := by
        simpa [ModMulConfig.ValidState, headCfg, headEnv] using hψI0ValidCfg

      -- Apply the induction hypothesis to the ideal head output.
      have hTail :
          ‖qs.eval RA ψI0 - qs.eval RI ψI0‖
            ≤ (ctrls.length : ℝ) * stepErr K η := by
        have h :=
          ih
            (e := e + 1)
            (ψ := ψI0)
            hTailLayout
            hTailArithmetic
            hψI0Valid
            hψI0Norm
        simpa [RA, RI] using h

      have hIso :
          ‖qs.eval RA ψA0 - qs.eval RA ψI0‖ = ‖ψA0 - ψI0‖ := by
        exact eval_isometry qs RA
          (by
            intro φ χ
            simpa using qs.inner_preserved RA φ χ)
          ψA0 ψI0

      -- Insert `RA ψI0` as the intermediate state for the hybrid bound.
      have hTriangle :
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
            ≤ ‖qs.eval RA ψA0 - qs.eval RA ψI0‖ +
              ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
        rw [
          show qs.eval RA ψA0 - qs.eval RI ψI0 =
            (qs.eval RA ψA0 - qs.eval RA ψI0) +
            (qs.eval RA ψI0 - qs.eval RI ψI0) by abel
        ]
        exact norm_add_le _ _

      have hMain :
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
            ≤ ((ctrls.length + 1 : ℕ) : ℝ) * stepErr K η := by
        calc
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
              ≤ ‖qs.eval RA ψA0 - qs.eval RA ψI0‖ +
                ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := hTriangle
          _ = ‖ψA0 - ψI0‖ +
              ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
            rw [hIso]
          _ ≤ stepErr K η + (ctrls.length : ℝ) * stepErr K η := by
            exact add_le_add hHead hTail
          _ = ((ctrls.length + 1 : ℕ) : ℝ) * stepErr K η := by
            push_cast
            ring

      simpa [hApprox, hIdeal, ψA0, ψI0, qs.eval_seq] using hMain

/-! =========================================================
    Section 4: Full modular-exponentiation bound

    The public end-to-end bound for the whole modular-exponentiation circuit,
    obtained by instantiating the recursive tail bound at the full register.
========================================================= -/

/--
Uniform approximation theorem for complete modular exponentiation.

The recursive tail theorem is instantiated with all qubits of the exponent
register, producing the final factor `tbits cfg.x`.
-/
theorem modExpApprox_valid_dist_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]:
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State),
        ModExpConfig.ValidUnitState qs cfg ψ →
        ‖qs.eval (ModExpConfig.approxGate (Basis := qs.Basis) cfg) ψ -
          qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
          ≤ (tbits cfg.x : ℝ) * stepErr K η := by
  rcases modExpApproxSteps_valid_dist_uniform (qs := qs) with
    ⟨K, hK_nonneg, hSteps⟩

  refine ⟨K, hK_nonneg, ?_⟩
  intro η cfg ψ hψ
  rcases hψ with ⟨hValid, hNorm⟩

  -- Reindex the public layout hypothesis over the exponent-qubit list.
  have hTailLayout :
      ModExpTailLayout cfg.env.data cfg.env.work cfg.flag cfg.x.qubits := by
    intro i
    let j : Fin (regSize cfg.x) :=
      ⟨i.1, by simp [regSize, Reg.width]⟩
    simpa [ModExpTailLayout, ModExpLayout, Reg.get, regSize, Reg.width, j]
      using cfg.layout j

  -- Reindex the public arithmetic hypothesis in the same way.
  have hTailArithmetic :
      ModExpTailArithmeticOK cfg.a cfg.env.N 0 cfg.x.qubits := by
    intro i
    let j : Fin (regSize cfg.x) :=
      ⟨i.1, by simp [regSize, Reg.width]⟩
    have h0 : 0 + i.1 = j.1 := by
      simp [j]
    simpa [ModExpTailArithmeticOK, ModExpArithmeticOK, regSize, Reg.width, j, h0]
      using cfg.arithmetic j

  have h := hSteps η cfg.a cfg.env.N cfg.env.data cfg.env.work cfg.env.scratch cfg.flag
    cfg.env.circuit_workspace cfg.step4_workspace 0 cfg.x.qubits ψ cfg.env.modulus_gt_one
    cfg.env.data_capacity cfg.env.precision hTailLayout hTailArithmetic
    hValid hNorm

  simpa [ModExpConfig.approxGate, ModExpConfig.idealGate, modExpApproxValid,
    modExpIdeal', tbits, regSize, Reg.width] using h
