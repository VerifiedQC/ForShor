import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModMulBounds.FinalModMul

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

/-! ## Tail Side Conditions and Reindexing -/

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

/-! ## Preservation by Ideal Modular Multiplication -/

/--
The ideal controlled multiplication preserves the valid modular-input
subspace described by its configuration.
-/
theorem ideal_preserves_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (hψ : cfg.ValidState qs ψ) :
    cfg.ValidState qs (qs.eval (ModMulConfig.idealGate cfg) ψ) := by
  simpa [ModMulConfig.ValidState, ModMulConfig.idealGate] using
    (idealCtrlModMul_preserves_valid qs cfg.c cfg.env.N cfg.env.data cfg.env.work
      cfg.flag cfg.ctrl cfg.env.modulus_gt_one cfg.env.data_capacity cfg.coprime
      cfg.layout ψ hψ)

/-! ## Uniform Recursive-Tail Hybrid Bound -/

/--
Uniform hybrid bound for a tail of modular exponentiation.

A tail with `ctrls.length` controlled multiplications differs from its ideal
counterpart by at most `ctrls.length * stepErr K η`. The proof inducts over the
controls and uses ideal-state preservation to apply the induction hypothesis.
-/
theorem modExpApproxSteps_valid_dist_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    [ModMulPrimitiveSemantics qs] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (η : ℝ)
        (a N : ℕ) (data work : ExtReg) (flag : ℕ)
        (hworkspace : ModMulCircuitWorkspaceOK data work)
        (e : ℕ) (ctrls : List ℕ) (ψ : qs.State),
        1 < N →
        N ≤ ASize data.active →
        Algorithm1Precision η data.active work.active →
        ModExpTailLayout data work flag ctrls →
        ModExpTailArithmeticOK a N e ctrls →
        ψ ∈ ValidModMulState qs N data work flag →
        ‖ψ‖ = 1 →
        ‖qs.eval
            (modExpApproxStepsValid (Basis := qs.Basis)
              a N data work flag hworkspace e ctrls) ψ -
          qs.eval (modExpIdealSteps qs a N data.active e ctrls) ψ‖
          ≤ (ctrls.length : ℝ) * stepErr K η := by
  -- Reuse one uniform constant for every controlled multiplication.
  rcases modMul_approx_valid_dist_uniform (qs := qs) with
    ⟨K, hK_nonneg, hmodMul⟩

  refine ⟨K, hK_nonneg, ?_⟩
  intro η a N data work flag hworkspace e ctrls ψ
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
          layout := hHeadLayout }

      -- Approximate/ideal head gates and approximate/ideal recursive tails.
      let A : Gate := CmodMulInPlaceCore (Basis := qs.Basis)
        c N ctrl data work flag hworkspace
      let I : Gate := Spec.idealCtrlModMul c N data.active ctrl
      let RA : Gate := modExpApproxStepsValid (Basis := qs.Basis)
        a N data work flag hworkspace (e + 1) ctrls
      let RI : Gate := modExpIdealSteps qs a N data.active (e + 1) ctrls

      have hApprox :
          modExpApproxStepsValid (Basis := qs.Basis)
            a N data work flag hworkspace e (ctrl :: ctrls) = A ;; RA := by
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

      have hψI0Valid : ψI0 ∈ ValidModMulState qs N data work flag := by
        simpa [ModMulConfig.ValidState, headCfg, headEnv] using hψI0ValidCfg

      -- Apply the induction hypothesis to the ideal head output.
      have hTail :
          ‖qs.eval RA ψI0 - qs.eval RI ψI0‖
            ≤ (ctrls.length : ℝ) * stepErr K η := by
        have h := ih (e := e + 1) (ψ := ψI0) hTailLayout hTailArithmetic
          hψI0Valid hψI0Norm
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

/-! ## Full Modular-Exponentiation Bound -/

/--
Uniform approximation theorem for complete modular exponentiation.

The recursive tail theorem is instantiated with all qubits of the exponent
register, producing the final factor `tbits cfg.x`.
-/
theorem modExpApprox_valid_dist_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    [ModMulPrimitiveSemantics qs] :
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

  have h := hSteps η cfg.a cfg.env.N cfg.env.data cfg.env.work cfg.flag
    cfg.env.circuit_workspace 0 cfg.x.qubits ψ cfg.env.modulus_gt_one
    cfg.env.data_capacity cfg.env.precision hTailLayout hTailArithmetic
    hValid hNorm

  simpa [ModExpConfig.approxGate, ModExpConfig.idealGate, modExpApproxValid,
    modExpIdeal', tbits, regSize, Reg.width] using h
