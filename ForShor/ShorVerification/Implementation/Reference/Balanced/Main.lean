import ForShor.ShorVerification.Implementation.Reference.Balanced.Proofs.Fits

/-!
# Balanced phase products: the implementations

The claims of `Statement.lean`, proved; the order-finding circuit lowered after
each pass; and the two packaged implementations: `balancedShorImplementation`
(the guarded pass, any rule) and `balancedUShorImplementation` (every site split
by the default rule, which the reference layout always fits). Both are the
reference submission with its circuit replaced, so they keep its layout, its
precision, its declared success probability and its trial count. This file is
the way into `Balanced/` from outside.
-/

namespace Shor
namespace Balanced

open Reference

/-! ## The claims, proved -/

section

variable (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]

theorem balanceOK (P : ShorLoweringPolicy) (R : Rule) : BalanceOK P R :=
  fun G hw => balance_ok P R G hw

theorem balanceCorrect (P : ShorLoweringPolicy) (R : Rule) : BalanceCorrect qs P R :=
  fun hP G hw _ ψ hclean => Policy.lowerGate_balance_correctness qs P hP R G hw ψ hclean

theorem balanceUOK (P : ShorLoweringPolicy) (R : Rule) : BalanceUOK P R :=
  fun G hw hf => balanceU_ok P R G hw hf

theorem balanceUCorrect (P : ShorLoweringPolicy) (R : Rule) : BalanceUCorrect qs P R :=
  fun hP G hw hf _ ψ hclean => Policy.lowerGate_balanceU_correctness qs P hP R G hw hf ψ hclean

end

theorem defaultRuleFits (P : ShorLoweringPolicy) : DefaultRuleFits P :=
  fun _ _ hx hz => siteFits_of_siteNeed P hx hz


/-! ## The order-finding circuit after each pass -/

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [GateSemanticsFacts qs]
variable [LowerGateClass qs]

/-- Lowered approximate order finding with balanced phase-product sites. -/
def orderFindingApproxLowBalanced
    (P : ShorLoweringPolicy) (R : Rule)
    (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (hmodWorkspace : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hLowerWorkspace : Policy.GateWorkspaceOK P
      (orderFindingApprox a N x y work scratch flag hmodWorkspace hstep4)) : LowGate :=
  Policy.lowerGate P
    (balance P R (orderFindingApprox a N x y work scratch flag hmodWorkspace hstep4))
    (balance_ok P R _ hLowerWorkspace)

/-- Balancing changes no success probability: the balanced lowering has the
source circuit's success probability. -/
theorem probability_of_success_balance_eq
    (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule)
    (T : ℕ → ℕ) (verify : ℕ → Bool) (x : Reg) (r Q : ℕ)
    (G : Gate) (hworkspace : Policy.GateWorkspaceOK P G) (ψ : qs.State)
    (hclean : Policy.GateWorkspaceCleanState qs P G hworkspace ψ) :
    probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs))
        (T := T) (verify := verify) (x := x) (r := r) (Q := Q)
        (C := Policy.lowerGate P (balance P R G) (balance_ok P R G hworkspace)) (ψ := ψ)
      =
    probability_of_success (qs := qs) (evalC := qs.eval)
        (T := T) (verify := verify) (x := x) (r := r) (Q := Q) (C := G) (ψ := ψ) := by
  have hEval := Policy.lowerGate_balance_correctness qs P hP R G hworkspace ψ hclean
  unfold probability_of_success MeasureClass.probMeas
  apply Finset.sum_congr rfl
  intro o _
  rw [hEval]

/-- **End-to-end Shor correctness with the balanced split**: the statement of
`Shor_correct_approx_lowered_of_modExp_bound`, for the balanced lowering. -/
theorem Shor_correct_approx_lowered_balanced_of_modExp_bound
    (R : Rule)
    (K : ℝ)
    (hmodExp :
      ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State),
        ModExpConfig.ValidUnitState qs cfg ψ →
        ‖qs.eval (ModExpConfig.approxGate cfg) ψ -
            qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
          ≤ (regSize cfg.x : ℝ) * stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    (P : ShorLoweringPolicy)
    (hP : P.Admissible)
    (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N^2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N))
    (η : ℝ)
    (hready : LoweredShorReady
      qs P η inst.a inst.N x y work scratch flag b0) :
    probability_of_success
        (qs := qs) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)
        (evalC := LowerGateClass.evalL (qs := qs))
        (C := orderFindingApproxLowBalanced P R
          inst.a inst.N x y work scratch flag
          hready.toShorApproxSetup.circuit_workspace
          hready.toShorApproxSetup.step4_workspace
          hready.workspace)
        (ψ := qs.ket b0)
      ≥
    κ / Real.log ((Nat.log2 inst.N : ℝ) + 1) -
      2 * (regSize x.active : ℝ) * Real.sqrt (2 * (K * η)) := by
  have h := Shor_correct_approx_lowered_of_modExp_bound (qs := qs) K hmodExp T hT
    inst P hP x y work scratch flag b0 hm hn η hready
  rw [orderFindingApproxLow_probability_eq (qs := qs) P hP T _ inst.a inst.N x y work scratch flag
    _ _ hready.workspace (qs.ket b0) (hready.workspace_clean hP)] at h
  unfold orderFindingApproxLowBalanced
  rw [probability_of_success_balance_eq (qs := qs) P hP R T _ _ _ _ _ hready.workspace (qs.ket b0)
    (hready.workspace_clean hP)]
  exact h

/-- Lowered approximate order finding with every phase-product site split. -/
def orderFindingApproxLowBalancedU (P : ShorLoweringPolicy) (R : Rule)
    (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : Policy.GateWorkspaceOK P (orderFindingApprox a N x y work scratch flag hmod hstep4))
    (hf : Fits P R (orderFindingApprox a N x y work scratch flag hmod hstep4)) : LowGate :=
  Policy.lowerGate P (balanceU R (orderFindingApprox a N x y work scratch flag hmod hstep4))
    (balanceU_ok P R _ hws hf)

/-! ## The reference circuit, balanced -/

/-- The reference circuit, balanced. Same layout as `referenceShorCircuit`. -/
def balancedShorCircuit (P : ShorLoweringPolicy) (R : Rule)
    (inst : ShorOrderFindingInstance) (m : ℕ) : LowGate :=
  let layout := allocateReferenceLayout P inst m
  orderFindingApproxLowBalanced P R
    inst.a inst.N layout.x layout.data layout.work layout.scratch layout.flag
    (reference_modMulCircuitWorkspaceOK P inst m)
    (reference_step4Workspace P inst m)
    (reference_gateWorkspaceOK P inst m)

/-- The balanced reference program at precision level `m`. -/
def balancedProgramAt (P : ShorLoweringPolicy) (R : Rule) (m : ℕ)
    (inst : ShorOrderFindingInstance) : ShorOrderFindingProgram where
  circuit := balancedShorCircuit P R inst m
  output := (allocateReferenceLayout P inst m).x.active

/-- From the framework's initial state the balanced and the reference programs
have the same success probability. -/
theorem balancedProgramAt_prob_eq
    (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule) (m : ℕ)
    (T : ℕ → ℕ) (inst : ShorOrderFindingInstance) :
    probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs)) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (balancedProgramAt P R m inst).output) (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (balancedProgramAt P R m inst).output)
        (C := (balancedProgramAt P R m inst).circuit)
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis)))
      =
    probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs)) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (referenceProgramAt P hP m inst).output) (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (referenceProgramAt P hP m inst).output)
        (C := (referenceProgramAt P hP m inst).circuit)
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  have hclean :
      Policy.GateWorkspaceCleanState qs P
        (orderFindingApprox inst.a inst.N
          (allocateReferenceLayout P inst m).x
          (allocateReferenceLayout P inst m).data
          (allocateReferenceLayout P inst m).work
          (allocateReferenceLayout P inst m).scratch
          (allocateReferenceLayout P inst m).flag
          (reference_modMulCircuitWorkspaceOK P inst m)
          (reference_step4Workspace P inst m))
        (reference_gateWorkspaceOK P inst m)
        (qs.ket (RegEncoding.zero (Basis := qs.Basis))) :=
    (referenceLayout_ready (qs := qs) P inst m).workspace_clean hP
  change probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs)) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (allocateReferenceLayout P inst m).x.active) (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (allocateReferenceLayout P inst m).x.active)
        (C := Policy.lowerGate P (balance P R _) (balance_ok P R _ (reference_gateWorkspaceOK P inst m)))
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) =
      probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs)) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (allocateReferenceLayout P inst m).x.active) (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (allocateReferenceLayout P inst m).x.active)
        (C := Policy.lowerGate P _ (reference_gateWorkspaceOK P inst m))
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis)))
  rw [probability_of_success_balance_eq (qs := qs) P hP R T _ _ _ _ _ _ _ hclean,
    probability_of_success_lowerGate_eq (qs := qs) P hP T _ _ _ _ _ _ _ hclean]

/-- Every fixed-`m` balanced program achieves the reference program's declared bound. -/
theorem balancedProgramAt_success
    (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule) (m : ℕ) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt m inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (balancedProgramAt P R m inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (balancedProgramAt P R m inst).output)
          (C := (balancedProgramAt P R m inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  intro T hT inst
  rw [balancedProgramAt_prob_eq (qs := qs) P hP R m T inst]
  exact referenceProgramAt_success (qs := qs) P hP m T hT inst

/-- The balanced submitted program (precision chosen as the reference does). -/
noncomputable def balancedSubmittedProgram (P : ShorLoweringPolicy) (R : Rule)
    (inst : ShorOrderFindingInstance) : ShorOrderFindingProgram :=
  balancedProgramAt P R (referenceChosenPrecision inst.N) inst

theorem balancedSubmittedProgram_correct (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      0 ≤ referenceSuccessProbability inst.N ∧
      referenceSuccessProbability inst.N ≤ 1 ∧
      referenceSuccessProbability inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (balancedSubmittedProgram P R inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (balancedSubmittedProgram P R inst).output)
          (C := (balancedSubmittedProgram P R inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  intro T hT inst
  obtain ⟨h0, h1, h2⟩ := referenceSubmittedProgram_correct (qs := qs) P hP T hT inst
  refine ⟨h0, h1, ?_⟩
  unfold balancedSubmittedProgram
  rw [balancedProgramAt_prob_eq (qs := qs) P hP R _ T inst]
  exact h2

/-- **ForShor's reference submission with balanced phase products**, packaged
into the framework's `ShorImplementation` contract. -/
noncomputable def balancedShorImplementation (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule) :
    ShorImplementation (qs := qs) where
  program := balancedSubmittedProgram P R
  successProbability := referenceSuccessProbability
  correct := balancedSubmittedProgram_correct (qs := qs) P hP R
  trialCount := referenceTrialCount
  trialCount_correct := by
    intro N _
    apply referenceTrialCount_correct

/-! ## The reference circuit, every site split -/

/-- Every reference layout fits the rule at every site, at every precision. -/
def ReferenceFits (P : ShorLoweringPolicy) (R : Rule) : Prop :=
  ∀ (inst : ShorOrderFindingInstance) (m : ℕ) (h : LayoutOK P inst m), Fits P R h.gate

/-- The default rule's split fits every instance's reference layout. -/
theorem referenceFits_default (P : ShorLoweringPolicy) : ReferenceFits P defaultRule :=
  fun inst m _ => reference_fits P inst m

/-- `ReferenceFits` at one instance and level, on the layout's own workspace facts. -/
theorem ReferenceFits.on {P : ShorLoweringPolicy} {R : Rule} (hfits : ReferenceFits P R)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    Fits P R (orderFindingApprox inst.a inst.N
      (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag
      (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m)) :=
  hfits inst m (reference_layoutOK P inst m)

/-- The reference circuit at precision `m` with every site split. -/
def balancedUShorCircuit (P : ShorLoweringPolicy) (R : Rule) (inst : ShorOrderFindingInstance)
    (m : ℕ)
    (hf : Fits P R (orderFindingApprox inst.a inst.N
      (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag
      (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m))) :
    LowGate :=
  orderFindingApproxLowBalancedU P R inst.a inst.N
    (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
    (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
    (allocateReferenceLayout P inst m).flag
    (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m)
    (reference_gateWorkspaceOK P inst m) hf

/-- The unconditionally balanced reference program at precision `m`. -/
def balancedUProgramAt (P : ShorLoweringPolicy) (R : Rule) (m : ℕ) (inst : ShorOrderFindingInstance)
    (hf : Fits P R (orderFindingApprox inst.a inst.N
      (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag
      (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m))) : ShorOrderFindingProgram where
  circuit := balancedUShorCircuit P R inst m hf
  output := (allocateReferenceLayout P inst m).x.active

/-- The unconditionally balanced submitted program. -/
noncomputable def balancedUSubmittedProgram (P : ShorLoweringPolicy) (R : Rule)
    (hfits : ReferenceFits P R) (inst : ShorOrderFindingInstance) : ShorOrderFindingProgram :=
  balancedUProgramAt P R (referenceChosenPrecision inst.N) inst (hfits.on inst _)

theorem balancedUShorCircuit_eq (P : ShorLoweringPolicy) (R : Rule) (inst : ShorOrderFindingInstance)
    (m : ℕ) (hf : Fits P R (orderFindingApprox inst.a inst.N
      (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag
      (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m))) :
    balancedUShorCircuit P R inst m hf = balancedShorCircuit P R inst m := by
  unfold balancedUShorCircuit orderFindingApproxLowBalancedU balancedShorCircuit
    orderFindingApproxLowBalanced
  exact lowerGate_congr _ (balanceU_eq _ hf) _ _

theorem balancedUSubmittedProgram_eq (P : ShorLoweringPolicy) (R : Rule) (hfits : ReferenceFits P R)
    (inst : ShorOrderFindingInstance) :
    balancedUSubmittedProgram P R hfits inst = balancedSubmittedProgram P R inst := by
  unfold balancedUSubmittedProgram balancedUProgramAt balancedSubmittedProgram balancedProgramAt
  rw [balancedUShorCircuit_eq]

theorem balancedUSubmittedProgram_correct (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule)
    (hfits : ReferenceFits P R) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      0 ≤ referenceSuccessProbability inst.N ∧
      referenceSuccessProbability inst.N ≤ 1 ∧
      referenceSuccessProbability inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (balancedUSubmittedProgram P R hfits inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (balancedUSubmittedProgram P R hfits inst).output)
          (C := (balancedUSubmittedProgram P R hfits inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  intro T hT inst
  rw [balancedUSubmittedProgram_eq]
  exact balancedSubmittedProgram_correct (qs := qs) P hP R T hT inst

/-! ## The packaged implementation -/

/-- **The reference submission with every phase-product site split by the
default rule**, packaged into the framework's `ShorImplementation` contract. -/
noncomputable def balancedUShorImplementation (P : ShorLoweringPolicy) (hP : P.Admissible) :
    ShorImplementation (qs := qs) where
  program := balancedUSubmittedProgram P defaultRule (referenceFits_default P)
  successProbability := referenceSuccessProbability
  correct := balancedUSubmittedProgram_correct (qs := qs) P hP defaultRule (referenceFits_default P)
  trialCount := referenceTrialCount
  trialCount_correct := by
    intro N _
    apply referenceTrialCount_correct

/-! ## The circuit claims, proved -/

section

variable (qs : QSemantics) [RegEncoding qs.Basis] [MeasureClass qs] [GateSemanticsFacts qs]
  [LowerGateClass qs]

theorem balancedShorCorrect (R : Rule) : BalancedShorCorrect qs R := by
  intro T hT
  obtain ⟨K, h0, hK, hunif⟩ := Shor_correct_approx_lowered_uniform (qs := qs) T hT
  refine ⟨K, h0, hK, ?_⟩
  intro inst P hP x y work scratch flag b0 hm hn η hready hb
  have h := hunif inst P hP x y work scratch flag b0 hm hn η hready hready.workspace
  rw [probability_of_success_lowerGate_eq (qs := qs) P hP T _ _ _ _ hready.circuit
    hready.workspace (qs.ket b0) (hready.workspace_clean hP)] at h
  rw [probability_of_success_balance_eq (qs := qs) P hP R T _ _ _ _ hready.circuit
    hready.workspace (qs.ket b0) (hready.workspace_clean hP)]
  exact h

theorem balancedUShorCorrect (R : Rule) : BalancedUShorCorrect qs R := by
  intro T hT
  obtain ⟨K, h0, hK, hbal⟩ := balancedShorCorrect qs R T hT
  refine ⟨K, h0, hK, ?_⟩
  intro inst P hP x y work scratch flag b0 hm hn η hready hf hb
  rw [lowerGate_congr P (balanceU_eq _ hf) hb (balance_ok P R _ hready.workspace)]
  exact hbal inst P hP x y work scratch flag b0 hm hn η hready _

end

end Balanced
end Shor
