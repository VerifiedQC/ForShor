import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.GateCount.Lemmas
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.ExactWidthBound

/-!
# Phase-product gate count under a policy

The gate count of `Policy.lowerSignedPhaseProd P` and `Policy.lowerCSignedPhaseProd P`:
`O(n ^ P.gateExponent)`, which for a policy whose first band is `b` is `O(n ^ log_k (2k - 1))` with
`k = b.table.k`.

Every width at or above `b.threshold` uses `b.table`, so the recurrence above that threshold is
the single-table one. Every width below it is a bounded input, and
`shifted_master_theorem_exact_family` asks for the recurrence step only where the width shrinks,
so the narrower bands enter the bound through its constant alone.
-/

namespace Shor

open Operations Gate

/-! ## Which table a policy picks -/

/-- A table the policy picks is the table of one of its bands. -/
theorem ShorLoweringPolicy.choose_mem {P : ShorLoweringPolicy} {n : ℕ} {T : ToomCookTable}
    (h : P.choose n = some T) : ∃ b ∈ P.bands, b.table = T := by
  unfold ShorLoweringPolicy.choose at h
  rcases hb : P.bands.find? (fun b => decide (b.threshold ≤ n)) with _ | b
  · rw [hb] at h; exact absurd h (by simp)
  · rw [hb] at h
    exact ⟨b, List.mem_of_find?_eq_some hb, by simpa using h⟩

/-- At or above the first band's threshold the policy picks the first band's table. -/
theorem ShorLoweringPolicy.choose_of_head? {P : ShorLoweringPolicy} {b : PolicyBand}
    (hb : P.bands.head? = some b) {n : ℕ} (hn : b.threshold ≤ n) :
    P.choose n = some b.table := by
  unfold ShorLoweringPolicy.choose
  cases hbands : P.bands with
  | nil => rw [hbands] at hb; simp at hb
  | cons a rest =>
      rw [hbands] at hb
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      simp [List.find?, hn]

/-- The first band is a band. -/
theorem ShorLoweringPolicy.mem_of_head? {P : ShorLoweringPolicy} {b : PolicyBand}
    (hb : P.bands.head? = some b) : b ∈ P.bands := by
  cases hbands : P.bands with
  | nil => rw [hbands] at hb; simp at hb
  | cons a rest =>
      rw [hbands] at hb
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      simp

section PolicyGateCount

variable (nm : NegationMethod)
variable (P : ShorLoweringPolicy)

/-- Gate count of the policy-lowered signed phase product, under a negation method. -/
noncomputable def Policy.signedPhaseProductGateCountFor (φ : Angle) (x z : ExtReg) : ℕ :=
  LowGate.gateCount (shorGateCostModelFor nm) (Policy.lowerSignedPhaseProd P φ x z)

/-- Gate count of the policy-lowered controlled signed phase product, under a negation method. -/
noncomputable def Policy.cSignedPhaseProductGateCountFor (ctrl : ℕ) (φ : Angle) (x z : ExtReg) : ℕ :=
  LowGate.gateCount (shorGateCostModelFor nm) (Policy.lowerCSignedPhaseProd P ctrl φ x z)

/-! ## The dispatcher with its lookup resolved -/

/-- The policy lowering is the dispatcher's circuit at any size label and any resolved lookup. -/
theorem Policy.lowerSignedPhaseProd_eq_of (φ : Angle) (x z : ExtReg) (n : ℕ)
    (o : Option ToomCookTable) (ho : P.choose (phaseInputSize x z) = o) :
    Policy.lowerSignedPhaseProd P φ x z = lowerGateRec (Policy.signedPlanOf P φ x z n o ho) := by
  subst ho
  exact Policy.lowerGateRec_signedPlanOf_relabel P φ x z _ _ _ rfl

/-- The controlled twin. -/
theorem Policy.lowerCSignedPhaseProd_eq_of (ctrl : ℕ) (φ : Angle) (x z : ExtReg) (n : ℕ)
    (o : Option ToomCookTable) (ho : P.choose (phaseInputSize x z) = o) :
    Policy.lowerCSignedPhaseProd P ctrl φ x z
      = lowerGateRec (Policy.cSignedPlanOf P ctrl φ x z n o ho) := by
  subst ho
  exact Policy.lowerGateRec_cSignedPlanOf_relabel P ctrl φ x z _ _ _ rfl

/-! ## One node -/

/-- A node where the policy stops is the schoolbook leaf: `5 · wx · wz` gates. -/
theorem Policy.signedPhaseProductGateCountFor_of_stops (φ : Angle) (x z : ExtReg)
    (hws : Policy.WorkspaceOK P x z)
    (hstop : P.Stops (phaseInputSize x z) (fun T => nextSignedWidthBy P.widthRule x z T.ops)) :
    Policy.signedPhaseProductGateCountFor nm P φ x z = 5 * ExtReg.width x * ExtReg.width z := by
  unfold Policy.signedPhaseProductGateCountFor
  rcases ho : P.choose (phaseInputSize x z) with _ | T
  · rw [Policy.lowerSignedPhaseProd_eq_of P φ x z (phaseInputSize x z) none ho, Policy.signedPlanOf]
    exact LowerGateClass.gateCount_Naive_SignedPhaseProd (shorGateCostModelFor nm) φ x z
      hws.owned_disjoint
  · have hno : ¬ nextSignedWidthBy P.widthRule x z T.ops < phaseInputSize x z := hstop T ho
    rw [Policy.lowerSignedPhaseProd_eq_of P φ x z (phaseInputSize x z) (some T) ho,
      Policy.signedPlanOf]
    simp only [hno, ↓reduceDIte]
    exact LowerGateClass.gateCount_Naive_SignedPhaseProd (shorGateCostModelFor nm) φ x z
      hws.owned_disjoint

/-- A node where the policy picks `T` and `T` shrinks the width costs the allocation and
arithmetic of one `T`-level plus its `phaseProductCount T.ops` children. -/
theorem Policy.signedPhaseProductGateCountFor_node_le (φ : Angle) (x z : ExtReg)
    (T : ToomCookTable) (ho : P.choose (phaseInputSize x z) = some T)
    (hrec : nextSignedWidthBy P.widthRule x z T.ops < phaseInputSize x z)
    (hws : Policy.WorkspaceOK P x z) (R : ℝ)
    (hchildren : ∀ (ψ : Angle) (a b : ExtReg), Policy.WorkspaceOK P a b →
      ExtReg.width a = nextSignedWidthBy P.widthRule x z T.ops →
      ExtReg.width b = nextSignedWidthBy P.widthRule x z T.ops →
      (Policy.signedPhaseProductGateCountFor nm P ψ a b : ℝ) ≤ R) :
    (Policy.signedPhaseProductGateCountFor nm P φ x z : ℝ)
      ≤ ((4 * T.k * nextSignedWidthBy P.widthRule x z T.ops : ℕ) : ℝ)
        + (phaseProgramOverheadFor nm (nextSignedWidthBy P.widthRule x z T.ops) T.ops : ℝ)
        + (phaseProductCount T.ops : ℝ) * R := by
  let step : Gate.PhaseProductLayout x z T.k := Policy.canonicalStep P T x z
  have hspec : Policy.StepSpec P T x z step := Policy.canonicalStep_spec ho hrec hws
  let src : LayoutState T.k := initSignedLayoutState step
  let dst : LayoutState T.k :=
    targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
  have hxw : ∀ i : Fin T.k,
      ExtReg.width (dst.xslot i) = nextSignedWidthBy P.widthRule x z T.ops := fun i =>
    targetSignedLayoutState_xslot_width_by P.widthRule step T.ops i hspec.capacity
  have hzw : ∀ i : Fin T.k,
      ExtReg.width (dst.zslot i) = nextSignedWidthBy P.widthRule x z T.ops := fun i =>
    targetSignedLayoutState_zslot_width_by P.widthRule step T.ops i hspec.capacity
  have childWorkspace : ∀ i : Fin T.k, Policy.WorkspaceOK P (dst.xslot i) (dst.zslot i) :=
    hspec.childWorkspace
  have hR : 0 ≤ R := by
    have hi : (0 : ℕ) < T.k := by have := T.hk; omega
    exact le_trans (by positivity)
      (hchildren φ (dst.xslot ⟨0, hi⟩) (dst.zslot ⟨0, hi⟩) (childWorkspace ⟨0, hi⟩)
        (hxw ⟨0, hi⟩) (hzw ⟨0, hi⟩))
  let recurse : ∀ (i : Fin T.k) (theta : Angle),
      PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
        (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i)) := fun i theta =>
    Policy.signedPlanOf P theta (dst.xslot i) (dst.zslot i)
      (nextSignedWidthBy P.widthRule x z T.ops) _ rfl
  have hchild : ∀ (ψ : Angle) (i : Fin T.k),
      (LowGate.gateCount (shorGateCostModelFor nm) (lowerGateRec (recurse i ψ)) : ℝ) ≤ R := by
    intro ψ i
    have h := hchildren ψ (dst.xslot i) (dst.zslot i) (childWorkspace i) (hxw i) (hzw i)
    unfold Policy.signedPhaseProductGateCountFor at h
    rw [Policy.lowerSignedPhaseProd_eq_of P ψ (dst.xslot i) (dst.zslot i)
      (nextSignedWidthBy P.widthRule x z T.ops) _ rfl] at h
    exact h
  have halloc :
      LowGate.gateCount (shorGateCostModelFor nm)
          (lowerGateRec (planCompileSignedAllocations (P := P)
            (nextSignedWidthBy P.widthRule x z T.ops) src dst))
        ≤ 2 * T.k * nextSignedWidthBy P.widthRule x z T.ops := by
    apply lgc_allocs_le (P := P) (W := nextSignedWidthBy P.widthRule x z T.ops)
    · intro i; exact le_of_eq (hxw i)
    · intro i; exact le_of_eq (hzw i)
  have hdealloc :
      LowGate.gateCount (shorGateCostModelFor nm)
          (lowerGateRec (planCompileSignedDeallocations (P := P)
            (nextSignedWidthBy P.widthRule x z T.ops) src dst))
        ≤ 2 * T.k * nextSignedWidthBy P.widthRule x z T.ops := by
    apply lgc_deallocs_le (P := P) (W := nextSignedWidthBy P.widthRule x z T.ops)
    · intro i; exact le_of_eq (hxw i)
    · intro i; exact le_of_eq (hzw i)
  have hbody :=
    lgc_body_le nm (P := P) (hk := T.hk) (W := nextSignedWidthBy P.widthRule x z T.ops)
      (st := dst) (coeff := cramerCoeffFromPtsWidth T.k (phaseLimbWidth x z T.k) T.pts T.hpts)
      (φ := φ) (R := R) (hR := hR) (hxw := hxw) (hzw := hzw) (recurse := recurse)
      (hchild := hchild) (n := 0) (l := T.ops)
  have hallocR :
      ((LowGate.gateCount (shorGateCostModelFor nm)
          (lowerGateRec (planCompileSignedAllocations (P := P)
            (nextSignedWidthBy P.widthRule x z T.ops) src dst)) : ℕ) : ℝ)
        ≤ ((2 * T.k * nextSignedWidthBy P.widthRule x z T.ops : ℕ) : ℝ) := by
    exact_mod_cast halloc
  have hdeallocR :
      ((LowGate.gateCount (shorGateCostModelFor nm)
          (lowerGateRec (planCompileSignedDeallocations (P := P)
            (nextSignedWidthBy P.widthRule x z T.ops) src dst)) : ℕ) : ℝ)
        ≤ ((2 * T.k * nextSignedWidthBy P.widthRule x z T.ops : ℕ) : ℝ) := by
    exact_mod_cast hdealloc
  unfold Policy.signedPhaseProductGateCountFor
  rw [Policy.lowerSignedPhaseProd_eq_of P φ x z (phaseInputSize x z) (some T) ho,
    Policy.signedPlanOf]
  simp only [hrec, ↓reduceDIte]
  simp only [PhaseLoweringPlan.lowerGateRec_signedStep]
  unfold Policy.stepPlan
  change
    ((LowGate.gateCount (shorGateCostModelFor nm)
        (lowerGateRec (planCompileSignedAllocations (P := P)
          (nextSignedWidthBy P.widthRule x z T.ops) src dst))
      + (LowGate.gateCount (shorGateCostModelFor nm)
          (lowerGateRec (planCompileAnnotatedOpsToSignedGateAux (P := P) (hk := T.hk)
            (nextSignedWidthBy P.widthRule x z T.ops) φ
            (cramerCoeffFromPtsWidth T.k (phaseLimbWidth x z T.k) T.pts T.hpts) dst recurse
            (annotatePhaseTermsAux T.k 0 T.ops)))
        + LowGate.gateCount (shorGateCostModelFor nm)
          (lowerGateRec (planCompileSignedDeallocations (P := P)
            (nextSignedWidthBy P.widthRule x z T.ops) src dst))) : ℕ) : ℝ)
      ≤ ((4 * T.k * nextSignedWidthBy P.widthRule x z T.ops : ℕ) : ℝ)
        + (phaseProgramOverheadFor nm (nextSignedWidthBy P.widthRule x z T.ops) T.ops : ℝ)
        + (phaseProductCount T.ops : ℝ) * R
  push_cast at hallocR hdeallocR ⊢
  nlinarith [hallocR, hbody, hdeallocR]

/-- The node bound in natural numbers, with one bound `D` on every child. -/
theorem Policy.signedPhaseProductGateCountFor_node_le_nat (φ : Angle) (x z : ExtReg)
    (T : ToomCookTable) (ho : P.choose (phaseInputSize x z) = some T)
    (hrec : nextSignedWidthBy P.widthRule x z T.ops < phaseInputSize x z)
    (hws : Policy.WorkspaceOK P x z) (D : ℕ)
    (hchildren : ∀ (ψ : Angle) (a b : ExtReg), Policy.WorkspaceOK P a b →
      ExtReg.width a = nextSignedWidthBy P.widthRule x z T.ops →
      ExtReg.width b = nextSignedWidthBy P.widthRule x z T.ops →
      Policy.signedPhaseProductGateCountFor nm P ψ a b ≤ D) :
    Policy.signedPhaseProductGateCountFor nm P φ x z
      ≤ 4 * T.k * nextSignedWidthBy P.widthRule x z T.ops
        + phaseProgramOverheadFor nm (nextSignedWidthBy P.widthRule x z T.ops) T.ops
        + phaseProductCount T.ops * D := by
  have h := Policy.signedPhaseProductGateCountFor_node_le nm P φ x z T ho hrec hws (D : ℝ)
    (fun ψ a b hw ha hb => by exact_mod_cast hchildren ψ a b hw ha hb)
  exact_mod_cast h

/-! ## Bounded inputs -/

/-- The cost of one `b`-level at width at most `N` over children costing at most `D`. -/
def Policy.bandLevelCost (N D : ℕ) (b : PolicyBand) : ℕ :=
  4 * b.table.k * N + phaseProgramOverheadFor nm N b.table.ops + phaseProductCount b.table.ops * D

/-- Operands of bounded width cost a bounded number of gates, whatever the bands are. -/
theorem Policy.signedPhaseProductGateCountFor_bounded (N : ℕ) :
    ∃ D : ℕ, ∀ (φ : Angle) (x z : ExtReg), Policy.WorkspaceOK P x z →
      phaseInputSize x z ≤ N → Policy.signedPhaseProductGateCountFor nm P φ x z ≤ D := by
  classical
  have hleaf : ∀ (φ : Angle) (x z : ExtReg), Policy.WorkspaceOK P x z →
      (¬ ∃ T, P.choose (phaseInputSize x z) = some T ∧
        nextSignedWidthBy P.widthRule x z T.ops < phaseInputSize x z) →
      Policy.signedPhaseProductGateCountFor nm P φ x z
        ≤ 5 * phaseInputSize x z * phaseInputSize x z := by
    intro φ x z hws hno
    rw [Policy.signedPhaseProductGateCountFor_of_stops nm P φ x z hws
      (fun T hT hlt => hno ⟨T, hT, hlt⟩)]
    have hx : ExtReg.width x ≤ phaseInputSize x z := le_max_left _ _
    have hz : ExtReg.width z ≤ phaseInputSize x z := le_max_right _ _
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 5 hx) hz
  induction N with
  | zero =>
      refine ⟨0, fun φ x z hws hsize => ?_⟩
      have hno : ¬ ∃ T, P.choose (phaseInputSize x z) = some T ∧
          nextSignedWidthBy P.widthRule x z T.ops < phaseInputSize x z := by
        rintro ⟨T, _, hlt⟩; omega
      have h := hleaf φ x z hws hno
      have h0 : phaseInputSize x z = 0 := by omega
      rw [h0] at h
      simpa using h
  | succ N ih =>
      obtain ⟨D, hD⟩ := ih
      refine ⟨D + 5 * (N + 1) * (N + 1) + (P.bands.map (Policy.bandLevelCost nm N D)).sum,
        fun φ x z hws hsize => ?_⟩
      by_cases hsmall : phaseInputSize x z ≤ N
      · exact (hD φ x z hws hsmall).trans (by omega)
      by_cases hnode : ∃ T, P.choose (phaseInputSize x z) = some T ∧
          nextSignedWidthBy P.widthRule x z T.ops < phaseInputSize x z
      · obtain ⟨T, hT, hrec⟩ := hnode
        obtain ⟨b, hbmem, rfl⟩ := ShorLoweringPolicy.choose_mem hT
        have hW : nextSignedWidthBy P.widthRule x z b.table.ops ≤ N := by omega
        have hnodeBound := Policy.signedPhaseProductGateCountFor_node_le_nat nm P φ x z b.table hT
          hrec hws D (fun ψ a c hw ha hc => hD ψ a c hw (by
            show max (ExtReg.width a) (ExtReg.width c) ≤ N
            rw [ha, hc]; simpa using hW))
        have hmono : 4 * b.table.k * nextSignedWidthBy P.widthRule x z b.table.ops
              + phaseProgramOverheadFor nm (nextSignedWidthBy P.widthRule x z b.table.ops)
                  b.table.ops
              + phaseProductCount b.table.ops * D
            ≤ Policy.bandLevelCost nm N D b := by
          unfold Policy.bandLevelCost
          have h1 := phaseProgramOverheadFor_mono nm b.table.ops hW
          have h2 : 4 * b.table.k * nextSignedWidthBy P.widthRule x z b.table.ops
              ≤ 4 * b.table.k * N := Nat.mul_le_mul_left _ hW
          omega
        have hsum : Policy.bandLevelCost nm N D b
            ≤ (P.bands.map (Policy.bandLevelCost nm N D)).sum :=
          List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hbmem)
        omega
      · have h := hleaf φ x z hws hnode
        have hle : 5 * phaseInputSize x z * phaseInputSize x z ≤ 5 * (N + 1) * (N + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 5 hsize) hsize
        omega

/-! ## The balanced recurrence above the top threshold -/

/-- A signed phase product with operands of equal width and enough workspace under `P`. -/
structure Policy.BalancedInstance where
  φ : Angle
  x : ExtReg
  z : ExtReg
  workspace : Policy.WorkspaceOK P x z
  balanced : ExtReg.width x = ExtReg.width z

/-- Equal-width operands: `O(n ^ log_k (2k - 1))` for the top band's `k`. -/
theorem Policy.signedPhaseProductGateCountFor_balanced_bound (b : PolicyBand)
    (hb : P.bands.head? = some b)
    (hcount : phaseProductCount b.table.ops = q b.table.k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : Angle) (x z : ExtReg), Policy.WorkspaceOK P x z →
      ExtReg.width x = ExtReg.width z →
      (Policy.signedPhaseProductGateCountFor nm P φ x z : ℝ)
        ≤ C * Real.rpow (((max 1 (ExtReg.width x) : ℕ)) : ℝ) (phaseProductExponent b.table.k) := by
  classical
  have hk0 : 0 < b.table.k := by have := b.table.hk; omega
  obtain ⟨c, hc⟩ := prog_balanced_nextSignedWidth b.table.k b.table.hk b.table.ops
  obtain ⟨A, B, hAB⟩ := phaseProgramOverheadFor_linear nm b.table.ops
  let size : Policy.BalancedInstance P → ℕ := fun i => ExtReg.width i.x
  let nsw : Policy.BalancedInstance P → ℕ := fun i =>
    nextSignedWidthBy P.widthRule i.x i.z b.table.ops
  let next : Policy.BalancedInstance P → ℕ := fun i =>
    if b.threshold ≤ size i ∧ nsw i < size i then nsw i else size i
  let cost : Policy.BalancedInstance P → ℕ := fun i =>
    Policy.signedPhaseProductGateCountFor nm P i.φ i.x i.z
  have hsize : ∀ i : Policy.BalancedInstance P, phaseInputSize i.x i.z = size i := by
    intro i
    simp [phaseInputSize, size, ← i.balanced]
  have hnsw : ∀ i : Policy.BalancedInstance P,
      nsw i ≤ (size i + b.table.k - 1) / b.table.k + c := fun i =>
    (nextSignedWidthBy_le_scan P.widthRule hk0 i.x i.z b.table.ops).trans (hc i.x i.z i.balanced)
  have hnext : ∀ i : Policy.BalancedInstance P,
      next i ≤ (size i + b.table.k - 1) / b.table.k + (c + b.threshold) := by
    intro i
    have h := hnsw i
    by_cases hcase : b.threshold ≤ size i ∧ nsw i < size i
    · simp only [next, hcase, and_self, ↓reduceIte]; omega
    · simp only [next, hcase, ↓reduceIte]
      by_cases ht : b.threshold ≤ size i
      · have : size i ≤ nsw i := by
          by_contra hlt; exact hcase ⟨ht, by omega⟩
        omega
      · omega
  have hbounded : ∀ N : ℕ, ∃ D : ℕ, ∀ i : Policy.BalancedInstance P, size i ≤ N → cost i ≤ D := by
    intro N
    obtain ⟨D, hD⟩ := Policy.signedPhaseProductGateCountFor_bounded nm P N
    exact ⟨D, fun i hi => hD i.φ i.x i.z i.workspace (by rw [hsize]; exact hi)⟩
  have hstep : ∀ i : Policy.BalancedInstance P, next i < size i → ∀ D : ℕ,
      (∀ j : Policy.BalancedInstance P, size j = next i → cost j ≤ D) →
      cost i ≤ (4 * b.table.k + A) * next i + B + q b.table.k * D := by
    intro i hlt D hD
    by_cases hcase : b.threshold ≤ size i ∧ nsw i < size i
    · have hnexteq : next i = nsw i := by simp only [next, hcase, and_self, ↓reduceIte]
      have ho : P.choose (phaseInputSize i.x i.z) = some b.table :=
        ShorLoweringPolicy.choose_of_head? hb (by rw [hsize]; exact hcase.1)
      have hrec : nextSignedWidthBy P.widthRule i.x i.z b.table.ops < phaseInputSize i.x i.z := by
        rw [hsize]; exact hcase.2
      have h := Policy.signedPhaseProductGateCountFor_node_le_nat nm P i.φ i.x i.z b.table ho hrec
        i.workspace D (fun ψ a c hw ha hc' =>
          hD ⟨ψ, a, c, hw, ha.trans hc'.symm⟩ (by rw [hnexteq]; exact ha))
      rw [hcount] at h
      have hov := hAB (nextSignedWidthBy P.widthRule i.x i.z b.table.ops)
      rw [hnexteq]
      show Policy.signedPhaseProductGateCountFor nm P i.φ i.x i.z
        ≤ (4 * b.table.k + A) * nextSignedWidthBy P.widthRule i.x i.z b.table.ops + B
          + q b.table.k * D
      rw [Nat.add_mul]
      omega
    · simp only [next, hcase, ↓reduceIte] at hlt
      exact absurd hlt (lt_irrefl _)
  obtain ⟨C, hC, hbound⟩ := shifted_master_theorem_exact_family
    (k := b.table.k) (q := q b.table.k) (c := c + b.threshold) (A := 4 * b.table.k + A) (B := B)
    (α := phaseProductExponent b.table.k) b.table.hk
    (one_lt_phaseProductExponent b.table.k b.table.hk)
    (rpow_phaseProductExponent_eq_q b.table.k b.table.hk)
    size next cost hnext hbounded hstep
  exact ⟨C, hC, fun φ x z hws hbal => hbound ⟨φ, x, z, hws, hbal⟩⟩

/-! ## Operands of any widths -/

/-- **The signed phase-product gate count under a policy**: above some width, at most a constant
times `n ^ log_k (2k - 1)`, `n` the wider operand's width and `k` the top band's arity. -/
theorem Policy.signedPhaseProductGateCountFor_bound (b : PolicyBand) (hP : P.Admissible)
    (hb : P.bands.head? = some b) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (φ : Angle) (x z : ExtReg), Policy.WorkspaceOK P x z →
        n₀ ≤ max (ExtReg.width x) (ExtReg.width z) →
        (Policy.signedPhaseProductGateCountFor nm P φ x z : ℝ)
          ≤ C * Real.rpow ((max (ExtReg.width x) (ExtReg.width z) : ℕ) : ℝ)
              (phaseProductExponent b.table.k) := by
  have hk0 : 0 < b.table.k := by have := b.table.hk; omega
  have hq : 0 < q b.table.k := by unfold q; omega
  have hadm := hP b (ShorLoweringPolicy.mem_of_head? hb)
  have hcount : phaseProductCount b.table.ops = q b.table.k := by
    rw [ProgConsumesPts.phaseProductCount_eq (k := b.table.k) hk0 State.start_state b.table.ops
      b.table.pts hadm.2.1.consumes]
    exact b.table.hpts
  obtain ⟨C, hC, hbal⟩ := Policy.signedPhaseProductGateCountFor_balanced_bound nm P b hb hcount
  obtain ⟨A, B, hAB⟩ := phaseProgramOverheadFor_linear nm b.table.ops
  obtain ⟨d, hd⟩ := prog_no_recurse_implies_small_operand b.table.k b.table.hk b.table.ops
  have hα : 1 < phaseProductExponent b.table.k :=
    one_lt_phaseProductExponent b.table.k b.table.hk
  have hα0 : 0 ≤ phaseProductExponent b.table.k := le_of_lt (lt_trans zero_lt_one hα)
  have hqC : 0 < (q b.table.k : ℝ) * C := mul_pos (by exact_mod_cast hq) hC
  refine ⟨((4 * b.table.k + A + B : ℕ) : ℝ) + (q b.table.k : ℝ) * C + 5 * (d : ℝ),
    by positivity, max 1 b.threshold, le_max_left _ _, ?_⟩
  intro φ x z hws hn
  obtain ⟨n, hn_def⟩ : ∃ n, n = max (ExtReg.width x) (ExtReg.width z) := ⟨_, rfl⟩
  rw [← hn_def] at hn ⊢
  have hsize : phaseInputSize x z = n := by rw [hn_def]; rfl
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnt : b.threshold ≤ n := le_trans (le_max_right _ _) hn
  have ho : P.choose (phaseInputSize x z) = some b.table :=
    ShorLoweringPolicy.choose_of_head? hb (by rw [hsize]; exact hnt)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hp1 : 1 ≤ Real.rpow (n : ℝ) (phaseProductExponent b.table.k) :=
    Real.one_le_rpow hnR hα0
  have hpn : (n : ℝ) ≤ Real.rpow (n : ℝ) (phaseProductExponent b.table.k) := by
    have h := Real.rpow_le_rpow_of_exponent_le hnR hα.le
    rw [Real.rpow_one] at h
    exact h
  have hmono : ∀ m : ℕ, m ≤ n →
      Real.rpow (((max 1 m : ℕ)) : ℝ) (phaseProductExponent b.table.k)
        ≤ Real.rpow (n : ℝ) (phaseProductExponent b.table.k) := by
    intro m hm
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast (max_le hn1 hm)) hα0
  generalize Real.rpow (n : ℝ) (phaseProductExponent b.table.k) = p at hp1 hpn hmono ⊢
  have hp0 : 0 ≤ p := le_trans zero_le_one hp1
  by_cases hrec : nextSignedWidthBy P.widthRule x z b.table.ops < phaseInputSize x z
  · have hW : nextSignedWidthBy P.widthRule x z b.table.ops ≤ n := by rw [← hsize]; exact hrec.le
    have h := Policy.signedPhaseProductGateCountFor_node_le nm P φ x z b.table ho hrec hws (C * p)
      (fun ψ a c hw ha hc =>
        (hbal ψ a c hw (ha.trans hc.symm)).trans
          (mul_le_mul_of_nonneg_left (hmono _ (by rw [ha]; exact hW)) hC.le))
    rw [hcount] at h
    have hov : (phaseProgramOverheadFor nm (nextSignedWidthBy P.widthRule x z b.table.ops)
          b.table.ops : ℝ)
        ≤ (A : ℝ) * (nextSignedWidthBy P.widthRule x z b.table.ops : ℝ) + B := by
      exact_mod_cast hAB _
    have hWp : (nextSignedWidthBy P.widthRule x z b.table.ops : ℝ) ≤ p :=
      le_trans (by exact_mod_cast hW) hpn
    have t1 : (4 * (b.table.k : ℝ)) * (nextSignedWidthBy P.widthRule x z b.table.ops : ℝ)
        ≤ 4 * (b.table.k : ℝ) * p := mul_le_mul_of_nonneg_left hWp (by positivity)
    have t2 : (A : ℝ) * (nextSignedWidthBy P.widthRule x z b.table.ops : ℝ) ≤ (A : ℝ) * p :=
      mul_le_mul_of_nonneg_left hWp (by positivity)
    have t3 : (B : ℝ) ≤ (B : ℝ) * p := le_mul_of_one_le_right (by positivity) hp1
    have t4 : 0 ≤ 5 * (d : ℝ) * p := by positivity
    push_cast at h ⊢
    nlinarith [h, hov, t1, t2, t3, t4]
  · have hstop : P.Stops (phaseInputSize x z)
        (fun T => nextSignedWidthBy P.widthRule x z T.ops) := by
      intro T hT
      rw [ho] at hT
      cases hT
      exact hrec
    rw [Policy.signedPhaseProductGateCountFor_of_stops nm P φ x z hws hstop]
    have hscan : ¬ nextSignedWidth x z b.table.ops < phaseInputSize x z := fun hlt =>
      hrec (lt_of_le_of_lt (nextSignedWidthBy_le_scan P.widthRule hk0 x z b.table.ops) hlt)
    have hmin := hd x z hscan
    have hxn : ExtReg.width x ≤ n := by rw [hn_def]; exact le_max_left _ _
    have hzn : ExtReg.width z ≤ n := by rw [hn_def]; exact le_max_right _ _
    have hprod : 5 * ExtReg.width x * ExtReg.width z ≤ 5 * d * n := by
      rcases le_total (ExtReg.width x) (ExtReg.width z) with hle | hle
      · rw [min_eq_left hle] at hmin
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 5 hmin) hzn
      · rw [min_eq_right hle] at hmin
        calc 5 * ExtReg.width x * ExtReg.width z = 5 * ExtReg.width z * ExtReg.width x := by ring
          _ ≤ 5 * d * n := Nat.mul_le_mul (Nat.mul_le_mul_left 5 hmin) hxn
    have hprodR : ((5 * ExtReg.width x * ExtReg.width z : ℕ) : ℝ) ≤ 5 * (d : ℝ) * (n : ℝ) := by
      exact_mod_cast hprod
    have e1 : 5 * (d : ℝ) * (n : ℝ) ≤ 5 * (d : ℝ) * p :=
      mul_le_mul_of_nonneg_left hpn (by positivity)
    have e2 : 0 ≤ ((4 * b.table.k + A + B : ℕ) : ℝ) * p := by positivity
    have e3 : 0 ≤ (q b.table.k : ℝ) * C * p := mul_nonneg hqC.le hp0
    nlinarith [hprodR, e1, e2, e3]

/-! ## The controlled product -/

/-- The controlled product costs at most five times the uncontrolled one, node by node. -/
theorem Policy.cSignedPhaseProductGateCountFor_le_five_signed (ctrl : ℕ) (φ : Angle)
    (x z : ExtReg) (hws : Policy.CWorkspaceOK P ctrl x z) :
    Policy.cSignedPhaseProductGateCountFor nm P ctrl φ x z
      ≤ 5 * Policy.signedPhaseProductGateCountFor nm P φ x z := by
  suffices H : ∀ (n : ℕ) (φ : Angle) (x z : ExtReg), phaseInputSize x z = n →
      Policy.CWorkspaceOK P ctrl x z →
      Policy.cSignedPhaseProductGateCountFor nm P ctrl φ x z
        ≤ 5 * Policy.signedPhaseProductGateCountFor nm P φ x z from H _ φ x z rfl hws
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ x z hn hws
    have hleaf :
        LowGate.gateCount (shorGateCostModelFor nm) (LowGate.Naive_CSignedPhaseProd ctrl φ x z)
          ≤ 5 * LowGate.gateCount (shorGateCostModelFor nm) (LowGate.Naive_SignedPhaseProd φ x z) := by
      rw [LowGate.gateCount_Naive_CSignedPhaseProd (shorGateCostModelFor nm) ctrl φ x z
          hws.toWorkspaceOK.owned_disjoint hws.control_disjoint.1 hws.control_disjoint.2,
        LowerGateClass.gateCount_Naive_SignedPhaseProd (shorGateCostModelFor nm) φ x z
          hws.toWorkspaceOK.owned_disjoint]
      nlinarith [Nat.zero_le (ExtReg.width x * ExtReg.width z)]
    unfold Policy.cSignedPhaseProductGateCountFor Policy.signedPhaseProductGateCountFor
    rcases ho : P.choose (phaseInputSize x z) with _ | T
    · rw [Policy.lowerCSignedPhaseProd_eq_of P ctrl φ x z (phaseInputSize x z) none ho,
        Policy.cSignedPlanOf,
        Policy.lowerSignedPhaseProd_eq_of P φ x z (phaseInputSize x z) none ho,
        Policy.signedPlanOf]
      exact hleaf
    · rw [Policy.lowerCSignedPhaseProd_eq_of P ctrl φ x z (phaseInputSize x z) (some T) ho,
        Policy.cSignedPlanOf,
        Policy.lowerSignedPhaseProd_eq_of P φ x z (phaseInputSize x z) (some T) ho,
        Policy.signedPlanOf]
      by_cases hrec : nextSignedWidthBy P.widthRule x z T.ops < phaseInputSize x z
      · let step : Gate.PhaseProductLayout x z T.k := Policy.canonicalStep P T x z
        have hspec : Policy.StepSpec P T x z step :=
          Policy.canonicalStep_spec ho hrec hws.toWorkspaceOK
        let src : LayoutState T.k := initSignedLayoutState step
        let dst : LayoutState T.k :=
          targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
        have hctrlLayout : step.ControlDisjoint ctrl :=
          Gate.PhaseProductLayout.controlDisjoint_of_ctrlDisjoint hspec.valid
            hws.control_disjoint
        have hctrlDst :
            (∀ i, ctrl ∉ (dst.xslot i).ownedQubits) ∧ (∀ i, ctrl ∉ (dst.zslot i).ownedQubits) := by
          simpa [src, dst] using
            controlDisjoint_target step ctrl (neededWidthsBy P.widthRule x z T.ops) hctrlLayout
        have childWorkspace : ∀ i : Fin T.k,
            Policy.CWorkspaceOK P ctrl (dst.xslot i) (dst.zslot i) := fun i =>
          { toWorkspaceOK := hspec.childWorkspace i
            control_disjoint := ⟨hctrlDst.1 i, hctrlDst.2 i⟩ }
        have childSize : ∀ i : Fin T.k,
            phaseInputSize (dst.xslot i) (dst.zslot i)
              = nextSignedWidthBy P.widthRule x z T.ops := hspec.childInputSize
        let recurseC : ∀ (i : Fin T.k) (theta : Angle),
            PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
              (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)) := fun i theta =>
          Policy.cSignedPlanOf P ctrl theta (dst.xslot i) (dst.zslot i)
            (nextSignedWidthBy P.widthRule x z T.ops) _ rfl
        let recurseS : ∀ (i : Fin T.k) (theta : Angle),
            PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
              (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i)) := fun i theta =>
          Policy.signedPlanOf P theta (dst.xslot i) (dst.zslot i)
            (nextSignedWidthBy P.widthRule x z T.ops) _ rfl
        have hchild : ∀ (i : Fin T.k) (theta : Angle),
            LowGate.gateCount (shorGateCostModelFor nm) (lowerGateRec (recurseC i theta))
              ≤ 5 * LowGate.gateCount (shorGateCostModelFor nm)
                  (lowerGateRec (recurseS i theta)) := by
          intro i theta
          have h := ih (nextSignedWidthBy P.widthRule x z T.ops) (by rw [← hn]; exact hrec) theta
            (dst.xslot i) (dst.zslot i) (childSize i) (childWorkspace i)
          unfold Policy.cSignedPhaseProductGateCountFor Policy.signedPhaseProductGateCountFor at h
          rw [Policy.lowerCSignedPhaseProd_eq_of P ctrl theta (dst.xslot i) (dst.zslot i)
              (nextSignedWidthBy P.widthRule x z T.ops) _ rfl,
            Policy.lowerSignedPhaseProd_eq_of P theta (dst.xslot i) (dst.zslot i)
              (nextSignedWidthBy P.widthRule x z T.ops) _ rfl] at h
          exact h
        simp only [hrec, ↓reduceDIte]
        simp only [PhaseLoweringPlan.lowerGateRec_cSignedStep,
          PhaseLoweringPlan.lowerGateRec_signedStep]
        unfold Policy.cStepPlan Policy.stepPlan
        dsimp only
        rw [lowerGateRec_mpr_gate_of_eq (P := P)
          (hUV := by
            simp [compiledCSignedPhaseGateBy, compileOpsToCSignedGateBy, compileOpsToSignedGateBy,
              controlPhaseLeaves, controlPhaseLeaves_compileSignedAllocations,
              controlPhaseLeaves_compileSignedDeallocations])]
        simp only [lgc_seq]
        have hbody :=
          CPhaseProductReduction.lgc_cbody_le_five nm (hk := T.hk) (nextSignedWidthBy P.widthRule x z T.ops) ctrl dst
            (cramerCoeffFromPtsWidth T.k (phaseLimbWidth x z T.k) T.pts T.hpts) φ recurseC
            recurseS hchild 0 T.ops
        change
          LowGate.gateCount (shorGateCostModelFor nm)
              (lowerGateRec (planCompileSignedAllocations
                (nextSignedWidthBy P.widthRule x z T.ops) src dst))
            + (LowGate.gateCount (shorGateCostModelFor nm)
                (lowerGateRec (planCompileAnnotatedOpsToCSignedGateAux
                  (nextSignedWidthBy P.widthRule x z T.ops) ctrl φ
                  (cramerCoeffFromPtsWidth T.k (phaseLimbWidth x z T.k) T.pts T.hpts)
                  dst recurseC (annotatePhaseTermsAux T.k 0 T.ops)))
              + LowGate.gateCount (shorGateCostModelFor nm)
                (lowerGateRec (planCompileSignedDeallocations
                  (nextSignedWidthBy P.widthRule x z T.ops) src dst)))
            ≤ 5 * (LowGate.gateCount (shorGateCostModelFor nm)
                (lowerGateRec (planCompileSignedAllocations
                  (nextSignedWidthBy P.widthRule x z T.ops) src dst))
              + (LowGate.gateCount (shorGateCostModelFor nm)
                  (lowerGateRec (planCompileAnnotatedOpsToSignedGateAux
                    (nextSignedWidthBy P.widthRule x z T.ops) φ
                    (cramerCoeffFromPtsWidth T.k (phaseLimbWidth x z T.k) T.pts T.hpts)
                    dst recurseS (annotatePhaseTermsAux T.k 0 T.ops)))
                + LowGate.gateCount (shorGateCostModelFor nm)
                  (lowerGateRec (planCompileSignedDeallocations
                    (nextSignedWidthBy P.widthRule x z T.ops) src dst))))
        omega
      · simp only [hrec, ↓reduceDIte]
        exact hleaf

/-! ## The exponent of a policy -/

/-- A policy with a first band has that band's exponent. -/
theorem ShorLoweringPolicy.gateExponent_of_head? {P : ShorLoweringPolicy} {b : PolicyBand}
    (hb : P.bands.head? = some b) : P.gateExponent = phaseProductExponent b.table.k := by
  simp [ShorLoweringPolicy.gateExponent, hb, phaseProductExponent, q]

/-- The policy with no bands has exponent two. -/
theorem ShorLoweringPolicy.gateExponent_of_none {P : ShorLoweringPolicy}
    (hb : P.bands.head? = none) : P.gateExponent = 2 := by
  simp [ShorLoweringPolicy.gateExponent, hb]

/-- Every policy's exponent is above one. -/
theorem ShorLoweringPolicy.one_lt_gateExponent (P : ShorLoweringPolicy) : 1 < P.gateExponent := by
  rcases hb : P.bands.head? with _ | b
  · rw [ShorLoweringPolicy.gateExponent_of_none hb]; norm_num
  · rw [ShorLoweringPolicy.gateExponent_of_head? hb]
    exact one_lt_phaseProductExponent b.table.k b.table.hk

/-- The policy with no bands picks no table. -/
theorem ShorLoweringPolicy.choose_of_head?_none {P : ShorLoweringPolicy}
    (hb : P.bands.head? = none) (n : ℕ) : P.choose n = none := by
  have hnil : P.bands = [] := List.head?_eq_none_iff.mp hb
  simp [ShorLoweringPolicy.choose, hnil]

/-- **The signed phase-product gate count under a policy**: above some width, at most a constant
times `n ^ P.gateExponent`, `n` the wider operand's width. -/
theorem Policy.signedPhaseProductGateCountFor_gateExponent_bound (hP : P.Admissible) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (φ : Angle) (x z : ExtReg), Policy.WorkspaceOK P x z →
        n₀ ≤ max (ExtReg.width x) (ExtReg.width z) →
        (Policy.signedPhaseProductGateCountFor nm P φ x z : ℝ)
          ≤ C * Real.rpow ((max (ExtReg.width x) (ExtReg.width z) : ℕ) : ℝ) P.gateExponent := by
  rcases hb : P.bands.head? with _ | b
  · refine ⟨5, by norm_num, 1, le_rfl, fun φ x z hws _ => ?_⟩
    rw [ShorLoweringPolicy.gateExponent_of_none hb,
      Policy.signedPhaseProductGateCountFor_of_stops nm P φ x z hws
        (fun T hT => by rw [ShorLoweringPolicy.choose_of_head?_none hb] at hT; cases hT)]
    have hx : ExtReg.width x ≤ max (ExtReg.width x) (ExtReg.width z) := le_max_left _ _
    have hz : ExtReg.width z ≤ max (ExtReg.width x) (ExtReg.width z) := le_max_right _ _
    have hnat : 5 * ExtReg.width x * ExtReg.width z
        ≤ 5 * (max (ExtReg.width x) (ExtReg.width z) * max (ExtReg.width x) (ExtReg.width z)) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left 5 (Nat.mul_le_mul hx hz)
    have hpow : Real.rpow ((max (ExtReg.width x) (ExtReg.width z) : ℕ) : ℝ) 2
        = ((max (ExtReg.width x) (ExtReg.width z) : ℕ) : ℝ)
          * ((max (ExtReg.width x) (ExtReg.width z) : ℕ) : ℝ) := by
      rw [Real.rpow_eq_pow, Real.rpow_two, sq]
    rw [hpow]
    exact_mod_cast hnat
  · rw [ShorLoweringPolicy.gateExponent_of_head? hb]
    exact Policy.signedPhaseProductGateCountFor_bound nm P b hP hb

end PolicyGateCount

end Shor
