import ForShor.ShorVerification.Implementation.Reference.Standard.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Registers

/-!
# Reference: the layout

The precision schedule's facts, the shape of the allocated registers, where they
sit relative to one another, and the workspace facts the circuit needs of them:
`reference_layoutOK`, and the reserve budget `reference_shorWorkspaceLargeEnough`.
-/

namespace Shor
namespace Reference

/-! ## The precision schedule -/

theorem referencePrecision_pos (m : ℕ) : 0 < referencePrecision m := by
  unfold referencePrecision
  positivity

theorem referencePrecision_lt_half (m : ℕ) : referencePrecision m < (1 / 2 : ℝ) := by
  unfold referencePrecision
  have hden : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  rw [div_lt_iff₀ hden]
  have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
  nlinarith

/-- `algorithm1ExtraBitsNat` computes `algorithm1ExtraBits` at the reference schedule. -/
theorem algorithm1ExtraBits_referencePrecision (m : ℕ) :
    algorithm1ExtraBits (referencePrecision m) = algorithm1ExtraBitsNat m := by
  unfold algorithm1ExtraBits algorithm1ExtraBitsNat referencePrecision
  have hstep : (2 + 1 / (2 * (1 / ((m : ℝ) + 3)))) = ((m : ℝ) + 7) / 2 := by
    have hm3 : ((m : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring
  rw [hstep]
  have hlogb :
      2 * Real.logb 2 (((m : ℝ) + 7) / 2) =
        Real.logb 2 (((((m + 7) ^ 2 : ℕ)) : ℝ)) - 2 := by
    rw [Real.logb_div (by positivity) (by norm_num)]
    have hpow :
        Real.logb 2 ((((m + 7) ^ 2 : ℕ) : ℝ)) = 2 * Real.logb 2 (((m : ℝ) + 7)) := by
      rw [show (((((m + 7) ^ 2 : ℕ)) : ℝ)) = (((m : ℝ) + 7)) ^ 2 by push_cast; ring]
      rw [Real.logb_pow]
      push_cast
      ring
    rw [hpow, Real.logb_self_eq_one (by norm_num)]
    ring
  rw [hlogb]
  have hcast2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [hcast2, Nat.ceil_sub_natCast, Real.natCeil_logb_natCast]

/-! ## The shape of the registers -/

@[simp] lemma regSize_interval (lo size : ℕ) : regSize (Reg.interval lo size) = size := by
  simp [regSize, Reg.width, Reg.interval]

@[simp] lemma width_widthShell (n : ℕ) : (widthShell n).width = n := by
  simp [widthShell, ExtReg.ofReg, ExtReg.width]

@[simp] private theorem withReserve_active (active reserve : Reg) (h : Disjoint active reserve) :
    (ExtReg.withReserve active reserve h).active = active := rfl

@[simp] private theorem withReserve_reserve (active reserve : Reg) (h : Disjoint active reserve) :
    (ExtReg.withReserve active reserve h).reserve = reserve := rfl

variable (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ)

@[simp] theorem allocateReferenceLayout_x_active :
    (allocateReferenceLayout P inst m).x.active = referenceXActive inst := rfl

@[simp] theorem allocateReferenceLayout_x_width :
    regSize (allocateReferenceLayout P inst m).x.active = Nat.log2 (2 * inst.N^2) := by
  simp [allocateReferenceLayout, referenceX, referenceXActive, referenceXWidth]

@[simp] theorem allocateReferenceLayout_data_width :
    regSize (allocateReferenceLayout P inst m).data.active = Nat.log2 (2 * inst.N) := by
  simp [allocateReferenceLayout, referenceData, referenceDataActive, referenceDataWidth]

@[simp] theorem allocateReferenceLayout_work_width :
    regSize (allocateReferenceLayout P inst m).work.active =
      referenceDataWidth inst + algorithm1ExtraBitsNat m := by
  simp [allocateReferenceLayout, referenceWork, referenceWorkActive, referenceWorkWidth]

@[simp] theorem allocateReferenceLayout_scratch_width :
    regSize (allocateReferenceLayout P inst m).scratch.active = referenceScratchWidth inst m := by
  simp [allocateReferenceLayout, referenceScratch, referenceScratchActive]

@[simp] theorem allocateReferenceLayout_x_capacity :
    (allocateReferenceLayout P inst m).x.capacity = referenceXReserveSize P inst m := by
  simp [allocateReferenceLayout, referenceX, referenceXReserve, ExtReg.capacity]

@[simp] theorem allocateReferenceLayout_data_capacity :
    (allocateReferenceLayout P inst m).data.capacity = referenceDataReserveSize P inst m := by
  simp [allocateReferenceLayout, referenceData, referenceDataReserve, ExtReg.capacity]

@[simp] theorem allocateReferenceLayout_work_capacity :
    (allocateReferenceLayout P inst m).work.capacity = referenceWorkReserveSize P inst m := by
  simp [allocateReferenceLayout, referenceWork, referenceWorkReserve, ExtReg.capacity]

@[simp] theorem allocateReferenceLayout_scratch_capacity :
    (allocateReferenceLayout P inst m).scratch.capacity = referenceScratchReserveSize P inst m := by
  simp [allocateReferenceLayout, referenceScratch, referenceScratchReserve, ExtReg.capacity]

/-! ## Where the registers sit -/

private lemma referenceX_owned_lt_dataStart {q : ℕ}
    (hq : q ∈ (referenceX P inst m).ownedQubits) : q < referenceDataStart P inst m := by
  simp only [referenceX, ExtReg.ownedQubits, ExtReg.withReserve, List.mem_append] at hq
  rcases hq with hactive | hreserve
  · have hlt := (mem_interval_bounds hactive).2
    unfold referenceXActive referenceDataStart referenceXReserveStart at *
    omega
  · have hlt := (mem_interval_bounds hreserve).2
    unfold referenceXReserve referenceDataStart referenceXReserveStart at *
    omega

private lemma referenceData_owned_ge_dataStart {q : ℕ}
    (hq : q ∈ (referenceData P inst m).ownedQubits) : referenceDataStart P inst m ≤ q := by
  simp only [referenceData, ExtReg.ownedQubits, ExtReg.withReserve, List.mem_append] at hq
  rcases hq with hactive | hreserve
  · exact (mem_interval_bounds hactive).1
  · have hge := (mem_interval_bounds hreserve).1
    unfold referenceDataReserveStart at hge
    omega

private lemma referenceWork_owned_ge_workStart {q : ℕ}
    (hq : q ∈ (referenceWork P inst m).ownedQubits) : referenceWorkStart P inst m ≤ q := by
  simp only [referenceWork, ExtReg.ownedQubits, ExtReg.withReserve, List.mem_append] at hq
  rcases hq with hactive | hreserve
  · exact (mem_interval_bounds hactive).1
  · have hge := (mem_interval_bounds hreserve).1
    unfold referenceWorkReserveStart at hge
    omega

private lemma referenceWork_owned_lt_scratchStart {q : ℕ}
    (hq : q ∈ (referenceWork P inst m).ownedQubits) : q < referenceScratchStart P inst m := by
  simp only [referenceWork, ExtReg.ownedQubits, ExtReg.withReserve, List.mem_append] at hq
  rcases hq with hactive | hreserve
  · have hlt := (mem_interval_bounds hactive).2
    unfold referenceScratchStart referenceWorkReserveStart
    omega
  · have hlt := (mem_interval_bounds hreserve).2
    simpa [referenceWorkReserve, referenceScratchStart] using hlt

private lemma referenceScratch_owned_ge_scratchStart {q : ℕ}
    (hq : q ∈ (referenceScratch P inst m).ownedQubits) : referenceScratchStart P inst m ≤ q := by
  simp only [referenceScratch, ExtReg.ownedQubits, ExtReg.withReserve, List.mem_append] at hq
  rcases hq with hactive | hreserve
  · exact (mem_interval_bounds hactive).1
  · have hge := (mem_interval_bounds hreserve).1
    unfold referenceScratchReserveStart at hge
    omega

private lemma referenceScratch_owned_lt_flag {q : ℕ}
    (hq : q ∈ (referenceScratch P inst m).ownedQubits) : q < referenceFlag P inst m := by
  simp only [referenceScratch, ExtReg.ownedQubits, ExtReg.withReserve, List.mem_append] at hq
  rcases hq with hactive | hreserve
  · have hlt := (mem_interval_bounds hactive).2
    unfold referenceFlag referenceScratchReserveStart
    omega
  · have hlt := (mem_interval_bounds hreserve).2
    simpa [referenceScratchReserve, referenceFlag] using hlt

private lemma referenceX_owned_lt_workStart {q : ℕ}
    (hq : q ∈ (referenceX P inst m).ownedQubits) : q < referenceWorkStart P inst m := by
  have hlt := referenceX_owned_lt_dataStart P inst m hq
  unfold referenceWorkStart referenceDataReserveStart
  omega

private lemma referenceData_owned_lt_workStart {q : ℕ}
    (hq : q ∈ (referenceData P inst m).ownedQubits) : q < referenceWorkStart P inst m := by
  simp only [referenceData, ExtReg.ownedQubits, ExtReg.withReserve, List.mem_append] at hq
  rcases hq with hactive | hreserve
  · have hlt := (mem_interval_bounds hactive).2
    unfold referenceDataActive referenceWorkStart referenceDataReserveStart at *
    omega
  · have hlt := (mem_interval_bounds hreserve).2
    simpa [referenceDataReserve, referenceWorkStart] using hlt

theorem reference_exponent_data_disjoint :
    ExtReg.OwnedDisjoint (referenceX P inst m) (referenceData P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hx hy
  have hlt := referenceX_owned_lt_dataStart P inst m hx
  have hge := referenceData_owned_ge_dataStart P inst m hy
  omega

theorem reference_data_work_disjoint :
    ExtReg.OwnedDisjoint (referenceData P inst m) (referenceWork P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hdata hwork
  have hlt := referenceData_owned_lt_workStart P inst m hdata
  have hge := referenceWork_owned_ge_workStart P inst m hwork
  omega

theorem reference_exponent_work_disjoint :
    ExtReg.OwnedDisjoint (referenceX P inst m) (referenceWork P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hx hwork
  have hxlt := referenceX_owned_lt_workStart P inst m hx
  have hworkge := referenceWork_owned_ge_workStart P inst m hwork
  omega

theorem reference_exponent_scratch_disjoint :
    ExtReg.OwnedDisjoint (referenceX P inst m) (referenceScratch P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hx hscratch
  have hxlt := referenceX_owned_lt_workStart P inst m hx
  have hscratchge := referenceScratch_owned_ge_scratchStart P inst m hscratch
  unfold referenceScratchStart referenceWorkReserveStart at hscratchge
  omega

theorem reference_data_scratch_disjoint :
    ExtReg.OwnedDisjoint (referenceData P inst m) (referenceScratch P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hdata hscratch
  have hdlt := referenceData_owned_lt_workStart P inst m hdata
  have hscratchge := referenceScratch_owned_ge_scratchStart P inst m hscratch
  unfold referenceScratchStart referenceWorkReserveStart at hscratchge
  omega

theorem reference_work_scratch_disjoint :
    ExtReg.OwnedDisjoint (referenceWork P inst m) (referenceScratch P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hwork hscratch
  have hlt := referenceWork_owned_lt_scratchStart P inst m hwork
  have hge := referenceScratch_owned_ge_scratchStart P inst m hscratch
  omega

theorem reference_flag_outside_exponent :
    referenceFlag P inst m ∉ (referenceX P inst m).ownedQubits := by
  intro hflag
  have hlt := referenceX_owned_lt_workStart P inst m hflag
  have hge : referenceWorkStart P inst m ≤ referenceFlag P inst m := by
    unfold referenceFlag referenceScratchReserveStart referenceScratchStart referenceWorkReserveStart
    omega
  omega

theorem reference_flag_outside_data :
    referenceFlag P inst m ∉ (referenceData P inst m).ownedQubits := by
  intro hflag
  have hlt := referenceData_owned_lt_workStart P inst m hflag
  have hge : referenceWorkStart P inst m ≤ referenceFlag P inst m := by
    unfold referenceFlag referenceScratchReserveStart referenceScratchStart referenceWorkReserveStart
    omega
  omega

theorem reference_flag_outside_work :
    referenceFlag P inst m ∉ (referenceWork P inst m).ownedQubits := by
  intro hflag
  have hlt := referenceWork_owned_lt_scratchStart P inst m hflag
  unfold referenceFlag referenceScratchReserveStart at *
  omega

theorem reference_flag_outside_scratch :
    referenceFlag P inst m ∉ (referenceScratch P inst m).ownedQubits := by
  intro hflag
  have hlt := referenceScratch_owned_lt_flag P inst m hflag
  omega

theorem reference_controls_outside_work :
    ∀ q ∈ (referenceX P inst m).active.qubits, q ∉ (referenceWork P inst m).ownedQubits := by
  intro q hq hwork
  have hxOwned : q ∈ (referenceX P inst m).ownedQubits := by
    rw [ExtReg.ownedQubits, List.mem_append]
    exact Or.inl hq
  exact reference_exponent_work_disjoint P inst m hxOwned hwork

theorem reference_flag_outside_controls :
    referenceFlag P inst m ∉ (referenceX P inst m).active.qubits := by
  intro hctrl
  apply reference_flag_outside_exponent P inst m
  rw [ExtReg.ownedQubits, List.mem_append]
  exact Or.inl hctrl

/-! ## The workspace facts -/

private theorem shorWorkspaceNeed_ext {a b : ShorWorkspaceNeed}
    (hexponent : a.exponent = b.exponent) (hdata : a.data = b.data)
    (hauxiliary : a.auxiliary = b.auxiliary) (hscratch : a.scratch = b.scratch) : a = b := by
  cases a with
  | mk ae ad aa as =>
      cases b with
      | mk be bd ba bs =>
          simp at hexponent hdata hauxiliary hscratch
          simp [hexponent, hdata, hauxiliary, hscratch]

/-- The allocated registers have the same width-based reserve need as the shells used
to size them. -/
theorem reference_workspaceNeed_eq :
    shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (referenceSiteReserve P)
      (referenceX P inst m) (referenceData P inst m) (referenceWork P inst m)
      (referenceScratch P inst m)
      = referenceWorkspaceNeed P inst m := by
  apply shorWorkspaceNeed_ext <;>
    simp only [shorWorkspaceNeedOf, qftReserveNeedOf, referenceWorkspaceNeed, widthShell,
      referenceX, referenceXActive, referenceData, referenceDataActive, referenceWork,
      referenceWorkActive, referenceScratch, referenceScratchActive, referenceXWidth,
      referenceDataWidth, referenceWorkWidth, referenceScratchWidth, ExtReg.width, ExtReg.ofReg,
      withReserve_active, regSize_interval]

theorem reference_data_canGrow_two : (referenceData P inst m).CanGrow 2 := by
  simp [ExtReg.CanGrow, referenceData, referenceDataReserve, ExtReg.capacity,
    referenceDataReserveSize]

theorem reference_work_canGrow_one : (referenceWork P inst m).CanGrow 1 := by
  simp [ExtReg.CanGrow, referenceWork, referenceWorkReserve, ExtReg.capacity,
    referenceWorkReserveSize]

theorem reference_scratch_canGrow_one : (referenceScratch P inst m).CanGrow 1 := by
  simp [ExtReg.CanGrow, referenceScratch, referenceScratchReserve, ExtReg.capacity,
    referenceScratchReserveSize]

theorem reference_modMulCircuitWorkspaceOK :
    ModMulCircuitWorkspaceOK (referenceData P inst m) (referenceWork P inst m) :=
  ⟨reference_data_canGrow_two P inst m, reference_work_canGrow_one P inst m,
    reference_data_work_disjoint P inst m⟩

/-- The layout facts the circuit needs hold of every layout. -/
theorem reference_layoutOK : LayoutOK P inst m where
  modMul := reference_modMulCircuitWorkspaceOK P inst m
  scratch_canGrow := reference_scratch_canGrow_one P inst m
  work_scratch_disjoint := reference_work_scratch_disjoint P inst m
  data_scratch_disjoint := by
    simpa [ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow] using
      reference_data_scratch_disjoint P inst m
  flag_not_data := by
    simpa [Gate.ExtReg.ownedQubits_grow] using reference_flag_outside_data P inst m
  flag_not_work := reference_flag_outside_work P inst m
  flag_not_scratch := reference_flag_outside_scratch P inst m
  scratch_width := by
    have hmod := reference_modMulCircuitWorkspaceOK P inst m
    have hdataGrowWidth : ((referenceData P inst m).grow 1).width = referenceDataWidth inst + 1 := by
      rw [ExtReg.width_grow _ 1 (le_trans (by norm_num) hmod.1)]
      simp [referenceData, referenceDataActive, ExtReg.width]
    have hworkWidth : (referenceWork P inst m).width = referenceWorkWidth inst m := by
      simp [referenceWork, referenceWorkActive, ExtReg.width]
    rw [show regSize (referenceScratch P inst m).active = referenceScratchWidth inst m by
      simp [referenceScratch, referenceScratchActive]]
    unfold cmpLtNWWidth
    change referenceScratchWidth inst m =
      2 + max (((referenceData P inst m).grow 1).width + (referenceWork P inst m).width)
        (Nat.log2 (inst.N + 1) + 1 + (referenceWork P inst m).width)
    rw [hdataGrowWidth, hworkWidth]
    rfl

/-- The comparator's registers on the layout. -/
def reference_step4Workspace :
    CmpLtNWWorkspace inst.N ((referenceData P inst m).grow 1) (referenceWork P inst m)
      (referenceScratch P inst m) (referenceFlag P inst m) :=
  (reference_layoutOK P inst m).step4Workspace

/-- `referenceSiteReserve` is at least the lowerer's own need at every site. -/
private theorem shorWorkspaceNeed_le_referenceSiteReserve (x data work scratch : ExtReg) :
    (Policy.shorWorkspaceNeed P x data work scratch).exponent ≤
        (shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (referenceSiteReserve P)
          x data work scratch).exponent ∧
      (Policy.shorWorkspaceNeed P x data work scratch).data ≤
        (shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (referenceSiteReserve P)
          x data work scratch).data ∧
      (Policy.shorWorkspaceNeed P x data work scratch).auxiliary ≤
        (shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (referenceSiteReserve P)
          x data work scratch).auxiliary ∧
      (Policy.shorWorkspaceNeed P x data work scratch).scratch ≤
        (shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (referenceSiteReserve P)
          x data work scratch).scratch := by
  simp only [Policy.shorWorkspaceNeed, shorWorkspaceNeedOf, referenceSiteReserve]
  omega

/-- The reserve budget of the lowering is met by construction. -/
theorem reference_shorWorkspaceLargeEnough :
    Policy.ShorWorkspaceLargeEnough P (referenceX P inst m) (referenceData P inst m)
      (referenceWork P inst m) (referenceScratch P inst m) := by
  have hneed := reference_workspaceNeed_eq P inst m
  have hle := shorWorkspaceNeed_le_referenceSiteReserve P
    (referenceX P inst m) (referenceData P inst m) (referenceWork P inst m)
    (referenceScratch P inst m)
  rw [hneed] at hle
  obtain ⟨hx, hd, hw, hs⟩ := hle
  refine ⟨hx.trans ?_, hd.trans ?_, hw.trans ?_, hs.trans ?_⟩
  · simp [referenceX, referenceXReserve, ExtReg.capacity, referenceXReserveSize]
  · simp [referenceData, referenceDataReserve, ExtReg.capacity, referenceDataReserveSize]
  · simp [referenceWork, referenceWorkReserve, ExtReg.capacity, referenceWorkReserveSize]
  · simp [referenceScratch, referenceScratchReserve, ExtReg.capacity, referenceScratchReserveSize]

theorem reference_shorWorkspaceIsolation :
    ShorWorkspaceIsolation (referenceX P inst m) (referenceWork P inst m)
      (referenceScratch P inst m) (referenceFlag P inst m) :=
  ⟨reference_exponent_work_disjoint P inst m, reference_exponent_scratch_disjoint P inst m,
    reference_flag_outside_exponent P inst m⟩

/-- The work width meets Algorithm 1's precision equation at every level `m`. -/
theorem reference_algorithm1Precision :
    Algorithm1Precision (referencePrecision m) (referenceData P inst m).active
      (referenceWork P inst m).active := by
  refine ⟨referencePrecision_pos m, referencePrecision_lt_half m, ?_⟩
  simp [referenceData, referenceDataActive, referenceWork, referenceWorkActive,
    referenceDataWidth, referenceWorkWidth, algorithm1ExtraBits_referencePrecision]

end Reference
end Shor
