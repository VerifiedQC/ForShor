import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.OrderFinding

namespace Shor
namespace Reference

noncomputable section

/-!
# Reference Shor layout allocator

This file is the implementation-side allocator used to turn the construction-free
`ShorImplementation` input into the concrete register layout required by the
reference LowGate implementation.

The framework measures `inst.x.active`, so that active register is preserved.
Everything else used by the reference implementation is allocated in a fresh
contiguous region strictly above every qubit already owned by the public `x` and
`y` registers:

```
public x/y qubits
       |
       v
 privateStart
       |
       |-- x reserve
       |-- fresh data active
       |-- data reserve
       |-- work active
       |-- work reserve
       `-- flag
```

The data register is deliberately allocated fresh rather than reusing
`inst.y.active`: `ShorOrderFindingInstance` currently fixes the data width but
does not require the public `x` and `y` registers to be physically disjoint.
The allocated data register has exactly the same active width as `inst.y`.

Because `ShorImplementation.correct` runs from `RegEncoding.zero`, all qubits
selected by this allocator are clean in the framework's canonical initial state.
The cleanliness bridge belongs in the later discharge file; this module handles
only deterministic placement and the static layout/workspace facts.
-/

/-! =========================================================
    Section 1: Physical-qubit ceiling and interval helpers
========================================================= -/


private lemma mem_interval_bounds
    {lo size q : ℕ}
    (hq : q ∈ (Reg.interval lo size).qubits) :
    lo ≤ q ∧ q < lo + size := by
  change q ∈ (List.range size).map (fun i => lo + i) at hq
  rcases List.mem_map.mp hq with ⟨i, hi, hqi⟩
  have hi' : i < size := by simpa using hi
  subst q
  omega

private lemma interval_disjoint_of_end_le
    {lo₁ size₁ lo₂ size₂ : ℕ}
    (h : lo₁ + size₁ ≤ lo₂) :
    Disjoint (Reg.interval lo₁ size₁) (Reg.interval lo₂ size₂) := by
  rw [Disjoint, List.disjoint_left]
  intro q hq₁ hq₂
  have h₁ := mem_interval_bounds hq₁
  have h₂ := mem_interval_bounds hq₂
  omega

private lemma reg_disjoint_interval_of_below
    (r : Reg)
    {start size : ℕ}
    (hbelow : ∀ q ∈ r.qubits, q < start) :
    Disjoint r (Reg.interval start size) := by
  rw [Disjoint, List.disjoint_left]
  intro q hqr hqi
  have hlt := hbelow q hqr
  have hge := (mem_interval_bounds hqi).1
  omega

@[simp] lemma regSize_interval (lo size : ℕ) :
    regSize (Reg.interval lo size) = size := by
  simp [regSize, Reg.width, Reg.interval]

/-! =========================================================
    Section 2: Widths and reserve budgets
========================================================= -/

/-- Active width of the phase-estimation/output register. -/
def referenceXWidth (inst : ShorOrderFindingInstance) : ℕ :=
  Nat.log2 (2 * inst.N^2)

/-- Active width of the modular-data register. -/
def referenceDataWidth (inst : ShorOrderFindingInstance) : ℕ :=
  Nat.log2 (2 * inst.N)

/-- Active width prescribed for Algorithm 1's work register. -/
noncomputable def referenceWorkWidth
    (inst : ShorOrderFindingInstance)
    (η : ℝ) : ℕ :=
  referenceDataWidth inst + algorithm1ExtraBits η

/-- Width-only stand-in used to evaluate `shorWorkspaceNeed`. -/
private def widthShell (n : ℕ) : ExtReg :=
  ExtReg.ofReg (Reg.interval 0 n)

@[simp] private lemma width_widthShell (n : ℕ) :
    (widthShell n).width = n := by
  simp [widthShell, ExtReg.ofReg, ExtReg.width]

/--
Reserve budget required by the current reference lowerer at these active widths.
The locations of the shell registers are irrelevant because
`shorWorkspaceNeed` depends only on active widths.
-/
noncomputable def referenceWorkspaceNeed
    {k : ℕ}
    (ops : Prog k)
    (inst : ShorOrderFindingInstance)
    (η : ℝ) : ShorWorkspaceNeed :=
  shorWorkspaceNeed ops
    (widthShell (referenceXWidth inst))
    (widthShell (referenceDataWidth inst))
    (widthShell (referenceWorkWidth inst η))

noncomputable def referenceXReserveSize
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : ℕ :=
  (referenceWorkspaceNeed ops inst η).exponent

/-- Two bits are additionally guaranteed for Algorithm 1's data growth. -/
noncomputable def referenceDataReserveSize
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : ℕ :=
  max 2 (referenceWorkspaceNeed ops inst η).data

/-- One bit is additionally guaranteed for Algorithm 1's work growth. -/
noncomputable def referenceWorkReserveSize
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : ℕ :=
  max 1 (referenceWorkspaceNeed ops inst η).auxiliary

private theorem shorWorkspaceNeed_ext
    {a b : ShorWorkspaceNeed}
    (hexponent : a.exponent = b.exponent)
    (hdata : a.data = b.data)
    (hauxiliary : a.auxiliary = b.auxiliary) :
    a = b := by
  cases a with
  | mk ae ad aa =>
      cases b with
      | mk be bd ba =>
          simp at hexponent hdata hauxiliary
          simp [hexponent, hdata, hauxiliary]

/-! =========================================================
    Section 3: Deterministic fresh-region placement
========================================================= -/

/-- The reference implementation starts its exponent register at qubit 0. -/
def referenceXActive (inst : ShorOrderFindingInstance) : Reg :=
  Reg.interval 0 (referenceXWidth inst)

def referenceXReserveStart
    (inst : ShorOrderFindingInstance) : ℕ :=
  referenceXWidth inst

noncomputable def referenceDataStart
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : ℕ :=
  referenceXReserveStart inst +
    referenceXReserveSize ops inst η

noncomputable def referenceDataReserveStart
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : ℕ :=
  referenceDataStart ops inst η +
    referenceDataWidth inst

noncomputable def referenceWorkStart
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : ℕ :=
  referenceDataReserveStart ops inst η +
    referenceDataReserveSize ops inst η

noncomputable def referenceWorkReserveStart
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : ℕ :=
  referenceWorkStart ops inst η +
    referenceWorkWidth inst η

noncomputable def referenceFlag
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : ℕ :=
  referenceWorkReserveStart ops inst η +
    referenceWorkReserveSize ops inst η

noncomputable def referenceXReserve
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : Reg :=
  Reg.interval
    (referenceXReserveStart inst)
    (referenceXReserveSize ops inst η)

noncomputable def referenceDataActive
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : Reg :=
  Reg.interval
    (referenceDataStart ops inst η)
    (referenceDataWidth inst)

noncomputable def referenceDataReserve
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : Reg :=
  Reg.interval
    (referenceDataReserveStart ops inst η)
    (referenceDataReserveSize ops inst η)

noncomputable def referenceWorkActive
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : Reg :=
  Reg.interval
    (referenceWorkStart ops inst η)
    (referenceWorkWidth inst η)

noncomputable def referenceWorkReserve
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : Reg :=
  Reg.interval
    (referenceWorkReserveStart ops inst η)
    (referenceWorkReserveSize ops inst η)

/-! =========================================================
    Section 4: Extended-register construction
========================================================= -/

noncomputable def referenceX
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : ExtReg :=
  ExtReg.withReserve
    (referenceXActive inst)
    (referenceXReserve ops inst η)
    (interval_disjoint_of_end_le (by simp [referenceXReserveStart]))

noncomputable def referenceData
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : ExtReg :=
  ExtReg.withReserve
    (referenceDataActive ops inst η)
    (referenceDataReserve ops inst η)
    (interval_disjoint_of_end_le (by
      simp [referenceDataReserveStart]))

noncomputable def referenceWork
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) : ExtReg :=
  ExtReg.withReserve
    (referenceWorkActive ops inst η)
    (referenceWorkReserve ops inst η)
    (interval_disjoint_of_end_le (by
      simp [referenceWorkReserveStart]))


@[simp] private theorem withReserve_active
    (active reserve : Reg) (h : Disjoint active reserve) :
    (ExtReg.withReserve active reserve h).active = active := by
  rfl

@[simp] private theorem withReserve_reserve
    (active reserve : Reg) (h : Disjoint active reserve) :
    (ExtReg.withReserve active reserve h).reserve = reserve := by
  rfl

/-- Concrete register package consumed by the reference Shor implementation. -/
structure ReferenceShorLayout where
  x : ExtReg
  data : ExtReg
  work : ExtReg
  flag : ℕ

/--
Allocate all reference-implementation storage deterministically above the public
register file.
-/
noncomputable def allocateReferenceLayout
    {k : ℕ}
    (ops : Prog k)
    (inst : ShorOrderFindingInstance)
    (η : ℝ) : ReferenceShorLayout :=
  {
    x := referenceX ops inst η
    data := referenceData ops inst η
    work := referenceWork ops inst η
    flag := referenceFlag ops inst η
  }

/-! =========================================================
    Section 5: Basic shape facts
========================================================= -/

@[simp] theorem allocateReferenceLayout_x_active
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    (allocateReferenceLayout ops inst η).x.active =
      referenceXActive inst := by
  rfl

@[simp] theorem allocateReferenceLayout_x_width
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    regSize (allocateReferenceLayout ops inst η).x.active =
      Nat.log2 (2 * inst.N^2) := by
  simp [allocateReferenceLayout, referenceX,
    referenceXActive, referenceXWidth]

@[simp] theorem allocateReferenceLayout_data_width
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    regSize (allocateReferenceLayout ops inst η).data.active =
      Nat.log2 (2 * inst.N) := by
  simp [allocateReferenceLayout, referenceData,
    referenceDataActive, referenceDataWidth]

@[simp] theorem allocateReferenceLayout_work_width
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    regSize (allocateReferenceLayout ops inst η).work.active =
      referenceDataWidth inst + algorithm1ExtraBits η := by
  simp [allocateReferenceLayout, referenceWork,
    referenceWorkActive, referenceWorkWidth]

@[simp] theorem allocateReferenceLayout_x_capacity
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    (allocateReferenceLayout ops inst η).x.capacity =
      referenceXReserveSize ops inst η := by
  simp [allocateReferenceLayout, referenceX, referenceXReserve,
    ExtReg.capacity]

@[simp] theorem allocateReferenceLayout_data_capacity
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    (allocateReferenceLayout ops inst η).data.capacity =
      referenceDataReserveSize ops inst η := by
  simp [allocateReferenceLayout, referenceData, referenceDataReserve,
    ExtReg.capacity]

@[simp] theorem allocateReferenceLayout_work_capacity
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    (allocateReferenceLayout ops inst η).work.capacity =
      referenceWorkReserveSize ops inst η := by
  simp [allocateReferenceLayout, referenceWork, referenceWorkReserve,
    ExtReg.capacity]

/-! =========================================================
    Section 6: Ordered-region bounds
========================================================= -/

private lemma referenceX_owned_lt_dataStart
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ)
    {q : ℕ}
    (hq : q ∈ (referenceX ops inst η).ownedQubits) :
    q < referenceDataStart ops inst η := by
  simp only [
    referenceX,
    ExtReg.ownedQubits,
    ExtReg.withReserve,
    List.mem_append
  ] at hq

  rcases hq with hactive | hreserve
  · have hlt := (mem_interval_bounds hactive).2
    unfold referenceXActive referenceDataStart referenceXReserveStart at *
    omega
  · have hlt := (mem_interval_bounds hreserve).2
    unfold referenceXReserve referenceDataStart referenceXReserveStart at *
    omega

private lemma referenceData_owned_ge_dataStart
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ)
    {q : ℕ}
    (hq : q ∈ (referenceData ops inst η).ownedQubits) :
    referenceDataStart ops inst η ≤ q := by
  simp only [
    referenceData,
    ExtReg.ownedQubits,
    ExtReg.withReserve,
    List.mem_append
  ] at hq

  rcases hq with hactive | hreserve
  · exact (mem_interval_bounds hactive).1
  · have hge := (mem_interval_bounds hreserve).1
    unfold referenceDataReserveStart at hge
    omega

private lemma referenceWork_owned_ge_workStart
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ)
    {q : ℕ}
    (hq : q ∈ (referenceWork ops inst η).ownedQubits) :
    referenceWorkStart ops inst η ≤ q := by
  simp only [referenceWork, ExtReg.ownedQubits, ExtReg.withReserve,
    List.mem_append] at hq
  rcases hq with hactive | hreserve
  · exact (mem_interval_bounds hactive).1
  · have hge := (mem_interval_bounds hreserve).1
    unfold referenceWorkReserveStart at hge
    omega

private lemma referenceWork_owned_lt_flag
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ)
    {q : ℕ}
    (hq : q ∈ (referenceWork ops inst η).ownedQubits) :
    q < referenceFlag ops inst η := by
  simp only [referenceWork, ExtReg.ownedQubits, ExtReg.withReserve,
    List.mem_append] at hq
  rcases hq with hactive | hreserve
  · have hlt := (mem_interval_bounds hactive).2
    unfold referenceFlag referenceWorkReserveStart
    omega
  · have hlt := (mem_interval_bounds hreserve).2
    simpa [referenceWorkReserve, referenceFlag] using hlt

/-! =========================================================
    Section 7: Static layout facts supplied by the allocator
========================================================= -/

/-- The allocated exponent and data storage are completely ownership-disjoint. -/
theorem reference_exponent_data_disjoint
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    ExtReg.OwnedDisjoint
      (referenceX ops inst η)
      (referenceData ops inst η) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hx hy
  have hlt := referenceX_owned_lt_dataStart ops inst η hx
  have hge := referenceData_owned_ge_dataStart ops inst η hy
  omega

private lemma referenceX_owned_lt_workStart
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ)
    {q : ℕ}
    (hq : q ∈ (referenceX ops inst η).ownedQubits) :
    q < referenceWorkStart ops inst η := by
  have hlt :=
    referenceX_owned_lt_dataStart ops inst η hq
  unfold referenceWorkStart referenceDataReserveStart
  omega

private lemma referenceData_owned_lt_workStart
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ)
    {q : ℕ}
    (hq : q ∈ (referenceData ops inst η).ownedQubits) :
    q < referenceWorkStart ops inst η := by
  simp only [
    referenceData,
    ExtReg.ownedQubits,
    ExtReg.withReserve,
    List.mem_append
  ] at hq

  rcases hq with hactive | hreserve
  · have hlt := (mem_interval_bounds hactive).2
    unfold referenceDataActive referenceWorkStart referenceDataReserveStart at *
    omega
  · have hlt := (mem_interval_bounds hreserve).2
    simpa [referenceDataReserve, referenceWorkStart] using hlt

/-- The allocated data and work storage are completely ownership-disjoint. -/
theorem reference_data_work_disjoint
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    ExtReg.OwnedDisjoint
      (referenceData ops inst η)
      (referenceWork ops inst η) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hdata hwork
  have hlt := referenceData_owned_lt_workStart ops inst η hdata
  have hge := referenceWork_owned_ge_workStart ops inst η hwork
  omega

/-- The exponent register and all work storage are ownership-disjoint. -/
theorem reference_exponent_work_disjoint
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    ExtReg.OwnedDisjoint
      (referenceX ops inst η)
      (referenceWork ops inst η) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hx hwork
  have hxlt :=
    referenceX_owned_lt_workStart ops inst η hx
  have hworkge :=
    referenceWork_owned_ge_workStart ops inst η hwork
  omega

/-- The flag is outside all exponent-owned qubits. -/
theorem reference_flag_outside_exponent
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    referenceFlag ops inst η ∉ (referenceX ops inst η).ownedQubits := by
  intro hflag
  have hlt := referenceX_owned_lt_workStart ops inst η hflag
  unfold referenceFlag referenceWorkReserveStart at *
  omega

/-- The flag is outside all data-owned qubits. -/
theorem reference_flag_outside_data
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    referenceFlag ops inst η ∉ (referenceData ops inst η).ownedQubits := by
  intro hflag
  have hlt := referenceData_owned_lt_workStart ops inst η hflag
  unfold referenceFlag referenceWorkReserveStart at *
  omega

/-- The flag is outside all work-owned qubits. -/
theorem reference_flag_outside_work
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    referenceFlag ops inst η ∉ (referenceWork ops inst η).ownedQubits := by
  intro hflag
  have hlt := referenceWork_owned_lt_flag ops inst η hflag
  omega

/-- Every active exponent/control qubit is outside the work register. -/
theorem reference_controls_outside_work
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    ∀ q ∈ (referenceX ops inst η).active.qubits,
      q ∉ (referenceWork ops inst η).ownedQubits := by
  intro q hq hwork
  have hxOwned : q ∈ (referenceX ops inst η).ownedQubits := by
    rw [ExtReg.ownedQubits, List.mem_append]
    exact Or.inl hq
  exact reference_exponent_work_disjoint ops inst η hxOwned hwork

/-- The comparison flag is not an active exponent/control qubit. -/
theorem reference_flag_outside_controls
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    referenceFlag ops inst η ∉
      (referenceX ops inst η).active.qubits := by
  intro hctrl
  apply reference_flag_outside_exponent ops inst η
  rw [ExtReg.ownedQubits, List.mem_append]
  exact Or.inl hctrl

/-! =========================================================
    Section 8: Workspace and precision facts
========================================================= -/

/-- The final allocated registers have the same width-based Shor reserve need
as the shells used to size them. -/
theorem reference_workspaceNeed_eq
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    shorWorkspaceNeed ops
      (referenceX ops inst η)
      (referenceData ops inst η)
      (referenceWork ops inst η)
      =
    referenceWorkspaceNeed ops inst η := by
  apply shorWorkspaceNeed_ext <;>
    simp only [
      shorWorkspaceNeed,
      referenceWorkspaceNeed,
      widthShell,
      referenceX,
      referenceXActive,
      referenceData,
      referenceDataActive,
      referenceWork,
      referenceWorkActive,
      referenceXWidth,
      referenceDataWidth,
      referenceWorkWidth,
      ExtReg.width,
      ExtReg.ofReg,
      withReserve_active,
      regSize_interval
    ]
/-- The data reserve always supports the two temporary Algorithm 1 growth bits. -/
theorem reference_data_canGrow_two
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    (referenceData ops inst η).CanGrow 2 := by
  simp [ExtReg.CanGrow, referenceData, referenceDataReserve,
    ExtReg.capacity, referenceDataReserveSize]

/-- The work reserve always supports Algorithm 1's temporary growth bit. -/
theorem reference_work_canGrow_one
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    (referenceWork ops inst η).CanGrow 1 := by
  simp [ExtReg.CanGrow, referenceWork, referenceWorkReserve,
    ExtReg.capacity, referenceWorkReserveSize]

/-- Static modular-multiplication workspace is guaranteed by construction. -/
theorem reference_modMulCircuitWorkspaceOK
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    ModMulCircuitWorkspaceOK
      (referenceData ops inst η)
      (referenceWork ops inst η) := by
  exact ⟨reference_data_canGrow_two ops inst η,
    reference_work_canGrow_one ops inst η,
    reference_data_work_disjoint ops inst η⟩

/-- The full lowering reserve budget is guaranteed by construction. -/
theorem reference_shorWorkspaceLargeEnough
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    ShorWorkspaceLargeEnough ops
      (referenceX ops inst η)
      (referenceData ops inst η)
      (referenceWork ops inst η) := by
  let need := referenceWorkspaceNeed ops inst η
  have hneed := reference_workspaceNeed_eq ops inst η
  refine ⟨?_, ?_, ?_⟩
  · rw [hneed]
    simp [referenceX, referenceXReserve, ExtReg.capacity,
      referenceXReserveSize]
  · rw [hneed]
    simp [referenceData, referenceDataReserve, ExtReg.capacity,
      referenceDataReserveSize]
  · rw [hneed]
    simp [referenceWork, referenceWorkReserve, ExtReg.capacity,
      referenceWorkReserveSize]

/-- The implementation-specific isolation condition is guaranteed by placement. -/
theorem reference_shorWorkspaceIsolation
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ) :
    ShorWorkspaceIsolation
      (referenceX ops inst η)
      (referenceWork ops inst η)
      (referenceFlag ops inst η) :=
  ⟨reference_exponent_work_disjoint ops inst η,
    reference_flag_outside_exponent ops inst η⟩

/-- The chosen work width satisfies Algorithm 1's precision equation whenever
`η` is in the admissible interval. -/
theorem reference_algorithm1Precision
    {k : ℕ} (ops : Prog k)
    (inst : ShorOrderFindingInstance) (η : ℝ)
    (hηpos : 0 < η)
    (hηhalf : η < (1 / 2 : ℝ)) :
    Algorithm1Precision η
      (referenceData ops inst η).active
      (referenceWork ops inst η).active := by
  refine ⟨hηpos, hηhalf, ?_⟩
  simp [
    referenceData,
    referenceDataActive,
    referenceWork,
    referenceWorkActive,
    referenceDataWidth,
    referenceWorkWidth
  ]
