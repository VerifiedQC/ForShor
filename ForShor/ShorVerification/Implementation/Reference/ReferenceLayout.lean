import ForShor.ShorVerification.Implementation.Shor.Circuit.Workspace
import ForShor.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import ForShor.ShorVerification.Implementation.Shor.Spec.Contract
import ForShor.ShorVerification.Implementation.Reference.ReferencePrecision

namespace Shor
namespace Reference

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
       |-- comparator scratch active
       |-- comparator scratch reserve
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
def referenceWorkWidth
    (inst : ShorOrderFindingInstance)
    (m : ℕ) : ℕ :=
  referenceDataWidth inst + algorithm1ExtraBitsNat m

/-- Active width required by the concrete Step-3/4 comparator scratch. -/
def referenceScratchWidth
    (inst : ShorOrderFindingInstance)
    (m : ℕ) : ℕ :=
  2 + max
    ((referenceDataWidth inst + 1) + referenceWorkWidth inst m)
    (Nat.log2 (inst.N + 1) + 1 + referenceWorkWidth inst m)

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
def referenceWorkspaceNeed
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance)
    (m : ℕ) : ShorWorkspaceNeed :=
  Policy.shorWorkspaceNeed P
    (widthShell (referenceXWidth inst))
    (widthShell (referenceDataWidth inst))
    (widthShell (referenceWorkWidth inst m))
    (widthShell (referenceScratchWidth inst m))

def referenceXReserveSize
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  (referenceWorkspaceNeed P inst m).exponent

/-- Two bits are additionally guaranteed for Algorithm 1's data growth. -/
def referenceDataReserveSize
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  max 2 (referenceWorkspaceNeed P inst m).data

/-- One bit is additionally guaranteed for Algorithm 1's work growth. -/
def referenceWorkReserveSize
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  max 1 (referenceWorkspaceNeed P inst m).auxiliary

/-- One reserve bit is guaranteed for the concrete Step-3 subtraction unit. -/
def referenceScratchReserveSize
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  max 1 (referenceWorkspaceNeed P inst m).scratch

private theorem shorWorkspaceNeed_ext
    {a b : ShorWorkspaceNeed}
    (hexponent : a.exponent = b.exponent)
    (hdata : a.data = b.data)
    (hauxiliary : a.auxiliary = b.auxiliary)
    (hscratch : a.scratch = b.scratch) :
    a = b := by
  cases a with
  | mk ae ad aa as =>
      cases b with
      | mk be bd ba bs =>
          simp at hexponent hdata hauxiliary hscratch
          simp [hexponent, hdata, hauxiliary, hscratch]

/-! =========================================================
    Section 3: Deterministic fresh-region placement
========================================================= -/

/-- The reference implementation starts its exponent register at qubit 0. -/
def referenceXActive (inst : ShorOrderFindingInstance) : Reg :=
  Reg.interval 0 (referenceXWidth inst)

def referenceXReserveStart
    (inst : ShorOrderFindingInstance) : ℕ :=
  referenceXWidth inst

def referenceDataStart
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceXReserveStart inst +
    referenceXReserveSize P inst m

def referenceDataReserveStart
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceDataStart P inst m +
    referenceDataWidth inst

def referenceWorkStart
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceDataReserveStart P inst m +
    referenceDataReserveSize P inst m

def referenceWorkReserveStart
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceWorkStart P inst m +
    referenceWorkWidth inst m

def referenceScratchStart
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceWorkReserveStart P inst m +
    referenceWorkReserveSize P inst m

def referenceScratchReserveStart
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceScratchStart P inst m +
    referenceScratchWidth inst m

def referenceFlag
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceScratchReserveStart P inst m +
    referenceScratchReserveSize P inst m

def referenceXReserve
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : Reg :=
  Reg.interval
    (referenceXReserveStart inst)
    (referenceXReserveSize P inst m)

def referenceDataActive
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : Reg :=
  Reg.interval
    (referenceDataStart P inst m)
    (referenceDataWidth inst)

def referenceDataReserve
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : Reg :=
  Reg.interval
    (referenceDataReserveStart P inst m)
    (referenceDataReserveSize P inst m)

def referenceWorkActive
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : Reg :=
  Reg.interval
    (referenceWorkStart P inst m)
    (referenceWorkWidth inst m)

def referenceWorkReserve
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : Reg :=
  Reg.interval
    (referenceWorkReserveStart P inst m)
    (referenceWorkReserveSize P inst m)

def referenceScratchActive
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : Reg :=
  Reg.interval
    (referenceScratchStart P inst m)
    (referenceScratchWidth inst m)

def referenceScratchReserve
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : Reg :=
  Reg.interval
    (referenceScratchReserveStart P inst m)
    (referenceScratchReserveSize P inst m)

/-! =========================================================
    Section 4: Extended-register construction
========================================================= -/

def referenceX
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ExtReg :=
  ExtReg.withReserve
    (referenceXActive inst)
    (referenceXReserve P inst m)
    (interval_disjoint_of_end_le (by simp [referenceXReserveStart]))

def referenceData
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ExtReg :=
  ExtReg.withReserve
    (referenceDataActive P inst m)
    (referenceDataReserve P inst m)
    (interval_disjoint_of_end_le (by
      simp [referenceDataReserveStart]))

def referenceWork
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ExtReg :=
  ExtReg.withReserve
    (referenceWorkActive P inst m)
    (referenceWorkReserve P inst m)
    (interval_disjoint_of_end_le (by
      simp [referenceWorkReserveStart]))

def referenceScratch
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) : ExtReg :=
  ExtReg.withReserve
    (referenceScratchActive P inst m)
    (referenceScratchReserve P inst m)
    (interval_disjoint_of_end_le (by
      simp [referenceScratchReserveStart]))


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
  scratch : ExtReg
  flag : ℕ

/--
Allocate all reference-implementation storage deterministically above the public
register file.
-/
def allocateReferenceLayout
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance)
    (m : ℕ) : ReferenceShorLayout :=
  {
    x := referenceX P inst m
    data := referenceData P inst m
    work := referenceWork P inst m
    scratch := referenceScratch P inst m
    flag := referenceFlag P inst m
  }

/-! =========================================================
    Section 5: Basic shape facts
========================================================= -/

@[simp] theorem allocateReferenceLayout_x_active
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    (allocateReferenceLayout P inst m).x.active =
      referenceXActive inst := by
  rfl

@[simp] theorem allocateReferenceLayout_x_width
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    regSize (allocateReferenceLayout P inst m).x.active =
      Nat.log2 (2 * inst.N^2) := by
  simp [allocateReferenceLayout, referenceX,
    referenceXActive, referenceXWidth]

@[simp] theorem allocateReferenceLayout_data_width
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    regSize (allocateReferenceLayout P inst m).data.active =
      Nat.log2 (2 * inst.N) := by
  simp [allocateReferenceLayout, referenceData,
    referenceDataActive, referenceDataWidth]

@[simp] theorem allocateReferenceLayout_work_width
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    regSize (allocateReferenceLayout P inst m).work.active =
      referenceDataWidth inst + algorithm1ExtraBitsNat m := by
  simp [allocateReferenceLayout, referenceWork,
    referenceWorkActive, referenceWorkWidth]

@[simp] theorem allocateReferenceLayout_scratch_width
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    regSize (allocateReferenceLayout P inst m).scratch.active =
      referenceScratchWidth inst m := by
  simp [allocateReferenceLayout, referenceScratch,
    referenceScratchActive]

@[simp] theorem allocateReferenceLayout_x_capacity
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    (allocateReferenceLayout P inst m).x.capacity =
      referenceXReserveSize P inst m := by
  simp [allocateReferenceLayout, referenceX, referenceXReserve,
    ExtReg.capacity]

@[simp] theorem allocateReferenceLayout_data_capacity
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    (allocateReferenceLayout P inst m).data.capacity =
      referenceDataReserveSize P inst m := by
  simp [allocateReferenceLayout, referenceData, referenceDataReserve,
    ExtReg.capacity]

@[simp] theorem allocateReferenceLayout_work_capacity
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    (allocateReferenceLayout P inst m).work.capacity =
      referenceWorkReserveSize P inst m := by
  simp [allocateReferenceLayout, referenceWork, referenceWorkReserve,
    ExtReg.capacity]

@[simp] theorem allocateReferenceLayout_scratch_capacity
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    (allocateReferenceLayout P inst m).scratch.capacity =
      referenceScratchReserveSize P inst m := by
  simp [allocateReferenceLayout, referenceScratch, referenceScratchReserve,
    ExtReg.capacity]

/-! =========================================================
    Section 6: Ordered-region bounds
========================================================= -/

private lemma referenceX_owned_lt_dataStart
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ)
    {q : ℕ}
    (hq : q ∈ (referenceX P inst m).ownedQubits) :
    q < referenceDataStart P inst m := by
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
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ)
    {q : ℕ}
    (hq : q ∈ (referenceData P inst m).ownedQubits) :
    referenceDataStart P inst m ≤ q := by
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
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ)
    {q : ℕ}
    (hq : q ∈ (referenceWork P inst m).ownedQubits) :
    referenceWorkStart P inst m ≤ q := by
  simp only [referenceWork, ExtReg.ownedQubits, ExtReg.withReserve,
    List.mem_append] at hq
  rcases hq with hactive | hreserve
  · exact (mem_interval_bounds hactive).1
  · have hge := (mem_interval_bounds hreserve).1
    unfold referenceWorkReserveStart at hge
    omega

private lemma referenceWork_owned_lt_scratchStart
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ)
    {q : ℕ}
    (hq : q ∈ (referenceWork P inst m).ownedQubits) :
    q < referenceScratchStart P inst m := by
  simp only [referenceWork, ExtReg.ownedQubits, ExtReg.withReserve,
    List.mem_append] at hq
  rcases hq with hactive | hreserve
  · have hlt := (mem_interval_bounds hactive).2
    unfold referenceScratchStart referenceWorkReserveStart
    omega
  · have hlt := (mem_interval_bounds hreserve).2
    simpa [referenceWorkReserve, referenceScratchStart] using hlt

private lemma referenceScratch_owned_ge_scratchStart
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ)
    {q : ℕ}
    (hq : q ∈ (referenceScratch P inst m).ownedQubits) :
    referenceScratchStart P inst m ≤ q := by
  simp only [referenceScratch, ExtReg.ownedQubits, ExtReg.withReserve,
    List.mem_append] at hq
  rcases hq with hactive | hreserve
  · exact (mem_interval_bounds hactive).1
  · have hge := (mem_interval_bounds hreserve).1
    unfold referenceScratchReserveStart at hge
    omega

private lemma referenceScratch_owned_lt_flag
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ)
    {q : ℕ}
    (hq : q ∈ (referenceScratch P inst m).ownedQubits) :
    q < referenceFlag P inst m := by
  simp only [referenceScratch, ExtReg.ownedQubits, ExtReg.withReserve,
    List.mem_append] at hq
  rcases hq with hactive | hreserve
  · have hlt := (mem_interval_bounds hactive).2
    unfold referenceFlag referenceScratchReserveStart
    omega
  · have hlt := (mem_interval_bounds hreserve).2
    simpa [referenceScratchReserve, referenceFlag] using hlt

/-! =========================================================
    Section 7: Static layout facts supplied by the allocator
========================================================= -/

/-- The allocated exponent and data storage are completely ownership-disjoint. -/
theorem reference_exponent_data_disjoint
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    ExtReg.OwnedDisjoint
      (referenceX P inst m)
      (referenceData P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hx hy
  have hlt := referenceX_owned_lt_dataStart P inst m hx
  have hge := referenceData_owned_ge_dataStart P inst m hy
  omega

private lemma referenceX_owned_lt_workStart
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ)
    {q : ℕ}
    (hq : q ∈ (referenceX P inst m).ownedQubits) :
    q < referenceWorkStart P inst m := by
  have hlt :=
    referenceX_owned_lt_dataStart P inst m hq
  unfold referenceWorkStart referenceDataReserveStart
  omega

private lemma referenceData_owned_lt_workStart
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ)
    {q : ℕ}
    (hq : q ∈ (referenceData P inst m).ownedQubits) :
    q < referenceWorkStart P inst m := by
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
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    ExtReg.OwnedDisjoint
      (referenceData P inst m)
      (referenceWork P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hdata hwork
  have hlt := referenceData_owned_lt_workStart P inst m hdata
  have hge := referenceWork_owned_ge_workStart P inst m hwork
  omega

/-- The exponent register and all work storage are ownership-disjoint. -/
theorem reference_exponent_work_disjoint
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    ExtReg.OwnedDisjoint
      (referenceX P inst m)
      (referenceWork P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hx hwork
  have hxlt :=
    referenceX_owned_lt_workStart P inst m hx
  have hworkge :=
    referenceWork_owned_ge_workStart P inst m hwork
  omega

/-- The exponent register and comparator scratch are ownership-disjoint. -/
theorem reference_exponent_scratch_disjoint
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    ExtReg.OwnedDisjoint
      (referenceX P inst m)
      (referenceScratch P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hx hscratch
  have hxlt := referenceX_owned_lt_workStart P inst m hx
  have hscratchge :=
    referenceScratch_owned_ge_scratchStart P inst m hscratch
  unfold referenceScratchStart referenceWorkReserveStart at hscratchge
  omega

/-- The data register and comparator scratch are ownership-disjoint. -/
theorem reference_data_scratch_disjoint
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    ExtReg.OwnedDisjoint
      (referenceData P inst m)
      (referenceScratch P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hdata hscratch
  have hdlt := referenceData_owned_lt_workStart P inst m hdata
  have hscratchge :=
    referenceScratch_owned_ge_scratchStart P inst m hscratch
  unfold referenceScratchStart referenceWorkReserveStart at hscratchge
  omega

/-- The work register and comparator scratch are ownership-disjoint. -/
theorem reference_work_scratch_disjoint
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    ExtReg.OwnedDisjoint
      (referenceWork P inst m)
      (referenceScratch P inst m) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hwork hscratch
  have hlt := referenceWork_owned_lt_scratchStart P inst m hwork
  have hge := referenceScratch_owned_ge_scratchStart P inst m hscratch
  omega

/-- The flag is outside all exponent-owned qubits. -/
theorem reference_flag_outside_exponent
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    referenceFlag P inst m ∉ (referenceX P inst m).ownedQubits := by
  intro hflag
  have hlt := referenceX_owned_lt_workStart P inst m hflag
  have hge :
      referenceWorkStart P inst m ≤ referenceFlag P inst m := by
    unfold referenceFlag referenceScratchReserveStart referenceScratchStart
      referenceWorkReserveStart
    omega
  omega

/-- The flag is outside all data-owned qubits. -/
theorem reference_flag_outside_data
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    referenceFlag P inst m ∉ (referenceData P inst m).ownedQubits := by
  intro hflag
  have hlt := referenceData_owned_lt_workStart P inst m hflag
  have hge :
      referenceWorkStart P inst m ≤ referenceFlag P inst m := by
    unfold referenceFlag referenceScratchReserveStart referenceScratchStart
      referenceWorkReserveStart
    omega
  omega

/-- The flag is outside all work-owned qubits. -/
theorem reference_flag_outside_work
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    referenceFlag P inst m ∉ (referenceWork P inst m).ownedQubits := by
  intro hflag
  have hlt := referenceWork_owned_lt_scratchStart P inst m hflag
  unfold referenceFlag referenceScratchReserveStart at *
  omega

/-- The flag is outside all comparator-scratch-owned qubits. -/
theorem reference_flag_outside_scratch
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    referenceFlag P inst m ∉
      (referenceScratch P inst m).ownedQubits := by
  intro hflag
  have hlt := referenceScratch_owned_lt_flag P inst m hflag
  omega

/-- Every active exponent/control qubit is outside the work register. -/
theorem reference_controls_outside_work
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    ∀ q ∈ (referenceX P inst m).active.qubits,
      q ∉ (referenceWork P inst m).ownedQubits := by
  intro q hq hwork
  have hxOwned : q ∈ (referenceX P inst m).ownedQubits := by
    rw [ExtReg.ownedQubits, List.mem_append]
    exact Or.inl hq
  exact reference_exponent_work_disjoint P inst m hxOwned hwork

/-- The comparison flag is not an active exponent/control qubit. -/
theorem reference_flag_outside_controls
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    referenceFlag P inst m ∉
      (referenceX P inst m).active.qubits := by
  intro hctrl
  apply reference_flag_outside_exponent P inst m
  rw [ExtReg.ownedQubits, List.mem_append]
  exact Or.inl hctrl

/-! =========================================================
    Section 8: Workspace and precision facts
========================================================= -/

/-- The final allocated registers have the same width-based Shor reserve need
as the shells used to size them. -/
theorem reference_workspaceNeed_eq
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    Policy.shorWorkspaceNeed P
      (referenceX P inst m)
      (referenceData P inst m)
      (referenceWork P inst m)
      (referenceScratch P inst m)
      =
    referenceWorkspaceNeed P inst m := by
  apply shorWorkspaceNeed_ext <;>
    simp only [
      Policy.shorWorkspaceNeed,
      shorWorkspaceNeedOf,
      qftReserveNeedOf,
      referenceWorkspaceNeed,
      widthShell,
      referenceX,
      referenceXActive,
      referenceData,
      referenceDataActive,
      referenceWork,
      referenceWorkActive,
      referenceScratch,
      referenceScratchActive,
      referenceXWidth,
      referenceDataWidth,
      referenceWorkWidth,
      referenceScratchWidth,
      ExtReg.width,
      ExtReg.ofReg,
      withReserve_active,
      regSize_interval
    ]
/-- The data reserve always supports the two temporary Algorithm 1 growth bits. -/
theorem reference_data_canGrow_two
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    (referenceData P inst m).CanGrow 2 := by
  simp [ExtReg.CanGrow, referenceData, referenceDataReserve,
    ExtReg.capacity, referenceDataReserveSize]

/-- The work reserve always supports Algorithm 1's temporary growth bit. -/
theorem reference_work_canGrow_one
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    (referenceWork P inst m).CanGrow 1 := by
  simp [ExtReg.CanGrow, referenceWork, referenceWorkReserve,
    ExtReg.capacity, referenceWorkReserveSize]

/-- The scratch reserve supports the unit bit borrowed by concrete Step 3. -/
theorem reference_scratch_canGrow_one
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    (referenceScratch P inst m).CanGrow 1 := by
  simp [ExtReg.CanGrow, referenceScratch, referenceScratchReserve,
    ExtReg.capacity, referenceScratchReserveSize]

/-- Static modular-multiplication workspace is guaranteed by construction. -/
theorem reference_modMulCircuitWorkspaceOK
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    ModMulCircuitWorkspaceOK
      (referenceData P inst m)
      (referenceWork P inst m) := by
  exact ⟨reference_data_canGrow_two P inst m,
    reference_work_canGrow_one P inst m,
    reference_data_work_disjoint P inst m⟩

/-- The concrete comparator workspace is guaranteed by the fresh interval layout. -/
def reference_step4Workspace
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    CmpLtNWWorkspace
      inst.N
      ((referenceData P inst m).grow 1)
      (referenceWork P inst m)
      (referenceScratch P inst m)
      (referenceFlag P inst m) := by
  have hmod := reference_modMulCircuitWorkspaceOK P inst m
  have hscratchGrow := reference_scratch_canGrow_one P inst m
  have hworkScratch := reference_work_scratch_disjoint P inst m
  refine
    {
      data_can_grow := hmod.dataCarry_canGrow_one
      mulWorkspace :=
        Gate.PhaseProdWorkspace.ofExtRegs
          (referenceWork P inst m)
          (referenceScratch P inst m)
          hmod.work_canGrow_one
          hscratchGrow
          hworkScratch
      mul_xReserve_eq := rfl
      mul_zReserve_eq := rfl
      data_work_disjoint := hmod.dataCarry_work_disjoint
      data_scratch_disjoint := ?_
      work_scratch_disjoint := hworkScratch
      flag_not_data := ?_
      flag_not_work := reference_flag_outside_work P inst m
      flag_not_scratch := reference_flag_outside_scratch P inst m
      scratch_width := ?_
    }
  · simpa [ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow] using
      reference_data_scratch_disjoint P inst m
  · simpa [Gate.ExtReg.ownedQubits_grow] using
      reference_flag_outside_data P inst m
  · have hdataGrowWidth :
        ((referenceData P inst m).grow 1).width =
          referenceDataWidth inst + 1 := by
      rw [ExtReg.width_grow _ 1 hmod.data_canGrow_one]
      simp [referenceData, referenceDataActive, ExtReg.width]
    have hworkWidth :
        (referenceWork P inst m).width =
          referenceWorkWidth inst m := by
      simp [referenceWork, referenceWorkActive, ExtReg.width]
    rw [show
      regSize (referenceScratch P inst m).active =
        referenceScratchWidth inst m by
      simp [referenceScratch, referenceScratchActive]]
    unfold cmpLtNWWidth
    change referenceScratchWidth inst m =
      2 + max
        (((referenceData P inst m).grow 1).width +
          (referenceWork P inst m).width)
        (Nat.log2 (inst.N + 1) + 1 +
          (referenceWork P inst m).width)
    rw [hdataGrowWidth, hworkWidth]
    rfl

/-- The full P reserve budget is guaranteed by construction. -/
theorem reference_shorWorkspaceLargeEnough
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    Policy.ShorWorkspaceLargeEnough P
      (referenceX P inst m)
      (referenceData P inst m)
      (referenceWork P inst m)
      (referenceScratch P inst m) := by
  let need := referenceWorkspaceNeed P inst m
  have hneed := reference_workspaceNeed_eq P inst m
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hneed]
    simp [referenceX, referenceXReserve, ExtReg.capacity,
      referenceXReserveSize]
  · rw [hneed]
    simp [referenceData, referenceDataReserve, ExtReg.capacity,
      referenceDataReserveSize]
  · rw [hneed]
    simp [referenceWork, referenceWorkReserve, ExtReg.capacity,
      referenceWorkReserveSize]
  · rw [hneed]
    simp [referenceScratch, referenceScratchReserve, ExtReg.capacity,
      referenceScratchReserveSize]

/-- The implementation-specific isolation condition is guaranteed by placement. -/
theorem reference_shorWorkspaceIsolation
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    ShorWorkspaceIsolation
      (referenceX P inst m)
      (referenceWork P inst m)
      (referenceScratch P inst m)
      (referenceFlag P inst m) :=
  ⟨reference_exponent_work_disjoint P inst m,
    reference_exponent_scratch_disjoint P inst m,
    reference_flag_outside_exponent P inst m⟩

/-- The chosen work width satisfies Algorithm 1's precision equation at every
reference precision level `m`. -/
theorem reference_algorithm1Precision
    (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (m : ℕ) :
    Algorithm1Precision (referencePrecision m)
      (referenceData P inst m).active
      (referenceWork P inst m).active := by
  refine ⟨referencePrecision_pos m, referencePrecision_lt_half m, ?_⟩
  simp [
    referenceData,
    referenceDataActive,
    referenceWork,
    referenceWorkActive,
    referenceDataWidth,
    referenceWorkWidth,
    algorithm1ExtraBits_referencePrecision
  ]
