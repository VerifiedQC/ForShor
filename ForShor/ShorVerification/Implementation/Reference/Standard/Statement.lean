import ForShor.ShorVerification.Implementation.Reference.Contract
import ForShor.ShorVerification.Implementation.Reference.Balanced.Statement

/-!
# Reference: the reference's choices, and the claims

The reference makes every choice the other folders leave open: the precision schedule, the register widths and
reserves, and where the registers sit. From those it builds its circuit, and
`Main.lean` packages the result as `referenceShorImplementation`.

Building the circuit needs the layout's workspace facts, since `Policy.lowerGate`
takes a proof of them. `Ready` states those facts, `referenceShorCircuitOf` builds
the circuit from any proof of them, and `Main.lean` proves them once. The claims
at the end are what `Main.lean` proves.

Everything evaluated by the emitter (widths, reserves, the layout) is computable.
-/

namespace Shor

namespace Reference

/-! ## The precision schedule

The framework exposes a natural-number precision level `m`. The reference turns
it into Algorithm 1's real parameter `η = referencePrecision m`; the width that
parameter forces on the work register is computed directly from `m` by
`algorithm1ExtraBitsNat`, and `algorithm1ExtraBits_referencePrecision`
(`Proofs/Layout.lean`) shows the two agree. -/

/-- The approximation parameter at precision level `m`. The offset by `3` keeps
every level in `0 < η < 1/2`, including `m = 0`, while `η → 0` as `m → ∞`. -/
noncomputable def referencePrecision (m : ℕ) : ℝ :=
  1 / ((m : ℝ) + 3)

/-- The work register's extra bits at precision level `m`, without `Real.logb`. -/
def algorithm1ExtraBitsNat (m : ℕ) : ℕ :=
  Nat.clog 2 ((m + 7) ^ 2) - 2

example : algorithm1ExtraBitsNat 0 = 4 := by decide
example : algorithm1ExtraBitsNat 1 = 4 := by decide

/-! ## Register widths and reserves -/

/-- Active width of the phase-estimation/output register. -/
def referenceXWidth (inst : ShorOrderFindingInstance) : ℕ :=
  Nat.log2 (2 * inst.N^2)

/-- Active width of the modular-data register. -/
def referenceDataWidth (inst : ShorOrderFindingInstance) : ℕ :=
  Nat.log2 (2 * inst.N)

/-- Active width of Algorithm 1's work register. -/
def referenceWorkWidth (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceDataWidth inst + algorithm1ExtraBitsNat m

/-- Active width of the Step-3/4 comparator scratch. -/
def referenceScratchWidth (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  2 + max
    ((referenceDataWidth inst + 1) + referenceWorkWidth inst m)
    (Nat.log2 (inst.N + 1) + 1 + referenceWorkWidth inst m)

/-- A register of width `n` at qubit `0`: a width-only stand-in used to evaluate the
workspace need, whose location is irrelevant. -/
def widthShell (n : ℕ) : ExtReg :=
  ExtReg.ofReg (Reg.interval 0 n)

/-- The phase-product reserve the layout gives a site: enough for the product itself
and for every block of the default rule's split of it. -/
def referenceSiteReserve (P : ShorLoweringPolicy) (wx wz : ℕ) : ℕ × ℕ :=
  (max (Policy.reserveNeed P wx wz).1 (Balanced.siteNeed P Balanced.defaultRule wx wz).1,
   max (Policy.reserveNeed P wx wz).2 (Balanced.siteNeed P Balanced.defaultRule wx wz).2)

/-- The reserve budget of the layout at these widths: the lowerer's
`shorWorkspaceNeed`, with each phase-product site's reserve `referenceSiteReserve`. -/
def referenceWorkspaceNeed (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    ShorWorkspaceNeed :=
  shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (referenceSiteReserve P)
    (widthShell (referenceXWidth inst))
    (widthShell (referenceDataWidth inst))
    (widthShell (referenceWorkWidth inst m))
    (widthShell (referenceScratchWidth inst m))

def referenceXReserveSize (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  (referenceWorkspaceNeed P inst m).exponent

/-- Two bits are additionally guaranteed for Algorithm 1's data growth. -/
def referenceDataReserveSize (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    ℕ :=
  max 2 (referenceWorkspaceNeed P inst m).data

/-- One bit is additionally guaranteed for Algorithm 1's work growth. -/
def referenceWorkReserveSize (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    ℕ :=
  max 1 (referenceWorkspaceNeed P inst m).auxiliary

/-- One reserve bit is guaranteed for the concrete Step-3 subtraction unit. -/
def referenceScratchReserveSize (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (m : ℕ) : ℕ :=
  max 1 (referenceWorkspaceNeed P inst m).scratch

/-! ## Placement

Everything the reference uses sits in one contiguous region from qubit `0`:

```
x active | x reserve | data active | data reserve | work active | work reserve
  | scratch active | scratch reserve | flag
```

Because `ShorImplementation.correct` runs from `RegEncoding.zero`, every qubit the
layout selects is clean in the framework's initial state. -/

/-- The exponent register starts at qubit 0. -/
def referenceXActive (inst : ShorOrderFindingInstance) : Reg :=
  Reg.interval 0 (referenceXWidth inst)

def referenceXReserveStart (inst : ShorOrderFindingInstance) : ℕ :=
  referenceXWidth inst

def referenceDataStart (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceXReserveStart inst + referenceXReserveSize P inst m

def referenceDataReserveStart (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    ℕ :=
  referenceDataStart P inst m + referenceDataWidth inst

def referenceWorkStart (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceDataReserveStart P inst m + referenceDataReserveSize P inst m

def referenceWorkReserveStart (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    ℕ :=
  referenceWorkStart P inst m + referenceWorkWidth inst m

def referenceScratchStart (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceWorkReserveStart P inst m + referenceWorkReserveSize P inst m

def referenceScratchReserveStart (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (m : ℕ) : ℕ :=
  referenceScratchStart P inst m + referenceScratchWidth inst m

def referenceFlag (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : ℕ :=
  referenceScratchReserveStart P inst m + referenceScratchReserveSize P inst m

def referenceXReserve (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : Reg :=
  Reg.interval (referenceXReserveStart inst) (referenceXReserveSize P inst m)

def referenceDataActive (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : Reg :=
  Reg.interval (referenceDataStart P inst m) (referenceDataWidth inst)

def referenceDataReserve (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    Reg :=
  Reg.interval (referenceDataReserveStart P inst m) (referenceDataReserveSize P inst m)

def referenceWorkActive (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : Reg :=
  Reg.interval (referenceWorkStart P inst m) (referenceWorkWidth inst m)

def referenceWorkReserve (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    Reg :=
  Reg.interval (referenceWorkReserveStart P inst m) (referenceWorkReserveSize P inst m)

def referenceScratchActive (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    Reg :=
  Reg.interval (referenceScratchStart P inst m) (referenceScratchWidth inst m)

def referenceScratchReserve (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    Reg :=
  Reg.interval (referenceScratchReserveStart P inst m) (referenceScratchReserveSize P inst m)

/-! ## The registers and the layout -/

lemma mem_interval_bounds {lo size q : ℕ} (hq : q ∈ (Reg.interval lo size).qubits) :
    lo ≤ q ∧ q < lo + size := by
  change q ∈ (List.range size).map (fun i => lo + i) at hq
  rcases List.mem_map.mp hq with ⟨i, hi, hqi⟩
  have hi' : i < size := by simpa using hi
  subst q
  omega

lemma interval_disjoint_of_end_le {lo₁ size₁ lo₂ size₂ : ℕ} (h : lo₁ + size₁ ≤ lo₂) :
    Disjoint (Reg.interval lo₁ size₁) (Reg.interval lo₂ size₂) := by
  rw [Disjoint, List.disjoint_left]
  intro q hq₁ hq₂
  have h₁ := mem_interval_bounds hq₁
  have h₂ := mem_interval_bounds hq₂
  omega

def referenceX (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : ExtReg :=
  ExtReg.withReserve (referenceXActive inst) (referenceXReserve P inst m)
    (interval_disjoint_of_end_le (by simp [referenceXReserveStart]))

def referenceData (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : ExtReg :=
  ExtReg.withReserve (referenceDataActive P inst m) (referenceDataReserve P inst m)
    (interval_disjoint_of_end_le (by simp [referenceDataReserveStart]))

def referenceWork (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : ExtReg :=
  ExtReg.withReserve (referenceWorkActive P inst m) (referenceWorkReserve P inst m)
    (interval_disjoint_of_end_le (by simp [referenceWorkReserveStart]))

def referenceScratch (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : ExtReg :=
  ExtReg.withReserve (referenceScratchActive P inst m) (referenceScratchReserve P inst m)
    (interval_disjoint_of_end_le (by simp [referenceScratchReserveStart]))

/-- The registers the reference circuit runs on. -/
structure ReferenceShorLayout where
  x : ExtReg
  data : ExtReg
  work : ExtReg
  scratch : ExtReg
  flag : ℕ

/-- The layout of an instance at precision level `m`. -/
def allocateReferenceLayout (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    ReferenceShorLayout :=
  { x := referenceX P inst m
    data := referenceData P inst m
    work := referenceWork P inst m
    scratch := referenceScratch P inst m
    flag := referenceFlag P inst m }

/-! ## What the circuit needs of the layout -/

/-- The layout facts the modular multiplication and the Step-4 comparator need. -/
structure LayoutOK (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : Prop where
  modMul : ModMulCircuitWorkspaceOK (referenceData P inst m) (referenceWork P inst m)
  scratch_canGrow : (referenceScratch P inst m).CanGrow 1
  work_scratch_disjoint :
    ExtReg.OwnedDisjoint (referenceWork P inst m) (referenceScratch P inst m)
  data_scratch_disjoint :
    ExtReg.OwnedDisjoint ((referenceData P inst m).grow 1) (referenceScratch P inst m)
  flag_not_data : referenceFlag P inst m ∉ ((referenceData P inst m).grow 1).ownedQubits
  flag_not_work : referenceFlag P inst m ∉ (referenceWork P inst m).ownedQubits
  flag_not_scratch : referenceFlag P inst m ∉ (referenceScratch P inst m).ownedQubits
  scratch_width :
    regSize (referenceScratch P inst m).active =
      cmpLtNWWidth inst.N ((referenceData P inst m).grow 1).active (referenceWork P inst m).active

/-- The comparator's registers, from the layout facts. -/
def LayoutOK.step4Workspace {P : ShorLoweringPolicy} {inst : ShorOrderFindingInstance} {m : ℕ}
    (h : LayoutOK P inst m) :
    CmpLtNWWorkspace inst.N ((referenceData P inst m).grow 1) (referenceWork P inst m)
      (referenceScratch P inst m) (referenceFlag P inst m) where
  data_can_grow := ExtReg.canGrow_grow (n := 1) (k := 1) h.modMul.1
  mulWorkspace :=
    Gate.PhaseProdWorkspace.ofExtRegs (referenceWork P inst m) (referenceScratch P inst m)
      h.modMul.2.1 h.scratch_canGrow h.work_scratch_disjoint
  mul_xReserve_eq := rfl
  mul_zReserve_eq := rfl
  data_work_disjoint := h.modMul.2.2.grow_left 1
  data_scratch_disjoint := h.data_scratch_disjoint
  work_scratch_disjoint := h.work_scratch_disjoint
  flag_not_data := h.flag_not_data
  flag_not_work := h.flag_not_work
  flag_not_scratch := h.flag_not_scratch
  scratch_width := h.scratch_width

/-- The order-finding gate on the layout, from the layout facts. -/
abbrev LayoutOK.gate {P : ShorLoweringPolicy} {inst : ShorOrderFindingInstance} {m : ℕ}
    (h : LayoutOK P inst m) : Gate :=
  orderFindingApprox inst.a inst.N (referenceX P inst m) (referenceData P inst m)
    (referenceWork P inst m) (referenceScratch P inst m) (referenceFlag P inst m)
    h.modMul h.step4Workspace

/-- Everything building the circuit needs: the layout facts and the lowering's
workspace. -/
structure Ready (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) : Prop where
  layout : LayoutOK P inst m
  lowering : Policy.GateWorkspaceOK P layout.gate

/-- The lowered order-finding circuit on the layout, from a proof that it is ready.
By proof irrelevance it does not depend on which proof. -/
def referenceShorCircuitOf {P : ShorLoweringPolicy} {inst : ShorOrderFindingInstance} {m : ℕ}
    (h : Ready P inst m) : LowGate :=
  orderFindingApproxLow P inst.a inst.N (referenceX P inst m) (referenceData P inst m)
    (referenceWork P inst m) (referenceScratch P inst m) (referenceFlag P inst m)
    h.layout.modMul h.layout.step4Workspace h.lowering

/-- The program: the circuit, measuring the exponent register. -/
def referenceProgramOf {P : ShorLoweringPolicy} {inst : ShorOrderFindingInstance} {m : ℕ}
    (h : Ready P inst m) : ShorOrderFindingProgram :=
  { circuit := referenceShorCircuitOf h
    output := (referenceX P inst m).active }

/-! ## The success bound -/

/-- The constant of the modular-exponentiation approximation error.
`Shor_correct_approx_lowered_uniform` proves the lowered bound for some `K ≤ 1600`
(from `Cpe ≤ 512` and `Cstep2 ≤ 2π + 2π²`, which give `K ≤ 1536 + 3π + 3π² ≈ 1575`),
so by monotonicity it holds at `1600` itself. -/
noncomputable def referenceK : ℝ := 1600

/-- The approximation error in the reference's bound at precision level `m`. -/
noncomputable def referenceApproximationErrorAt (m N : ℕ) : ℝ :=
  2 * (regSize (Reg.interval 0 (Nat.log2 (2 * N ^ 2))) : ℝ) *
    Real.sqrt (2 * (referenceK * referencePrecision m))

/-- The single-run success lower bound at precision level `m`, unclamped. -/
noncomputable def referenceRawSuccessProbabilityAt (m N : ℕ) : ℝ :=
  κ / Real.log ((Nat.log2 N : ℝ) + 1) - referenceApproximationErrorAt m N

/-- The declared bound at `m`, clamped to `[0, 1]`. -/
noncomputable def referenceSuccessProbabilityAt (m N : ℕ) : ℝ :=
  max 0 (min 1 (referenceRawSuccessProbabilityAt m N))

open Classical in
/-- The precision level the reference submits at: the least one with a positive
declared bound. `Proofs/Success.lean` shows one exists for every `N ≥ 2`. -/
noncomputable def referenceChosenPrecision (N : ℕ) : ℕ :=
  if h : ∃ m : ℕ, 0 < referenceSuccessProbabilityAt m N then Nat.find h else 0

/-- The single-run success probability the reference declares. -/
noncomputable def referenceSuccessProbability (N : ℕ) : ℝ :=
  if 2 ≤ N then referenceSuccessProbabilityAt (referenceChosenPrecision N) N else 1

open Classical in
/-- The number of trials the reference declares: the least that amplifies the
declared bound to 99%. `Proofs/Success.lean` shows one exists. -/
noncomputable def referenceTrialCount (N : ℕ) : ℕ :=
  if h : ∃ k : ℕ, (99 / 100 : ℝ) ≤ 1 - (1 - referenceSuccessProbability N) ^ k then Nat.find h
  else 0

/-! ## The 2048-bit headline -/

/-- The precision level of the 2048-bit headline: `η = 2⁻¹⁵⁰` exactly. -/
def m2048 : ℕ := 2 ^ 150 - 3

/-- 99% of the ideal baseline `κ / log 2048`: the single-run bound at the headline
level for every 2048-bit modulus. -/
noncomputable def headlineP : ℝ := (99 / 100) * (κ / Real.log (2048 : ℝ))

open Classical in
/-- The number of trials that amplifies `headlineP` to 99%. -/
noncomputable def headlineTrialCount : ℕ :=
  if h : ∃ k : ℕ, (99 / 100 : ℝ) ≤ 1 - (1 - headlineP) ^ k then Nat.find h else 0

/-! ## The claims -/

section

variable (qs : QSemantics) [RegEncoding qs.Basis] [MeasureClass qs] [LowerGateClass qs]

/-- Every instance's layout is ready at every precision level. -/
def ReferenceReady (P : ShorLoweringPolicy) : Prop :=
  ∀ (inst : ShorOrderFindingInstance) (m : ℕ), Ready P inst m

/-- At precision level `m`, the reference program meets the declared bound
`referenceSuccessProbabilityAt m`. -/
def ReferenceSuccessAt (P : ShorLoweringPolicy) (m : ℕ) : Prop :=
  ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
  ∀ (inst : ShorOrderFindingInstance) (h : Ready P inst m),
    referenceSuccessProbabilityAt m inst.N ≤
      probability_of_success
        (qs := qs)
        (evalC := LowerGateClass.evalL (qs := qs))
        (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (referenceProgramOf h).output)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (referenceProgramOf h).output)
        (C := (referenceProgramOf h).circuit)
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis)))

/-- At the chosen precision, the reference program meets the contract's `correct`. -/
def ReferenceCorrect (P : ShorLoweringPolicy) : Prop :=
  ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
  ∀ (inst : ShorOrderFindingInstance) (h : Ready P inst (referenceChosenPrecision inst.N)),
    0 ≤ referenceSuccessProbability inst.N ∧ referenceSuccessProbability inst.N ≤ 1 ∧
    referenceSuccessProbability inst.N ≤
      probability_of_success
        (qs := qs)
        (evalC := LowerGateClass.evalL (qs := qs))
        (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (referenceProgramOf h).output)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (referenceProgramOf h).output)
        (C := (referenceProgramOf h).circuit)
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis)))

/-- The declared trial count amplifies the declared bound to 99%, for every modulus. -/
def ReferenceTrialCount : Prop :=
  ∀ N : ℕ, (99 / 100 : ℝ) ≤ 1 - (1 - referenceSuccessProbability N) ^ referenceTrialCount N

/-- At the headline level, the declared bound is at least 99% of the ideal baseline
for every 2048-bit modulus. -/
def Headline2048 : Prop :=
  ∀ N : ℕ, Is2048Bit N →
    (99 / 100 : ℝ) * (κ / Real.log (2048 : ℝ)) ≤ referenceSuccessProbabilityAt m2048 N

/-- `headlineTrialCount` trials amplify `headlineP` to 99%. -/
def HeadlineTrialCount : Prop :=
  (99 / 100 : ℝ) ≤ 1 - (1 - headlineP) ^ headlineTrialCount

end

end Reference
end Shor
