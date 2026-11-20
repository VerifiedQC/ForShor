import ForShor.ShorVerification.Implementation.Readout.Proofs.LowLocality
import ForShor.ShorVerification.Implementation.Readout.Proofs.LowerSupport

/-!
# Readout: low-gate locality of the lowered semiclassical circuit

`Proofs/LowLocality.lean` proves that a lowered program `P : MLowGate` does not see a qubit
outside its low support `P.lowSupport` (the footprints `LowGate.lowFootprint` of its unitary
parts and the measured / phase qubits), for ANY start state and with no hypothesis on the
program. Here: what that support is for `orderFindingSemiclassicalLow`.

## Can the support be bounded by names?

Only outside the lowered QFT and phase-product blocks. `lowerGate_lowFootprint_subset`: every
qubit in the footprint of `Policy.lowerGate P G h` is named by `G` (`Gate.qubitSupport`, owned
qubits of the `ExtReg` operands, reserves included), or lies in `Gate.qftPhaseFoot P G h`, the
footprint of the lowered QFT and phase-product blocks of `G` themselves. The constant
comparison and subtraction blocks are bounded by their operands
(`cmpGe_lowFootprint_subset`, `cSub_lowFootprint_subset`). `qftPhaseFoot` is, by definition,
the footprint of those blocks, so for them the inclusion says nothing beyond "a block uses the
qubits it uses": it is NOT a list of names. The existing development does not bound them
either: `Gate.qftPhaseReach` is the same residual for the walk's `QubitCount.reach`, and the
peak walk (`QubitCount.lower_walk`, `sAfter`, `SFact`) treats each block as opaque — it
records the live set before and after the block (`sAfter (QFT r) = L \ firstOf (qftXWork P r)`,
`sAfter (SignedPhaseProd …) = L`) and the block's peak as a NUMBER (`Rec.qftPeak`,
`Rec.ppPeak`), never the names of the qubits inside. Bounding them by names would need a new
induction over the recursive plans (`lowerQFTPlan`, `lowerGateRec`), not done here.

**Update (B4).** The residual IS bounded by names in `Proofs/LowFootprintNamed.lean`
(`qftPhaseFoot_subset`: `Gate.qftPhaseFoot P G h ⊆ G.qubitSupport`, by induction over valid
phase-product plans and the QFT plan), so the hypothesis `q ∉ MGate.qftPhaseFoot` below follows
from `q ∉ semiclassicalQubits`; the hypothesis-free forms are in `LowLocalityNamed.lean`.

## What is proved for the lowered circuit

`semiclassical_lowSupport_subset`: `(orderFindingSemiclassicalLow …).lowSupport ⊆
semiclassicalQubits c y work scratch flag ∪ MGate.qftPhaseFoot P … hws`. Hence, for a qubit
`q` outside `semiclassicalQubits` AND outside `MGate.qftPhaseFoot` (the second hypothesis is
about the actual qubits the lowered blocks name, not a named set), the lowered circuit's record
distribution does not see `q`, for ANY start state:
`orderFindingSemiclassicalLow_recordProb_init_X`, `…_recordProb_of_agree'`,
`…_recordProb_decomp`, `…_recordProb_superpose'`. Compared with the existing lowered results
(`orderFindingSemiclassicalLow_recordProb_of_agree`, `…_superpose`, through
`semiclassical_lowerM_eval`): no admissibility, no layout, no clean-workspace or zero-scratch
hypothesis on the start ket, any start state (the decomposition was not stated at the lowered
level before); but the extra hypothesis `q ∉ MGate.qftPhaseFoot` replaces nothing named: it is
the honest low-level statement (locality relative to what the lowered program names).

Also: `LowGate.lowFootprint_subset_used_reach`: the footprint is inside the union of the two
existing qubit sets, `usedQubits` and the walk's `QubitCount.reach`.
-/

namespace Shor

open QubitCount

/-- The footprint is inside the used qubits of the peak walk and the walk's reach. -/
theorem LowGate.lowFootprint_subset_used_reach (g : LowGate) :
    g.lowFootprint ⊆ g.usedQubits ∪ QubitCount.reach g := by
  induction g with
  | seq U V ihU ihV =>
    intro q hq
    simp only [LowGate.lowFootprint, LowGate.usedQubits, QubitCount.reach, Finset.mem_union] at hq ⊢
    rcases hq with hq | hq
    · rcases Finset.mem_union.mp (ihU hq) with h | h <;> tauto
    · rcases Finset.mem_union.mp (ihV hq) with h | h <;> tauto
  | adj U ih => exact ih
  | signDealloc r n =>
    intro q hq
    simp only [LowGate.lowFootprint, extRegGrowQubits, ExtReg.grow, Reg.append, List.mem_toFinset,
      List.mem_append] at hq
    simp only [LowGate.usedQubits, QubitCount.reach, allocBits, Finset.mem_union, List.mem_toFinset,
      mem_regQubitSet]
    exact hq
  | zeroDealloc r n => intro q hq; simp [LowGate.lowFootprint] at hq
  | _ => exact Finset.subset_union_left

/-- The footprint of the lowered QFT and phase-product blocks of `G` (the residual of
`lowerGate_lowFootprint_subset`; by definition the blocks' own footprint, NOT a named set). -/
def Gate.qftPhaseFoot (P : ShorLoweringPolicy) : (G : Gate) → Policy.GateWorkspaceOK P G → Finset ℕ
  | .seq U V, h => Gate.qftPhaseFoot P U h.1 ∪ Gate.qftPhaseFoot P V h.2
  | .adj U, h => Gate.qftPhaseFoot P U h
  | .QFT r, h => (Policy.lowerQFT P r h).lowFootprint
  | .SignedPhaseProd phi x z, _ => (Policy.lowerSignedPhaseProd P phi x z).lowFootprint
  | .CSignedPhaseProd ctrl phi x z, _ => (Policy.lowerCSignedPhaseProd P ctrl phi x z).lowFootprint
  | _, _ => ∅

/-- `Gate.qftPhaseFoot` over the unitary parts of a measurement-language program. -/
def MGate.qftPhaseFoot (P : ShorLoweringPolicy) : (g : MGate) → MGate.WorkspaceOK P g → Finset ℕ
  | .unitary u, h => Gate.qftPhaseFoot P u h
  | .seq a b, h => MGate.qftPhaseFoot P a h.1 ∪ MGate.qftPhaseFoot P b h.2
  | .measureReset _, _ => ∅
  | .ffPhase _ _, _ => ∅

namespace Readout

/-! ## The constant-arithmetic blocks stay in their operands -/

theorem mem_owned_of_grow' {e : ExtReg} {n q : ℕ} (h : q ∈ extRegGrowQubits e n) :
    q ∈ e.ownedQubits := by
  simp only [extRegGrowQubits, List.mem_toFinset] at h
  rw [← Gate.ExtReg.ownedQubits_grow e n]
  exact List.mem_append_left _ h

theorem unit_mem_owned' (s : ExtReg) (h : s.CanGrow 1) :
    constArithmeticUnitQubit s h ∈ s.ownedQubits := by
  have hm : constArithmeticUnitQubit s h ∈ allocBits s 1 := by
    rw [allocBits_one_eq s h]; exact Finset.mem_singleton_self _
  exact List.mem_append_right _ ((mem_regQubitSet).mp (allocBits_subset_reserve s 1 hm))

theorem lowFootprint_copyBitPowers (dst : ExtReg) (ctrl : ℕ) :
    ∀ bits : List ℕ, (lowerCopyBitPowers dst ctrl bits).lowFootprint
      ⊆ insert ctrl (regQubitSet dst.active) := by
  intro bits
  induction bits with
  | nil => simp [lowerCopyBitPowers, LowGate.lowFootprint]
  | cons i bits ih =>
      unfold lowerCopyBitPowers
      split
      · intro q hq
        simp only [LowGate.lowFootprint, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton] at hq
        rcases hq with (rfl | rfl) | hq
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem ((mem_regQubitSet).mpr (List.get_mem _ _))
        · exact ih hq
      · exact ih

private theorem coe_sub {A : Finset ℕ} {S : Set ℕ} (h : ∀ q ∈ A, q ∈ S) : (↑A : Set ℕ) ⊆ S :=
  fun q hq => h q hq

/-- **The lowered comparison's footprint stays in its operands.** -/
theorem cmpGe_lowFootprint_subset (N : ℕ) (d s : ExtReg) (f : ℕ)
    (h : ConstArithmeticWorkspace N d s f) :
    (↑(lowerCmpGeConst N d s f h).lowFootprint : Set ℕ) ⊆ (Gate.CmpGeConst N d s f).qubitSupport := by
  set S := (Gate.CmpGeConst N d s f).qubitSupport with hS
  have hSd : ∀ q, q ∈ d.ownedQubits → q ∈ S := fun q h => Or.inl h
  have hSs : ∀ q, q ∈ s.ownedQubits → q ∈ S := fun q h => Or.inr (Or.inl h)
  have hSf : f ∈ S := Or.inr (Or.inr rfl)
  have hu := hSs _ (unit_mem_owned' s h.scratch_can_grow)
  have hcp : (↑(lowerCopyBitPowers s (constArithmeticUnitQubit s h.scratch_can_grow)
      N.bitIndices).lowFootprint : Set ℕ) ⊆ S := coe_sub fun q hq => by
    rcases Finset.mem_insert.mp (lowFootprint_copyBitPowers _ _ _ hq) with rfl | h'
    · exact hu
    · exact hSs _ (List.mem_append_left _ ((mem_regQubitSet).mp h'))
  have hsA : (↑(extRegActiveQubits s) : Set ℕ) ⊆ S := coe_sub fun q hq =>
    hSs _ (List.mem_append_left _ (List.mem_toFinset.mp hq))
  have hdG : (↑(extRegGrowQubits d 1) : Set ℕ) ⊆ S := coe_sub fun q hq =>
    hSd _ (mem_owned_of_grow' hq)
  simp only [lowerCmpGeConst, lowerPrepareNegConst, lowerCopyConstFromUnit, LowGate.lowFootprint,
    Finset.coe_union, Set.union_subset_iff, Finset.coe_insert, Finset.coe_singleton,
    Set.insert_subset_iff, Set.singleton_subset_iff, Finset.coe_empty, Set.empty_subset,
    and_true]
  repeat' apply And.intro
  all_goals first
    | exact hu | exact hcp | exact hsA | exact hdG | exact hSf
    | exact hSs _ (List.mem_append_left _ (List.get_mem _ _))

/-- **The lowered controlled subtraction's footprint stays in its operands.** -/
theorem cSub_lowFootprint_subset (N : ℕ) (d s : ExtReg) (f : ℕ)
    (h : ConstArithmeticWorkspace N d s f) :
    (↑(lowerCSubConst N d s f h).lowFootprint : Set ℕ) ⊆ (Gate.CSubConst N d s f).qubitSupport := by
  set S := (Gate.CSubConst N d s f).qubitSupport with hS
  have hSd : ∀ q, q ∈ d.ownedQubits → q ∈ S := fun q h => Or.inl h
  have hSs : ∀ q, q ∈ s.ownedQubits → q ∈ S := fun q h => Or.inr (Or.inl h)
  have hSf : f ∈ S := Or.inr (Or.inr rfl)
  have hu := hSs _ (unit_mem_owned' s h.scratch_can_grow)
  have hcp : (↑(lowerCopyBitPowers s (constArithmeticUnitQubit s h.scratch_can_grow)
      N.bitIndices).lowFootprint : Set ℕ) ⊆ S := coe_sub fun q hq => by
    rcases Finset.mem_insert.mp (lowFootprint_copyBitPowers _ _ _ hq) with rfl | h'
    · exact hu
    · exact hSs _ (List.mem_append_left _ ((mem_regQubitSet).mp h'))
  have hsA : (↑(extRegActiveQubits s) : Set ℕ) ⊆ S := coe_sub fun q hq =>
    hSs _ (List.mem_append_left _ (List.mem_toFinset.mp hq))
  have hdA : (↑(extRegActiveQubits d) : Set ℕ) ⊆ S := coe_sub fun q hq =>
    hSd _ (List.mem_append_left _ (List.mem_toFinset.mp hq))
  simp only [lowerCSubConst, lowerCopyConstFromUnit, LowGate.lowFootprint,
    Finset.coe_union, Set.union_subset_iff, Finset.coe_insert, Finset.coe_singleton,
    Set.insert_subset_iff, Set.singleton_subset_iff]
  repeat' apply And.intro
  all_goals first
    | exact hu | exact hcp | exact hsA | exact hdA | exact hSf

/-! ## Outside the QFT and phase-product blocks, the footprint is named -/

/-- **Outside its QFT and phase-product blocks, the lowering's footprint is named.** -/
theorem lowerGate_lowFootprint_subset (P : ShorLoweringPolicy) :
    ∀ (G : Gate) (h : Policy.GateWorkspaceOK P G),
      (↑(Policy.lowerGate P G h).lowFootprint : Set ℕ) ⊆ G.qubitSupport ∪ ↑(Gate.qftPhaseFoot P G h) := by
  have hown : ∀ (e : ExtReg) (q : ℕ), q ∈ e.active.qubits → q ∈ e.ownedQubits :=
    fun e q h => List.mem_append_left _ h
  intro G
  induction G with
  | id => intro _; simp [Policy.lowerGate, LowGate.lowFootprint]
  | seq U V ihU ihV =>
      intro h q hq
      simp only [Policy.lowerGate, LowGate.lowFootprint, Finset.coe_union, Set.mem_union] at hq
      rcases hq with hq | hq
      · rcases ihU h.1 hq with h1 | h1
        · exact Or.inl (Or.inl h1)
        · exact Or.inr (Finset.mem_union_left _ h1)
      · rcases ihV h.2 hq with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr (Finset.mem_union_right _ h1)
  | adj U ih => intro h; exact ih h
  | H _ | X _ =>
      intro _ q hq
      simp only [Policy.lowerGate, LowGate.lowFootprint, Finset.coe_singleton] at hq
      exact Or.inl hq
  | CNOT a b =>
      intro _ q hq
      simp only [Policy.lowerGate, LowGate.lowFootprint, Finset.coe_insert,
        Finset.coe_singleton] at hq
      exact Or.inl hq
  | Toffoli a b t =>
      intro _ q hq
      simp only [Policy.lowerGate, LowGate.lowFootprint, Finset.coe_insert,
        Finset.coe_singleton] at hq
      exact Or.inl hq
  | QFT r => intro h q hq; exact Or.inr hq
  | SignedPhaseProd phi x z => intro h q hq; exact Or.inr hq
  | CSignedPhaseProd ctrl phi x z => intro h q hq; exact Or.inr hq
  | CmpGeConst N d s f => intro h q hq; exact Or.inl (cmpGe_lowFootprint_subset N d s f h hq)
  | CSubConst N d s f => intro h q hq; exact Or.inl (cSub_lowFootprint_subset N d s f h hq)
  | RadixReverse r m =>
      intro _ q hq
      simp only [Policy.lowerGate, LowGate.lowFootprint, Finset.mem_coe, List.mem_toFinset] at hq
      exact Or.inl hq
  | ShiftL r n | ShiftR r n | Negate r =>
      intro _ q hq
      simp only [Policy.lowerGate, LowGate.lowFootprint, extRegActiveQubits,
        Finset.mem_coe, List.mem_toFinset] at hq
      exact Or.inl (hown r q hq)
  | AddScaled d s b n =>
      intro _ q hq
      simp only [Policy.lowerGate, LowGate.lowFootprint, extRegActiveQubits,
        Finset.coe_union, Set.mem_union, Finset.mem_coe, List.mem_toFinset] at hq
      rcases hq with hq | hq
      · exact Or.inl (Or.inl (hown d q hq))
      · exact Or.inl (Or.inr (hown s q hq))
  | zeroExtend r n | signExtend r n | signDealloc r n =>
      intro _ q hq
      exact Or.inl (mem_owned_of_grow' hq)
  | zeroDealloc r n =>
      intro _ q hq
      simp [Policy.lowerGate, LowGate.lowFootprint] at hq
  | idealCtrlModMul _ _ _ _ => intro h; exact h.elim

/-- `lowerGate_lowFootprint_subset` for the measurement language. -/
theorem lowerM_lowSupport_subset (P : ShorLoweringPolicy) :
    ∀ (g : MGate) (h : MGate.WorkspaceOK P g),
      (↑(Policy.lowerM P g h).lowSupport : Set ℕ)
        ⊆ g.qubitSupport ∪ ↑(MGate.qftPhaseFoot P g h) := by
  intro g
  induction g with
  | unitary u => intro h; exact lowerGate_lowFootprint_subset P u h
  | seq a b iha ihb =>
      intro h q hq
      simp only [Policy.lowerM, Policy.lowerMWith, MLowGate.lowSupport, Finset.coe_union,
        Set.mem_union] at hq
      rcases hq with hq | hq
      · rcases iha h.1 hq with h1 | h1
        · exact Or.inl (Or.inl h1)
        · exact Or.inr (Finset.mem_union_left _ h1)
      · rcases ihb h.2 hq with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr (Finset.mem_union_right _ h1)
  | measureReset q =>
      intro _ q' hq
      simp only [Policy.lowerM, Policy.lowerMWith, MLowGate.lowSupport, Finset.coe_singleton] at hq
      exact Or.inl hq
  | ffPhase q j =>
      intro _ q' hq
      simp only [Policy.lowerM, Policy.lowerMWith, MLowGate.lowSupport, Finset.coe_singleton] at hq
      exact Or.inl hq

/-- **The low support of the lowered semiclassical circuit.** -/
theorem semiclassical_lowSupport_subset (P : ShorLoweringPolicy) (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)) :
    (↑(orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).lowSupport : Set ℕ)
      ⊆ semiclassicalQubits c y work scratch flag
        ∪ ↑(MGate.qftPhaseFoot P (orderFindingSemiclassical a N c m y work scratch flag hw hs4) hws) := by
  intro q hq
  rcases lowerM_lowSupport_subset P _ hws hq with h | h
  · exact Or.inl (orderFindingSemiclassical_support a N m hw hs4 h)
  · exact Or.inr h

/-! ## The lowered semiclassical circuit, any start state -/

section Specialise
variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs] [MeasureClass qs]
variable {P : ShorLoweringPolicy} {a N c m : ℕ} {y work scratch : ExtReg} {flag : ℕ}
  {hw : ModMulCircuitWorkspaceOK y work} {hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag}
  {hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)}

/-- A qubit outside the semiclassical registers and outside the footprint of the lowered QFT
and phase-product blocks is outside the lowered circuit's low support. -/
theorem not_mem_semiclassicalLow_lowSupport {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag)
    (hq' : q ∉ MGate.qftPhaseFoot P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)
      hws) :
    q ∉ (orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).lowSupport :=
  fun h => by
    rcases semiclassical_lowSupport_subset P a N c m y work scratch flag hw hs4 hws h with h1 | h1
    · exact hq h1
    · exact hq' h1

/-- **B3 (ii), flip form, any start state.** For ANY policy, registers, lowering workspace
`hws` and start state `ψ₀` (no admissibility, layout or clean-workspace hypothesis), and a
qubit `q` outside `semiclassicalQubits` and outside `MGate.qftPhaseFoot` (the actual footprint
of the lowered QFT / phase-product blocks): applying the low-level `X q` to the start state does
not change any record probability of the lowered circuit. -/
theorem orderFindingSemiclassicalLow_recordProb_init_X {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag)
    (hq' : q ∉ MGate.qftPhaseFoot P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)
      hws) (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (LowerGateClass.evalL (LowGate.X q) ψ₀))) r
      = recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
          (MState.init ψ₀)) r :=
  MLowGate.recordProb_init_X _ (not_mem_semiclassicalLow_lowSupport hq hq') ψ₀ r

/-- **B3 (ii), decomposition, any start state.** Same hypotheses: every record probability of
the lowered circuit from `ψ₀` is the sum over `o ∈ {0, 1}` of those from
`measProj (qubitReg q) o ψ₀`. (Not stated at the lowered level before.) -/
theorem orderFindingSemiclassicalLow_recordProb_decomp {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag)
    (hq' : q ∉ MGate.qftPhaseFoot P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)
      hws) (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch
          flag hw hs4 hws).eval (MState.init (MeasureClass.measProj (qubitReg q) o ψ₀))) r :=
  MLowGate.recordProb_decomp _ (not_mem_semiclassicalLow_lowSupport hq hq') ψ₀ r

/-- **B3 (ii), superposed spectator, any start ket.** Same hypotheses, ANY `b0`, ANY `α β`:
from `α|b0⟩ + β|flipBit q b0⟩` every record of the lowered circuit has `(‖α‖² + ‖β‖²)` times
its probability from `|b0⟩`. Unlike `orderFindingSemiclassicalLow_recordProb_superpose`, no
admissibility, layout, clean-workspace or zero-scratch hypothesis on `b0`. -/
theorem orderFindingSemiclassicalLow_recordProb_superpose_direct {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag)
    (hq' : q ∉ MGate.qftPhaseFoot P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)
      hws) (b0 : qs.Basis) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch
          flag hw hs4 hws).eval (MState.init (qs.ket b0))) r :=
  MLowGate.recordProb_superpose _ (not_mem_semiclassicalLow_lowSupport hq hq') b0 α β r

/-- **B3 (ii), agreement form, any start kets.** Two start kets that agree on
`semiclassicalQubits` and on `MGate.qftPhaseFoot`, and differ at finitely many qubits, give
every record of the lowered circuit the same probability. -/
theorem orderFindingSemiclassicalLow_recordProb_of_agree_direct (b0 b0' : qs.Basis)
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (hagree' : ∀ p ∈ MGate.qftPhaseFoot P (orderFindingSemiclassical a N c m y work scratch flag
      hw hs4) hws, RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (hfin : {p | RegEncoding.bit p b0' ≠ RegEncoding.bit p b0}.Finite) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (qs.ket b0'))) r
      = recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
          (MState.init (qs.ket b0))) r := by
  refine MLowGate.recordProb_of_agree _ b0 b0' (fun p hp => ?_) hfin r
  rcases semiclassical_lowSupport_subset P a N c m y work scratch flag hw hs4 hws hp with h | h
  · exact hagree p h
  · exact hagree' p h

end Specialise

end Readout
end Shor
