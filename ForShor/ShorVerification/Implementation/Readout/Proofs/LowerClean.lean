import ForShor.ShorVerification.Implementation.Readout.Proofs.LowerEval
import ForShor.ShorVerification.Implementation.Readout.ShorStatement
import ForShor.ShorVerification.Implementation.Readout.Proofs.Basic
import ForShor.ShorVerification.Implementation.Shor.Proofs.Readiness.ModMul
import ForShor.ShorVerification.Implementation.Shor.Proofs.Budgets

/-!
# Readout: the lowered semiclassical run keeps every lowered block's workspace clean

`semiclassical_clean`: the real semiclassical circuit `orderFindingSemiclassical`
(`initY1`, then the rounds `H c ;; CmodMulInPlaceCore … (ctrl := c) ;; ffPhase c j ;;
H c ;; measureReset c`), run from a ket `b0` whose data, work and scratch reserves are
zero and whose scratch register is zero, satisfies `MGate.WorkspaceCleanState`: the
hypothesis of `lowerM_eval`. So the lowered program `Policy.lowerM P (orderFindingSemiclassical …)`
evaluates, on every branch, exactly as the high-level program
(`semiclassical_lowerM_eval`).

## The invariant

`SemiclassicalCleanState qs y work scratch` is the existing invariant of the lowered
coherent proof, `ShorConcreteCleanState qs x y work scratch _`, at an EMPTY exponent
register `x = emptyExtReg`: the linear span of basis kets in which

* every qubit of `scratch` (active and spare) is `0`,
* the data register's spare qubits after the first (`y.reserve.drop 1`) are `0`,
* every spare qubit of `work` is `0`.

The per-multiplier theorem of the coherent proof,
`lowered_CmodMulInPlaceCore_ready_and_clean`, is stated for this invariant at ANY
exponent register `x` owned-disjoint from data, work and scratch and not containing
the flag, and for ANY control qubit `ctrl` (its layout argument is
`ModMulCoreLayout data work flag ctrl`; it does not ask the control to be a qubit of
`x`, nor any valid-state hypothesis). With `x` empty the disjointness facts are
trivial, and the control is the semiclassical control `c`. It gives: the lowered
multiplier's blocks start clean, and its lowered output satisfies the invariant again.

The other steps keep the invariant on every branch because they only write qubits
outside the three clean registers (`OffClean`): `initY1` writes the lowest data qubit
(active, so not a data spare; owned-disjoint from work and scratch); `H c`, the reset
`X c`, `Phase c θ` and the Born projections on `c` act on `c`, which the layout keeps
outside data, work and scratch (reserves included). The projections and the phase send
each ket to a multiple of itself or to `0`; `H` and `X` send a ket to kets that differ
from it only on the written qubit.

## Why this is the predicate `lowerM_eval` needs

`MGate.WorkspaceCleanState qs P G hws ψ` asks, for every `unitary u` part, the
dynamic workspace condition `Policy.GateWorkspaceCleanState qs P u _` on every branch
of the state that part sees in the LOWERED run (for `seq a b`, `b`'s condition on
`(Policy.lowerM P a _).eval ψ`). `MLoweredCleanResult` packages that condition with the
invariant on every branch of the lowered output (the measurement-language form of the
coherent `LoweredCleanResult`), and composes over `seq`
(`MLoweredCleanResult.seq`). `semiclassical_clean` is exactly the hypothesis
`hclean` of `lowerM_eval` for this circuit and this start state.
-/

namespace Shor
namespace Readout

/-! ## The empty exponent register and the invariant -/

/-- The extendable register with no qubits (no active part, no reserve). The proof-only
"exponent register" at which the coherent invariant `ShorConcreteCleanState` is used. -/
def emptyExtReg : ExtReg := ExtReg.ofReg Reg.empty

@[simp] theorem emptyExtReg_ownedQubits : emptyExtReg.ownedQubits = [] := rfl

/-- The empty register is owned-disjoint from every register. -/
theorem emptyExtReg_ownedDisjoint (e : ExtReg) : emptyExtReg.OwnedDisjoint e := by
  simp [ExtReg.OwnedDisjoint]

/-- The empty register is owned-disjoint from every register, on the right. -/
theorem ownedDisjoint_emptyExtReg (e : ExtReg) : e.OwnedDisjoint emptyExtReg := by
  simp [ExtReg.OwnedDisjoint]

/-- **The clean invariant of the lowered semiclassical run**: `ShorConcreteCleanState`
at the empty exponent register: the span of kets in which `scratch` (all of it), the
data spares after the first, and the work spares are `0`. -/
abbrev SemiclassicalCleanState (qs : QSemantics) [RegEncoding qs.Basis]
    (y work scratch : ExtReg) : qs.State → Prop :=
  ShorConcreteCleanState qs emptyExtReg y work scratch (emptyExtReg_ownedDisjoint scratch)

/-- The spare qubits the lowered semiclassical run uses start at zero: the data, work
and scratch reserves (the semiclassical form of `ShorWorkspaceCleanInput`, without the
exponent register, which the circuit does not have). -/
def SemiclassicalWorkspaceCleanInput {Basis : Type*} [RegEncoding Basis]
    (y work scratch : ExtReg) (b0 : Basis) : Prop :=
  FreshZero y.reserve b0 ∧ FreshZero work.reserve b0 ∧ FreshZero scratch.reserve b0

/-- The coherent clean-input hypothesis gives the semiclassical one. -/
theorem SemiclassicalWorkspaceCleanInput.of_shor {Basis : Type*} [RegEncoding Basis]
    {x y work scratch : ExtReg} {b0 : Basis} (h : ShorWorkspaceCleanInput x y work scratch b0) :
    SemiclassicalWorkspaceCleanInput y work scratch b0 :=
  ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-! ## The measurement-language clean result -/

section Result
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- `MLoweredCleanResult qs P Inv G hws ψ`: every lowered block of `G` starts with clean
workspace in the lowered run from `ψ` (`MGate.WorkspaceCleanState`), and every branch of
the lowered output satisfies `Inv`. The measurement-language form of `LoweredCleanResult`. -/
def MLoweredCleanResult (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    [LowerGateClass qs] [MeasureClass qs] (P : ShorLoweringPolicy) (Inv : qs.State → Prop)
    (G : MGate) (hws : MGate.WorkspaceOK P G) (ψ : MState qs) : Prop :=
  MGate.WorkspaceCleanState qs P G hws ψ ∧ ∀ r, Inv ((Policy.lowerM P G hws).eval ψ r)

/-- `G` keeps `Inv`: from every branching state with `Inv` on every branch, the lowered
run of `G` is clean (`MLoweredCleanResult`). -/
def MCleanPreserving (P : ShorLoweringPolicy) (Inv : qs.State → Prop) (G : MGate)
    (hws : MGate.WorkspaceOK P G) : Prop :=
  ∀ ψ : MState qs, (∀ r, Inv (ψ r)) → MLoweredCleanResult qs P Inv G hws ψ

variable {P : ShorLoweringPolicy} {Inv : qs.State → Prop}

/-- Sequencing (the measurement-language `LoweredCleanResult.seq`). -/
theorem MCleanPreserving.seq {a b : MGate} (hws : MGate.WorkspaceOK P (.seq a b))
    (ha : MCleanPreserving P Inv a hws.1) (hb : MCleanPreserving P Inv b hws.2) :
    MCleanPreserving P Inv (.seq a b) hws := by
  intro ψ hψ
  have h1 := ha ψ hψ
  have h2 := hb _ h1.2
  exact ⟨⟨h1.1, h2.1⟩, h2.2⟩

/-- A unitary part whose lowered run is clean and keeps `Inv` on every state with `Inv`. -/
theorem MCleanPreserving.unitary {u : Gate} (hws : Policy.GateWorkspaceOK P u)
    (h : ∀ φ, Inv φ → LoweredCleanResult qs P Inv u hws φ) :
    MCleanPreserving P Inv (.unitary u) hws :=
  fun ψ hψ => ⟨fun r => (h (ψ r) (hψ r)).1, fun r => (h (ψ r) (hψ r)).2⟩

/-- A workspace-free unitary part (`H`, `X`, `initY1`, `id`) whose high-level action keeps
`Inv`: its lowered action is its high-level action (`Policy.lowerGate_correct`). -/
theorem MCleanPreserving.free (hP : P.Admissible) {u : Gate} (hfree : WorkspaceFree u)
    (hws : Policy.GateWorkspaceOK P u) (hpres : ∀ φ, Inv φ → Inv (qs.eval u φ)) :
    MCleanPreserving P Inv (.unitary u) hws := by
  refine MCleanPreserving.unitary hws fun φ hφ => ⟨hfree.clean hws φ, ?_⟩
  rw [Policy.lowerGate_correct qs P hP u hws φ (hfree.clean hws φ)]
  exact hpres φ hφ

/-- The feed-forward phase keeps `Inv` when every phase on `q` does. -/
theorem MCleanPreserving.ffPhase {q j : ℕ} (hws : MGate.WorkspaceOK P (.ffPhase q j))
    (hpres : ∀ θ φ, Inv φ → Inv (LowerGateClass.evalL (LowGate.Phase q θ) φ)) :
    MCleanPreserving P Inv (.ffPhase q j) hws :=
  fun _ hψ => ⟨trivial, fun r => hpres _ _ (hψ r)⟩

/-- Measure-and-reset keeps `Inv` when `Inv 0` holds and both children of a branch
(`measureResetBranch`, the Born projection, then `X q` on outcome `1`) keep it. -/
theorem MCleanPreserving.measureReset (hP : P.Admissible) {q : ℕ}
    (hws : MGate.WorkspaceOK P (.measureReset q)) (h0 : Inv 0)
    (hpres : ∀ b φ, Inv φ → Inv (measureResetBranch q b φ)) :
    MCleanPreserving P Inv (.measureReset q) hws := by
  intro ψ hψ
  refine ⟨trivial, fun r => ?_⟩
  show Inv (if h : r = [] then 0 else measureResetBranchL q (r.getLast h) (ψ r.dropLast))
  split
  · exact h0
  · rw [measureResetBranchL_eq hP]
    exact hpres _ _ (hψ _)

end Result

/-! ## The clean registers and the qubits outside them -/

section Clean
variable {qs : QSemantics} [RegEncoding qs.Basis]

/-- Qubit `q` lies outside the three registers of `SemiclassicalCleanState`: not a qubit
of `scratch` (active or spare), not a data spare, not a work spare. -/
def OffClean (y work scratch : ExtReg) (q : ℕ) : Prop :=
  q ∉ scratch.ownedQubits ∧ q ∉ y.reserve.qubits ∧ q ∉ work.reserve.qubits

/-- The first clean register of the invariant is the whole scratch register. -/
theorem mem_scratchClean {scratch : ExtReg} {q : ℕ}
    (h : q ∈ (exponentScratchCleanReg emptyExtReg scratch
      (emptyExtReg_ownedDisjoint scratch)).qubits) : q ∈ scratch.ownedQubits := by
  simpa [exponentScratchCleanReg, Reg.append, ExtReg.ownedReg, emptyExtReg, ExtReg.ofReg,
    Reg.empty, ExtReg.ownedQubits] using h

/-- A register without `q` is disjoint from the one-qubit register at `q`. -/
theorem disjoint_qubitReg_of_not_mem {R : Reg} {q : ℕ} (h : q ∉ R.qubits) :
    Disjoint R (qubitReg q) :=
  List.disjoint_left.2 fun p hp hpq => h (((mem_qubitReg q p).1 hpq) ▸ hp)

/-- Writing a qubit outside the clean registers keeps a clean ket clean. -/
theorem cleanState_ket_write {y work scratch : ExtReg} {q : ℕ} (hq : OffClean y work scratch q)
    (b : qs.Basis) (v : ℕ)
    (h₁ : FreshZero (exponentScratchCleanReg emptyExtReg scratch
      (emptyExtReg_ownedDisjoint scratch)) b)
    (h₂ : FreshZero (y.reserve.drop 1) b) (h₃ : FreshZero work.reserve b) :
    SemiclassicalCleanState qs y work scratch (qs.ket (RegEncoding.writeNat (qubitReg q) v b)) := by
  have d₁ : Disjoint (exponentScratchCleanReg emptyExtReg scratch
      (emptyExtReg_ownedDisjoint scratch)) (qubitReg q) :=
    disjoint_qubitReg_of_not_mem fun h => hq.1 (mem_scratchClean h)
  have d₂ : Disjoint (y.reserve.drop 1) (qubitReg q) :=
    disjoint_qubitReg_of_not_mem fun h => hq.2.1 (List.mem_of_mem_drop h)
  have d₃ : Disjoint work.reserve (qubitReg q) := disjoint_qubitReg_of_not_mem hq.2.2
  refine ThreeRegsCleanState.ket _ ?_ ?_ ?_
  · unfold FreshZero at h₁ ⊢; rw [toNat_left_write_right _ _ d₁]; exact h₁
  · unfold FreshZero at h₂ ⊢; rw [toNat_left_write_right _ _ d₂]; exact h₂
  · unfold FreshZero at h₃ ⊢; rw [toNat_left_write_right _ _ d₃]; exact h₃

/-- A linear map that sends every clean ket to a clean state keeps clean states clean. -/
theorem threeRegsClean_map {r₁ r₂ r₃ : Reg} (f : qs.State → qs.State)
    (hadd : ∀ ψ φ, f (ψ + φ) = f ψ + f φ) (hsmul : ∀ (a : ℂ) ψ, f (a • ψ) = a • f ψ)
    (hket : ∀ b, FreshZero r₁ b → FreshZero r₂ b → FreshZero r₃ b →
      ThreeRegsCleanState qs r₁ r₂ r₃ (f (qs.ket b)))
    {ψ : qs.State} (h : ThreeRegsCleanState qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState qs r₁ r₂ r₃ (f ψ) := by
  induction h with
  | zero =>
      have h0 : f 0 = 0 := by simpa using hsmul 0 0
      rw [h0]; exact ThreeRegsCleanState.zero
  | ket b h₁ h₂ h₃ => exact hket b h₁ h₂ h₃
  | add _ _ ihψ ihφ => rw [hadd]; exact ThreeRegsCleanState.add ihψ ihφ
  | smul a _ ih => rw [hsmul]; exact ThreeRegsCleanState.smul a ih

variable {y work scratch : ExtReg} {q : ℕ}

/-- `H q` keeps the invariant for `q` outside the clean registers. -/
theorem cleanState_H [GateSemanticsFacts qs] (hq : OffClean y work scratch q) {φ : qs.State}
    (h : SemiclassicalCleanState qs y work scratch φ) :
    SemiclassicalCleanState qs y work scratch (qs.eval (Gate.H q) φ) := by
  refine threeRegsClean_map _ (qs.eval_add _) (qs.eval_smul _) (fun b h₁ h₂ h₃ => ?_) h
  rw [HadamardSemantics.eval_H_ket]
  exact ThreeRegsCleanState.smul _ (ThreeRegsCleanState.add
    (cleanState_ket_write hq b 0 h₁ h₂ h₃)
    (ThreeRegsCleanState.smul _ (cleanState_ket_write hq b 1 h₁ h₂ h₃)))

/-- `X q` keeps the invariant for `q` outside the clean registers. -/
theorem cleanState_X [GateSemanticsFacts qs] (hq : OffClean y work scratch q) {φ : qs.State}
    (h : SemiclassicalCleanState qs y work scratch φ) :
    SemiclassicalCleanState qs y work scratch (qs.eval (Gate.X q) φ) := by
  refine threeRegsClean_map _ (qs.eval_add _) (qs.eval_smul _) (fun b h₁ h₂ h₃ => ?_) h
  rw [PauliXSemantics.eval_X_ket]
  exact cleanState_ket_write hq b _ h₁ h₂ h₃

/-- Every phase gate keeps the invariant (it scales each ket). -/
theorem cleanState_Phase [LowerGateClass qs] (θ : Angle) {φ : qs.State}
    (h : SemiclassicalCleanState qs y work scratch φ) :
    SemiclassicalCleanState qs y work scratch (LowerGateClass.evalL (LowGate.Phase q θ) φ) := by
  refine threeRegsClean_map _ (LowerGateClass.evalL_add _) (LowerGateClass.evalL_smul _)
    (fun b h₁ h₂ h₃ => ?_) h
  rw [LowerGateClass.evalL_Phase_ket]
  split
  · exact ThreeRegsCleanState.smul _ (ThreeRegsCleanState.ket b h₁ h₂ h₃)
  · exact ThreeRegsCleanState.ket b h₁ h₂ h₃

/-- Every Born projection keeps the invariant (it keeps or kills each ket). -/
theorem cleanState_measProj [MeasureClass qs] (R : Reg) (o : ℕ) {φ : qs.State}
    (h : SemiclassicalCleanState qs y work scratch φ) :
    SemiclassicalCleanState qs y work scratch (MeasureClass.measProj R o φ) := by
  refine threeRegsClean_map _ (map_add _) (map_smul _) (fun b h₁ h₂ h₃ => ?_) h
  rw [MeasureClass.measProj_ket]
  split
  · exact ThreeRegsCleanState.ket b h₁ h₂ h₃
  · exact ThreeRegsCleanState.zero

/-- Both children of measure-and-reset on `q` keep the invariant. -/
theorem cleanState_measureResetBranch [GateSemanticsFacts qs] [MeasureClass qs]
    (hq : OffClean y work scratch q) (b : Bool) {φ : qs.State}
    (h : SemiclassicalCleanState qs y work scratch φ) :
    SemiclassicalCleanState qs y work scratch (measureResetBranch q b φ) := by
  unfold measureResetBranch
  split
  · exact cleanState_X hq (cleanState_measProj _ _ h)
  · exact cleanState_measProj _ _ h

/-- `initY1 y.active` keeps the invariant: it writes the lowest data qubit, which is not
a data spare and (by the workspaces) not a work or scratch qubit. -/
theorem cleanState_initY1 [GateSemanticsFacts qs] {N flag : ℕ}
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) {φ : qs.State}
    (h : SemiclassicalCleanState qs y work scratch φ) :
    SemiclassicalCleanState qs y work scratch (qs.eval (initY1 y.active) φ) := by
  unfold initY1
  split
  · rw [qs.eval_id]; exact h
  · rename_i p rest hyq
    have hp : p ∈ y.active.qubits := by rw [hyq]; exact List.mem_cons_self
    have hpy : p ∈ y.ownedQubits := List.mem_append_left _ hp
    have hys : ExtReg.OwnedDisjoint y scratch := by
      simpa [ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow] using hs4.data_scratch_disjoint
    refine cleanState_X ⟨fun hs => hys hpy hs, fun hr => ?_, fun hr => ?_⟩ h
    · exact (List.disjoint_left.1 y.active_reserve_disjoint) hp hr
    · exact hw.2.2 hpy (List.mem_append_right _ hr)

end Clean

/-! ## The rounds -/

section Rounds
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- The control is outside the clean registers. -/
theorem offClean_of_layout {c : ℕ} {y work scratch : ExtReg} {flag : ℕ}
    (hl : SemiclassicalLayout c y work scratch flag) : OffClean y work scratch c :=
  ⟨hl.c_not_mem_scratch, fun h => hl.c_not_mem_data (List.mem_append_right _ h),
    fun h => hl.c_not_mem_work (List.mem_append_right _ h)⟩

/-- **The rounds keep the invariant.** For any multiplier constants `f j`, the rounds
`readoutRounds (fun j => CmodMulInPlaceCore (f j) N c y work scratch flag hw hs4) c m`
keep `SemiclassicalCleanState` with every lowered block clean, from every branching state
with the invariant on every branch. The multiplier step is the coherent proof's
`lowered_CmodMulInPlaceCore_ready_and_clean` at the empty exponent register and
`ctrl := c`. -/
theorem readoutRounds_cleanPreserving {P : ShorLoweringPolicy} (hP : P.Admissible)
    (f : ℕ → ℕ) (N c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hl : SemiclassicalLayout c y work scratch flag) (m : ℕ)
    (hws : MGate.WorkspaceOK P
      (readoutRounds (fun j => CmodMulInPlaceCore (f j) N c y work scratch flag hw hs4) c m)) :
    MCleanPreserving P (SemiclassicalCleanState qs y work scratch)
      (readoutRounds (fun j => CmodMulInPlaceCore (f j) N c y work scratch flag hw hs4) c m)
      hws := by
  have hc := offClean_of_layout hl
  have hlayout : ModMulCoreLayout y work flag c :=
    ⟨hw.2.2, by simpa [Gate.ExtReg.ownedQubits_grow] using hs4.flag_not_data,
      hs4.flag_not_work, hl.c_not_mem_data, hl.c_not_mem_work, hl.c_ne_flag⟩
  have hH : ∀ h : Policy.GateWorkspaceOK P (Gate.H c),
      MCleanPreserving P (SemiclassicalCleanState qs y work scratch) (.unitary (Gate.H c)) h :=
    fun h => MCleanPreserving.free hP (WorkspaceFree.H c) h fun _ hφ => cleanState_H hc hφ
  induction m with
  | zero =>
      exact MCleanPreserving.free hP WorkspaceFree.id hws fun φ hφ => by rw [qs.eval_id]; exact hφ
  | succ k ih =>
      refine MCleanPreserving.seq hws (ih hws.1) ?_
      refine MCleanPreserving.seq _ (hH _) ?_
      refine MCleanPreserving.seq _ ?_ ?_
      · exact MCleanPreserving.unitary _ fun φ hφ =>
          lowered_CmodMulInPlaceCore_ready_and_clean P hP emptyExtReg y work scratch (f k) N c flag
            (emptyExtReg_ownedDisjoint _) (emptyExtReg_ownedDisjoint _)
            (emptyExtReg_ownedDisjoint _) hw (by simp) hlayout hs4 _ φ hφ
      refine MCleanPreserving.seq _ (MCleanPreserving.ffPhase _ fun θ _ hφ => cleanState_Phase θ hφ) ?_
      refine MCleanPreserving.seq _ (hH _) ?_
      exact MCleanPreserving.measureReset hP _ ThreeRegsCleanState.zero
        fun b _ hφ => cleanState_measureResetBranch hc b hφ

end Rounds

end Readout

/-! ## The headline -/

section
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

open Readout

/-- **The lowered semiclassical run is clean** (`semiclassical_clean`). For an admissible
policy `P`, constant `a`, modulus `N`, control `c`, number of rounds `m`, registers
`y` (data), `work`, `scratch` and flag with the multiplier's workspaces `hw`, `hs4`, the
lowering workspace `hws`, the layout `SemiclassicalLayout c y work scratch flag`, and a
start ket `b0` whose data, work and scratch reserves are zero and whose scratch register
is zero: the real circuit `orderFindingSemiclassical a N c m …` run from
`MState.init |b0⟩` satisfies `MGate.WorkspaceCleanState` (every lowered block of every
round starts with clean workspace on every branch of the lowered run). -/
theorem semiclassical_clean {P : ShorLoweringPolicy} (hP : P.Admissible) (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0) :
    MGate.WorkspaceCleanState qs P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)
      hws (MState.init (qs.ket b0)) := by
  have hempty : FreshZero emptyExtReg.reserve b0 := by
    have := RegEncoding.toNat_lt_ASize Reg.empty b0
    simp only [ASize, regSize, Reg.width, Reg.empty, List.length_nil, pow_zero,
      Nat.lt_one_iff] at this
    exact this
  have hstart : SemiclassicalCleanState qs y work scratch (qs.ket b0) :=
    shorConcreteCleanState_ket ⟨hempty, hzero.1, hzero.2.1, hzero.2.2⟩ hscratch
  have hinit : ∀ r, SemiclassicalCleanState qs y work scratch (MState.init (qs.ket b0) r) := by
    intro r
    unfold MState.init
    split
    · exact hstart
    · exact ThreeRegsCleanState.zero
  have hall : MCleanPreserving P (SemiclassicalCleanState qs y work scratch)
      (orderFindingSemiclassical a N c m y work scratch flag hw hs4) hws :=
    MCleanPreserving.seq hws
      (MCleanPreserving.free hP (workspaceFree_initY1 y.active) hws.1
        fun _ hφ => cleanState_initY1 hw hs4 hφ)
      (readoutRounds_cleanPreserving hP (fun j => (a ^ (2 ^ (m - 1 - j))) % N) N c y work scratch
        flag hw hs4 hl m hws.2)
  exact (hall _ hinit).1

/-- **The lowered semiclassical circuit evaluates as the circuit**: under the hypotheses
of `semiclassical_clean`, the lowered program `Policy.lowerM P (orderFindingSemiclassical …)`
run from `MState.init |b0⟩` gives the same branching state (every record's branch) as
the high-level program (`lowerM_eval` with `semiclassical_clean`). -/
theorem semiclassical_lowerM_eval {P : ShorLoweringPolicy} (hP : P.Admissible) (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0) :
    (Policy.lowerM P (orderFindingSemiclassical a N c m y work scratch flag hw hs4) hws).eval
        (MState.init (qs.ket b0))
      = (orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0)) :=
  lowerM_eval hP _ hws _ (semiclassical_clean hP a N c m y work scratch flag hw hs4 hws hl b0
    hzero hscratch)

end

end Shor
