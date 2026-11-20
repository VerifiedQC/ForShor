import ForShor.ShorVerification.Implementation.Readout.LowLocalityNamed
import ForShor.ShorVerification.Implementation.Readout.Proofs.LowFootprintReach

/-!
# Readout: the facts the named footprint consumes, and the balanced lowerings

## Item 1: where `Valid` comes from

The footprint bound on phase-product plans (`lowerGateRec_lowFootprint`) assumes the plan is
`PhaseLoweringPlan.Valid`. In plain words, a plan is `Valid` when:

* every primitive node (`H`, `X`, shifts, `Negate`, `AddScaled`, extensions,
  deallocations, `RadixReverse`, `id`) imposes no condition, and `seq` asks both parts;
* every naive base node (`signedBase`, `cSignedBase`) is one where the policy stops
  (`P.Stops` at the node's input width);
* every recursive node (`signedStep phi x z T layout child`) satisfies `SignedStepOK`: the
  policy chose `T` at the node's input width, `T` shrinks the operands, the `layout` is valid
  (`Gate.PhaseProductLayout.Valid`: on each operand the children's reserves concatenate to
  exactly the operand's reserve, distinct children own disjoint qubits, and every `x` child is
  disjoint from every `z` child), and every chunk can grow to its needed width; and the child
  plan is `Valid`;
* a controlled recursive node (`cSignedStep`) satisfies the same plus: the control is outside
  every child register (`CSignedStepOK`).

(Informal remark about the proof, not a stated theorem: the footprint proof uses only the
reserve-partition field of layout validity.)

Theorems below (restated from `PhaseProduct/Proofs/Lowering/PlanReadiness/PlanValid.lean` and
`QFT/Statement.lean` so that a statements-only reader sees them):

* `signedPlan_valid_of_workspaceOK`: `Policy.WorkspaceOK P x z → (Policy.signedPlan P φ x z).Valid`;
* `cSignedPlan_valid_of_cWorkspaceOK`: the controlled form, from `Policy.CWorkspaceOK`;
* `gateWorkspaceOK_QFT_iff`, `gateWorkspaceOK_signed_iff`, `gateWorkspaceOK_csigned_iff`:
  `Policy.GateWorkspaceOK` IS `QFTReserveOK` / `WorkspaceOK` / `CWorkspaceOK` at those gates;
* `qftWorkspace_of_reserveOK`, `qftXWork_sub_reserve`, `qftZWork_sub_reserve`: the QFT's two
  pools are slices of `r.reserve` and satisfy the plan's `QFTWorkspaceOK`;
* `phaseProdUsingPlan_valid`: the QFT's inner phase-product plan is `Valid`.

## Item 3: the balanced lowerings

`Policy.lowerMBalanced P R` / `Policy.lowerMBalancedU P R` lower each unitary part after the
balanced split `Balanced.balance P R` / `Balanced.balanceU R`. The split introduces NO qubit
outside the operands: every block is `Balanced.lowBlock x w` (low active qubits of `x` and
ALL of `x.reserve`) or `Balanced.highPart x w` (the other active qubits of `x` and all of
`x.reserve`), grown by extensions into their own reserves, and the small operand `z` grown into
its own reserve (`support_splitGate`). So `(balance P R G).qubitSupport ⊆ G.qubitSupport` and
`(balanceU R G).qubitSupport ⊆ G.qubitSupport` for every gate, with no hypothesis.

* `semiclassical_lowSupport_balanced`, `semiclassical_lowSupport_balancedU`: the low support of
  `orderFindingSemiclassicalLowBalanced` / `…BalancedU` is inside `semiclassicalQubits`;
* `…Balanced(U)_recordProb_init_X_named`, `…_decomp_named`, `…_superpose_named`: locality of
  the balanced lowered circuits with the single hypothesis `q ∉ semiclassicalQubits`, any
  policy, rule, workspace (and fit hypothesis `hf` for `U`, part of the circuit's definition),
  any start state.

Not covered: qubits of `semiclassicalQubits` (control, reserves); flip forms use `LowGate.X q`.
-/

namespace Shor
namespace Readout

open Gate Operations

/-! ## Item 1 -/

/-- **The planner's plan is valid under the operands' workspace condition.** `Valid`: see the
module docstring. -/
theorem signedPlan_valid_of_workspaceOK (P : ShorLoweringPolicy) (phi : Angle) (x z : ExtReg)
    (h : Policy.WorkspaceOK P x z) : (Policy.signedPlan P phi x z).Valid :=
  Policy.signedPlan_valid P phi x z h

/-- **The controlled planner's plan is valid under the controlled workspace condition.** -/
theorem cSignedPlan_valid_of_cWorkspaceOK (P : ShorLoweringPolicy) (ctrl : ℕ) (phi : Angle)
    (x z : ExtReg) (h : Policy.CWorkspaceOK P ctrl x z) :
    (Policy.cSignedPlan P ctrl phi x z).Valid :=
  Policy.cSignedPlan_valid P ctrl phi x z h

/-- The lowering workspace of a QFT is the reserve condition of its register. -/
theorem gateWorkspaceOK_QFT_iff (P : ShorLoweringPolicy) (r : ExtReg) :
    Policy.GateWorkspaceOK P (Gate.QFT r) ↔ Policy.QFTReserveOK P r := Iff.rfl

/-- The lowering workspace of a signed phase product is `Policy.WorkspaceOK`. -/
theorem gateWorkspaceOK_signed_iff (P : ShorLoweringPolicy) (phi : Angle) (x z : ExtReg) :
    Policy.GateWorkspaceOK P (Gate.SignedPhaseProd phi x z) ↔ Policy.WorkspaceOK P x z := Iff.rfl

/-- The lowering workspace of a controlled signed phase product is `Policy.CWorkspaceOK`. -/
theorem gateWorkspaceOK_csigned_iff (P : ShorLoweringPolicy) (c : ℕ) (phi : Angle) (x z : ExtReg) :
    Policy.GateWorkspaceOK P (Gate.CSignedPhaseProd c phi x z) ↔ Policy.CWorkspaceOK P c x z :=
  Iff.rfl

/-- The QFT's two pools satisfy the plan's workspace condition. -/
theorem qftWorkspace_of_reserveOK (P : ShorLoweringPolicy) (r : ExtReg)
    (h : Policy.QFTReserveOK P r) :
    Policy.QFTWorkspaceOK P r.active (Policy.qftXWork P r) (Policy.qftZWork P r) :=
  h.explicitWorkspace

/-- The QFT's x-pool is a slice of the register's reserve. -/
theorem qftXWork_sub_reserve (P : ShorLoweringPolicy) (r : ExtReg) :
    ∀ p ∈ (Policy.qftXWork P r).qubits, p ∈ r.reserve.qubits :=
  fun _ h => List.mem_of_mem_take h

/-- The QFT's z-pool is a slice of the register's reserve. -/
theorem qftZWork_sub_reserve (P : ShorLoweringPolicy) (r : ExtReg) :
    ∀ p ∈ (Policy.qftZWork P r).qubits, p ∈ r.reserve.qubits :=
  fun _ h => List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- The QFT's inner phase-product plan is valid. It exists only at a split node, i.e. for a
register of width at least two (`hsize`); a QFT on 0 or 1 qubits lowers to `id` / one `H` and
bypasses the phase-product plan. -/
theorem phaseProdUsingPlan_valid (P : ShorLoweringPolicy) {r xW zW : Reg}
    (h : Policy.QFTWorkspaceOK P r xW zW) (hsize : 2 ≤ regSize r) (phi : Angle) :
    (Policy.phaseProdUsingPlan P phi (h.phaseWorkspace hsize)).Valid := by
  have hphase : Policy.WorkspaceOK P ((h.phaseWorkspace hsize).xExt.grow 1)
      ((h.phaseWorkspace hsize).zExt.grow 1) := by
    simpa using h.policySignedWorkspaceOK hsize
  exact ⟨trivial, trivial, Policy.signedPlan_valid P _ _ _ hphase, trivial, trivial⟩

/-! ## Item 3: the balanced split stays in the operands -/

theorem owned_lowBlock {x : ExtReg} {w p : ℕ} (h : p ∈ (Balanced.lowBlock x w).ownedQubits) :
    p ∈ x.ownedQubits := by
  simp only [Balanced.lowBlock, ExtReg.ownedQubits, Reg.take, List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl (List.mem_of_mem_take h)
  · exact Or.inr h

theorem owned_highPart {x : ExtReg} {w p : ℕ} (h : p ∈ (Balanced.highPart x w).ownedQubits) :
    p ∈ x.ownedQubits := by
  simp only [Balanced.highPart, ExtReg.ownedQubits, Reg.drop, List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl (List.mem_of_mem_drop h)
  · exact Or.inr h

/-- Membership in the support of a phase-product gate of kind `c`. -/
theorem mem_ctlGate_iff (c : Balanced.Ctl) (φ : Angle) (x z : ExtReg) (p : ℕ) :
    p ∈ (c.gate φ x z).qubitSupport ↔
      p ∈ x.ownedQubits ∨ p ∈ z.ownedQubits ∨ ∃ q, c = .ctrl q ∧ p = q := by
  cases c <;> simp [Balanced.Ctl.gate, Gate.qubitSupport]; tauto

theorem support_splitGate (c : Balanced.Ctl) (t : ℕ) (z : ExtReg) :
    ∀ (bs : List Balanced.Block) (φ : Angle) (x : ExtReg) (p : ℕ),
      p ∈ (Balanced.splitGate c φ bs t x z).qubitSupport →
      p ∈ x.ownedQubits ∨ p ∈ z.ownedQubits ∨ ∃ q, c = .ctrl q ∧ p = q := by
  intro bs
  induction bs with
  | nil =>
    intro φ x p hp
    simp only [Balanced.splitGate, Balanced.topGate, Gate.qubitSupport, Set.mem_union,
      Set.mem_ofPred_eq, mem_ctlGate_iff, Gate.ExtReg.ownedQubits_grow] at hp
    tauto
  | cons b bs ih =>
    intro φ x p hp
    have h1 := @owned_lowBlock x b.w p
    have h2 := @owned_highPart x b.w p
    have h3 := ih (φ * 2 ^ b.w) (Balanced.highPart x b.w) p
    simp only [Balanced.splitGate, Balanced.lowGate, Gate.qubitSupport, Set.mem_union,
      Set.mem_ofPred_eq, mem_ctlGate_iff, Gate.ExtReg.ownedQubits_grow] at hp
    tauto

theorem support_siteGate (P : ShorLoweringPolicy) (R : Balanced.Rule) (c : Balanced.Ctl)
    (φ : Angle) (x z : ExtReg) (p : ℕ) (hp : p ∈ (Balanced.siteGate P R c φ x z).qubitSupport) :
    p ∈ (c.gate φ x z).qubitSupport := by
  rw [mem_ctlGate_iff]
  unfold Balanced.siteGate at hp
  split_ifs at hp
  · split at hp
    · split_ifs at hp
      · exact support_splitGate c _ z _ φ x p hp
      · exact (mem_ctlGate_iff c φ x z p).mp hp
    · exact (mem_ctlGate_iff c φ x z p).mp hp
  · split at hp
    · split_ifs at hp
      · have := support_splitGate c _ x _ φ z p hp
        tauto
      · exact (mem_ctlGate_iff c φ x z p).mp hp
    · exact (mem_ctlGate_iff c φ x z p).mp hp
  · exact (mem_ctlGate_iff c φ x z p).mp hp

theorem support_siteGateU (R : Balanced.Rule) (c : Balanced.Ctl)
    (φ : Angle) (x z : ExtReg) (p : ℕ) (hp : p ∈ (Balanced.siteGateU R c φ x z).qubitSupport) :
    p ∈ (c.gate φ x z).qubitSupport := by
  rw [mem_ctlGate_iff]
  unfold Balanced.siteGateU at hp
  split_ifs at hp
  · split at hp
    · exact support_splitGate c _ z _ φ x p hp
    · exact (mem_ctlGate_iff c φ x z p).mp hp
  · split at hp
    · have := support_splitGate c _ x _ φ z p hp
      tauto
    · exact (mem_ctlGate_iff c φ x z p).mp hp
  · exact (mem_ctlGate_iff c φ x z p).mp hp

/-- **The balanced split names no new qubit.** -/
theorem support_balance (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    ∀ (G : Gate), (Balanced.balance P R G).qubitSupport ⊆ G.qubitSupport := by
  intro G
  induction G with
  | seq U V ihU ihV =>
    intro p hp
    rcases hp with hp | hp
    · exact Or.inl (ihU hp)
    · exact Or.inr (ihV hp)
  | adj U ih => exact ih
  | SignedPhaseProd φ x z => exact fun p hp => support_siteGate P R .none φ x z p hp
  | CSignedPhaseProd q φ x z => exact fun p hp => support_siteGate P R (.ctrl q) φ x z p hp
  | _ => exact fun _ hp => hp

/-- **The unconditional balanced split names no new qubit.** -/
theorem support_balanceU (R : Balanced.Rule) :
    ∀ (G : Gate), (Balanced.balanceU R G).qubitSupport ⊆ G.qubitSupport := by
  intro G
  induction G with
  | seq U V ihU ihV =>
    intro p hp
    rcases hp with hp | hp
    · exact Or.inl (ihU hp)
    · exact Or.inr (ihV hp)
  | adj U ih => exact ih
  | SignedPhaseProd φ x z => exact fun p hp => support_siteGateU R .none φ x z p hp
  | CSignedPhaseProd q φ x z => exact fun p hp => support_siteGateU R (.ctrl q) φ x z p hp
  | _ => exact fun _ hp => hp

/-! ## The balanced lowered programs -/

theorem lowerMBalanced_lowSupport_named (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    ∀ (g : MGate) (h : MGate.WorkspaceOK P g),
      (↑(Policy.lowerMBalanced P R g h).lowSupport : Set ℕ) ⊆ g.qubitSupport := by
  intro g
  induction g with
  | unitary u =>
    intro h p hp
    exact support_balance P R u (lowerGate_lowFootprint_named P _ _ hp)
  | seq a b iha ihb =>
    intro h p hp
    simp only [Policy.lowerMBalanced, Policy.lowerMWith, MLowGate.lowSupport, Finset.coe_union,
      Set.mem_union] at hp
    rcases hp with hp | hp
    · exact Or.inl (iha h.1 hp)
    · exact Or.inr (ihb h.2 hp)
  | measureReset q =>
    intro _ p hp
    simp only [Policy.lowerMBalanced, Policy.lowerMWith, MLowGate.lowSupport,
      Finset.coe_singleton] at hp
    exact hp
  | ffPhase q j =>
    intro _ p hp
    simp only [Policy.lowerMBalanced, Policy.lowerMWith, MLowGate.lowSupport,
      Finset.coe_singleton] at hp
    exact hp

theorem lowerMBalancedU_lowSupport_named (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    ∀ (g : MGate) (h : MGate.WorkspaceOK P g) (hf : MGate.Fits P R g),
      (↑(Policy.lowerMBalancedU P R g h hf).lowSupport : Set ℕ) ⊆ g.qubitSupport := by
  intro g
  induction g with
  | unitary u =>
    intro h hf p hp
    exact support_balanceU R u (lowerGate_lowFootprint_named P _ _ hp)
  | seq a b iha ihb =>
    intro h hf p hp
    simp only [Policy.lowerMBalancedU, MLowGate.lowSupport, Finset.coe_union, Set.mem_union] at hp
    rcases hp with hp | hp
    · exact Or.inl (iha h.1 hf.1 hp)
    · exact Or.inr (ihb h.2 hf.2 hp)
  | measureReset q =>
    intro _ _ p hp
    simp only [Policy.lowerMBalancedU, MLowGate.lowSupport, Finset.coe_singleton] at hp
    exact hp
  | ffPhase q j =>
    intro _ _ p hp
    simp only [Policy.lowerMBalancedU, MLowGate.lowSupport, Finset.coe_singleton] at hp
    exact hp

/-- **The balanced lowered semiclassical circuit names only the semiclassical registers.** -/
theorem semiclassical_lowSupport_balanced (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)) :
    (↑(orderFindingSemiclassicalLowBalanced P R a N c m y work scratch flag hw hs4 hws).lowSupport
        : Set ℕ) ⊆ semiclassicalQubits c y work scratch flag := fun _ hp =>
  orderFindingSemiclassical_support a N m hw hs4 (lowerMBalanced_lowSupport_named P R _ hws hp)

/-- **The unconditionally balanced lowered semiclassical circuit names only the semiclassical
registers.** -/
theorem semiclassical_lowSupport_balancedU (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hf : MGate.Fits P R (orderFindingSemiclassical a N c m y work scratch flag hw hs4)) :
    (↑(orderFindingSemiclassicalLowBalancedU P R a N c m y work scratch flag hw hs4 hws hf).lowSupport
        : Set ℕ) ⊆ semiclassicalQubits c y work scratch flag := fun _ hp =>
  orderFindingSemiclassical_support a N m hw hs4 (lowerMBalancedU_lowSupport_named P R _ hws hf hp)

section Specialise
variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs] [MeasureClass qs]
variable {P : ShorLoweringPolicy} {R : Balanced.Rule} {a N c m : ℕ} {y work scratch : ExtReg}
  {flag : ℕ} {hw : ModMulCircuitWorkspaceOK y work}
  {hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag}
  {hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)}
  {hf : MGate.Fits P R (orderFindingSemiclassical a N c m y work scratch flag hw hs4)}

theorem orderFindingSemiclassicalLowBalanced_recordProb_init_X_named {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalanced P R a N c m y work scratch flag hw hs4
        hws).eval (MState.init (LowerGateClass.evalL (LowGate.X q) ψ₀))) r
      = recordProb ((orderFindingSemiclassicalLowBalanced P R a N c m y work scratch flag hw hs4
          hws).eval (MState.init ψ₀)) r :=
  MLowGate.recordProb_init_X _
    (fun h => hq (semiclassical_lowSupport_balanced P R a N c m y work scratch flag hw hs4 hws h))
    ψ₀ r

theorem orderFindingSemiclassicalLowBalanced_recordProb_decomp_named {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalanced P R a N c m y work scratch flag hw hs4
        hws).eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((orderFindingSemiclassicalLowBalanced P R a N c m y
          work scratch flag hw hs4 hws).eval
          (MState.init (MeasureClass.measProj (qubitReg q) o ψ₀))) r :=
  MLowGate.recordProb_decomp _
    (fun h => hq (semiclassical_lowSupport_balanced P R a N c m y work scratch flag hw hs4 hws h))
    ψ₀ r

theorem orderFindingSemiclassicalLowBalanced_recordProb_superpose_named {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (b0 : qs.Basis) (α β : ℂ)
    (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalanced P R a N c m y work scratch flag hw hs4
        hws).eval (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassicalLowBalanced P R a N c m y
          work scratch flag hw hs4 hws).eval (MState.init (qs.ket b0))) r :=
  MLowGate.recordProb_superpose _
    (fun h => hq (semiclassical_lowSupport_balanced P R a N c m y work scratch flag hw hs4 hws h))
    b0 α β r

theorem orderFindingSemiclassicalLowBalancedU_recordProb_init_X_named {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalancedU P R a N c m y work scratch flag hw hs4
        hws hf).eval (MState.init (LowerGateClass.evalL (LowGate.X q) ψ₀))) r
      = recordProb ((orderFindingSemiclassicalLowBalancedU P R a N c m y work scratch flag hw hs4
          hws hf).eval (MState.init ψ₀)) r :=
  MLowGate.recordProb_init_X _
    (fun h => hq (semiclassical_lowSupport_balancedU P R a N c m y work scratch flag hw hs4 hws
      hf h)) ψ₀ r

theorem orderFindingSemiclassicalLowBalancedU_recordProb_decomp_named {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalancedU P R a N c m y work scratch flag hw hs4
        hws hf).eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((orderFindingSemiclassicalLowBalancedU P R a N c m y
          work scratch flag hw hs4 hws hf).eval
          (MState.init (MeasureClass.measProj (qubitReg q) o ψ₀))) r :=
  MLowGate.recordProb_decomp _
    (fun h => hq (semiclassical_lowSupport_balancedU P R a N c m y work scratch flag hw hs4 hws
      hf h)) ψ₀ r

theorem orderFindingSemiclassicalLowBalancedU_recordProb_superpose_named {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (b0 : qs.Basis) (α β : ℂ)
    (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalancedU P R a N c m y work scratch flag hw hs4
        hws hf).eval (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassicalLowBalancedU P R a N c m y
          work scratch flag hw hs4 hws hf).eval (MState.init (qs.ket b0))) r :=
  MLowGate.recordProb_superpose _
    (fun h => hq (semiclassical_lowSupport_balancedU P R a N c m y work scratch flag hw hs4 hws
      hf h)) b0 α β r

end Specialise

end Readout
end Shor
