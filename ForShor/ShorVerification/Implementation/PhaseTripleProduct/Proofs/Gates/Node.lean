import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Gates.LeafSandwich
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Values.Semantics
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.GateLaws
/-!
# One PTP recursion level at the gate level

The PTP node circuit in ForShor's `LowGate` language, modelled on ForShor's
`compileAnnotatedOpsToSignedGateAux` (PhaseProduct), with three operand
families instead of two:

* the layout holds `3 k` slot registers `slot s i` (operand `s`, limb `i`), all
  of the node's working width `C`, pairwise disjoint;
* each table operation becomes **three** gates, one per operand: `ShiftL`,
  `ShiftR`, `Negate` on `slot s i`, `AddScaled (slot s d) (slot s src)`;
* the `t`-th `phaseProduct i` becomes the child on the triple
  `(slot 0 i, slot 1 i, slot 2 i)` with angle `φ · cₜ`; here the child is the
  compute–rotate–uncompute leaf `ptpLeafSandwich` (`PTP/LeafSandwich.lean`), sharing
  two clean ancillas `ta`, `ua` across all children (`ptpNodeCCPhase` keeps the
  original CCPhase-leaf node, `evalL_ptpNodeCCPhase_ket`).

`evalL_ptpNode_ket` (headline): on a basis state whose slots hold the
top-heavy limbs of three operands that fit signed `n` bits, whose two leaf
ancillas are off the slots and `|0⟩`, and with `C ≥ childWidth n T.ops`, the
node multiplies by `exp(i·π·φ·x₀·x₁·x₂)` and
returns the basis state unchanged. The proof is a classical simulation of the
three register files, using ForShor's basis-level gate laws
(`extToInt_addScaledBasis_dst`, `extToInt_shiftLBasis_of_fits`, ...), PTP
width soundness (`node_width_sound`: no write ever wraps) and the PTP node
identity.

Not covered here (stated in the inquiry records): the split of three parent
registers into the slots and the zero/sign extension to `C` (ForShor's
`PhaseSplitLayout` + `allocChunkGate`), reserve/workspace management, children
that are themselves nodes (only through the `ChildSpec` interface), and any
controlled variant: the circuit is uncontrolled. `evalL_ptpNode_ket` is one
recursion level with leaf children on pre-split slots, not the gate-level
correctness of a whole policy.
-/

namespace Shor
namespace PTP

open Shor Operations






/-- **The PTP node circuit with sandwich-leaf children** (default, 2026-10-28). Every
child is `ptpLeafSandwich` on the slot triple, sharing the two leaf ancillas `ta`, `ua`
(the children run one after another, and each returns them to `|0⟩`). -/
noncomputable def ptpNode (T : PTPTable) (Lay : NodeLayout T.k) (n : ℕ) (φ : Angle) (ta ua : ℕ) :
    LowGate :=
  body Lay (fun t i => ptpLeafSandwich (φ * coeffN T n t) (Lay.slot 0 i) (Lay.slot 1 i)
    (Lay.slot 2 i) ta ua) 0 T.ops

/-- The PTP node circuit with CCPhase-leaf children (documented alternative; the
original `ptpNode`). -/
noncomputable def ptpNodeCCPhase (T : PTPTable) (Lay : NodeLayout T.k) (n : ℕ) (φ : Angle) :
    LowGate :=
  body Lay (fun t i => ptpLeafCCPhase (φ * coeffN T n t) (Lay.slot 0 i) (Lay.slot 1 i)
    (Lay.slot 2 i)) 0 T.ops

/-! ## Basis bit lemmas for the arithmetic gates -/

section Bits

variable {Basis : Type*} [RegEncoding Basis]

theorem bit_shiftLBasis_out (r : ExtReg) (n : ℕ) (b : Basis) (q : ℕ) (hq : q ∉ r.active.qubits) :
    RegEncoding.bit q (shiftLBasis r n b) = RegEncoding.bit q b := by
  unfold shiftLBasis
  dsimp only
  split
  · exact RegEncoding.bit_writeNat_out _ _ _ _ hq
  · exact RegEncoding.bit_writeNat_out _ _ _ _ hq

theorem bit_shiftRBasis_out (r : ExtReg) (n : ℕ) (b : Basis) (q : ℕ) (hq : q ∉ r.active.qubits) :
    RegEncoding.bit q (shiftRBasis r n b) = RegEncoding.bit q b := by
  unfold shiftRBasis
  split
  · exact RegEncoding.bit_writeNat_out _ _ _ _ hq
  · exact RegEncoding.bit_writeNat_out _ _ _ _ hq

theorem bit_negateBasis_out (r : ExtReg) (b : Basis) (q : ℕ) (hq : q ∉ r.active.qubits) :
    RegEncoding.bit q (negateBasis r b) = RegEncoding.bit q b :=
  RegEncoding.bit_writeNat_out _ _ _ _ hq

theorem bit_addScaledBasis_out (d s : ExtReg) (neg : Bool) (sh : ℕ) (b : Basis) (q : ℕ)
    (hq : q ∉ d.active.qubits) :
    RegEncoding.bit q (addScaledBasis d s neg sh b) = RegEncoding.bit q b := by
  unfold addScaledBasis
  split
  · exact RegEncoding.bit_writeNat_out _ _ _ _ hq
  · rfl

end Bits

/-! ## The classical-simulation invariant -/

/-- Values of the three operands' register files. -/
abbrev Files (k : ℕ) := Fin 3 → Vals k

/-- Replace one operand's file. -/
def updF {k : ℕ} (V : Files k) (s : Fin 3) (W : Vals k) : Files k :=
  fun s' => if s' = s then W else V s'

/-- `b` holds the values `V` in the slots and agrees with `b0` off the slots. -/
def Inv {k : ℕ} {Basis : Type*} [RegEncoding Basis] (Lay : NodeLayout k) (b0 b : Basis)
    (V : Files k) : Prop :=
  (∀ s i, extToInt (Lay.slot s i) b = V s i) ∧
    (∀ q, (∀ s i, q ∉ (Lay.slot s i).active.qubits) → RegEncoding.bit q b = RegEncoding.bit q b0)

/-- The register an operation writes. -/
def dstOf {k : ℕ} : valid_ops k → Fin k
  | .shiftL i _ => i
  | .shiftR i _ => i
  | .negate i => i
  | .addScaled d _ _ _ => d
  | .phaseProduct i => i

theorem vStepF_ne {k : ℕ} (V : Vals k) (op : valid_ops k) (j : Fin k) (hj : j ≠ dstOf op) :
    vStepF id V op j = V j := by
  cases op <;> simp_all [vStepF, upd, dstOf]

/-- The basis map of `opGate Lay s op` (non-checkpoint operations). -/
noncomputable def opBasis {k : ℕ} {Basis : Type*} [RegEncoding Basis] (Lay : NodeLayout k)
    (s : Fin 3) (b : Basis) : valid_ops k → Basis
  | .shiftL i n => shiftLBasis (Lay.slot s i) n b
  | .shiftR i n => shiftRBasis (Lay.slot s i) n b
  | .negate i => negateBasis (Lay.slot s i) b
  | .addScaled d src neg sh => addScaledBasis (Lay.slot s d) (Lay.slot s src) neg sh b
  | .phaseProduct _ => b

theorem evalL_opGate {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) (s : Fin 3) (op : valid_ops k) (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs) (opGate Lay s op) (qs.ket b) = qs.ket (opBasis Lay s b op) := by
  cases op with
  | shiftL i n => exact LowerGateClass.evalL_shiftL_ket_total _ _ _
  | shiftR i n => exact LowerGateClass.evalL_shiftR_ket_total _ _ _
  | negate i => exact LowerGateClass.evalL_negate_ket_total _ _
  | addScaled d src neg sh => exact LowerGateClass.evalL_addScaled_ket_total _ _ _ _ _
  | phaseProduct i => exact LowerGateClass.evalL_id _

/-- One operand's gate keeps the invariant: the destination slot gets the exact
new value (no wrap, by the fit hypothesis), everything else is untouched. -/
theorem opBasis_inv {k : ℕ} {Basis : Type*} [RegEncoding Basis] (Lay : NodeLayout k)
    (hC : 0 < Lay.width) {b0 b : Basis} {V : Files k} (hI : Inv Lay b0 b V) (s : Fin 3)
    (op : valid_ops k) (hfit : ∀ j, |vStepF id (V s) op j| < 2 ^ (Lay.width - 1))
    (hex : ShiftExact (V s) op) (hok : opOK? op = true) :
    Inv Lay b0 (opBasis Lay s b op) (updF V s (vStepF id (V s) op)) := by
  obtain ⟨hval, hbit⟩ := hI
  have hfits : ∀ j, FitsSignedWidth (Lay.slot s j).width (vStepF id (V s) op j) := by
    intro j; rw [Lay.slot_width]; exact fits_of_abs_lt hC (hfit j)
  -- the destination slot's new value
  have hdst : extToInt (Lay.slot s (dstOf op)) (opBasis Lay s b op) =
      vStepF id (V s) op (dstOf op) := by
    have hf := hfits (dstOf op)
    cases op with
    | shiftL i n =>
        simp only [opBasis, dstOf] at hf ⊢
        simp only [vStepF, upd, id] at hf ⊢
        rw [mul_comm] at hf ⊢
        rw [← hval s i] at hf ⊢
        exact extToInt_shiftLBasis_of_fits _ _ _ hf
    | shiftR i n =>
        simp only [opBasis, dstOf] at hf ⊢
        simp only [vStepF, upd, id] at hf ⊢
        apply extToInt_shiftRBasis_of_exact _ _ _ _ _ hf
        rw [hval s i]
        exact (Int.mul_ediv_cancel' hex).symm
    | negate i =>
        simp only [opBasis, dstOf] at hf ⊢
        simp only [vStepF, upd, id] at hf ⊢
        rw [extToInt_negateBasis, hval s i]
        rw [← hval s i] at hf
        rw [hval s i] at hf
        exact tcWrapInt_eq_of_fits hf.1 (by rw [Lay.slot_width] at hf ⊢; exact hf)
    | addScaled d src neg sh =>
        simp only [opBasis, dstOf] at hf ⊢
        simp only [vStepF, upd, id] at hf ⊢
        have hne : d ≠ src := by simpa [opOK?] using hok
        have hds : ExtReg.ActiveDisjoint (Lay.slot s d) (Lay.slot s src) :=
          Lay.disjoint s d s src (by simp [hne])
        rw [extToInt_addScaledBasis_dst _ _ _ _ _ hds]
        have hv : addScaledValue (Lay.slot s d) (Lay.slot s src) neg sh b =
            V s d + (if neg then -1 else 1) * V s src * 2 ^ sh := by
          simp only [addScaledValue, hval]; ring
        rw [hv]
        exact tcWrapInt_eq_of_fits hf.1 hf
    | phaseProduct i => simp [opBasis, dstOf, vStepF, hval]
  -- every other slot keeps its value
  have hother : ∀ s' i', (s', i') ≠ (s, dstOf op) →
      extToInt (Lay.slot s' i') (opBasis Lay s b op) = extToInt (Lay.slot s' i') b := by
    intro s' i' hne
    have hd : ExtReg.ActiveDisjoint (Lay.slot s' i') (Lay.slot s (dstOf op)) :=
      Lay.disjoint s' i' s (dstOf op) hne
    cases op with
    | shiftL i n => exact extToInt_shiftLBasis_of_activeDisjoint _ _ _ _ hd
    | shiftR i n => exact extToInt_shiftRBasis_of_activeDisjoint _ _ _ _ hd
    | negate i => exact extToInt_negateBasis_of_activeDisjoint _ _ _ hd
    | addScaled d src neg sh =>
        have hne' : d ≠ src := by simpa [opOK?] using hok
        exact extToInt_addScaledBasis_of_activeDisjoint _ _ _ _ _ _
          (Lay.disjoint s d s src (by simp [hne'])) hd
    | phaseProduct i => rfl
  refine ⟨?_, ?_⟩
  · intro s' i'
    by_cases h : (s', i') = (s, dstOf op)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [hdst]; simp [updF]
    · rw [hother s' i' h, hval s' i']
      by_cases hs : s' = s
      · subst hs
        have hi : i' ≠ dstOf op := fun e => h (by rw [e])
        simp [updF, vStepF_ne (V s') op i' hi]
      · simp [updF, hs]
  · intro q hq
    have hq' : q ∉ (Lay.slot s (dstOf op)).active.qubits := hq s (dstOf op)
    rw [← hbit q hq]
    cases op with
    | shiftL i n => exact bit_shiftLBasis_out _ _ _ _ hq'
    | shiftR i n => exact bit_shiftRBasis_out _ _ _ _ hq'
    | negate i => exact bit_negateBasis_out _ _ _ hq'
    | addScaled d src neg sh => exact bit_addScaledBasis_out _ _ _ _ _ _ hq'
    | phaseProduct i => rfl

/-- Two bases with the invariant for the same values are equal. -/
theorem inv_unique {k : ℕ} {Basis : Type*} [RegEncoding Basis] (Lay : NodeLayout k)
    {b0 b1 b2 : Basis} {V : Files k} (h1 : Inv Lay b0 b1 V) (h2 : Inv Lay b0 b2 V) : b1 = b2 := by
  apply RegEncoding.basis_ext
  intro q
  by_cases hq : ∃ s i, q ∈ (Lay.slot s i).active.qubits
  · obtain ⟨s, i, hmem⟩ := hq
    set r := Lay.slot s i
    have hnat : RegEncoding.toNat r.active b1 = RegEncoding.toNat r.active b2 := by
      have e : extToInt r b1 = extToInt r b2 := by rw [h1.1, h2.1]
      unfold extToInt at e
      exact tcDecodeWidth_inj_of_lt (ExtReg.toNat_lt r b1) (ExtReg.toNat_lt r b2) e
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
    have key := fun (b : Basis) => RegEncoding.bit_eq_testBit_toNat r.active b ⟨j, hj⟩
    -- v4.36 port: was `rw [← hget, key b1, key b2, hnat]` with
    -- `hget : r.active.get ⟨j, hj⟩ = r.active.qubits[j] := rfl`; the rewrite left a term that is
    -- ill-typed at reducible transparency. The same chain of equalities, as a term:
    exact (key b1).trans ((congrArg (fun m => Nat.testBit m j) hnat).trans (key b2).symm)
  · push Not at hq
    rw [h1.2 q hq, h2.2 q hq]

/-! ## The body: classical simulation with phases -/

/-- The phase (in units of `π`) the body accumulates: at the `t`-th checkpoint
on limb `i`, `θ t · V₀ i · V₁ i · V₂ i`. -/
def bodyPhase {k : ℕ} (θ : ℕ → ℚ) : ℕ → Files k → Prog k → ℚ
  | _, _, [] => 0
  | t, V, .phaseProduct i :: ops =>
      θ t * (V 0 i : ℚ) * (V 1 i : ℚ) * (V 2 i : ℚ) + bodyPhase θ (t + 1) V ops
  | t, V, .shiftL i n :: ops => bodyPhase θ t (fun s => vStepF id (V s) (.shiftL i n)) ops
  | t, V, .shiftR i n :: ops => bodyPhase θ t (fun s => vStepF id (V s) (.shiftR i n)) ops
  | t, V, .negate i :: ops => bodyPhase θ t (fun s => vStepF id (V s) (.negate i)) ops
  | t, V, .addScaled d s neg sh :: ops =>
      bodyPhase θ t (fun s' => vStepF id (V s') (.addScaled d s neg sh)) ops

theorem updF_three {k : ℕ} (V : Files k) (op : valid_ops k) :
    updF (updF (updF V 0 (vStepF id (V 0) op)) 1 (vStepF id (V 1) op)) 2 (vStepF id (V 2) op) =
      fun s => vStepF id (V s) op := by
  funext s
  fin_cases s <;> simp [updF]

/-- One non-checkpoint operation: three gates, no phase, invariant kept. -/
theorem opGates_step {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) (hC : 0 < Lay.width) {b0 b : qs.Basis} {V : Files k}
    (hI : Inv Lay b0 b V) (op : valid_ops k)
    (hfit : ∀ s j, |vStepF id (V s) op j| < 2 ^ (Lay.width - 1))
    (hex : ∀ s, ShiftExact (V s) op) (hok : opOK? op = true) :
    ∃ b', LowerGateClass.evalL (qs := qs) (opGates Lay op) (qs.ket b) = qs.ket b' ∧
      Inv Lay b0 b' (fun s => vStepF id (V s) op) := by
  have h1 := opBasis_inv Lay hC hI 0 op (hfit 0) (hex 0) hok
  have h2 := opBasis_inv Lay hC h1 1 op (by simpa [updF] using hfit 1)
    (by simpa [updF] using hex 1) hok
  have h3 := opBasis_inv Lay hC h2 2 op (by simpa [updF] using hfit 2)
    (by simpa [updF] using hex 2) hok
  refine ⟨opBasis Lay 2 (opBasis Lay 1 (opBasis Lay 0 b op) op) op, ?_, ?_⟩
  · rw [opGates, LowerGateClass.evalL_seq, LowerGateClass.evalL_seq, evalL_opGate, evalL_opGate,
      evalL_opGate]
  · have e : updF (updF (updF V 0 (vStepF id (V 0) op)) 1
        (vStepF id ((updF V 0 (vStepF id (V 0) op)) 1) op)) 2
        (vStepF id ((updF (updF V 0 (vStepF id (V 0) op)) 1
          (vStepF id ((updF V 0 (vStepF id (V 0) op)) 1) op)) 2) op) =
        fun s => vStepF id (V s) op := by
      funext s
      fin_cases s <;> simp [updF]
    rw [← e]; exact h3

/-- Leaf children read the slot values. -/
theorem evalL_leafCCPhaseChild {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) {b0 b : qs.Basis} {V : Files k} (hI : Inv Lay b0 b V) (θ : ℚ) (i : Fin k) :
    LowerGateClass.evalL (qs := qs) (ptpLeafCCPhase θ (Lay.slot 0 i) (Lay.slot 1 i) (Lay.slot 2 i))
        (qs.ket b) =
      Complex.exp (((Angle.toReal (θ * (V 0 i : ℚ) * (V 1 i : ℚ) * (V 2 i : ℚ)) : ℝ) : ℂ) *
        Complex.I) • qs.ket b := by
  rw [evalL_ptpLeafCCPhase_ket, hI.1, hI.1, hI.1]
  congr 2
  simp only [Angle.toReal]
  push_cast
  ring

/-- What a child circuit must do for the body proof: on every basis state on
which its three input slots fit signed `C` bits and which agrees with `b0` off
the slots (so the child's own workspace is as clean as in `b0`), it multiplies
by `exp(i π θₜ · ⟦slot 0 i⟧ ⟦slot 1 i⟧ ⟦slot 2 i⟧)` and changes nothing else.
The CCPhase leaf meets it unconditionally (`leafCCPhase_childSpec`), the sandwich
leaf given its two ancillas off the slots and clean in `b0` (`leafSandwich_childSpec`);
a recursive child node would meet it given its own clean workspace. -/
def ChildSpec {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) (θ : ℕ → ℚ) (b0 : qs.Basis) (child : ℕ → Fin k → LowGate) : Prop :=
  ∀ (t : ℕ) (i : Fin k) (b : qs.Basis),
    (∀ s, FitsSignedWidth Lay.width (extToInt (Lay.slot s i) b)) →
    (∀ q, (∀ s j, q ∉ (Lay.slot s j).active.qubits) →
      RegEncoding.bit q b = RegEncoding.bit q b0) →
    LowerGateClass.evalL (qs := qs) (child t i) (qs.ket b) =
      Complex.exp (((Angle.toReal (θ t * (extToInt (Lay.slot 0 i) b : ℚ) *
        (extToInt (Lay.slot 1 i) b : ℚ) * (extToInt (Lay.slot 2 i) b : ℚ)) : ℝ) : ℂ) *
        Complex.I) • qs.ket b

theorem leafCCPhase_childSpec {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) (θ : ℕ → ℚ) (b0 : qs.Basis) :
    ChildSpec Lay θ b0
      (fun t i => ptpLeafCCPhase (θ t) (Lay.slot 0 i) (Lay.slot 1 i) (Lay.slot 2 i)) := by
  intro t i b _ _
  rw [evalL_ptpLeafCCPhase_ket]
  congr 2
  simp only [Angle.toReal]
  push_cast
  ring

/-- Slot triples of a node layout are active-disjoint. -/
theorem triple_disjoint {k : ℕ} (Lay : NodeLayout k) (i : Fin k) :
    LeafActiveDisjoint (Lay.slot 0 i) (Lay.slot 1 i) (Lay.slot 2 i) :=
  ⟨Lay.disjoint 0 i 1 i (by simp), Lay.disjoint 0 i 2 i (by simp), Lay.disjoint 1 i 2 i (by simp)⟩

/-- The two leaf ancillas of a node: distinct, and off every slot. -/
def NodeAnc {k : ℕ} (Lay : NodeLayout k) (ta ua : ℕ) : Prop :=
  ta ≠ ua ∧ ∀ s i, ta ∉ (Lay.slot s i).active.qubits ∧ ua ∉ (Lay.slot s i).active.qubits

theorem NodeAnc.sandwichAnc {k : ℕ} {Lay : NodeLayout k} {ta ua : ℕ} (h : NodeAnc Lay ta ua)
    (i : Fin k) : SandwichAnc (Lay.slot 0 i) (Lay.slot 1 i) (Lay.slot 2 i) ta ua :=
  ⟨h.1, (h.2 0 i).1, (h.2 1 i).1, (h.2 2 i).1, (h.2 0 i).2, (h.2 1 i).2, (h.2 2 i).2⟩

/-- **The sandwich leaf meets `ChildSpec`** when its ancillas are off the slots and
clean in the reference state `b0` (a `ChildSpec` state agrees with `b0` off the
slots, so its ancillas are clean too). -/
theorem leafSandwich_childSpec {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) (θ : ℕ → ℚ) (b0 : qs.Basis) (ta ua : ℕ) (hA : NodeAnc Lay ta ua)
    (h0 : AncClean ta ua b0) :
    ChildSpec Lay θ b0
      (fun t i => ptpLeafSandwich (θ t) (Lay.slot 0 i) (Lay.slot 1 i) (Lay.slot 2 i) ta ua) := by
  intro t i b _ hoff
  have hclean : AncClean ta ua b :=
    ⟨(hoff ta fun s j => (hA.2 s j).1).trans h0.1, (hoff ua fun s j => (hA.2 s j).2).trans h0.2⟩
  rw [evalL_ptpLeafSandwich_ket _ _ _ _ _ _ b (triple_disjoint Lay i) (hA.sandwichAnc i) hclean]
  congr 2
  simp only [Angle.toReal]
  push_cast
  ring

/-- **Body simulation (any children meeting `ChildSpec`).** Along a run whose
values stay below `2^(C-1)` with exact shifts and distinct `addScaled`
operands, the body maps `ket b` to `exp(i π · bodyPhase) • ket b'`, where `b'`
holds the final values and agrees with `b0` off the slots. -/
theorem body_eval_gen {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) (hC : 0 < Lay.width) (θ : ℕ → ℚ) (b0 : qs.Basis)
    (child : ℕ → Fin k → LowGate) (hchild : ChildSpec Lay θ b0 child) :
    ∀ (ops : Prog k) (t : ℕ) (V : Files k) (b : qs.Basis), Inv Lay b0 b V →
      (∀ s, AllBounded (Lay.width - 1) (V s) ops) → (∀ s, ExactShifts (V s) ops) →
      wellFormed? ops = true →
      ∃ b', LowerGateClass.evalL (qs := qs) (body Lay child t ops) (qs.ket b) =
        Complex.exp (((Angle.toReal (bodyPhase θ t V ops) : ℝ) : ℂ) * Complex.I) • qs.ket b' ∧
        Inv Lay b0 b' (fun s => (runF id (V s) ops).2)
  | [], t, V, b, hI, _, _, _ => ⟨b, by simp [body, bodyPhase, LowerGateClass.evalL_id], by
      simpa [runF] using hI⟩
  | op :: ops, t, V, b, hI, hB, hX, hW => by
      have hok : opOK? op = true := by
        simp only [wellFormed?, Bool.and_eq_true] at hW; exact hW.1
      have hW' : wellFormed? ops = true := by
        simp only [wellFormed?, Bool.and_eq_true] at hW; exact hW.2
      have hB' : ∀ s, AllBounded (Lay.width - 1) (vStepF id (V s) op) ops := fun s => (hB s).2
      have hX' : ∀ s, ExactShifts (vStepF id (V s) op) ops := fun s => (hX s).2
      have hfit : ∀ s j, |vStepF id (V s) op j| < 2 ^ (Lay.width - 1) := fun s => (hB' s).head
      cases op with
      | phaseProduct i =>
          have hB'' : ∀ s, AllBounded (Lay.width - 1) (V s) ops := fun s => (hB s).2
          have hX'' : ∀ s, ExactShifts (V s) ops := fun s => (hX s).2
          obtain ⟨b', he, hI'⟩ := body_eval_gen Lay hC θ b0 child hchild ops (t + 1) V b hI hB''
            hX'' hW'
          refine ⟨b', ?_, by simpa [runF] using hI'⟩
          have hpre : ∀ s, FitsSignedWidth Lay.width (extToInt (Lay.slot s i) b) := by
            intro s; rw [hI.1]; exact fits_of_abs_lt hC ((hB s).1 i)
          simp only [body, bodyPhase, LowerGateClass.evalL_seq]
          rw [hchild t i b hpre hI.2, hI.1, hI.1, hI.1, LowerGateClass.evalL_smul, he, smul_smul,
            ← Complex.exp_add, Angle.toReal_add]
          congr 2
          push_cast
          ring
      | shiftL i n =>
          obtain ⟨b1, he1, hI1⟩ := opGates_step Lay hC hI _ hfit (fun s => (hX s).1) hok
          obtain ⟨b', he, hI'⟩ := body_eval_gen Lay hC θ b0 child hchild ops t _ b1 hI1 hB' hX' hW'
          exact ⟨b', by simp only [body, bodyPhase, LowerGateClass.evalL_seq]; rw [he1, he], by
            simpa [runF] using hI'⟩
      | shiftR i n =>
          obtain ⟨b1, he1, hI1⟩ := opGates_step Lay hC hI _ hfit (fun s => (hX s).1) hok
          obtain ⟨b', he, hI'⟩ := body_eval_gen Lay hC θ b0 child hchild ops t _ b1 hI1 hB' hX' hW'
          exact ⟨b', by simp only [body, bodyPhase, LowerGateClass.evalL_seq]; rw [he1, he], by
            simpa [runF] using hI'⟩
      | negate i =>
          obtain ⟨b1, he1, hI1⟩ := opGates_step Lay hC hI _ hfit (fun s => (hX s).1) hok
          obtain ⟨b', he, hI'⟩ := body_eval_gen Lay hC θ b0 child hchild ops t _ b1 hI1 hB' hX' hW'
          exact ⟨b', by simp only [body, bodyPhase, LowerGateClass.evalL_seq]; rw [he1, he], by
            simpa [runF] using hI'⟩
      | addScaled d src neg sh =>
          obtain ⟨b1, he1, hI1⟩ := opGates_step Lay hC hI _ hfit (fun s => (hX s).1) hok
          obtain ⟨b', he, hI'⟩ := body_eval_gen Lay hC θ b0 child hchild ops t _ b1 hI1 hB' hX' hW'
          exact ⟨b', by simp only [body, bodyPhase, LowerGateClass.evalL_seq]; rw [he1, he], by
            simpa [runF] using hI'⟩


/-- The body phase as a sum over checkpoints of the run's checkpoint values. -/
theorem bodyPhase_eq {k : ℕ} (θ : ℕ → ℚ) :
    ∀ (ops : Prog k) (t : ℕ) (V : Files k),
      bodyPhase θ t V ops =
        ∑ j ∈ Finset.range (cpCount ops), θ (t + j) *
          ((runF id (V 0) ops).1.getD j 0 : ℚ) * ((runF id (V 1) ops).1.getD j 0 : ℚ) *
          ((runF id (V 2) ops).1.getD j 0 : ℚ)
  | [], t, V => by simp [bodyPhase, cpCount]
  | op :: ops, t, V => by
      cases op with
      | phaseProduct i =>
          simp only [bodyPhase, cpCount, runF]
          rw [Finset.sum_range_succ', bodyPhase_eq θ ops (t + 1) V]
          simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
          rw [add_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show t + (j + 1) = t + 1 + j by omega]
      | shiftL i n => simp only [bodyPhase, cpCount, runF]; exact bodyPhase_eq θ ops t _
      | shiftR i n => simp only [bodyPhase, cpCount, runF]; exact bodyPhase_eq θ ops t _
      | negate i => simp only [bodyPhase, cpCount, runF]; exact bodyPhase_eq θ ops t _
      | addScaled d s neg sh => simp only [bodyPhase, cpCount, runF]; exact bodyPhase_eq θ ops t _

theorem cpCount_eq_length {k : ℕ} (f : ℤ → ℤ) :
    ∀ (ops : Prog k) (V : Vals k), (runF f V ops).1.length = cpCount ops
  | [], _ => rfl
  | op :: ops, V => by
      cases op <;> simp [runF, cpCount, cpCount_eq_length f ops]

/-! ## Headline: one PTP recursion level, gate level -/

/-- **PTP node body correctness (gate level, any children meeting `ChildSpec`).**
Let `T` pass the PTP contract, `x₀, x₁, x₂` fit signed `n` bits, and the layout
have working width `C ≥ childWidth n T.ops`. On a basis state `b` whose slot
`(s, i)` holds limb `i` of `xₛ`, if every child meets `ChildSpec` relative to
`b`, the body multiplies by `exp(i · π φ · x₀ · x₁ · x₂)` and returns `b`. -/
theorem evalL_nodeBody_ket {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (T : PTPTable) (hT : T.contract = true) (n : ℕ) (x : Fin 3 → ℤ)
    (hx : ∀ s, FitsSignedWidth n (x s)) (Lay : NodeLayout T.k)
    (hC : childWidth n T.ops ≤ Lay.width) (φ : Angle) (b : qs.Basis)
    (hb : ∀ s i, extToInt (Lay.slot s i) b = limbsAt T.k (limbWidth n T.k) (x s) i)
    (child : ℕ → Fin T.k → LowGate) (hchild : ChildSpec Lay (fun t => φ * coeffN T n t) b child) :
    LowerGateClass.evalL (qs := qs) (body Lay child 0 T.ops) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((x 0 : ℤ) : ℂ) * ((x 1 : ℤ) : ℂ) * ((x 2 : ℤ) : ℂ))) • qs.ket b := by
  obtain ⟨hk, _, hsafe⟩ := (PTPTable.contract_iff T).mp hT
  set L : Files T.k := fun s => limbsAt T.k (limbWidth n T.k) (x s) with hL
  have hn : ∀ s : Fin 3, 0 < (fun _ => n) s := fun s => (hx s).1
  have hws := fun s => node_width_sound T hT (fun _ => n) hn x hx s
  have hCpos : 0 < Lay.width := lt_of_lt_of_le (by simp [childWidth, childWidth3]) hC
  -- AllBounded at C - 1 and exact shifts, per operand
  have hrun := (returnsToStartCheck_iff T.ops State.start_state).mp
    hsafe.returns_start
  have hB : ∀ s, AllBounded (Lay.width - 1) (L s) T.ops := by
    intro s
    obtain ⟨hex, _⟩ := run_val (L s) T.ops State.start_state State.start_state hrun
    rw [valOf_start] at hex
    have hm : (fun _ => n : Fin 3 → ℕ) s = n := rfl
    have hW : limbWidth3 (fun _ => n) T.k = limbWidth n T.k := rfl
    have hb0 := scan_sound T.ops (initW n (limbWidth n T.k) T.k) (L s) (initW_length _ _ _)
      (init_bound n (limbWidth n T.k) T.k (by omega)
        (lowerBound_le _ _ _ (by omega) (hx s).1 (by rw [limbWidth_eq])) (x s) (hx s)) hex
    refine AllBounded.mono ?_ hb0
    have : scanMax (initW n (limbWidth n T.k) T.k) T.ops ≤ childWidth n T.ops - 1 := by
      simp only [childWidth, childWidth3, ← hW]
      fin_cases s <;> simp
    omega
  have hX : ∀ s, ExactShifts (L s) T.ops := by
    intro s
    obtain ⟨hex, _⟩ := run_val (L s) T.ops State.start_state State.start_state hrun
    rwa [valOf_start] at hex
  have hI0 : Inv Lay b b L := ⟨fun s i => hb s i, fun _ _ => rfl⟩
  obtain ⟨b', he, hI'⟩ := body_eval_gen Lay hCpos (fun t => φ * coeffN T n t) b child hchild
    T.ops 0 L b hI0 hB hX hsafe.safe_add
  -- the run returns the limbs, so the final basis state is `b`
  have hfin : (fun s => (runF id (L s) T.ops).2) = L := by
    funext s; exact (hws s).2.2.2.2
  rw [hfin] at hI'
  have hb' : b' = b := inv_unique Lay hI' hI0
  rw [he, hb']
  congr 2
  -- the accumulated phase is `φ x₀ x₁ x₂`
  rw [bodyPhase_eq]
  have hlen : cpCount T.ops = T.pts.length := by
    rw [← cpCount_eq_length id T.ops (L 0)]
    exact (congrArg List.length (children_eq T hT n (x 0))).trans (by simp)
  rw [hlen, ← Fin.sum_univ_eq_sum_range (fun j => φ * coeffN T n (0 + j) *
      ((runF id (L 0) T.ops).1.getD j 0 : ℚ) * ((runF id (L 1) T.ops).1.getD j 0 : ℚ) *
      ((runF id (L 2) T.ops).1.getD j 0 : ℚ))]
  have key := node_identity T hT n φ x
  have hsum : (∑ j : Fin T.pts.length, φ * coeffN T n (0 + (j : ℕ)) *
      ((runF id (L 0) T.ops).1.getD j 0 : ℚ) * ((runF id (L 1) T.ops).1.getD j 0 : ℚ) *
      ((runF id (L 2) T.ops).1.getD j 0 : ℚ)) = φ * x 0 * x 1 * x 2 := by
    rw [← key]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcj : coeffN T n (0 + (j : ℕ)) = T.coeff n j := by
      simp [coeffN, j.2]
    rw [hcj, Fin.prod_univ_three]
    have h0 := children_getD T hT n (x 0) j
    have h1 := children_getD T hT n (x 1) j
    have h2 := children_getD T hT n (x 2) j
    simp only [PTPTable.children] at h0 h1 h2
    simp only [hL, h0, h1, h2]
    ring
  rw [hsum]
  simp only [Angle.toReal]
  push_cast
  ring

/-- **PTP node correctness (gate level, sandwich-leaf children).** Let `T` pass the PTP
contract, `x₀, x₁, x₂` fit signed `n` bits, and the node layout have working width
`C ≥ childWidth n T.ops`. Let the two leaf ancillas `ta ≠ ua` lie off every slot and
be `|0⟩` in `b`. On a basis state whose slot `(s, i)` holds limb `i` of `xₛ`
(top-heavy split at `n / k`), the node circuit multiplies by
`exp(i · π φ · x₀ · x₁ · x₂)` and leaves the basis state unchanged (ancillas
included). -/
theorem evalL_ptpNode_ket {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (T : PTPTable) (hT : T.contract = true) (n : ℕ) (x : Fin 3 → ℤ)
    (hx : ∀ s, FitsSignedWidth n (x s)) (Lay : NodeLayout T.k)
    (hC : childWidth n T.ops ≤ Lay.width) (φ : Angle) (ta ua : ℕ) (hA : NodeAnc Lay ta ua)
    (b : qs.Basis) (hclean : AncClean ta ua b)
    (hb : ∀ s i, extToInt (Lay.slot s i) b = limbsAt T.k (limbWidth n T.k) (x s) i) :
    LowerGateClass.evalL (qs := qs) (ptpNode T Lay n φ ta ua) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((x 0 : ℤ) : ℂ) * ((x 1 : ℤ) : ℂ) * ((x 2 : ℤ) : ℂ))) • qs.ket b :=
  evalL_nodeBody_ket T hT n x hx Lay hC φ b hb _
    (leafSandwich_childSpec Lay _ b ta ua hA hclean)

/-- **PTP node correctness, CCPhase-leaf children** (documented alternative: the
original `evalL_ptpNode_ket`, no ancilla hypotheses). -/
theorem evalL_ptpNodeCCPhase_ket {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (T : PTPTable) (hT : T.contract = true) (n : ℕ) (x : Fin 3 → ℤ)
    (hx : ∀ s, FitsSignedWidth n (x s)) (Lay : NodeLayout T.k)
    (hC : childWidth n T.ops ≤ Lay.width) (φ : Angle) (b : qs.Basis)
    (hb : ∀ s i, extToInt (Lay.slot s i) b = limbsAt T.k (limbWidth n T.k) (x s) i) :
    LowerGateClass.evalL (qs := qs) (ptpNodeCCPhase T Lay n φ) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((x 0 : ℤ) : ℂ) * ((x 1 : ℤ) : ℂ) * ((x 2 : ℤ) : ℂ))) • qs.ket b :=
  evalL_nodeBody_ket T hT n x hx Lay hC φ b hb _ (leafCCPhase_childSpec Lay _ b)

end PTP
end Shor
