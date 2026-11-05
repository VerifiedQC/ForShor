import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Gates.Node
import ForShor.ShorVerification.Framework.Gatecount.ResourceModel
/-!
# PTP gate census and qubit layout, from the gate-level lowering

The analogue of ForShor's `ResourceModel` / `Workspace.reserveNeed` for PTP,
read off the circuits of `PTP/Leaf.lean` and `PTP/Node.lean` under ForShor's
own structural resource model `Shor.shorGateResourceModel` (Cuccaro adders,
Cuccaro-based negation, shifts as wiring; basis `H, X, CNOT, Toffoli, Rz` plus
peak clean scratch ancillas).

Proved, for one node at working width `C` (all `3k` slots of width `C`), with
`A`, `N`, `P` the numbers of `addScaled`, `negate` and `phaseProduct` operations of
the table (`P = 3k - 2` for a contract-passing table).

**Sandwich-leaf children (default; `ptpNode_resources`, `ptpNode_adjToffCount`,
`ptpNode_cleanAnc_le`, `ptpNode_qubits_le`):**

    Rz      = P · C³                                  (exactly one per leaf cell)
    Toffoli = 3 (A + N)(2C - 3) + P · 2 (C² + C³)     (leaves: P(C² + C³) And + as many And†)
    † Toffoli (uncompute) = P · (C² + C³)
    CNOT    = 3 (A + N)(5C - 7)
    X       = 3 (A (2C - 6) + N (C + (2C - 6) + 2))
    H       = 0
    model scratch ancillas ≤ C + 1;  qubits touched ≤ 3 k C + 2 (slots + 2 leaf ancillas)

**CCPhase-leaf children (documented alternative; `ptpNodeCCPhase_resources`, ...):**
`Rz = P · 5C³`, `CNOT = 3(A+N)(5C-7) + P · 2C³`, `Toffoli = 3(A+N)(2C-3) + P · 2C³`,
same `X`, `H`; qubits ≤ 3 k C.

Leaves alone (width `w` operands): sandwich `Rz = w³, Toffoli = 2(w² + w³), CNOT = 0`
(`ptpLeafSandwich_resources`, any resource model, no disjointness hypothesis);
CCPhase `Rz = 5 w³, CNOT = 2 w³, Toffoli = 2 w³` (`leafCCPhase_resources`).

`ptpResources P n` (policy level) composes the node formula recursively down
the policy's ladder, with the leaf formula at the bottom; `ptpReserveNeed P n`
is ForShor's `reserveNeed` recursion for three operands. At depth one (the
child width is a leaf width) `ptpResources` is the proved node census
(`ptpResources_depth_one`; `ptpResourcesCCPhase`, `ptpResourcesCCPhase_depth_one` for the CCPhase leaf); deeper levels compose the same node formula, which
is proved per node but whose composition is not yet a gate-level theorem
(`PTP/Node.lean`, residual).
-/

namespace Shor
namespace PTP

open Shor Operations

/-! ## The leaf -/

/-- Resources of one cell (distinct qubits). -/
theorem cell_resources (M : LowGateResourceModel) (φ : Angle) (t : Cell)
    (h : t.1.1 ≠ t.2.1.1 ∧ t.1.1 ≠ t.2.2.1 ∧ t.2.1.1 ≠ t.2.2.1) :
    LowGate.resources M (cellGate φ t) = { rz := 5, cnot := 2, toffoli := 2 } := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [cellGate, LowGate.CCPhase, LowGate.CPhase, h1, h2, h3, LowGate.resources,
    GateResources.seq]

/-- **CCPhase-leaf census**: an additive field of the leaf is `|x||y||z|` times the cell's. -/
theorem leafCCPhase_field (F : AddField) (M : LowGateResourceModel) (φ : Angle) (x y z : ExtReg)
    (h : LeafActiveDisjoint x y z) :
    F.f (LowGate.resources M (ptpLeafCCPhase φ x y z)) =
      F.f { rz := 5, cnot := 2, toffoli := 2 } * (x.width * y.width * z.width) := by
  unfold ptpLeafCCPhase
  rw [field_sequence, List.map_map, ← leafCells_length x y z]
  exact sum_const_of_mem _ _ _ fun t ht => by
    simp only [Function.comp, cell_resources M φ t (cell_distinct' h ht)]

theorem leafCCPhase_resources (M : LowGateResourceModel) (φ : Angle) (x y z : ExtReg)
    (h : LeafActiveDisjoint x y z) :
    let R := LowGate.resources M (ptpLeafCCPhase φ x y z)
    let w3 := x.width * y.width * z.width
    R.rz = 5 * w3 ∧ R.cnot = 2 * w3 ∧ R.toffoli = 2 * w3 ∧ R.x = 0 ∧ R.h = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact leafCCPhase_field fRz M φ x y z h
  · exact leafCCPhase_field fCnot M φ x y z h
  · exact leafCCPhase_field fToff M φ x y z h
  · have := leafCCPhase_field fX M φ x y z h; simpa [fX] using this
  · have := leafCCPhase_field fH M φ x y z h; simpa [fH] using this

/-! ## The node -/

/-- Resources of one operation on one operand at slot width `C` under ForShor's
`shorGateResourceModel`. -/
def opRes (C : ℕ) {k : ℕ} : valid_ops k → GateResources
  | .addScaled _ _ _ _ => cuccaroModAddResources C
  | .negate _ =>
      { h := (cuccaroModAddResources C).h
        x := C + (cuccaroModAddResources C).x + 2
        cnot := (cuccaroModAddResources C).cnot
        toffoli := (cuccaroModAddResources C).toffoli
        rz := (cuccaroModAddResources C).rz
        cleanAnc := C + (cuccaroModAddResources C).cleanAnc }
  | _ => {}

theorem opGate_resources {k : ℕ} (Lay : NodeLayout k) (s : Fin 3) (op : valid_ops k) :
    LowGate.resources shorGateResourceModel (opGate Lay s op) = opRes Lay.width op := by
  cases op with
  | shiftL i n => rfl
  | shiftR i n => rfl
  | negate i =>
      simp only [opGate, LowGate.resources, shorGateResourceModel, negateResources, opRes,
        Lay.slot_width]
  | addScaled d src neg sh =>
      simp only [opGate, LowGate.resources, shorGateResourceModel, addScaledResources, opRes,
        Lay.slot_width]
  | phaseProduct i => rfl

/-- An additive field of the body, operation by operation. -/
def bodyField (F : AddField) {k : ℕ} (C : ℕ) (childF : ℕ) : Prog k → ℕ
  | [] => 0
  | .phaseProduct _ :: ops => childF + bodyField F C childF ops
  | op :: ops => 3 * F.f (opRes C op) + bodyField F C childF ops

theorem body_field (F : AddField) {k : ℕ} (Lay : NodeLayout k) (child : ℕ → Fin k → LowGate)
    (childF : ℕ) (hchild : ∀ t i, F.f (LowGate.resources shorGateResourceModel (child t i)) = childF) :
    ∀ (ops : Prog k) (t : ℕ),
      F.f (LowGate.resources shorGateResourceModel (body Lay child t ops)) =
        bodyField F Lay.width childF ops
  | [], t => by simp [body, bodyField, LowGate.resources, F.zero]
  | op :: ops, t => by
      cases op with
      | phaseProduct i =>
          simp only [body, LowGate.resources, F.seq, bodyField, hchild, body_field F Lay child childF
            hchild ops]
      | _ =>
          simp only [body, opGates, LowGate.resources, F.seq, bodyField, opGate_resources,
            body_field F Lay child childF hchild ops]
          ring



theorem bodyField_eq (F : AddField) {k : ℕ} (C childF : ℕ) :
    ∀ ops : Prog k, bodyField F C childF ops =
      3 * (addCount ops * F.f (cuccaroModAddResources C) +
        negCount ops * F.f (opRes C (.negate (k := 1) 0))) + cpCount ops * childF
  | [] => by simp [bodyField, addCount, negCount, cpCount]
  | op :: ops => by
      have ih := bodyField_eq F C childF ops
      cases op <;> simp only [bodyField, addCount, negCount, cpCount, ih, opRes, F.zero] <;> ring

/-- **PTP node census (one node, sandwich-leaf children), proved from the lowering.**
Exactly one Rz per leaf cell: `P · C³`. -/
theorem ptpNode_resources (T : PTPTable) (Lay : NodeLayout T.k) (n : ℕ) (φ : Angle) (ta ua : ℕ) :
    let R := LowGate.resources shorGateResourceModel (ptpNode T Lay n φ ta ua)
    let C := Lay.width
    let A := addCount T.ops
    let N := negCount T.ops
    let P := cpCount T.ops
    R.rz = P * (C * C * C) ∧
    R.cnot = 3 * ((A + N) * (5 * C - 7)) ∧
    R.toffoli = 3 * ((A + N) * (2 * C - 3)) + P * (2 * (C * C + C * C * C)) ∧
    R.x = 3 * (A * (2 * C - 6) + N * (C + (2 * C - 6) + 2)) ∧
    R.h = 0 := by
  intro R C A N P
  have hw : ∀ s i, (Lay.slot s i).width = C := Lay.slot_width
  have go : ∀ F : AddField, F.f R =
      3 * (A * F.f (cuccaroModAddResources C) + N * F.f (opRes C (.negate (k := 1) 0))) +
        P * (C * C * (2 * F.f { toffoli := 1 } + C * F.f { toffoli := 2, rz := 1 })) := fun F =>
    (body_field F Lay (fun t i => ptpLeafSandwich (φ * coeffN T n t) (Lay.slot 0 i)
        (Lay.slot 1 i) (Lay.slot 2 i) ta ua)
      (C * C * (2 * F.f { toffoli := 1 } + C * F.f { toffoli := 2, rz := 1 }))
      (fun t i => by rw [leafSandwich_field, hw, hw, hw]) T.ops 0).trans
      (bodyField_eq F C _ T.ops)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := go fRz; simp only [fRz, opRes, cuccaroModAddResources] at h; rw [show R.rz = _ from h]; ring
  · have h := go fCnot; simp only [fCnot, opRes, cuccaroModAddResources] at h
    rw [show R.cnot = _ from h]; ring
  · have h := go fToff; simp only [fToff, opRes, cuccaroModAddResources] at h
    rw [show R.toffoli = _ from h]; ring
  · have h := go fX; simp only [fX, opRes, cuccaroModAddResources] at h
    rw [show R.x = _ from h]; ring
  · have h := go fH; simp only [fH, opRes, cuccaroModAddResources] at h; rw [show R.h = _ from h]; ring

/-- Uncomputing Toffolis (`† Toffoli`, the Qualtran And†) of the node: all in the
leaves, `P · (C² + C³)`; the same number of computing Toffolis (And) are in the
leaves, the rest of `R.toffoli` is the Cuccaro arithmetic. -/
theorem ptpNode_adjToffCount (T : PTPTable) (Lay : NodeLayout T.k) (n : ℕ) (φ : Angle)
    (ta ua : ℕ) :
    adjToffCount (ptpNode T Lay n φ ta ua) =
      cpCount T.ops * (Lay.width * Lay.width + Lay.width * Lay.width * Lay.width) := by
  have hw : ∀ s i, (Lay.slot s i).width = Lay.width := Lay.slot_width
  have hleaf : ∀ (θ : Angle) (i : Fin T.k), adjToffCount (ptpLeafSandwich θ (Lay.slot 0 i)
      (Lay.slot 1 i) (Lay.slot 2 i) ta ua) = Lay.width * Lay.width + Lay.width * Lay.width * Lay.width := by
    intro θ i
    have := (ptpLeafSandwich_counts θ (Lay.slot 0 i) (Lay.slot 1 i) (Lay.slot 2 i) ta ua).2.2.1
    rw [this, hw, hw, hw]
  have hop : ∀ (s : Fin 3) (op : valid_ops T.k), adjToffCount (opGate Lay s op) = 0 := by
    intro s op; cases op <;> rfl
  unfold ptpNode
  generalize 0 = t
  induction T.ops generalizing t with
  | nil => simp [body, adjToffCount, cpCount]
  | cons op ops ih =>
      cases op with
      | phaseProduct i =>
          simp only [body, adjToffCount, hleaf, ih, cpCount]; ring
      | _ =>
          simp only [body, opGates, adjToffCount, hop, ih, cpCount]; ring

/-- **PTP node census, CCPhase-leaf children** (documented alternative). -/
theorem ptpNodeCCPhase_resources (T : PTPTable) (Lay : NodeLayout T.k) (n : ℕ) (φ : Angle) :
    let R := LowGate.resources shorGateResourceModel (ptpNodeCCPhase T Lay n φ)
    let C := Lay.width
    let A := addCount T.ops
    let N := negCount T.ops
    let P := cpCount T.ops
    R.rz = P * (5 * (C * C * C)) ∧
    R.cnot = 3 * ((A + N) * (5 * C - 7)) + P * (2 * (C * C * C)) ∧
    R.toffoli = 3 * ((A + N) * (2 * C - 3)) + P * (2 * (C * C * C)) ∧
    R.x = 3 * (A * (2 * C - 6) + N * (C + (2 * C - 6) + 2)) ∧
    R.h = 0 := by
  intro R C A N P
  have hw : ∀ s i, (Lay.slot s i).width = C := Lay.slot_width
  have go : ∀ F : AddField, F.f R =
      3 * (A * F.f (cuccaroModAddResources C) + N * F.f (opRes C (.negate (k := 1) 0))) +
        P * (F.f { rz := 5, cnot := 2, toffoli := 2 } * (C * C * C)) := fun F =>
    (body_field F Lay (fun t i => ptpLeafCCPhase (φ * coeffN T n t) (Lay.slot 0 i) (Lay.slot 1 i)
        (Lay.slot 2 i)) (F.f { rz := 5, cnot := 2, toffoli := 2 } * (C * C * C))
      (fun t i => by rw [leafCCPhase_field F _ _ _ _ _ (triple_disjoint Lay i), hw, hw, hw]) T.ops 0).trans
      (bodyField_eq F C _ T.ops)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := go fRz; simp only [fRz, opRes, cuccaroModAddResources] at h; rw [show R.rz = _ from h]; ring
  · have h := go fCnot; simp only [fCnot, opRes, cuccaroModAddResources] at h
    rw [show R.cnot = _ from h]; ring
  · have h := go fToff; simp only [fToff, opRes, cuccaroModAddResources] at h
    rw [show R.toffoli = _ from h]; ring
  · have h := go fX; simp only [fX, opRes, cuccaroModAddResources] at h
    rw [show R.x = _ from h]; ring
  · have h := go fH; simp only [fH, opRes, cuccaroModAddResources] at h; rw [show R.h = _ from h]; ring

/-- Peak model scratch of a body whose children need none: at most `C + 1`
(negation's constant-one register plus the Cuccaro carry). -/
theorem body_cleanAnc_le {k : ℕ} (Lay : NodeLayout k) (child : ℕ → Fin k → LowGate)
    (hchild : ∀ t i, (LowGate.resources shorGateResourceModel (child t i)).cleanAnc = 0) :
    ∀ (ops : Prog k) (t : ℕ),
      (LowGate.resources shorGateResourceModel (body Lay child t ops)).cleanAnc ≤ Lay.width + 1 := by
  have hop : ∀ (s : Fin 3) (op : valid_ops k),
      (LowGate.resources shorGateResourceModel (opGate Lay s op)).cleanAnc ≤ Lay.width + 1 := by
    intro s op
    rw [opGate_resources]
    cases op <;> simp [opRes, cuccaroModAddResources]
  intro ops
  induction ops with
  | nil => intro t; simp [body, LowGate.resources]
  | cons op ops ih =>
      intro t
      cases op with
      | phaseProduct i =>
          simp only [body, LowGate.resources, GateResources.seq, hchild]
          exact max_le (Nat.zero_le _) (ih _)
      | _ =>
          simp only [body, opGates, LowGate.resources, GateResources.seq]
          exact max_le (max_le (hop _ _) (max_le (hop _ _) (hop _ _))) (ih _)

/-- Peak model scratch ancillas of the (sandwich) node: at most `C + 1`. The two leaf
ancillas `ta`, `ua` are explicit qubits, counted in `ptpNode_qubits_le`. -/
theorem ptpNode_cleanAnc_le (T : PTPTable) (Lay : NodeLayout T.k) (n : ℕ) (φ : Angle)
    (ta ua : ℕ) :
    (LowGate.resources shorGateResourceModel (ptpNode T Lay n φ ta ua)).cleanAnc ≤ Lay.width + 1 :=
  body_cleanAnc_le Lay _ (fun _ _ => leafSandwich_cleanAnc _ _ _ _ _ _ _) T.ops 0

theorem ptpNodeCCPhase_cleanAnc_le (T : PTPTable) (Lay : NodeLayout T.k) (n : ℕ) (φ : Angle) :
    (LowGate.resources shorGateResourceModel (ptpNodeCCPhase T Lay n φ)).cleanAnc ≤ Lay.width + 1 := by
  have hleaf : ∀ (θ : Angle) (x y z : ExtReg),
      (LowGate.resources shorGateResourceModel (ptpLeafCCPhase θ x y z)).cleanAnc = 0 := by
    intro θ x y z
    unfold ptpLeafCCPhase
    induction leafCells x y z with
    | nil => rfl
    | cons c cs ih =>
        simp only [List.map_cons, LowGate.sequence, LowGate.resources, GateResources.seq, ih]
        simp only [cellGate, LowGate.CCPhase, LowGate.CPhase]
        split_ifs <;> simp [LowGate.resources, GateResources.seq]
  exact body_cleanAnc_le Lay _ (fun _ _ => hleaf _ _ _ _) T.ops 0

/-! ## Qubits -/

/-- All qubits of the node's slots. -/
def slotQubits {k : ℕ} (Lay : NodeLayout k) : Finset ℕ :=
  Finset.univ.biUnion fun s : Fin 3 => Finset.univ.biUnion fun i : Fin k =>
    (Lay.slot s i).active.qubits.toFinset

theorem mem_slotQubits {k : ℕ} (Lay : NodeLayout k) {s : Fin 3} {i : Fin k} {q : ℕ}
    (h : q ∈ (Lay.slot s i).active.qubits) : q ∈ slotQubits Lay := by
  simp only [slotQubits, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset]
  exact ⟨s, i, h⟩

theorem slotQubits_card_le {k : ℕ} (Lay : NodeLayout k) :
    (slotQubits Lay).card ≤ 3 * k * Lay.width := by
  unfold slotQubits
  refine (Finset.card_biUnion_le).trans ?_
  have h1 : ∀ s : Fin 3, (Finset.univ.biUnion fun i : Fin k =>
      (Lay.slot s i).active.qubits.toFinset).card ≤ k * Lay.width := by
    intro s
    refine (Finset.card_biUnion_le).trans ?_
    have : ∀ i : Fin k, ((Lay.slot s i).active.qubits.toFinset).card ≤ Lay.width := by
      intro i
      refine (List.toFinset_card_le _).trans ?_
      have := Lay.slot_width s i
      simp only [ExtReg.width, regSize, Reg.width] at this
      omega
    calc (∑ i : Fin k, ((Lay.slot s i).active.qubits.toFinset).card)
        ≤ ∑ _i : Fin k, Lay.width := Finset.sum_le_sum fun i _ => this i
      _ = k * Lay.width := by simp
  calc (∑ s : Fin 3, (Finset.univ.biUnion fun i : Fin k =>
        (Lay.slot s i).active.qubits.toFinset).card)
      ≤ ∑ _s : Fin 3, k * Lay.width := Finset.sum_le_sum fun s _ => h1 s
    _ = 3 * k * Lay.width := by simp; ring

theorem usedQubits_CCPhase_subset (a c d : ℕ) (θ : Angle) :
    LowGate.usedQubits (LowGate.CCPhase a c d θ) ⊆ {a, c, d} := by
  intro q hq
  simp only [LowGate.CCPhase, LowGate.CPhase] at hq
  split_ifs at hq <;> simp [LowGate.usedQubits] at hq <;> simp <;> tauto

/-- A body touches only the slots and what its children touch. -/
theorem body_usedQubits_subset {k : ℕ} (Lay : NodeLayout k) (child : ℕ → Fin k → LowGate)
    (S : Finset ℕ) (hS : slotQubits Lay ⊆ S) (hchild : ∀ t i, LowGate.usedQubits (child t i) ⊆ S) :
    ∀ (ops : Prog k) (t : ℕ), LowGate.usedQubits (body Lay child t ops) ⊆ S := by
  have hop : ∀ (s : Fin 3) (op : valid_ops k), LowGate.usedQubits (opGate Lay s op) ⊆ S := by
    intro s op q hq
    apply hS
    cases op with
    | shiftL i n => exact mem_slotQubits Lay (by simpa [opGate, LowGate.usedQubits, extRegActiveQubits] using hq)
    | shiftR i n => exact mem_slotQubits Lay (by simpa [opGate, LowGate.usedQubits, extRegActiveQubits] using hq)
    | negate i => exact mem_slotQubits Lay (by simpa [opGate, LowGate.usedQubits, extRegActiveQubits] using hq)
    | addScaled d src neg sh =>
        simp only [opGate, LowGate.usedQubits, extRegActiveQubits, Finset.mem_union,
          List.mem_toFinset] at hq
        rcases hq with hq | hq
        · exact mem_slotQubits Lay hq
        · exact mem_slotQubits Lay hq
    | phaseProduct i => simp [opGate, LowGate.usedQubits] at hq
  intro ops
  induction ops with
  | nil => intro t; simp [body, LowGate.usedQubits]
  | cons op ops ih =>
      intro t
      cases op with
      | phaseProduct i =>
          simp only [body, LowGate.usedQubits]
          exact Finset.union_subset (hchild _ i) (ih _)
      | _ =>
          simp only [body, opGates, LowGate.usedQubits]
          exact Finset.union_subset (Finset.union_subset (hop _ _)
            (Finset.union_subset (hop _ _) (hop _ _))) (ih _)

/-- **Qubits touched by the (sandwich) node**: the `3k` slots and the two leaf ancillas. -/
theorem ptpNode_usedQubits_subset (T : PTPTable) (Lay : NodeLayout T.k) (n : ℕ) (φ : Angle)
    (ta ua : ℕ) :
    LowGate.usedQubits (ptpNode T Lay n φ ta ua) ⊆ slotQubits Lay ∪ {ta, ua} := by
  refine body_usedQubits_subset Lay _ _ Finset.subset_union_left (fun t i => ?_) T.ops 0
  refine (ptpLeafSandwich_usedQubits_subset _ _ _ _ _ _).trans ?_
  have h : ∀ s, extRegActiveQubits (Lay.slot s i) ⊆ slotQubits Lay := fun s q hq =>
    mem_slotQubits Lay (by simpa [extRegActiveQubits] using hq)
  exact Finset.union_subset_union
    (Finset.union_subset (Finset.union_subset (h 0) (h 1)) (h 2)) (subset_refl _)

theorem ptpNode_qubits_le (T : PTPTable) (Lay : NodeLayout T.k) (n : ℕ) (φ : Angle) (ta ua : ℕ) :
    (LowGate.usedQubits (ptpNode T Lay n φ ta ua)).card ≤ 3 * T.k * Lay.width + 2 :=
  (Finset.card_le_card (ptpNode_usedQubits_subset T Lay n φ ta ua)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add (slotQubits_card_le Lay)
      (Finset.card_le_two)))

/-- Qubits touched by the CCPhase node: inside the `3k` slots. -/
theorem ptpNodeCCPhase_usedQubits_subset (T : PTPTable) (Lay : NodeLayout T.k) (n : ℕ) (φ : Angle) :
    LowGate.usedQubits (ptpNodeCCPhase T Lay n φ) ⊆ slotQubits Lay := by
  refine body_usedQubits_subset Lay _ _ (subset_refl _) (fun t i => ?_) T.ops 0
  unfold ptpLeafCCPhase
  have hc : ∀ c ∈ leafCells (Lay.slot 0 i) (Lay.slot 1 i) (Lay.slot 2 i),
      LowGate.usedQubits (cellGate (φ * coeffN T n t) c) ⊆ slotQubits Lay := by
    intro c hc q hq
    obtain ⟨h0, h1, h2⟩ := mem_triples hc
    have := usedQubits_CCPhase_subset _ _ _ _ hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl
    · exact mem_slotQubits Lay (LowerGateClass.signedTerms_fst_mem h0)
    · exact mem_slotQubits Lay (LowerGateClass.signedTerms_fst_mem h1)
    · exact mem_slotQubits Lay (LowerGateClass.signedTerms_fst_mem h2)
  have gen : ∀ cs : List Cell, (∀ c ∈ cs, LowGate.usedQubits (cellGate (φ * coeffN T n t) c) ⊆
      slotQubits Lay) → LowGate.usedQubits (LowGate.sequence (cs.map (cellGate (φ * coeffN T n t)))) ⊆
        slotQubits Lay := by
    intro cs
    induction cs with
    | nil => intro _; simp [LowGate.sequence, LowGate.usedQubits]
    | cons c cs ih =>
        intro h
        simp only [List.map_cons, LowGate.sequence, LowGate.usedQubits]
        exact Finset.union_subset (h c (by simp)) (ih fun c' h' => h c' (by simp [h']))
  exact gen _ hc

theorem ptpNodeCCPhase_qubits_le (T : PTPTable) (Lay : NodeLayout T.k) (n : ℕ) (φ : Angle) :
    (LowGate.usedQubits (ptpNodeCCPhase T Lay n φ)).card ≤ 3 * T.k * Lay.width :=
  (Finset.card_le_card (ptpNodeCCPhase_usedQubits_subset T Lay n φ)).trans (slotQubits_card_le Lay)

/-! ## Policy-level census (composition of the proved node formula) -/


def Census.total (c : Census) : ℕ := c.h + c.x + c.cnot + c.toffoli + c.rz


/-- CCPhase-leaf census at width `w` (documented alternative). -/
def leafCensusCCPhase (w : ℕ) : Census :=
  ⟨0, 0, 2 * (w * w * w), 2 * (w * w * w), 5 * (w * w * w)⟩


/-- **Policy-level PTP census** at width `n`: the node formula composed down the
ladder, leaf formula at the bottom. -/
def ptpResources (P : PTPPolicy) (n : ℕ) : Census :=
  match P.choose n with
  | none => leafCensus n
  | some T =>
      if _h : childWidth n T.ops < n then
        nodeCensus (childWidth n T.ops) (addCount T.ops) (negCount T.ops) (cpCount T.ops)
          (ptpResources P (childWidth n T.ops))
      else leafCensus n
termination_by n

/-- Policy-level PTP census with CCPhase leaves (documented alternative) at width `n`: the node formula composed down the
ladder, leaf formula at the bottom. -/
def ptpResourcesCCPhase (P : PTPPolicy) (n : ℕ) : Census :=
  match P.choose n with
  | none => leafCensusCCPhase n
  | some T =>
      if _h : childWidth n T.ops < n then
        nodeCensus (childWidth n T.ops) (addCount T.ops) (negCount T.ops) (cpCount T.ops)
          (ptpResourcesCCPhase P (childWidth n T.ops))
      else leafCensusCCPhase n
termination_by n




/-- Logical qubits with CCPhase leaves (no leaf ancilla; documented alternative). -/
def ptpQubitsCCPhase (P : PTPPolicy) (n : ℕ) : ℕ :=
  3 * n + 3 * ptpReserveNeed P n + ptpCleanAnc P n

/-- **Depth one is the proved circuit.** When the policy's node at `n` has leaf
children (the child width selects the leaf), every additive field of
`ptpResources` equals the resources of the gate-level node `ptpNode` (sandwich
leaves) at working width `C = childWidth n T.ops`. -/
theorem ptpResources_depth_one (P : PTPPolicy) (n : ℕ) (T : PTPTable) (hc : P.choose n = some T)
    (hlt : childWidth n T.ops < n) (hleaf : P.choose (childWidth n T.ops) = none)
    (Lay : NodeLayout T.k) (hw : Lay.width = childWidth n T.ops) (φ : Angle) (ta ua : ℕ) :
    let R := LowGate.resources shorGateResourceModel (ptpNode T Lay n φ ta ua)
    let c := ptpResources P n
    c.rz = R.rz ∧ c.cnot = R.cnot ∧ c.toffoli = R.toffoli ∧ c.x = R.x ∧ c.h = R.h := by
  intro R c
  have hc' : c = nodeCensus (childWidth n T.ops) (addCount T.ops) (negCount T.ops) (cpCount T.ops)
      (leafCensus (childWidth n T.ops)) := by
    simp only [c]
    rw [ptpResources, hc]
    simp only [hlt, ↓reduceDIte]
    rw [ptpResources, hleaf]
  obtain ⟨h1, h2, h3, h4, h5⟩ := ptpNode_resources T Lay n φ ta ua
  rw [hc']
  simp only [R] at *
  rw [h1, h2, h3, h4, h5, hw]
  simp [nodeCensus, leafCensus]

/-- Depth one, CCPhase leaves (documented alternative). -/
theorem ptpResourcesCCPhase_depth_one (P : PTPPolicy) (n : ℕ) (T : PTPTable)
    (hc : P.choose n = some T) (hlt : childWidth n T.ops < n)
    (hleaf : P.choose (childWidth n T.ops) = none)
    (Lay : NodeLayout T.k) (hw : Lay.width = childWidth n T.ops) (φ : Angle) :
    let R := LowGate.resources shorGateResourceModel (ptpNodeCCPhase T Lay n φ)
    let c := ptpResourcesCCPhase P n
    c.rz = R.rz ∧ c.cnot = R.cnot ∧ c.toffoli = R.toffoli ∧ c.x = R.x ∧ c.h = R.h := by
  intro R c
  have hc' : c = nodeCensus (childWidth n T.ops) (addCount T.ops) (negCount T.ops) (cpCount T.ops)
      (leafCensusCCPhase (childWidth n T.ops)) := by
    simp only [c]
    rw [ptpResourcesCCPhase, hc]
    simp only [hlt, ↓reduceDIte]
    rw [ptpResourcesCCPhase, hleaf]
  obtain ⟨h1, h2, h3, h4, h5⟩ := ptpNodeCCPhase_resources T Lay n φ
  rw [hc']
  simp only [R] at *
  rw [h1, h2, h3, h4, h5, hw]
  simp [nodeCensus, leafCensusCCPhase]

end PTP
end Shor
