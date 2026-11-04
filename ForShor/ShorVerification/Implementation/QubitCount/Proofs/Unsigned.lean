import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PhaseProduct

/-!
# Qubit count: the unsigned phase-product wrapper

`Gate.PhaseProdUsing` extends each operand by one reserve qubit, runs a signed
phase product on the grown operands, and deallocates the two qubits. Every
lowering of it has that shape. This file computes the walk of the shape for
any middle circuit, including the case where the qubit the `x` extension
activates is already live, which is what happens to the scratch register's
first reserve qubit in Step 4 of a modular multiplication.
-/

namespace Shor
namespace QubitCount

open Gate

/-- The wrapper shape: grow `X` and `Z` by one qubit, run `S`, release them. -/
def wrap (X Z : ExtReg) (S : LowGate) : LowGate :=
  LowGate.zeroExtend X 1 ;; LowGate.zeroExtend Z 1 ;; S ;;
    LowGate.zeroDealloc Z 1 ;; LowGate.zeroDealloc X 1

/-- Every lowering plan of an unsigned phase product is the two extensions, a
plan of the signed phase product on the grown operands, and the two
deallocations; the inner plan is valid when the whole one is. -/
lemma ppUsing_plan_shape {P : ShorLoweringPolicy} {n : ℕ} {phi : Angle} {x z : Reg}
    {ws : Gate.PhaseProdWorkspace x z} (p : PhaseLoweringPlan P n (Gate.PhaseProdUsing phi x z ws))
    (hv : p.Valid) :
    ∃ c : PhaseLoweringPlan P n (Gate.SignedPhaseProd phi (ws.xExt.grow 1) (ws.zExt.grow 1)),
      c.Valid ∧ lowerGateRec p = wrap ws.xExt ws.zExt (lowerGateRec c) := by
  rcases p with _ | ⟨pA, p2⟩
  rcases pA with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, _, _⟩
  rcases p2 with _ | ⟨pB, p3⟩
  rcases pB with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, _, _⟩
  rcases p3 with _ | ⟨c, p4⟩
  rcases p4 with _ | ⟨pD, pE⟩
  rcases pD with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, _, _⟩
  rcases pE with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, _, _⟩
  exact ⟨c, hv.2.2.1, rfl⟩

/-- The same for the controlled wrapper. -/
lemma cppUsing_plan_shape {P : ShorLoweringPolicy} {n : ℕ} {ctrl : ℕ} {phi : Angle} {x z : Reg}
    {ws : Gate.PhaseProdWorkspace x z}
    (p : PhaseLoweringPlan P n (Gate.CPhaseProdUsing ctrl phi x z ws)) (hv : p.Valid) :
    ∃ c : PhaseLoweringPlan P n
        (Gate.CSignedPhaseProd ctrl phi (ws.xExt.grow 1) (ws.zExt.grow 1)),
      c.Valid ∧ lowerGateRec p = wrap ws.xExt ws.zExt (lowerGateRec c) := by
  rcases p with _ | ⟨pA, p2⟩
  rcases pA with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, _, _⟩
  rcases p2 with _ | ⟨pB, p3⟩
  rcases pB with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, _, _⟩
  rcases p3 with _ | ⟨c, p4⟩
  rcases p4 with _ | ⟨pD, pE⟩
  rcases pD with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, _, _⟩
  rcases pE with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, _, _⟩
  exact ⟨c, hv.2.2.1, rfl⟩

/--
The wrapper ends with the `X` qubit released and peaks at two above that, plus
`S`'s own cost. If the `X` qubit was live on entry it is released at the end,
and its activation costs nothing; the wrapper is then not well formed. If it
was not live, the wrapper is well formed whenever `S` is.
-/
theorem wrap_walk {anc : LowGate → ℕ} {X Z : ExtReg} {S : LowGate} {L : Finset ℕ} {E : ℕ}
    (hX : X.CanGrow 1) (hZ : Z.CanGrow 1)
    (hxz : _root_.Disjoint (allocBits X 1) (allocBits Z 1))
    (hzL : _root_.Disjoint (allocBits Z 1) L)
    (hSa : after S true (L ∪ allocBits X 1 ∪ allocBits Z 1) = L ∪ allocBits X 1 ∪ allocBits Z 1)
    (hSp : peak anc S true (L ∪ allocBits X 1 ∪ allocBits Z 1)
      = (L ∪ allocBits X 1 ∪ allocBits Z 1).card + E) :
    after (wrap X Z S) true L = L \ allocBits X 1 ∧
    peak anc (wrap X Z S) true L = (L \ allocBits X 1).card + 2 + E ∧
    (_root_.Disjoint (allocBits X 1) L → WellFormed S true (L ∪ allocBits X 1 ∪ allocBits Z 1) →
      WellFormed (wrap X Z S) true L) := by
  set bx := allocBits X 1 with hbx
  set bz := allocBits Z 1 with hbz
  have hcx : bx.card = 1 := card_allocBits X hX
  have hcz : bz.card = 1 := card_allocBits Z hZ
  have hL1 : L ∪ bx = (L \ bx) ∪ bx := (Finset.sdiff_union_self_eq_union).symm
  have hc1 : (L ∪ bx).card = (L \ bx).card + 1 := by
    rw [hL1, Finset.card_union_of_disjoint Finset.sdiff_disjoint, hcx]
  have hzL1 : _root_.Disjoint bz (L ∪ bx) :=
    Finset.disjoint_union_right.mpr ⟨hzL, hxz.symm⟩
  have hc2 : (L ∪ bx ∪ bz).card = (L \ bx).card + 2 := by
    rw [Finset.card_union_of_disjoint hzL1.symm, hc1, hcz]
  have hd2 : (L ∪ bx ∪ bz) \ bz = L ∪ bx := Finset.union_sdiff_cancel_right hzL1.symm
  have hd1 : (L ∪ bx) \ bx = L \ bx := Finset.union_sdiff_right L bx
  simp only [wrap, after, peak, WellFormed, move_true, move_false, Bool.not_true,
    moveOK_true, moveOK_false]
  rw [hSa, hd2, hd1, hSp]
  refine ⟨rfl, ?_, fun h1 h2 => ⟨h1, hzL1, h2, Finset.subset_union_right, ?_⟩⟩
  · have h0 : L.card ≤ (L ∪ bx).card := Finset.card_le_card Finset.subset_union_left
    rw [← hbx, hc2]
    apply le_antisymm <;> simp only [max_le_iff, le_max_iff] <;> omega
  · rw [← hbx]; exact Finset.subset_union_right

end QubitCount
end Shor
