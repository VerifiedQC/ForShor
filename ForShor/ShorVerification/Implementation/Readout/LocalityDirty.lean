import ForShor.ShorVerification.Implementation.Readout.Proofs.DirtyBlocks
import ForShor.ShorVerification.Implementation.Readout.LocalityReserve

/-!
# Readout: what the LOWERED circuit does on dirty reserve qubits

The locality files (`Locality*.lean`, `LowLocality*.lean`) ask which qubits a circuit can see.
This file asks a different question: what the LOWERED blocks (`LowGate` circuits, evaluated by
`LowerGateClass.evalL`) compute when reserve / workspace qubits start in an ARBITRARY basis
state instead of `0`. The proofs are in `Proofs/DirtyBasis.lean` (basis level) and
`Proofs/DirtyBlocks.lean` (low-gate level); this file restates the headline results, adds tests,
and prints their axioms. No new axiom, class or class field.

## What is TRUE (proved)

D1 holds for every `RegEncoding` basis. The low-gate statements hold for every semantics with a
`LowerGateClass` instance; those that also mention a high-level gate (`qs.eval`) assume
`GateSemanticsFacts` as well, as their signatures say.


* Growth on dirty reserve (D1). `zeroExtend` is the identity and `signExtend` XORs the sign
  into the new bits; the grown register then reads, with `w = r.width` and `sd` the new bits read
  as an `n`-bit two's-complement number:
  `r.toNat b + 2^w * sd` after `zeroExtend` (needs `n ≥ 1`), and
  `extToInt r b ± 2^w * sd` after `signExtend` (`-` iff `r` is negative). Clean reserve is
  `sd = 0`.
* Stopping nodes are exact on every state (D2). Where the policy has no table, the lowered
  (controlled) signed phase product and the lowered `PhaseProdUsing` macro equal the
  high-level gates on EVERY state, dirty sign-extension qubits included. This does NOT mean
  that dirty input is harmless there: `Gate.PhaseProdUsing` zero-extends into the reserve qubit
  and `Gate.SignedPhaseProd` reads it, so on dirty input BOTH sides compute the same wrong
  unsigned phase. D2 says only that the lowering adds no further error at a stopping node.
* The constant comparator and controlled constant subtraction (D3) restore every qubit except
  the flag (resp. `data.active`) on EVERY basis ket, dirty `u`, `scratch` and data reserve
  included. The flag is toggled iff a wrapped sum of INPUT values is `≥ 0`, and `data` receives
  `data + p` modulo `2^(data.width)`, with `p` given by a case split on the input value of `u`
  (comparator) or `u xor flag` (subtraction): `-s` wrapped if nothing is copied,
  `-(tcDecodeWidth w (s ^^^ N))` wrapped if `N` is copied (copying XORs `N` into `scratch`).
  Closed forms: `dirty_comparator_toggle_closed`, `dirty_csub_value_closed`. On clean input both reduce to the high-level
  basis maps (`cmpDirtyToggle_of_clean`, `csubDirty_of_clean`).

## What is FALSE (proved negatives)

"The lowered circuit equals the high-level circuit as long as only reserve qubits that the
high-level circuit already sees are dirty" is false at the level of single blocks:

* N1 (`dirty_unit_breaks_comparator`): the unit qubit `u = scratch.newBits 1`[0] is one of the
  qubits the high-level readout circuit names (`unit_mem_semiclassicalExactQubits`),
  and the high-level `Gate.CmpGeConst` ignores it (it commutes with `X u`). Yet with `u = 1`, a
  clean `scratch`, a clean data reserve qubit and `data < N`, the lowered comparator toggles
  the flag and the high-level gate does not.
* N2 (`lowered_qft_reads_pool`): the high-level `Gate.QFT` commutes with `X` on every qubit
  outside `r.active`, in particular on its first pool qubit; the lowered QFT (no-table policy,
  width 2) does NOT. So "the lowered program commutes with `X` on every reserve qubit" is false.
  Ket-level form (`lowered_qft_differs_on_dirty_pool`): some basis ket with a dirty pool qubit
  (`2` or `3`) is mapped to different states by the lowered and the high-level QFT.

These are block-level counterexamples. That a dirty reserve qubit changes the record
probabilities of the FULL lowered order-finding circuit is NOT proved here.

## What is NOT covered (research)

* An exact record-level semantics of the full lowered circuit on dirty input. Toom-Cook nodes
  (`signedStep`) place child operands in reserve slots; dirty slots change every child operand.
  For tables with shifts (`ShiftL` / `ShiftR`) the reversible completions are not ring maps,
  and whether the slots are even restored is open.
* Dirty negation / adder ancillas: `LowGate.Negate` and `LowGate.AddScaled` are primitives whose
  scratch is not modelled as qubits, so this cannot be stated in the present semantics.
* Exhibiting these negatives at the reference layout of the real circuit (the instances here
  are a small register and a workspace record supplied by hand; `Model.qs` instances are in
  `Model/Standard/SemiclassicalDirtyModel.lean`).
-/

namespace Shor
namespace Dirty

open Readout

/-! ## D1 -/

/-- **D1, zero extension.** For `n ≥ 1` and `r.CanGrow n`, on ANY basis state the grown register
reads `r.toNat b + 2^(r.width) * tcDecodeWidth n hi`, `hi` the content of the new bits. -/
theorem dirty_zeroExtend_value {B : Type*} [RegEncoding B] (r : ExtReg) (n : ℕ) (b : B)
    (hcap : r.CanGrow n) (hn : 0 < n) :
    extToInt (r.grow n) b =
      (r.toNat b : ℤ) + 2 ^ r.width * tcDecodeWidth n (RegEncoding.toNat (r.newBits n) b) :=
  extToInt_grow_dirty r n b hcap hn

/-- **D1, sign extension.** For `r.CanGrow n`, on ANY basis state the grown register after
`signExtendBasis` reads `extToInt r b ± 2^(r.width) * tcDecodeWidth n hi` (`-` iff `r` reads
negative), `hi` the ORIGINAL content of the new bits. -/
theorem dirty_signExtend_value {B : Type*} [RegEncoding B] (r : ExtReg) (n : ℕ) (b : B)
    (hcap : r.CanGrow n) :
    extToInt (r.grow n) (signExtendBasis r n b) =
      extToInt r b + (if extToInt r b < 0 then (-1 : ℤ) else 1) * 2 ^ r.width *
        tcDecodeWidth n (RegEncoding.toNat (r.newBits n) b) :=
  extToInt_grow_signExtendBasis_dirty r n b hcap

section Low

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]

/-! ## D2 -/

/-- **D2.** If the policy has no table at the node's width, the lowered signed phase product equals
`Gate.SignedPhaseProd` on every state (no cleanliness, no admissibility). -/
theorem dirty_stop_signed (P : ShorLoweringPolicy) (phi : Angle) (x z : ExtReg)
    (h : P.choose (phaseInputSize x z) = none) (ψ : qs.State) :
    LowerGateClass.evalL (Policy.lowerSignedPhaseProd P phi x z) ψ
      = qs.eval (Gate.SignedPhaseProd phi x z) ψ :=
  Policy.lowerSignedPhaseProd_eval_of_stop P phi x z h ψ

/-- **D2, controlled.** Same hypothesis, `Gate.CSignedPhaseProd`, every state. -/
theorem dirty_stop_csigned (P : ShorLoweringPolicy) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (h : P.choose (phaseInputSize x z) = none) (ψ : qs.State) :
    LowerGateClass.evalL (Policy.lowerCSignedPhaseProd P ctrl phi x z) ψ
      = qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ :=
  Policy.lowerCSignedPhaseProd_eval_of_stop P ctrl phi x z h ψ

/-- **D2, `PhaseProdUsing`.** If the policy has no table at the width of the grown operands, the
lowered macro equals `Gate.PhaseProdUsing` on every state, including states whose two
sign-extension reserve qubits are dirty. -/
theorem dirty_stop_phaseProdUsing (P : ShorLoweringPolicy) (phi : Angle) {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (h : P.choose (phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1)) = none) (ψ : qs.State) :
    LowerGateClass.evalL (lowerGateRec (Policy.phaseProdUsingPlan P phi ws)) ψ
      = qs.eval (Gate.PhaseProdUsing phi x z ws) ψ :=
  Policy.phaseProdUsing_eval_of_stop P phi ws h ψ

/-! ## D3 -/

omit [GateSemanticsFacts qs] in
/-- **D3, comparator.** Static workspace record only: on every basis ket the lowered comparator
restores every qubit except the flag, which it toggles iff `cmpDirtyToggle` (see
`cmpDirtyToggle_iff`). -/
theorem dirty_comparator (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : qs.Basis) :
    LowerGateClass.evalL (lowerCmpGeConst N data scratch flag h) (qs.ket b)
      = qs.ket (if cmpDirtyToggle N data scratch flag h b then flipBit flag b else b) :=
  evalL_lowerCmpGeConst_ket_dirty N data scratch flag h b

omit [GateSemanticsFacts qs] in
/-- **D3, controlled subtraction.** Static workspace record only: on every basis ket the lowered
controlled subtraction restores every qubit except `data.active`, which receives
`csubDirtyValue`. -/
theorem dirty_csub (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : qs.Basis) :
    LowerGateClass.evalL (lowerCSubConst N data scratch flag h) (qs.ket b)
      = qs.ket (RegEncoding.writeNat data.active
          (csubDirtyValue N data scratch flag h.scratch_can_grow b) b) :=
  evalL_lowerCSubConst_ket_dirty N data scratch flag h b

omit [GateSemanticsFacts qs] [LowerGateClass qs] in
/-- **D3, comparator toggle in closed form.** See `cmpDirtyToggle_iff_closed`: toggle iff
`0 ≤ tcWrapInt w (p + d + 2^(data.width) * tcDecodeWidth 1 hi)`, all input values. -/
theorem dirty_comparator_toggle_closed (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : qs.Basis) :
    cmpDirtyToggle N data scratch flag h b = true ↔
      0 ≤ tcWrapInt scratch.width
        ((if RegEncoding.bit (constArithmeticUnitQubit scratch h.scratch_can_grow) b then
            tcWrapInt scratch.width (-extToInt scratch b)
          else tcWrapInt scratch.width (-(tcDecodeWidth scratch.width
            (RegEncoding.toNat scratch.active b ^^^ N))))
          + ((RegEncoding.toNat data.active b : ℤ) + 2 ^ data.width *
              tcDecodeWidth 1 (RegEncoding.toNat (data.newBits 1) b))) :=
  cmpDirtyToggle_iff_closed N data scratch flag h b

omit [GateSemanticsFacts qs] [LowerGateClass qs] in
/-- **D3, value written by the controlled subtraction, closed form.** See
`csubDirtyValue_eq_closed`. -/
theorem dirty_csub_value_closed (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : qs.Basis) :
    csubDirtyValue N data scratch flag h.scratch_can_grow b
      = tcModWidth data.width (extToInt data b +
          if xor (RegEncoding.bit (constArithmeticUnitQubit scratch h.scratch_can_grow) b)
              (RegEncoding.bit flag b) then
            tcWrapInt scratch.width (-(tcDecodeWidth scratch.width
              (RegEncoding.toNat scratch.active b ^^^ N)))
          else tcWrapInt scratch.width (-extToInt scratch b)) :=
  csubDirtyValue_eq_closed N data scratch flag h b

/-! ## N1, N2 -/

omit [GateSemanticsFacts qs] [LowerGateClass qs] in
/-- The unit qubit `u` of `scratch` is one of the qubits the high-level readout circuit
names: it lies in `semiclassicalExactQubits c y work scratch flag` (for any `c y work flag`). -/
theorem unit_mem_semiclassicalExactQubits (c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hcap : scratch.CanGrow 1) :
    constArithmeticUnitQubit scratch hcap ∈ semiclassicalExactQubits c y work scratch flag := by
  simp only [semiclassicalExactQubits, Set.mem_ofPred_eq]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.get_mem _ _)))))))

/-- **N1.** Under the static workspace record, with a basis ket `b` where the unit qubit
`u = constArithmeticUnitQubit scratch _` reads `1`, `scratch` reads `0`, the data reserve qubit
is clean and `data < N`: (a) the HIGH-LEVEL `Gate.CmpGeConst` commutes with `X u` (it does not
read `u`), and (b) the LOWERED comparator and `Gate.CmpGeConst` give different kets on `b`. -/
theorem dirty_unit_breaks_comparator (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : qs.Basis)
    (hu : RegEncoding.bit (constArithmeticUnitQubit scratch h.scratch_can_grow) b = true)
    (hs : extToInt scratch b = 0) (hd : data.FreshFor 1 b)
    (hlt : RegEncoding.toNat data.active b < N) :
    CommX qs (Gate.CmpGeConst N data scratch flag)
        (constArithmeticUnitQubit scratch h.scratch_can_grow) ∧
      LowerGateClass.evalL (lowerCmpGeConst N data scratch flag h) (qs.ket b)
        ≠ qs.eval (Gate.CmpGeConst N data scratch flag) (qs.ket b) :=
  ⟨commX_of_basis _ (ModularArithmeticSemantics.eval_CmpGeConst_ket N data scratch flag)
      (fun b' => cmpGeConstBasis_flipBit (ws_unit_not_mem_data h)
        (fun e => ws_flag_ne_unit h e.symm) b'),
    lowerCmpGeConst_ne_of_unit_dirty N data scratch flag h b hu hs hd hlt⟩

/-- **N2.** At any policy with no table, for the width-2 register `n2Reg` (active `[0, 1]`,
reserve `[2, 3]`) and its first pool qubit `2`: the HIGH-LEVEL `Gate.QFT n2Reg` commutes with
`X 2`, the LOWERED QFT does not. -/
theorem lowered_qft_reads_pool (P : ShorLoweringPolicy) (hP : P.bands = [])
    (h : Policy.QFTReserveOK P n2Reg) :
    (Policy.qftXWork P n2Reg).qubits = [2] ∧ CommX qs (Gate.QFT n2Reg) 2 ∧
      ¬ CommXL qs (Policy.lowerQFT P n2Reg h) 2 :=
  ⟨qftXWork_n2Reg P hP, commX_QFT (by decide), lowerQFT_not_commXL_pool P hP h⟩

/-- **N2, ket level.** At any policy with no table: some basis ket with qubit `2` or qubit `3`
(the two pool qubits of `n2Reg`) set is sent to different states by the lowered QFT and by
`Gate.QFT n2Reg`. Which pool qubit must be dirty is not claimed. -/
theorem lowered_qft_differs_on_dirty_pool (P : ShorLoweringPolicy) (hP : P.bands = [])
    (h : Policy.QFTReserveOK P n2Reg) :
    ∃ b : qs.Basis, (RegEncoding.bit 2 b = true ∨ RegEncoding.bit 3 b = true) ∧
      LowerGateClass.evalL (Policy.lowerQFT P n2Reg h) (qs.ket b)
        ≠ qs.eval (Gate.QFT n2Reg) (qs.ket b) :=
  lowerQFT_ne_QFT_dirty_pool P hP h

end Low

/-! ## Tests -/

/-- The policy with no bands (every node is a stopping node). -/
def noTablePolicy : ShorLoweringPolicy where
  bands := []
  sorted := List.IsChain.nil

/-- At the no-table policy every lowered signed phase product is the naive leaf. -/
example (phi : Angle) (x z : ExtReg) :
    Policy.lowerSignedPhaseProd noTablePolicy phi x z = LowGate.Naive_SignedPhaseProd phi x z :=
  Policy.lowerSignedPhaseProd_eq_naive_of_stop _ _ _ _ (choose_none_of_bands_nil _ rfl _)

/-- N2's reserve hypothesis holds at the no-table policy. -/
example : Policy.QFTReserveOK noTablePolicy n2Reg := n2Reg_reserveOK _ rfl

/-- N2 at the no-table policy, every `LowerGateClass` semantics. -/
example {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs] :
    ¬ CommXL qs (Policy.lowerQFT noTablePolicy n2Reg (n2Reg_reserveOK _ rfl)) 2 :=
  lowerQFT_not_commXL_pool _ rfl _

/-- D1 arithmetic core: `(u, h) = (1, 3)` on `2 + 2` bits reads `1 + 4 * (-1) = -3`. -/
example : tcDecodeWidth (2 + 2) (1 + 2 ^ 2 * 3) = (1 : ℤ) + 2 ^ 2 * tcDecodeWidth 2 3 :=
  tcDecodeWidth_append 2 2 1 3 (by decide) (by decide) (by decide)

example : tcDecodeWidth 2 3 = -1 := by decide

end Dirty
end Shor

#print axioms Shor.Dirty.dirty_zeroExtend_value
#print axioms Shor.Dirty.dirty_signExtend_value
#print axioms Shor.Dirty.extToInt_grow_zero
#print axioms Shor.Dirty.extToInt_grow_signExtendBasis_clean
#print axioms Shor.Dirty.dirty_stop_signed
#print axioms Shor.Dirty.dirty_stop_csigned
#print axioms Shor.Dirty.dirty_stop_phaseProdUsing
#print axioms Shor.Dirty.dirty_comparator
#print axioms Shor.Dirty.dirty_csub
#print axioms Shor.Dirty.cmpDirtyToggle_iff
#print axioms Shor.Dirty.extToInt_cmpPrepBasis_of_unit_set
#print axioms Shor.Dirty.cmpDirtyToggle_of_clean
#print axioms Shor.Dirty.csubDirty_of_clean
#print axioms Shor.Dirty.dirty_unit_breaks_comparator
#print axioms Shor.Dirty.lowered_qft_reads_pool
#print axioms Shor.Dirty.n2Reg_reserveOK
#print axioms Shor.Dirty.dirty_comparator_toggle_closed
#print axioms Shor.Dirty.dirty_csub_value_closed
#print axioms Shor.Dirty.extToInt_cmpPrepBasis
#print axioms Shor.Dirty.extToInt_csubPrepBasis
#print axioms Shor.Dirty.toNat_copyBitsBasis_xor
#print axioms Shor.Dirty.lowered_qft_differs_on_dirty_pool
#print axioms Shor.Dirty.unit_mem_semiclassicalExactQubits
