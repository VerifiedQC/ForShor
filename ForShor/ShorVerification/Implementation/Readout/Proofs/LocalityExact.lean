import ForShor.ShorVerification.Implementation.Readout.Proofs.LocalityDom

/-!
# Readout: the EXACT qubit support of a program, and locality outside it

`Gate.qubitSupport` (`Readout/Support.lean`) is a syntactic over-approximation: a register
operand of type `ExtReg` counts with ALL its owned qubits, active and reserve. Here
`Gate.exactSupport` / `MGate.exactSupport` is the set of qubits read or written by the
high-level ket laws of a program (an upper bound on what it acts on, see below),
read off the ket laws of `Framework/Semantics/GateSemantics.lean` constructor by constructor
(bits READ or WRITTEN by the basis map / ket law):

| constructor | ket law reads / writes | `exactSupport` |
|---|---|---|
| `H q`, `X q` | bit `q` | `{q}` |
| `CNOT a t`, `Toffoli a a' t` | controls (read), target (read+write) | `{a, t}`, `{a, a', t}` |
| `QFT r` | `r.active` (`ExtReg.toNat r`, `writeNat r.active`) | `r.active` |
| `RadixReverse r m` | `r` (a plain `Reg`) | `r` |
| `SignedPhaseProd _ x z` | `extToInt x`, `extToInt z` (active parts), diagonal | `x.active ∪ z.active` |
| `CSignedPhaseProd ctrl _ x z` | `ctrl`, `x.active`, `z.active`, diagonal | `{ctrl} ∪ x.active ∪ z.active` |
| `CmpGeConst N d s f` | `d.active` (read), `f` (read+write); `s` is NOT used | `d.active ∪ {f}` |
| `CSubConst N d s f` | `f` (read), `d.active` (read+write); `s` is NOT used | `d.active ∪ {f}` |
| `ShiftL r _`, `ShiftR r _`, `Negate r` | `r.active` | `r.active` |
| `AddScaled d s _ _` | `s.active` (read), `d.active` (read+write) | `d.active ∪ s.active` |
| `zeroExtend r n`, `zeroDealloc r n` | identity (`eval_zeroExtend`, `eval_zeroDealloc`) | `∅` |
| `signExtend r n`, `signDealloc r n` | `r.active` (sign, read), `r.newBits n` = first `n` reserve qubits (read+write) | `r.active ∪ r.newBits n` |
| `idealCtrlModMul c N data ctrl` | `data`, `ctrl` (law only on `data < N`) | `data ∪ {ctrl}` |

`MGate.exactSupport` adds the qubit of every `measureReset` and `ffPhase`.

It is the set of qubits the ket law's FORMULA reads or writes; in degenerate cases the gate may
act on less (e.g. `CNOT a a` is the identity but has exact support `{a}`), so it is an upper bound
on the qubits acted on; tightness is not claimed or proved. The scratch operand of
`CmpGeConst`/`CSubConst` is not read by their high-level ket laws (the lowering may use it); the
`ExtReg` reserves beyond `newBits n` are read by no high-level law.

"Growing into the reserve" is therefore visible exactly where a later gate acts on the GROWN
register `r.grow n` (whose ACTIVE part is `r.active ++ r.newBits n`), or where a sign
extension/deallocation writes `r.newBits n`. `zeroExtend`/`zeroDealloc` themselves are the
identity in the high-level semantics: the requirement that the new bits START at `0` is a
correctness precondition of the arithmetic (and of the lowering), not something the gate does.

All ket laws used are TOTAL (no side condition on the ket) except the ideal multiplier's; so
the A1 theorems carry exactly the hypotheses `P.NoIdeal` and `q ∉ P.exactSupport` (no domain
needed). The ideal multiplier on its domain is in `Proofs/LocalityIdeal.lean`.

* `Gate.exactSupport_subset`, `MGate.exactSupport_subset`: `exactSupport ⊆ qubitSupport`, so
  every theorem below strengthens its `qubitSupport` counterpart.
* `gate_commX_exact`, `gate_commP_exact`: a gate with no ideal node commutes with `X q` and
  with `measProj (qubitReg q) o` on EVERY state, for `q ∉ U.exactSupport`.
* `MGate.eval_commX_exact`, `MGate.eval_commProj_exact`, `MGate.spectatorOn_exact`: the same
  for `MGate` programs, branch by branch.
* Corollaries, every start state / ket (no domain): `MGate.recordProb_init_X_exact`,
  `MGate.recordProb_flipBit_exact`, `MGate.recordProb_flipBits_exact`,
  `MGate.recordProb_of_agree_exact`, `MGate.recordProb_decomp_exact`,
  `MGate.recordProb_superpose_exact`.

NOT covered: programs with an `idealCtrlModMul` node (A2); qubits in `exactSupport` (for them
locality can genuinely fail, `LocalityTests.measureReset_flip_named`). No new axiom or field.
-/

namespace Shor

open Readout MeasureClass

/-- The qubits a high-level gate's ket law reads or writes (an upper bound on what it acts on);
see the
module docstring for the table. -/
def Gate.exactSupport : Gate → Set ℕ
  | .id => ∅
  | .seq U V => U.exactSupport ∪ V.exactSupport
  | .adj U => U.exactSupport
  | .H q => {q}
  | .X q => {q}
  | .CNOT a b => {a, b}
  | .Toffoli a b t => {a, b, t}
  | .QFT r => {q | q ∈ r.active.qubits}
  | .RadixReverse r _ => {q | q ∈ r.qubits}
  | .SignedPhaseProd _ x z => {q | q ∈ x.active.qubits ∨ q ∈ z.active.qubits}
  | .CSignedPhaseProd ctrl _ x z => {q | q = ctrl ∨ q ∈ x.active.qubits ∨ q ∈ z.active.qubits}
  | .CmpGeConst _ d _ f => {q | q ∈ d.active.qubits ∨ q = f}
  | .CSubConst _ d _ f => {q | q ∈ d.active.qubits ∨ q = f}
  | .ShiftL r _ => {q | q ∈ r.active.qubits}
  | .ShiftR r _ => {q | q ∈ r.active.qubits}
  | .Negate r => {q | q ∈ r.active.qubits}
  | .AddScaled d s _ _ => {q | q ∈ d.active.qubits ∨ q ∈ s.active.qubits}
  | .zeroExtend _ _ => ∅
  | .signExtend r n => {q | q ∈ r.active.qubits ∨ q ∈ (r.newBits n).qubits}
  | .zeroDealloc _ _ => ∅
  | .signDealloc r n => {q | q ∈ r.active.qubits ∨ q ∈ (r.newBits n).qubits}
  | .idealCtrlModMul _ _ data ctrl => {q | q ∈ data.qubits ∨ q = ctrl}

/-- The qubits a measurement program's laws read or write: those of its gates (`Gate.exactSupport`),
and the qubit of every `measureReset` and `ffPhase`. -/
def MGate.exactSupport : MGate → Set ℕ
  | .unitary g => g.exactSupport
  | .seq a b => a.exactSupport ∪ b.exactSupport
  | .measureReset q => {q}
  | .ffPhase q _ => {q}

namespace Readout

theorem mem_owned_of_active {e : ExtReg} {q : ℕ} (h : q ∈ e.active.qubits) :
    q ∈ e.ownedQubits := List.mem_append_left _ h

theorem mem_owned_of_newBits {e : ExtReg} {n q : ℕ} (h : q ∈ (e.newBits n).qubits) :
    q ∈ e.ownedQubits := List.mem_append_right _ (List.mem_of_mem_take h)

/-- **The exact support is inside the syntactic one.** -/
theorem Gate.exactSupport_subset (U : Gate) : U.exactSupport ⊆ U.qubitSupport := by
  induction U with
  | seq U V ihU ihV => exact Set.union_subset_union ihU ihV
  | adj U ih => exact ih
  | QFT r => exact fun q h => mem_owned_of_active h
  | SignedPhaseProd _ x z =>
    rintro q (h | h)
    · exact Or.inl (mem_owned_of_active h)
    · exact Or.inr (mem_owned_of_active h)
  | CSignedPhaseProd ctrl _ x z =>
    rintro q (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (mem_owned_of_active h))
    · exact Or.inr (Or.inr (mem_owned_of_active h))
  | CmpGeConst _ d s f =>
    rintro q (h | h)
    · exact Or.inl (mem_owned_of_active h)
    · exact Or.inr (Or.inr h)
  | CSubConst _ d s f =>
    rintro q (h | h)
    · exact Or.inl (mem_owned_of_active h)
    · exact Or.inr (Or.inr h)
  | ShiftL r _ => exact fun q h => mem_owned_of_active h
  | ShiftR r _ => exact fun q h => mem_owned_of_active h
  | Negate r => exact fun q h => mem_owned_of_active h
  | AddScaled d s _ _ =>
    rintro q (h | h)
    · exact Or.inl (mem_owned_of_active h)
    · exact Or.inr (mem_owned_of_active h)
  | zeroExtend r n => exact Set.empty_subset _
  | zeroDealloc r n => exact Set.empty_subset _
  | signExtend r n =>
    rintro q (h | h)
    · exact mem_owned_of_active h
    · exact mem_owned_of_newBits h
  | signDealloc r n =>
    rintro q (h | h)
    · exact mem_owned_of_active h
    · exact mem_owned_of_newBits h
  | _ => exact le_rfl

/-- **The exact support is inside the syntactic one** (programs). -/
theorem MGate.exactSupport_subset (P : MGate) : P.exactSupport ⊆ P.qubitSupport := by
  induction P with
  | unitary g => exact Gate.exactSupport_subset g
  | seq a b iha ihb => exact Set.union_subset_union iha ihb
  | measureReset q => exact le_rfl
  | ffPhase q _ => exact le_rfl

/-! ## Sign extension: only the active part and the first `n` reserve qubits -/

section Basis
variable {B : Type*} [RegEncoding B]

theorem signExtendBasis_flipBit_exact {r : ExtReg} {n q : ℕ} (ha : q ∉ r.active.qubits)
    (hn : q ∉ (r.newBits n).qubits) (b : B) :
    signExtendBasis r n (flipBit q b) = flipBit q (signExtendBasis r n b) := by
  unfold signExtendBasis signExtendNewValue
  rw [extToInt_flipBit ha, toNat_flipBit hn, writeNat_flipBit hn]

theorem bit_signExtendBasis_of_not_mem_exact {r : ExtReg} {n q : ℕ}
    (hn : q ∉ (r.newBits n).qubits) (b : B) :
    RegEncoding.bit q (signExtendBasis r n b) = RegEncoding.bit q b :=
  RegEncoding.bit_writeNat_out _ _ _ _ hn

end Basis

section Gates
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]

/-- **Per-primitive locality, exact support, all states.** A gate with no `idealCtrlModMul`
node commutes with `X q` for every qubit `q` outside its EXACT support. -/
theorem gate_commX_exact (U : Gate) (hU : U.NoIdeal) {q : ℕ} (hq : q ∉ U.exactSupport) :
    CommX qs U q := by
  induction U with
  | id => exact commX_id q
  | seq U V ihU ihV =>
    simp only [Gate.exactSupport, Set.mem_union, not_or] at hq
    exact commX_seq (ihU hU.1 hq.1) (ihV hU.2 hq.2)
  | adj U ih => exact commX_adj (ih hU hq)
  | H p => exact commX_H (by simpa [Gate.exactSupport] using hq)
  | X p => exact commX_X
  | CNOT a t =>
    simp only [Gate.exactSupport, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
    exact commX_of_basis _ (ClassicalReversibleSemantics.eval_CNOT_ket a t)
      (cnotBasis_flipBit hq.1 hq.2)
  | Toffoli a a' t =>
    simp only [Gate.exactSupport, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
    exact commX_of_basis _ (ClassicalReversibleSemantics.eval_Toffoli_ket a a' t)
      (toffoliBasis_flipBit hq.1 hq.2.1 hq.2.2)
  | QFT r => exact commX_QFT (by simpa [Gate.exactSupport] using hq)
  | RadixReverse r m =>
    exact commX_of_basis _ (RadixReverseSemantics.eval_RadixReverse_ket_total r m)
      (radixReverseBasis_flipBit (by simpa [Gate.exactSupport] using hq))
  | SignedPhaseProd phi x z =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_of_diag _ (PhaseSemantics.eval_SignedPhaseProd_ket phi x z) fun b => by
      rw [extToInt_flipBit hq.1, extToInt_flipBit hq.2]
  | CSignedPhaseProd ctrl phi x z =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_CSignedPhaseProd hq.1 hq.2.1 hq.2.2
  | CmpGeConst N d s f =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_of_basis _ (ModularArithmeticSemantics.eval_CmpGeConst_ket N d s f)
      (cmpGeConstBasis_flipBit hq.1 hq.2)
  | CSubConst N d s f =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_of_basis _ (ModularArithmeticSemantics.eval_CSubConst_ket N d s f)
      (csubConstBasis_flipBit hq.1 hq.2)
  | ShiftL r n =>
    exact commX_of_basis _ (ArithmeticSemantics.eval_ShiftL_ket_total r n)
      (shiftLBasis_flipBit (by simpa [Gate.exactSupport] using hq))
  | ShiftR r n =>
    exact commX_of_basis _ (ArithmeticSemantics.eval_ShiftR_ket_total r n)
      (shiftRBasis_flipBit (by simpa [Gate.exactSupport] using hq))
  | Negate r =>
    exact commX_of_basis _ (ArithmeticSemantics.eval_Negate_ket_total r)
      (negateBasis_flipBit (by simpa [Gate.exactSupport] using hq))
  | AddScaled d s neg sh =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_of_basis _ (ArithmeticSemantics.eval_AddScaled_ket_total d s neg sh)
      (addScaledBasis_flipBit hq.1 hq.2)
  | zeroExtend r n =>
    intro ψ
    rw [ExtensionSemantics.eval_zeroExtend, ExtensionSemantics.eval_zeroExtend]
  | signExtend r n =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_of_basis _ (ExtensionSemantics.eval_signExtend_ket_total r n)
      (signExtendBasis_flipBit_exact hq.1 hq.2)
  | zeroDealloc r n =>
    intro ψ
    rw [ExtensionSemantics.eval_zeroDealloc, ExtensionSemantics.eval_zeroDealloc]
  | signDealloc r n =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_of_basis _ (ExtensionSemantics.eval_signDealloc_ket_total r n)
      (signExtendBasis_flipBit_exact hq.1 hq.2)
  | idealCtrlModMul _ _ _ _ => exact hU.elim

variable [MeasureClass qs]

/-- **Per-primitive spectator law, exact support, all states.** A gate with no
`idealCtrlModMul` node commutes with `measProj (qubitReg q) o` for every `q` outside its exact
support. -/
theorem gate_commP_exact (U : Gate) (hU : U.NoIdeal) {q : ℕ} (hq : q ∉ U.exactSupport) (o : ℕ) :
    CommP qs U q o := by
  induction U with
  | id => exact commP_id q o
  | seq U V ihU ihV =>
    simp only [Gate.exactSupport, Set.mem_union, not_or] at hq
    exact commP_seq (ihU hU.1 hq.1) (ihV hU.2 hq.2)
  | adj U ih => exact commP_adj (ih hU hq)
  | H p => exact commP_H (by simpa [Gate.exactSupport] using hq)
  | X p =>
    exact commP_of_basis (flipBit p) (fun b => eval_X_ket_flipBit p b)
      (bit_flipBit_ne (by simpa [Gate.exactSupport] using hq))
  | CNOT a t =>
    simp only [Gate.exactSupport, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
    exact commP_of_basis _ (ClassicalReversibleSemantics.eval_CNOT_ket a t)
      (bit_cnotBasis_of_ne hq.2)
  | Toffoli a a' t =>
    simp only [Gate.exactSupport, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
    exact commP_of_basis _ (ClassicalReversibleSemantics.eval_Toffoli_ket a a' t)
      (bit_toffoliBasis_of_ne hq.2.2)
  | QFT r => exact commP_QFT (by simpa [Gate.exactSupport] using hq)
  | RadixReverse r m =>
    exact commP_of_basis _ (RadixReverseSemantics.eval_RadixReverse_ket_total r m)
      (bit_radixReverseBasis_of_not_mem (by simpa [Gate.exactSupport] using hq))
  | SignedPhaseProd phi x z =>
    exact commP_of_diag _ (PhaseSemantics.eval_SignedPhaseProd_ket phi x z)
  | CSignedPhaseProd ctrl phi x z =>
    refine commP_of_diag (fun b => if RegEncoding.bit ctrl b then
      Complex.exp (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
        (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ)))) else 1) fun b => ?_
    rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
    split_ifs <;> simp
  | CmpGeConst N d s f =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commP_of_basis _ (ModularArithmeticSemantics.eval_CmpGeConst_ket N d s f)
      (bit_cmpGeConstBasis_of_ne hq.2)
  | CSubConst N d s f =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commP_of_basis _ (ModularArithmeticSemantics.eval_CSubConst_ket N d s f)
      (bit_csubConstBasis_of_not_mem hq.1)
  | ShiftL r n =>
    exact commP_of_basis _ (ArithmeticSemantics.eval_ShiftL_ket_total r n)
      (bit_shiftLBasis_of_not_mem (by simpa [Gate.exactSupport] using hq))
  | ShiftR r n =>
    exact commP_of_basis _ (ArithmeticSemantics.eval_ShiftR_ket_total r n)
      (bit_shiftRBasis_of_not_mem (by simpa [Gate.exactSupport] using hq))
  | Negate r =>
    exact commP_of_basis _ (ArithmeticSemantics.eval_Negate_ket_total r)
      (bit_negateBasis_of_not_mem (by simpa [Gate.exactSupport] using hq))
  | AddScaled d s neg sh =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commP_of_basis _ (ArithmeticSemantics.eval_AddScaled_ket_total d s neg sh)
      (bit_addScaledBasis_of_not_mem hq.1)
  | zeroExtend r n =>
    intro ψ
    rw [ExtensionSemantics.eval_zeroExtend, ExtensionSemantics.eval_zeroExtend]
  | signExtend r n =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commP_of_basis _ (ExtensionSemantics.eval_signExtend_ket_total r n)
      (bit_signExtendBasis_of_not_mem_exact hq.2)
  | zeroDealloc r n =>
    intro ψ
    rw [ExtensionSemantics.eval_zeroDealloc, ExtensionSemantics.eval_zeroDealloc]
  | signDealloc r n =>
    simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commP_of_basis _ (ExtensionSemantics.eval_signDealloc_ket_total r n)
      (bit_signExtendBasis_of_not_mem_exact hq.2)
  | idealCtrlModMul _ _ _ _ => exact hU.elim

end Gates

/-! ## Measurement programs -/

section MGates
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- **Locality of `MGate` programs outside the exact support, branch by branch.** -/
theorem MGate.eval_commX_exact (P : MGate) (hP : P.NoIdeal) {q : ℕ} (hq : q ∉ P.exactSupport)
    (ψ : MState qs) :
    P.eval (fun r => qs.eval (Gate.X q) (ψ r)) = fun r => qs.eval (Gate.X q) (P.eval ψ r) := by
  induction P generalizing ψ with
  | unitary g =>
    funext r
    exact gate_commX_exact g hP hq (ψ r)
  | seq a b iha ihb =>
    simp only [MGate.exactSupport, Set.mem_union, not_or] at hq
    simp only [MGate.eval_seq]
    rw [iha hP.1 hq.1, ihb hP.2 hq.2]
  | measureReset p =>
    have hp : q ≠ p := by simpa [MGate.exactSupport] using hq
    funext r
    simp only [MGate.eval]
    split
    · rw [MGate.gate_eval_zero_state]
    · exact measureResetBranch_commX hp _ _
  | ffPhase p j =>
    have hp : q ≠ p := by simpa [MGate.exactSupport] using hq
    funext r
    exact phase_commX hp _ _

/-- **Spectator law of `MGate` programs outside the exact support, branch by branch.** -/
theorem MGate.eval_commProj_exact (P : MGate) (hP : P.NoIdeal) {q : ℕ}
    (hq : q ∉ P.exactSupport) (o : ℕ) (ψ : MState qs) :
    P.eval (fun r => measProj (qubitReg q) o (ψ r))
      = fun r => measProj (qubitReg q) o (P.eval ψ r) := by
  induction P generalizing ψ with
  | unitary g =>
    funext r
    exact gate_commP_exact g hP hq o (ψ r)
  | seq a b iha ihb =>
    simp only [MGate.exactSupport, Set.mem_union, not_or] at hq
    simp only [MGate.eval_seq]
    rw [iha hP.1 hq.1, ihb hP.2 hq.2]
  | measureReset p =>
    have hp : q ≠ p := by simpa [MGate.exactSupport] using hq
    funext r
    simp only [MGate.eval]
    split
    · simp
    · exact measureResetBranch_commProj hp o _ _
  | ffPhase p j =>
    funext r
    exact phase_commProj p q o _ _

/-- A qubit outside the exact support of a program with no ideal node is a spectator on every
state. -/
theorem MGate.spectatorOn_exact (P : MGate) (hP : P.NoIdeal) {q : ℕ} (hq : q ∉ P.exactSupport) :
    P.SpectatorOn q (⊤ : Submodule ℂ qs.State) :=
  ⟨fun ψ _ => MGate.eval_commX_exact P hP hq ψ, fun o ψ _ => MGate.eval_commProj_exact P hP hq o ψ⟩

/-! ### Corollaries (every start state, no domain) -/

/-- Flipping `q ∉ P.exactSupport` in ANY start state changes no record probability. -/
theorem MGate.recordProb_init_X_exact (P : MGate) (hP : P.NoIdeal) {q : ℕ}
    (hq : q ∉ P.exactSupport) (ψ₀ : qs.State) (r : Record) :
    recordProb (P.eval (MState.init (qs.eval (Gate.X q) ψ₀))) r
      = recordProb (P.eval (MState.init ψ₀)) r :=
  (MGate.spectatorOn_exact P hP hq).recordProb_init_X Submodule.mem_top r

/-- Ket form. -/
theorem MGate.recordProb_flipBit_exact (P : MGate) (hP : P.NoIdeal) {q : ℕ}
    (hq : q ∉ P.exactSupport) (b : qs.Basis) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket (flipBit q b)))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r :=
  (MGate.spectatorOn_exact P hP hq).recordProb_flipBit Submodule.mem_top r

/-- Finitely many flips outside the exact support. -/
theorem MGate.recordProb_flipBits_exact (P : MGate) (hP : P.NoIdeal) (l : List ℕ)
    (hl : ∀ q ∈ l, q ∉ P.exactSupport) (b : qs.Basis) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket (flipBits l b)))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r :=
  MGate.recordProb_flipBits_on P l (fun q hq => MGate.spectatorOn_exact P hP (hl q hq))
    (fun _ _ _ _ => Submodule.mem_top) b Submodule.mem_top r

/-- **Agreement form, exact support.** If `P` has no ideal node and the start kets `b`, `b'`
agree on every qubit of `P.exactSupport` and differ at only finitely many qubits, every record
has the same probability. -/
theorem MGate.recordProb_of_agree_exact (P : MGate) (hP : P.NoIdeal) (b b' : qs.Basis)
    (hagree : ∀ p ∈ P.exactSupport, RegEncoding.bit p b' = RegEncoding.bit p b)
    (hfin : {p | RegEncoding.bit p b' ≠ RegEncoding.bit p b}.Finite) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket b'))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r :=
  MGate.recordProb_of_agree_on P b b' Submodule.mem_top
    (fun q hq => MGate.spectatorOn_exact P hP (fun h => hq (hagree q h)))
    (fun _ _ _ _ => Submodule.mem_top) hfin r

/-- Decomposition along `q ∉ P.exactSupport`, any start state. -/
theorem MGate.recordProb_decomp_exact (P : MGate) (hP : P.NoIdeal) {q : ℕ}
    (hq : q ∉ P.exactSupport) (ψ₀ : qs.State) (r : Record) :
    recordProb (P.eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2,
          recordProb (P.eval (MState.init (measProj (qubitReg q) o ψ₀))) r :=
  (MGate.spectatorOn_exact P hP hq).recordProb_decomp Submodule.mem_top r

/-- Spectator in superposition, `q ∉ P.exactSupport`, any basis state, any `α β`. -/
theorem MGate.recordProb_superpose_exact (P : MGate) (hP : P.NoIdeal) {q : ℕ}
    (hq : q ∉ P.exactSupport) (b : qs.Basis) (α β : ℂ) (r : Record) :
    recordProb (P.eval (MState.init (α • qs.ket b + β • qs.ket (flipBit q b)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb (P.eval (MState.init (qs.ket b))) r :=
  (MGate.spectatorOn_exact P hP hq).recordProb_superpose Submodule.mem_top Submodule.mem_top α β r

end MGates

end Readout
end Shor
