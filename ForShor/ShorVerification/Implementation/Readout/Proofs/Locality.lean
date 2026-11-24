import ForShor.ShorVerification.Implementation.Readout.Support
import ForShor.ShorVerification.Implementation.Readout.Proofs.Basic

/-!
# Readout: semantic locality of `Gate` and `MGate` programs

`Gate.qubitSupport` / `MGate.qubitSupport` (`Readout/Support.lean`) are syntactic. This file
ties them to the semantics: a program never depends on a qubit it does not name.

* `flipBit q b`: the basis state `b` with bit `q` flipped, i.e. the ket law of `X q`
  (`PauliXSemantics.eval_X_ket`: `eval (X q) |b⟩ = |flipBit q b⟩`). `flipBits l b` flips the
  qubits of a list one after the other.
* Basis level: every basis map of the gate classes commutes with `flipBit q` for `q` outside
  the qubits it reads or writes (`cnotBasis_flipBit`, …, `radixReverseBasis_flipBit`).
* `Gate.NoIdeal U`: `U` contains no `idealCtrlModMul` node. This is the only domain condition:
  every other ket law of the classes is TOTAL (it holds on every basis ket), while
  `IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact` gives the ideal multiplier
  only on kets with `data < N` (and under side conditions on `c, N, data, ctrl`), so nothing
  is known about it off that domain. `idealCtrlModMul_ket_flipBit` gives the commutation on
  the domain (which flipping an unnamed qubit preserves).
* `gate_commX` (all states): if `U.NoIdeal` and `q ∉ U.qubitSupport` then
  `eval U (eval (X q) ψ) = eval (X q) (eval U ψ)` for EVERY state `ψ`. `adj` is covered
  because every gate is invertible (`GateSemanticsCore.eval_apply_adj`).
* `MGate.eval_commX`: the same for `MGate` programs, branch by branch (`unitary` branchwise,
  `ffPhase` by the `LowerGateClass` phase ket law, `measureReset p` with `p ≠ q`: the Born
  projectors of `qubitReg p` and the reset `X p` commute with `X q`).
* Consequences: `MGate.eval_init_X`, `MGate.recordProb_init_X` (any start state),
  `MGate.recordProb_flipBit`, `MGate.recordProb_flipBits` (finitely many flips),
  `MGate.recordProb_of_agree` (two start kets that agree on every named qubit and differ at
  finitely many qubits have the same record distribution).

No new axiom, no class field: everything is derived from the existing ket laws. This file
treats finitely many differing qubits and the programs' syntactic support; exact support,
infinitely many differences and the low-gate level are in `LocalityReserve`/`LocalityExact`,
`LocalityInfinite` and `LowLocality*`.
-/

namespace Shor
namespace Readout

open MeasureClass

/-! ## Flipping one basis bit -/

section Basis
variable {B : Type*} [RegEncoding B]

/-- `b` with bit `q` flipped: exactly the basis state of the `X q` ket law
(`PauliXSemantics.eval_X_ket`). -/
def flipBit (q : ℕ) (b : B) : B :=
  RegEncoding.writeNat (qubitReg q) (if RegEncoding.bit q b then 0 else 1) b

/-- Flip the qubits of a list in turn (`flipBits [q₁, …, qₖ] b = flipBit q₁ (… (flipBit qₖ b))`). -/
def flipBits (l : List ℕ) (b : B) : B := l.foldr flipBit b

@[simp] theorem flipBits_nil (b : B) : flipBits [] b = b := rfl
@[simp] theorem flipBits_cons (q : ℕ) (l : List ℕ) (b : B) :
    flipBits (q :: l) b = flipBit q (flipBits l b) := rfl

theorem not_mem_qubitReg {p q : ℕ} : q ∉ (qubitReg p).qubits ↔ q ≠ p := by
  simp [qubitReg, Reg.singleton]

theorem bit_flipBit_self (q : ℕ) (b : B) :
    RegEncoding.bit q (flipBit q b) = !RegEncoding.bit q b := by
  unfold flipBit
  rw [bit_writeNat_qubitReg q _ b (by split <;> omega)]
  cases RegEncoding.bit q b <;> simp

theorem bit_flipBit_ne {p q : ℕ} (h : p ≠ q) (b : B) :
    RegEncoding.bit p (flipBit q b) = RegEncoding.bit p b :=
  RegEncoding.bit_writeNat_out _ _ _ _ (not_mem_qubitReg.mpr h)

theorem bit_flipBit (p q : ℕ) (b : B) :
    RegEncoding.bit p (flipBit q b)
      = if p = q then !RegEncoding.bit p b else RegEncoding.bit p b := by
  split_ifs with h
  · subst h; exact bit_flipBit_self p b
  · exact bit_flipBit_ne h b

theorem flipBit_flipBit (q : ℕ) (b : B) : flipBit q (flipBit q b) = b :=
  RegEncoding.basis_ext _ _ fun p => by
    rw [bit_flipBit, bit_flipBit]; split_ifs <;> simp

theorem flipBit_comm (p q : ℕ) (b : B) : flipBit p (flipBit q b) = flipBit q (flipBit p b) :=
  RegEncoding.basis_ext _ _ fun s => by
    rw [bit_flipBit, bit_flipBit, bit_flipBit, bit_flipBit]
    split_ifs <;> subst_vars <;> simp

/-- A register's value depends only on the bits of its own qubits. -/
theorem toNat_congr_bits' (r : Reg) {b b' : B}
    (h : ∀ p ∈ r.qubits, RegEncoding.bit p b = RegEncoding.bit p b') :
    RegEncoding.toNat r b = RegEncoding.toNat r b' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < regSize r
  · rw [← RegEncoding.bit_eq_testBit_toNat r b ⟨i, hi⟩,
      ← RegEncoding.bit_eq_testBit_toNat r b' ⟨i, hi⟩]
    exact h _ (List.getElem_mem _)
  · push Not at hi
    have l1 := RegEncoding.toNat_lt_ASize r b
    have l2 := RegEncoding.toNat_lt_ASize r b'
    rw [ASize] at l1 l2
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le l1 (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le l2 (Nat.pow_le_pow_right (by norm_num) hi))]

theorem toNat_flipBit {r : Reg} {q : ℕ} (h : q ∉ r.qubits) (b : B) :
    RegEncoding.toNat r (flipBit q b) = RegEncoding.toNat r b :=
  toNat_congr_bits' r fun p hp => bit_flipBit_ne (fun e : p = q => h (e ▸ hp)) b

theorem writeNat_flipBit {r : Reg} {q : ℕ} (h : q ∉ r.qubits) (v : ℕ) (b : B) :
    RegEncoding.writeNat r v (flipBit q b) = flipBit q (RegEncoding.writeNat r v b) := by
  refine RegEncoding.basis_ext _ _ fun p => ?_
  by_cases hp : p ∈ r.qubits
  · rw [bit_flipBit_ne (fun e : p = q => h (e ▸ hp))]
    exact RegEncoding.bit_writeNat_in _ _ _ _ _ hp
  · rw [RegEncoding.bit_writeNat_out _ _ _ _ hp, bit_flipBit, bit_flipBit,
      RegEncoding.bit_writeNat_out _ _ _ _ hp]

theorem extToInt_flipBit {e : ExtReg} {q : ℕ} (h : q ∉ e.active.qubits) (b : B) :
    extToInt e (flipBit q b) = extToInt e b := by
  simp only [extToInt, ExtReg.toNat, toNat_flipBit h]

theorem not_mem_active {e : ExtReg} {q : ℕ} (h : q ∉ e.ownedQubits) : q ∉ e.active.qubits :=
  fun h' => h (List.mem_append_left _ h')

theorem not_mem_reserve {e : ExtReg} {q : ℕ} (h : q ∉ e.ownedQubits) : q ∉ e.reserve.qubits :=
  fun h' => h (List.mem_append_right _ h')

/-! ### Every basis map of the gate classes commutes with flipping an unnamed bit -/

theorem cnotBasis_flipBit {a t q : ℕ} (ha : q ≠ a) (ht : q ≠ t) (b : B) :
    cnotBasis a t (flipBit q b) = flipBit q (cnotBasis a t b) := by
  unfold cnotBasis
  rw [bit_flipBit_ne (Ne.symm ha), bit_flipBit_ne (Ne.symm ht),
    writeNat_flipBit (not_mem_qubitReg.mpr ht)]
  split_ifs <;> rfl

theorem toffoliBasis_flipBit {a a' t q : ℕ} (ha : q ≠ a) (ha' : q ≠ a') (ht : q ≠ t) (b : B) :
    toffoliBasis a a' t (flipBit q b) = flipBit q (toffoliBasis a a' t b) := by
  unfold toffoliBasis
  rw [bit_flipBit_ne (Ne.symm ha), bit_flipBit_ne (Ne.symm ha'), bit_flipBit_ne (Ne.symm ht),
    writeNat_flipBit (not_mem_qubitReg.mpr ht)]
  split_ifs <;> rfl

theorem cmpGeConstBasis_flipBit {N : ℕ} {data : Reg} {f q : ℕ} (hd : q ∉ data.qubits)
    (hf : q ≠ f) (b : B) :
    cmpGeConstBasis N data f (flipBit q b) = flipBit q (cmpGeConstBasis N data f b) := by
  unfold cmpGeConstBasis
  rw [bit_flipBit_ne (Ne.symm hf), toNat_flipBit hd, writeNat_flipBit (not_mem_qubitReg.mpr hf)]
  split_ifs <;> rfl

theorem csubConstBasis_flipBit {N : ℕ} {data : Reg} {f q : ℕ} (hd : q ∉ data.qubits)
    (hf : q ≠ f) (b : B) :
    csubConstBasis N data f (flipBit q b) = flipBit q (csubConstBasis N data f b) := by
  unfold csubConstBasis
  rw [bit_flipBit_ne (Ne.symm hf), toNat_flipBit hd, writeNat_flipBit hd]
  split_ifs <;> rfl

theorem negateBasis_flipBit {r : ExtReg} {q : ℕ} (h : q ∉ r.active.qubits) (b : B) :
    negateBasis r (flipBit q b) = flipBit q (negateBasis r b) := by
  unfold negateBasis
  rw [extToInt_flipBit h, writeNat_flipBit h]

theorem addScaledBasis_flipBit {d s : ExtReg} {neg : Bool} {sh q : ℕ} (hd : q ∉ d.active.qubits)
    (hs : q ∉ s.active.qubits) (b : B) :
    addScaledBasis d s neg sh (flipBit q b) = flipBit q (addScaledBasis d s neg sh b) := by
  unfold addScaledBasis
  by_cases hdis : ExtReg.ActiveDisjoint d s
  · simp only [hdis, ↓reduceDIte, extToInt_flipBit hd, extToInt_flipBit hs, writeNat_flipBit hd]
  · simp only [hdis, ↓reduceDIte]

theorem shiftLBasis_flipBit {r : ExtReg} {n q : ℕ} (h : q ∉ r.active.qubits) (b : B) :
    shiftLBasis r n (flipBit q b) = flipBit q (shiftLBasis r n b) := by
  unfold shiftLBasis shiftLBasisRaw
  rw [extToInt_flipBit h]
  simp only [ExtReg.toNat, toNat_flipBit h, writeNat_flipBit h]
  split_ifs <;> rfl

theorem shiftRBasis_flipBit {r : ExtReg} {n q : ℕ} (h : q ∉ r.active.qubits) (b : B) :
    shiftRBasis r n (flipBit q b) = flipBit q (shiftRBasis r n b) := by
  unfold shiftRBasis shiftRBasisRaw
  rw [extToInt_flipBit h]
  simp only [ExtReg.toNat, toNat_flipBit h, writeNat_flipBit h]
  split_ifs <;> rfl

theorem signExtendBasis_flipBit {r : ExtReg} {n q : ℕ} (h : q ∉ r.ownedQubits) (b : B) :
    signExtendBasis r n (flipBit q b) = flipBit q (signExtendBasis r n b) := by
  have hn : q ∉ (r.newBits n).qubits := fun h' =>
    not_mem_reserve h (List.mem_of_mem_take h')
  unfold signExtendBasis signExtendNewValue
  rw [extToInt_flipBit (not_mem_active h), toNat_flipBit hn, writeNat_flipBit hn]

theorem radixReverseBasis_flipBit {r : Reg} {m q : ℕ} (h : q ∉ r.qubits) (b : B) :
    radixReverseBasis r m (flipBit q b) = flipBit q (radixReverseBasis r m b) := by
  unfold radixReverseBasis
  split_ifs with hm
  · have hL : q ∉ (splitLeft r ⟨m, hm⟩).qubits := fun h' => h (List.mem_of_mem_take h')
    have hR : q ∉ (splitRight r ⟨m, hm⟩).qubits := fun h' => h (List.mem_of_mem_drop h')
    simp only [toNat_flipBit hL, toNat_flipBit hR, writeNat_flipBit h]
  · rfl

end Basis

/-! ## Gates commute with `X q` for every unnamed `q` -/

/-- `U` contains no `idealCtrlModMul` node: the one gate whose ket law the classes give only
on a domain (`data < N`, plus side conditions). -/
def _root_.Shor.Gate.NoIdeal : Gate → Prop
  | .seq U V => U.NoIdeal ∧ V.NoIdeal
  | .adj U => U.NoIdeal
  | .idealCtrlModMul _ _ _ _ => False
  | _ => True

/-- `MGate.NoIdeal P`: no unitary part of `P` contains an `idealCtrlModMul` node. -/
def _root_.Shor.MGate.NoIdeal : MGate → Prop
  | .unitary g => g.NoIdeal
  | .seq a b => a.NoIdeal ∧ b.NoIdeal
  | .measureReset _ => True
  | .ffPhase _ _ => True

section Gates
variable {qs : QSemantics} [RegEncoding qs.Basis]

/-- `eval U` commutes with `eval (X q)` on every state. -/
def CommX (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs] (U : Gate) (q : ℕ) :
    Prop :=
  ∀ ψ : qs.State, qs.eval U (qs.eval (Gate.X q) ψ) = qs.eval (Gate.X q) (qs.eval U ψ)

variable [GateSemanticsFacts qs]

theorem eval_X_ket_flipBit (q : ℕ) (b : qs.Basis) :
    qs.eval (Gate.X q) (qs.ket b) = qs.ket (flipBit q b) :=
  PauliXSemantics.eval_X_ket q b

/-- Commutation on kets gives commutation on every state (both sides are linear). -/
theorem commX_of_ket {U : Gate} {q : ℕ}
    (h : ∀ b, qs.eval U (qs.ket (flipBit q b)) = qs.eval (Gate.X q) (qs.eval U (qs.ket b))) :
    CommX qs U q := by
  intro ψ
  have := linearMap_ext_ket ((gateL U).comp (gateL (Gate.X q)))
    ((gateL (Gate.X q)).comp (gateL U)) (fun b => by
      simp only [LinearMap.comp_apply, gateL_apply]
      rw [eval_X_ket_flipBit]; exact h b) ψ
  simpa using this

/-- A gate acting on kets by a basis map that commutes with `flipBit q` commutes with `X q`. -/
theorem commX_of_basis {U : Gate} {q : ℕ} (f : qs.Basis → qs.Basis)
    (hU : ∀ b, qs.eval U (qs.ket b) = qs.ket (f b)) (hf : ∀ b, f (flipBit q b) = flipBit q (f b)) :
    CommX qs U q :=
  commX_of_ket fun b => by rw [hU, hf, hU, eval_X_ket_flipBit]

/-- A gate acting on kets diagonally, with a scalar that does not see bit `q`, commutes with
`X q`. -/
theorem commX_of_diag {U : Gate} {q : ℕ} (s : qs.Basis → ℂ)
    (hU : ∀ b, qs.eval U (qs.ket b) = s b • qs.ket b) (hs : ∀ b, s (flipBit q b) = s b) :
    CommX qs U q :=
  commX_of_ket fun b => by rw [hU, hs, hU, gate_eval_smul, eval_X_ket_flipBit]

theorem commX_id (q : ℕ) : CommX qs Gate.id q := fun ψ => by
  simp only [QSemantics.eval, GateSemanticsCore.eval_id]

theorem commX_seq {U V : Gate} {q : ℕ} (hU : CommX qs U q) (hV : CommX qs V q) :
    CommX qs (U ;; V) q := fun ψ => by
  unfold CommX at hU hV
  simp only [QSemantics.eval, GateSemanticsCore.eval_seq] at hU hV ⊢
  rw [hU, hV]

/-- Every gate is injective (it preserves norms). -/
theorem gate_eval_injective (V : Gate) {a b : qs.State} (h : qs.eval V a = qs.eval V b) :
    a = b := by
  have h1 : qs.eval V (a - b) = 0 := by rw [gate_eval_sub, h, sub_self]
  have h2 := norm_eval_gate V (a - b)
  rw [h1, norm_zero] at h2
  exact sub_eq_zero.mp (norm_eq_zero.mp h2.symm)

/-- Every gate is invertible: `U` undoes `adj U` (from `eval_adj_apply` and injectivity of
`adj U`). -/
theorem gate_eval_apply_adj (U : Gate) (ψ : qs.State) : qs.eval U (qs.eval (Gate.adj U) ψ) = ψ :=
  gate_eval_injective (Gate.adj U) (GateSemanticsCore.eval_adj_apply U _)

/-- `adj U` commutes with `X q` when `U` does: every gate is invertible
(`eval U (eval (adj U) ψ) = ψ`). -/
theorem commX_adj {U : Gate} {q : ℕ} (hU : CommX qs U q) : CommX qs (Gate.adj U) q := fun ψ => by
  have h1 := gate_eval_apply_adj U ψ
  conv_lhs => rw [← h1]
  rw [← hU, QSemantics.eval, GateSemanticsCore.eval_adj_apply]

theorem commX_H {p q : ℕ} (h : q ≠ p) : CommX qs (Gate.H p) q := commX_of_ket fun b => by
  rw [HadamardSemantics.eval_H_ket, HadamardSemantics.eval_H_ket, bit_flipBit_ne (Ne.symm h),
    writeNat_flipBit (not_mem_qubitReg.mpr h), writeNat_flipBit (not_mem_qubitReg.mpr h),
    ← eval_X_ket_flipBit, ← eval_X_ket_flipBit, gate_eval_smul, gate_eval_add, gate_eval_smul]

theorem commX_X {p q : ℕ} : CommX qs (Gate.X p) q :=
  commX_of_basis (flipBit p) (fun b => eval_X_ket_flipBit p b) (fun b => flipBit_comm p q b)

theorem commX_QFT {r : ExtReg} {q : ℕ} (h : q ∉ r.active.qubits) : CommX qs (Gate.QFT r) q :=
  commX_of_ket fun b => by
    rw [QFTSemantics.eval_QFT_ket, QFTSemantics.eval_QFT_ket, ← gateL_apply, map_smul, map_sum]
    simp only [ExtReg.toNat, toNat_flipBit h, writeNat_flipBit h, map_smul, gateL_apply,
      eval_X_ket_flipBit]

theorem commX_CSignedPhaseProd {ctrl q : ℕ} {phi : Angle} {x z : ExtReg} (hc : q ≠ ctrl)
    (hx : q ∉ x.active.qubits) (hz : q ∉ z.active.qubits) :
    CommX qs (Gate.CSignedPhaseProd ctrl phi x z) q := commX_of_ket fun b => by
  rw [PhaseSemantics.eval_CSignedPhaseProd_ket, PhaseSemantics.eval_CSignedPhaseProd_ket,
    bit_flipBit_ne (Ne.symm hc), extToInt_flipBit hx, extToInt_flipBit hz]
  split_ifs
  · rw [gate_eval_smul, eval_X_ket_flipBit]
  · rw [eval_X_ket_flipBit]

/-- **Per-primitive locality, all states.** A gate with no `idealCtrlModMul` node commutes
with `X q` for every qubit `q` it does not name: `eval U (eval (X q) ψ) = eval (X q) (eval U ψ)`
for every state `ψ`. -/
theorem gate_commX (U : Gate) (hU : U.NoIdeal) {q : ℕ} (hq : q ∉ U.qubitSupport) :
    CommX qs U q := by
  induction U with
  | id => exact commX_id q
  | seq U V ihU ihV =>
    simp only [Gate.qubitSupport, Set.mem_union, not_or] at hq
    exact commX_seq (ihU hU.1 hq.1) (ihV hU.2 hq.2)
  | adj U ih => exact commX_adj (ih hU hq)
  | H p => exact commX_H (by simpa [Gate.qubitSupport] using hq)
  | X p => exact commX_X
  | CNOT a t =>
    simp only [Gate.qubitSupport, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
    exact commX_of_basis _ (ClassicalReversibleSemantics.eval_CNOT_ket a t)
      (cnotBasis_flipBit hq.1 hq.2)
  | Toffoli a a' t =>
    simp only [Gate.qubitSupport, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
    exact commX_of_basis _ (ClassicalReversibleSemantics.eval_Toffoli_ket a a' t)
      (toffoliBasis_flipBit hq.1 hq.2.1 hq.2.2)
  | QFT r =>
    exact commX_QFT (not_mem_active (by simpa [Gate.qubitSupport] using hq))
  | RadixReverse r m =>
    exact commX_of_basis _ (RadixReverseSemantics.eval_RadixReverse_ket_total r m)
      (radixReverseBasis_flipBit (by simpa [Gate.qubitSupport] using hq))
  | SignedPhaseProd phi x z =>
    simp only [Gate.qubitSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_of_diag _ (PhaseSemantics.eval_SignedPhaseProd_ket phi x z) fun b => by
      rw [extToInt_flipBit (not_mem_active hq.1), extToInt_flipBit (not_mem_active hq.2)]
  | CSignedPhaseProd ctrl phi x z =>
    simp only [Gate.qubitSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_CSignedPhaseProd hq.1 (not_mem_active hq.2.1) (not_mem_active hq.2.2)
  | CmpGeConst N d s f =>
    simp only [Gate.qubitSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_of_basis _ (ModularArithmeticSemantics.eval_CmpGeConst_ket N d s f)
      (cmpGeConstBasis_flipBit (not_mem_active hq.1) hq.2.2)
  | CSubConst N d s f =>
    simp only [Gate.qubitSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_of_basis _ (ModularArithmeticSemantics.eval_CSubConst_ket N d s f)
      (csubConstBasis_flipBit (not_mem_active hq.1) hq.2.2)
  | ShiftL r n =>
    exact commX_of_basis _ (ArithmeticSemantics.eval_ShiftL_ket_total r n)
      (shiftLBasis_flipBit (not_mem_active (by simpa [Gate.qubitSupport] using hq)))
  | ShiftR r n =>
    exact commX_of_basis _ (ArithmeticSemantics.eval_ShiftR_ket_total r n)
      (shiftRBasis_flipBit (not_mem_active (by simpa [Gate.qubitSupport] using hq)))
  | Negate r =>
    exact commX_of_basis _ (ArithmeticSemantics.eval_Negate_ket_total r)
      (negateBasis_flipBit (not_mem_active (by simpa [Gate.qubitSupport] using hq)))
  | AddScaled d s neg sh =>
    simp only [Gate.qubitSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commX_of_basis _ (ArithmeticSemantics.eval_AddScaled_ket_total d s neg sh)
      (addScaledBasis_flipBit (not_mem_active hq.1) (not_mem_active hq.2))
  | zeroExtend r n =>
    intro ψ
    rw [ExtensionSemantics.eval_zeroExtend, ExtensionSemantics.eval_zeroExtend]
  | signExtend r n =>
    exact commX_of_basis _ (ExtensionSemantics.eval_signExtend_ket_total r n)
      (signExtendBasis_flipBit (by simpa [Gate.qubitSupport] using hq))
  | zeroDealloc r n =>
    intro ψ
    rw [ExtensionSemantics.eval_zeroDealloc, ExtensionSemantics.eval_zeroDealloc]
  | signDealloc r n =>
    exact commX_of_basis _ (ExtensionSemantics.eval_signDealloc_ket_total r n)
      (signExtendBasis_flipBit (by simpa [Gate.qubitSupport] using hq))
  | idealCtrlModMul _ _ _ _ => exact hU.elim

/-- **The ideal multiplier, on its domain.** Its ket law
(`eval_idealCtrlModMul_ket_exact`) needs `1 < N ≤ 2^|data|`, `c` coprime to `N`,
`ctrl ∉ data` and `data < N` on the ket. On such a ket, flipping a qubit `q` outside `data`
and `≠ ctrl` (which keeps `data < N`) commutes with the gate. Off the domain the classes say
nothing, which is why `gate_commX` excludes this constructor. -/
theorem idealCtrlModMul_ket_flipBit {c N ctrl q : ℕ} {data : Reg} (hN : 1 < N)
    (hNd : N ≤ ASize data) (hc : Nat.Coprime c N) (hctrl : ctrl ∉ data.qubits)
    (hqd : q ∉ data.qubits) (hqc : q ≠ ctrl) (b : qs.Basis)
    (hb : RegEncoding.toNat data b < N) :
    qs.eval (Gate.idealCtrlModMul c N data ctrl) (qs.ket (flipBit q b))
      = qs.eval (Gate.X q) (qs.eval (Gate.idealCtrlModMul c N data ctrl) (qs.ket b)) := by
  have hb' : RegEncoding.toNat data (flipBit q b) < N := by rwa [toNat_flipBit hqd]
  rw [IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact c N data ctrl _ hN hNd hc
      hctrl hb',
    IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact c N data ctrl _ hN hNd hc
      hctrl hb, bit_flipBit_ne (Ne.symm hqc), toNat_flipBit hqd, writeNat_flipBit hqd,
    eval_X_ket_flipBit]

end Gates

/-! ## Measurement programs -/

section MGates
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

omit [LowerGateClass qs] in
/-- The Born projectors of the one-qubit register `qubitReg p` commute with `X q`, `q ≠ p`. -/
theorem measProj_commX {p q : ℕ} (h : q ≠ p) (o : ℕ) (ψ : qs.State) :
    measProj (qubitReg p) o (qs.eval (Gate.X q) ψ)
      = qs.eval (Gate.X q) (measProj (qubitReg p) o ψ) := by
  have := linearMap_ext_ket ((measProj (qubitReg p) o).toLinearMap.comp (gateL (Gate.X q)))
    ((gateL (Gate.X q)).comp (measProj (qubitReg p) o).toLinearMap) (fun b => by
      simp only [LinearMap.comp_apply, gateL_apply, ContinuousLinearMap.coe_coe]
      rw [eval_X_ket_flipBit, MeasureClass.measProj_ket, MeasureClass.measProj_ket,
        toNat_flipBit (not_mem_qubitReg.mpr h)]
      split_ifs
      · rw [eval_X_ket_flipBit]
      · rw [MGate.gate_eval_zero_state]) ψ
  simpa using this

omit [MeasureClass qs] in
/-- The phase gate on `p` commutes with `X q`, `q ≠ p`. -/
theorem phase_commX {p q : ℕ} (h : q ≠ p) (θ : Angle) (ψ : qs.State) :
    LowerGateClass.evalL (LowGate.Phase p θ) (qs.eval (Gate.X q) ψ)
      = qs.eval (Gate.X q) (LowerGateClass.evalL (LowGate.Phase p θ) ψ) := by
  have := linearMap_ext_ket ((lowL (LowGate.Phase p θ)).comp (gateL (Gate.X q)))
    ((gateL (Gate.X q)).comp (lowL (LowGate.Phase p θ))) (fun b => by
      simp only [LinearMap.comp_apply, gateL_apply, lowL_apply]
      rw [eval_X_ket_flipBit, LowerGateClass.evalL_Phase_ket, LowerGateClass.evalL_Phase_ket,
        bit_flipBit_ne (Ne.symm h)]
      split_ifs
      · rw [gate_eval_smul, eval_X_ket_flipBit]
      · rw [eval_X_ket_flipBit]) ψ
  simpa using this

omit [LowerGateClass qs] in
/-- Both children of `measureReset p` commute with `X q`, `q ≠ p`. -/
theorem measureResetBranch_commX {p q : ℕ} (h : q ≠ p) (o : Bool) (ψ : qs.State) :
    measureResetBranch p o (qs.eval (Gate.X q) ψ)
      = qs.eval (Gate.X q) (measureResetBranch p o ψ) := by
  cases o
  · exact measProj_commX h 0 ψ
  · simp only [measureResetBranch, ite_true]
    rw [measProj_commX h 1 ψ]
    exact commX_X _

/-- **Locality of `MGate` programs, branch by branch.** If no unitary part of `P` has an
`idealCtrlModMul` node and `q ∉ P.qubitSupport`, then running `P` on the branching state
`X q ψ` (branchwise) gives `X q` of the run on `ψ`, branch by branch. -/
theorem MGate.eval_commX (P : MGate) (hP : P.NoIdeal) {q : ℕ} (hq : q ∉ P.qubitSupport)
    (ψ : MState qs) :
    P.eval (fun r => qs.eval (Gate.X q) (ψ r)) = fun r => qs.eval (Gate.X q) (P.eval ψ r) := by
  induction P generalizing ψ with
  | unitary g =>
    funext r
    exact gate_commX g hP hq (ψ r)
  | seq a b iha ihb =>
    simp only [MGate.qubitSupport, Set.mem_union, not_or] at hq
    simp only [MGate.eval_seq]
    rw [iha hP.1 hq.1, ihb hP.2 hq.2]
  | measureReset p =>
    have hp : q ≠ p := by simpa [MGate.qubitSupport] using hq
    funext r
    simp only [MGate.eval]
    split
    · rw [MGate.gate_eval_zero_state]
    · exact measureResetBranch_commX hp _ _
  | ffPhase p j =>
    have hp : q ≠ p := by simpa [MGate.qubitSupport] using hq
    funext r
    exact phase_commX hp _ _

omit [LowerGateClass qs] [MeasureClass qs] in
theorem MState.init_X (q : ℕ) (ψ₀ : qs.State) :
    MState.init (qs.eval (Gate.X q) ψ₀) = fun r => qs.eval (Gate.X q) (MState.init ψ₀ r) := by
  funext r
  unfold MState.init
  split
  · rfl
  · rw [MGate.gate_eval_zero_state]

/-- **Locality from a start state.** Under the hypotheses of `MGate.eval_commX`, every branch
of the run from `X q ψ₀` is `X q` of the corresponding branch of the run from `ψ₀`. -/
theorem MGate.eval_init_X (P : MGate) (hP : P.NoIdeal) {q : ℕ} (hq : q ∉ P.qubitSupport)
    (ψ₀ : qs.State) (r : Record) :
    P.eval (MState.init (qs.eval (Gate.X q) ψ₀)) r
      = qs.eval (Gate.X q) (P.eval (MState.init ψ₀) r) := by
  rw [MState.init_X, MGate.eval_commX P hP hq]

/-- **The record distribution does not see an unnamed qubit.** For every start state `ψ₀`
and every record `r`, flipping a qubit `q ∉ P.qubitSupport` in the start state (applying
`X q`) does not change the probability of `r`. -/
theorem MGate.recordProb_init_X (P : MGate) (hP : P.NoIdeal) {q : ℕ}
    (hq : q ∉ P.qubitSupport) (ψ₀ : qs.State) (r : Record) :
    recordProb (P.eval (MState.init (qs.eval (Gate.X q) ψ₀))) r
      = recordProb (P.eval (MState.init ψ₀)) r := by
  rw [recordProb, recordProb, MGate.eval_init_X P hP hq, norm_eval_gate]

/-- Basis-ket form: `|flipBit q b⟩` and `|b⟩` give the same record distribution. -/
theorem MGate.recordProb_flipBit (P : MGate) (hP : P.NoIdeal) {q : ℕ}
    (hq : q ∉ P.qubitSupport) (b : qs.Basis) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket (flipBit q b)))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  rw [← eval_X_ket_flipBit]
  exact MGate.recordProb_init_X P hP hq _ r

/-- Finitely many flips of unnamed qubits. -/
theorem MGate.recordProb_flipBits (P : MGate) (hP : P.NoIdeal) (l : List ℕ)
    (hl : ∀ q ∈ l, q ∉ P.qubitSupport) (b : qs.Basis) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket (flipBits l b)))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [flipBits_cons, MGate.recordProb_flipBit P hP (hl q (List.mem_cons_self ..)),
      ih fun q' h => hl q' (List.mem_cons_of_mem _ h)]

end MGates

/-! ## Two kets that differ at finitely many qubits -/

section Agree
variable {B : Type*} [RegEncoding B]

theorem bit_flipBits {l : List ℕ} (hl : l.Nodup) (p : ℕ) (b : B) :
    RegEncoding.bit p (flipBits l b)
      = if p ∈ l then !RegEncoding.bit p b else RegEncoding.bit p b := by
  induction l with
  | nil => simp
  | cons q l ih =>
    rw [List.nodup_cons] at hl
    rw [flipBits_cons, bit_flipBit]
    by_cases hpq : p = q
    · subst hpq
      rw [ih hl.2]
      simp [hl.1]
    · rw [ih hl.2]
      simp [hpq]

/-- Two basis states that differ at finitely many bits are related by flipping exactly those
bits. -/
theorem eq_flipBits_of_finite (b b' : B)
    (hfin : {p | RegEncoding.bit p b' ≠ RegEncoding.bit p b}.Finite) :
    b' = flipBits hfin.toFinset.toList b := by
  refine RegEncoding.basis_ext _ _ fun p => ?_
  rw [bit_flipBits (Finset.nodup_toList _)]
  simp only [Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  split_ifs with h
  · cases h1 : RegEncoding.bit p b' <;> cases h2 : RegEncoding.bit p b <;> simp_all
  · simpa using h

end Agree

section AgreeM
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- **Locality, agreement form.** If `P` has no `idealCtrlModMul` node, and the start kets
`b` and `b'` agree on every qubit `P` names and differ at only finitely many qubits, then
every record has the same probability from `|b'⟩` as from `|b⟩`. -/
theorem MGate.recordProb_of_agree (P : MGate) (hP : P.NoIdeal) (b b' : qs.Basis)
    (hagree : ∀ p ∈ P.qubitSupport, RegEncoding.bit p b' = RegEncoding.bit p b)
    (hfin : {p | RegEncoding.bit p b' ≠ RegEncoding.bit p b}.Finite) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket b'))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  conv_lhs => rw [eq_flipBits_of_finite b b' hfin]
  refine MGate.recordProb_flipBits P hP _ (fun q hq hS => ?_) b r
  simp only [Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hq
  exact hq (hagree q hS)

end AgreeM

end Readout
end Shor
