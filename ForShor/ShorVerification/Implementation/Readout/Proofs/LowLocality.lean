import ForShor.ShorVerification.Implementation.Readout.LocalitySpectator

/-!
# Readout: semantic locality at the low-gate level

`Proofs/Locality.lean` and `Proofs/LocalityProj.lean` prove locality for the high-level
languages `Gate` / `MGate` over `qs.eval`. This file proves it directly for the low-level
languages `LowGate` / `MLowGate` over `LowerGateClass.evalL`, with no detour through the
lowering-correctness theorem (`semiclassical_lowerM_eval`), hence with no clean-workspace
hypothesis and for ANY start state.

Only the laws of `LowerGateClass` and `MeasureClass` are used (no `GateSemanticsCore`):
the bit flip is the low-level `LowGate.X q` (`evalL_X_ket` gives `|b⟩ ↦ |flipBit q b⟩`).

## The footprint `LowGate.lowFootprint`

`LowGate.usedQubits` (the qubit set of the peak walk, `Framework/Gatecount/ResourceModel`)
is NOT a semantic footprint for one constructor: `usedQubits (signDealloc r n)` is
`r.active` only, while its ket law (`signDeallocBasis = signExtendBasis`) WRITES the `n`
deallocated qubits `r.newBits n` (it complements them when `r` is negative). Such a qubit is
outside `usedQubits` but its Z projector does not commute with the gate (a model
counterexample is in `Model/Standard/SemiclassicalLowLocalityModel.lean`). So the theorems
here use `lowFootprint`, which is `usedQubits` on every constructor except
`signDealloc r n`, where it is `extRegGrowQubits r n` (= `r.active` and `r.newBits n`, the
same set as `usedQubits (signExtend r n)`). `usedQubits g ⊆ lowFootprint g`, with equality
on programs with no `signDealloc` (`lowFootprint_eq_usedQubits`).

## Results

The labels B1-B3 below name the three groups of results.

* B1 (`lowGate_commX`): for EVERY `LowGate` `g` (adjoints included) and
  `q ∉ g.lowFootprint`, `evalL g (evalL (X q) ψ) = evalL (X q) (evalL g ψ)` for every state.
  Per constructor: `H`, `X`, `Phase`, `CNOT`, `Toffoli`, `ShiftL`, `ShiftR`, `Negate`,
  `AddScaled`, `signExtend`, `signDealloc`, `RadixReverse` have TOTAL ket laws (no side
  condition) and are handled on kets, then on every state by `qs.state_induction` and
  `evalL_add` / `evalL_smul` (`linearMap_ext_ket`); `zeroExtend`, `zeroDealloc` are the
  identity on every state (`evalL_zeroExtend_id`, `evalL_zeroDealloc_id`), so they commute with
  everything (their footprint condition is not even used).
* B2 (`evalL_apply_adj`, `commX_adj`): NO new law is needed for adjoints. The existing law
  `evalL_adj_apply : evalL (adj L) (evalL L ψ) = ψ` holds for EVERY low gate, in particular
  for `adj L`, so `evalL (adj L)` is injective; being also surjective (it undoes `evalL L`), it
  is a bijection with inverse `evalL L`, which gives `evalL L (evalL (adj L) ψ) = ψ` on every
  state. Commutation of `adj L` then follows from that of `L`.
* `lowGate_commProj`: the same hypotheses give commutation with the Born projectors
  `measProj (qubitReg q) o`.
* B3 (general, `MLowGate`): `MLowGate.lowSupport` (footprints of the unitary parts, plus the
  qubit of every `measureReset` / `ffPhase`); `MLowGate.eval_commX`, `MLowGate.eval_commProj`,
  and for ANY start state: `MLowGate.recordProb_init_X`, `recordProb_flipBit(s)`,
  `recordProb_of_agree`, `recordProb_decomp`, `recordProb_superpose(_unit)`.

No new axiom, no new class, no class field.
-/

namespace Shor

/-! ## The semantic footprint of a low-level gate -/

/-- The qubits a low-level gate may read or write, as far as its `LowerGateClass` ket law
says: `LowGate.usedQubits`, except for `signDealloc r n`, whose ket law writes the `n`
deallocated reserve qubits `r.newBits n` too (`extRegGrowQubits r n`). -/
def LowGate.lowFootprint : LowGate → Finset ℕ
  | .id => ∅
  | .seq U V => U.lowFootprint ∪ V.lowFootprint
  | .adj U => U.lowFootprint
  | .H q => {q}
  | .X q => {q}
  | .Phase q _ => {q}
  | .CNOT c t => {c, t}
  | .Toffoli c₁ c₂ t => {c₁, c₂, t}
  | .ShiftL r _ => extRegActiveQubits r
  | .ShiftR r _ => extRegActiveQubits r
  | .Negate r => extRegActiveQubits r
  | .AddScaled d s _ _ => extRegActiveQubits d ∪ extRegActiveQubits s
  | .zeroExtend r n => extRegGrowQubits r n
  | .signExtend r n => extRegGrowQubits r n
  | .zeroDealloc _ _ => ∅
  | .signDealloc r n => extRegGrowQubits r n
  | .RadixReverse r _ => r.qubits.toFinset

/-- `LowGate` has no `signDealloc` node. -/
def LowGate.NoSignDealloc : LowGate → Prop
  | .seq U V => U.NoSignDealloc ∧ V.NoSignDealloc
  | .adj U => U.NoSignDealloc
  | .signDealloc _ _ => False
  | _ => True

/-- The used-qubit set of the peak walk is contained in the footprint. -/
theorem LowGate.usedQubits_subset_lowFootprint (g : LowGate) : g.usedQubits ⊆ g.lowFootprint := by
  induction g with
  | seq U V ihU ihV => exact Finset.union_subset_union ihU ihV
  | adj U ih => exact ih
  | signDealloc r n =>
    intro q hq
    simp only [LowGate.usedQubits, List.mem_toFinset] at hq
    simp only [LowGate.lowFootprint, extRegGrowQubits, ExtReg.grow, Reg.append, List.mem_toFinset,
      List.mem_append]
    exact Or.inl hq
  | _ => exact le_rfl

/-- Without `signDealloc`, the footprint IS the used-qubit set of the peak walk. -/
theorem LowGate.lowFootprint_eq_usedQubits (g : LowGate) (h : g.NoSignDealloc) :
    g.lowFootprint = g.usedQubits := by
  induction g with
  | seq U V ihU ihV =>
    simp only [LowGate.lowFootprint, LowGate.usedQubits, ihU h.1, ihV h.2]
  | adj U ih => exact ih h
  | signDealloc r n => exact h.elim
  | _ => rfl

namespace Readout

open MeasureClass

/-! ## Basis lemmas for sign extension, with the exact footprint -/

section Basis
variable {B : Type*} [RegEncoding B]

theorem not_mem_grow {r : ExtReg} {n q : ℕ} (h : q ∉ extRegGrowQubits r n) :
    q ∉ r.active.qubits ∧ q ∉ (r.newBits n).qubits := by
  simp only [extRegGrowQubits, ExtReg.grow, Reg.append, List.mem_toFinset, List.mem_append,
    not_or] at h
  exact h

theorem signExtendBasis_flipBit_grow {r : ExtReg} {n q : ℕ} (ha : q ∉ r.active.qubits)
    (hn : q ∉ (r.newBits n).qubits) (b : B) :
    signExtendBasis r n (flipBit q b) = flipBit q (signExtendBasis r n b) := by
  unfold signExtendBasis signExtendNewValue
  rw [extToInt_flipBit ha, toNat_flipBit hn, writeNat_flipBit hn]

theorem bit_signExtendBasis_of_not_mem_newBits {r : ExtReg} {n q : ℕ}
    (hn : q ∉ (r.newBits n).qubits) (b : B) :
    RegEncoding.bit q (signExtendBasis r n b) = RegEncoding.bit q b :=
  RegEncoding.bit_writeNat_out _ _ _ _ hn

end Basis

/-! ## B1/B2: every low gate commutes with `X q` off its footprint -/

section Gates
variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

/-- The low-level `X q` acts on kets by `flipBit q` (this is `evalL_X_ket`). -/
theorem evalL_X_ket_flipBit (q : ℕ) (b : qs.Basis) :
    LowerGateClass.evalL (LowGate.X q) (qs.ket b) = qs.ket (flipBit q b) :=
  LowerGateClass.evalL_X_ket q b

/-- `evalL L` commutes with the low-level `evalL (X q)` on every state. -/
def CommXL (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs] (L : LowGate) (q : ℕ) :
    Prop :=
  ∀ ψ : qs.State, LowerGateClass.evalL L (LowerGateClass.evalL (LowGate.X q) ψ)
    = LowerGateClass.evalL (LowGate.X q) (LowerGateClass.evalL L ψ)

theorem commXL_of_ket {L : LowGate} {q : ℕ}
    (h : ∀ b, LowerGateClass.evalL L (qs.ket (flipBit q b))
      = LowerGateClass.evalL (LowGate.X q) (LowerGateClass.evalL L (qs.ket b))) :
    CommXL qs L q := by
  intro ψ
  have := linearMap_ext_ket ((lowL L).comp (lowL (LowGate.X q)))
    ((lowL (LowGate.X q)).comp (lowL L)) (fun b => by
      simp only [LinearMap.comp_apply, lowL_apply]
      rw [evalL_X_ket_flipBit]; exact h b) ψ
  simpa using this

theorem commXL_of_basis {L : LowGate} {q : ℕ} (f : qs.Basis → qs.Basis)
    (hL : ∀ b, LowerGateClass.evalL L (qs.ket b) = qs.ket (f b))
    (hf : ∀ b, f (flipBit q b) = flipBit q (f b)) : CommXL qs L q :=
  commXL_of_ket fun b => by rw [hL, hf, hL, evalL_X_ket_flipBit]

theorem commXL_of_diag {L : LowGate} {q : ℕ} (s : qs.Basis → ℂ)
    (hL : ∀ b, LowerGateClass.evalL L (qs.ket b) = s b • qs.ket b)
    (hs : ∀ b, s (flipBit q b) = s b) : CommXL qs L q :=
  commXL_of_ket fun b => by rw [hL, hs, hL, LowerGateClass.evalL_smul, evalL_X_ket_flipBit]

theorem commXL_of_id {L : LowGate} {q : ℕ} (hL : ∀ ψ, LowerGateClass.evalL (qs := qs) L ψ = ψ) :
    CommXL qs L q := fun ψ => by rw [hL, hL]

theorem commXL_seq {U V : LowGate} {q : ℕ} (hU : CommXL qs U q) (hV : CommXL qs V q) :
    CommXL qs (U ;; V) q := fun ψ => by
  simp only [LowerGateClass.evalL_seq]
  rw [hU, hV]

/-- **B2: every low gate is invertible, from the existing laws alone.** `evalL_adj_apply`
holds for `adj L` too, so `evalL (adj L)` is injective; as it undoes `evalL L`, `evalL L`
undoes it on EVERY state. -/
theorem evalL_apply_adj (L : LowGate) (ψ : qs.State) :
    LowerGateClass.evalL L (LowerGateClass.evalL (LowGate.adj L) ψ) = ψ := by
  have hinj : Function.Injective (LowerGateClass.evalL (qs := qs) (LowGate.adj L)) :=
    fun a b h => by
      have := congrArg (LowerGateClass.evalL (qs := qs) (LowGate.adj (LowGate.adj L))) h
      rwa [LowerGateClass.evalL_adj_apply, LowerGateClass.evalL_adj_apply] at this
  exact hinj (LowerGateClass.evalL_adj_apply L _)

/-- **B2: adjoints commute when the gate does.** No domain condition, no new law. -/
theorem commXL_adj {L : LowGate} {q : ℕ} (hL : CommXL qs L q) : CommXL qs (LowGate.adj L) q :=
  fun ψ => by
    have h1 := evalL_apply_adj (qs := qs) L ψ
    conv_lhs => rw [← h1]
    rw [← hL, LowerGateClass.evalL_adj_apply]

theorem commXL_H {p q : ℕ} (h : q ≠ p) : CommXL qs (LowGate.H p) q := commXL_of_ket fun b => by
  rw [LowerGateClass.evalL_H_ket, LowerGateClass.evalL_H_ket, bit_flipBit_ne (Ne.symm h),
    writeNat_flipBit (not_mem_qubitReg.mpr h), writeNat_flipBit (not_mem_qubitReg.mpr h),
    ← evalL_X_ket_flipBit, ← evalL_X_ket_flipBit, LowerGateClass.evalL_smul,
    LowerGateClass.evalL_add, LowerGateClass.evalL_smul]

theorem commXL_Phase {p q : ℕ} (h : q ≠ p) (θ : Angle) : CommXL qs (LowGate.Phase p θ) q :=
  commXL_of_diag _ (evalL_Phase_ket_diag p θ) fun b => by rw [bit_flipBit_ne (Ne.symm h)]

/-- **B1 + B2: per-gate locality of the low-level language, all states.** For EVERY low-level
gate `g` (adjoint nodes included) and every qubit `q` outside its footprint,
`evalL g (evalL (X q) ψ) = evalL (X q) (evalL g ψ)` for every state `ψ`. Only the
`LowerGateClass` laws are used. -/
theorem lowGate_commX (g : LowGate) {q : ℕ} (hq : q ∉ g.lowFootprint) : CommXL qs g q := by
  induction g with
  | id => exact commXL_of_id LowerGateClass.evalL_id
  | seq U V ihU ihV =>
    simp only [LowGate.lowFootprint, Finset.mem_union, not_or] at hq
    exact commXL_seq (ihU hq.1) (ihV hq.2)
  | adj U ih => exact commXL_adj (ih hq)
  | H p => exact commXL_H (by simpa [LowGate.lowFootprint] using hq)
  | X p => exact commXL_of_basis (flipBit p) (evalL_X_ket_flipBit p) (fun b => flipBit_comm p q b)
  | Phase p θ => exact commXL_Phase (by simpa [LowGate.lowFootprint] using hq) θ
  | CNOT a t =>
    simp only [LowGate.lowFootprint, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    exact commXL_of_basis _ (LowerGateClass.evalL_CNOT_ket a t) (cnotBasis_flipBit hq.1 hq.2)
  | Toffoli a a' t =>
    simp only [LowGate.lowFootprint, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    exact commXL_of_basis _ (LowerGateClass.evalL_Toffoli_ket a a' t)
      (toffoliBasis_flipBit hq.1 hq.2.1 hq.2.2)
  | ShiftL r n =>
    simp only [LowGate.lowFootprint, extRegActiveQubits, List.mem_toFinset] at hq
    exact commXL_of_basis _ (LowerGateClass.evalL_shiftL_ket_total r n) (shiftLBasis_flipBit hq)
  | ShiftR r n =>
    simp only [LowGate.lowFootprint, extRegActiveQubits, List.mem_toFinset] at hq
    exact commXL_of_basis _ (LowerGateClass.evalL_shiftR_ket_total r n) (shiftRBasis_flipBit hq)
  | Negate r =>
    simp only [LowGate.lowFootprint, extRegActiveQubits, List.mem_toFinset] at hq
    exact commXL_of_basis _ (LowerGateClass.evalL_negate_ket_total r) (negateBasis_flipBit hq)
  | AddScaled d s ng sh =>
    simp only [LowGate.lowFootprint, extRegActiveQubits, Finset.mem_union, List.mem_toFinset,
      not_or] at hq
    exact commXL_of_basis _ (LowerGateClass.evalL_addScaled_ket_total d s ng sh)
      (addScaledBasis_flipBit hq.1 hq.2)
  | zeroExtend r n => exact commXL_of_id (LowerGateClass.evalL_zeroExtend_id r n)
  | signExtend r n =>
    obtain ⟨ha, hn⟩ := not_mem_grow hq
    exact commXL_of_basis _ (LowerGateClass.evalL_signExtend_ket_total r n)
      (signExtendBasis_flipBit_grow ha hn)
  | zeroDealloc r n => exact commXL_of_id (LowerGateClass.evalL_zeroDealloc_id r n)
  | signDealloc r n =>
    obtain ⟨ha, hn⟩ := not_mem_grow hq
    exact commXL_of_basis _ (LowerGateClass.evalL_signDealloc_ket_total r n)
      (signExtendBasis_flipBit_grow ha hn)
  | RadixReverse r m =>
    simp only [LowGate.lowFootprint, List.mem_toFinset] at hq
    exact commXL_of_basis _ (LowerGateClass.evalL_radixReverse_ket_total r m)
      (radixReverseBasis_flipBit hq)

end Gates

/-! ## The Z projectors of an unnamed qubit -/

section GatesP
variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs] [MeasureClass qs]

/-- `evalL L` commutes with the Born projector `measProj (qubitReg q) o` on every state. -/
def CommPL (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs] [MeasureClass qs]
    (L : LowGate) (q o : ℕ) : Prop :=
  ∀ ψ : qs.State, LowerGateClass.evalL L (measProj (qubitReg q) o ψ)
    = measProj (qubitReg q) o (LowerGateClass.evalL L ψ)

theorem commPL_of_ket {L : LowGate} {q o : ℕ}
    (h : ∀ b, measProj (qubitReg q) o (LowerGateClass.evalL L (qs.ket b))
      = if (if RegEncoding.bit q b then 1 else 0) = o then LowerGateClass.evalL L (qs.ket b)
        else 0) :
    CommPL qs L q o := by
  intro ψ
  have := linearMap_ext_ket ((lowL L).comp (measProj (qubitReg q) o).toLinearMap)
    ((measProj (qubitReg q) o).toLinearMap.comp (lowL L)) (fun b => by
      simp only [LinearMap.comp_apply, lowL_apply, ContinuousLinearMap.coe_coe]
      rw [h b, measProj_qubitReg_ket]
      split_ifs <;> simp) ψ
  simpa using this

theorem commPL_of_basis {L : LowGate} {q o : ℕ} (f : qs.Basis → qs.Basis)
    (hL : ∀ b, LowerGateClass.evalL L (qs.ket b) = qs.ket (f b))
    (hf : ∀ b, RegEncoding.bit q (f b) = RegEncoding.bit q b) : CommPL qs L q o :=
  commPL_of_ket fun b => by rw [hL, measProj_ket_keep (hf b)]

theorem commPL_of_diag {L : LowGate} {q o : ℕ} (s : qs.Basis → ℂ)
    (hL : ∀ b, LowerGateClass.evalL L (qs.ket b) = s b • qs.ket b) : CommPL qs L q o :=
  commPL_of_ket fun b => by
    rw [hL, map_smul, measProj_qubitReg_ket]
    split_ifs <;> simp

theorem commPL_of_id {L : LowGate} {q o : ℕ}
    (hL : ∀ ψ, LowerGateClass.evalL (qs := qs) L ψ = ψ) : CommPL qs L q o := fun ψ => by
  rw [hL, hL]

theorem commPL_seq {U V : LowGate} {q o : ℕ} (hU : CommPL qs U q o) (hV : CommPL qs V q o) :
    CommPL qs (U ;; V) q o := fun ψ => by
  simp only [LowerGateClass.evalL_seq]
  rw [hU, hV]

theorem commPL_adj {L : LowGate} {q o : ℕ} (hL : CommPL qs L q o) :
    CommPL qs (LowGate.adj L) q o := fun ψ => by
  have h1 := evalL_apply_adj (qs := qs) L ψ
  conv_lhs => rw [← h1]
  rw [← hL, LowerGateClass.evalL_adj_apply]

theorem commPL_H {p q o : ℕ} (h : q ≠ p) : CommPL qs (LowGate.H p) q o := commPL_of_ket fun b => by
  have hw : ∀ v, RegEncoding.bit q (RegEncoding.writeNat (qubitReg p) v b) = RegEncoding.bit q b :=
    fun v => RegEncoding.bit_writeNat_out _ _ _ _ (not_mem_qubitReg.mpr h)
  rw [LowerGateClass.evalL_H_ket, map_smul, map_add, map_smul, measProj_ket_keep (hw 0),
    measProj_ket_keep (hw 1)]
  split_ifs <;> simp

/-- **Per-gate spectator law of the low-level language, all states.** For EVERY low-level
gate `g` (adjoints included) and every qubit `q` outside its footprint, `evalL g` commutes
with the Born projectors `measProj (qubitReg q) o`. -/
theorem lowGate_commProj (g : LowGate) {q : ℕ} (hq : q ∉ g.lowFootprint) (o : ℕ) :
    CommPL qs g q o := by
  induction g with
  | id => exact commPL_of_id LowerGateClass.evalL_id
  | seq U V ihU ihV =>
    simp only [LowGate.lowFootprint, Finset.mem_union, not_or] at hq
    exact commPL_seq (ihU hq.1) (ihV hq.2)
  | adj U ih => exact commPL_adj (ih hq)
  | H p => exact commPL_H (by simpa [LowGate.lowFootprint] using hq)
  | X p =>
    exact commPL_of_basis (flipBit p) (evalL_X_ket_flipBit p)
      (bit_flipBit_ne (by simpa [LowGate.lowFootprint] using hq))
  | Phase p θ => exact commPL_of_diag _ (evalL_Phase_ket_diag p θ)
  | CNOT a t =>
    simp only [LowGate.lowFootprint, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    exact commPL_of_basis _ (LowerGateClass.evalL_CNOT_ket a t) (bit_cnotBasis_of_ne hq.2)
  | Toffoli a a' t =>
    simp only [LowGate.lowFootprint, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    exact commPL_of_basis _ (LowerGateClass.evalL_Toffoli_ket a a' t)
      (bit_toffoliBasis_of_ne hq.2.2)
  | ShiftL r n =>
    simp only [LowGate.lowFootprint, extRegActiveQubits, List.mem_toFinset] at hq
    exact commPL_of_basis _ (LowerGateClass.evalL_shiftL_ket_total r n)
      (bit_shiftLBasis_of_not_mem hq)
  | ShiftR r n =>
    simp only [LowGate.lowFootprint, extRegActiveQubits, List.mem_toFinset] at hq
    exact commPL_of_basis _ (LowerGateClass.evalL_shiftR_ket_total r n)
      (bit_shiftRBasis_of_not_mem hq)
  | Negate r =>
    simp only [LowGate.lowFootprint, extRegActiveQubits, List.mem_toFinset] at hq
    exact commPL_of_basis _ (LowerGateClass.evalL_negate_ket_total r)
      (bit_negateBasis_of_not_mem hq)
  | AddScaled d s ng sh =>
    simp only [LowGate.lowFootprint, extRegActiveQubits, Finset.mem_union, List.mem_toFinset,
      not_or] at hq
    exact commPL_of_basis _ (LowerGateClass.evalL_addScaled_ket_total d s ng sh)
      (bit_addScaledBasis_of_not_mem hq.1)
  | zeroExtend r n => exact commPL_of_id (LowerGateClass.evalL_zeroExtend_id r n)
  | signExtend r n =>
    exact commPL_of_basis _ (LowerGateClass.evalL_signExtend_ket_total r n)
      (bit_signExtendBasis_of_not_mem_newBits (not_mem_grow hq).2)
  | zeroDealloc r n => exact commPL_of_id (LowerGateClass.evalL_zeroDealloc_id r n)
  | signDealloc r n =>
    exact commPL_of_basis _ (LowerGateClass.evalL_signDealloc_ket_total r n)
      (bit_signExtendBasis_of_not_mem_newBits (not_mem_grow hq).2)
  | RadixReverse r m =>
    simp only [LowGate.lowFootprint, List.mem_toFinset] at hq
    exact commPL_of_basis _ (LowerGateClass.evalL_radixReverse_ket_total r m)
      (bit_radixReverseBasis_of_not_mem hq)

end GatesP

/-! ## B3: the lowered measurement language -/

/-- The low-level support of a lowered measurement-language program: the footprints of its
unitary parts, and the qubit of every `measureReset` and `ffPhase`. -/
def _root_.Shor.MLowGate.lowSupport : MLowGate → Finset ℕ
  | .unitary g => g.lowFootprint
  | .seq a b => a.lowSupport ∪ b.lowSupport
  | .measureReset q => {q}
  | .ffPhase q _ => {q}

section MLow
variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs] [MeasureClass qs]

/-- The Born projectors of `qubitReg p` commute with the low-level `X q`, `q ≠ p`. -/
theorem measProj_commXL {p q : ℕ} (h : q ≠ p) (o : ℕ) (ψ : qs.State) :
    measProj (qubitReg p) o (LowerGateClass.evalL (LowGate.X q) ψ)
      = LowerGateClass.evalL (LowGate.X q) (measProj (qubitReg p) o ψ) := by
  have := linearMap_ext_ket ((measProj (qubitReg p) o).toLinearMap.comp (lowL (LowGate.X q)))
    ((lowL (LowGate.X q)).comp (measProj (qubitReg p) o).toLinearMap) (fun b => by
      simp only [LinearMap.comp_apply, lowL_apply, ContinuousLinearMap.coe_coe]
      rw [evalL_X_ket_flipBit, MeasureClass.measProj_ket, MeasureClass.measProj_ket,
        toNat_flipBit (not_mem_qubitReg.mpr h)]
      split_ifs
      · rw [evalL_X_ket_flipBit]
      · rw [MGate.lowGate_evalL_zero_state]) ψ
  simpa using this

theorem measureResetBranchL_commX {p q : ℕ} (h : q ≠ p) (c : Bool) (ψ : qs.State) :
    measureResetBranchL p c (LowerGateClass.evalL (LowGate.X q) ψ)
      = LowerGateClass.evalL (LowGate.X q) (measureResetBranchL p c ψ) := by
  cases c
  · exact measProj_commXL h 0 ψ
  · simp only [measureResetBranchL, ite_true]
    rw [measProj_commXL h 1 ψ]
    exact lowGate_commX (LowGate.X p) (by simpa [LowGate.lowFootprint] using h) _

theorem measureResetBranchL_commProj {p q : ℕ} (h : q ≠ p) (o : ℕ) (c : Bool) (ψ : qs.State) :
    measureResetBranchL p c (measProj (qubitReg q) o ψ)
      = measProj (qubitReg q) o (measureResetBranchL p c ψ) := by
  cases c
  · exact measProj_commProj p q o 0 ψ
  · simp only [measureResetBranchL, ite_true]
    rw [measProj_commProj p q o 1 ψ]
    exact lowGate_commProj (LowGate.X p) (by simpa [LowGate.lowFootprint] using h) o _

/-- **B3: locality of `MLowGate` programs, branch by branch.** If `q ∉ P.lowSupport`, running
`P` on the branchwise `X q ψ` gives `X q` of the run on `ψ`, branch by branch. No hypothesis
on the program (adjoints, any low gate) or on the state. -/
theorem MLowGate.eval_commX (P : MLowGate) {q : ℕ} (hq : q ∉ P.lowSupport) (ψ : MState qs) :
    P.eval (fun r => LowerGateClass.evalL (LowGate.X q) (ψ r))
      = fun r => LowerGateClass.evalL (LowGate.X q) (P.eval ψ r) := by
  induction P generalizing ψ with
  | unitary g =>
    funext r
    exact lowGate_commX g hq (ψ r)
  | seq a b iha ihb =>
    simp only [MLowGate.lowSupport, Finset.mem_union, not_or] at hq
    simp only [MLowGate.eval]
    rw [iha hq.1, ihb hq.2]
  | measureReset p =>
    have hp : q ≠ p := by simpa [MLowGate.lowSupport] using hq
    funext r
    simp only [MLowGate.eval]
    split
    · rw [MGate.lowGate_evalL_zero_state]
    · exact measureResetBranchL_commX hp _ _
  | ffPhase p j =>
    have hp : q ≠ p := by simpa [MLowGate.lowSupport] using hq
    funext r
    exact commXL_Phase hp _ (ψ r)

/-- **B3: spectator law of `MLowGate` programs, branch by branch.** -/
theorem MLowGate.eval_commProj (P : MLowGate) {q : ℕ} (hq : q ∉ P.lowSupport) (o : ℕ)
    (ψ : MState qs) :
    P.eval (fun r => measProj (qubitReg q) o (ψ r))
      = fun r => measProj (qubitReg q) o (P.eval ψ r) := by
  induction P generalizing ψ with
  | unitary g =>
    funext r
    exact lowGate_commProj g hq o (ψ r)
  | seq a b iha ihb =>
    simp only [MLowGate.lowSupport, Finset.mem_union, not_or] at hq
    simp only [MLowGate.eval]
    rw [iha hq.1, ihb hq.2]
  | measureReset p =>
    have hp : q ≠ p := by simpa [MLowGate.lowSupport] using hq
    funext r
    simp only [MLowGate.eval]
    split
    · simp
    · exact measureResetBranchL_commProj hp o _ _
  | ffPhase p j =>
    funext r
    exact commPL_of_diag _ (evalL_Phase_ket_diag p _) (ψ r)

/-! ### Norm of the low-level `X` -/

omit [MeasureClass qs] in
/-- The low-level `X q` preserves inner products (it permutes the orthonormal kets). Derived
from the `LowerGateClass` laws and ket orthonormality; no extra assumption. -/
theorem inner_evalL_X (q : ℕ) (ψ φ : qs.State) :
    inner ℂ (LowerGateClass.evalL (LowGate.X q) ψ) (LowerGateClass.evalL (LowGate.X q) φ)
      = inner ℂ ψ φ := by
  have hket : ∀ b φ, inner ℂ (LowerGateClass.evalL (LowGate.X q) (qs.ket b))
      (LowerGateClass.evalL (LowGate.X q) φ) = inner ℂ (qs.ket b) φ := by
    intro b φ
    refine qs.state_induction (fun φ => inner ℂ (LowerGateClass.evalL (LowGate.X q) (qs.ket b))
      (LowerGateClass.evalL (LowGate.X q) φ) = inner ℂ (qs.ket b) φ) ?_ ?_ ?_ ?_ φ
    · simp
    · intro ψ φ hψ hφ
      rw [LowerGateClass.evalL_add, inner_add_right, inner_add_right, hψ, hφ]
    · intro a ψ hψ
      rw [LowerGateClass.evalL_smul, inner_smul_right, inner_smul_right, hψ]
    · intro b'
      rw [evalL_X_ket_flipBit, evalL_X_ket_flipBit]
      by_cases hb : b = b'
      · subst hb
        rw [qs.ket_inner_eq_of_eq rfl, qs.ket_inner_eq_of_eq rfl]
      · have hb2 : flipBit q b ≠ flipBit q b' := fun h => hb (by
          have := congrArg (flipBit q) h
          rwa [flipBit_flipBit, flipBit_flipBit] at this)
        rw [qs.ket_inner_eq_zero_of_ne hb, qs.ket_inner_eq_zero_of_ne hb2]
  refine qs.state_induction (fun ψ => ∀ φ, inner ℂ (LowerGateClass.evalL (LowGate.X q) ψ)
    (LowerGateClass.evalL (LowGate.X q) φ) = inner ℂ ψ φ) ?_ ?_ ?_ ?_ ψ φ
  · intro φ; simp
  · intro ψ ψ' hψ hψ' φ
    rw [LowerGateClass.evalL_add, inner_add_left, inner_add_left, hψ, hψ']
  · intro a ψ hψ φ
    rw [LowerGateClass.evalL_smul, inner_smul_left, inner_smul_left, hψ]
  · exact hket

omit [MeasureClass qs] in
theorem norm_evalL_X (q : ℕ) (φ : qs.State) :
    ‖LowerGateClass.evalL (LowGate.X q) φ‖ = ‖φ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (LowerGateClass.evalL (LowGate.X q) φ),
    norm_eq_sqrt_re_inner (𝕜 := ℂ) φ, inner_evalL_X]

/-! ### Corollaries for a start state -/

omit [MeasureClass qs] in
theorem MState.init_XL (q : ℕ) (ψ₀ : qs.State) :
    MState.init (LowerGateClass.evalL (LowGate.X q) ψ₀)
      = fun r => LowerGateClass.evalL (LowGate.X q) (MState.init ψ₀ r) := by
  funext r
  unfold MState.init
  split
  · rfl
  · rw [MGate.lowGate_evalL_zero_state]

/-- Flipping an unnamed qubit of the start state flips it in every branch. -/
theorem MLowGate.eval_init_X (P : MLowGate) {q : ℕ} (hq : q ∉ P.lowSupport) (ψ₀ : qs.State)
    (r : Record) :
    P.eval (MState.init (LowerGateClass.evalL (LowGate.X q) ψ₀)) r
      = LowerGateClass.evalL (LowGate.X q) (P.eval (MState.init ψ₀) r) := by
  rw [MState.init_XL, MLowGate.eval_commX P hq]

/-- **B3 (i): the record distribution of a lowered program does not see a qubit outside its
low support.** For EVERY start state `ψ₀` and record `r`, applying the low-level `X q`,
`q ∉ P.lowSupport`, to the start state does not change the probability of `r`. -/
theorem MLowGate.recordProb_init_X (P : MLowGate) {q : ℕ} (hq : q ∉ P.lowSupport)
    (ψ₀ : qs.State) (r : Record) :
    recordProb (P.eval (MState.init (LowerGateClass.evalL (LowGate.X q) ψ₀))) r
      = recordProb (P.eval (MState.init ψ₀)) r := by
  rw [recordProb, recordProb, MLowGate.eval_init_X P hq, norm_evalL_X]

theorem MLowGate.recordProb_flipBit (P : MLowGate) {q : ℕ} (hq : q ∉ P.lowSupport)
    (b : qs.Basis) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket (flipBit q b)))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  rw [← evalL_X_ket_flipBit]
  exact MLowGate.recordProb_init_X P hq _ r

theorem MLowGate.recordProb_flipBits (P : MLowGate) (l : List ℕ)
    (hl : ∀ q ∈ l, q ∉ P.lowSupport) (b : qs.Basis) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket (flipBits l b)))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [flipBits_cons, MLowGate.recordProb_flipBit P (hl q (List.mem_cons_self ..)),
      ih fun q' h => hl q' (List.mem_cons_of_mem _ h)]

/-- **B3 (i), agreement form.** Two start kets that agree on every qubit of `P.lowSupport`
and differ at only finitely many qubits give every record the same probability. -/
theorem MLowGate.recordProb_of_agree (P : MLowGate) (b b' : qs.Basis)
    (hagree : ∀ p ∈ P.lowSupport, RegEncoding.bit p b' = RegEncoding.bit p b)
    (hfin : {p | RegEncoding.bit p b' ≠ RegEncoding.bit p b}.Finite) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket b'))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  conv_lhs => rw [eq_flipBits_of_finite b b' hfin]
  refine MLowGate.recordProb_flipBits P _ (fun q hq hS => ?_) b r
  simp only [Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hq
  exact hq (hagree q hS)

theorem MLowGate.eval_init_proj (P : MLowGate) {q : ℕ} (hq : q ∉ P.lowSupport) (o : ℕ)
    (ψ₀ : qs.State) (r : Record) :
    P.eval (MState.init (measProj (qubitReg q) o ψ₀)) r
      = measProj (qubitReg q) o (P.eval (MState.init ψ₀) r) := by
  rw [MState.init_proj, MLowGate.eval_commProj P hq]

/-- **B3 (i), decomposition.** For ANY start state, the record probabilities of a lowered
program are the sums of those of the two Z-projections of the start state on a qubit outside
its low support. -/
theorem MLowGate.recordProb_decomp (P : MLowGate) {q : ℕ} (hq : q ∉ P.lowSupport)
    (ψ₀ : qs.State) (r : Record) :
    recordProb (P.eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2,
          recordProb (P.eval (MState.init (measProj (qubitReg q) o ψ₀))) r := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, recordProb,
    MLowGate.eval_init_proj P hq]
  exact (probMeas_qubitReg_zero_add_one q _).symm

theorem MLowGate.recordProb_init_smul (P : MLowGate) (a : ℂ) (ψ₀ : qs.State) (r : Record) :
    recordProb (P.eval (MState.init (a • ψ₀))) r
      = ‖a‖ ^ 2 * recordProb (P.eval (MState.init ψ₀)) r := by
  rw [recordProb, recordProb, MState.init_smul, MLowGate.eval_smul, Pi.smul_apply, norm_smul,
    mul_pow]

private theorem recordProb_superpose_of_falseL (P : MLowGate) {q : ℕ} (hq : q ∉ P.lowSupport)
    (b : qs.Basis) (hb : RegEncoding.bit q b = false) (α β : ℂ) (r : Record) :
    recordProb (P.eval (MState.init (α • qs.ket b + β • qs.ket (flipBit q b)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb (P.eval (MState.init (qs.ket b))) r := by
  have h0 : measProj (qubitReg q) 0 (α • qs.ket b + β • qs.ket (flipBit q b)) = α • qs.ket b := by
    simp [map_add, map_smul, measProj_qubitReg_ket, bit_flipBit_self, hb]
  have h1 : measProj (qubitReg q) 1 (α • qs.ket b + β • qs.ket (flipBit q b))
      = β • qs.ket (flipBit q b) := by
    simp [map_add, map_smul, measProj_qubitReg_ket, bit_flipBit_self, hb]
  rw [MLowGate.recordProb_decomp P hq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [show ((0 : ℕ) : ℕ) = 0 from rfl, h0, h1, MLowGate.recordProb_init_smul,
    MLowGate.recordProb_init_smul, MLowGate.recordProb_flipBit P hq]
  ring

/-- **B3 (i), superposed spectator.** For ANY basis state `b`, ANY `α β : ℂ` and every record:
from `α|b⟩ + β|flipBit q b⟩`, `q ∉ P.lowSupport`, the record has `(‖α‖² + ‖β‖²)` times its
probability from `|b⟩`. -/
theorem MLowGate.recordProb_superpose (P : MLowGate) {q : ℕ} (hq : q ∉ P.lowSupport)
    (b : qs.Basis) (α β : ℂ) (r : Record) :
    recordProb (P.eval (MState.init (α • qs.ket b + β • qs.ket (flipBit q b)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb (P.eval (MState.init (qs.ket b))) r := by
  cases hb : RegEncoding.bit q b
  · exact recordProb_superpose_of_falseL P hq b hb α β r
  · set b' := flipBit q b with hb'
    have hb'0 : RegEncoding.bit q b' = false := by rw [hb', bit_flipBit_self, hb]; rfl
    have hbb : b = flipBit q b' := by rw [hb', flipBit_flipBit]
    have e : α • qs.ket b + β • qs.ket b' = β • qs.ket b' + α • qs.ket (flipBit q b') := by
      rw [← hbb, add_comm]
    rw [e, recordProb_superpose_of_falseL P hq b' hb'0 β α r, hbb,
      MLowGate.recordProb_flipBit P hq b' r]
    ring

theorem MLowGate.recordProb_superpose_unit (P : MLowGate) {q : ℕ} (hq : q ∉ P.lowSupport)
    (b : qs.Basis) (α β : ℂ) (hαβ : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) (r : Record) :
    recordProb (P.eval (MState.init (α • qs.ket b + β • qs.ket (flipBit q b)))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  rw [MLowGate.recordProb_superpose P hq b α β r, hαβ, one_mul]

end MLow

end Readout
end Shor
