import ForShor.ShorVerification.Implementation.Readout.Proofs.LocalityExact
import ForShor.ShorVerification.Implementation.Readout.LocalitySpectator
import ForShor.ShorVerification.Implementation.Readout.Proofs.ReferenceLayout

/-!
# Readout: which reserve qubits the real semiclassical circuit uses

`Locality.lean` (T3/T4) counts every OWNED qubit of `y`, `work`, `scratch` as named, reserves
included. With the exact support (`Proofs/LocalityExact.lean`) the real circuit
`orderFindingSemiclassical` (real `CmodMulInPlaceCore`, `initY1`) is seen to read or write,
according to the high-level ket laws, only

  `semiclassicalExactQubits c y work scratch flag` = the control `c`, the ACTIVE qubits of `y`,
  `work`, `scratch`, the FIRST TWO reserve qubits of `y` (`y.newBits 2`), the FIRST reserve
  qubit of `work` and of `scratch` (`newBits 1`), and the flag

(`orderFindingSemiclassical_exactSupport`, no hypothesis beyond the circuit's own `hw`/`hs4`
arguments). Where they come from: `y.newBits 1`
is the carry bit of `y.grow 1` (Steps 2–5); the second reserve qubit of `y` is the phase-product
sign bit of Steps 1, 2, 5 and of the comparator's `(y.grow 1).grow 1`; `work.newBits 1` and
`scratch.newBits 1` are the phase-product sign bits of Steps 1, 2, 4, 5. These ARE in the
exact support (`reserve_used_*`, for `m ≥ 1` rounds): some ket-law formula of the circuit reads
or writes them. This is NOT a proof that flipping them changes a record probability (the exact
support is an upper bound; a formula may over-count, e.g. `CNOT a a`); no such counterexample is
proved here.

Every reserve qubit beyond them, `unusedReserve y work scratch` = `y.reserve` after its first
two qubits, `work.reserve` and `scratch.reserve` after their first one, is not read or written
by the high-level ket laws of the real circuit (`unusedReserve_not_mem_exact`, under the register layout `hw`, `hs4`,
`SemiclassicalLayout`). Hence, for ANY start ket and any finite list of such qubits (or any
qubit outside `semiclassicalExactQubits` at all):

* `orderFindingSemiclassical_recordProb_flipBits_exact`: every record probability is unchanged;
* `orderFindingSemiclassical_recordProb_of_agree_exact`: two kets agreeing on
  `semiclassicalExactQubits`, finitely many differences: same distribution;
* `orderFindingSemiclassical_recordProb_superpose_exact`: one such qubit in any superposition;
* `orderFindingSemiclassical_recordProb_flip_unusedReserve`: the reserve form.

## What is NOT covered

* The LOWERED circuit `orderFindingSemiclassicalLow` with a flipped reserve qubit. Its only
  available semantics, `semiclassical_lowerM_eval`, requires EVERY reserve qubit of `y`, `work`,
  `scratch` to start at `0` (`SemiclassicalWorkspaceCleanInput`: the lowering allocates its
  workspace in those reserves; that is why the layout sizes them by the lowering's need). A
  flipped reserve qubit violates that hypothesis (`cleanInput_fails_flip_reserve`), so nothing
  is claimed there; the hypothesis cannot be "restricted" without a new semantics for the
  lowered program on dirty workspace. Lowered results remain those of T4/T5 (qubits outside
  `semiclassicalQubits`).
* Qubits in `semiclassicalExactQubits`: named in the exact sense; locality can fail for them.
  In particular flipping the control `c` or a data qubit in the start state is NOT covered (and
  changes the record distribution in general, `LocalityTests.measureReset_flip_named`).
* Infinitely many flips: the agreement forms need `hfin` (finitely many differing qubits) and
  the flip forms take finite lists. Harmless for physical kets, which differ in finitely many
  qubits; a restriction of the abstract basis only.
* Programs with ideal nodes (`LocalityIdeal`).
-/

namespace Shor

/-- The qubits the real semiclassical circuit acts on (exact support bound): the control, the
active parts of `y`, `work`, `scratch`, the first two reserve qubits of `y`, the first reserve
qubit of `work` and of `scratch`, and the flag. -/
def semiclassicalExactQubits (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) : Set ℕ :=
  {q | q = c ∨ q ∈ y.active.qubits ∨ q ∈ (y.newBits 2).qubits ∨ q ∈ work.active.qubits ∨
    q ∈ (work.newBits 1).qubits ∨ q ∈ scratch.active.qubits ∨ q ∈ (scratch.newBits 1).qubits ∨
    q = flag}

/-- The reserve qubits no high-level ket law of the real circuit reads or writes: `y.reserve` after its first two
qubits, `work.reserve` and `scratch.reserve` after their first one. -/
def unusedReserve (y work scratch : ExtReg) : Set ℕ :=
  {q | q ∈ (y.reserve.drop 2).qubits ∨ q ∈ (work.reserve.drop 1).qubits ∨
    q ∈ (scratch.reserve.drop 1).qubits}

namespace Readout

theorem mem_take_two_of_take_one {l : List ℕ} {q : ℕ} (h : q ∈ l.take 1) : q ∈ l.take 2 := by
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all

theorem mem_take_two_of_take_one_drop_one {l : List ℕ} {q : ℕ} (h : q ∈ (l.drop 1).take 1) :
    q ∈ l.take 2 := by
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all

/-- `H_reg r` acts only on the qubits of `r`. -/
theorem H_reg_exactSupport (r : Reg) : (H_reg r).exactSupport ⊆ {q | q ∈ r.qubits} := by
  have key : ∀ (l : List ℕ) (acc : Gate),
      (l.foldl (fun acc q => Gate.H q ;; acc) acc).exactSupport ⊆ acc.exactSupport ∪ {q | q ∈ l} := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc q hq
      rcases ih _ hq with h | h
      · simp only [Gate.exactSupport, Set.mem_union, Set.mem_singleton_iff] at h
        rcases h with rfl | h
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
  intro q hq
  rcases key _ _ hq with h | h
  · simp [Gate.exactSupport] at h
  · exact h

/-- `initY1 r` acts on at most one qubit of `r`. -/
theorem initY1_exactSupport (r : Reg) : (initY1 r).exactSupport ⊆ {q | q ∈ r.qubits} := by
  intro q hq
  unfold initY1 at hq
  split at hq
  · simp [Gate.exactSupport] at hq
  · rename_i q0 rest h
    simp only [Gate.exactSupport, Set.mem_singleton_iff] at hq
    show q ∈ r.qubits
    rw [h, hq]
    exact List.mem_cons_self ..

section Static
variable {c flag : ℕ} {y work scratch : ExtReg}

/-- **Exact support of the real multiplier.** -/
theorem cmodMul_exactSupport (cm N : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    (CmodMulInPlaceCore cm N c y work scratch flag hw hs4).exactSupport
      ⊆ semiclassicalExactQubits c y work scratch flag := by
  have hzR : hs4.mulWorkspace.zReserve = scratch.reserve := hs4.mul_zReserve_eq
  have hxR : hs4.mulWorkspace.xReserve = work.reserve := hs4.mul_xReserve_eq
  intro q hq
  simp only [CmodMulInPlaceCore, step1, step2, step3, step4, step5, cmpLtNW, fastConstMulInto,
    cmpLtNWDifference, IQFT, Gate.PhaseProdUsing, Gate.CPhaseProdUsing, Gate.exactSupport,
    Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_insert_iff,
    Set.mem_empty_iff_false, false_or, or_false] at hq
  simp only [ModMulCircuitWorkspaceOK.step1Workspace, ModMulCircuitWorkspaceOK.step2Workspace,
    ModMulCircuitWorkspaceOK.step5Workspace, Gate.PhaseProdWorkspace.xExt,
    Gate.PhaseProdWorkspace.zExt, Gate.PhaseProdWorkspace.ofExtRegs,
    ExtReg.newBits, ExtReg.grow, ExtReg.remainingReserve,
    Reg.take, Reg.drop, Reg.append, ExtReg.withReserve_active, ExtReg.withReserve_reserve,
    hzR, hxR, List.mem_append] at hq
  simp only [semiclassicalExactQubits, ExtReg.newBits, Reg.take, Set.mem_ofPred_eq]
  by_contra hS
  simp only [not_or] at hS
  obtain ⟨nc, nYa, nY2, nWa, nW1, nSa, nS1, nf⟩ := hS
  have nY1 : q ∉ List.take 1 y.reserve.qubits := fun h => nY2 (mem_take_two_of_take_one h)
  have nY11 : q ∉ List.take 1 (List.drop 1 y.reserve.qubits) := fun h =>
    nY2 (mem_take_two_of_take_one_drop_one h)
  have nH : q ∉ (H_reg work.active).exactSupport := fun h => nWa (H_reg_exactSupport _ h)
  have nSg : ∀ h, q ≠ cmpLtNWSignQubit scratch h := fun h e =>
    nSa (e ▸ List.get_mem _ _)
  simp [nc, nYa, nY1, nWa, nW1, nSa, nS1, nf, nH, nSg] at hq
  exact nY11 (by simpa using hq)

/-- **Exact support of the real semiclassical circuit** (any `m`, no hypothesis beyond the
circuit's own `hw`/`hs4`). -/
theorem orderFindingSemiclassical_exactSupport (a N m : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    (orderFindingSemiclassical a N c m y work scratch flag hw hs4).exactSupport
      ⊆ semiclassicalExactQubits c y work scratch flag := by
  have hc : c ∈ semiclassicalExactQubits c y work scratch flag := Or.inl rfl
  have hrounds : ∀ k, (readoutRounds (semiclassicalMultipliers a N c m y work scratch flag hw hs4)
      c k).exactSupport ⊆ semiclassicalExactQubits c y work scratch flag := by
    intro k
    induction k with
    | zero => simp [readoutRounds, MGate.exactSupport, Gate.exactSupport]
    | succ k ih =>
      simp only [readoutRounds, MGate.exactSupport, Gate.exactSupport, Set.union_subset_iff,
        Set.singleton_subset_iff]
      exact ⟨ih, hc, cmodMul_exactSupport _ N hw hs4, hc, hc, hc⟩
  simp only [orderFindingSemiclassical, MGate.exactSupport, Set.union_subset_iff]
  exact ⟨fun q h => Or.inr (Or.inl (initY1_exactSupport _ h)), hrounds m⟩

/-- **Unused reserve qubits are outside the exact support.** Under the register layout of the
circuit (`hw`, `hs4`, `SemiclassicalLayout`). -/
theorem unusedReserve_not_mem_exact (N : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hl : SemiclassicalLayout c y work scratch flag) {q : ℕ}
    (hq : q ∈ unusedReserve y work scratch) :
    q ∉ semiclassicalExactQubits c y work scratch flag := by
  have hyw : ExtReg.OwnedDisjoint y work := hw.2.2
  have hys : ExtReg.OwnedDisjoint y scratch := by
    have h := hs4.data_scratch_disjoint
    unfold ExtReg.OwnedDisjoint at h ⊢
    rwa [Gate.ExtReg.ownedQubits_grow] at h
  have hws : ExtReg.OwnedDisjoint work scratch := hs4.work_scratch_disjoint
  have hfy : flag ∉ y.ownedQubits := by
    have h := hs4.flag_not_data; rwa [Gate.ExtReg.ownedQubits_grow] at h
  have tk : ∀ (e : ExtReg) (n : ℕ) {p : ℕ}, p ∈ (e.newBits n).qubits → p ∈ e.ownedQubits :=
    fun e n p h => mem_owned_of_newBits h
  have ac : ∀ (e : ExtReg) {p : ℕ}, p ∈ e.active.qubits → p ∈ e.ownedQubits :=
    fun e p h => mem_owned_of_active h
  -- `q` lies in the reserve of one register, beyond its first `n` qubits
  have key : ∀ (e : ExtReg) (n : ℕ), q ∈ (e.reserve.drop n).qubits →
      q ∈ e.ownedQubits ∧ q ∉ e.active.qubits ∧ q ∉ (e.newBits n).qubits := by
    intro e n h
    have hr : q ∈ e.reserve.qubits := List.mem_of_mem_drop h
    refine ⟨List.mem_append_right _ hr, fun ha => e.active_reserve_disjoint ha hr, fun ht => ?_⟩
    exact List.disjoint_take_drop e.reserve.nodup (le_refl n) ht h
  rintro (h | h | h | h | h | h | h | h)
  · subst h
    rcases hq with hq | hq | hq
    · exact hl.c_not_mem_data (key y 2 hq).1
    · exact hl.c_not_mem_work (key work 1 hq).1
    · exact hl.c_not_mem_scratch (key scratch 1 hq).1
  · rcases hq with hq | hq | hq
    · exact (key y 2 hq).2.1 h
    · exact hyw (ac y h) (key work 1 hq).1
    · exact hys (ac y h) (key scratch 1 hq).1
  · rcases hq with hq | hq | hq
    · exact (key y 2 hq).2.2 h
    · exact hyw (tk y 2 h) (key work 1 hq).1
    · exact hys (tk y 2 h) (key scratch 1 hq).1
  · rcases hq with hq | hq | hq
    · exact hyw (key y 2 hq).1 (ac work h)
    · exact (key work 1 hq).2.1 h
    · exact hws (ac work h) (key scratch 1 hq).1
  · rcases hq with hq | hq | hq
    · exact hyw (key y 2 hq).1 (tk work 1 h)
    · exact (key work 1 hq).2.2 h
    · exact hws (tk work 1 h) (key scratch 1 hq).1
  · rcases hq with hq | hq | hq
    · exact hys (key y 2 hq).1 (ac scratch h)
    · exact hws (key work 1 hq).1 (ac scratch h)
    · exact (key scratch 1 hq).2.1 h
  · rcases hq with hq | hq | hq
    · exact hys (key y 2 hq).1 (tk scratch 1 h)
    · exact hws (key work 1 hq).1 (tk scratch 1 h)
    · exact (key scratch 1 hq).2.2 h
  · subst h
    rcases hq with hq | hq | hq
    · exact hfy (key y 2 hq).1
    · exact hs4.flag_not_work (key work 1 hq).1
    · exact hs4.flag_not_scratch (key scratch 1 hq).1

theorem mem_take_one_or_tail_of_take_two {l : List ℕ} {q : ℕ} (h : q ∈ l.take 2) :
    q ∈ l.take 1 ∨ q ∈ l.tail.take 1 := by
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all

/-- **The first reserve qubits are in the multiplier's exact support** (a ket-law formula reads
or writes them; this does not by itself show a flip changes an outcome): the first two of `y`, the first of
`work` and of `scratch` are in the exact support of `CmodMulInPlaceCore`. -/
theorem reserve_used_cmodMul (cm N : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) {q : ℕ}
    (hq : q ∈ (y.newBits 2).qubits ∨ q ∈ (work.newBits 1).qubits ∨
      q ∈ (scratch.newBits 1).qubits) :
    q ∈ (CmodMulInPlaceCore cm N c y work scratch flag hw hs4).exactSupport := by
  have hzR : hs4.mulWorkspace.zReserve = scratch.reserve := hs4.mul_zReserve_eq
  have hxR : hs4.mulWorkspace.xReserve = work.reserve := hs4.mul_xReserve_eq
  simp only [CmodMulInPlaceCore, step1, step2, step3, step4, step5, cmpLtNW, fastConstMulInto,
    cmpLtNWDifference, IQFT, Gate.PhaseProdUsing, Gate.CPhaseProdUsing, Gate.exactSupport,
    Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_insert_iff,
    Set.mem_empty_iff_false, false_or, or_false]
  simp only [ModMulCircuitWorkspaceOK.step1Workspace, ModMulCircuitWorkspaceOK.step2Workspace,
    ModMulCircuitWorkspaceOK.step5Workspace, Gate.PhaseProdWorkspace.xExt,
    Gate.PhaseProdWorkspace.zExt, Gate.PhaseProdWorkspace.ofExtRegs,
    ExtReg.newBits, ExtReg.grow, ExtReg.remainingReserve,
    Reg.take, Reg.drop, Reg.append, ExtReg.withReserve_active, ExtReg.withReserve_reserve,
    hzR, hxR, List.mem_append]
  simp only [ExtReg.newBits, Reg.take] at hq
  rcases hq with hq | hq | hq
  · rcases mem_take_one_or_tail_of_take_two hq with h | h
    · simp [h]
    · simp [h]
  · simp [hq]
  · simp [hq]

/-- **The first reserve qubits are in the circuit's exact support** (as soon as there is one
round). Membership only: the exact support is an upper bound (see the module docstring). -/
theorem reserve_used (a N m : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) {q : ℕ}
    (hq : q ∈ (y.newBits 2).qubits ∨ q ∈ (work.newBits 1).qubits ∨
      q ∈ (scratch.newBits 1).qubits) :
    q ∈ (orderFindingSemiclassical a N c (m + 1) y work scratch flag hw hs4).exactSupport := by
  simp only [orderFindingSemiclassical, readoutRounds, MGate.exactSupport, Set.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inl (reserve_used_cmodMul _ N hw hs4 hq))))

/-- A register that starts at `0` no longer does after one of its qubits is flipped. -/
theorem freshZero_flipBit {B : Type*} [RegEncoding B] {r : Reg} {q : ℕ} (hq : q ∈ r.qubits)
    {b : B} (h : FreshZero r b) : ¬ FreshZero r (flipBit q b) := by
  intro h'
  have e1 := _root_.Shor.bit_of_toNat_zero_of_mem r b h hq
  have e2 := _root_.Shor.bit_of_toNat_zero_of_mem r _ h' hq
  rw [bit_flipBit_self, e1] at e2
  exact Bool.noConfusion e2

/-- **Negative: the lowered circuit's clean hypothesis fails after flipping ANY reserve qubit.**
If `b0` satisfies `SemiclassicalWorkspaceCleanInput` (every reserve qubit of `y`, `work`,
`scratch` at `0`, the hypothesis of `semiclassical_lowerM_eval`), then flipping any reserve
qubit, in particular any `unusedReserve` qubit, breaks it. So the lowered-circuit theorems
(T4/T5) cannot be applied to such a flipped ket. -/
theorem cleanInput_fails_flip_reserve {B : Type*} [RegEncoding B] {b0 : B} {q : ℕ}
    (hq : q ∈ y.reserve.qubits ∨ q ∈ work.reserve.qubits ∨ q ∈ scratch.reserve.qubits)
    (h : SemiclassicalWorkspaceCleanInput y work scratch b0) :
    ¬ SemiclassicalWorkspaceCleanInput y work scratch (flipBit q b0) := by
  rintro ⟨h1, h2, h3⟩
  rcases hq with hq | hq | hq
  · exact freshZero_flipBit hq h.1 h1
  · exact freshZero_flipBit hq h.2.1 h2
  · exact freshZero_flipBit hq h.2.2 h3

/-- Every `unusedReserve` qubit is a reserve qubit. -/
theorem unusedReserve_mem_reserve {q : ℕ} (hq : q ∈ unusedReserve y work scratch) :
    q ∈ y.reserve.qubits ∨ q ∈ work.reserve.qubits ∨ q ∈ scratch.reserve.qubits := by
  rcases hq with h | h | h
  · exact Or.inl (List.mem_of_mem_drop h)
  · exact Or.inr (Or.inl (List.mem_of_mem_drop h))
  · exact Or.inr (Or.inr (List.mem_of_mem_drop h))

end Static

/-! ## At the reference layout: there ARE unused reserve qubits, for every policy

The reference layout (`Implementation/Reference/Standard/Statement.lean`) sizes the reserves by
the LOWERING's need: data reserve `max 2 need.data`, work `max 1 need.auxiliary`, scratch
`max 1 need.scratch`. Every one of these needs contains a QFT reserve term
`qftReserveNeedOf need w ≥ 2` (`w ≥ 2`), so for EVERY policy the data reserve has at least
`3` qubits, the work and scratch reserves at least `2`: at least one qubit of each lies beyond
what the real high-level circuit grows into (`reference_unusedReserve_length`). These qubits
exist only for the lowering's workspace. -/

section Reference
open Reference

-- `RL` abbreviates the reference layout `allocateReferenceLayout P inst ℓ`.
set_option hygiene false in
local notation "RL" => allocateReferenceLayout P inst ℓ

/-- The QFT reserve of a width `≥ 2` is at least `2` (one on each side), for any phase-product
reserve model. -/
theorem qftReserveNeedOf_ge_two (res : ℕ → ℕ → ℕ × ℕ) {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ qftReserveNeedOf (qftWorkspaceNeedOf res) n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [qftReserveNeedOf, qftWorkspaceNeedOf]
  dsimp only
  have h1 := le_max_left (1 + (res ((k + 2) / 2 + 1) (k + 2 - (k + 2) / 2 + 1)).1)
    (max (qftWorkspaceNeedOf res ((k + 2) / 2)).1
      (qftWorkspaceNeedOf res (k + 2 - (k + 2) / 2)).1)
  have h2 := le_max_left (1 + (res ((k + 2) / 2 + 1) (k + 2 - (k + 2) / 2 + 1)).2)
    (max (qftWorkspaceNeedOf res ((k + 2) / 2)).2
      (qftWorkspaceNeedOf res (k + 2 - (k + 2) / 2)).2)
  omega

theorem widthShell_width (n : ℕ) : (widthShell n).width = n := regSize_interval 0 n

/-- The reference data width is at least `2` (`N ≥ 2`). -/
theorem referenceDataWidth_ge_two (inst : ShorOrderFindingInstance) :
    2 ≤ referenceDataWidth inst := by
  unfold referenceDataWidth
  rw [Nat.log2_eq_log_two]
  have := inst.range
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

theorem reference_data_need_ge (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : 3 ≤ (referenceWorkspaceNeed P inst ℓ).data := by
  have hq := qftReserveNeedOf_ge_two (Policy.reserveNeed P)
    (n := (widthShell (referenceDataWidth inst)).width + 1)
    (by rw [widthShell_width]; have := referenceDataWidth_ge_two inst; omega)
  unfold referenceWorkspaceNeed shorWorkspaceNeedOf
  dsimp only
  exact le_trans (by unfold Policy.qftWorkspaceNeed; omega) (le_trans (le_max_left _ _)
    (le_max_right _ _))

theorem reference_work_need_ge (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : 2 ≤ (referenceWorkspaceNeed P inst ℓ).auxiliary := by
  have hq := qftReserveNeedOf_ge_two (Policy.reserveNeed P)
    (n := (widthShell (referenceWorkWidth inst ℓ)).width)
    (by rw [widthShell_width]; unfold referenceWorkWidth
        have := referenceDataWidth_ge_two inst; omega)
  unfold referenceWorkspaceNeed shorWorkspaceNeedOf
  dsimp only
  exact le_trans (by unfold Policy.qftWorkspaceNeed; omega) (le_max_left _ _)

theorem reference_scratch_need_ge (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : 2 ≤ (referenceWorkspaceNeed P inst ℓ).scratch := by
  have hq := qftReserveNeedOf_ge_two (Policy.reserveNeed P)
    (n := (widthShell (referenceScratchWidth inst ℓ)).width)
    (by rw [widthShell_width]; unfold referenceScratchWidth; omega)
  unfold referenceWorkspaceNeed shorWorkspaceNeedOf
  dsimp only
  exact le_trans (by unfold Policy.qftWorkspaceNeed; omega) (le_max_left _ _)

/-- **Every policy leaves unused reserve qubits on all three registers.** At the reference
layout, `y.reserve` has at least one qubit after its first two, and `work.reserve`,
`scratch.reserve` at least one after their first: exactly
`referenceDataReserveSize - 2`, `referenceWorkReserveSize - 1`, `referenceScratchReserveSize - 1`
of them. -/
theorem reference_unusedReserve_length (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) :
    ((RL).data.reserve.drop 2).qubits.length = referenceDataReserveSize P inst ℓ - 2 ∧
    ((RL).work.reserve.drop 1).qubits.length = referenceWorkReserveSize P inst ℓ - 1 ∧
    ((RL).scratch.reserve.drop 1).qubits.length = referenceScratchReserveSize P inst ℓ - 1 ∧
    1 ≤ referenceDataReserveSize P inst ℓ - 2 ∧ 1 ≤ referenceWorkReserveSize P inst ℓ - 1 ∧
    1 ≤ referenceScratchReserveSize P inst ℓ - 1 := by
  have hd := reference_data_need_ge P inst ℓ
  have hw := reference_work_need_ge P inst ℓ
  have hs := reference_scratch_need_ge P inst ℓ
  have md := le_max_right 2 (referenceWorkspaceNeed P inst ℓ).data
  have mw := le_max_right 1 (referenceWorkspaceNeed P inst ℓ).auxiliary
  have ms := le_max_right 1 (referenceWorkspaceNeed P inst ℓ).scratch
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [allocateReferenceLayout, referenceData, referenceDataReserve, Reg.drop, Reg.interval]
  · simp [allocateReferenceLayout, referenceWork, referenceWorkReserve, Reg.drop, Reg.interval]
  · simp [allocateReferenceLayout, referenceScratch, referenceScratchReserve, Reg.drop,
      Reg.interval]
  · unfold referenceDataReserveSize; omega
  · unfold referenceWorkReserveSize; omega
  · unfold referenceScratchReserveSize; omega

/-- So the unused-reserve lists are nonempty, for every policy, instance and level. -/
theorem reference_unusedReserve_ne_nil (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) :
    ((RL).data.reserve.drop 2).qubits ≠ [] ∧ ((RL).work.reserve.drop 1).qubits ≠ [] ∧
    ((RL).scratch.reserve.drop 1).qubits ≠ [] := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := reference_unusedReserve_length P inst ℓ
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at h1; simp at h1; omega
  · rw [h] at h2; simp at h2; omega
  · rw [h] at h3; simp at h3; omega

end Reference

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- **Real circuit, finitely many flips outside the exact support.** For ANY registers and ANY
start ket `b0`, and any list `l` of qubits outside `semiclassicalExactQubits`: every record has
the same probability from `|flipBits l b0⟩` as from `|b0⟩`. -/
theorem orderFindingSemiclassical_recordProb_flipBits_exact (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 : qs.Basis) (l : List ℕ)
    (hl : ∀ q ∈ l, q ∉ semiclassicalExactQubits c y work scratch flag) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket (flipBits l b0)))) r
      = recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0))) r :=
  MGate.recordProb_flipBits_exact _ (orderFindingSemiclassical_noIdeal a N c m hw hs4) l
    (fun q hq h => hl q hq (orderFindingSemiclassical_exactSupport a N m hw hs4 h)) b0 r

/-- **Real circuit, agreement form on the exact support.** -/
theorem orderFindingSemiclassical_recordProb_of_agree_exact (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 b0' : qs.Basis)
    (hagree : ∀ p ∈ semiclassicalExactQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (hfin : {p | RegEncoding.bit p b0' ≠ RegEncoding.bit p b0}.Finite) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0'))) r
      = recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0))) r :=
  MGate.recordProb_of_agree_exact _ (orderFindingSemiclassical_noIdeal a N c m hw hs4) b0 b0'
    (fun p hp => hagree p (orderFindingSemiclassical_exactSupport a N m hw hs4 hp)) hfin r

/-- **Real circuit, superposed qubit outside the exact support.** -/
theorem orderFindingSemiclassical_recordProb_superpose_exact (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 : qs.Basis) {q : ℕ}
    (hq : q ∉ semiclassicalExactQubits c y work scratch flag) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassical a N c m y work scratch flag
        hw hs4).eval (MState.init (qs.ket b0))) r :=
  MGate.recordProb_superpose_exact _ (orderFindingSemiclassical_noIdeal a N c m hw hs4)
    (fun h => hq (orderFindingSemiclassical_exactSupport a N m hw hs4 h)) b0 α β r

/-- **Real circuit, unused reserve qubits.** Under the register layout (`hw`, `hs4`,
`SemiclassicalLayout`), for ANY start ket and any list of reserve qubits the circuit never
grows into (`unusedReserve`): every record probability is unchanged. -/
theorem orderFindingSemiclassical_recordProb_flip_unusedReserve (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hl : SemiclassicalLayout c y work scratch flag) (b0 : qs.Basis) (l : List ℕ)
    (hlq : ∀ q ∈ l, q ∈ unusedReserve y work scratch) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket (flipBits l b0)))) r
      = recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0))) r :=
  orderFindingSemiclassical_recordProb_flipBits_exact a N c m y work scratch flag hw hs4 b0 l
    (fun q hq => unusedReserve_not_mem_exact N hw hs4 hl (hlq q hq)) r

end Readout
end Shor
