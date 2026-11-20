import ForShor.ShorVerification.Model.Standard.SemiclassicalLocalityModel
import ForShor.ShorVerification.Implementation.Readout.LocalityReserve
import ForShor.ShorVerification.Implementation.Readout.LocalityIdeal

/-!
# Semiclassical readout in the standard model: unused reserves and the ideal circuit (A1, A2)

Instances at `Model.qs`, the reference layout `allocateReferenceLayout P inst ℓ` and the control
`referenceControl P inst ℓ`, for every policy `P`, instance `inst`, level `ℓ`:

A1 (reserve qubits, real circuit):
* `model_unusedReserve_ne_nil`: for EVERY policy there are unused reserve qubits on the data,
  work and scratch registers (data reserve `≥ 3`, work and scratch reserves `≥ 2`; the real
  circuit's high-level ket laws read or write `2`, `1`, `1` of them);
* `model_reserve_used`: the first two data reserve qubits, and the first work and scratch
  reserve qubits, are in the exact support of the real circuit (one round or more): a ket-law
  formula reads or writes them. Membership only; that flipping them changes a record
  probability is NOT proved (the exact support is an upper bound);
* `model_real_flip_unusedReserve`: ANY start ket, any list of unused reserve qubits: every record
  probability of the real circuit is unchanged;
* `model_real_flip_all_unusedReserve`: concretely, every unused reserve qubit of all three
  registers flipped in `|0…0⟩` (`model_flipBits_dataUnused_ne_zero`: the flipped ket differs
  from `|0…0⟩`);
* `model_real_superpose_unusedReserve`: one unused reserve qubit in any superposition;
* `model_lowered_cleanInput_fails_unusedReserve` (negative): the same flip breaks the lowered
  circuit's clean hypothesis, so no lowered statement is made.

A2 (ideal circuit):
* `model_ideal_flip_zero`: the ideal readout from `|0…0⟩` (data `0`, NOT covered by T1, which
  needs data `= 1`), any list of qubits outside the data register other than the control
  flipped: every record probability unchanged;
* `model_ideal_superpose_exponent_zero`: an exponent qubit other than the control in any
  superposition, from `|0…0⟩`. These two are DEGENERATE witnesses (data `0` is a fixed point of
  every multiplier; exponent qubits are untouched by the ideal readout);
* non-degenerate witnesses: `model_ideal_flip_work_dataTop` (start data `N - 1`, work qubits
  flipped), `model_ideal_flip_work_twoData` (start `α|data 1⟩ + β|data N-1⟩`, a work qubit
  flipped), and `model_ideal_moves_dataTop` (with control `1`, the round-`m-1` multiplier `a`,
  `a ≠ 1`, moves the data-`N-1` ket to a ket with a different data value).

Caveat for every `model_real_*` theorem: it is about the HIGH-LEVEL real circuit. The lowered
circuit's semantics needs every reserve qubit clean (`cleanInput_fails_flip_reserve`,
`model_lowered_cleanInput_fails_unusedReserve`), so no lowered statement is made for reserve
flips. Flipping the control or a data qubit is not covered (and false in general).
-/

namespace Shor
namespace Model

open Reference Readout

set_option hygiene false in
local notation "RL" => allocateReferenceLayout P inst ℓ

/-- Every register is `0` in the all-zero ket. -/
theorem toNat_zero_ket (r : Reg) : RegEncoding.toNat r (RegEncoding.zero (Basis := qs.Basis)) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  by_cases hi : i < regSize r
  · rw [← RegEncoding.bit_eq_testBit_toNat r _ ⟨i, hi⟩, RegEncoding.bit_zero]
  · push Not at hi
    have l1 := RegEncoding.toNat_lt_ASize r (RegEncoding.zero (Basis := qs.Basis))
    rw [ASize] at l1
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le l1 (Nat.pow_le_pow_right (by norm_num) hi))

/-- **For every policy there are unused reserve qubits** on all three registers. -/
theorem model_unusedReserve_ne_nil (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) :
    ((RL).data.reserve.drop 2).qubits ≠ [] ∧ ((RL).work.reserve.drop 1).qubits ≠ [] ∧
    ((RL).scratch.reserve.drop 1).qubits ≠ [] :=
  reference_unusedReserve_ne_nil P inst ℓ

/-- **The grown-into reserve qubits are in the exact support** of the real circuit (one round or
more). Membership only: it is not proved that flipping them changes a record probability. -/
theorem model_reserve_used (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ m : ℕ)
    (q : ℕ) (hq : q ∈ ((RL).data.newBits 2).qubits ∨ q ∈ ((RL).work.newBits 1).qubits ∨
      q ∈ ((RL).scratch.newBits 1).qubits) :
    q ∈ (orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) (m + 1)
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).exactSupport :=
  reserve_used _ _ m _ _ hq

/-- **Real circuit, unused reserve qubits, model.** Any start ket, any list of unused reserve
qubits of the reference layout, any number of rounds: every record probability unchanged. About the high-level circuit only:
the lowered circuit needs every reserve clean (`cleanInput_fails_flip_reserve`), so nothing is
claimed for it. -/
theorem model_real_flip_unusedReserve (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) (b : qs.Basis) (l : List ℕ)
    (hl : ∀ q ∈ l, q ∈ unusedReserve (RL).data (RL).work (RL).scratch) (r : Record) :
    recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket (flipBits l b)))) r
      = recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket b))) r :=
  orderFindingSemiclassical_recordProb_flip_unusedReserve _ _ _ m _ _ _ _ _ _
    (referenceSemiclassicalSetup P inst ℓ).layout b l hl r

/-- All unused reserve qubits of the reference layout, data first. -/
def unusedReserveList (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    List ℕ :=
  ((RL).data.reserve.drop 2).qubits ++ ((RL).work.reserve.drop 1).qubits ++
    ((RL).scratch.reserve.drop 1).qubits

/-- **Every unused reserve qubit flipped in `|0…0⟩`, real circuit, model.** About the high-level circuit only:
the lowered circuit needs every reserve clean (`cleanInput_fails_flip_reserve`), so nothing is
claimed for it. -/
theorem model_real_flip_all_unusedReserve (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (r : Record) :
    recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket (flipBits (unusedReserveList P inst ℓ) RegEncoding.zero)))) r
      = recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket RegEncoding.zero))) r :=
  model_real_flip_unusedReserve P inst ℓ m _ _ (fun q hq => by
    simp only [unusedReserveList, List.mem_append] at hq
    rcases hq with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)) r

/-- The ket with the unused data reserve qubits flipped really differs from `|0…0⟩`. -/
theorem model_flipBits_dataUnused_ne_zero (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    flipBits ((RL).data.reserve.drop 2).qubits (RegEncoding.zero (Basis := qs.Basis))
      ≠ RegEncoding.zero := by
  intro h
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (model_unusedReserve_ne_nil P inst ℓ).1
  have hb := bit_flipBits ((RL).data.reserve.drop 2).nodup q
    (RegEncoding.zero (Basis := qs.Basis))
  rw [h, RegEncoding.bit_zero] at hb
  simp [hq] at hb

/-- **One unused reserve qubit in any superposition, real circuit, model.** About the high-level circuit only:
the lowered circuit needs every reserve clean (`cleanInput_fails_flip_reserve`), so nothing is
claimed for it. -/
theorem model_real_superpose_unusedReserve (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ)
    (hq : q ∈ unusedReserve (RL).data (RL).work (RL).scratch) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (α • qs.ket RegEncoding.zero + β • qs.ket (flipBit q RegEncoding.zero)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassical inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket RegEncoding.zero))) r :=
  orderFindingSemiclassical_recordProb_superpose_exact _ _ _ m _ _ _ _ _ _ _
    (unusedReserve_not_mem_exact inst.N (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
      (referenceSemiclassicalSetup P inst ℓ).step4_workspace
      (referenceSemiclassicalSetup P inst ℓ).layout hq) α β r

/-- **Negative: the lowered circuit's hypothesis fails after such a flip.** Flipping any unused
reserve qubit in `|0…0⟩` breaks `SemiclassicalWorkspaceCleanInput`, the hypothesis under which
the lowered circuit has a semantics (`semiclassical_lowerM_eval`). -/
theorem model_lowered_cleanInput_fails_unusedReserve (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) (q : ℕ)
    (hq : q ∈ unusedReserve (RL).data (RL).work (RL).scratch) :
    ¬ SemiclassicalWorkspaceCleanInput (RL).data (RL).work (RL).scratch
      (flipBit q (RegEncoding.zero (Basis := qs.Basis))) :=
  cleanInput_fails_flip_reserve (unusedReserve_mem_reserve hq)
    (referenceSemiclassicalCleanInput P inst ℓ)

section Ideal

theorem model_ideal_hyps (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    1 < inst.N ∧ inst.N ≤ ASize (RL).data.active ∧
      referenceControl P inst ℓ ∉ (RL).data.active.qubits := by
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hn : regSize (RL).data.active = Nat.log2 (2 * inst.N) := by simp
  refine ⟨by omega, by simpa [ASize, hn] using shor_data_capacity_from_log2 inst.N, fun h =>
    (referenceSemiclassicalSetup P inst ℓ).layout.c_not_mem_data (List.mem_append_left _ h)⟩

/-- **Ideal circuit from `|0…0⟩`, model (A2).** Data `0 < N` (outside T1, which needs data `1`);
any list of qubits outside the data register, other than the control, flipped: every record
probability of the ideal readout is unchanged. -/
theorem model_ideal_flip_zero (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) (l : List ℕ)
    (hl : ∀ q ∈ l, q ∉ (RL).data.active.qubits ∧ q ≠ referenceControl P inst ℓ) (r : Record) :
    recordProb ((semiclassicalIdeal inst.a inst.N m (RL).data.active
        (referenceControl P inst ℓ)).eval
        (MState.init (qs.ket (flipBits l RegEncoding.zero)))) r
      = recordProb ((semiclassicalIdeal inst.a inst.N m (RL).data.active
        (referenceControl P inst ℓ)).eval (MState.init (qs.ket RegEncoding.zero))) r := by
  obtain ⟨hN, hNy, hc⟩ := model_ideal_hyps P inst ℓ
  exact semiclassicalIdeal_recordProb_flipBits_dom inst.a inst.N m _ _ hN hNy inst.coprime hc _
    (by rw [toNat_zero_ket]; omega) l hl r

/-- **Ideal circuit, exponent qubit in superposition from `|0…0⟩`, model (A2).** -/
theorem model_ideal_superpose_exponent_zero (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (α β : ℂ) (r : Record) :
    recordProb ((semiclassicalIdeal inst.a inst.N m (RL).data.active
        (referenceControl P inst ℓ)).eval
        (MState.init (α • qs.ket RegEncoding.zero + β • qs.ket (flipBit q RegEncoding.zero)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((semiclassicalIdeal inst.a inst.N m (RL).data.active
        (referenceControl P inst ℓ)).eval (MState.init (qs.ket RegEncoding.zero))) r := by
  obtain ⟨hN, hNy, hc⟩ := model_ideal_hyps P inst ℓ
  have h := model_exponent_tail_unnamed P inst ℓ q hq
  have hqc := (model_exponent_tail_mem_x_ne_control P inst ℓ q hq).2
  exact semiclassicalIdeal_recordProb_superpose_dom inst.a inst.N m _ _ hN hNy inst.coprime hc _
    (by rw [toNat_zero_ket]; omega) (fun hd => h.1 (Or.inr (Or.inl (List.mem_append_left _ hd))))
    hqc α β r

/-- The ket `|0…0 with data := v⟩` at the reference layout. -/
noncomputable def dataKet (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ v : ℕ) :
    qs.Basis :=
  RegEncoding.writeNat (RL).data.active v RegEncoding.zero

theorem toNat_dataKet (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ v : ℕ)
    (hv : v < inst.N) : RegEncoding.toNat (RL).data.active (dataKet P inst ℓ v) = v :=
  RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le hv (model_ideal_hyps P inst ℓ).2.1)

/-- Work qubits are outside the data register and are not the control. -/
theorem model_work_not_data (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ)
    {q : ℕ} (hq : q ∈ (RL).work.active.qubits) :
    q ∉ (RL).data.active.qubits ∧ q ≠ referenceControl P inst ℓ := by
  have hw := (referenceSemiclassicalSetup P inst ℓ).circuit_workspace.2.2
  have hl := (referenceSemiclassicalSetup P inst ℓ).layout
  refine ⟨fun hd => hw (List.mem_append_left _ hd) (List.mem_append_left _ hq), ?_⟩
  rintro rfl
  exact hl.c_not_mem_work (List.mem_append_left _ hq)

/-- **Non-degenerate A2 witness: data `N - 1`, work qubits flipped.** -/
theorem model_ideal_flip_work_dataTop (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) (l : List ℕ) (hl : ∀ q ∈ l, q ∈ (RL).work.active.qubits) (r : Record) :
    recordProb ((semiclassicalIdeal inst.a inst.N m (RL).data.active
        (referenceControl P inst ℓ)).eval
        (MState.init (qs.ket (flipBits l (dataKet P inst ℓ (inst.N - 1)))))) r
      = recordProb ((semiclassicalIdeal inst.a inst.N m (RL).data.active
        (referenceControl P inst ℓ)).eval (MState.init (qs.ket (dataKet P inst ℓ (inst.N - 1))))) r := by
  obtain ⟨hN, hNy, hc⟩ := model_ideal_hyps P inst ℓ
  exact semiclassicalIdeal_recordProb_flipBits_dom inst.a inst.N m _ _ hN hNy inst.coprime hc _
    (by rw [toNat_dataKet P inst ℓ _ (by omega)]; omega) l
    (fun q hq => model_work_not_data P inst ℓ (hl q hq)) r

/-- **Non-degenerate A2 witness: superposition of data `1` and `N - 1`, a work qubit flipped.** -/
theorem model_ideal_flip_work_twoData (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).work.active.qubits) (α β : ℂ) (r : Record) :
    recordProb ((semiclassicalIdeal inst.a inst.N m (RL).data.active
        (referenceControl P inst ℓ)).eval (MState.init (qs.eval (Gate.X q)
          (α • qs.ket (dataKet P inst ℓ 1) + β • qs.ket (dataKet P inst ℓ (inst.N - 1)))))) r
      = recordProb ((semiclassicalIdeal inst.a inst.N m (RL).data.active
        (referenceControl P inst ℓ)).eval (MState.init
          (α • qs.ket (dataKet P inst ℓ 1) + β • qs.ket (dataKet P inst ℓ (inst.N - 1))))) r := by
  obtain ⟨hN, hNy, hc⟩ := model_ideal_hyps P inst ℓ
  have h := model_work_not_data P inst ℓ hq
  refine semiclassicalIdeal_recordProb_init_X_dom inst.a inst.N m _ _ hN hNy inst.coprime hc
    h.1 h.2 ?_ r
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (ket_mem_idealDom (by rw [toNat_dataKet P inst ℓ _ hN]; exact hN)))
    (Submodule.smul_mem _ _ (ket_mem_idealDom (by rw [toNat_dataKet P inst ℓ _ (by omega)]; omega)))

/-- **The ideal node really moves the data-`N-1` ket** (with the control set, multiplier
`a mod N = a` of the last round, `a ≠ 1`): the output ket has a different data value. -/
theorem model_ideal_moves_dataTop (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) (ha1 : inst.a ≠ 1) :
    let b := flipBit (referenceControl P inst ℓ) (dataKet P inst ℓ (inst.N - 1))
    qs.eval (Gate.idealCtrlModMul inst.a inst.N (RL).data.active (referenceControl P inst ℓ))
        (qs.ket b)
        = qs.ket (RegEncoding.writeNat (RL).data.active (inst.a * (inst.N - 1) % inst.N) b) ∧
      RegEncoding.toNat (RL).data.active
          (RegEncoding.writeNat (RL).data.active (inst.a * (inst.N - 1) % inst.N) b)
        ≠ RegEncoding.toNat (RL).data.active b := by
  intro b
  obtain ⟨hN, hNy, hc⟩ := model_ideal_hyps P inst ℓ
  have hr := inst.range
  refine idealCtrlModMul_moves_top _ _ _ _ b hN hNy inst.coprime hc ?_ ?_ ?_
  · simp only [b]; rw [toNat_flipBit hc, toNat_dataKet P inst ℓ _ (by omega)]
  · simp only [b, dataKet]
    rw [bit_flipBit_self, RegEncoding.bit_writeNat_out _ _ _ _ hc, RegEncoding.bit_zero]; rfl
  · rw [Nat.mod_eq_of_lt hr.2]; exact ha1

end Ideal

end Model
end Shor

#print axioms Shor.Model.toNat_zero_ket
#print axioms Shor.Model.model_unusedReserve_ne_nil
#print axioms Shor.Model.model_reserve_used
#print axioms Shor.Model.model_real_flip_unusedReserve
#print axioms Shor.Model.model_real_flip_all_unusedReserve
#print axioms Shor.Model.model_flipBits_dataUnused_ne_zero
#print axioms Shor.Model.model_real_superpose_unusedReserve
#print axioms Shor.Model.model_lowered_cleanInput_fails_unusedReserve
#print axioms Shor.Model.model_ideal_hyps
#print axioms Shor.Model.model_ideal_flip_zero
#print axioms Shor.Model.model_ideal_superpose_exponent_zero
#print axioms Shor.Model.toNat_dataKet
#print axioms Shor.Model.model_work_not_data
#print axioms Shor.Model.model_ideal_flip_work_dataTop
#print axioms Shor.Model.model_ideal_flip_work_twoData
#print axioms Shor.Model.model_ideal_moves_dataTop
