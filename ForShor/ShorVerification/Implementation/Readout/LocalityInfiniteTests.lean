import ForShor.ShorVerification.Implementation.Readout.LocalityInfinite
import ForShor.ShorVerification.Implementation.Readout.LocalityInfiniteSuperpose
import ForShor.ShorVerification.Implementation.Readout.LocalityTests

/-!
# Readout: tests of locality for infinitely many differing qubits

* `named_qubit_breaks` (negative sanity): agreement on the support cannot be weakened even by
  one qubit. `measureReset q` names `q`; the kets `|b⟩` (bit `q = 0`) and `|flipBit q b⟩` agree
  at EVERY qubit except `q`, yet record `[false]` has probability `1` from one and `0` from the
  other. So `MGate.recordProb_of_agree_inf` would be false without `hagree` at `q`.
* `recordProb_of_agree_recovered`: the old finite-difference theorem `MGate.recordProb_of_agree`
  (with its `hfin` hypothesis, verbatim) is a corollary of `MGate.recordProb_of_agree_inf`; the
  `example` after it proves the same statement with the old theorem, so the two statements are
  literally the same proposition.
* `superpose_inf_weights_needed` (negative sanity for `MGate.recordProb_superpose_inf`): the
  empty program, two DISTINCT kets with weights `1, 1`: record `[]` has probability `2` from the
  superposition and `1` from `|b⟩`, so the factor `∑ ‖α i‖²` cannot be dropped.
* `superpose_inf_distinct_needed`: the distinctness hypothesis `Set.InjOn b s` is needed: with
  `b' = b` the superposition `|b⟩ + |b⟩` has probability `4`, not `(1 + 1) · 1 = 2`.
* `supportReg_exact`: the register used internally is exactly the support (no qubit is added to
  it, so the agreement hypothesis is not strengthened behind the docstring's back).
* `ideal_not_covered`: the general theorem needs `NoIdeal`, and the ideal circuit is not
  `NoIdeal` (it is covered only by T1, with `hfin`, in `Locality.lean`).
* `#print axioms` of every new declaration.

Model instances (an infinite pattern outside the named qubits) are in
`Model/Standard/SemiclassicalLocalityInfiniteModel.lean`.
-/

namespace Shor
namespace Readout
namespace LocalityInfiniteTests

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- **Negative sanity: a named qubit matters.** -/
theorem named_qubit_breaks (q : ℕ) (b : qs.Basis) (hb : RegEncoding.bit q b = false) :
    q ∈ (MGate.measureReset q).qubitSupport ∧
    (∀ p, p ≠ q → RegEncoding.bit p (flipBit q b) = RegEncoding.bit p b) ∧
    recordProb ((MGate.measureReset q).eval (MState.init (qs.ket (flipBit q b)))) [false]
      ≠ recordProb ((MGate.measureReset q).eval (MState.init (qs.ket b))) [false] := by
  obtain ⟨h1, h0⟩ := LocalityTests.measureReset_flip_named (qs := qs) q b hb
  refine ⟨by simp [MGate.qubitSupport], fun p hp => bit_flipBit_ne hp b, ?_⟩
  rw [h1, h0]
  norm_num

/-- **The finite theorem is a corollary.** The statement of `MGate.recordProb_of_agree`
(hypotheses `hP`, `hagree`, `hfin`, verbatim), proved from `MGate.recordProb_of_agree_inf`
alone; `hfin` is not used. -/
theorem recordProb_of_agree_recovered (P : MGate) (hP : P.NoIdeal) (b b' : qs.Basis)
    (hagree : ∀ p ∈ P.qubitSupport, RegEncoding.bit p b' = RegEncoding.bit p b)
    (_hfin : {p | RegEncoding.bit p b' ≠ RegEncoding.bit p b}.Finite) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket b'))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r :=
  MGate.recordProb_of_agree_inf P hP b b' hagree r

/-- Same statement, proved by the OLD theorem: the recovered statement is the old one. -/
example (P : MGate) (hP : P.NoIdeal) (b b' : qs.Basis)
    (hagree : ∀ p ∈ P.qubitSupport, RegEncoding.bit p b' = RegEncoding.bit p b)
    (hfin : {p | RegEncoding.bit p b' ≠ RegEncoding.bit p b}.Finite) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket b'))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r :=
  MGate.recordProb_of_agree P hP b b' hagree hfin r

omit [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
theorem recordProb_id_ket [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]
    (b : qs.Basis) : recordProb ((MGate.unitary Gate.id).eval (MState.init (qs.ket b))) [] = 1 := by
  simp [recordProb, MState.init, QSemantics.eval, GateSemanticsCore.eval_id, ket_norm_one]

/-- **Negative sanity: the weights are needed.** -/
theorem superpose_inf_weights_needed (b b' : qs.Basis) (hne : b ≠ b') :
    recordProb ((MGate.unitary Gate.id).eval (MState.init
        (∑ i ∈ (Finset.univ : Finset Bool), (1 : ℂ) • qs.ket (if i then b' else b)))) [] = 2 ∧
    recordProb ((MGate.unitary Gate.id).eval (MState.init (qs.ket b))) [] = 1 := by
  refine ⟨?_, recordProb_id_ket b⟩
  refine (MGate.recordProb_superpose_inf (MGate.unitary Gate.id) trivial Finset.univ
    (fun _ => 1) (fun i : Bool => if i then b' else b) b ?_
    (by simp [MGate.qubitSupport, Gate.qubitSupport]) []).trans ?_
  · intro i _ j _ hij
    cases i <;> cases j <;> simp_all [eq_comm]
  · rw [recordProb_id_ket]; norm_num

/-- **Negative sanity: distinctness is needed.** With `b' = b`, `|b⟩ + |b⟩` has probability
`4`, while the formula would give `(1 + 1) · 1 = 2`. -/
theorem superpose_inf_distinct_needed (b : qs.Basis) :
    recordProb ((MGate.unitary Gate.id).eval (MState.init
        (∑ i ∈ (Finset.univ : Finset Bool), (1 : ℂ) • qs.ket (if i then b else b)))) [] = 4 := by
  simp only [ite_self, Finset.sum_const, Finset.card_univ, Fintype.card_bool, one_smul]
  simp only [recordProb, MState.init, ↓reduceIte, MGate.eval_unitary, QSemantics.eval,
    GateSemanticsCore.eval_id]
  rw [← Nat.cast_smul_eq_nsmul ℂ, norm_smul, ket_norm_one]
  norm_num

/-- The internal register is exactly the support. -/
theorem supportReg_exact (P : MGate) : {q | q ∈ P.supportReg.qubits} = P.qubitSupport := by
  ext q; exact MGate.mem_supportReg P q

/-- The ideal circuit is outside the scope of the general theorem. -/
theorem ideal_not_covered (a N m : ℕ) (data : Reg) (c : ℕ) :
    ¬ (semiclassicalIdeal a N (m + 1) data c).NoIdeal :=
  LocalityTests.semiclassicalIdeal_not_noIdeal a N m data c

end LocalityInfiniteTests
end Readout
end Shor

#print axioms Shor.Readout.LocalityInfiniteTests.named_qubit_breaks
#print axioms Shor.Readout.LocalityInfiniteTests.recordProb_of_agree_recovered
#print axioms Shor.Readout.LocalityInfiniteTests.superpose_inf_weights_needed
#print axioms Shor.Readout.LocalityInfiniteTests.superpose_inf_distinct_needed
#print axioms Shor.Readout.LocalWith.inner_eq_zero_of_not_agreeOff
#print axioms Shor.Readout.norm_sq_sum_of_orthogonal
#print axioms Shor.Readout.MGate.recordProb_superpose_inf
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_superpose_inf
#print axioms Shor.Readout.MLowGate.eval_init_sum_eq
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_superpose_inf
#print axioms Shor.Readout.LocalityInfiniteTests.supportReg_exact
#print axioms Shor.Readout.LocalityInfiniteTests.ideal_not_covered
#print axioms Shor.Readout.agreeOff_writeNat_of_sub
#print axioms Shor.Readout.agreeOff_writeNat
#print axioms Shor.Readout.AgreeOn.writeNat
#print axioms Shor.Readout.AgreeOn.toNat
#print axioms Shor.Readout.AgreeOn.extToInt
#print axioms Shor.Readout.agreeOn_of_toNat_eq
#print axioms Shor.Readout.eq_of_agreeOff_agreeOn
#print axioms Shor.Readout.eq_iff_toNat_eq_of_agreeOff
#print axioms Shor.Readout.eq_writeNat_iff
#print axioms Shor.Readout.writeNat_fin_injective
#print axioms Shor.Readout.agreeOn_canonR
#print axioms Shor.Readout.localMap_flipBit
#print axioms Shor.Readout.localMap_cnot
#print axioms Shor.Readout.localMap_toffoli
#print axioms Shor.Readout.localMap_cmpGeConst
#print axioms Shor.Readout.localMap_csubConst
#print axioms Shor.Readout.localMap_negate
#print axioms Shor.Readout.localMap_addScaled
#print axioms Shor.Readout.localMap_shiftL
#print axioms Shor.Readout.localMap_shiftR
#print axioms Shor.Readout.localMap_signExtend
#print axioms Shor.Readout.localMap_radixReverse
#print axioms Shor.Readout.inner_ket_ket
#print axioms Shor.Readout.state_eq_of_inner_ket
#print axioms Shor.Readout.LocalWith.expand
#print axioms Shor.Readout.orthonormal_block
#print axioms Shor.Readout.LocalWith.norm_sq_eq
#print axioms Shor.Readout.LocalWith.comp
#print axioms Shor.Readout.LocalOn.comp
#print axioms Shor.Readout.localOn_zero
#print axioms Shor.Readout.localOn_of_sum
#print axioms Shor.Readout.localOn_of_basis
#print axioms Shor.Readout.localOn_of_diag
#print axioms Shor.Readout.inner_eval_adj
#print axioms Shor.Readout.LocalWith.adj
#print axioms Shor.Readout.LocalOn.adj
#print axioms Shor.Readout.gateL_seq
#print axioms Shor.Readout.gate_localOn
#print axioms Shor.Readout.measResetL_apply
#print axioms Shor.Readout.measProj_localOn
#print axioms Shor.Readout.measResetL_localOn
#print axioms Shor.Readout.mgate_mlocal
#print axioms Shor.Readout.MGate.recordProb_of_agreeOn
#print axioms Shor.Readout.Gate.qubitSupport_finite
#print axioms Shor.Readout.MGate.qubitSupport_finite
#print axioms Shor.Readout.MGate.mem_supportReg
#print axioms Shor.Readout.MGate.recordProb_of_agree_inf
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_of_agree_inf
#print axioms Shor.Readout.orderFindingSemiclassical_success_of_agree_inf
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_of_agree_inf
#print axioms Shor.Readout.orderFindingSemiclassicalLow_success_of_agree_inf
#print axioms Shor.Readout.orderFindingSemiclassicalLow_success_eq_of_named
