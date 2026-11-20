import ForShor.ShorVerification.Framework.Semantics.MSemantics

/-!
# Framework/Semantics: tests for the measurement language `MGate`

Basic laws of `MGate.eval` (`Framework/Semantics/MSemantics.lean`), stated for
an arbitrary quantum semantics `qs` with the classes the evaluator needs:

* `measureReset_resets`: after `measureReset q`, every branch has qubit `q`
  in `|0⟩` (it is fixed by the outcome-0 projector of the one-qubit register
  `qubitReg q`);
* `measureReset_recordProb`: the branch `r ++ [b]` carries exactly the Born
  probability of outcome `b` on qubit `q` in branch `r`;
* `measureReset_recordProb_sum`: the two children of a branch together carry
  that branch's probability (measurement and reset lose no weight);
* `unitary_branchwise`, `eval_seq`: a unitary acts on every branch, and
  sequencing is composition;
* `ffAngle_zero`, `ffAngle_one`: the feed-forward angle of round 0 is `0`, and
  that of round 1 is `-1/2` (units of `π`) exactly when the first outcome was 1;
  `ffAngle_two_*` pin the dyadic weights of round 2 (older outcomes weigh less);
* `measureReset_twice_*`: measuring the same qubit twice, the second outcome is
  `0` with certainty; `measureReset_child_of_zero`: a zero branch has zero
  children; `twoRound_hasSum_and_support`: conservation of probability and the
  record-length support on a concrete two-round program;
  `measureReset_init_ket_zero`: measuring the all-zero ket reads `0` with
  probability `1` (a run is not identically zero).
-/

namespace Shor

namespace MSemanticsTests

variable {qs : QSemantics} [RegEncoding qs.Basis]
  [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]

/-- After `measureReset q`, qubit `q` is `|0⟩` in every branch. -/
theorem measureReset_resets [PauliXSemantics qs] (q : ℕ) (ψ : MState qs) (r : Record) :
    MeasureClass.measProj (qubitReg q) 0 ((MGate.measureReset q).eval ψ r)
      = (MGate.measureReset q).eval ψ r := by
  rcases List.eq_nil_or_concat r with rfl | ⟨r₀, b, rfl⟩
  · simp
  · rw [List.concat_eq_append, MGate.eval_measureReset_append]
    exact measProj_zero_measureResetBranch q b (ψ r₀)

/-- The child `r ++ [b]` of branch `r` has the Born probability of reading `b`
on qubit `q` in `ψ r`. -/
theorem measureReset_recordProb (q : ℕ) (ψ : MState qs) (r : Record) (b : Bool) :
    recordProb ((MGate.measureReset q).eval ψ) (r ++ [b])
      = MeasureClass.probMeas (qubitReg q) (if b then 1 else 0) (ψ r) := by
  simp only [recordProb, MGate.eval_measureReset_append]
  exact norm_sq_measureResetBranch q b (ψ r)

/-- The two children of branch `r` carry together exactly the probability of `r`. -/
theorem measureReset_recordProb_sum (q : ℕ) (ψ : MState qs) (r : Record) :
    recordProb ((MGate.measureReset q).eval ψ) (r ++ [false])
      + recordProb ((MGate.measureReset q).eval ψ) (r ++ [true])
      = recordProb ψ r := by
  rw [measureReset_recordProb, measureReset_recordProb]
  exact probMeas_qubitReg_zero_add_one q (ψ r)

/-- A unitary gate acts on each branch separately. -/
theorem unitary_branchwise (g : Gate) (ψ : MState qs) (r : Record) :
    (MGate.unitary g).eval ψ r = qs.eval g (ψ r) := by
  rfl

/-- Sequencing is composition of the branch-family maps. -/
theorem eval_seq (a b : MGate) (ψ : MState qs) :
    (MGate.seq a b).eval ψ = b.eval (a.eval ψ) := by
  rfl

/-- No correction in round 0. -/
theorem ffAngle_zero (rec : Record) : ffAngle 0 rec = 0 := by
  simp [ffAngle]

/-- In round 1 the correction is `-1/2` (a `-π/2` phase) iff the first outcome was 1. -/
theorem ffAngle_one (rec : Record) :
    ffAngle 1 rec = if rec.getD 0 false then -1 / 2 else 0 := by
  unfold ffAngle
  rw [Finset.sum_range_one]
  cases rec.getD 0 false <;> norm_num

/-- Round 2 after outcomes `1, 1`: slot 0 weighs `1/4`, slot 1 weighs `1/2`. -/
theorem ffAngle_two_true_true : ffAngle 2 [true, true] = -3 / 4 := by
  norm_num [ffAngle, Finset.sum_range_succ]

/-- Round 2 after outcomes `1, 0`: only slot 0 (the older outcome) contributes, with weight `1/4`. -/
theorem ffAngle_two_true_false : ffAngle 2 [true, false] = -1 / 4 := by
  norm_num [ffAngle, Finset.sum_range_succ]

/-- Measuring a qubit twice in a row: since the first `measureReset` leaves `q`
in `|0⟩`, the second never reads `1`: every record ending in `[b, true]` has
probability `0`. -/
theorem measureReset_twice_second_one [PauliXSemantics qs] (q : ℕ) (ψ : MState qs)
    (r : Record) (b : Bool) :
    recordProb ((MGate.seq (MGate.measureReset q) (MGate.measureReset q)).eval ψ)
      (r ++ [b, true]) = 0 := by
  have hr : r ++ [b, true] = (r ++ [b]) ++ [true] := by simp
  rw [hr]
  simp only [recordProb, MGate.eval_seq, MGate.eval_measureReset_append]
  rw [← measProj_zero_measureResetBranch q b (ψ r)]
  simp [measureResetBranch, MeasureClass.measProj_orthogonal _ 1 0 _ (by decide),
    MGate.gate_eval_zero_state]

/-- ... and the second reading `0` keeps the whole weight of the first reading:
record `r ++ [b, false]` has the probability that `r ++ [b]` had after one
`measureReset`. -/
theorem measureReset_twice_second_zero [PauliXSemantics qs] (q : ℕ) (ψ : MState qs)
    (r : Record) (b : Bool) :
    recordProb ((MGate.seq (MGate.measureReset q) (MGate.measureReset q)).eval ψ)
        (r ++ [b, false])
      = recordProb ((MGate.measureReset q).eval ψ) (r ++ [b]) := by
  have hr : r ++ [b, false] = (r ++ [b]) ++ [false] := by simp
  rw [hr]
  simp only [recordProb, MGate.eval_seq, MGate.eval_measureReset_append]
  rw [show ∀ φ : qs.State, measureResetBranch q false φ
      = MeasureClass.measProj (qubitReg q) 0 φ from fun _ => rfl,
    measProj_zero_measureResetBranch q b (ψ r)]

/-- A branch of probability `0` has children of probability `0`. -/
theorem measureReset_child_of_zero (q : ℕ) (ψ : MState qs) (r : Record) (b : Bool)
    (h : recordProb ψ r = 0) :
    recordProb ((MGate.measureReset q).eval ψ) (r ++ [b]) = 0 := by
  have hs := measureReset_recordProb_sum q ψ r
  have h0 : 0 ≤ recordProb ((MGate.measureReset q).eval ψ) (r ++ [false]) := by
    unfold recordProb; positivity
  have h1 : 0 ≤ recordProb ((MGate.measureReset q).eval ψ) (r ++ [true]) := by
    unfold recordProb; positivity
  cases b <;> linarith

/-- Conservation of probability on a concrete program with two measurements and a
feed-forward phase in between: the record probabilities sum to `‖ψ₀‖ ^ 2`, and
only records of length 2 are nonzero. -/
theorem twoRound_hasSum_and_support (q : ℕ) (g : Gate) (ψ₀ : qs.State) :
    let P := MGate.seq (MGate.unitary g) (MGate.seq (MGate.measureReset q)
      (MGate.seq (MGate.ffPhase q 1) (MGate.seq (MGate.unitary g) (MGate.measureReset q))))
    HasSum (recordProb (P.eval (MState.init ψ₀))) (‖ψ₀‖ ^ 2)
      ∧ ∀ r : Record, r.length ≠ 2 → P.eval (MState.init ψ₀) r = 0 := by
  intro P
  refine ⟨MGate.eval_init_hasSum P ψ₀, fun r hr => MGate.eval_init_support P ψ₀ r ?_⟩
  simpa [P, MGate.numMeas] using hr

/-- Non-vacuity: measuring any qubit of the all-zero ket reads `0` with
probability `1` (record `[false]`). -/
theorem measureReset_init_ket_zero (q : ℕ) :
    recordProb ((MGate.measureReset q).eval (MState.init (qs.ket RegEncoding.zero))) [false]
      = 1 := by
  have h0 : RegEncoding.toNat (qubitReg q) (RegEncoding.zero : qs.Basis) = 0 := by
    have hlt := RegEncoding.toNat_lt_ASize (qubitReg q) (RegEncoding.zero : qs.Basis)
    have hbit := RegEncoding.bit_eq_testBit_toNat (qubitReg q) (RegEncoding.zero : qs.Basis)
      ⟨0, Nat.zero_lt_one⟩
    change RegEncoding.bit q _ = _ at hbit
    rw [RegEncoding.bit_zero] at hbit
    generalize RegEncoding.toNat (qubitReg q) (RegEncoding.zero : qs.Basis) = n at hlt hbit ⊢
    change n < 2 ^ 1 at hlt
    interval_cases n
    · rfl
    · simp at hbit
  rw [show ([false] : Record) = [] ++ [false] from rfl, measureReset_recordProb]
  simp [MeasureClass.probMeas, MState.init, MeasureClass.measProj_ket, h0, ket_norm_one]

end MSemanticsTests

end Shor
