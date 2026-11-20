import ForShor.ShorVerification.Implementation.Readout.Proofs.Branch
import ForShor.ShorVerification.Implementation.Shor.Proofs.Measurement
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Fintype.Vector

/-!
# Readout: approximate gates (triangle-inequality bound)

The semiclassical readout `semiclassicalIdeal a N m data c` uses exact gates:
the ideal controlled multiplier `U j = idealCtrlModMul (a^(2^(m-1-j)) mod N) N data c`
and the exact feed-forward phase `Phase c (ffAngle j r)`. A real readout replaces

* each multiplier `U j` by a gate `Ũ j` (e.g. the five-step circuit
  `CmodMulInPlaceCore` with control `c`), and
* each feed-forward phase by a record-dependent linear map `R j r` (e.g. a
  synthesized rotation for the angle `ffAngle j r`).

`semiclassicalImpl c Ũ R m` is that implemented readout, as a map on branching
states: round `j` is `H c`, then `Ũ j`, then `R j r` on the branch at record `r`,
then `H c`, then `measureReset c` (the same measurement-and-reset step as
`MGate.measureReset`). With `Ũ = U` and `R j r = Phase c (ffAngle j r)` it IS the
ideal readout (`semiclassicalImpl_exact`).

## The bound (`semiclassical_dist_le_sum_errors`)

Hypotheses, for every round `j < m`:
* `Ũ j` is `ε j`-close to `U j` on `ValidSpan data N P`, the span of the kets
  whose data value is `< N` and which satisfy the side condition `P` (the control
  qubit is arbitrary): `‖Ũ j φ - U j φ‖ ≤ ε j · ‖φ‖`;
* `R j r` is `ρ j`-close to the exact phase on every state, for every record `r`
  of length `j` (the records round `j` sees): `‖R j r φ - Phase c (ffAngle j r) φ‖ ≤ ρ j · ‖φ‖`.
  This is a distance to the exact phase itself, with no global-phase freedom: a
  synthesized rotation that is exact only up to a global phase `e^{iα}` must be
  charged its `|e^{iα} - 1|` here, although a global phase does not change any
  record probability. The hypothesis is therefore conservative (sufficient,
  not necessary);
* `R j r` does not increase norms (true for any unitary);
* the run starts from a unit state `ψ₀` in `InRangeOn c data N P` (control `0`,
  data `< N`, side condition `P`), and `P` is unchanged by writing the control
  or the data register.

Only the multipliers and the feed-forward phases are replaced: the two
Hadamards `H c` and the measure-and-reset step of every round stay exact in the
implemented readout (they are the same `MGate` steps as in the ideal one).

Conclusion: the `ℓ¹` distance of the record distributions,
`∑_r |P_impl(r) - P_ideal(r)|` over all records, is at most
`2 ∑_{j<m} (ε j + ρ j)`. In standard total-variation terms
(`TV = ½ · ℓ¹`) this is `TV ≤ ∑_{j<m} (ε j + ρ j)`. Only records of length `m` contribute
(`semiclassical_dist_summand_eq_zero`); `semiclassical_dist_le_sum_errors_finite`
is the same bound as a finite sum over them. `semiclassical_dist_zero`: with all
`ε j = ρ j = 0` the two record distributions are equal.

## Discharging the multiplier hypothesis (for the real multiplier)

The existing per-step bound `modMul_approx_valid_dist_uniform` is stated on unit
vectors of `ValidAlgorithm1State` (data `< N`, work, scratch, flag and reserve
qubits zero; control arbitrary), for `CmodMulInPlaceCore c N ctrl …` against
`idealCtrlModMul c N data.active ctrl`, with the control `ctrl` a plain
parameter (take `ctrl := c`). With `P` the non-data part of
`GoodAlgorithm1BasisInput`, `ValidSpan data.active N P` is that span, and
`gate_dist_le_of_unit` turns a unit-vector bound into the `ε · ‖φ‖` form used here.

## Proof

* Geometry: `l2 k ψ` is the `ℓ²` norm `√(∑_{|r| = k} ‖ψ r‖²)` of the branches at
  the records of length `k` (as a `PiLp 2` norm over `List.Vector Bool k`).
  `measureReset` maps the records of length `k` onto those of length `k + 1`
  and is an `ℓ²` isometry (`l2_measureReset`, Born completeness per branch);
  branchwise unitaries preserve `l2`; branchwise contractions do not increase it.
* Where the error hypotheses are used: the ideal run stays in
  `InRangeOn c data N P` round by round (`inRangeOn_round_eval`, from the
  one-round identity of `Proofs/Deferred.lean`), so the input of the ideal
  multiplier `H c (v r)` lies in `ValidSpan` (`H_mem_validSpan`). In round `k`,
  with `u`, `v` the implemented and ideal states before the round,
  `R(Ũ(H u)) - Phase(U(H v)) = R(Ũ(H(u - v))) + R(Ũ(H v) - U(H v)) + (R - Phase)(U(H v))`,
  so each error term is evaluated on the ideal-run vector, where the hypothesis
  holds (`l2_round_sub_le`). Summing over rounds:
  `l2 m (impl - ideal) ≤ ∑_{j<m} (ε j + ρ j)` (`l2_readout_sub_le`).
* From `ℓ²` distance to the `ℓ¹` distance of probabilities: `|‖u_r‖² - ‖v_r‖²| ≤ ‖u_r + v_r‖‖u_r - v_r‖`
  (`abs_norm_sq_sub_norm_sq_le`), then Cauchy-Schwarz over the records and
  `l2 (u + v) ≤ l2 u + l2 v ≤ 2` (`sum_abs_recordProb_sub_le`). This is where
  the factor `2` comes from.

Everything is derived from the existing classes; no new axioms.
-/

namespace Shor
namespace Readout

open MeasureClass

/-! ## Records of one length and the `ℓ²` norm of a branching state -/

section L2

variable {qs : QSemantics}

/-- The records of length `k + 1` are the records `r ++ [b]`, `|r| = k`. -/
def snocRecEquiv (k : ℕ) : List.Vector Bool k × Bool ≃ List.Vector Bool (k + 1) where
  toFun p := ⟨p.1.1 ++ [p.2], by simp [p.1.2]⟩
  invFun v := (⟨v.1.dropLast, by simp [v.2]⟩,
    v.1.getLast (List.ne_nil_of_length_pos (by simp [v.2])))
  left_inv p := by
    rcases p with ⟨⟨l, hl⟩, b⟩
    simp
  right_inv v := by
    rcases v with ⟨l, hl⟩
    exact Subtype.ext (List.dropLast_append_getLast _)

/-- The branches of `ψ` at the records of length `k`, as a vector of the
`ℓ²` direct sum of copies of `qs.State` indexed by those records. -/
noncomputable def toL2 (k : ℕ) (ψ : MState qs) :
    PiLp 2 (fun _ : List.Vector Bool k => qs.State) :=
  WithLp.toLp 2 (fun v => ψ v.1)

/-- The `ℓ²` norm of the branches of `ψ` at the records of length `k`:
`l2 k ψ = √(∑_{|r| = k} ‖ψ r‖²)` (`l2_sq`). For `ψ` reached from
`MState.init ψ₀` by `k` measurements this is the norm of the whole branching
state, and `l2 k ψ ^ 2` is its total probability. -/
noncomputable def l2 (k : ℕ) (ψ : MState qs) : ℝ := ‖toL2 k ψ‖

theorem l2_nonneg (k : ℕ) (ψ : MState qs) : 0 ≤ l2 k ψ := norm_nonneg _

/-- `l2 k ψ ^ 2 = ∑_{|r| = k} ‖ψ r‖²`. -/
theorem l2_sq (k : ℕ) (ψ : MState qs) :
    l2 k ψ ^ 2 = ∑ v : List.Vector Bool k, ‖ψ v.1‖ ^ 2 := by
  rw [l2, PiLp.norm_sq_eq_of_L2]
  rfl

/-- Two nonnegative reals with equal squares are equal (for `l2`). -/
theorem l2_eq_of_sq_eq {k k' : ℕ} {ψ : MState qs} {φ : MState qs}
    (h : l2 k ψ ^ 2 = l2 k' φ ^ 2) : l2 k ψ = l2 k' φ :=
  (pow_left_inj₀ (l2_nonneg k ψ) (l2_nonneg k' φ) two_ne_zero).1 h

/-- Triangle inequality. -/
theorem l2_add_le (k : ℕ) (f g : MState qs) : l2 k (f + g) ≤ l2 k f + l2 k g :=
  norm_add_le (toL2 k f) (toL2 k g)

/-- Comparison branch by branch: if `‖f r‖ ≤ C · ‖g r‖` on every record of
length `k`, then `l2 k f ≤ C · l2 k g` (any real `C`). -/
theorem l2_le_of_branch_le (k : ℕ) (f g : MState qs) (C : ℝ)
    (h : ∀ r : Record, r.length = k → ‖f r‖ ≤ C * ‖g r‖) : l2 k f ≤ C * l2 k g := by
  by_cases hC : 0 ≤ C
  · have hsq : l2 k f ^ 2 ≤ (C * l2 k g) ^ 2 := by
      rw [mul_pow, l2_sq, l2_sq, Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (h v.1 v.2) 2
    exact (pow_le_pow_iff_left₀ (l2_nonneg k f) (mul_nonneg hC (l2_nonneg k g))
      two_ne_zero).1 hsq
  · push Not at hC
    have hg : ∀ r : Record, r.length = k → ‖g r‖ = 0 := fun r hr => by
      have := h r hr
      nlinarith [norm_nonneg (f r), norm_nonneg (g r)]
    have hf : ∀ r : Record, r.length = k → ‖f r‖ = 0 := fun r hr => by
      have := h r hr
      rw [hg r hr, mul_zero] at this
      exact le_antisymm this (norm_nonneg _)
    have h0 : ∀ ψ : MState qs, (∀ r : Record, r.length = k → ‖ψ r‖ = 0) → l2 k ψ = 0 :=
      fun ψ hψ => by
        have : l2 k ψ ^ 2 = 0 := by
          rw [l2_sq]
          exact Finset.sum_eq_zero fun v _ => by rw [hψ v.1 v.2]; simp
        exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this
    rw [h0 f hf, h0 g hg, mul_zero]

/-- Equal norms branch by branch on the records of length `k` give equal `l2 k`. -/
theorem l2_eq_of_branch_eq (k : ℕ) (f g : MState qs)
    (h : ∀ r : Record, r.length = k → ‖f r‖ = ‖g r‖) : l2 k f = l2 k g :=
  le_antisymm (by simpa using l2_le_of_branch_le k f g 1 (fun r hr => by rw [h r hr, one_mul]))
    (by simpa using l2_le_of_branch_le k g f 1 (fun r hr => by rw [h r hr, one_mul]))

/-- The initial branching state has `l2 0 (init ψ₀) = ‖ψ₀‖`. -/
theorem l2_init (ψ₀ : qs.State) : l2 0 (MState.init ψ₀) = ‖ψ₀‖ := by
  have h : l2 0 (MState.init ψ₀) ^ 2 = ‖ψ₀‖ ^ 2 := by
    rw [l2_sq, Fintype.sum_eq_single (List.Vector.nil : List.Vector Bool 0)]
    · rfl
    · intro v hv
      exact absurd (Subtype.ext (List.eq_nil_of_length_eq_zero v.2)) hv
  exact (pow_left_inj₀ (l2_nonneg _ _) (norm_nonneg _) two_ne_zero).1 h

variable [RegEncoding qs.Basis] [GateSemanticsCore qs] [MeasureClass qs]

/-- `measureReset q` is an `ℓ²` isometry from the records of length `k` to the
records of length `k + 1` (Born completeness on each branch). -/
theorem l2_measureReset [LowerGateClass qs] (q k : ℕ) (ψ : MState qs) :
    l2 (k + 1) ((MGate.measureReset q).eval ψ) = l2 k ψ := by
  refine l2_eq_of_sq_eq ?_
  rw [l2_sq, l2_sq, ← (snocRecEquiv k).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_bool]
  change ‖(MGate.measureReset q).eval ψ (v.1 ++ [true])‖ ^ 2
      + ‖(MGate.measureReset q).eval ψ (v.1 ++ [false])‖ ^ 2 = _
  rw [MGate.eval_measureReset_append, MGate.eval_measureReset_append, add_comm,
    norm_sq_measureResetBranch_false_add_true]

end L2

/-! ## The implemented readout -/

section Impl

variable {qs : QSemantics} [RegEncoding qs.Basis]
  [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]

/-- The last two steps of a round, `H c ;; measureReset c`. -/
def roundTail (c : ℕ) : MGate := .seq (.unitary (Gate.H c)) (.measureReset c)

/-- One round of the implemented readout on control qubit `c`: `H c`, then the
gate `U`, then the linear map `R r` on the branch at record `r` (the
implemented feed-forward rotation), then `H c ;; measureReset c`. -/
noncomputable def implRound (c : ℕ) (U : Gate) (R : Record → qs.State →ₗ[ℂ] qs.State)
    (ψ : MState qs) : MState qs :=
  (roundTail c).eval (fun r => R r (qs.eval U (qs.eval (Gate.H c) (ψ r))))

/-- **The implemented semiclassical readout**: `m` rounds on the control qubit
`c`; round `j` (in increasing `j`) is `implRound c (Ũ j) (R j)`, i.e. the round
`H c ;; Ũ j ;; [R j r on branch r] ;; H c ;; measureReset c`. Same shape as
`readoutRounds`, with the controlled multiplier replaced by `Ũ j` and the exact
feed-forward phase `Phase c (ffAngle j r)` replaced by `R j r`. -/
noncomputable def semiclassicalImpl (c : ℕ) (Ũ : ℕ → Gate)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) : ℕ → MState qs → MState qs
  | 0, ψ => ψ
  | j + 1, ψ => implRound c (Ũ j) (R j) (semiclassicalImpl c Ũ R j ψ)

/-- The exact feed-forward phase of round `j` as a record-dependent linear map:
`Phase c (ffAngle j r)` on the branch at `r`. -/
noncomputable def exactPhase (c j : ℕ) : Record → qs.State →ₗ[ℂ] qs.State :=
  fun r => lowL (LowGate.Phase c (ffAngle j r))

/-- Every `MGate` program acts linearly on branching states (here: commutes
with subtraction). -/
theorem MGate_eval_sub (P : MGate) (ψ φ : MState qs) :
    P.eval (ψ - φ) = P.eval ψ - P.eval φ := by
  induction P generalizing ψ φ with
  | unitary g => funext r; exact gate_eval_sub g (ψ r) (φ r)
  | ffPhase q j => funext r; exact (lowL (LowGate.Phase q (ffAngle j r))).map_sub (ψ r) (φ r)
  | seq a b iha ihb => simp only [MGate.eval_seq, iha, ihb]
  | measureReset q =>
    funext r
    rcases List.eq_nil_or_concat r with rfl | ⟨r₀, b, rfl⟩
    · simp
    · simp only [List.concat_eq_append, Pi.sub_apply, MGate.eval_measureReset_append]
      cases b
      · simp [measureResetBranch, map_sub]
      · simp [measureResetBranch, map_sub, gate_eval_sub]

/-- `H c ;; measureReset c` maps `l2 k` to `l2 (k+1)` isometrically. -/
theorem l2_roundTail (c k : ℕ) (ψ : MState qs) :
    l2 (k + 1) ((roundTail c).eval ψ) = l2 k ψ := by
  simp only [roundTail, MGate.eval_seq]
  rw [l2_measureReset]
  exact l2_eq_of_branch_eq k _ _ fun r _ => norm_eval_gate _ _

/-- A round of the ideal readout is `implRound` with the ideal multiplier and the
exact feed-forward phase. -/
theorem readoutRound_eval_eq_implRound (c j : ℕ) (U : Gate) (ψ : MState qs) :
    (readoutRound c U j).eval ψ = implRound c U (exactPhase c j) ψ := rfl

/-- **Exact gates give the ideal readout.** With `Ũ = U` and the exact phases,
the implemented readout is the run of `readoutRounds U c m`. -/
theorem semiclassicalImpl_exact (c : ℕ) (U : ℕ → Gate) (m : ℕ) (ψ : MState qs) :
    semiclassicalImpl c U (fun j => exactPhase c j) m ψ = (readoutRounds U c m).eval ψ := by
  induction m with
  | zero =>
    funext r
    simp [semiclassicalImpl, readoutRounds, GateSemanticsCore.eval_id]
  | succ k ih =>
    rw [semiclassicalImpl, ih, readoutRounds_succ_eval, readoutRound_eval_eq_implRound]

/-- The ideal readout as an implemented readout. -/
theorem semiclassicalIdeal_eq_impl (a N m : ℕ) (data : Reg) (c : ℕ) (ψ : MState qs) :
    (semiclassicalIdeal a N m data c).eval ψ
      = semiclassicalImpl c (schedule a N m data c) (fun j => exactPhase c j) m ψ := by
  rw [semiclassicalImpl_exact, semiclassicalIdeal_eq]

/-- The `l2` norm after an implemented round is the `l2` norm of the branches
just before the final `H c ;; measureReset c`. -/
theorem l2_implRound (c k : ℕ) (U : Gate) (R : Record → qs.State →ₗ[ℂ] qs.State)
    (ψ : MState qs) :
    l2 (k + 1) (implRound c U R ψ)
      = l2 k (fun r => R r (qs.eval U (qs.eval (Gate.H c) (ψ r)))) :=
  l2_roundTail c k _

/-- An implemented round whose rotations do not increase norms (on the records
of length `k`) does not increase `l2`. -/
theorem l2_implRound_le (c k : ℕ) (U : Gate) (R : Record → qs.State →ₗ[ℂ] qs.State)
    (hR : ∀ r : Record, r.length = k → ∀ φ, ‖R r φ‖ ≤ ‖φ‖) (ψ : MState qs) :
    l2 (k + 1) (implRound c U R ψ) ≤ l2 k ψ := by
  rw [l2_implRound]
  simpa using l2_le_of_branch_le k _ ψ 1 fun r hr => by
    rw [one_mul]
    refine (hR r hr _).trans ?_
    rw [norm_eval_gate, norm_eval_gate]

/-- An ideal round preserves `l2`. -/
theorem l2_readoutRound (c k : ℕ) (U : Gate) (ψ : MState qs) :
    l2 (k + 1) ((readoutRound c U k).eval ψ) = l2 k ψ := by
  rw [readoutRound_eval_eq_implRound, l2_implRound]
  exact l2_eq_of_branch_eq k _ _ fun r _ => by
    simp only [exactPhase, lowL_apply]
    rw [norm_evalL_phase, norm_eval_gate, norm_eval_gate]

/-- Support: if `ψ` vanishes off the records of length `k`, an implemented round
gives a state vanishing off the records of length `k + 1`. -/
theorem implRound_support (c k : ℕ) (U : Gate) (R : Record → qs.State →ₗ[ℂ] qs.State)
    (ψ : MState qs) (h : ∀ r : Record, r.length ≠ k → ψ r = 0) :
    ∀ r : Record, r.length ≠ k + 1 → implRound c U R ψ r = 0 := by
  intro r hr
  refine MGate.eval_support (roundTail c) (k := k) (fun r' hr' => ?_) r (by simpa [roundTail,
    MGate.numMeas] using hr)
  simp [h r' hr', MGate.gate_eval_zero_state]

/-- The implemented readout from `MState.init ψ₀` vanishes off the records of
length `m`. -/
theorem semiclassicalImpl_support (c : ℕ) (Ũ : ℕ → Gate)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ψ₀ : qs.State) (m : ℕ) :
    ∀ r : Record, r.length ≠ m → semiclassicalImpl c Ũ R m (MState.init ψ₀) r = 0 := by
  induction m with
  | zero =>
    intro r hr
    have : r ≠ [] := fun h => hr (by simp [h])
    simp [semiclassicalImpl, MState.init, this]
  | succ k ih => exact implRound_support c k (Ũ k) (R k) _ ih

/-- **One round, implemented versus ideal.** Let `u`, `v` be the implemented and
ideal states before round `k`. Suppose the ideal multiplier's input `H c (v r)`
lies in `S` for every record `r` of length `k`, `Ũ` is `ε`-close to `U` on `S`,
and on the records of length `k` the rotation `R r` is `ρ`-close to the exact
phase and does not increase norms. Then after the round
`l2 (u' - v') ≤ l2 (u - v) + (ε + ρ) · l2 v`.

Each error is evaluated on the IDEAL-run vector: `R(Ũ(H u)) - Phase(U(H v))`
splits as `R(Ũ(H(u - v))) + R(Ũ(H v) - U(H v)) + (R - Phase)(U(H v))`. -/
theorem l2_round_sub_le (c k : ℕ) (Ũ U : Gate) (R : Record → qs.State →ₗ[ℂ] qs.State)
    (S : Submodule ℂ qs.State) (ε ρ : ℝ) (u v : MState qs)
    (hv : ∀ r : Record, r.length = k → qs.eval (Gate.H c) (v r) ∈ S)
    (hU : ∀ φ ∈ S, ‖qs.eval Ũ φ - qs.eval U φ‖ ≤ ε * ‖φ‖)
    (hR : ∀ r : Record, r.length = k → ∀ φ : qs.State,
      ‖R r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle k r)) φ‖ ≤ ρ * ‖φ‖)
    (hRc : ∀ r : Record, r.length = k → ∀ φ : qs.State, ‖R r φ‖ ≤ ‖φ‖) :
    l2 (k + 1) (implRound c Ũ R u - (readoutRound c U k).eval v)
      ≤ l2 k (u - v) + (ε + ρ) * l2 k v := by
  rw [readoutRound_eval_eq_implRound, implRound, implRound, ← MGate_eval_sub, l2_roundTail]
  set A : MState qs := fun r => R r (qs.eval Ũ (qs.eval (Gate.H c) ((u - v) r))) with hA
  set B : MState qs := fun r => R r (qs.eval Ũ (qs.eval (Gate.H c) (v r))
    - qs.eval U (qs.eval (Gate.H c) (v r))) with hB
  set C : MState qs := fun r => R r (qs.eval U (qs.eval (Gate.H c) (v r)))
    - LowerGateClass.evalL (LowGate.Phase c (ffAngle k r)) (qs.eval U (qs.eval (Gate.H c) (v r)))
    with hC
  have hsplit : (fun r => R r (qs.eval Ũ (qs.eval (Gate.H c) (u r))))
      - (fun r => exactPhase c k r (qs.eval U (qs.eval (Gate.H c) (v r)))) = A + B + C := by
    funext r
    simp only [hA, hB, hC, Pi.sub_apply, Pi.add_apply, gate_eval_sub, map_sub, exactPhase,
      lowL_apply]
    abel
  rw [hsplit]
  have hAle : l2 k A ≤ 1 * l2 k (u - v) := l2_le_of_branch_le k _ _ 1 fun r hr => by
    refine (hRc r hr _).trans ?_
    rw [norm_eval_gate, norm_eval_gate, one_mul]
  have hBle : l2 k B ≤ ε * l2 k v := l2_le_of_branch_le k _ _ ε fun r hr => by
    refine (hRc r hr _).trans ?_
    refine (hU _ (hv r hr)).trans ?_
    rw [norm_eval_gate]
  have hCle : l2 k C ≤ ρ * l2 k v := l2_le_of_branch_le k _ _ ρ fun r hr => by
    refine (hR r hr _).trans ?_
    rw [norm_eval_gate, norm_eval_gate]
  calc l2 k (A + B + C) ≤ l2 k A + l2 k B + l2 k C :=
        (l2_add_le k _ _).trans (by linarith [l2_add_le k A B])
    _ ≤ 1 * l2 k (u - v) + ε * l2 k v + ρ * l2 k v := by linarith
    _ = l2 k (u - v) + (ε + ρ) * l2 k v := by ring

/-- The ideal run from `MState.init ψ₀` keeps `l2 = ‖ψ₀‖` after every number of
rounds. -/
theorem l2_readoutRounds (U : ℕ → Gate) (c : ℕ) (ψ₀ : qs.State) (m : ℕ) :
    l2 m ((readoutRounds U c m).eval (MState.init ψ₀)) = ‖ψ₀‖ := by
  induction m with
  | zero =>
    rw [← l2_init ψ₀]
    exact l2_eq_of_branch_eq 0 _ _ fun r _ => by
      simp [readoutRounds, GateSemanticsCore.eval_id]
  | succ k ih => rw [readoutRounds_succ_eval, l2_readoutRound, ih]

/-- The implemented run from `MState.init ψ₀` has `l2 ≤ ‖ψ₀‖` when its rotations
do not increase norms. -/
theorem l2_semiclassicalImpl_le (c : ℕ) (Ũ : ℕ → Gate)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ψ₀ : qs.State) (m : ℕ)
    (hRc : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State, ‖R j r φ‖ ≤ ‖φ‖) :
    l2 m (semiclassicalImpl c Ũ R m (MState.init ψ₀)) ≤ ‖ψ₀‖ := by
  induction m with
  | zero => exact (l2_init ψ₀).le
  | succ k ih =>
    exact (l2_implRound_le c k (Ũ k) (R k) (hRc k (by omega)) _).trans
      (ih fun j hj => hRc j (by omega))

/-- **Telescoping over rounds.** If, for every round `j < m`, the ideal
multiplier's input `H c (v_j r)` along the ideal run lies in `S` (records of
length `j`), `Ũ j` is `ε j`-close to `U j` on `S`, and `R j r` is `ρ j`-close to
the exact phase and norm-nonincreasing on the records of length `j`, then after
`m` rounds `l2 m (impl - ideal) ≤ (∑_{j<m} (ε j + ρ j)) · ‖ψ₀‖`. -/
theorem l2_readout_sub_le (c : ℕ) (U Ũ : ℕ → Gate) (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State)
    (S : Submodule ℂ qs.State) (ε ρ : ℕ → ℝ) (ψ₀ : qs.State) (m : ℕ)
    (hv : ∀ j < m, ∀ r : Record, r.length = j →
      qs.eval (Gate.H c) ((readoutRounds U c j).eval (MState.init ψ₀) r) ∈ S)
    (hU : ∀ j < m, ∀ φ ∈ S, ‖qs.eval (Ũ j) φ - qs.eval (U j) φ‖ ≤ ε j * ‖φ‖)
    (hR : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State, ‖R j r φ‖ ≤ ‖φ‖) :
    l2 m (semiclassicalImpl c Ũ R m (MState.init ψ₀) - (readoutRounds U c m).eval (MState.init ψ₀))
      ≤ (∑ j ∈ Finset.range m, (ε j + ρ j)) * ‖ψ₀‖ := by
  induction m with
  | zero =>
    have := l2_le_of_branch_le 0
      (semiclassicalImpl c Ũ R 0 (MState.init ψ₀) - (readoutRounds U c 0).eval (MState.init ψ₀))
      (MState.init ψ₀) 0 fun r _ => by
        simp [semiclassicalImpl, readoutRounds, GateSemanticsCore.eval_id]
    simpa using this
  | succ k ih =>
    have ih' := ih (fun j hj => hv j (by omega)) (fun j hj => hU j (by omega))
      (fun j hj => hR j (by omega)) (fun j hj => hRc j (by omega))
    have hstep := l2_round_sub_le c k (Ũ k) (U k) (R k) S (ε k) (ρ k)
      (semiclassicalImpl c Ũ R k (MState.init ψ₀)) ((readoutRounds U c k).eval (MState.init ψ₀))
      (hv k (by omega)) (hU k (by omega)) (hR k (by omega)) (hRc k (by omega))
    rw [l2_readoutRounds] at hstep
    rw [semiclassicalImpl, readoutRounds_succ_eval, Finset.sum_range_succ]
    linarith

omit [LowerGateClass qs] [MeasureClass qs] in
/-- **From a unit-vector bound to the multiplier hypothesis.** If two gates are
`ε`-close on every UNIT vector of a subspace `S` (the form of the existing
per-step bound `modMul_approx_valid_dist_uniform` on `ModMulConfig.ValidUnitState`),
then `‖A φ - B φ‖ ≤ ε · ‖φ‖` on all of `S` (the form `hU` of
`semiclassical_dist_le_sum_errors` asks for), by linearity. -/
theorem gate_dist_le_of_unit (S : Submodule ℂ qs.State) (A B : Gate) (ε : ℝ)
    (h : ∀ φ ∈ S, ‖φ‖ = 1 → ‖qs.eval A φ - qs.eval B φ‖ ≤ ε) :
    ∀ φ ∈ S, ‖qs.eval A φ - qs.eval B φ‖ ≤ ε * ‖φ‖ := by
  intro φ hφ
  by_cases h0 : φ = 0
  · subst h0
    simp [MGate.gate_eval_zero_state]
  · have ht : 0 < ‖φ‖ := norm_pos_iff.2 h0
    set φ' : qs.State := ((‖φ‖⁻¹ : ℝ) : ℂ) • φ with hφ'
    have hφ'S : φ' ∈ S := S.smul_mem _ hφ
    have hφ'1 : ‖φ'‖ = 1 := by
      rw [hφ', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ ht.ne']
    have hscale : ∀ G : Gate, qs.eval G φ = ((‖φ‖ : ℝ) : ℂ) • qs.eval G φ' := fun G => by
      rw [hφ', gate_eval_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne',
        Complex.ofReal_one, one_smul]
    have hlin : qs.eval A φ - qs.eval B φ = ((‖φ‖ : ℝ) : ℂ) • (qs.eval A φ' - qs.eval B φ') := by
      rw [hscale A, hscale B, smul_sub]
    rw [hlin, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm, mul_comm ε]
    exact mul_le_mul_of_nonneg_left (h φ' hφ'S hφ'1) (norm_nonneg _)

end Impl

/-! ## From `ℓ²` distance to the `ℓ¹` distance of record probabilities -/

section TV

variable {qs : QSemantics}

/-- **`ℓ¹` distance of probabilities from `ℓ²` distance of branches.** Over the
records of length `k`, `∑ |‖u r‖² - ‖v r‖²| ≤ (l2 u + l2 v) · l2 (u - v)`: per record
`|‖u_r‖² - ‖v_r‖²| ≤ ‖u_r + v_r‖‖u_r - v_r‖` (`abs_norm_sq_sub_norm_sq_le`),
then Cauchy-Schwarz over the records and the triangle inequality. -/
theorem sum_abs_recordProb_sub_le (k : ℕ) (u v : MState qs) :
    ∑ w : List.Vector Bool k, |recordProb u w.1 - recordProb v w.1|
      ≤ (l2 k u + l2 k v) * l2 k (u - v) := by
  have hsqrt : ∀ ψ : MState qs, l2 k ψ = Real.sqrt (∑ w : List.Vector Bool k, ‖ψ w.1‖ ^ 2) :=
    fun ψ => by rw [← l2_sq, Real.sqrt_sq (l2_nonneg k ψ)]
  calc ∑ w : List.Vector Bool k, |recordProb u w.1 - recordProb v w.1|
      ≤ ∑ w : List.Vector Bool k, ‖(u + v) w.1‖ * ‖(u - v) w.1‖ :=
        Finset.sum_le_sum fun w _ => abs_norm_sq_sub_norm_sq_le (u w.1) (v w.1)
    _ ≤ l2 k (u + v) * l2 k (u - v) := by
        rw [hsqrt (u + v), hsqrt (u - v)]
        exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ (l2 k u + l2 k v) * l2 k (u - v) :=
        mul_le_mul_of_nonneg_right (l2_add_le k u v) (l2_nonneg k _)

/-- A function of records vanishing off the records of length `k` has its sum
over all records equal to its finite sum over the records of length `k`. -/
theorem tsum_eq_sum_vector (k : ℕ) (f : Record → ℝ) (h : ∀ r : Record, r.length ≠ k → f r = 0) :
    ∑' r : Record, f r = ∑ w : List.Vector Bool k, f w.1 := by
  rw [tsum_eq_sum (s := (Finset.univ : Finset (List.Vector Bool k)).map
    ⟨List.Vector.toList, List.Vector.toList_injective⟩)]
  · rw [Finset.sum_map]
    rfl
  · intro r hr
    refine h r fun hl => hr ?_
    exact Finset.mem_map.2 ⟨⟨r, hl⟩, Finset.mem_univ _, rfl⟩

end TV

/-! ## The subspaces where the ideal run lives -/

section Spans

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis]

/-- The span of the basis kets `|x⟩` with data value `< N` and side condition
`P x` (the control qubit arbitrary): where the multiplier error hypothesis is
required. With `P` the "work, scratch, flag and reserve qubits are zero"
condition this is `ValidAlgorithm1State`, on which the existing per-step
modular-multiplication bound holds. -/
def ValidSpan (data : Reg) (N : ℕ) (P : qs.Basis → Prop) : Submodule ℂ qs.State :=
  Submodule.span ℂ (qs.ket '' {x | RegEncoding.toNat data x < N ∧ P x})

/-- `InRange c data N` with a side condition `P`: the span of the basis kets
with control bit `c` equal to `0`, data value `< N`, and `P`. The branches of
the ideal readout stay in it (`inRangeOn_round_eval`). -/
def InRangeOn (c : ℕ) (data : Reg) (N : ℕ) (P : qs.Basis → Prop) (φ : qs.State) : Prop :=
  φ ∈ Submodule.span ℂ
    (qs.ket '' {x | RegEncoding.bit c x = false ∧ RegEncoding.toNat data x < N ∧ P x})

/-- `InRangeOn` (any side condition) implies `InRange`. -/
theorem InRangeOn.inRange [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]
    {c : ℕ} {data : Reg} {N : ℕ} {P : qs.Basis → Prop} {φ : qs.State}
    (h : InRangeOn c data N P φ) : InRange c data N φ :=
  by
  refine Submodule.span_mono ?_ h
  rintro _ ⟨x, ⟨h1, h2, -⟩, rfl⟩
  exact ⟨x, ⟨h1, h2⟩, rfl⟩

/-- Writing the control `c` (outside `data`) does not change the data value. -/
theorem toNat_data_writeNat_ctrl (data : Reg) (c v : ℕ) (hc : c ∉ data.qubits) (x : qs.Basis) :
    RegEncoding.toNat data (RegEncoding.writeNat (qubitReg c) v x) = RegEncoding.toNat data x :=
  toNat_eq_of_bits (qs := qs) data fun q hq => RegEncoding.bit_writeNat_out _ _ _ _ (by
    rw [mem_qubitReg]; rintro rfl; exact hc hq)

/-- `H c` maps `InRangeOn c data N P` into `ValidSpan data N P`: the input of the
ideal multiplier in every round of the ideal run is where the multiplier error
hypothesis holds. -/
theorem H_mem_validSpan [GateSemanticsCore qs] [HadamardSemantics qs]
    (c : ℕ) (data : Reg) (N : ℕ) (P : qs.Basis → Prop) (hc : c ∉ data.qubits)
    (hPc : ∀ x v, P x → P (RegEncoding.writeNat (qubitReg c) v x))
    (φ : qs.State) (h : InRangeOn c data N P φ) :
    qs.eval (Gate.H c) φ ∈ ValidSpan data N P := by
  unfold InRangeOn at h
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨-, hyd, hyP⟩, rfl⟩ := hx
    rw [HadamardSemantics.eval_H_ket]
    have hk : ∀ v, qs.ket (RegEncoding.writeNat (qubitReg c) v y) ∈ ValidSpan data N P :=
      fun v => Submodule.subset_span ⟨_, ⟨by rwa [toNat_data_writeNat_ctrl data c v hc], hPc y v hyP⟩,
        rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hk 0) (Submodule.smul_mem _ _ (hk 1)))
  | zero => rw [MGate.gate_eval_zero_state]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [gate_eval_add]; exact Submodule.add_mem _ hx hy
  | smul z x _ hx => rw [gate_eval_smul]; exact Submodule.smul_mem _ _ hx

/-- The uncontrolled action of the ideal multiplier keeps `InRangeOn` (on kets it
writes the data register only). -/
theorem inRangeOn_uncontrolledAction [GateSemanticsCore qs] [MeasureClass qs]
    [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ) (data : Reg) (c : ℕ) (P : qs.Basis → Prop)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hPdata : ∀ x v, P x → P (RegEncoding.writeNat data v x))
    (φ : qs.State) (h : InRangeOn c data N P φ) :
    InRangeOn c data N P (uncontrolledAction c (Gate.idealCtrlModMul a N data c) φ) := by
  unfold InRangeOn at h ⊢
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hyc, hyd, hyP⟩, rfl⟩ := hx
    obtain ⟨-, -, -, h4⟩ := idealCtrlModMul_round_hyps_ket a N data c y hN hNdata ha hc hyd hyc
    rw [h4]
    have hv : a * RegEncoding.toNat data y % N < N := Nat.mod_lt _ (by omega)
    refine Submodule.subset_span ⟨_, ⟨?_, ?_, hPdata _ _ hyP⟩, rfl⟩
    · rw [RegEncoding.bit_writeNat_out _ _ _ _ hc, hyc]
    · rw [RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le hv hNdata)]; exact hv
  | zero =>
    simp only [uncontrolledAction, MGate.gate_eval_zero_state]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    simp only [uncontrolledAction, gate_eval_add] at hx hy ⊢
    exact Submodule.add_mem _ hx hy
  | smul z x _ hx =>
    simp only [uncontrolledAction, gate_eval_smul] at hx ⊢
    exact Submodule.smul_mem _ _ hx

/-- A round of the ideal readout keeps every branch in `InRangeOn` (the
side-condition version of `inRange_round_eval`). -/
theorem inRangeOn_round_eval [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]
    [HadamardSemantics qs] [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ) (data : Reg) (c : ℕ) (P : qs.Basis → Prop)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hPdata : ∀ x v, P x → P (RegEncoding.writeNat data v x))
    (j : ℕ) (ψ : MState qs) (h : ∀ r, InRangeOn c data N P (ψ r)) (r : Record) :
    InRangeOn c data N P ((readoutRound c (Gate.idealCtrlModMul a N data c) j).eval ψ r) := by
  rcases List.eq_nil_or_concat r with rfl | ⟨r₀, b, rfl⟩
  · rw [round_branch_nil]; exact Submodule.zero_mem _
  · rw [List.concat_eq_append]
    obtain ⟨h1, h2, h3⟩ := round_hyps_of_inRange a N data c hN hNdata ha hc _ (h r₀).inRange
    rw [round_branch c _ j ψ r₀ b h1 h2 h3]
    have hT := inRangeOn_uncontrolledAction a N data c P hN hNdata ha hc hPdata _ (h r₀)
    have h0 := h r₀
    unfold InRangeOn at h0 hT ⊢
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ h0 (Submodule.smul_mem _ _ hT))

/-- Along the ideal readout from `MState.init ψ₀` with `ψ₀` in `InRangeOn`, every
branch after every number `k` of rounds is in `InRangeOn`. -/
theorem inRangeOn_semiclassicalIdeal_rounds [GateSemanticsCore qs] [LowerGateClass qs]
    [MeasureClass qs] [HadamardSemantics qs] [PauliXSemantics qs]
    [IdealCtrlModMulExactSemantics qs]
    (a N m : ℕ) (data : Reg) (c : ℕ) (P : qs.Basis → Prop)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hPdata : ∀ x v, P x → P (RegEncoding.writeNat data v x))
    (ψ₀ : qs.State) (hψ₀ : InRangeOn c data N P ψ₀) (k : ℕ) (r : Record) :
    InRangeOn c data N P ((readoutRounds (schedule a N m data c) c k).eval (MState.init ψ₀) r) := by
  induction k generalizing r with
  | zero =>
    simp only [readoutRounds, MGate.eval_unitary, GateSemanticsCore.eval_id, MState.init]
    split_ifs
    · exact hψ₀
    · exact Submodule.zero_mem _
  | succ k ih =>
    rw [readoutRounds_succ_eval]
    exact inRangeOn_round_eval _ N data c P hN hNdata (coprime_pow_mod a N ha _) hc hPdata k _ ih r

end Spans

/-! ## The bound -/

section Bound

variable {qs : QSemantics} [RegEncoding qs.Basis]
  [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]
  [HadamardSemantics qs] [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs]

omit [HadamardSemantics qs] [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs] in
/-- Only records of length `m` carry probability in either readout: off length
`m` both summands of `semiclassical_dist_le_sum_errors` are `0` (so its sum
over all records is a finite sum). -/
theorem semiclassical_dist_summand_eq_zero (a N m : ℕ) (data : Reg) (c : ℕ) (Ũ : ℕ → Gate)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ψ₀ : qs.State) (r : Record)
    (hr : r.length ≠ m) :
    recordProb (semiclassicalImpl c Ũ R m (MState.init ψ₀)) r = 0 ∧
    recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r = 0 := by
  rw [semiclassicalIdeal_eq_impl]
  simp [recordProb, semiclassicalImpl_support _ _ _ _ m r hr]

/-- `semiclassical_dist_le_sum_errors` as a finite sum over the records of
length `m` (the only ones that carry probability). Same hypotheses. -/
theorem semiclassical_dist_le_sum_errors_finite
    (a N m : ℕ) (data : Reg) (c : ℕ) (P : qs.Basis → Prop)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hPc : ∀ x v, P x → P (RegEncoding.writeNat (qubitReg c) v x))
    (hPdata : ∀ x v, P x → P (RegEncoding.writeNat data v x))
    (ψ₀ : qs.State) (hψ₀ : InRangeOn c data N P ψ₀) (hnorm : ‖ψ₀‖ = 1)
    (Ũ : ℕ → Gate) (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ε ρ : ℕ → ℝ)
    (hU : ∀ j < m, ∀ φ ∈ ValidSpan data N P,
      ‖qs.eval (Ũ j) φ
          - qs.eval (Gate.idealCtrlModMul ((a ^ (2 ^ (m - 1 - j))) % N) N data c) φ‖
        ≤ ε j * ‖φ‖)
    (hR : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State, ‖R j r φ‖ ≤ ‖φ‖) :
    ∑ w : List.Vector Bool m, |recordProb (semiclassicalImpl c Ũ R m (MState.init ψ₀)) w.1
        - recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) w.1|
      ≤ 2 * ∑ j ∈ Finset.range m, (ε j + ρ j) := by
  have hvS : ∀ j < m, ∀ r : Record, r.length = j →
      qs.eval (Gate.H c) ((readoutRounds (schedule a N m data c) c j).eval (MState.init ψ₀) r)
        ∈ ValidSpan data N P := fun j _ r _ =>
    H_mem_validSpan c data N P hc hPc _
      (inRangeOn_semiclassicalIdeal_rounds a N m data c P hN hNdata ha hc hPdata ψ₀ hψ₀ j r)
  have hd := l2_readout_sub_le c (schedule a N m data c) Ũ R (ValidSpan data N P) ε ρ ψ₀ m hvS
    (fun j hj φ hφ => hU j hj φ hφ) hR hRc
  have hu := l2_semiclassicalImpl_le c Ũ R ψ₀ m hRc
  have hv := l2_readoutRounds (schedule a N m data c) c ψ₀ m
  rw [hnorm, mul_one] at hd
  rw [hnorm] at hu hv
  rw [semiclassicalIdeal_eq]
  refine (sum_abs_recordProb_sub_le m _ _).trans ?_
  have hD := l2_nonneg m (semiclassicalImpl c Ũ R m (MState.init ψ₀)
    - (readoutRounds (schedule a N m data c) c m).eval (MState.init ψ₀))
  calc _ ≤ 2 * l2 m (semiclassicalImpl c Ũ R m (MState.init ψ₀)
          - (readoutRounds (schedule a N m data c) c m).eval (MState.init ψ₀)) :=
        mul_le_mul_of_nonneg_right (by linarith) hD
    _ ≤ _ := by linarith

/-- **Approximate-gate bound for the semiclassical readout.**

Ideal readout: `semiclassicalIdeal a N m data c` (round `j` multiplies by
`a^(2^(m-1-j)) mod N` with `U j = idealCtrlModMul _ N data c`, exact phase
`Phase c (ffAngle j r)`). Implemented readout: `semiclassicalImpl c Ũ R m`, the
same rounds with `Ũ j` for `U j` and `R j r` for the phase.

Hypotheses: `1 < N ≤ 2^|data|`, `a` coprime to `N`, `c ∉ data`; the side
condition `P` on basis states is unchanged by writing the control `c` or the
data register; the initial state `ψ₀` has norm `1` and lies in
`InRangeOn c data N P` (control `0`, data `< N`, `P`); for every round `j < m`:
* `‖Ũ j φ - U j φ‖ ≤ ε j · ‖φ‖` for every `φ ∈ ValidSpan data N P`;
* `‖R j r φ - Phase c (ffAngle j r) φ‖ ≤ ρ j · ‖φ‖` and `‖R j r φ‖ ≤ ‖φ‖` for
  every state `φ` and every record `r` of length `j` (distance to the exact
  phase with no global-phase freedom: conservative).

The Hadamards and the measure-and-reset steps are exact in both runs.

Conclusion: the `ℓ¹` distance `∑_r |P_impl(r) - P_ideal(r)|` of the record
distributions of the two runs from `ψ₀`, summed over ALL records `r`, is at most
`2 · ∑_{j<m} (ε j + ρ j)`; equivalently the total-variation distance
`TV = ½ · ℓ¹` is at most `∑_{j<m} (ε j + ρ j)`. (Only records of
length `m` contribute, `semiclassical_dist_summand_eq_zero`, so the sum is a
finite sum.) -/
theorem semiclassical_dist_le_sum_errors
    (a N m : ℕ) (data : Reg) (c : ℕ) (P : qs.Basis → Prop)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hPc : ∀ x v, P x → P (RegEncoding.writeNat (qubitReg c) v x))
    (hPdata : ∀ x v, P x → P (RegEncoding.writeNat data v x))
    (ψ₀ : qs.State) (hψ₀ : InRangeOn c data N P ψ₀) (hnorm : ‖ψ₀‖ = 1)
    (Ũ : ℕ → Gate) (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ε ρ : ℕ → ℝ)
    (hU : ∀ j < m, ∀ φ ∈ ValidSpan data N P,
      ‖qs.eval (Ũ j) φ
          - qs.eval (Gate.idealCtrlModMul ((a ^ (2 ^ (m - 1 - j))) % N) N data c) φ‖
        ≤ ε j * ‖φ‖)
    (hR : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State, ‖R j r φ‖ ≤ ‖φ‖) :
    ∑' r : Record, |recordProb (semiclassicalImpl c Ũ R m (MState.init ψ₀)) r
        - recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r|
      ≤ 2 * ∑ j ∈ Finset.range m, (ε j + ρ j) := by
  rw [tsum_eq_sum_vector m _ fun r hr => by
    obtain ⟨h1, h2⟩ := semiclassical_dist_summand_eq_zero a N m data c Ũ R ψ₀ r hr
    rw [h1, h2, sub_zero, abs_zero]]
  exact semiclassical_dist_le_sum_errors_finite a N m data c P hN hNdata ha hc hPc hPdata ψ₀ hψ₀
    hnorm Ũ R ε ρ hU hR hRc

/-- **Zero error, equal distributions.** Under the hypotheses of
`semiclassical_dist_le_sum_errors` with `ε j = ρ j = 0` for every round
`j < m`, every record has the same probability in the implemented and the ideal
readout. -/
theorem semiclassical_dist_zero
    (a N m : ℕ) (data : Reg) (c : ℕ) (P : qs.Basis → Prop)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hPc : ∀ x v, P x → P (RegEncoding.writeNat (qubitReg c) v x))
    (hPdata : ∀ x v, P x → P (RegEncoding.writeNat data v x))
    (ψ₀ : qs.State) (hψ₀ : InRangeOn c data N P ψ₀) (hnorm : ‖ψ₀‖ = 1)
    (Ũ : ℕ → Gate) (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ε ρ : ℕ → ℝ)
    (hU : ∀ j < m, ∀ φ ∈ ValidSpan data N P,
      ‖qs.eval (Ũ j) φ
          - qs.eval (Gate.idealCtrlModMul ((a ^ (2 ^ (m - 1 - j))) % N) N data c) φ‖
        ≤ ε j * ‖φ‖)
    (hR : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State, ‖R j r φ‖ ≤ ‖φ‖)
    (hε : ∀ j < m, ε j = 0) (hρ : ∀ j < m, ρ j = 0) (r : Record) :
    recordProb (semiclassicalImpl c Ũ R m (MState.init ψ₀)) r
      = recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r := by
  by_cases hr : r.length = m
  · have hfin := semiclassical_dist_le_sum_errors_finite a N m data c P hN hNdata ha hc hPc hPdata
      ψ₀ hψ₀ hnorm Ũ R ε ρ hU hR hRc
    have hzero : ∑ j ∈ Finset.range m, (ε j + ρ j) = 0 := Finset.sum_eq_zero fun j hj => by
      rw [hε j (Finset.mem_range.1 hj), hρ j (Finset.mem_range.1 hj), add_zero]
    have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun w : List.Vector Bool m =>
        |recordProb (semiclassicalImpl c Ũ R m (MState.init ψ₀)) w.1
          - recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) w.1|)
      (fun w _ => abs_nonneg _) (Finset.mem_univ ⟨r, hr⟩)
    have h0 : |recordProb (semiclassicalImpl c Ũ R m (MState.init ψ₀)) r
        - recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r| = 0 :=
      le_antisymm (by simp only at hle; rw [hzero, mul_zero] at hfin; linarith) (abs_nonneg _)
    exact sub_eq_zero.1 (abs_eq_zero.1 h0)
  · obtain ⟨h1, h2⟩ := semiclassical_dist_summand_eq_zero a N m data c Ũ R ψ₀ r hr
    rw [h1, h2]

end Bound

end Readout
end Shor
