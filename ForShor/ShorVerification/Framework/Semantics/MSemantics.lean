import ForShor.ShorVerification.Framework.AbstractMachine.MGate
import ForShor.ShorVerification.Framework.Semantics.LowGateSemantics
import ForShor.ShorVerification.Framework.Quantum.Measurement

/-!
# Framework/Semantics: branching-record semantics of `MGate`

A program of the measurement language `MGate` acts on an `MState`: a family of
*unnormalised* states indexed by the measurement record, `Record → qs.State`.
The branch `ψ r` is the (projected, unnormalised) state of the machine on the
run whose measurement outcomes were `r`, and its squared norm is the
probability of that record (`recordProb`). A run starts from `MState.init ψ₀`:
the state `ψ₀` on the empty record, `0` elsewhere.

* `unitary g` applies `eval g` to every branch.
* `measureReset q` splits each branch `r` into `r ++ [false]` and
  `r ++ [true]`: branch `r ++ [b]` is the outcome-`b` Born projection
  `measProj (qubitReg q) b` of `ψ r`, followed by `X q` when `b = true`, so
  that `q` is `|0⟩` again. The empty record, which no measurement produces, is
  sent to `0`. Slot `i` of a record is thus the outcome of the `i`-th
  `measureReset` executed (the convention of `Framework/AbstractMachine/MGate`).
* `ffPhase q j` applies `LowGate.Phase q (ffAngle j r)` to branch `r`: the
  phase angle is a function of that branch's own record.

The model uses only the existing abstract classes (`GateSemanticsCore` for
`unitary` and the reset `X`, `LowerGateClass` for the phase, `MeasureClass` for
the projectors); no new axioms. Proved here: reset correctness
(`measProj_zero_measureResetBranch`), the Born probabilities of the two
children (`norm_sq_measureResetBranch`) and that they sum to the parent's
(`norm_sq_measureResetBranch_false_add_true`), norm preservation of `unitary`
and `ffPhase` (`MGate.norm_eval_unitary`, `MGate.norm_eval_ffPhase`; the phase
case is derived from the `LowerGateClass` ket laws), the support of a run
(`MGate.eval_init_support`: only records of length `P.numMeas` are nonzero) and
conservation of total probability for every program
(`MGate.eval_init_hasSum`: the record probabilities of a run from `ψ₀` sum to
`‖ψ₀‖ ^ 2`). Worked checks are in `MSemanticsTests.lean`.

The probability reading of a branch (its squared norm is the probability of
its record) is meant for families reached from `MState.init`; `MGate.eval` is
defined on every family, but an arbitrary family need not have total
probability `1`.

Which qubits exist: the abstract classes define `measProj (qubitReg q)`,
`Gate.X q` and `LowGate.Phase q θ` for every `q : ℕ`, and the basis encoding
reads a bit `RegEncoding.bit q b` for every `q`, so there is no qubit "outside
the machine" at this level. Measuring a qubit that no other step touches reads
its basis bit (by `MeasureClass.measProj_ket`); in particular, on a state built
from kets whose bit `q` is `0` (e.g. `qs.ket RegEncoding.zero`, all of whose
bits are `0` by `RegEncoding.bit_zero`) it gives outcome `0` with probability
one. A finite concrete machine would have to say what such indices mean; the
abstract classes do not.
-/

namespace Shor

variable {qs : QSemantics} [RegEncoding qs.Basis]

/-- A branching state: one unnormalised state per measurement record. -/
abbrev MState (qs : QSemantics) := Record → qs.State

/-- The initial branching state of a run started in `ψ₀`: `ψ₀` on the empty
record (no measurement yet), `0` on every other record. -/
def MState.init (ψ₀ : qs.State) : MState qs :=
  fun r => if r = [] then ψ₀ else 0

/-- The probability of record `r`: the squared norm of its branch (the branches
are unnormalised, so this is the Born probability of observing `r`). -/
noncomputable def recordProb (ψ : MState qs) (r : Record) : ℝ := ‖ψ r‖ ^ 2

/-- One child of a branch under `measureReset q`: the outcome-`b` projection of
`φ` on qubit `q` (`b = true` is outcome `1`), followed by `X q` when `b = true`
so that `q` ends in `|0⟩`. -/
noncomputable def measureResetBranch [GateSemanticsCore qs] [MeasureClass qs]
    (q : ℕ) (b : Bool) (φ : qs.State) : qs.State :=
  if b then qs.eval (Gate.X q) (MeasureClass.measProj (qubitReg q) 1 φ)
  else MeasureClass.measProj (qubitReg q) 0 φ

/-- Branching-record semantics of `MGate` (see the module docstring).

`measureReset q` sends branch `r ++ [b]` to `measureResetBranch q b (ψ r)` and
the empty record to `0`. The branching reading (squared norm of branch `r` =
Born probability of observing record `r`) holds for families reached from
`MState.init ψ₀` with `‖ψ₀‖ = 1`; see `MGate.eval_init_hasSum`. -/
noncomputable def MGate.eval [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] :
    MGate → MState qs → MState qs
  | .unitary g, ψ => fun r => qs.eval g (ψ r)
  | .seq a b, ψ => MGate.eval b (MGate.eval a ψ)
  | .measureReset q, ψ => fun r =>
      if h : r = [] then 0 else measureResetBranch q (r.getLast h) (ψ r.dropLast)
  | .ffPhase q j, ψ => fun r => LowerGateClass.evalL (LowGate.Phase q (ffAngle j r)) (ψ r)

namespace MGate

variable [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]

@[simp] theorem eval_unitary (g : Gate) (ψ : MState qs) (r : Record) :
    (MGate.unitary g).eval ψ r = qs.eval g (ψ r) := rfl

@[simp] theorem eval_seq (a b : MGate) (ψ : MState qs) :
    (MGate.seq a b).eval ψ = b.eval (a.eval ψ) := rfl

@[simp] theorem eval_ffPhase (q j : ℕ) (ψ : MState qs) (r : Record) :
    (MGate.ffPhase q j).eval ψ r
      = LowerGateClass.evalL (LowGate.Phase q (ffAngle j r)) (ψ r) := rfl

/-- No measurement produces the empty record. -/
@[simp] theorem eval_measureReset_nil (q : ℕ) (ψ : MState qs) :
    (MGate.measureReset q).eval ψ [] = 0 := rfl

/-- Branch `r ++ [b]` after `measureReset q` is the outcome-`b` child of branch `r`. -/
@[simp] theorem eval_measureReset_append (q : ℕ) (ψ : MState qs) (r : Record) (b : Bool) :
    (MGate.measureReset q).eval ψ (r ++ [b]) = measureResetBranch q b (ψ r) := by
  simp [MGate.eval]

end MGate

/-! ## Reset correctness and probabilities -/

section Laws

variable [GateSemanticsCore qs] [MeasureClass qs]

omit [MeasureClass qs] in
/-- A gate sends the zero state to zero. -/
theorem MGate.gate_eval_zero_state (U : Gate) : qs.eval U (0 : qs.State) = 0 := by
  have h := GateSemanticsCore.eval_smul (qs := qs) U (0 : ℂ) 0
  simpa using h

/-- The single-qubit register `qubitReg q` has width 1. -/
private theorem regSize_qubitReg (q : ℕ) : regSize (qubitReg q) = 1 := rfl

omit [GateSemanticsCore qs] [MeasureClass qs] in
/-- Reading `qubitReg q` as a number gives `1` only when bit `q` is set. -/
private theorem bit_of_toNat_qubitReg_eq_one (q : ℕ) (b : qs.Basis)
    (h : RegEncoding.toNat (qubitReg q) b = 1) : RegEncoding.bit q b = true := by
  have := RegEncoding.bit_eq_testBit_toNat (qubitReg q) b ⟨0, by simp [regSize_qubitReg]⟩
  rw [h] at this
  change RegEncoding.bit q b = Nat.testBit 1 0 at this
  simpa using this

/-- Flipping qubit `q` after projecting it onto `|1⟩` leaves it in `|0⟩`. -/
theorem measProj_zero_X_measProj_one [PauliXSemantics qs] (q : ℕ) (φ : qs.State) :
    MeasureClass.measProj (qubitReg q) 0
        (qs.eval (Gate.X q) (MeasureClass.measProj (qubitReg q) 1 φ))
      = qs.eval (Gate.X q) (MeasureClass.measProj (qubitReg q) 1 φ) := by
  refine qs.state_induction
    (fun φ => MeasureClass.measProj (qubitReg q) 0
        (qs.eval (Gate.X q) (MeasureClass.measProj (qubitReg q) 1 φ))
      = qs.eval (Gate.X q) (MeasureClass.measProj (qubitReg q) 1 φ)) ?_ ?_ ?_ ?_ φ
  · simp [MGate.gate_eval_zero_state]
  · intro ψ φ hψ hφ
    simp only [map_add, GateSemanticsCore.eval_add, QSemantics.eval] at hψ hφ ⊢
    rw [hψ, hφ]
  · intro a ψ hψ
    simp only [map_smul, GateSemanticsCore.eval_smul, QSemantics.eval] at hψ ⊢
    rw [hψ]
  · intro b
    rw [MeasureClass.measProj_ket]
    split_ifs with h1
    · have hbit := bit_of_toNat_qubitReg_eq_one q b h1
      rw [PauliXSemantics.eval_X_ket, MeasureClass.measProj_ket]
      have h0 : RegEncoding.toNat (qubitReg q)
          (RegEncoding.writeNat (qubitReg q) (if RegEncoding.bit q b then 0 else 1) b) = 0 := by
        simp only [hbit, ite_true]
        exact RegEncoding.toNat_writeNat_of_lt _ _ _ (by simp [ASize, regSize_qubitReg])
      simp [h0]
    · simp [MGate.gate_eval_zero_state]

/-- Both children of `measureReset q` have qubit `q` in `|0⟩`. -/
theorem measProj_zero_measureResetBranch [PauliXSemantics qs] (q : ℕ) (b : Bool) (φ : qs.State) :
    MeasureClass.measProj (qubitReg q) 0 (measureResetBranch q b φ)
      = measureResetBranch q b φ := by
  cases b
  · exact MeasureClass.measProj_idempotent qs _ _ _
  · exact measProj_zero_X_measProj_one q φ

/-- The outcome-`b` child has the Born probability of outcome `b` (the reset
`X` preserves norms). -/
theorem norm_sq_measureResetBranch (q : ℕ) (b : Bool) (φ : qs.State) :
    ‖measureResetBranch q b φ‖ ^ 2
      = MeasureClass.probMeas (qubitReg q) (if b then 1 else 0) φ := by
  cases b
  · simp [measureResetBranch, MeasureClass.probMeas]
  · simp only [measureResetBranch, MeasureClass.probMeas, ite_true]
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
    simp only [QSemantics.eval, GateSemanticsCore.inner_preserved]

omit [GateSemanticsCore qs] in
/-- Born completeness on one qubit: the two outcome probabilities sum to the
squared norm. -/
theorem probMeas_qubitReg_zero_add_one (q : ℕ) (φ : qs.State) :
    MeasureClass.probMeas (qubitReg q) 0 φ + MeasureClass.probMeas (qubitReg q) 1 φ
      = ‖φ‖ ^ 2 := by
  have hsum : MeasureClass.measProj (qubitReg q) 0 φ + MeasureClass.measProj (qubitReg q) 1 φ
      = φ := by
    have h := MeasureClass.measProj_complete (qs := qs) (qubitReg q) φ
    rw [regSize_qubitReg] at h
    simpa [Fin.sum_univ_two] using h
  have horth : inner ℂ (MeasureClass.measProj (qubitReg q) 0 φ)
      (MeasureClass.measProj (qubitReg q) 1 φ) = 0 := by
    rw [MeasureClass.measProj_selfAdjoint, MeasureClass.measProj_orthogonal _ _ _ _ (by decide)]
    simp
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [hsum] at this
  simp only [MeasureClass.probMeas, sq]
  exact this.symm

/-- Measurement and reset of a branch of squared norm `p` splits it into two
children of squared norms summing to `p`. -/
theorem norm_sq_measureResetBranch_false_add_true (q : ℕ) (φ : qs.State) :
    ‖measureResetBranch q false φ‖ ^ 2 + ‖measureResetBranch q true φ‖ ^ 2 = ‖φ‖ ^ 2 := by
  rw [norm_sq_measureResetBranch, norm_sq_measureResetBranch]
  exact probMeas_qubitReg_zero_add_one q φ

end Laws

/-! ## Norm preservation of the unitary steps -/

section Norms

/-- A low-level gate sends the zero state to zero. -/
theorem MGate.lowGate_evalL_zero_state [LowerGateClass qs] (L : LowGate) :
    LowerGateClass.evalL L (0 : qs.State) = 0 := by
  simpa using LowerGateClass.evalL_smul (qs := qs) L (0 : ℂ) 0

/-- A unitary `Gate` preserves the norm (from `GateSemanticsCore.inner_preserved`). -/
theorem norm_eval_gate [GateSemanticsCore qs] (U : Gate) (φ : qs.State) :
    ‖qs.eval U φ‖ = ‖φ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (qs.eval U φ), norm_eq_sqrt_re_inner (𝕜 := ℂ) φ]
  simp only [QSemantics.eval, GateSemanticsCore.inner_preserved]

/-- The phase gate is diagonal on kets with a scalar of modulus one. -/
private theorem evalL_Phase_ket_smul [LowerGateClass qs] (q : ℕ) (θ : Angle) (b : qs.Basis) :
    LowerGateClass.evalL (LowGate.Phase q θ) (qs.ket b)
      = (if RegEncoding.bit q b then Complex.exp (((Angle.toReal θ : ℝ) : ℂ) * Complex.I)
          else 1) • qs.ket b := by
  rw [LowerGateClass.evalL_Phase_ket]
  split_ifs <;> simp

private theorem mul_conj_phase_scalar (c : Prop) [Decidable c] (x : ℝ) :
    (if c then Complex.exp ((x : ℂ) * Complex.I) else 1)
      * (starRingEnd ℂ) (if c then Complex.exp ((x : ℂ) * Complex.I) else 1) = 1 := by
  rw [Complex.mul_conj']
  split_ifs
  · simp [Complex.norm_exp_ofReal_mul_I]
  · simp

/-- The phase gate `LowGate.Phase q θ` preserves inner products. Derived from
the `LowerGateClass` laws (additivity, homogeneity, its action on kets) and
orthonormality of kets; no extra assumption. -/
theorem inner_evalL_Phase [LowerGateClass qs] (q : ℕ) (θ : Angle) (ψ φ : qs.State) :
    inner ℂ (LowerGateClass.evalL (LowGate.Phase q θ) ψ)
        (LowerGateClass.evalL (LowGate.Phase q θ) φ) = inner ℂ ψ φ := by
  set P := LowGate.Phase q θ
  -- first argument a ket, by induction on the second
  have hket : ∀ b φ, inner ℂ (LowerGateClass.evalL P (qs.ket b))
      (LowerGateClass.evalL P φ) = inner ℂ (qs.ket b) φ := by
    intro b φ
    refine qs.state_induction (fun φ => inner ℂ (LowerGateClass.evalL P (qs.ket b))
      (LowerGateClass.evalL P φ) = inner ℂ (qs.ket b) φ) ?_ ?_ ?_ ?_ φ
    · simp [MGate.lowGate_evalL_zero_state]
    · intro ψ φ hψ hφ
      rw [LowerGateClass.evalL_add, inner_add_right, inner_add_right, hψ, hφ]
    · intro a ψ hψ
      rw [LowerGateClass.evalL_smul, inner_smul_right, inner_smul_right, hψ]
    · intro b'
      simp only [P, evalL_Phase_ket_smul, inner_smul_left, inner_smul_right]
      by_cases hb : b = b'
      · subst hb
        rw [← mul_assoc, mul_conj_phase_scalar, one_mul]
      · rw [qs.ket_inner_eq_zero_of_ne hb]
        simp
  refine qs.state_induction (fun ψ => ∀ φ, inner ℂ (LowerGateClass.evalL P ψ)
    (LowerGateClass.evalL P φ) = inner ℂ ψ φ) ?_ ?_ ?_ ?_ ψ φ
  · intro φ; simp [MGate.lowGate_evalL_zero_state]
  · intro ψ ψ' hψ hψ' φ
    rw [LowerGateClass.evalL_add, inner_add_left, inner_add_left, hψ, hψ']
  · intro a ψ hψ φ
    rw [LowerGateClass.evalL_smul, inner_smul_left, inner_smul_left, hψ]
  · exact hket

/-- The phase gate `LowGate.Phase q θ` preserves the norm. -/
theorem norm_evalL_phase [LowerGateClass qs] (q : ℕ) (θ : Angle) (φ : qs.State) :
    ‖LowerGateClass.evalL (LowGate.Phase q θ) φ‖ = ‖φ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (LowerGateClass.evalL (LowGate.Phase q θ) φ),
    norm_eq_sqrt_re_inner (𝕜 := ℂ) φ, inner_evalL_Phase]

variable [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]

/-- `unitary g` preserves the norm of every branch. -/
theorem MGate.norm_eval_unitary (g : Gate) (ψ : MState qs) (r : Record) :
    ‖(MGate.unitary g).eval ψ r‖ = ‖ψ r‖ := by
  rw [MGate.eval_unitary, norm_eval_gate]

/-- `ffPhase q j` preserves the norm of every branch. -/
theorem MGate.norm_eval_ffPhase (q j : ℕ) (ψ : MState qs) (r : Record) :
    ‖(MGate.ffPhase q j).eval ψ r‖ = ‖ψ r‖ := by
  rw [MGate.eval_ffPhase, norm_evalL_phase]

end Norms

/-! ## Support and conservation of total probability -/

section Conservation

variable [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]

namespace MGate

/-- Support: if every branch whose record does not have length `k` is zero,
then after `P` every branch whose record does not have length
`k + P.numMeas` is zero. -/
theorem eval_support (P : MGate) {ψ : MState qs} {k : ℕ}
    (h : ∀ r : Record, r.length ≠ k → ψ r = 0) :
    ∀ r : Record, r.length ≠ k + P.numMeas → P.eval ψ r = 0 := by
  induction P generalizing ψ k with
  | unitary g =>
    intro r hr
    simp only [numMeas, Nat.add_zero] at hr
    rw [eval_unitary, h r hr, gate_eval_zero_state]
  | ffPhase q j =>
    intro r hr
    simp only [numMeas, Nat.add_zero] at hr
    rw [eval_ffPhase, h r hr, lowGate_evalL_zero_state]
  | seq a b iha ihb =>
    intro r hr
    rw [eval_seq]
    exact ihb (iha h) r (by simpa [numMeas, Nat.add_assoc] using hr)
  | measureReset q =>
    intro r hr
    rcases List.eq_nil_or_concat r with rfl | ⟨r₀, b, rfl⟩
    · rfl
    · rw [List.concat_eq_append, eval_measureReset_append]
      have h0 : ψ r₀ = 0 := h r₀ (by
        intro hl; apply hr; simp [numMeas, hl])
      rw [h0]
      cases b <;> simp [measureResetBranch, gate_eval_zero_state]

/-- Started from `MState.init ψ₀`, a program `P` leaves only the branches whose
record has exactly `P.numMeas` entries (one per executed `measureReset`)
possibly nonzero. -/
theorem eval_init_support (P : MGate) (ψ₀ : qs.State) (r : Record)
    (h : r.length ≠ P.numMeas) : P.eval (MState.init ψ₀) r = 0 := by
  refine eval_support P (k := 0) ?_ r (by simpa using h)
  intro r' hr'
  have : r' ≠ [] := fun h' => hr' (by simp [h'])
  simp [MState.init, this]

/-- `measureReset q` conserves total probability: if the squared norms of the
branches of `ψ` sum to `s`, so do those of `(measureReset q).eval ψ`. -/
theorem hasSum_recordProb_measureReset (q : ℕ) {ψ : MState qs} {s : ℝ}
    (h : HasSum (recordProb ψ) s) :
    HasSum (recordProb ((MGate.measureReset q).eval ψ)) s := by
  set F : Bool → Record → ℝ := fun b r => ‖measureResetBranch q b (ψ r)‖ ^ 2 with hF
  have hsplit : ∀ r, F false r + F true r = recordProb ψ r := fun r =>
    norm_sq_measureResetBranch_false_add_true q (ψ r)
  have hsum : ∀ b, Summable (F b) := by
    intro b
    refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_) h.summable
    have h0 : 0 ≤ F false r := by positivity
    have h1 : 0 ≤ F true r := by positivity
    rw [← hsplit r]; cases b <;> linarith
  obtain ⟨a₀, ha₀⟩ := hsum false
  obtain ⟨a₁, ha₁⟩ := hsum true
  have hs : a₀ + a₁ = s := by
    have := ha₀.add ha₁
    exact this.unique (by simpa [Pi.add_def, hsplit] using h)
  -- put each child family on `Record × Bool`
  have hslice : ∀ (b : Bool) (a : ℝ), HasSum (F b) a →
      HasSum (fun p : Record × Bool => if p.2 = b then F b p.1 else 0) a := by
    intro b a hb
    have hinj : Function.Injective (fun r : Record => (r, b)) :=
      fun r r' hrr => (Prod.mk.inj hrr).1
    rw [← hinj.hasSum_iff]
    · convert hb using 1
      funext r
      simp
    · rintro ⟨r, b'⟩ hr
      have : b' ≠ b := fun hb' => hr ⟨r, by simp [hb']⟩
      simp [this]
  have hprod : HasSum (fun p : Record × Bool => F p.2 p.1) s := by
    rw [← hs]
    convert (hslice false a₀ ha₀).add (hslice true a₁ ha₁) using 1
    funext ⟨r, b⟩
    cases b <;> simp
  -- and pull back along `(r, b) ↦ r ++ [b]`
  have hinj : Function.Injective (fun p : Record × Bool => p.1 ++ [p.2]) := by
    rintro ⟨r, b⟩ ⟨r', b'⟩ hrr
    have := List.append_inj' hrr rfl
    simp_all
  rw [← hinj.hasSum_iff]
  · convert hprod using 1
    funext ⟨r, b⟩
    simp [recordProb, hF]
  · intro r hr
    rcases List.eq_nil_or_concat r with rfl | ⟨r₀, b, rfl⟩
    · simp [recordProb]
    · exact absurd ⟨(r₀, b), by simp⟩ hr

/-- Every `MGate` program conserves total probability: if the record
probabilities of `ψ` sum to `s`, so do those of `P.eval ψ`. -/
theorem hasSum_recordProb_eval (P : MGate) {ψ : MState qs} {s : ℝ}
    (h : HasSum (recordProb ψ) s) : HasSum (recordProb (P.eval ψ)) s := by
  induction P generalizing ψ s with
  | unitary g =>
    have : recordProb ((MGate.unitary g).eval ψ) = recordProb ψ := by
      funext r; simp only [recordProb, norm_eval_unitary]
    rwa [this]
  | ffPhase q j =>
    have : recordProb ((MGate.ffPhase q j).eval ψ) = recordProb ψ := by
      funext r; simp only [recordProb, norm_eval_ffPhase]
    rwa [this]
  | seq a b iha ihb => exact ihb (iha h)
  | measureReset q => exact hasSum_recordProb_measureReset q h

omit [RegEncoding qs.Basis] [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] in
/-- The initial branching state has total probability `‖ψ₀‖ ^ 2`. -/
theorem hasSum_recordProb_init (ψ₀ : qs.State) :
    HasSum (recordProb (MState.init ψ₀)) (‖ψ₀‖ ^ 2) := by
  have := hasSum_single (f := recordProb (MState.init ψ₀)) [] (fun r hr => by
    simp [recordProb, MState.init, hr])
  simpa [recordProb, MState.init] using this

/-- **Conservation of probability.** For every program `P` and every initial
state `ψ₀`, the record probabilities of the run of `P` from `ψ₀` sum to
`‖ψ₀‖ ^ 2` (to `1` for a normalised `ψ₀`). -/
theorem eval_init_hasSum (P : MGate) (ψ₀ : qs.State) :
    HasSum (fun r => recordProb (P.eval (MState.init ψ₀)) r) (‖ψ₀‖ ^ 2) :=
  hasSum_recordProb_eval P (hasSum_recordProb_init ψ₀)

end MGate

end Conservation

end Shor
