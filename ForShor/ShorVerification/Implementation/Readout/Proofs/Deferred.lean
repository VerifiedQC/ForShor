import ForShor.ShorVerification.Implementation.Readout.Proofs.Basic

/-!
# Readout: the one-round identity and the deferred-measurement lemma

Two facts about the measurement language `MGate`
(`Framework/AbstractMachine/MGate.lean`, `Framework/Semantics/MSemantics.lean`)
for the semiclassical readout, which recycles ONE control qubit `c`.

## One readout round (`round_branch`)

Round `j` of the readout, controlled gate `U` (control `c`), is

  `readoutRound c U j = H c ;; unitary U ;; ffPhase c j ;; H c ;; measureReset c`.

Let `φ` be the branch at record `r` before the round, with qubit `c` in `|0⟩`.
Write `T φ := X c (U (X c φ))` (`uncontrolledAction c U φ`): the action of `U`
on the copy of `φ` whose control is `1`, with the control flipped back to `0`.
Then the round's child branch at record `r ++ [b]` is exactly

  `(1/2) • (φ + s_b • exp(iπ · ffAngle j r) • T φ)`,  `s_false = 1`, `s_true = -1`

(Griffiths-Niu). The child has qubit `c` in `|0⟩` again, so rounds chain.
The hypotheses on `U` are stated on the one state they are used at
(`round_branch`), or once for all states (`ControlledOn`,
`round_branch_of_controlledOn`); the real controlled modular multiplier
satisfies the pointwise ones on every state in the span of basis kets with
control `0` and data in range (`InRange`, `idealCtrlModMul_round_hyps_ket`,
`round_hyps_of_inRange`), and a round keeps every branch in that span
(`inRange_round_child`, `inRange_round_eval`), so an induction over rounds
can apply `round_branch` at every step.

## Deferred measurement (`deferred_measurement`)

The single-qubit deferred-measurement principle in the branching-record
model: measuring (and resetting) qubit `q` and then applying `U b` when the
outcome was `b` (`condOnLast U`) gives the SAME branching state (every branch,
not only every record probability) as applying the `q`-controlled gate
(`U false` on the `q = 0` part, `U true` on the `q = 1` part) and measuring
`q` afterwards, provided both `U b` commute with the Born projectors of qubit
`q` and with `X q` (they act on other qubits only).

Everything is derived from the existing classes (`GateSemanticsCore`,
`LowerGateClass`, `MeasureClass`, `HadamardSemantics`, `PauliXSemantics`,
`IdealCtrlModMulExactSemantics`); no new axioms or class fields.
-/

namespace Shor
namespace Readout

open MeasureClass

variable {qs : QSemantics} [RegEncoding qs.Basis]
  [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]

/-! ## One readout round -/

/-- Round `j` of the semiclassical readout on control qubit `c` with the
controlled gate `U`:
`H c ;; unitary U ;; ffPhase c j ;; H c ;; measureReset c`. -/
def readoutRound (c : ℕ) (U : Gate) (j : ℕ) : MGate :=
  .seq (.unitary (Gate.H c))
    (.seq (.unitary U) (.seq (.ffPhase c j) (.seq (.unitary (Gate.H c)) (.measureReset c))))

/-- `T φ = X c (U (X c φ))`: on a state `φ` with qubit `c` in `|0⟩`, the action
of the `c`-controlled gate `U` on the control-`1` copy of `φ`, with the control
flipped back to `0` (the "uncontrolled" action of `U`). -/
noncomputable def uncontrolledAction (c : ℕ) (U : Gate) (φ : qs.State) : qs.State :=
  qs.eval (Gate.X c) (qs.eval U (qs.eval (Gate.X c) φ))

/-- The sign `(-1)^b` of the outcome-`b` child: `1` for outcome `0`, `-1` for
outcome `1`. -/
def outcomeSign (b : Bool) : ℂ := if b then -1 else 1

/-- **One readout round (Griffiths-Niu).** Let the branch of `ψ` at record `r`
have qubit `c` in `|0⟩` (`hφ`), and let `U` act on it as follows:
`U` fixes it (`hU0`: on the control-`0` part, `U` is the identity), and `U`
keeps its control-`1` copy `X c (ψ r)` in the control-`1` subspace (`hU1`).
Then round `j` sends that branch to the child at record `r ++ [b]`

  `(1/2) • (ψ r + ((-1)^b · exp(iπ · ffAngle j r)) • X c (U (X c (ψ r))))`.

(`Angle.toReal θ = θ · π`; the phase angle is read from the record `r` before
the round's own measurement.) -/
theorem round_branch [HadamardSemantics qs] [PauliXSemantics qs]
    (c : ℕ) (U : Gate) (j : ℕ) (ψ : MState qs) (r : Record) (b : Bool)
    (hφ : measProj (qubitReg c) 0 (ψ r) = ψ r)
    (hU0 : qs.eval U (ψ r) = ψ r)
    (hU1 : measProj (qubitReg c) 1 (qs.eval U (qs.eval (Gate.X c) (ψ r)))
      = qs.eval U (qs.eval (Gate.X c) (ψ r))) :
    (readoutRound c U j).eval ψ (r ++ [b])
      = (1 / 2 : ℂ) • (ψ r + (outcomeSign b
          * Complex.exp (((Angle.toReal (ffAngle j r) : ℝ) : ℂ) * Complex.I))
          • uncontrolledAction c U (ψ r)) := by
  set φ := ψ r with hφdef
  set χ := qs.eval U (qs.eval (Gate.X c) φ) with hχ
  set E := Complex.exp (((Angle.toReal (ffAngle j r) : ℝ) : ℂ) * Complex.I) with hE
  set k : ℂ := 1 / (Real.sqrt 2 : ℂ) with hk
  have hT : uncontrolledAction c U φ = qs.eval (Gate.X c) χ := rfl
  -- where each piece lives with respect to qubit `c`
  have hXφ1 : measProj (qubitReg c) 1 (qs.eval (Gate.X c) φ) = qs.eval (Gate.X c) φ := by
    have := measProj_one_X_measProj_zero c φ; rwa [hφ] at this
  have hT0 : measProj (qubitReg c) 0 (qs.eval (Gate.X c) χ) = qs.eval (Gate.X c) χ := by
    have := measProj_zero_X_measProj_one c χ; rwa [hU1] at this
  have hXχ : qs.eval (Gate.X c) (qs.eval (Gate.X c) χ) = χ := gate_X_X c χ
  have hφ1 := measProj_of_measProj_ne c 1 0 φ hφ (by decide)
  have hXφ0 := measProj_of_measProj_ne c 0 1 _ hXφ1 (by decide)
  have hχ0 := measProj_of_measProj_ne c 0 1 χ hU1 (by decide)
  have hT1 := measProj_of_measProj_ne c 1 0 _ hT0 (by decide)
  -- the four steps before the measurement
  have s1 : qs.eval (Gate.H c) φ = k • (φ + qs.eval (Gate.X c) φ) := by
    have := H_measProj_zero c φ; rwa [hφ] at this
  have s2 : qs.eval U (k • (φ + qs.eval (Gate.X c) φ)) = k • (φ + χ) := by
    rw [gate_eval_smul, gate_eval_add, hU0]
  have s3 : LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) (k • (φ + χ))
      = k • (φ + E • χ) := by
    rw [LowerGateClass.evalL_smul, LowerGateClass.evalL_add]
    have h0 := phase_measProj_zero c (ffAngle j r) φ
    have h1 := phase_measProj_one c (ffAngle j r) χ
    rw [hφ] at h0; rw [hU1] at h1
    rw [h0, h1]
  have s4 : qs.eval (Gate.H c) (k • (φ + E • χ))
      = k • (k • (φ + qs.eval (Gate.X c) φ)
          + E • (k • (qs.eval (Gate.X c) χ - χ))) := by
    have hHχ := H_X_measProj_zero c (qs.eval (Gate.X c) χ)
    rw [hT0, hXχ] at hHχ
    rw [gate_eval_smul, gate_eval_add, gate_eval_smul, s1, hHχ]
  simp only [readoutRound, MGate.eval_seq, MGate.eval_measureReset_append,
    MGate.eval_unitary, MGate.eval_ffPhase]
  rw [← hφdef, s1, s2, s3, s4, hT]
  have hkk : k * k = 1 / 2 := invSqrtTwo_mul_self
  cases b
  · simp only [measureResetBranch, Bool.false_eq_true, ite_false, map_smul, map_add, map_sub,
      hφ, hXφ0, hT0, hχ0, outcomeSign]
    rw [show k • (k • (φ + (0 : qs.State)) + E • (k • (qs.eval (Gate.X c) χ - 0)))
        = (k * k) • (φ + E • qs.eval (Gate.X c) χ) by module, hkk]
    module
  · simp only [measureResetBranch, ite_true, map_smul, map_add, map_sub,
      hφ1, hXφ1, hT1, hU1, outcomeSign]
    simp only [zero_add, zero_sub, gate_eval_smul, gate_eval_add, gate_eval_neg, gate_X_X]
    rw [show k • (k • φ + E • (k • -qs.eval (Gate.X c) χ))
        = (k * k) • (φ + (-1 * E) • qs.eval (Gate.X c) χ) by module, hkk]

/-- A round ends with a measurement, so it has no branch at the empty record. -/
theorem round_branch_nil (c : ℕ) (U : Gate) (j : ℕ) (ψ : MState qs) :
    (readoutRound c U j).eval ψ [] = 0 := by
  simp [readoutRound]

/-- Every branch after a round has the control qubit `c` back in `|0⟩`, so the
next round's hypothesis `hφ` holds for it. -/
theorem round_branch_qubit_zero [PauliXSemantics qs]
    (c : ℕ) (U : Gate) (j : ℕ) (ψ : MState qs) (r : Record) :
    measProj (qubitReg c) 0 ((readoutRound c U j).eval ψ r)
      = (readoutRound c U j).eval ψ r := by
  rcases List.eq_nil_or_concat r with rfl | ⟨r₀, b, rfl⟩
  · rw [round_branch_nil, map_zero]
  · simp only [readoutRound, MGate.eval_seq, List.concat_eq_append,
      MGate.eval_measureReset_append]
    exact measProj_zero_measureResetBranch c b _

/-- `U` is a gate controlled by qubit `c` in the sense the round needs, on all
states: it is the identity on the control-`0` subspace, and it maps the
control-`1` subspace into itself.

This global form is NOT provable for `Gate.idealCtrlModMul` from the classes:
`IdealCtrlModMulExactSemantics` fixes its action only on kets whose data value
is `< N`, and leaves it unspecified elsewhere. For that gate use the pointwise
`round_branch` with `InRange` (`round_hyps_of_inRange`). `ControlledOn` serves
gates specified on every ket (e.g. `CNOT c t`, `DeferredTests.controlledOn_CNOT`). -/
def ControlledOn (c : ℕ) (U : Gate) : Prop :=
  (∀ ψ : qs.State, qs.eval U (measProj (qubitReg c) 0 ψ) = measProj (qubitReg c) 0 ψ) ∧
  (∀ ψ : qs.State, measProj (qubitReg c) 1 (qs.eval U (measProj (qubitReg c) 1 ψ))
      = qs.eval U (measProj (qubitReg c) 1 ψ))

/-- `round_branch` for a gate `U` controlled by `c` on all states: only the
hypothesis that the incoming branch has qubit `c` in `|0⟩` remains. -/
theorem round_branch_of_controlledOn [HadamardSemantics qs] [PauliXSemantics qs]
    (c : ℕ) (U : Gate) (hU : ControlledOn (qs := qs) c U) (j : ℕ) (ψ : MState qs)
    (r : Record) (b : Bool) (hφ : measProj (qubitReg c) 0 (ψ r) = ψ r) :
    (readoutRound c U j).eval ψ (r ++ [b])
      = (1 / 2 : ℂ) • (ψ r + (outcomeSign b
          * Complex.exp (((Angle.toReal (ffAngle j r) : ℝ) : ℂ) * Complex.I))
          • uncontrolledAction c U (ψ r)) := by
  refine round_branch c U j ψ r b hφ ?_ ?_
  · have h := hU.1 (ψ r); rwa [hφ] at h
  · have h := measProj_one_X_measProj_zero c (ψ r)
    rw [hφ] at h
    rw [← h]
    exact hU.2 _

omit [LowerGateClass qs] in
/-- The real use: the ideal controlled modular multiplier by `a` modulo `N`
on `data`, with control `c` (outside `data`), meets the hypotheses `hU0` and
`hU1` of `round_branch` on every basis ket `|x⟩` with control bit `0` and data
value `x_data < N`, and its uncontrolled action on that ket multiplies the data
value by `a` modulo `N`:
`X c (U (X c |x⟩)) = |x with data := a · x_data mod N⟩`.
(Off `x_data < N` the gate's action is unspecified by the classes, so this is
stated per ket; `round_hyps_of_inRange` extends it to the span `InRange`.) -/
theorem idealCtrlModMul_round_hyps_ket [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ) (data : Reg) (c : ℕ) (x : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hx : RegEncoding.toNat data x < N) (hxc : RegEncoding.bit c x = false) :
    measProj (qubitReg c) 0 (qs.ket x) = qs.ket x ∧
    qs.eval (Gate.idealCtrlModMul a N data c) (qs.ket x) = qs.ket x ∧
    measProj (qubitReg c) 1
        (qs.eval (Gate.idealCtrlModMul a N data c) (qs.eval (Gate.X c) (qs.ket x)))
      = qs.eval (Gate.idealCtrlModMul a N data c) (qs.eval (Gate.X c) (qs.ket x)) ∧
    uncontrolledAction c (Gate.idealCtrlModMul a N data c) (qs.ket x)
      = qs.ket (RegEncoding.writeNat data (a * RegEncoding.toNat data x % N) x) := by
  set y := RegEncoding.writeNat (qubitReg c) 1 x with hy
  have hdisj : Disjoint (qubitReg c) data := by
    simp [Disjoint, qubitReg, Reg.singleton, hc]
  have hcq : ∀ q ∈ data.qubits, q ∉ (qubitReg c).qubits := by
    intro q hq hqc
    rw [mem_qubitReg] at hqc
    exact hc (hqc ▸ hq)
  have hX : qs.eval (Gate.X c) (qs.ket x) = qs.ket y := by
    rw [PauliXSemantics.eval_X_ket, hxc]; rfl
  have hyc : RegEncoding.bit c y = true := by
    rw [hy, bit_qubitReg_writeNat _ _ _ (by norm_num)]; rfl
  have hyd : RegEncoding.toNat data y = RegEncoding.toNat data x :=
    toNat_eq_of_bits data (fun q hq => RegEncoding.bit_writeNat_out _ _ _ _ (hcq q hq))
  have hUx : qs.eval (Gate.idealCtrlModMul a N data c) (qs.ket x) = qs.ket x := by
    rw [IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact a N data c x
      hN hNdata ha hc hx, hxc]
    simp only [Bool.false_eq_true, ite_false]
    rw [RegEncoding.writeNat_toNat]
  set z := RegEncoding.writeNat data (a * RegEncoding.toNat data x % N) y with hz
  have hUy : qs.eval (Gate.idealCtrlModMul a N data c) (qs.ket y) = qs.ket z := by
    rw [IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact a N data c y
      hN hNdata ha hc (hyd ▸ hx), hyc, hyd]
    rfl
  have hzc : RegEncoding.bit c z = true := by
    rw [hz, RegEncoding.bit_writeNat_out _ _ _ _ hc, hyc]
  refine ⟨?_, hUx, ?_, ?_⟩
  · rw [measProj_qubitReg_ket, hxc]; simp
  · rw [hX, hUy, measProj_qubitReg_ket, hzc]; simp
  · unfold uncontrolledAction
    rw [hX, hUy, PauliXSemantics.eval_X_ket, hzc]
    simp only [ite_true]
    congr 1
    rw [hz, writeNat_comm_of_disjoint (qubitReg c) data hdisj, hy,
      writeNat_qubitReg_writeNat _ _ _ _ (by norm_num) (by norm_num)]
    have h0 := writeNat_qubitReg_self c x
    rw [hxc] at h0
    simp only [Bool.false_eq_true, ite_false] at h0
    rw [h0]

/-! ## Staying in range over rounds (the real multiplier) -/

/-- `φ` is a finite linear combination of basis kets `|x⟩` with control bit
`c` equal to `0` and data value `< N`: the subspace on which the classes
specify `Gate.idealCtrlModMul _ N data c` and on which `round_branch` applies
to it. (Stated as membership in the `ℂ`-span; `inRange_iff_exists_sum` gives
the explicit finite-sum form.) -/
def InRange (c : ℕ) (data : Reg) (N : ℕ) (φ : qs.State) : Prop :=
  φ ∈ Submodule.span ℂ
    (qs.ket '' {x | RegEncoding.bit c x = false ∧ RegEncoding.toNat data x < N})

omit [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] in
/-- `InRange` is exactly: `φ = ∑ x ∈ s, w x • |x⟩` for a finite set `s` of
basis states with control bit `0` and data value `< N`. -/
theorem inRange_iff_exists_sum (c : ℕ) (data : Reg) (N : ℕ) (φ : qs.State) :
    InRange c data N φ ↔ ∃ (s : Finset qs.Basis) (w : qs.Basis → ℂ),
      φ = ∑ x ∈ s, w x • qs.ket x ∧
      ∀ x ∈ s, RegEncoding.bit c x = false ∧ RegEncoding.toNat data x < N := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 h
    refine ⟨l.support, l, ?_, fun x hx => hl (Finset.mem_coe.2 hx)⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  · rintro ⟨s, w, rfl, hs⟩
    exact Submodule.sum_mem _ (fun x hx =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hs x hx, rfl⟩))

omit [LowerGateClass qs] in
/-- On every `InRange` state `φ` the ideal controlled multiplier
`U = idealCtrlModMul a N data c` meets the three hypotheses of
`round_branch`: `φ` has `c` in `|0⟩`, `U φ = φ`, and `U (X c φ)` lies in the
`c = 1` subspace. -/
theorem round_hyps_of_inRange [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ) (data : Reg) (c : ℕ)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (φ : qs.State) (h : InRange c data N φ) :
    measProj (qubitReg c) 0 φ = φ ∧
    qs.eval (Gate.idealCtrlModMul a N data c) φ = φ ∧
    measProj (qubitReg c) 1
        (qs.eval (Gate.idealCtrlModMul a N data c) (qs.eval (Gate.X c) φ))
      = qs.eval (Gate.idealCtrlModMul a N data c) (qs.eval (Gate.X c) φ) := by
  unfold InRange at h
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hyc, hyd⟩, rfl⟩ := hx
    obtain ⟨h1, h2, h3, -⟩ := idealCtrlModMul_round_hyps_ket a N data c y hN hNdata ha hc hyd hyc
    exact ⟨h1, h2, h3⟩
  | zero => simp [MGate.gate_eval_zero_state]
  | add x y _ _ hx hy =>
    refine ⟨by rw [map_add, hx.1, hy.1], by rw [gate_eval_add, hx.2.1, hy.2.1], ?_⟩
    rw [gate_eval_add, gate_eval_add, map_add, hx.2.2, hy.2.2]
  | smul z x _ hx =>
    refine ⟨by rw [map_smul, hx.1], by rw [gate_eval_smul, hx.2.1], ?_⟩
    rw [gate_eval_smul, gate_eval_smul, map_smul, hx.2.2]

omit [LowerGateClass qs] in
/-- The uncontrolled action `X c (U (X c ·))` of `U = idealCtrlModMul a N data c`
maps `InRange` states to `InRange` states (on kets it replaces the data value
`x_data < N` by `a · x_data mod N < N` and leaves `c` at `0`). -/
theorem inRange_uncontrolledAction [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ) (data : Reg) (c : ℕ)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (φ : qs.State) (h : InRange c data N φ) :
    InRange c data N (uncontrolledAction c (Gate.idealCtrlModMul a N data c) φ) := by
  unfold InRange at h ⊢
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hyc, hyd⟩, rfl⟩ := hx
    obtain ⟨-, -, -, h4⟩ := idealCtrlModMul_round_hyps_ket a N data c y hN hNdata ha hc hyd hyc
    rw [h4]
    have hv : a * RegEncoding.toNat data y % N < N := Nat.mod_lt _ (by omega)
    refine Submodule.subset_span ⟨_, ⟨?_, ?_⟩, rfl⟩
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

/-- A readout round with the ideal controlled multiplier keeps a branch in
range: if the branch of `ψ` at `r` is `InRange`, so is the round's child at
`r ++ [b]`, for both outcomes `b` and every round index `j`. -/
theorem inRange_round_child [HadamardSemantics qs] [PauliXSemantics qs]
    [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ) (data : Reg) (c : ℕ)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (j : ℕ) (ψ : MState qs) (r : Record) (b : Bool) (h : InRange c data N (ψ r)) :
    InRange c data N
      ((readoutRound c (Gate.idealCtrlModMul a N data c) j).eval ψ (r ++ [b])) := by
  obtain ⟨h1, h2, h3⟩ := round_hyps_of_inRange a N data c hN hNdata ha hc _ h
  rw [round_branch c _ j ψ r b h1 h2 h3]
  have hT := inRange_uncontrolledAction a N data c hN hNdata ha hc _ h
  unfold InRange at h hT ⊢
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ h (Submodule.smul_mem _ _ hT))

/-- The induction step over rounds: if every branch of `ψ` is `InRange`, then
every branch after one more round with the ideal controlled multiplier is
`InRange` (so `round_branch` applies again at the next round). -/
theorem inRange_round_eval [HadamardSemantics qs] [PauliXSemantics qs]
    [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ) (data : Reg) (c : ℕ)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (j : ℕ) (ψ : MState qs) (h : ∀ r, InRange c data N (ψ r)) (r : Record) :
    InRange c data N ((readoutRound c (Gate.idealCtrlModMul a N data c) j).eval ψ r) := by
  rcases List.eq_nil_or_concat r with rfl | ⟨r₀, b, rfl⟩
  · rw [round_branch_nil]; exact Submodule.zero_mem _
  · rw [List.concat_eq_append]
    exact inRange_round_child a N data c hN hNdata ha hc j ψ r₀ b (h r₀)

/-! ## Deferred measurement -/

/-- The classically conditioned gate: on the branch at a record ending in
outcome `b`, apply `U b` (on the empty record, `U false`). It is the semantic
step "if the last measured bit was `b`, apply `U b`". -/
noncomputable def condOnLast (U : Bool → Gate) (ψ : MState qs) : MState qs :=
  fun r => qs.eval (U (r.getLastD false)) (ψ r)

/-- **Deferred measurement (one qubit).** Let `CU` be the `q`-controlled
version of the pair `U false`, `U true`: on every state it applies `U false` to
the `q = 0` part and `U true` to the `q = 1` part (`hCU`). Let each `U b` act
away from qubit `q`: it commutes with the Born projectors of `q` (`hcomm`) and
with `X q` (`hX`). Then, from every branching state `ψ`, the two programs give
EQUAL branching states, branch by branch:

  measure-and-reset `q`, then apply `U b` on the branch whose last outcome is `b`
  `=` apply `CU`, then measure-and-reset `q`.

In particular every continuation (any further `MGate` program) gives the same
record probabilities after either one. -/
theorem deferred_measurement (q : ℕ) (U : Bool → Gate) (CU : Gate)
    (hCU : ∀ φ : qs.State, qs.eval CU φ
      = qs.eval (U false) (measProj (qubitReg q) 0 φ)
        + qs.eval (U true) (measProj (qubitReg q) 1 φ))
    (hcomm : ∀ (b : Bool) (o : ℕ) (φ : qs.State),
      measProj (qubitReg q) o (qs.eval (U b) φ) = qs.eval (U b) (measProj (qubitReg q) o φ))
    (hX : ∀ (b : Bool) (φ : qs.State),
      qs.eval (Gate.X q) (qs.eval (U b) φ) = qs.eval (U b) (qs.eval (Gate.X q) φ))
    (ψ : MState qs) :
    condOnLast U ((MGate.measureReset q).eval ψ)
      = (MGate.seq (.unitary CU) (.measureReset q)).eval ψ := by
  -- the outcome-`b` Born projection of the controlled gate's output
  have hproj : ∀ (b : Bool) (φ : qs.State),
      measProj (qubitReg q) (if b then 1 else 0) (qs.eval CU φ)
        = qs.eval (U b) (measProj (qubitReg q) (if b then 1 else 0) φ) := by
    intro b φ
    rw [hCU, map_add, hcomm, hcomm]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [MeasureClass.measProj_idempotent, MeasureClass.measProj_orthogonal _ _ _ _ (by decide),
        MGate.gate_eval_zero_state, add_zero]
    · simp only [ite_true]
      rw [MeasureClass.measProj_idempotent, MeasureClass.measProj_orthogonal _ _ _ _ (by decide),
        MGate.gate_eval_zero_state, zero_add]
  funext r
  rcases List.eq_nil_or_concat r with rfl | ⟨r₀, b, rfl⟩
  · simp [condOnLast, MGate.gate_eval_zero_state]
  · simp only [condOnLast, List.concat_eq_append, MGate.eval_seq,
      MGate.eval_measureReset_append, MGate.eval_unitary, List.getLastD_concat]
    have hb := hproj b (ψ r₀)
    cases b
    · simp only [measureResetBranch, Bool.false_eq_true, ite_false] at hb ⊢
      exact hb.symm
    · simp only [measureResetBranch, ite_true] at hb ⊢
      rw [hb, hX]

/-- Consequence of `deferred_measurement`: after any continuation program `P`,
the two orders give the same probability for every record. -/
theorem deferred_measurement_recordProb (q : ℕ) (U : Bool → Gate) (CU : Gate)
    (hCU : ∀ φ : qs.State, qs.eval CU φ
      = qs.eval (U false) (measProj (qubitReg q) 0 φ)
        + qs.eval (U true) (measProj (qubitReg q) 1 φ))
    (hcomm : ∀ (b : Bool) (o : ℕ) (φ : qs.State),
      measProj (qubitReg q) o (qs.eval (U b) φ) = qs.eval (U b) (measProj (qubitReg q) o φ))
    (hX : ∀ (b : Bool) (φ : qs.State),
      qs.eval (Gate.X q) (qs.eval (U b) φ) = qs.eval (U b) (qs.eval (Gate.X q) φ))
    (P : MGate) (ψ : MState qs) :
    recordProb (P.eval (condOnLast U ((MGate.measureReset q).eval ψ)))
      = recordProb (P.eval ((MGate.seq (.unitary CU) (.measureReset q)).eval ψ)) := by
  rw [deferred_measurement q U CU hCU hcomm hX ψ]

end Readout
end Shor
