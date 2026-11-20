import ForShor.ShorVerification.Implementation.Readout.ShorStatement
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.OrderFinding

/-!
# Readout: exact counts and the qubit formula of the semiclassical readout

## Counts (`MGate.counts`)

`MGate.counts g` counts, in the program text of `g`:

* `hCount`: the `Gate.H` constructors written in its unitary parts (`Gate.hCount`;
  syntactic: a macro gate such as `QFT` or a phase product counts `0` here, its
  Hadamards appear only after lowering and are priced by the lowered resource model);
* `measCount`: the `measureReset` steps;
* `ffCount`: the `ffPhase` steps;
* `nontrivialFfCount`: the `ffPhase` steps whose angle can be nonzero, i.e. those of
  round index `j ≥ 1`. `ffPhase q j` applies `Phase q (ffAngle j rec)`;
  `ffAngle 0 rec = 0` for every record (`ffAngle_zero_eq`), and for `j ≥ 1` the angle
  is nonzero on some record (`ffAngle_pos_ne_zero`). So `ffPhase q 0` is the identity
  and every other `ffPhase` is a genuine record-dependent rotation. "Nontrivial" does
  NOT mean "needs a synthesis": the angle `ffAngle j rec` is a multiple of `π / 2^j`, so
  round `j = 1` angles are S-class (multiples of `π/2`), round `j = 2` angles are
  multiples of `π/4` (Clifford+T exactly), and only from round `j = 3` on can an angle
  need an approximate synthesis. The cost model nevertheless prices every nontrivial
  `ffPhase` as one Ross-Selinger rotation (project rule), so this count is the number
  of priced rotations, not the number of rotations that need synthesis.

`readout_counts c m`: the skeleton `readoutRounds (fun _ => Gate.id) c m` has `2m`
Hadamards (two per round: before the multiplier and before the measurement), `m`
measurements, `m` feed-forward phases, of which `m - 1` are nontrivial (round `0`'s is
the identity). With real multipliers `U j` the counts add (`readoutRounds_counts`):
the `H` count gains `Σ_{j<m} (U j).hCount`, the other three are unchanged. For an
arbitrary additive per-gate cost `f` (e.g. a lowered resource count) the same holds
for the list of unitary parts (`readoutRounds_cost`, `orderFindingSemiclassical_cost`):
the circuit costs `f (initY1 …) + 2m · f (H c) + Σ_{j<m} f (U j)`, plus its `m`
measurements and `m - 1` nontrivial phases, which `f` does not see.

Lean-tier rotation price: an `ffPhase` lowers to one `LowGate.Phase`, which the
resource model charges `rz := 1` (`ResourceModel.lean`), as today's `Phase`; the
`nontrivialFfCount` is the number of such rotations whose angle can be nonzero (round
index `≥ 1`), each priced as one Ross-Selinger rotation by the cost model, although
rounds `1` and `2` only need S- and T-class angles (see above).

## Qubits (formula level)

The semiclassical circuit `orderFindingSemiclassical` names only `c`, `y`, `work`,
`scratch` and `flag` (`orderFindingSemiclassical_support`). Its base set
(`orderFindingBaseSetSC`) is the control `c`, the data register with its carry bit,
the work and scratch registers and the flag: the exponent register `x` of
`orderFindingBaseSet` is replaced by the one qubit `c`
(`orderFindingBaseSetSC_eq`, `orderFindingBaseSetSC_card`).

There is no inverse QFT, so its extra-qubit peak is that of one controlled modular
multiplication alone, `modMulPeakWith` (`orderFindingPeakSCWith`): the term `qp xW` of
`orderFindingPeakWith = max (modMulPeakWith …) (qp xW)` is gone. The budgets
`Policy.orderFindingQubitsSC` / `…BalancedSC` / `…USC` mirror
`Policy.orderFindingQubits` / `…Balanced` / `…U` with `xW` replaced by `1`. They are
the formula for a run of at least one round (`m ≥ 1`; with `m = 0` the circuit is
just `initY1` and no multiplication runs). That the lowered semiclassical circuit
really peaks at this formula is proved separately (`semiclassical_peak_formula` and its
balanced variants in `Readout/Proofs/LowerPeak.lean`); here only the formulas are
compared.

`qubits_saving_eq`: for `1 ≤ xW`, the old count is exactly the new count plus
`xW - 1` plus `qftPeak xW - modMulPeak` (truncated subtraction). Hence
`qubits_saving` (new ≤ old - (xW - 1)), with equality (`qubits_saving_eq_of_le`)
exactly when the old peak was set by the modular multiplication, i.e.
`qftPeak xW ≤ modMulPeak` (both directions: `qubits_saving_eq_iff`). The same for the
balanced and the every-site-split budgets. That the lowered circuit peaks at these
formulas is `semiclassical_peak_formula` (`Readout/Proofs/LowerPeak.lean`).
-/

namespace Shor

/-! ## Counts -/

/-- The number of `Gate.H` constructors written in a gate term (`seq` adds, `adj`
counts its body). Syntactic: every other constructor, including the macro gates
(`QFT`, phase products, constant arithmetic, `idealCtrlModMul`), counts `0` here.
Note that the catch-all `| _ => 0` also makes any constructor added to `Gate` later
count `0` without a compile error: a new constructor that contains Hadamards must be
given its own case here.

Exhaustiveness, checked by hand against `Gate` as of this file: the catch-all covers
exactly `id`, `X`, `CNOT`, `Toffoli`, `QFT`, `RadixReverse`, `SignedPhaseProd`,
`CSignedPhaseProd`, `CmpGeConst`, `CSubConst`, `ShiftL`, `ShiftR`, `Negate`, `AddScaled`,
`zeroExtend`, `signExtend`, `zeroDealloc`, `signDealloc` and `idealCtrlModMul`. Some of
these (e.g. `QFT`) lower to circuits that contain Hadamards; they count `0` here on purpose,
since `hCount` counts the `H` constructors written in the term, not those of a lowering. -/
def Gate.hCount : Gate → ℕ
  | .seq U V => U.hCount + V.hCount
  | .adj U => U.hCount
  | .H _ => 1
  -- catch-all: every other constructor, INCLUDING any added to `Gate` later, counts `0`
  | _ => 0

/-- Four counts of a measurement-language program; see `MGate.counts`. -/
structure MCounts where
  /-- `Gate.H` constructors in the unitary parts (`Gate.hCount`). -/
  hCount : ℕ
  /-- `measureReset` steps. -/
  measCount : ℕ
  /-- `ffPhase` steps. -/
  ffCount : ℕ
  /-- `ffPhase q j` steps with `j ≥ 1`, the ones whose angle `ffAngle j rec` can be nonzero
  (not "the ones that need synthesis": `j = 1` angles are S-class, `j = 2` multiples of
  `π/4`; every one is priced as a Ross-Selinger rotation by the cost model). -/
  nontrivialFfCount : ℕ
deriving DecidableEq, Repr

instance : Add MCounts :=
  ⟨fun a b => ⟨a.hCount + b.hCount, a.measCount + b.measCount, a.ffCount + b.ffCount,
    a.nontrivialFfCount + b.nontrivialFfCount⟩⟩

@[simp] theorem MCounts.mk_add_mk (a b c d a' b' c' d' : ℕ) :
    (⟨a, b, c, d⟩ : MCounts) + ⟨a', b', c', d'⟩ = ⟨a + a', b + b', c + c', d + d'⟩ := rfl

@[simp] theorem MCounts.add_hCount (a b : MCounts) : (a + b).hCount = a.hCount + b.hCount := rfl

/-- Counts of a program text: `unitary g` contributes `g.hCount` Hadamards; `seq`
adds; `measureReset` is one measurement; `ffPhase q j` is one feed-forward phase,
nontrivial iff `j ≠ 0` (`ffAngle 0 = 0`). -/
def MGate.counts : MGate → MCounts
  | .unitary g => ⟨g.hCount, 0, 0, 0⟩
  | .seq a b => a.counts + b.counts
  | .measureReset _ => ⟨0, 1, 0, 0⟩
  | .ffPhase _ j => ⟨0, 0, 1, if j = 0 then 0 else 1⟩

/-- The unitary parts of a program, in program order (`measureReset` and `ffPhase`
contribute none). -/
def MGate.unitaryGates : MGate → List Gate
  | .unitary g => [g]
  | .seq a b => a.unitaryGates ++ b.unitaryGates
  | .measureReset _ => []
  | .ffPhase _ _ => []

namespace Readout

/-- Round `0`'s feed-forward angle is `0` whatever the record: `ffPhase q 0` is the
identity. -/
theorem ffAngle_zero_eq (rec : Record) : ffAngle 0 rec = 0 := by
  simp [ffAngle]

/-- For `j ≥ 1` the feed-forward angle is not identically zero: on the record
`[true]` (first outcome `1`) it is `-1/2^j`. -/
theorem ffAngle_pos_ne_zero {j : ℕ} (hj : 0 < j) : ffAngle j [true] ≠ 0 := by
  have hs : (∑ i ∈ Finset.range j, (if [true].getD i false then (1 : ℚ) else 0) / 2 ^ (j - i))
      = 1 / 2 ^ j := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      simp
    · intro h; exact absurd (Finset.mem_range.mpr hj) h
  unfold ffAngle
  rw [hs, neg_ne_zero]
  positivity

/-- The `H` count of a program is the sum of `Gate.hCount` over its unitary parts. -/
theorem counts_hCount_eq_sum (g : MGate) :
    g.counts.hCount = (g.unitaryGates.map Gate.hCount).sum := by
  induction g with
  | unitary g => simp [MGate.counts, MGate.unitaryGates]
  | seq a b iha ihb => simp [MGate.counts, MGate.unitaryGates, iha, ihb]
  | measureReset q => simp [MGate.counts, MGate.unitaryGates]
  | ffPhase q j => simp [MGate.counts, MGate.unitaryGates]

/-- **Counts of the readout with multipliers `U`.** `m` rounds on `c` have
`2m + Σ_{j<m} (U j).hCount` Hadamards, `m` measurements, `m` feed-forward phases,
`m - 1` of them nontrivial: the multipliers add their own `H` count and nothing else. -/
theorem readoutRounds_counts (U : ℕ → Gate) (c m : ℕ) :
    (readoutRounds U c m).counts
      = ⟨2 * m + ∑ j ∈ Finset.range m, (U j).hCount, m, m, m - 1⟩ := by
  induction m with
  | zero => simp [readoutRounds, MGate.counts, Gate.hCount]
  | succ k ih =>
    simp only [readoutRounds, MGate.counts, ih, Gate.hCount, MCounts.mk_add_mk,
      Finset.sum_range_succ, MCounts.mk.injEq]
    refine ⟨by ring, trivial, trivial, ?_⟩
    split <;> omega

/-- **Counts of the readout skeleton.** With identity multipliers, `m` rounds have
`2m` Hadamards, `m` measurements, `m` feed-forward phases and `m - 1` nontrivial
ones. -/
theorem readout_counts (c m : ℕ) :
    (readoutRounds (fun _ => Gate.id) c m).counts = ⟨2 * m, m, m, m - 1⟩ := by
  rw [readoutRounds_counts]
  simp [Gate.hCount]

/-- **Additivity for any per-gate cost.** For `f : Gate → ℕ` with `f Gate.id = 0`, the
unitary parts of `m` rounds cost `2m · f (H c) + Σ_{j<m} f (U j)`. -/
theorem readoutRounds_cost (f : Gate → ℕ) (hid : f Gate.id = 0) (U : ℕ → Gate) (c m : ℕ) :
    ((readoutRounds U c m).unitaryGates.map f).sum
      = 2 * m * f (Gate.H c) + ∑ j ∈ Finset.range m, f (U j) := by
  induction m with
  | zero => simp [readoutRounds, MGate.unitaryGates, hid]
  | succ k ih =>
    simp only [readoutRounds, MGate.unitaryGates, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.append_nil]
    ring

/-- **The semiclassical order-finding circuit, per-gate cost.** For `f` with
`f Gate.id = 0`, its unitary parts cost `f (initY1 y.active) + 2m · f (H c)` plus
the cost of the `m` real multipliers (`semiclassicalMultipliers`, round `j`'s
`CmodMulInPlaceCore` by `a^(2^(m-1-j)) mod N` controlled by `c`). -/
theorem orderFindingSemiclassical_cost (f : Gate → ℕ) (hid : f Gate.id = 0)
    (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).unitaryGates.map f).sum
      = f (initY1 y.active) + 2 * m * f (Gate.H c)
        + ∑ j ∈ Finset.range m, f (semiclassicalMultipliers a N c m y work scratch flag hw hs4 j) := by
  simp only [orderFindingSemiclassical, MGate.unitaryGates, List.map_append, List.sum_append,
    readoutRounds_cost f hid, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- **Counts of the semiclassical order-finding circuit.** `initY1`'s and the
multipliers' `H` constructors plus `2m`, and `m` measurements, `m` feed-forward phases,
`m - 1` nontrivial. -/
theorem orderFindingSemiclassical_counts (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    (orderFindingSemiclassical a N c m y work scratch flag hw hs4).counts
      = ⟨(initY1 y.active).hCount + 2 * m
          + ∑ j ∈ Finset.range m, (semiclassicalMultipliers a N c m y work scratch flag hw hs4 j).hCount,
         m, m, m - 1⟩ := by
  simp only [orderFindingSemiclassical, MGate.counts, readoutRounds_counts, MCounts.mk_add_mk,
    MCounts.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

end Readout

/-! ## Qubits: the base set -/

/-- The qubits live throughout the semiclassical order-finding circuit: the control
`c`, the data register with its carry bit, the work and scratch registers, and the
flag. It is `orderFindingBaseSet` with the exponent register replaced by `{c}`. -/
def orderFindingBaseSetSC (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) : Finset ℕ :=
  {c} ∪ regQubitSet (y.grow 1).active ∪ regQubitSet work.active
    ∪ regQubitSet scratch.active ∪ {flag}

/-! ## Qubits: the budgets -/

/-- Peak extra qubits of the semiclassical order-finding circuit (at least one round):
one controlled modular multiplication's peak, `modMulPeakWith`. Compared with
`orderFindingPeakWith`, the inverse-QFT term `qp xW` is absent (the readout has no
QFT); `qp` still prices the QFTs inside the multiplier. -/
def orderFindingPeakSCWith (m : NegationMethod) (pp : ℕ → ℕ → ℕ → ℕ → ℕ) (qp : ℕ → ℕ)
    (dW dC wW wC sW sC : ℕ) : ℕ :=
  modMulPeakWith m pp qp dW dC wW wC sW sC

/-- `orderFindingPeakD` without the inverse QFT: phase products lowered directly. -/
def orderFindingPeakSCD (m : NegationMethod) (R : WidthRule) (D : List (ℕ × TableData))
    (dW wW sW : ℕ) : ℕ :=
  orderFindingPeakSCWith m (fun wx _ wz _ => peakReserveD m R D wx wz) (qftPeakD m R D)
    dW 0 wW 0 sW 0

/-- `orderFindingPeakBalancedD` without the inverse QFT. -/
def orderFindingPeakBalancedSCD (m : NegationMethod) (R : WidthRule) (D : List (ℕ × TableData))
    (Rule : Balanced.Rule) (dW dC wW wC sW sC : ℕ) : ℕ :=
  orderFindingPeakSCWith m (sitePeakD m R D Rule) (qftPeakD m R D) dW dC wW wC sW sC

/-- `orderFindingPeakUD` without the inverse QFT. -/
def orderFindingPeakUSCD (m : NegationMethod) (R : WidthRule) (D : List (ℕ × TableData))
    (Rule : Balanced.Rule) (dW wW sW : ℕ) : ℕ :=
  orderFindingPeakSCWith m (fun wx _ wz _ => sitePeakU (peakReserveD m R D) Rule wx wz)
    (qftPeakD m R D) dW 0 wW 0 sW 0

/-- Peak extra qubits of the semiclassical circuit under `P` (phase products direct). -/
def Policy.orderFindingPeakSC (P : ShorLoweringPolicy) (dW wW sW : ℕ) : ℕ :=
  orderFindingPeakSCD P.negation P.widthRule (Policy.compile P) dW wW sW

/-- Peak extra qubits of the balanced semiclassical circuit under `P` and `Rule`. -/
def Policy.orderFindingPeakBalancedSC (P : ShorLoweringPolicy) (Rule : Balanced.Rule)
    (dW dC wW wC sW sC : ℕ) : ℕ :=
  orderFindingPeakBalancedSCD P.negation P.widthRule (Policy.compile P) Rule dW dC wW wC sW sC

/-- Peak extra qubits of the every-site-split semiclassical circuit under `P` and `Rule`. -/
def Policy.orderFindingPeakUSC (P : ShorLoweringPolicy) (Rule : Balanced.Rule) (dW wW sW : ℕ) :
    ℕ :=
  orderFindingPeakUSCD P.negation P.widthRule (Policy.compile P) Rule dW wW sW

/-- **The qubit-count formula of the semiclassical order-finding circuit** (at least one
round): the control qubit, the data register with its carry bit, the work and scratch
registers, the flag, plus one modular multiplication's peak. `Policy.orderFindingQubits`
with the exponent register's `xW` replaced by `1` and no inverse-QFT term. -/
def Policy.orderFindingQubitsSC (P : ShorLoweringPolicy) (dW wW sW : ℕ) : ℕ :=
  1 + (dW + 1) + wW + sW + 1 + Policy.orderFindingPeakSC P dW wW sW

/-- The balanced analogue of `Policy.orderFindingQubitsSC`. -/
def Policy.orderFindingQubitsBalancedSC (P : ShorLoweringPolicy) (Rule : Balanced.Rule)
    (dW dC wW wC sW sC : ℕ) : ℕ :=
  1 + (dW + 1) + wW + sW + 1 + Policy.orderFindingPeakBalancedSC P Rule dW dC wW wC sW sC

/-- The every-site-split analogue of `Policy.orderFindingQubitsSC`. -/
def Policy.orderFindingQubitsUSC (P : ShorLoweringPolicy) (Rule : Balanced.Rule)
    (dW wW sW : ℕ) : ℕ :=
  1 + (dW + 1) + wW + sW + 1 + Policy.orderFindingPeakUSC P Rule dW wW sW

namespace Readout

open QubitCount

/-! ### The base set -/

/-- **The new base set is the old one with `x` swapped for `c`.** When the exponent
register shares no qubit with the data, work, scratch registers or the flag (the
hypotheses of the old peak formula), `orderFindingBaseSetSC` is the old base set
minus `x`'s active qubits, plus `c`. -/
theorem orderFindingBaseSetSC_eq {x y work scratch : ExtReg} {flag N : ℕ} (c : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hlay : OrderFindingSpaceLayout x y work scratch flag) :
    orderFindingBaseSetSC c y work scratch flag
      = insert c (orderFindingBaseSet x y work scratch flag \ regQubitSet x.active) := by
  obtain ⟨hxy, hxw, hxs, _, _, _, hfx, _, _, _⟩ := base_facts hmod hs4 hlay
  have hY : ∀ q, q ∈ regQubitSet (y.grow 1).active → q ∉ regQubitSet x.active := fun q h hx =>
    Finset.disjoint_left.mp hxy (active_sub_own x hx) (yGrow_active_sub y h)
  have hW : ∀ q, q ∈ regQubitSet work.active → q ∉ regQubitSet x.active := fun q h hx =>
    Finset.disjoint_left.mp hxw (active_sub_own x hx) (active_sub_own work h)
  have hS : ∀ q, q ∈ regQubitSet scratch.active → q ∉ regQubitSet x.active := fun q h hx =>
    Finset.disjoint_left.mp hxs (active_sub_own x hx) (active_sub_own scratch h)
  have hF : flag ∉ regQubitSet x.active := fun h => hfx (active_sub_own x h)
  ext q
  simp only [orderFindingBaseSetSC, orderFindingBaseSet, Finset.mem_insert, Finset.mem_sdiff,
    Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ((((rfl | h) | h) | h) | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨Or.inl (Or.inl (Or.inl (Or.inr h))), hY q h⟩
    · exact Or.inr ⟨Or.inl (Or.inl (Or.inr h)), hW q h⟩
    · exact Or.inr ⟨Or.inl (Or.inr h), hS q h⟩
    · exact Or.inr ⟨Or.inr rfl, hF⟩
  · rintro (rfl | ⟨((((h | h) | h) | h) | rfl), hn⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
    · exact absurd h hn
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr rfl

/-- **Size of the new base set.** On the workspaces of one modular multiplication,
with `c` outside the data, work and scratch registers and different from the flag
(`SemiclassicalLayout`), the base set has `1 + (dW + 1) + wW + sW + 1` qubits. -/
theorem orderFindingBaseSetSC_card {y work scratch : ExtReg} {flag N c : ℕ}
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hc : SemiclassicalLayout c y work scratch flag) :
    (orderFindingBaseSetSC c y work scratch flag).card
      = 1 + (y.width + 1) + work.width + scratch.width + 1 := by
  have hyw := ownSet_disjoint hmod.2.2
  have hys := ownSet_disjoint hs4.data_scratch_disjoint
  have hws := ownSet_disjoint hs4.work_scratch_disjoint
  have hfy := not_mem_ownSet hs4.flag_not_data
  rw [ownSet_grow] at hys hfy
  have hfw := not_mem_ownSet hs4.flag_not_work
  have hfs := not_mem_ownSet hs4.flag_not_scratch
  have hcy := not_mem_ownSet hc.c_not_mem_data
  have hcw := not_mem_ownSet hc.c_not_mem_work
  have hcs := not_mem_ownSet hc.c_not_mem_scratch
  have hcf := hc.c_ne_flag
  have hyA := yGrow_active_sub y
  have hcap1 : y.CanGrow 1 := le_trans (by norm_num) hmod.1
  have d1 : _root_.Disjoint ({c} : Finset ℕ) (regQubitSet (y.grow 1).active) :=
    Finset.disjoint_singleton_left.mpr (fun h => hcy (hyA h))
  have d2 : _root_.Disjoint ({c} ∪ regQubitSet (y.grow 1).active) (regQubitSet work.active) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_singleton_left.mpr (fun h => hcw (active_sub_own work h)),
       Finset.disjoint_of_subset_left hyA
        (Finset.disjoint_of_subset_right (active_sub_own work) hyw)⟩
  have d3 : _root_.Disjoint ({c} ∪ regQubitSet (y.grow 1).active ∪ regQubitSet work.active)
      (regQubitSet scratch.active) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_singleton_left.mpr (fun h => hcs (active_sub_own scratch h)),
         Finset.disjoint_of_subset_left hyA
          (Finset.disjoint_of_subset_right (active_sub_own scratch) hys)⟩,
       Finset.disjoint_of_subset_left (active_sub_own work)
        (Finset.disjoint_of_subset_right (active_sub_own scratch) hws)⟩
  have d4 : flag ∉ {c} ∪ regQubitSet (y.grow 1).active ∪ regQubitSet work.active ∪
      regQubitSet scratch.active := by
    simp only [Finset.mem_union, Finset.mem_singleton, not_or]
    exact ⟨⟨⟨fun h => hcf h.symm, fun h => hfy (hyA h)⟩, fun h => hfw (active_sub_own work h)⟩,
      fun h => hfs (active_sub_own scratch h)⟩
  have hgw : (y.grow 1).width = y.width + 1 := ExtReg.width_grow y 1 hcap1
  simp only [orderFindingBaseSetSC]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr d4),
    Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2,
    Finset.card_union_of_disjoint d1, card_regQubitSet, card_regQubitSet, card_regQubitSet,
    Finset.card_singleton, Finset.card_singleton]
  rw [show regSize (y.grow 1).active = (y.grow 1).width from rfl, hgw]
  rfl

/-- **Old versus new base set.** Under both layouts, the old base set has `x.width - 1`
more qubits than the new one: `|new| + x.width = |old| + 1`. -/
theorem orderFindingBaseSetSC_card_add {x y work scratch : ExtReg} {flag N c : ℕ}
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hlay : OrderFindingSpaceLayout x y work scratch flag)
    (hc : SemiclassicalLayout c y work scratch flag) :
    (orderFindingBaseSetSC c y work scratch flag).card + x.width
      = (orderFindingBaseSet x y work scratch flag).card + 1 := by
  rw [orderFindingBaseSetSC_card hmod hs4 hc, base_card hmod hs4 hlay]
  omega

/-! ### The peak and the saving -/

/-- With at least one exponent qubit, the old peak is the new one (the modular
multiplication's) plus the excess of the inverse QFT's peak over it (truncated
subtraction: `0` when the multiplication sets the peak). -/
theorem orderFindingPeakWith_eq (m : NegationMethod) (pp : ℕ → ℕ → ℕ → ℕ → ℕ) (qp : ℕ → ℕ)
    {xW : ℕ} (hx : 0 < xW) (dW dC wW wC sW sC : ℕ) :
    orderFindingPeakWith m pp qp xW dW dC wW wC sW sC
      = orderFindingPeakSCWith m pp qp dW dC wW wC sW sC
        + (qp xW - orderFindingPeakSCWith m pp qp dW dC wW wC sW sC) := by
  simp only [orderFindingPeakWith, orderFindingPeakSCWith, hx, ↓reduceIte]
  omega

/-- **Exact saving (direct phase products).** For `1 ≤ xW`, the old count is the
semiclassical count plus `xW - 1` plus `qftPeakD xW - N_SC`, `N_SC` the new peak. -/
theorem qubits_saving_eq (P : ShorLoweringPolicy) {xW : ℕ} (hx : 1 ≤ xW) (dW wW sW : ℕ) :
    Policy.orderFindingQubits P xW dW wW sW
      = Policy.orderFindingQubitsSC P dW wW sW + (xW - 1)
        + (qftPeakD P.negation P.widthRule (Policy.compile P) xW
            - Policy.orderFindingPeakSC P dW wW sW) := by
  simp only [Policy.orderFindingQubits, Policy.orderFindingPeak, orderFindingPeakD,
    Policy.orderFindingQubitsSC, Policy.orderFindingPeakSC, orderFindingPeakSCD]
  rw [orderFindingPeakWith_eq _ _ _ (by omega)]
  omega

/-- **Qubit saving (direct phase products).** For `1 ≤ xW`, the semiclassical count is
at most the old count minus `xW - 1`. -/
theorem qubits_saving (P : ShorLoweringPolicy) {xW : ℕ} (hx : 1 ≤ xW) (dW wW sW : ℕ) :
    Policy.orderFindingQubitsSC P dW wW sW ≤ Policy.orderFindingQubits P xW dW wW sW - (xW - 1) := by
  rw [qubits_saving_eq P hx]
  omega

/-- **Saving exactly `xW - 1` (direct phase products)** when the old peak was set by the
modular multiplication (`qftPeakD xW ≤ N_SC`). -/
theorem qubits_saving_eq_of_le (P : ShorLoweringPolicy) {xW : ℕ} (hx : 1 ≤ xW) (dW wW sW : ℕ)
    (hq : qftPeakD P.negation P.widthRule (Policy.compile P) xW
      ≤ Policy.orderFindingPeakSC P dW wW sW) :
    Policy.orderFindingQubitsSC P dW wW sW = Policy.orderFindingQubits P xW dW wW sW - (xW - 1) := by
  rw [qubits_saving_eq P hx]
  omega

/-- **Exact saving (balanced).** -/
theorem qubits_saving_eq_balanced (P : ShorLoweringPolicy) (Rule : Balanced.Rule) {xW : ℕ}
    (hx : 1 ≤ xW) (dW dC wW wC sW sC : ℕ) :
    Policy.orderFindingQubitsBalanced P Rule xW dW dC wW wC sW sC
      = Policy.orderFindingQubitsBalancedSC P Rule dW dC wW wC sW sC + (xW - 1)
        + (qftPeakD P.negation P.widthRule (Policy.compile P) xW
            - Policy.orderFindingPeakBalancedSC P Rule dW dC wW wC sW sC) := by
  simp only [Policy.orderFindingQubitsBalanced, Policy.orderFindingPeakBalanced,
    orderFindingPeakBalancedD, Policy.orderFindingQubitsBalancedSC,
    Policy.orderFindingPeakBalancedSC, orderFindingPeakBalancedSCD]
  rw [orderFindingPeakWith_eq _ _ _ (by omega)]
  omega

/-- **Qubit saving (balanced).** -/
theorem qubits_saving_balanced (P : ShorLoweringPolicy) (Rule : Balanced.Rule) {xW : ℕ}
    (hx : 1 ≤ xW) (dW dC wW wC sW sC : ℕ) :
    Policy.orderFindingQubitsBalancedSC P Rule dW dC wW wC sW sC
      ≤ Policy.orderFindingQubitsBalanced P Rule xW dW dC wW wC sW sC - (xW - 1) := by
  rw [qubits_saving_eq_balanced P Rule hx]
  omega

/-- **Saving exactly `xW - 1` (balanced)** when the multiplication sets the old peak. -/
theorem qubits_saving_eq_of_le_balanced (P : ShorLoweringPolicy) (Rule : Balanced.Rule) {xW : ℕ}
    (hx : 1 ≤ xW) (dW dC wW wC sW sC : ℕ)
    (hq : qftPeakD P.negation P.widthRule (Policy.compile P) xW
      ≤ Policy.orderFindingPeakBalancedSC P Rule dW dC wW wC sW sC) :
    Policy.orderFindingQubitsBalancedSC P Rule dW dC wW wC sW sC
      = Policy.orderFindingQubitsBalanced P Rule xW dW dC wW wC sW sC - (xW - 1) := by
  rw [qubits_saving_eq_balanced P Rule hx]
  omega

/-- **Exact saving (every site split).** -/
theorem qubits_saving_eq_U (P : ShorLoweringPolicy) (Rule : Balanced.Rule) {xW : ℕ}
    (hx : 1 ≤ xW) (dW wW sW : ℕ) :
    Policy.orderFindingQubitsU P Rule xW dW wW sW
      = Policy.orderFindingQubitsUSC P Rule dW wW sW + (xW - 1)
        + (qftPeakD P.negation P.widthRule (Policy.compile P) xW
            - Policy.orderFindingPeakUSC P Rule dW wW sW) := by
  simp only [Policy.orderFindingQubitsU, Policy.orderFindingPeakU, orderFindingPeakUD,
    Policy.orderFindingQubitsUSC, Policy.orderFindingPeakUSC, orderFindingPeakUSCD]
  rw [orderFindingPeakWith_eq _ _ _ (by omega)]
  omega

/-- **Qubit saving (every site split).** -/
theorem qubits_saving_U (P : ShorLoweringPolicy) (Rule : Balanced.Rule) {xW : ℕ}
    (hx : 1 ≤ xW) (dW wW sW : ℕ) :
    Policy.orderFindingQubitsUSC P Rule dW wW sW
      ≤ Policy.orderFindingQubitsU P Rule xW dW wW sW - (xW - 1) := by
  rw [qubits_saving_eq_U P Rule hx]
  omega

/-- **Saving exactly `xW - 1` (every site split)** when the multiplication sets the old
peak. -/
theorem qubits_saving_eq_of_le_U (P : ShorLoweringPolicy) (Rule : Balanced.Rule) {xW : ℕ}
    (hx : 1 ≤ xW) (dW wW sW : ℕ)
    (hq : qftPeakD P.negation P.widthRule (Policy.compile P) xW
      ≤ Policy.orderFindingPeakUSC P Rule dW wW sW) :
    Policy.orderFindingQubitsUSC P Rule dW wW sW
      = Policy.orderFindingQubitsU P Rule xW dW wW sW - (xW - 1) := by
  rw [qubits_saving_eq_U P Rule hx]
  omega

/-! ### Exactly when the saving is `xW - 1` -/

/-- **Saving exactly `xW - 1` iff the multiplication set the old peak (direct).** -/
theorem qubits_saving_eq_iff (P : ShorLoweringPolicy) {xW : ℕ} (hx : 1 ≤ xW) (dW wW sW : ℕ) :
    Policy.orderFindingQubitsSC P dW wW sW = Policy.orderFindingQubits P xW dW wW sW - (xW - 1)
      ↔ qftPeakD P.negation P.widthRule (Policy.compile P) xW
          ≤ Policy.orderFindingPeakSC P dW wW sW := by
  rw [qubits_saving_eq P hx]
  omega

/-- **Saving exactly `xW - 1` iff the multiplication set the old peak (balanced).** -/
theorem qubits_saving_eq_iff_balanced (P : ShorLoweringPolicy) (Rule : Balanced.Rule) {xW : ℕ}
    (hx : 1 ≤ xW) (dW dC wW wC sW sC : ℕ) :
    Policy.orderFindingQubitsBalancedSC P Rule dW dC wW wC sW sC
        = Policy.orderFindingQubitsBalanced P Rule xW dW dC wW wC sW sC - (xW - 1)
      ↔ qftPeakD P.negation P.widthRule (Policy.compile P) xW
          ≤ Policy.orderFindingPeakBalancedSC P Rule dW dC wW wC sW sC := by
  rw [qubits_saving_eq_balanced P Rule hx]
  omega

/-- **Saving exactly `xW - 1` iff the multiplication set the old peak (every site
split).** -/
theorem qubits_saving_eq_iff_U (P : ShorLoweringPolicy) (Rule : Balanced.Rule) {xW : ℕ}
    (hx : 1 ≤ xW) (dW wW sW : ℕ) :
    Policy.orderFindingQubitsUSC P Rule dW wW sW
        = Policy.orderFindingQubitsU P Rule xW dW wW sW - (xW - 1)
      ↔ qftPeakD P.negation P.widthRule (Policy.compile P) xW
          ≤ Policy.orderFindingPeakUSC P Rule dW wW sW := by
  rw [qubits_saving_eq_U P Rule hx]
  omega

end Readout
end Shor
