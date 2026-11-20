import ForShor.ShorVerification.Implementation.Readout.Proofs.Locality
import ForShor.ShorVerification.Implementation.Readout.Main
import ForShor.ShorVerification.Implementation.Readout.Proofs.LowerClean
import ForShor.ShorVerification.Implementation.Readout.Proofs.GhostFreeSetup

/-!
# Readout: the semiclassical circuits do not depend on any qubit they do not name

Semantic locality of the semiclassical circuits. `flipBit q b` is `b` with bit `q` flipped
(the `X q` ket law), `flipBits l b` flips the qubits of a list. The general machinery (any
`Gate` / `MGate` program without an `idealCtrlModMul` node, adjoints included) is in
`Proofs/Locality.lean`. Here, for finitely many differing qubits:

* **T1, ideal circuit** (`semiclassicalIdeal`, closed form): if `b₀` has data `= 1` and
  `c = 0` (the hypotheses of `semiclassical_branch_state`), every branch from
  `|flipBit q b₀⟩` is `X q` of the branch from `|b₀⟩` for `q ∉ data`, `q ≠ c`
  (`semiclassicalIdeal_branch_flipBit`), so every record probability is unchanged
  (`semiclassicalIdeal_recordProb_flipBits`, `semiclassicalIdeal_recordProb_of_agree`).
* **T3, real circuit** (`orderFindingSemiclassical`, real `CmodMulInPlaceCore`, `initY1`): NO
  hypothesis on the registers or the start ket. Every branch from a ket flipped at a qubit
  outside `semiclassicalQubits c y work scratch flag` (control, owned qubits of
  `y`/`work`/`scratch`, flag) is `X q` of the original branch
  (`orderFindingSemiclassical_branch_flipBit`); record probabilities and the success
  probability are equal for any two start kets that agree on `semiclassicalQubits` and differ at
  finitely many qubits (`orderFindingSemiclassical_recordProb_of_agree`,
  `orderFindingSemiclassical_success_of_agree`). The ghost-free setup carries over to such a
  ket (`SemiclassicalGhostFreeSetup.ofAgree`); on the coherent layout (`ShorApproxSetup`) every
  exponent qubit other than `c` may be flipped (`orderFindingSemiclassical_recordProb_flip_exponent`).
* **T4, lowered circuit** (`orderFindingSemiclassicalLow`): the same, under the hypotheses of
  `semiclassical_lowerM_eval` for `b0` (admissible policy, layout, zero reserves, zero scratch);
  these hypotheses then hold for `b0'` too because they mention only named registers
  (`semiclassicalWorkspaceCleanInput_ofAgree`, `toNat_ofAgree`).

Why finitely many: the abstract basis may carry infinitely many bits, and the argument is one
`X q` per differing qubit.

## What "unnamed" means, and what is NOT covered

"Unnamed" is SYNTACTIC: outside the owned-qubit support. For the real and lowered circuits it
is `q ∉ semiclassicalQubits c y work scratch flag`, a set that contains the control, EVERY owned
qubit of `y`, `work`, `scratch` (active AND reserve) and the flag; for a general program it is
`q ∉ P.qubitSupport`, which counts an `ExtReg` operand with all its owned qubits. So:

* reserve (spare) qubits of `y`, `work`, `scratch` are NOT covered: they are named (the
  lowering may allocate workspace there), even when a given run never touches them;
* qubits that are named but never actually acted on are NOT covered either: the theorems say
  nothing about them in either direction;
* the control `c` and the data qubits are named, and locality genuinely fails for named qubits
  (`LocalityTests.measureReset_flip_named`); this is why the success theorems need the control
  to start at `0` and the data at `1`.

The second half of the spectator statement (commutation with the Z projectors of an unnamed
qubit, record decomposition, a spectator in superposition) is in
`Proofs/LocalityProj.lean` and `LocalitySpectator.lean` (T5).

Extensions live in separate files: exact support and unused reserve qubits
(`LocalityReserve`), the ideal multiplier on its domain (`LocalityIdeal`), infinitely many
differing qubits (`LocalityInfinite`, `LocalityInfiniteSuperpose`), and locality directly at the
low-gate level, with no clean-workspace hypothesis (`LowLocality`, `LowLocalityNamed`,
`LowLocalityBalanced`).
-/

namespace Shor
namespace Readout

/-! ## Helpers -/

section Helpers
variable {B : Type*} [RegEncoding B]

theorem toNat_flipBits {r : Reg} {l : List ℕ} (h : ∀ q ∈ l, q ∉ r.qubits) (b : B) :
    RegEncoding.toNat r (flipBits l b) = RegEncoding.toNat r b := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [flipBits_cons, toNat_flipBit (h q (List.mem_cons_self ..)),
      ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]

theorem bit_flipBits_of_not_mem {p : ℕ} {l : List ℕ} (h : ∀ q ∈ l, q ≠ p) (b : B) :
    RegEncoding.bit p (flipBits l b) = RegEncoding.bit p b := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [flipBits_cons, bit_flipBit_ne (Ne.symm (h q (List.mem_cons_self ..))),
      ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]

/-- A register's value is the same in two basis states that agree on a set containing its
qubits. -/
theorem toNat_ofAgree {S : Set ℕ} {r : Reg} (hr : ∀ p ∈ r.qubits, p ∈ S) {b b' : B}
    (hagree : ∀ p ∈ S, RegEncoding.bit p b' = RegEncoding.bit p b) :
    RegEncoding.toNat r b' = RegEncoding.toNat r b :=
  toNat_congr_bits' r fun p hp => hagree p (hr p hp)

end Helpers

theorem numMeas_readoutRounds (U : ℕ → Gate) (c m : ℕ) : (readoutRounds U c m).numMeas = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [readoutRounds, MGate.numMeas, ih]

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-! ## T1: the ideal circuit, from the closed form -/

/-- **T1, state level.** Hypotheses of `semiclassical_branch_state`: `1 < N ≤ 2^|data|`, `a`
coprime to `N`, `c ∉ data`, and `b₀` has data `= 1` and `c = 0`. For every qubit `q` outside
`data` and `≠ c`, every record `r`: the branch of the ideal semiclassical readout from
`|flipBit q b₀⟩` at `r` is `X q` of the branch from `|b₀⟩`. -/
theorem semiclassicalIdeal_branch_flipBit (a N m : ℕ) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hdata1 : RegEncoding.toNat data b₀ = 1) (hc0 : RegEncoding.bit c b₀ = false)
    {q : ℕ} (hqd : q ∉ data.qubits) (hqc : q ≠ c) (r : Record) :
    (semiclassicalIdeal a N m data c).eval (MState.init (qs.ket (flipBit q b₀))) r
      = qs.eval (Gate.X q) ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b₀)) r) := by
  by_cases hr : r.length = m
  · have hx : regSize (ExtReg.ofReg (Reg.interval 0 m)).active = m := regSize_interval 0 m
    have key : ∀ b : qs.Basis, RegEncoding.toNat data b = 1 → RegEncoding.bit c b = false →
        (semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b)) r
          = (1 / 2 ^ m : ℂ) • ∑ κ ∈ Finset.range (2 ^ m),
              Complex.exp (-(2 * Real.pi * Complex.I * ((readoutOfRecord r : ℂ) * κ) / 2 ^ m)) •
              qs.ket (RegEncoding.writeNat data (a ^ κ % N) b) := by
      intro b h1 h0
      have := semiclassical_branch_state a N (ExtReg.ofReg (Reg.interval 0 m)) data c b hN hNdata
        ha hc h1 h0 r (hr.trans hx.symm)
      rwa [hx] at this
    rw [key _ (by rwa [toNat_flipBit hqd]) (by rwa [bit_flipBit_ne (Ne.symm hqc)]),
      key _ hdata1 hc0, ← gateL_apply, map_smul, map_sum]
    simp only [map_smul, gateL_apply, writeNat_flipBit hqd, eval_X_ket_flipBit]
  · have hm : (semiclassicalIdeal a N m data c).numMeas = m := numMeas_readoutRounds _ c m
    rw [MGate.eval_init_support _ _ r (by rwa [hm]), MGate.eval_init_support _ _ r (by rwa [hm]),
      MGate.gate_eval_zero_state]

/-- **T1, one flip.** Same hypotheses: the record distribution of the ideal semiclassical
readout is the same from `|flipBit q b₀⟩` as from `|b₀⟩`, for `q ∉ data`, `q ≠ c`. -/
theorem semiclassicalIdeal_recordProb_flipBit (a N m : ℕ) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hdata1 : RegEncoding.toNat data b₀ = 1) (hc0 : RegEncoding.bit c b₀ = false)
    {q : ℕ} (hqd : q ∉ data.qubits) (hqc : q ≠ c) (r : Record) :
    recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket (flipBit q b₀)))) r
      = recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b₀))) r := by
  rw [recordProb, recordProb, semiclassicalIdeal_branch_flipBit a N m data c b₀ hN hNdata ha hc
    hdata1 hc0 hqd hqc r, norm_eval_gate]

/-- **T1, finitely many flips.** Same hypotheses on `b₀`; `l` any list of qubits outside `data`
and different from `c`. -/
theorem semiclassicalIdeal_recordProb_flipBits (a N m : ℕ) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hdata1 : RegEncoding.toNat data b₀ = 1) (hc0 : RegEncoding.bit c b₀ = false)
    (l : List ℕ) (hl : ∀ q ∈ l, q ∉ data.qubits ∧ q ≠ c) (r : Record) :
    recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket (flipBits l b₀)))) r
      = recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b₀))) r := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    have hl' : ∀ q' ∈ l, q' ∉ data.qubits ∧ q' ≠ c := fun q' h => hl q' (List.mem_cons_of_mem _ h)
    rw [flipBits_cons, semiclassicalIdeal_recordProb_flipBit a N m data c _ hN hNdata ha hc
      (by rw [toNat_flipBits (fun q' h => (hl' q' h).1)]; exact hdata1)
      (by rw [bit_flipBits_of_not_mem (fun q' h => (hl' q' h).2)]; exact hc0)
      (hl q (List.mem_cons_self ..)).1 (hl q (List.mem_cons_self ..)).2 r, ih hl']

/-- **T1, agreement form.** Same hypotheses on `b₀`. If `b₀'` agrees with `b₀` on every qubit
of `data` and on `c`, and the two differ at only finitely many qubits, every record of the ideal
semiclassical readout has the same probability from `|b₀'⟩` as from `|b₀⟩`. -/
theorem semiclassicalIdeal_recordProb_of_agree (a N m : ℕ) (data : Reg) (c : ℕ)
    (b₀ b₀' : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hdata1 : RegEncoding.toNat data b₀ = 1) (hc0 : RegEncoding.bit c b₀ = false)
    (hagree : ∀ p, p ∈ data.qubits ∨ p = c → RegEncoding.bit p b₀' = RegEncoding.bit p b₀)
    (hfin : {p | RegEncoding.bit p b₀' ≠ RegEncoding.bit p b₀}.Finite) (r : Record) :
    recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b₀'))) r
      = recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b₀))) r := by
  conv_lhs => rw [eq_flipBits_of_finite b₀ b₀' hfin]
  refine semiclassicalIdeal_recordProb_flipBits a N m data c b₀ hN hNdata ha hc hdata1 hc0 _
    (fun q hq => ?_) r
  simp only [Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hq
  exact ⟨fun h => hq (hagree q (Or.inl h)), fun h => hq (hagree q (Or.inr h))⟩

/-! ## T3: the real circuit -/

theorem H_reg_noIdeal (r : Reg) : (H_reg r).NoIdeal := by
  have key : ∀ (l : List ℕ) (acc : Gate), acc.NoIdeal →
      (l.foldl (fun acc q => Gate.H q ;; acc) acc).NoIdeal := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons a l ih => intro acc h; exact ih _ ⟨trivial, h⟩
  exact key _ _ trivial

/-- The real multiplier has no `idealCtrlModMul` node. -/
theorem cmodMul_noIdeal {cm N c flag : ℕ} {y work scratch : ExtReg}
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    (CmodMulInPlaceCore cm N c y work scratch flag hw hs4).NoIdeal := by
  simp [CmodMulInPlaceCore, step1, step2, step3, step4, step5, cmpLtNW, fastConstMulInto,
    cmpLtNWDifference, IQFT, Gate.PhaseProdUsing, Gate.CPhaseProdUsing, Gate.NoIdeal,
    H_reg_noIdeal]

/-- The real semiclassical circuit has no `idealCtrlModMul` node. -/
theorem orderFindingSemiclassical_noIdeal (a N c m : ℕ) {y work scratch : ExtReg} {flag : ℕ}
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    (orderFindingSemiclassical a N c m y work scratch flag hw hs4).NoIdeal := by
  have hr : ∀ k, (readoutRounds (semiclassicalMultipliers a N c m y work scratch flag hw hs4)
      c k).NoIdeal := by
    intro k
    induction k with
    | zero => exact trivial
    | succ k ih =>
      exact ⟨ih, trivial, cmodMul_noIdeal hw hs4, trivial, trivial, trivial⟩
  exact ⟨by simp [initY1]; split <;> trivial, hr m⟩

/-- An unnamed qubit of the semiclassical circuit is not in its syntactic support. -/
theorem not_mem_orderFindingSemiclassical_support {a N c m : ℕ} {y work scratch : ExtReg}
    {flag q : ℕ} (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hq : q ∉ semiclassicalQubits c y work scratch flag) :
    q ∉ (orderFindingSemiclassical a N c m y work scratch flag hw hs4).qubitSupport :=
  fun h => hq (orderFindingSemiclassical_support a N m hw hs4 h)

/-- **T3, state level.** For ANY registers and ANY start ket `b0` (no hypothesis), and any qubit
`q` outside `semiclassicalQubits c y work scratch flag` (not the control, not an owned qubit of
`y`, `work` or `scratch`, not the flag): every branch of the real semiclassical circuit run from
`|flipBit q b0⟩` is `X q` of the branch run from `|b0⟩`. -/
theorem orderFindingSemiclassical_branch_flipBit (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 : qs.Basis) {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (r : Record) :
    (orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket (flipBit q b0))) r
      = qs.eval (Gate.X q) ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0)) r) := by
  rw [← eval_X_ket_flipBit]
  exact MGate.eval_init_X _ (orderFindingSemiclassical_noIdeal a N c m hw hs4)
    (not_mem_orderFindingSemiclassical_support hw hs4 hq) _ r

/-- **T3, finitely many flips.** For any registers and start ket `b0`, and any list `l` of
qubits outside `semiclassicalQubits c y work scratch flag`, every record has the same
probability from `|flipBits l b0⟩` as from `|b0⟩`. -/
theorem orderFindingSemiclassical_recordProb_flipBits (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 : qs.Basis) (l : List ℕ)
    (hl : ∀ q ∈ l, q ∉ semiclassicalQubits c y work scratch flag) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket (flipBits l b0)))) r
      = recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0))) r :=
  MGate.recordProb_flipBits _ (orderFindingSemiclassical_noIdeal a N c m hw hs4) l
    (fun q hq => not_mem_orderFindingSemiclassical_support hw hs4 (hl q hq)) b0 r

/-- **T3, agreement form (the real circuit cannot depend on a qubit it does not name).** For any
registers and any two start kets `b0`, `b0'` that agree on every qubit of
`semiclassicalQubits c y work scratch flag` and differ at only finitely many qubits, every record
`r` has the same probability. -/
theorem orderFindingSemiclassical_recordProb_of_agree (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 b0' : qs.Basis)
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (hfin : {p | RegEncoding.bit p b0' ≠ RegEncoding.bit p b0}.Finite) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0'))) r
      = recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0))) r :=
  MGate.recordProb_of_agree _ (orderFindingSemiclassical_noIdeal a N c m hw hs4) b0 b0'
    (fun p hp => hagree p (orderFindingSemiclassical_support a N m hw hs4 hp)) hfin r

/-- **T3, success.** Same hypotheses as `orderFindingSemiclassical_recordProb_of_agree`: the
success probability (`probability_of_success_M`, any `T`, `verify`, `r`, `Q`) of the real
circuit is the same from `|b0'⟩` as from `|b0⟩`. -/
theorem orderFindingSemiclassical_success_of_agree (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 b0' : qs.Basis)
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (hfin : {p | RegEncoding.bit p b0' ≠ RegEncoding.bit p b0}.Finite)
    (T : ℕ → ℕ) (verify : ℕ → Bool) (r Q : ℕ) :
    probability_of_success_M T verify m r Q
        ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
          (MState.init (qs.ket b0')))
      = probability_of_success_M T verify m r Q
        ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
          (MState.init (qs.ket b0))) :=
  probability_of_success_M_congr T verify m r Q fun rec =>
    orderFindingSemiclassical_recordProb_of_agree a N c m y work scratch flag hw hs4 b0 b0'
      hagree hfin rec

section Setup
variable {c flag : ℕ} {y work scratch : ExtReg}

theorem mem_semiclassicalQubits_y {p : ℕ} (h : p ∈ y.ownedQubits) :
    p ∈ semiclassicalQubits c y work scratch flag := Or.inr (Or.inl h)
theorem mem_semiclassicalQubits_work {p : ℕ} (h : p ∈ work.ownedQubits) :
    p ∈ semiclassicalQubits c y work scratch flag := Or.inr (Or.inr (Or.inl h))
theorem mem_semiclassicalQubits_scratch {p : ℕ} (h : p ∈ scratch.ownedQubits) :
    p ∈ semiclassicalQubits c y work scratch flag := Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem active_sub {e : ExtReg} : ∀ p ∈ e.active.qubits, p ∈ e.ownedQubits :=
  fun _ h => List.mem_append_left _ h
theorem reserve_sub {e : ExtReg} : ∀ p ∈ e.reserve.qubits, p ∈ e.ownedQubits :=
  fun _ h => List.mem_append_right _ h
theorem newBits_sub {e : ExtReg} (n : ℕ) : ∀ p ∈ (e.newBits n).qubits, p ∈ e.ownedQubits :=
  fun _ h => List.mem_append_right _ (List.mem_of_mem_take h)

omit [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
/-- The clean-reserve hypothesis of the lowered theorems carries over to a ket that agrees on
`semiclassicalQubits`: it mentions only the reserves of `y`, `work`, `scratch`. -/
theorem semiclassicalWorkspaceCleanInput_ofAgree {b0 b0' : qs.Basis}
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (h : SemiclassicalWorkspaceCleanInput y work scratch b0) :
    SemiclassicalWorkspaceCleanInput y work scratch b0' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · unfold FreshZero at h1 ⊢
    rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_y (reserve_sub p hp)) hagree, h1]
  · unfold FreshZero at h2 ⊢
    rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_work (reserve_sub p hp)) hagree, h2]
  · unfold FreshZero at h3 ⊢
    rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_scratch (reserve_sub p hp)) hagree, h3]

omit [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
/-- **The ghost-free setup carries over.** Every field of `SemiclassicalGhostFreeSetup` for `b0`
holds for any `b0'` that agrees with `b0` on `semiclassicalQubits c y work scratch flag`: its
ket fields read only the data, work, scratch registers (and spares), the flag and `c`. -/
def SemiclassicalGhostFreeSetup.ofAgree {η : ℝ} {N : ℕ} {b0 b0' : qs.Basis}
    (h : SemiclassicalGhostFreeSetup qs η N c y work scratch flag b0)
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0) :
    SemiclassicalGhostFreeSetup qs η N c y work scratch flag b0' where
  layout := h.layout
  circuit_workspace := h.circuit_workspace
  step4_workspace := h.step4_workspace
  work_precision := h.work_precision
  clean_input := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h.clean_input
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_y (active_sub p hp)) hagree, h1]
    · unfold ExtReg.FreshFor FreshZero at h2 ⊢
      rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_y (newBits_sub 2 p hp)) hagree, h2]
    · rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_work (active_sub p hp)) hagree, h3]
    · unfold ExtReg.FreshFor FreshZero at h4 ⊢
      rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_work (newBits_sub 1 p hp)) hagree,
        h4]
    · rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_scratch (active_sub p hp)) hagree,
        h5]
    · unfold ExtReg.FreshFor FreshZero at h6 ⊢
      rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_scratch (newBits_sub 1 p hp))
        hagree, h6]
    · rw [toNat_ofAgree (S := semiclassicalQubits c y work scratch flag) (fun p hp => by
          simp only [qubitReg, Reg.singleton, List.mem_singleton] at hp
          exact Or.inr (Or.inr (Or.inr (Or.inr hp)))) hagree, h7]
  control_zero := by rw [hagree c (Or.inl rfl)]; exact h.control_zero

end Setup

/-- **T3 on the coherent layout: the exponent register is irrelevant.** Under a
`ShorApproxSetup` (the coherent circuit's setup, which places the exponent register `x`), for
ANY start ket `b0` and any list `l` of exponent qubits other than the control `c`, the real
semiclassical circuit (on `y`, `work`, `scratch`, `flag`, control `c`) has the same record
distribution from `|flipBits l b0⟩` as from `|b0⟩`. -/
theorem orderFindingSemiclassical_recordProb_flip_exponent {η : ℝ} {N c : ℕ}
    {x y work scratch : ExtReg} {flag : ℕ} {b0 : qs.Basis}
    (h : ShorApproxSetup qs η N x y work scratch flag b0) (a m : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b : qs.Basis) (l : List ℕ)
    (hl : ∀ q ∈ l, q ∈ x.active.qubits ∧ q ≠ c) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket (flipBits l b)))) r
      = recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b))) r :=
  orderFindingSemiclassical_recordProb_flipBits a N c m y work scratch flag hw hs4 b l
    (fun q hq => exponent_outside_semiclassicalQubits h q (hl q hq).1 (hl q hq).2) r

/-! ## T4: the lowered circuit -/

/-- **T4, agreement form.** Hypotheses of `semiclassical_lowerM_eval` for `b0`: admissible
policy `P`, lowering workspace `hws`, `SemiclassicalLayout c y work scratch flag`, zero data /
work / scratch reserves in `b0`, zero scratch register in `b0`. For any `b0'` that agrees with
`b0` on `semiclassicalQubits c y work scratch flag` and differs at finitely many qubits, every
record of the LOWERED circuit `orderFindingSemiclassicalLow` has the same probability from
`|b0'⟩` as from `|b0⟩`. (The clean hypotheses hold for `b0'` too; proved inside.) -/
theorem orderFindingSemiclassicalLow_recordProb_of_agree {P : ShorLoweringPolicy}
    (hP : P.Admissible) (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 b0' : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0)
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (hfin : {p | RegEncoding.bit p b0' ≠ RegEncoding.bit p b0}.Finite) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (qs.ket b0'))) r
      = recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (qs.ket b0))) r := by
  have hzero' := semiclassicalWorkspaceCleanInput_ofAgree hagree hzero
  have hscratch' : RegEncoding.toNat scratch.active b0' = 0 := by
    rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_scratch (active_sub p hp)) hagree,
      hscratch]
  rw [orderFindingSemiclassicalLow,
    semiclassical_lowerM_eval hP a N c m y work scratch flag hw hs4 hws hl b0' hzero' hscratch',
    semiclassical_lowerM_eval hP a N c m y work scratch flag hw hs4 hws hl b0 hzero hscratch]
  exact orderFindingSemiclassical_recordProb_of_agree a N c m y work scratch flag hw hs4 b0 b0'
    hagree hfin r

/-- **T4, finitely many flips.** Same hypotheses on `b0` as
`orderFindingSemiclassicalLow_recordProb_of_agree`; `l` any list of qubits outside
`semiclassicalQubits c y work scratch flag`. -/
theorem orderFindingSemiclassicalLow_recordProb_flipBits {P : ShorLoweringPolicy}
    (hP : P.Admissible) (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0) (l : List ℕ)
    (hlq : ∀ q ∈ l, q ∉ semiclassicalQubits c y work scratch flag) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (qs.ket (flipBits l b0)))) r
      = recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (qs.ket b0))) r := by
  have hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p (flipBits l b0) = RegEncoding.bit p b0 := fun p hp =>
    bit_flipBits_of_not_mem (fun q hq e => hlq q hq (e ▸ hp)) b0
  have hzero' := semiclassicalWorkspaceCleanInput_ofAgree hagree hzero
  have hscratch' : RegEncoding.toNat scratch.active (flipBits l b0) = 0 := by
    rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_scratch (active_sub p hp)) hagree,
      hscratch]
  rw [orderFindingSemiclassicalLow,
    semiclassical_lowerM_eval hP a N c m y work scratch flag hw hs4 hws hl _ hzero' hscratch',
    semiclassical_lowerM_eval hP a N c m y work scratch flag hw hs4 hws hl b0 hzero hscratch]
  exact orderFindingSemiclassical_recordProb_flipBits a N c m y work scratch flag hw hs4 b0 l
    hlq r

/-- **T4, success.** Same hypotheses as `orderFindingSemiclassicalLow_recordProb_of_agree`: the
success probability of the lowered circuit is the same from `|b0'⟩` as from `|b0⟩`. -/
theorem orderFindingSemiclassicalLow_success_of_agree {P : ShorLoweringPolicy}
    (hP : P.Admissible) (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 b0' : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0)
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (hfin : {p | RegEncoding.bit p b0' ≠ RegEncoding.bit p b0}.Finite)
    (T : ℕ → ℕ) (verify : ℕ → Bool) (r Q : ℕ) :
    probability_of_success_M T verify m r Q
        ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
          (MState.init (qs.ket b0')))
      = probability_of_success_M T verify m r Q
        ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
          (MState.init (qs.ket b0))) :=
  probability_of_success_M_congr T verify m r Q fun rec =>
    orderFindingSemiclassicalLow_recordProb_of_agree hP a N c m y work scratch flag hw hs4 hws hl
      b0 b0' hzero hscratch hagree hfin rec

end Readout
end Shor
