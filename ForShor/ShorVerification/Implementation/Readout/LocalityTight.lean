import ForShor.ShorVerification.Implementation.Readout.Proofs.LocalityTight

/-!
# Readout: which reserve qubits in the exact support the real circuit reads, and one over-count

`Readout/LocalityReserve.lean` proves that the first two reserve qubits of `y`, the first of
`work` and the first of `scratch` lie in the EXACT support of the real circuit (`reserve_used`,
membership only: the exact support is an UPPER bound). This file decides, for each of them,
whether a step of the multiplier `CmodMulInPlaceCore` reads it, in the sense of non-commutation
with `X q` (high-level semantics, `qs` abstract):

| qubit | gate of `CmodMulInPlaceCore` | result |
|---|---|---|
| `y.reserve[0]` (carry of `y.grow 1`) | the WHOLE Step 3 `step3 = CmpGeConst ;; CSubConst` | does NOT commute, if `1 ≤ N ≤ 2^|y|` (`step3_not_commX_carry`; named sub-gate form `step3Cmp_not_commX_carry`) |
| `y.reserve[1]` (sign of `(y.grow 1).grow 1`) | the WHOLE Step 4 `step4 = cmpLtNW = mul ;; diff ;; CNOT ;; †diff ;; †mul` | does NOT commute (`step4_not_commX_ySign`; named sub-gate form `cmpLtNWDifference_not_commX_ySign`) |
| `work.reserve[0]` (x sign bit of Step 4's phase product) | the named sub-gate `fastConstMulInto` (= `mul`) of Step 4 | named sub-gate reads it, if `1 ≤ N` (`fastConstMulInto_not_commX_workSign`); whole Step 4 NOT proved |
| `scratch.reserve[0]` (z sign bit of Step 4's phase product) | every node of the multiplier | DOES commute (with `X q` and the Z projectors of `q`) when `q` is not the control: one proved over-count (`cmodMul_gateLocal_refined`, `scratchSign_mem_exact_not_mem_refined`) |

Caveats on these read theorems:

* A read theorem for one step does NOT imply that the whole multiplier, or the whole circuit,
  fails to commute with `X q`: the other steps may undo the effect.
* For `work.reserve[0]` only the sub-gate `mul` is shown to read it. Step 4 also contains `†mul`;
  in the whole step the effects of `mul` and `†mul` on `q` could cancel. The whole-step argument
  used for `y.reserve[1]` (the two `mul` blocks commute with `X q`, so they can be peeled off)
  does not apply, because here it is exactly `mul` that reads `q`. Not attempted further.
* No statement here is about record probabilities of the real circuit changing; that is open
  (no computable evaluation of the real circuit's amplitudes). The proofs file contains only a
  stand-in (`toyPhaseKick_recordProb`): a 4-qubit program `H z ; PhaseProdUsing (1/2) x z ;
  H z ; measureReset z` with ONE-qubit operands and angle `1/2`, chosen so that the phase
  becomes a `Z` between two `H`s. It shares the macro, not the angles, widths or structure of
  the real circuit.

## The refined set: an upper bound, minus one proved over-count

`scratch.reserve[0]` enters the high-level circuit only as the `z` sign-extension bit of Step 4's
`PhaseProdUsing (2N/2^|scratch|) work scratch`. Flipping it shifts the signed `z` value by
`± 2^|scratch|`, so the phase changes by `exp(± iπ · 2N/2^|scratch| · x · 2^|scratch|) =
exp(± 2πi N x) = 1` (`signedPhaseProd_grow_commX_top`). Hence every node of the real circuit
is local at every qubit outside

  `semiclassicalExactQubitsRefined c y work scratch flag` = the old exact support bound
  `semiclassicalExactQubits` minus this one proved over-count, `scratch.newBits 1`

(`orderFindingSemiclassical_localAt_refined`), and the exact-support corollaries hold for it:
`orderFindingSemiclassical_recordProb_flipBits_refined`, `…_of_agree_refined`,
`…_superpose_refined`, `…_decomp_refined`, and for the dropped qubit itself
`orderFindingSemiclassical_recordProb_flip_scratchSign` (under `SemiclassicalLayout`, which keeps
the control off `scratch`). The statements of `Readout/LocalityReserve.lean` are unchanged.

The refined set is still only an UPPER bound. Its parts with a read theorem (at the gates in the
table above): `y.reserve[0]`, `y.reserve[1]`, `work.reserve[0]`. Its parts with NO read (lower
bound) theorem here: the control `c`, the flag, and the active qubits of `y`, `work` and
`scratch`.

The LOWERED circuit still reads `scratch.newBits 1`: in the lowering of Step 3 it is the
comparator's unit qubit (`constArithmeticUnitQubit scratch _`, `Compiler/Statement.lean`;
`constArithmeticUnitQubit_mem_newBits` below identifies it), and the lowered comparator is
correct only when it starts at `0` (`ConstArithmeticCleanBasis`). So the refinement is a
statement about the HIGH-LEVEL circuit only; nothing is claimed about the lowered circuit with
that qubit flipped.

## What is NOT claimed

* Any change of a record probability of the real circuit (open).
* Non-commutation of the whole multiplier or circuit for any reserve qubit; non-commutation of
  the whole Step 4 for `work.reserve[0]`.
* Any lower bound for the control, the flag, or the active qubits.
* Anything about the lowered circuit on a flipped reserve qubit.
-/

namespace Shor

/-- The refined set of qubits the real semiclassical circuit acts on: `semiclassicalExactQubits`
without the first reserve qubit of `scratch` (`scratch.newBits 1`), which every node of the
circuit commutes with (`Readout.orderFindingSemiclassical_localAt_refined`). -/
def semiclassicalExactQubitsRefined (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) : Set ℕ :=
  {q | q = c ∨ q ∈ y.active.qubits ∨ q ∈ (y.newBits 2).qubits ∨ q ∈ work.active.qubits ∨
    q ∈ (work.newBits 1).qubits ∨ q ∈ scratch.active.qubits ∨ q = flag}

namespace Readout

open MeasureClass

section Static
variable {c flag : ℕ} {y work scratch : ExtReg}

theorem ownedDisjoint_y_scratch {N : ℕ} (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    ExtReg.OwnedDisjoint y scratch := by
  have h := hs4.data_scratch_disjoint
  unfold ExtReg.OwnedDisjoint at h ⊢
  rwa [Gate.ExtReg.ownedQubits_grow] at h

theorem mem_grow_one_active {e : ExtReg} {p : ℕ} :
    p ∈ (e.grow 1).active.qubits ↔ p ∈ e.active.qubits ∨ p ∈ (e.newBits 1).qubits := by
  simp [ExtReg.grow, Reg.append]

theorem mem_grow_grow_active {e : ExtReg} {p : ℕ} (h : p ∈ ((e.grow 1).grow 1).active.qubits) :
    p ∈ e.active.qubits ∨ p ∈ (e.newBits 2).qubits := by
  rcases mem_grow_one_active.mp h with h | h
  · rcases mem_grow_one_active.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (mem_take_two_of_take_one h)
  · refine Or.inr (mem_take_two_of_take_one_drop_one ?_)
    simpa [ExtReg.newBits, ExtReg.grow, ExtReg.remainingReserve, Reg.take, Reg.drop] using h

theorem mulWorkspace_xExt_newBits {N : ℕ} (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    hs4.mulWorkspace.xExt.newBits 1 = work.newBits 1 := by
  show hs4.mulWorkspace.xReserve.take 1 = work.reserve.take 1
  rw [hs4.mul_xReserve_eq]

theorem mulWorkspace_zExt_newBits {N : ℕ} (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    hs4.mulWorkspace.zExt.newBits 1 = scratch.newBits 1 := by
  show hs4.mulWorkspace.zReserve.take 1 = scratch.reserve.take 1
  rw [hs4.mul_zReserve_eq]

theorem semiclassicalExactQubitsRefined_subset :
    semiclassicalExactQubitsRefined c y work scratch flag
      ⊆ semiclassicalExactQubits c y work scratch flag := by
  rintro q (h | h | h | h | h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- **The refinement removes exactly the scratch sign qubit.** Under the Step-4 workspace
hypothesis `hs4` (which makes `scratch` disjoint from `y`, `work` and the flag) and with the
control off `scratch` (`hc`), the first reserve qubit of `scratch` is in
`semiclassicalExactQubits` but not in `semiclassicalExactQubitsRefined`. -/
theorem scratchSign_mem_exact_not_mem_refined (N : ℕ)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (hc : c ∉ scratch.ownedQubits)
    {q : ℕ} (hq : q ∈ (scratch.newBits 1).qubits) :
    q ∈ semiclassicalExactQubits c y work scratch flag ∧
      q ∉ semiclassicalExactQubitsRefined c y work scratch flag := by
  have hqo : q ∈ scratch.ownedQubits := mem_owned_of_newBits hq
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq)))))), ?_⟩
  have hys : ExtReg.OwnedDisjoint y scratch := ownedDisjoint_y_scratch hs4
  have hws := hs4.work_scratch_disjoint
  rintro (h | h | h | h | h | h | h)
  · exact hc (h ▸ hqo)
  · exact hys (mem_owned_of_active h) hqo
  · exact hys (mem_owned_of_newBits h) hqo
  · exact hws (mem_owned_of_active h) hqo
  · exact hws (mem_owned_of_newBits h) hqo
  · exact not_mem_active_of_newBits hq h
  · exact hs4.flag_not_scratch (h ▸ hqo)

end Static


/-! ## Reads at the steps (and named sub-gates) of the multiplier -/

section SubGates
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
variable {c flag : ℕ} {y work scratch : ExtReg}

/-- Where the first gate below sits: Step 3 is `CmpGeConst ;; CSubConst`. -/
theorem step3_eq (N : ℕ) (d s : ExtReg) (f : ℕ) :
    step3 N d s f = Gate.CmpGeConst N d s f ;; Gate.CSubConst N d s f := rfl

/-- **Named sub-gate read: `y.reserve[0]` (Step 3's comparator).** Under the Step-4 workspace hypothesis
`hs4` (used only for: the flag is not a qubit of `y`) and `1 ≤ N ≤ 2^|y.active|`, for the first
reserve qubit `q` of `y`, the first gate of Step 3, `Gate.CmpGeConst N (y.grow 1) scratch flag`,
does not commute with `X q`. NOT claimed: non-commutation of Step 3, of the multiplier, or a
change of any record probability. -/
theorem step3Cmp_not_commX_carry {N : ℕ} (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hN1 : 1 ≤ N) (hN2 : N ≤ 2 ^ regSize y.active) {q : ℕ} (hq : q ∈ (y.newBits 1).qubits) :
    ¬ CommX qs (Gate.CmpGeConst N (y.grow 1) scratch flag) q :=
  cmpGeConst_grow_not_commX hq (fun h => hs4.flag_not_data (List.mem_append_left _ h)) hN1 hN2

/-- **Named sub-gate read: `y.reserve[1]` (Step 4's difference block).** Under the circuit's workspace
hypotheses (`hs4`; the reserve of `y` has two qubits because `q` exists), for the second reserve
qubit `q` of `y` (the first reserve qubit of `y.grow 1`), the block
`cmpLtNWDifference (y.grow 1) work scratch _` of Step 4 does not commute with `X q`: its
`AddScaled` adds `2^|work| · (y.grow 1).grow 1` to `scratch`, and flipping `q` changes that by
`2^(|work| + |y| + 1)`, nonzero modulo `2^|scratch|`. NOT claimed: non-commutation of Step 4, of
the multiplier, or a change of any record probability. -/
theorem cmpLtNWDifference_not_commX_ySign {N : ℕ}
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) {q : ℕ}
    (hq : q ∈ ((y.grow 1).newBits 1).qubits) :
    ¬ CommX qs (cmpLtNWDifference (y.grow 1) work scratch hs4.data_can_grow) q := by
  have hd : ExtReg.OwnedDisjoint y scratch := ownedDisjoint_y_scratch hs4
  have hy1 : y.CanGrow 1 := ExtReg.CanGrow.mono (canGrow_two_of_mem_grow hq) (by norm_num)
  have hwidth : regSize y.active + 1 + regSize work.active < regSize scratch.active := by
    rw [hs4.scratch_width, cmpLtNWWidth, regSize_grow_active hy1]
    have := le_max_left (regSize y.active + 1 + regSize work.active)
      (Nat.log2 (N + 1) + 1 + regSize work.active)
    omega
  have hAS := addScaled_growgrow_not_commX (qs := qs) (sh := regSize work.active) hq hd hwidth
  have hqo : q ∈ y.ownedQubits :=
    mem_owned_of_mem_grow_grow_active (mem_grow_active_of_newBits hq)
  have hqs : q ∉ scratch.active.qubits := fun h => hd hqo (mem_owned_of_active h)
  unfold cmpLtNWDifference
  refine not_commX_seq_left
    (gate_commX_exact (Gate.zeroExtend (y.grow 1) 1) trivial (by simp [Gate.exactSupport])) ?_
  refine not_commX_seq_left
    (gate_commX_exact (Gate.Negate scratch) trivial (by simpa [Gate.exactSupport] using hqs)) ?_
  exact not_commX_seq_right
    (gate_commX_exact (Gate.zeroDealloc (y.grow 1) 1) trivial (by simp [Gate.exactSupport])) hAS

/-- **Named sub-gate read: `work.reserve[0]` (Step 4's constant multiplier).** Under `hs4` and `1 ≤ N`, for the
first reserve qubit `q` of `work`, the block `fastConstMulInto N work scratch _` of Step 4 (QFT on
`scratch`, `PhaseProdUsing (2N/2^|scratch|) work scratch`, inverse QFT) does not commute with
`X q`: `q` is the sign-extension bit of the `x = work` operand, and the angle satisfies
`0 < 2N · 2^|work| / 2^|scratch| < 2` because `|scratch| ≥ log2(N+1) + 3 + |work|`. NOT claimed:
non-commutation of Step 4 or the multiplier (Step 4 also contains the adjoint of this block), or
a change of any record probability. -/
theorem fastConstMulInto_not_commX_workSign {N : ℕ}
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (hN1 : 1 ≤ N) {q : ℕ}
    (hq : q ∈ (work.newBits 1).qubits) :
    ¬ CommX qs (fastConstMulInto N work scratch hs4.mulWorkspace) q := by
  have hqx : q ∈ (hs4.mulWorkspace.xExt.newBits 1).qubits := by
    rw [mulWorkspace_xExt_newBits]; exact hq
  have hqo : q ∈ work.ownedQubits := mem_owned_of_newBits hq
  have hqZ : q ∉ hs4.mulWorkspace.zExt.active.qubits := fun h =>
    hs4.work_scratch_disjoint hqo (mem_owned_of_active (e := scratch) h)
  have hsw := hs4.scratch_width
  have hlog := Nat.lt_log2_self (n := N + 1)
  have hmax := le_max_right (regSize (y.grow 1).active + regSize work.active)
    (Nat.log2 (N + 1) + 1 + regSize work.active)
  unfold cmpLtNWWidth at hsw
  have hz : 1 ≤ regSize scratch.active := by omega
  -- `N · 2^|work| < 2^|scratch|`
  have hlt : N * 2 ^ regSize work.active < 2 ^ regSize scratch.active := by
    calc N * 2 ^ regSize work.active < 2 ^ (Nat.log2 (N + 1) + 1) * 2 ^ regSize work.active :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = 2 ^ (Nat.log2 (N + 1) + 1 + regSize work.active) := by rw [← pow_add]
      _ ≤ 2 ^ regSize scratch.active := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : (ASize hs4.mulWorkspace.zExt.active : ℚ) = 2 ^ regSize scratch.active := by
    simp [ASize]; rfl
  have hltQ : (N : ℚ) * 2 ^ regSize work.active < 2 ^ regSize scratch.active := by
    exact_mod_cast hlt
  have hS : (0 : ℚ) < 2 ^ regSize scratch.active := by positivity
  have h0 : (0 : ℚ) < (2 * (N : ℚ)) / (ASize hs4.mulWorkspace.zExt.active : ℚ)
      * 2 ^ regSize work.active := by
    rw [hA]; have : (1 : ℚ) ≤ N := by exact_mod_cast hN1
    positivity
  have h2 : (2 * (N : ℚ)) / (ASize hs4.mulWorkspace.zExt.active : ℚ)
      * 2 ^ regSize work.active < 2 := by
    rw [hA, div_mul_eq_mul_div, div_lt_iff₀ hS]; nlinarith
  unfold fastConstMulInto
  refine not_commX_seq_left (commX_QFT hqZ) ?_
  exact not_commX_seq_right (commX_adj (commX_QFT hqZ))
    (phaseProdUsing_not_commX_xSign hs4.mulWorkspace _ hqx hz h0 h2)

/-- Wrapping `-(2^a)` to `s > a` bits sets the top bit `s - 1`. -/
theorem tcModWidth_neg_two_pow_testBit {a s : ℕ} (h : a < s) :
    (tcModWidth s (-(2 ^ a : ℤ))).testBit (s - 1) = true := by
  unfold tcModWidth
  have ha : 2 ^ a ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs : 2 ^ s = 2 * 2 ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
  have hpos : 0 < 2 ^ a := by positivity
  have hm : (-(2 ^ a : ℤ)) % ((2 ^ s : ℕ) : ℤ) = ((2 ^ s - 2 ^ a : ℕ) : ℤ) := by
    have hle : 2 ^ a ≤ 2 ^ s := by omega
    rw [show (-(2 ^ a : ℤ)) = ((2 ^ s - 2 ^ a : ℕ) : ℤ) + ((2 ^ s : ℕ) : ℤ) * (-1) by
      push_cast [Nat.cast_sub hle]; ring, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by positivity)
      (by exact_mod_cast (show 2 ^ s - 2 ^ a < 2 ^ s by omega))
  rw [hm, Int.toNat_natCast, Nat.testBit_eq_decide_div_mod_eq]
  rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
  rfl

/-- **`y.reserve[0]` is read by the WHOLE Step 3.** Same hypotheses as
`step3Cmp_not_commX_carry`. `step3 N (y.grow 1) scratch flag = CmpGeConst ;; CSubConst` does not
commute with `X q`: from the all-zero ket the flag ends at `0`, from the ket with only `q` set
(data `2^|y| ≥ N`) the flag ends at `1` (`CSubConst` changes only the data). NOT claimed:
non-commutation of the multiplier, or a change of any record probability. -/
theorem step3_not_commX_carry {N : ℕ} (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hN1 : 1 ≤ N) (hN2 : N ≤ 2 ^ regSize y.active) {q : ℕ} (hq : q ∈ (y.newBits 1).qubits) :
    ¬ CommX qs (step3 N (y.grow 1) scratch flag) q := by
  have hf : flag ∉ (y.grow 1).active.qubits := fun h =>
    hs4.flag_not_data (List.mem_append_left _ h)
  have hqf : flag ≠ q := fun h => hf (h ▸ mem_grow_active_of_newBits hq)
  have hqy : q ∉ y.active.qubits := not_mem_active_of_newBits hq
  have hsub : ∀ c : qs.Basis, RegEncoding.bit flag (csubConstBasis N (y.grow 1).active flag c)
      = RegEncoding.bit flag c := fun c => by
    unfold csubConstBasis
    split
    · rfl
    · exact RegEncoding.bit_writeNat_out _ _ _ _ hf
  refine not_commX_of_basis
    (fun b => csubConstBasis N (y.grow 1).active flag (cmpGeConstBasis N (y.grow 1).active flag b))
    (fun b => by
      simp only [step3, qs.eval_seq, ModularArithmeticSemantics.eval_CmpGeConst_ket,
        ModularArithmeticSemantics.eval_CSubConst_ket])
    RegEncoding.zero fun h => ?_
  have e := congrArg (RegEncoding.bit flag) h
  rw [hsub, bit_flipBit_ne hqf, hsub] at e
  have v1 : RegEncoding.toNat (y.grow 1).active (flipBit q (RegEncoding.zero : qs.Basis))
      = 2 ^ regSize y.active := by
    rw [toNat_grow_one hq, toNat_flipBit hqy, toNat_zero_basis, bit_flipBit_self,
      RegEncoding.bit_zero]; simp
  have v0 : RegEncoding.toNat (y.grow 1).active (RegEncoding.zero : qs.Basis) = 0 :=
    toNat_zero_basis _
  have hN0 : ¬ N ≤ 0 := by omega
  simp only [cmpGeConstBasis, hf, bit_flipBit_ne hqf, RegEncoding.bit_zero, v1, v0,
    Bool.false_eq_true, ite_false, hN2, hN0, ite_true] at e
  rw [bit_writeNat_qubitReg_self _ _ _ (by norm_num),
    bit_writeNat_qubitReg_self _ _ _ (by norm_num)] at e
  simp at e

/-- **`y.reserve[1]` is read by the WHOLE Step 4.** Under `hs4`, for the second reserve qubit `q`
of `y`, `step4 N (y.grow 1) work scratch flag hs4` (= `cmpLtNW`: multiplier, difference block,
`CNOT sign flag`, and the two adjoints) does not commute with `X q`. The multiplier blocks do not
involve `q` (they commute with `X q`); the inner sandwich `diff ;; CNOT ;; †diff` acts on kets by
"flip the flag iff the top scratch bit of `diff b` is set", and from the all-zero ket that bit
is `0`, while with only `q` set it is `1` (the difference block writes
`2^|scratch| − 2^(|work|+|y|+1)` into `scratch`). NOT claimed: non-commutation of the
multiplier, or a change of any record probability. -/
theorem step4_not_commX_ySign {N : ℕ} (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    {q : ℕ} (hq : q ∈ ((y.grow 1).newBits 1).qubits) :
    ¬ CommX qs (step4 N (y.grow 1) work scratch flag hs4) q := by
  have hd : ExtReg.OwnedDisjoint y scratch := ownedDisjoint_y_scratch hs4
  have hy1 : y.CanGrow 1 := ExtReg.CanGrow.mono (canGrow_two_of_mem_grow hq) (by norm_num)
  have hwidth : regSize y.active + 1 + regSize work.active < regSize scratch.active := by
    rw [hs4.scratch_width, cmpLtNWWidth, regSize_grow_active hy1]
    have := le_max_left (regSize y.active + 1 + regSize work.active)
      (Nat.log2 (N + 1) + 1 + regSize work.active)
    omega
  have hqo : q ∈ y.ownedQubits :=
    mem_owned_of_mem_grow_grow_active (mem_grow_active_of_newBits hq)
  have hqs : q ∉ scratch.active.qubits := fun h => hd hqo (mem_owned_of_active h)
  have hqS : q ∉ scratch.ownedQubits := fun h => hd hqo h
  have hqW : q ∉ work.ownedQubits := fun h => hs4.data_work_disjoint
    (by rw [Gate.ExtReg.ownedQubits_grow]; exact hqo) h
  have hqg : q ∉ (y.grow 1).active.qubits := not_mem_active_of_newBits hq
  have hfs : flag ∉ scratch.active.qubits := fun h => hs4.flag_not_scratch (mem_owned_of_active h)
  have hfsrc : flag ∉ ((y.grow 1).grow 1).active.qubits := fun h => hs4.flag_not_data
    (by rw [Gate.ExtReg.ownedQubits_grow]; exact mem_owned_of_mem_grow_grow_active h)
  have hAD : ExtReg.ActiveDisjoint scratch ((y.grow 1).grow 1) := by
    unfold ExtReg.ActiveDisjoint Disjoint
    rw [List.disjoint_left]
    intro p hpd hps
    exact hd (mem_owned_of_mem_grow_grow_active hps) (List.mem_append_left _ hpd)
  have hsrcS : ∀ p ∈ ((y.grow 1).grow 1).active.qubits, p ∉ scratch.active.qubits :=
    fun p hp hs => hAD hs hp
  -- the multiplier commutes with `X q`
  have hmul : CommX qs (fastConstMulInto N work scratch hs4.mulWorkspace) q := by
    have hQ : CommX qs (Gate.QFT hs4.mulWorkspace.zExt) q := commX_QFT hqs
    have hx : q ∉ (hs4.mulWorkspace.xExt.grow 1).active.qubits := fun h => by
      rcases mem_grow_one_active.mp h with h | h
      · exact hqW (mem_owned_of_active (e := work) h)
      · rw [mulWorkspace_xExt_newBits] at h; exact hqW (mem_owned_of_newBits h)
    have hz : q ∉ (hs4.mulWorkspace.zExt.grow 1).active.qubits := fun h => by
      rcases mem_grow_one_active.mp h with h | h
      · exact hqs h
      · rw [mulWorkspace_zExt_newBits] at h; exact hqS (mem_owned_of_newBits h)
    have hP : CommX qs (Gate.PhaseProdUsing ((2 * (N : ℚ)) /
        (ASize hs4.mulWorkspace.zExt.active : ℚ)) work.active scratch.active hs4.mulWorkspace) q := by
      unfold Gate.PhaseProdUsing
      refine commX_seq (gate_commX_exact (Gate.zeroExtend _ _) trivial (by simp [Gate.exactSupport]))
        (commX_seq (gate_commX_exact (Gate.zeroExtend _ _) trivial (by simp [Gate.exactSupport]))
        (commX_seq (gate_commX_exact (Gate.SignedPhaseProd _ _ _) trivial ?_)
        (commX_seq (gate_commX_exact (Gate.zeroDealloc _ _) trivial (by simp [Gate.exactSupport]))
          (gate_commX_exact (Gate.zeroDealloc _ _) trivial (by simp [Gate.exactSupport])))))
      simp only [Gate.exactSupport, Set.mem_ofPred_eq, not_or]
      exact ⟨hx, hz⟩
    exact commX_seq hQ (commX_seq hP (commX_adj hQ))
  -- the difference block as a basis map
  set src := (y.grow 1).grow 1 with hsrc
  set sh := regSize work.active with hsh
  let d : qs.Basis → qs.Basis := fun b => addScaledBasis scratch src false sh (negateBasis scratch b)
  have hD : ∀ b, qs.eval (cmpLtNWDifference (y.grow 1) work scratch hs4.data_can_grow) (qs.ket b)
      = qs.ket (d b) := fun b => by
    simp only [cmpLtNWDifference, qs.eval_seq, ExtensionSemantics.eval_zeroExtend,
      ExtensionSemantics.eval_zeroDealloc, ArithmeticSemantics.eval_Negate_ket_total,
      ArithmeticSemantics.eval_AddScaled_ket_total, d]
    rfl
  have hdflip : ∀ b, d (flipBit flag b) = flipBit flag (d b) := fun b => by
    simp only [d, negateBasis_flipBit hfs, addScaledBasis_flipBit hfs hfsrc]
  have hpos : 0 < regSize scratch.active := by omega
  set sg := cmpLtNWSignQubit scratch (hs4.scratch_width ▸ Nat.lt_of_lt_of_le two_pos
    (Nat.le_add_right 2 _)) with hsg
  have hsgS : sg ∈ scratch.active.qubits := List.get_mem _ _
  have hsgf : sg ≠ flag := fun h => hfs (h ▸ hsgS)
  have hbitsg : ∀ c : qs.Basis, RegEncoding.bit sg c
      = (RegEncoding.toNat scratch.active c).testBit (regSize scratch.active - 1) := fun c =>
    RegEncoding.bit_eq_testBit_toNat scratch.active c ⟨regSize scratch.active - 1, by omega⟩
  -- the sandwich `diff ;; CNOT ;; †diff`
  let g : qs.Basis → qs.Basis := fun b => if RegEncoding.bit sg (d b) then flipBit flag b else b
  have hR : ∀ b, qs.eval (cmpLtNWDifference (y.grow 1) work scratch hs4.data_can_grow ;;
      (Gate.CNOT sg flag ;; †(cmpLtNWDifference (y.grow 1) work scratch hs4.data_can_grow)))
      (qs.ket b) = qs.ket (g b) := fun b => by
    simp only [qs.eval_seq, hD, ClassicalReversibleSemantics.eval_CNOT_ket, cnotBasis, hsgf,
      ite_false, g]
    split
    · rw [show RegEncoding.writeNat (qubitReg flag)
          (if RegEncoding.bit flag (d b) then 0 else 1) (d b) = flipBit flag (d b) from rfl,
        ← hdflip, ← hD]
      exact GateSemanticsCore.eval_adj_apply _ _
    · rw [← hD]
      exact GateSemanticsCore.eval_adj_apply _ _
  -- values of the top scratch bit
  have hsrcz : ∀ c : qs.Basis, extToInt src (negateBasis scratch c) = extToInt src c := fun c => by
    simp only [negateBasis, extToInt, ExtReg.toNat, toNat_writeNat_disjoint hsrcS]
  have hneg0 : ∀ c : qs.Basis, extToInt scratch c = 0 →
      extToInt scratch (negateBasis scratch c) = 0 := fun c hc => by
    have h0 : tcModWidth scratch.width (-extToInt scratch c) = 0 := by
      rw [hc]; simp [tcModWidth]
    show tcDecodeWidth scratch.width (RegEncoding.toNat scratch.active (RegEncoding.writeNat
      scratch.active (tcModWidth scratch.width (-extToInt scratch c)) c)) = 0
    rw [h0, RegEncoding.toNat_writeNat_of_lt _ _ _ (by unfold ASize; positivity),
      tcDecodeWidth_zero_right]
  have hlt : ∀ z : ℤ, tcModWidth scratch.width z < ASize scratch.active := fun z => by
    simpa [ASize, ExtReg.width] using tcModWidth_lt_two_pow scratch.width z
  have hval : ∀ c : qs.Basis, extToInt scratch c = 0 →
      RegEncoding.toNat scratch.active (d c)
        = tcModWidth scratch.width (2 ^ sh * extToInt src c) := fun c hc => by
    simp only [d, addScaledBasis, hAD, dite_true, RegEncoding.toNat_writeNat_of_lt _ _ _ (hlt _),
      hneg0 c hc, hsrcz]
    congr 1; simp
  have hs0 : extToInt scratch (RegEncoding.zero : qs.Basis) = 0 := extToInt_zero_basis _
  have hs1 : extToInt scratch (flipBit q (RegEncoding.zero : qs.Basis)) = 0 := by
    rw [extToInt_flipBit hqs, hs0]
  have hsrc0 : extToInt src (RegEncoding.zero : qs.Basis) = 0 := extToInt_zero_basis _
  have hsrc1 : extToInt src (flipBit q (RegEncoding.zero : qs.Basis))
      = -(2 ^ (regSize y.active + 1) : ℤ) := by
    rw [hsrc, extToInt_grow_one hq, toNat_flipBit hqg, toNat_zero_basis, bit_flipBit_self,
      RegEncoding.bit_zero, regSize_grow_active hy1]
    simp
  have hg0 : g RegEncoding.zero = RegEncoding.zero := by
    simp only [g, hbitsg, hval _ hs0, hsrc0, mul_zero]
    simp [tcModWidth]
  have hg1 : g (flipBit q RegEncoding.zero) = flipBit flag (flipBit q RegEncoding.zero) := by
    have key : (2 : ℤ) ^ sh * -(2 ^ (regSize y.active + 1) : ℤ)
        = -(2 ^ (sh + (regSize y.active + 1)) : ℤ) := by ring
    have ht := tcModWidth_neg_two_pow_testBit (a := sh + (regSize y.active + 1))
      (s := regSize scratch.active) (by omega)
    simp only [g, hbitsg, hval _ hs1, hsrc1, key]
    rw [show scratch.width = regSize scratch.active from rfl, ht]
    rfl
  have hRn : ¬ CommX qs (cmpLtNWDifference (y.grow 1) work scratch hs4.data_can_grow ;;
      (Gate.CNOT sg flag ;; †(cmpLtNWDifference (y.grow 1) work scratch hs4.data_can_grow))) q := by
    refine not_commX_of_basis g hR RegEncoding.zero ?_
    rw [hg1, hg0]
    intro h
    have e := congrArg (RegEncoding.bit flag) h
    rw [bit_flipBit_self] at e
    simp at e
  -- assemble: `step4 = mul ;; (R' ;; †mul)` with `R'` equal in action to the sandwich
  have hR' : ¬ CommX qs (cmpLtNWDifference (y.grow 1) work scratch hs4.data_can_grow ;;
      (Gate.CNOT sg flag ;; (†(cmpLtNWDifference (y.grow 1) work scratch hs4.data_can_grow) ;;
        †(fastConstMulInto N work scratch hs4.mulWorkspace)))) q := by
    intro h
    apply not_commX_seq_right (commX_adj hmul) hRn
    intro ψ
    have e := h ψ
    simp only [qs.eval_seq] at e ⊢
    exact e
  exact not_commX_seq_left hmul hR'

/-- **Named sub-gate reads: both data reserve qubits the circuit grows into.** Under
`hs4` and `1 ≤ N ≤ 2^|y.active|`: every qubit `q` of `y.newBits 2` is read either by Step 3's
comparator (`q` the first reserve qubit) or by Step 4's difference block (`q` the second). NOT
claimed: anything about the whole multiplier or about record probabilities. -/
theorem yReserve_read {N : ℕ} (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hN1 : 1 ≤ N) (hN2 : N ≤ 2 ^ regSize y.active) {q : ℕ} (hq : q ∈ (y.newBits 2).qubits) :
    ¬ CommX qs (Gate.CmpGeConst N (y.grow 1) scratch flag) q ∨
      ¬ CommX qs (cmpLtNWDifference (y.grow 1) work scratch hs4.data_can_grow) q := by
  rcases mem_take_one_or_tail_of_take_two hq with h | h
  · exact Or.inl (step3Cmp_not_commX_carry hs4 hN1 hN2 h)
  · refine Or.inr (cmpLtNWDifference_not_commX_ySign hs4 ?_)
    simpa [ExtReg.newBits, ExtReg.grow, ExtReg.remainingReserve, Reg.take, Reg.drop,
      List.drop_one] using h

end SubGates

/-! ## The over-count: the scratch sign qubit commutes with every node -/

section Refined
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [MeasureClass qs]
variable {c flag : ℕ} {y work scratch : ExtReg}

omit [MeasureClass qs] in
/-- **Step 4's phase product commutes with `X` on the scratch sign bit.** For any `N`, with
`hs4`, and `q` the first reserve qubit of `scratch`: `PhaseProdUsing (2N/2^|scratch|) work
scratch` (the phase product of `fastConstMulInto`) commutes with `X q` on every state. -/
theorem fastConstMulPhase_commX_scratchSign {N : ℕ}
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) {q : ℕ}
    (hq : q ∈ (scratch.newBits 1).qubits) :
    CommX qs (Gate.PhaseProdUsing ((2 * (N : ℚ)) / (ASize hs4.mulWorkspace.zExt.active : ℚ))
      work.active scratch.active hs4.mulWorkspace) q := by
  have hqz : q ∈ (hs4.mulWorkspace.zExt.newBits 1).qubits := by
    rw [mulWorkspace_zExt_newBits]; exact hq
  have hqo : q ∈ scratch.ownedQubits := mem_owned_of_newBits hq
  have hx : q ∉ (hs4.mulWorkspace.xExt.grow 1).active.qubits := fun h => by
    rcases mem_grow_one_active.mp h with h | h
    · exact hs4.work_scratch_disjoint (mem_owned_of_active (e := work) h) hqo
    · rw [mulWorkspace_xExt_newBits] at h
      exact hs4.work_scratch_disjoint (mem_owned_of_newBits h) hqo
  have hphi : (2 * (N : ℚ)) / (ASize hs4.mulWorkspace.zExt.active : ℚ)
      * 2 ^ regSize hs4.mulWorkspace.zExt.active = 2 * ((N : ℤ) : ℚ) := by
    have : (ASize hs4.mulWorkspace.zExt.active : ℚ) = 2 ^ regSize hs4.mulWorkspace.zExt.active := by
      simp [ASize]
    rw [this]; field_simp; push_cast; ring
  have hS := signedPhaseProd_grow_commX_top (qs := qs) hqz hx (N : ℤ) hphi
  have hz0 : ∀ (r : ExtReg) (n : ℕ), CommX qs (Gate.zeroExtend r n) q := fun r n =>
    gate_commX_exact (Gate.zeroExtend r n) trivial (by simp [Gate.exactSupport])
  have hz1 : ∀ (r : ExtReg) (n : ℕ), CommX qs (Gate.zeroDealloc r n) q := fun r n =>
    gate_commX_exact (Gate.zeroDealloc r n) trivial (by simp [Gate.exactSupport])
  unfold Gate.PhaseProdUsing
  exact commX_seq (hz0 _ _) (commX_seq (hz0 _ _) (commX_seq hS (commX_seq (hz1 _ _) (hz1 _ _))))

set_option linter.unusedSimpArgs false in
/-- **Every node of the multiplier is local outside the refined set.** For any constant `cm`,
any `N`, the circuit's workspace hypotheses `hw`, `hs4`, and any `q` outside
`semiclassicalExactQubitsRefined c y work scratch flag`: `CmodMulInPlaceCore cm N c …` commutes
with `X q` and with the Z projectors of `q` on every state. Informal remark on the proof: it
rests on two facts read off the circuit definitions, (i) the QFT blocks of Step 4 act only on
`hs4.mulWorkspace.zExt.active` (= `scratch.active`), and (ii) no node other than Step 4's
`PhaseProdUsing` has `scratch.newBits 1` in its exact support; at that node
`fastConstMulPhase_commX_scratchSign` is used. -/
theorem cmodMul_gateLocal_refined (cm N : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) {q : ℕ}
    (hq : q ∉ semiclassicalExactQubitsRefined c y work scratch flag) :
    GateLocal qs (CmodMulInPlaceCore cm N c y work scratch flag hw hs4) q := by
  have hzR : hs4.mulWorkspace.zReserve = scratch.reserve := hs4.mul_zReserve_eq
  have hxR : hs4.mulWorkspace.xReserve = work.reserve := hs4.mul_xReserve_eq
  obtain ⟨n1, n2, n3, n4, n5⟩ := cmodMul_noIdeal (cm := cm) (c := c) hw hs4
  simp only [semiclassicalExactQubitsRefined, Set.mem_ofPred_eq, not_or] at hq
  obtain ⟨nc, nYa, nY2', nWa, nW1', nSa, nf⟩ := hq
  have nY2 : q ∉ List.take 2 y.reserve.qubits := nY2'
  have nW1 : q ∉ List.take 1 work.reserve.qubits := nW1'
  have nY1 : q ∉ List.take 1 y.reserve.qubits := fun h => nY2 (mem_take_two_of_take_one h)
  have nY11 : q ∉ List.take 1 (List.drop 1 y.reserve.qubits) := fun h =>
    nY2 (mem_take_two_of_take_one_drop_one h)
  have nH : q ∉ (H_reg work.active).exactSupport := fun h => nWa (H_reg_exactSupport _ h)
  have nSg : ∀ h, q ≠ cmpLtNWSignQubit scratch h := fun h e => nSa (e ▸ List.get_mem _ _)
  have s1 : q ∉ (step1 cm N c y work hw).exactSupport := by
    intro hmem
    simp only [step1, IQFT, Gate.CPhaseProdUsing, Gate.exactSupport,
      Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_insert_iff,
      Set.mem_empty_iff_false, false_or, or_false] at hmem
    simp only [ModMulCircuitWorkspaceOK.step1Workspace, Gate.PhaseProdWorkspace.xExt,
      Gate.PhaseProdWorkspace.zExt, Gate.PhaseProdWorkspace.ofExtRegs,
      ExtReg.newBits, ExtReg.grow, ExtReg.remainingReserve,
      Reg.take, Reg.drop, Reg.append, ExtReg.withReserve_active, ExtReg.withReserve_reserve,
      List.mem_append] at hmem
    simp [nc, nYa, nY1, nWa, nW1, nSa, nf, nH] at hmem
    exact nY11 (by simpa using hmem)
  have s2 : q ∉ (step2 N y work hw).exactSupport := by
    intro hmem
    simp only [step2, IQFT, Gate.PhaseProdUsing, Gate.exactSupport,
      Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_insert_iff,
      Set.mem_empty_iff_false, false_or, or_false] at hmem
    simp only [ModMulCircuitWorkspaceOK.step1Workspace, ModMulCircuitWorkspaceOK.step2Workspace,
      ModMulCircuitWorkspaceOK.step5Workspace, Gate.PhaseProdWorkspace.xExt,
      Gate.PhaseProdWorkspace.zExt, Gate.PhaseProdWorkspace.ofExtRegs,
      ExtReg.newBits, ExtReg.grow, ExtReg.remainingReserve,
      Reg.take, Reg.drop, Reg.append, ExtReg.withReserve_active, ExtReg.withReserve_reserve,
      List.mem_append] at hmem
    simp [nc, nYa, nY1, nWa, nW1, nSa, nf, nH] at hmem
    try exact nY11 (by simpa using hmem)
  have s3 : q ∉ (step3 N (y.grow 1) scratch flag).exactSupport := by
    intro hmem
    simp only [step3, Gate.exactSupport,
      Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_insert_iff,
      Set.mem_empty_iff_false, false_or, or_false] at hmem
    simp only [ModMulCircuitWorkspaceOK.step1Workspace, ModMulCircuitWorkspaceOK.step2Workspace,
      ModMulCircuitWorkspaceOK.step5Workspace, Gate.PhaseProdWorkspace.xExt,
      Gate.PhaseProdWorkspace.zExt, Gate.PhaseProdWorkspace.ofExtRegs,
      ExtReg.newBits, ExtReg.grow, ExtReg.remainingReserve,
      Reg.take, Reg.drop, Reg.append, ExtReg.withReserve_active, ExtReg.withReserve_reserve,
      List.mem_append] at hmem
    simp [nc, nYa, nY1, nWa, nW1, nSa, nf, nH] at hmem
  have s5 : q ∉ (step5 (step5Constant cm N) N c y work hw).exactSupport := by
    intro hmem
    simp only [step5, IQFT, Gate.CPhaseProdUsing, Gate.exactSupport,
      Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_insert_iff,
      Set.mem_empty_iff_false, false_or, or_false] at hmem
    simp only [ModMulCircuitWorkspaceOK.step1Workspace, ModMulCircuitWorkspaceOK.step2Workspace,
      ModMulCircuitWorkspaceOK.step5Workspace, Gate.PhaseProdWorkspace.xExt,
      Gate.PhaseProdWorkspace.zExt, Gate.PhaseProdWorkspace.ofExtRegs,
      ExtReg.newBits, ExtReg.grow, ExtReg.remainingReserve,
      Reg.take, Reg.drop, Reg.append, ExtReg.withReserve_active, ExtReg.withReserve_reserve,
      List.mem_append] at hmem
    simp [nc, nYa, nY1, nWa, nW1, nSa, nf, nH] at hmem
    try exact nY11 (by simpa using hmem)
  -- Step 4: every node is local; the phase product via the over-count lemma
  have hPP : GateLocal qs (Gate.PhaseProdUsing ((2 * (N : ℚ)) /
      (ASize hs4.mulWorkspace.zExt.active : ℚ)) work.active scratch.active hs4.mulWorkspace) q := by
    by_cases hs : q ∈ (scratch.newBits 1).qubits
    · exact gateLocal_of_diag _ (eval_PhaseProdUsing_ket_total _ _)
        (fastConstMulPhase_commX_scratchSign hs4 hs)
    · refine gateLocal_of_exact (by trivial) ?_
      simp only [Gate.PhaseProdUsing, Gate.exactSupport, Set.mem_union, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, false_or, or_false, not_or]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases mem_grow_one_active.mp h with h | h
        · exact nWa h
        · rw [mulWorkspace_xExt_newBits] at h; exact nW1' h
      · rcases mem_grow_one_active.mp h with h | h
        · exact nSa h
        · rw [mulWorkspace_zExt_newBits] at h; exact hs h
  have hQ : GateLocal qs (Gate.QFT hs4.mulWorkspace.zExt) q :=
    gateLocal_of_exact (by trivial) (fun h => nSa h)
  have hmul : GateLocal qs (fastConstMulInto N work scratch hs4.mulWorkspace) q :=
    hQ.seq (hPP.seq hQ.adj)
  have hdiff : GateLocal qs (cmpLtNWDifference (y.grow 1) work scratch hs4.data_can_grow) q := by
    refine gateLocal_of_exact (by simp [cmpLtNWDifference, Gate.NoIdeal]) ?_
    simp only [cmpLtNWDifference, Gate.exactSupport, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, false_or, or_false, not_or]
    refine ⟨nSa, nSa, fun h => ?_⟩
    rcases mem_grow_grow_active h with h | h
    · exact nYa h
    · exact nY2' h
  have hcnot : ∀ hpos, GateLocal qs (Gate.CNOT (cmpLtNWSignQubit scratch hpos) flag) q :=
    fun hpos => gateLocal_of_exact (by trivial) (by
      simp only [Gate.exactSupport, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨nSg hpos, nf⟩)
  have l4 : GateLocal qs (step4 N (y.grow 1) work scratch flag hs4) q :=
    hmul.seq (hdiff.seq ((hcnot _).seq (hdiff.adj.seq hmul.adj)))
  exact (gateLocal_of_exact n1 s1).seq ((gateLocal_of_exact n2 s2).seq
    ((gateLocal_of_exact n3 s3).seq (l4.seq (gateLocal_of_exact n5 s5))))

variable [LowerGateClass qs]

omit [LowerGateClass qs] in
/-- **Every node of the real circuit is local outside the refined set** (any `a N m`, the
circuit's own `hw`, `hs4`). -/
theorem orderFindingSemiclassical_localAt_refined (a N m : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) {q : ℕ}
    (hq : q ∉ semiclassicalExactQubitsRefined c y work scratch flag) :
    (orderFindingSemiclassical a N c m y work scratch flag hw hs4).LocalAt qs q := by
  have hc : q ≠ c := fun h => hq (Or.inl h)
  have hH : GateLocal qs (Gate.H c) q := gateLocal_of_exact (by trivial) (by
    simpa [Gate.exactSupport] using hc)
  have hrounds : ∀ k, (readoutRounds (semiclassicalMultipliers a N c m y work scratch flag hw hs4)
      c k).LocalAt qs q := by
    intro k
    induction k with
    | zero => exact gateLocal_of_exact (by trivial) (by simp [Gate.exactSupport])
    | succ k ih =>
      exact ⟨ih, hH, cmodMul_gateLocal_refined _ N hw hs4 hq, hc, hH, hc⟩
  refine ⟨gateLocal_of_exact ?_ fun h => hq (Or.inr (Or.inl (initY1_exactSupport _ h))), hrounds m⟩
  unfold initY1; split <;> trivial

/-- **Real circuit, finitely many flips outside the refined set.** For ANY registers with the
circuit's `hw`, `hs4`, ANY start ket `b0`, and any list `l` of qubits outside
`semiclassicalExactQubitsRefined`: every record has the same probability from `|flipBits l b0⟩` as
from `|b0⟩`. -/
theorem orderFindingSemiclassical_recordProb_flipBits_refined (a N m : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work) (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (b0 : qs.Basis) (l : List ℕ)
    (hl : ∀ q ∈ l, q ∉ semiclassicalExactQubitsRefined c y work scratch flag) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket (flipBits l b0)))) r
      = recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0))) r :=
  MGate.recordProb_flipBits_on _ l (fun q hq => MGate.spectatorOn_of_localAt _
      (orderFindingSemiclassical_localAt_refined a N m hw hs4 (hl q hq)))
    (fun _ _ _ _ => Submodule.mem_top) b0 Submodule.mem_top r

/-- **Real circuit, agreement form on the refined set.** Two start kets that agree on
`semiclassicalExactQubitsRefined` and differ at finitely many qubits give every record the same
probability. -/
theorem orderFindingSemiclassical_recordProb_of_agree_refined (a N m : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work) (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (b0 b0' : qs.Basis)
    (hagree : ∀ p ∈ semiclassicalExactQubitsRefined c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (hfin : {p | RegEncoding.bit p b0' ≠ RegEncoding.bit p b0}.Finite) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0'))) r
      = recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0))) r :=
  MGate.recordProb_of_agree_on _ b0 b0' Submodule.mem_top
    (fun q hq => MGate.spectatorOn_of_localAt _
      (orderFindingSemiclassical_localAt_refined a N m hw hs4 (fun h => hq (hagree q h))))
    (fun _ _ _ _ => Submodule.mem_top) hfin r

/-- **Real circuit, one qubit outside the refined set in superposition** (any basis state `b0`,
any `α β`). -/
theorem orderFindingSemiclassical_recordProb_superpose_refined (a N m : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work) (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (b0 : qs.Basis) {q : ℕ} (hq : q ∉ semiclassicalExactQubitsRefined c y work scratch flag)
    (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassical a N c m y work scratch flag
        hw hs4).eval (MState.init (qs.ket b0))) r :=
  (MGate.spectatorOn_of_localAt _ (orderFindingSemiclassical_localAt_refined a N m hw hs4 hq)).recordProb_superpose
    Submodule.mem_top Submodule.mem_top α β r

/-- **Real circuit, decomposition along a qubit outside the refined set** (any start state). -/
theorem orderFindingSemiclassical_recordProb_decomp_refined (a N m : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work) (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    {q : ℕ} (hq : q ∉ semiclassicalExactQubitsRefined c y work scratch flag) (ψ₀ : qs.State)
    (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((orderFindingSemiclassical a N c m y work scratch flag
          hw hs4).eval (MState.init (measProj (qubitReg q) o ψ₀))) r :=
  (MGate.spectatorOn_of_localAt _ (orderFindingSemiclassical_localAt_refined a N m hw hs4 hq)).recordProb_decomp
    Submodule.mem_top r

/-- **Real circuit: flipping the scratch sign qubit changes no record probability.** Under the
circuit's `hw`, `hs4` and `SemiclassicalLayout` (used only for: the control is off `scratch`),
for ANY start ket `b0` and the first reserve qubit `q` of `scratch` (which IS in
`semiclassicalExactQubits`): every record has the same probability from `|flipBit q b0⟩` as from
`|b0⟩`. High-level circuit only; the lowered circuit uses `q` as its comparator unit qubit. -/
theorem orderFindingSemiclassical_recordProb_flip_scratchSign (a N m : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work) (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hl : SemiclassicalLayout c y work scratch flag) (b0 : qs.Basis) {q : ℕ}
    (hq : q ∈ (scratch.newBits 1).qubits) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket (flipBit q b0)))) r
      = recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0))) r :=
  (MGate.spectatorOn_of_localAt _ (orderFindingSemiclassical_localAt_refined a N m hw hs4
    (scratchSign_mem_exact_not_mem_refined N hs4 hl.c_not_mem_scratch hq).2)).recordProb_flipBit
    Submodule.mem_top r

end Refined

/-- **The dropped qubit is the lowered comparator's unit qubit.** For any `scratch` with a
reserve qubit, `constArithmeticUnitQubit scratch h` (the unit qubit of the Step-3 lowering
`lowerCmpGeConst` / `lowerCSubConst`) is the first reserve qubit of `scratch`. -/
theorem constArithmeticUnitQubit_mem_newBits (scratch : ExtReg) (h : scratch.CanGrow 1) :
    constArithmeticUnitQubit scratch h ∈ (scratch.newBits 1).qubits := by
  unfold constArithmeticUnitQubit
  exact List.get_mem _ _

end Readout
end Shor

-- Axioms of every new theorem (expected: propext, Classical.choice, Quot.sound).
#print axioms Shor.Readout.not_commX_of_diag
#print axioms Shor.Readout.not_commX_of_basis
#print axioms Shor.Readout.not_commXL_of_diag
#print axioms Shor.Readout.not_commXL_of_basis
#print axioms Shor.Readout.not_commX_seq_left
#print axioms Shor.Readout.not_commX_seq_right
#print axioms Shor.Readout.toNat_grow_one
#print axioms Shor.Readout.extToInt_grow_one
#print axioms Shor.Readout.cmpGeConst_grow_not_commX
#print axioms Shor.Readout.addScaled_growgrow_not_commX
#print axioms Shor.Readout.eval_PhaseProdUsing_ket_total
#print axioms Shor.Readout.phaseProdUsing_not_commX_xSign
#print axioms Shor.Readout.signedPhaseProd_grow_commX_top
#print axioms Shor.Readout.MGate.spectatorOn_of_localAt
#print axioms Shor.Readout.toyPhaseKick_recordProb
#print axioms Shor.Readout.semiclassicalExactQubitsRefined_subset
#print axioms Shor.Readout.scratchSign_mem_exact_not_mem_refined
#print axioms Shor.Readout.step3Cmp_not_commX_carry
#print axioms Shor.Readout.cmpLtNWDifference_not_commX_ySign
#print axioms Shor.Readout.fastConstMulInto_not_commX_workSign
#print axioms Shor.Readout.yReserve_read
#print axioms Shor.Readout.tcModWidth_neg_two_pow_testBit
#print axioms Shor.Readout.step3_not_commX_carry
#print axioms Shor.Readout.step4_not_commX_ySign
#print axioms Shor.Readout.fastConstMulPhase_commX_scratchSign
#print axioms Shor.Readout.cmodMul_gateLocal_refined
#print axioms Shor.Readout.orderFindingSemiclassical_localAt_refined
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_flipBits_refined
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_of_agree_refined
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_superpose_refined
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_decomp_refined
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_flip_scratchSign
#print axioms Shor.Readout.constArithmeticUnitQubit_mem_newBits
