import ForShor.ShorVerification.Implementation.Readout.LocalityReserve
import ForShor.ShorVerification.Implementation.Readout.Proofs.LowLocality

/-!
# Readout: generic lemmas for showing a qubit in the exact support is read

`Proofs/LocalityExact.lean` gives an UPPER bound (`Gate.exactSupport`) on the qubits a program
acts on; `Readout/LocalityReserve.lean` shows that the first reserve qubits of `y`, `work`,
`scratch` are IN that bound (membership only). This file supplies the generic tools to show a
qubit is GENUINELY read, i.e. that a gate does NOT commute with `X q`:

* `not_commX_of_diag`, `not_commX_of_basis` (and the low-level `not_commXL_of_diag`,
  `not_commXL_of_basis`): a diagonal gate whose scalar changes when bit `q` of ONE basis state is
  flipped, or a basis-permutation gate whose map does not commute with `flipBit q` at ONE basis
  state, does not commute with `X q`.
* `not_commX_seq_left`, `not_commX_seq_right`: composing with a gate that DOES commute with
  `X q` keeps non-commutation (every gate is invertible).
* Register arithmetic for growing by one reserve qubit (`toNat_grow_one`, `extToInt_grow_one`).
* Gate-level non-commutation for the three gate shapes that read the reserve qubits in the
  real multiplier: `cmpGeConst_grow_not_commX` (the carry bit of `y.grow 1`),
  `addScaled_growgrow_not_commX` (the second reserve bit of `y`, the sign bit of
  `(y.grow 1).grow 1`), `phaseProdUsing_not_commX_xSign` (the sign-extension bit of the `x`
  operand of a `PhaseProdUsing`).
* The positive counterpart `signedPhaseProd_grow_commX_top`: a `SignedPhaseProd φ x (e.grow 1)`
  whose angle satisfies `φ · 2^|e| ∈ 2ℤ` COMMUTES with `X` on the sign-extension bit of `z`
  (the phase changes by a multiple of `2π`).
* `GateLocal`, `MGate.LocalAt`, `MGate.spectatorOn_of_localAt`: a spectator criterion for
  `MGate` programs that is finer than "outside the exact support": every unitary node commutes
  with `X q` and the Z projectors of `q`, and `q` is not a measured / phased qubit.
* `toyPhaseKick_recordProb` (toy section): a STAND-IN, not the real circuit: a 4-qubit program
  `H z ; PhaseProdUsing (1/2) x z ; H z ; measureReset z` with one-qubit operands and angle
  `1/2`, chosen so that the phase becomes a `Z` between the two `H`s. It shares only the
  `PhaseProdUsing` macro with the real circuit (not its angles, widths or structure).

NOT claimed here: anything about record probabilities of the real order-finding circuit under a
flip of one of these qubits (open; see `Readout/LocalityTight.lean`). Statements here are upper
bound / non-commutation facts plus one proved over-count, not lower bounds on the support.
-/

namespace Shor
namespace Readout

open MeasureClass

/-! ## Basis and register lemmas -/

section Basis
variable {B : Type*} [RegEncoding B]

/-- Two registers with the same qubit list are equal. -/
theorem reg_eq_of_qubits {r s : Reg} (h : r.qubits = s.qubits) : r = s := by
  cases r; cases s; simp_all

/-- A qubit in the first reserve slot is the whole one-qubit slot. -/
theorem newBits_one_eq_qubitReg {e : ExtReg} {q : ℕ} (hq : q ∈ (e.newBits 1).qubits) :
    e.newBits 1 = qubitReg q := by
  apply reg_eq_of_qubits
  simp only [ExtReg.newBits, Reg.take, qubitReg, Reg.singleton] at hq ⊢
  rcases h : e.reserve.qubits with _ | ⟨a, t⟩
  · simp [h] at hq
  · simp [h] at hq ⊢; exact hq.symm

theorem canGrow_one_of_mem {e : ExtReg} {q : ℕ} (hq : q ∈ (e.newBits 1).qubits) : e.CanGrow 1 := by
  simp only [ExtReg.newBits, Reg.take, ExtReg.CanGrow, ExtReg.capacity, regSize, Reg.width] at hq ⊢
  rcases h : e.reserve.qubits with _ | ⟨a, t⟩
  · simp [h] at hq
  · simp

theorem not_mem_active_of_newBits {e : ExtReg} {n q : ℕ} (hq : q ∈ (e.newBits n).qubits) :
    q ∉ e.active.qubits := fun ha =>
  e.active_reserve_disjoint ha (List.mem_of_mem_take hq)

theorem mem_grow_active_of_newBits {e : ExtReg} {n q : ℕ} (hq : q ∈ (e.newBits n).qubits) :
    q ∈ (e.grow n).active.qubits := by
  simp only [ExtReg.grow, Reg.append, List.mem_append]; exact Or.inr hq

theorem mem_grow_active_of_active {e : ExtReg} {n q : ℕ} (hq : q ∈ e.active.qubits) :
    q ∈ (e.grow n).active.qubits := by
  simp only [ExtReg.grow, Reg.append, List.mem_append]; exact Or.inl hq

/-- Every register reads `0` on the all-zero basis state. -/
theorem toNat_zero_basis (r : Reg) : RegEncoding.toNat r (RegEncoding.zero : B) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  by_cases hi : i < regSize r
  · rw [← RegEncoding.bit_eq_testBit_toNat r _ ⟨i, hi⟩, RegEncoding.bit_zero]
  · push Not at hi
    have l1 := RegEncoding.toNat_lt_ASize r (RegEncoding.zero : B)
    rw [ASize] at l1
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le l1 (Nat.pow_le_pow_right (by norm_num) hi))

/-- Reading the one-qubit register `qubitReg q` gives the bit `q` (any encoding). -/
theorem toNat_qubitReg_toNat (q : ℕ) (b : B) :
    RegEncoding.toNat (qubitReg q) b = (RegEncoding.bit q b).toNat := by
  have hlt := RegEncoding.toNat_lt_ASize (qubitReg q) b
  have hbit := RegEncoding.bit_eq_testBit_toNat (qubitReg q) b ⟨0, by simp [qubitReg, Reg.singleton, regSize, Reg.width]⟩
  change RegEncoding.bit q b = _ at hbit
  change _ < 2 at hlt
  rw [hbit]
  interval_cases RegEncoding.toNat (qubitReg q) b <;> simp

/-- **Growing by one reserve qubit `q`:** the grown register reads `value + 2^|e| · bit q`. -/
theorem toNat_grow_one {e : ExtReg} {q : ℕ} (hq : q ∈ (e.newBits 1).qubits) (b : B) :
    RegEncoding.toNat (e.grow 1).active b
      = RegEncoding.toNat e.active b + 2 ^ regSize e.active * (RegEncoding.bit q b).toNat := by
  have hd : Disjoint e.active (e.newBits 1) := by
    have hdisj := e.active_reserve_disjoint
    rw [Disjoint, List.disjoint_left] at hdisj ⊢
    exact fun _ hA hN => hdisj hA (List.mem_of_mem_take hN)
  have h := RegEncoding.toNat_append e.active (e.newBits 1) hd b
  rw [show (e.grow 1).active = Reg.append e.active (e.newBits 1) hd from rfl, h, newBits_one_eq_qubitReg hq,
    toNat_qubitReg_toNat, ASize]

/-- **Signed reading after growing by one reserve qubit `q`:** `q` is the sign bit, of weight
`-2^|e|`. -/
theorem extToInt_grow_one {e : ExtReg} {q : ℕ} (hq : q ∈ (e.newBits 1).qubits) (b : B) :
    extToInt (e.grow 1) b
      = (RegEncoding.toNat e.active b : ℤ) - 2 ^ regSize e.active * (RegEncoding.bit q b).toNat := by
  have hw : (e.grow 1).width = regSize e.active + 1 := by
    rw [ExtReg.width_grow _ _ (canGrow_one_of_mem hq)]; rfl
  have hlt := RegEncoding.toNat_lt_ASize e.active b
  rw [ASize] at hlt
  unfold extToInt ExtReg.toNat
  rw [hw, toNat_grow_one hq, tcDecodeWidth]
  cases RegEncoding.bit q b
  · simp [hlt]
  · have : ¬ RegEncoding.toNat e.active b + 2 ^ regSize e.active * 1 < 2 ^ regSize e.active := by
      omega
    simp only [Bool.toNat_true, this, dite_false]
    push_cast
    ring

end Basis

/-! ## T0: generic non-commutation criteria -/

section Gates
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]

/-- **A diagonal gate whose phase sees bit `q` does not commute with `X q`.** Hypotheses: `U`
acts on every ket by a scalar `s b` (`hU`), and for ONE basis state `b₀` the scalar changes when
bit `q` is flipped (`hne`). -/
theorem not_commX_of_diag {U : Gate} {q : ℕ} (s : qs.Basis → ℂ)
    (hU : ∀ b, qs.eval U (qs.ket b) = s b • qs.ket b) (b₀ : qs.Basis)
    (hne : s (flipBit q b₀) ≠ s b₀) : ¬ CommX qs U q := by
  intro h
  have e := h (qs.ket b₀)
  rw [eval_X_ket_flipBit, hU, hU, gate_eval_smul, eval_X_ket_flipBit] at e
  exact hne (smul_left_injective ℂ (qs.ket_ne_zero _) e)

/-- **A basis-permutation gate whose map does not commute with `flipBit q` at one basis state
does not commute with `X q`.** Hypotheses: `U` sends every ket `|b⟩` to `|f b⟩` (`hU`), and for
ONE basis state `b₀`, `f (flipBit q b₀) ≠ flipBit q (f b₀)` (`hne`). -/
theorem not_commX_of_basis {U : Gate} {q : ℕ} (f : qs.Basis → qs.Basis)
    (hU : ∀ b, qs.eval U (qs.ket b) = qs.ket (f b)) (b₀ : qs.Basis)
    (hne : f (flipBit q b₀) ≠ flipBit q (f b₀)) : ¬ CommX qs U q := by
  intro h
  have e := h (qs.ket b₀)
  rw [eval_X_ket_flipBit, hU, hU, eval_X_ket_flipBit] at e
  exact hne (qs.ket_inj e)

/-- Non-commutation survives PRE-composition with a gate that commutes with `X q`. -/
theorem not_commX_seq_left {U V : Gate} {q : ℕ} (hU : CommX qs U q) (hV : ¬ CommX qs V q) :
    ¬ CommX qs (U ;; V) q := by
  intro h
  apply hV
  intro φ
  have e := h (qs.eval (Gate.adj U) φ)
  simp only [QSemantics.eval, GateSemanticsCore.eval_seq] at e
  have hU' := hU (qs.eval (Gate.adj U) φ)
  simp only [QSemantics.eval] at hU'
  rw [hU'] at e
  have hφ := gate_eval_apply_adj (qs := qs) U φ
  simp only [QSemantics.eval] at hφ
  rw [hφ] at e
  exact e

/-- Non-commutation survives POST-composition with a gate that commutes with `X q`. -/
theorem not_commX_seq_right {U V : Gate} {q : ℕ} (hU : CommX qs U q) (hV : ¬ CommX qs V q) :
    ¬ CommX qs (V ;; U) q := by
  intro h
  apply hV
  intro φ
  have e := h φ
  simp only [QSemantics.eval, GateSemanticsCore.eval_seq] at e
  have hU' := hU (qs.eval V φ)
  simp only [QSemantics.eval] at hU'
  rw [← hU'] at e
  exact gate_eval_injective U e

end Gates

section LowGates
variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

/-- Low-level form of `not_commX_of_diag`. -/
theorem not_commXL_of_diag {L : LowGate} {q : ℕ} (s : qs.Basis → ℂ)
    (hL : ∀ b, LowerGateClass.evalL L (qs.ket b) = s b • qs.ket b) (b₀ : qs.Basis)
    (hne : s (flipBit q b₀) ≠ s b₀) : ¬ CommXL qs L q := by
  intro h
  have e := h (qs.ket b₀)
  rw [evalL_X_ket_flipBit, hL, hL, LowerGateClass.evalL_smul, evalL_X_ket_flipBit] at e
  exact hne (smul_left_injective ℂ (qs.ket_ne_zero _) e)

/-- Low-level form of `not_commX_of_basis`. -/
theorem not_commXL_of_basis {L : LowGate} {q : ℕ} (f : qs.Basis → qs.Basis)
    (hL : ∀ b, LowerGateClass.evalL L (qs.ket b) = qs.ket (f b)) (b₀ : qs.Basis)
    (hne : f (flipBit q b₀) ≠ flipBit q (f b₀)) : ¬ CommXL qs L q := by
  intro h
  have e := h (qs.ket b₀)
  rw [evalL_X_ket_flipBit, hL, hL, evalL_X_ket_flipBit] at e
  exact hne (qs.ket_inj e)

end LowGates


/-! ## Register helpers for the three gate shapes -/

section Basis2
variable {B : Type*} [RegEncoding B]

/-- Writing `v < 2` into `qubitReg q` sets bit `q` to `v = 1` (any encoding). -/
theorem bit_writeNat_qubitReg_self (q v : ℕ) (b : B) (hv : v < 2) :
    RegEncoding.bit q (RegEncoding.writeNat (qubitReg q) v b) = decide (v = 1) := by
  have hbit := RegEncoding.bit_eq_testBit_toNat (qubitReg q)
    (RegEncoding.writeNat (qubitReg q) v b) ⟨0, by simp [qubitReg, Reg.singleton, regSize, Reg.width]⟩
  change RegEncoding.bit q _ = _ at hbit
  rw [hbit, RegEncoding.toNat_writeNat_of_lt _ _ _ (by
    simpa [ASize, qubitReg, Reg.singleton, regSize, Reg.width] using hv)]
  interval_cases v <;> simp

theorem tcModWidth_lt_two_pow (w : ℕ) (z : ℤ) : tcModWidth w z < 2 ^ w := by
  unfold tcModWidth
  have hpos : (0 : ℤ) < ((2 ^ w : ℕ) : ℤ) := by positivity
  have h1 := Int.emod_nonneg z hpos.ne'
  have h2 := Int.emod_lt_of_pos z hpos
  omega

theorem tcDecodeWidth_zero_right (w : ℕ) : tcDecodeWidth w 0 = 0 := by
  cases w <;> simp [tcDecodeWidth]

theorem extToInt_zero_basis (e : ExtReg) : extToInt e (RegEncoding.zero : B) = 0 := by
  simp [extToInt, ExtReg.toNat, tcDecodeWidth_zero_right]

/-- A register disjoint from `s` does not see a write to `s`. -/
theorem toNat_writeNat_disjoint {r s : Reg} (h : ∀ p ∈ r.qubits, p ∉ s.qubits) (v : ℕ) (b : B) :
    RegEncoding.toNat r (RegEncoding.writeNat s v b) = RegEncoding.toNat r b :=
  toNat_congr_bits' r fun p hp => RegEncoding.bit_writeNat_out _ _ _ _ (h p hp)

/-- A qubit of the second reserve slot exists only if the reserve has two qubits. -/
theorem canGrow_two_of_mem_grow {e : ExtReg} {q : ℕ} (hq : q ∈ ((e.grow 1).newBits 1).qubits) :
    e.CanGrow 2 := by
  simp only [ExtReg.newBits, ExtReg.grow, ExtReg.remainingReserve, Reg.take, Reg.drop,
    ExtReg.CanGrow, ExtReg.capacity, regSize, Reg.width] at hq ⊢
  have h1 := List.length_pos_of_mem (List.mem_of_mem_take hq)
  rw [List.length_drop] at h1
  omega

theorem regSize_grow_active {e : ExtReg} (h : e.CanGrow 1) :
    regSize (e.grow 1).active = regSize e.active + 1 := by
  have := ExtReg.width_grow e 1 h
  simpa [ExtReg.width] using this

/-- The active qubits of a twice-grown register are owned by the original register. -/
theorem mem_owned_of_mem_grow_grow_active {e : ExtReg} {p : ℕ}
    (h : p ∈ ((e.grow 1).grow 1).active.qubits) : p ∈ e.ownedQubits := by
  have h1 : p ∈ ((e.grow 1).grow 1).ownedQubits := List.mem_append_left _ h
  rwa [Gate.ExtReg.ownedQubits_grow, Gate.ExtReg.ownedQubits_grow] at h1

/-- Wrapping `-(2^a)` to `s > a` bits does not give `0`. -/
theorem tcModWidth_neg_two_pow_ne_zero {a s : ℕ} (h : a < s) :
    tcModWidth s (-(2 ^ a : ℤ)) ≠ 0 := by
  unfold tcModWidth
  intro h0
  have hpos : (0 : ℤ) < ((2 ^ s : ℕ) : ℤ) := by positivity
  have hnn := Int.emod_nonneg (-(2 ^ a : ℤ)) hpos.ne'
  have hz : (-(2 ^ a : ℤ)) % ((2 ^ s : ℕ) : ℤ) = 0 := by omega
  have hd : ((2 ^ s : ℕ) : ℤ) ∣ ((2 ^ a : ℕ) : ℤ) := by
    have := Int.dvd_of_emod_eq_zero hz
    rw [Int.dvd_neg] at this
    exact_mod_cast this
  have hd' : 2 ^ s ∣ 2 ^ a := Int.natCast_dvd_natCast.mp hd
  have := Nat.le_of_dvd (by positivity) hd'
  have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h
  omega

end Basis2

/-! ## T1–T3: the three gate shapes read the reserve qubit -/

section Shapes
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]

/-- **`CmpGeConst` on a grown register reads the carry bit.** Hypotheses: `q` is the first
reserve qubit of `y` (`hq`), the flag is not an active qubit of `y.grow 1` (`hf`), and
`1 ≤ N ≤ 2^|y|` (so the values `0` and `2^|y|`, which differ only in bit `q`, lie on opposite
sides of `N`). Then `Gate.CmpGeConst N (y.grow 1) s f` does not commute with `X q`
(witness: the all-zero basis state). -/
theorem cmpGeConst_grow_not_commX {N : ℕ} {y s : ExtReg} {f q : ℕ}
    (hq : q ∈ (y.newBits 1).qubits) (hf : f ∉ (y.grow 1).active.qubits)
    (hN1 : 1 ≤ N) (hN2 : N ≤ 2 ^ regSize y.active) :
    ¬ CommX qs (Gate.CmpGeConst N (y.grow 1) s f) q := by
  have hqf : f ≠ q := fun h => hf (h ▸ mem_grow_active_of_newBits hq)
  have hqy : q ∉ y.active.qubits := not_mem_active_of_newBits hq
  refine not_commX_of_basis _ (fun b => ModularArithmeticSemantics.eval_CmpGeConst_ket N (y.grow 1) s f b)
    RegEncoding.zero fun h => ?_
  have e := congrArg (RegEncoding.bit f) h
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

/-- **`AddScaled` from a twice-grown source reads the source's sign bit.** Hypotheses: `q` is
the SECOND reserve qubit of `y` (the first reserve qubit of `y.grow 1`, `hq`), the destination
`d` owns no qubit of `y` (`hdisj`), and `|y| + 1 + sh < |d|` (so the change `2^(sh+|y|+1)` is
nonzero modulo `2^|d|`). Then `Gate.AddScaled d ((y.grow 1).grow 1) false sh` does not commute
with `X q` (witness: the all-zero basis state). -/
theorem addScaled_growgrow_not_commX {d y : ExtReg} {sh q : ℕ}
    (hq : q ∈ ((y.grow 1).newBits 1).qubits) (hdisj : ExtReg.OwnedDisjoint y d)
    (hw : regSize y.active + 1 + sh < regSize d.active) :
    ¬ CommX qs (Gate.AddScaled d ((y.grow 1).grow 1) false sh) q := by
  have hy1 : y.CanGrow 1 := ExtReg.CanGrow.mono (canGrow_two_of_mem_grow hq) (by norm_num)
  have hqo : q ∈ y.ownedQubits := mem_owned_of_mem_grow_grow_active (mem_grow_active_of_newBits hq)
  have hqd : q ∉ d.active.qubits := fun h => hdisj hqo (List.mem_append_left _ h)
  have hqg : q ∉ (y.grow 1).active.qubits := not_mem_active_of_newBits hq
  have hAD : ExtReg.ActiveDisjoint d ((y.grow 1).grow 1) := by
    unfold ExtReg.ActiveDisjoint Disjoint
    rw [List.disjoint_left]
    intro p hpd hps
    exact hdisj (mem_owned_of_mem_grow_grow_active hps) (List.mem_append_left _ hpd)
  refine not_commX_of_basis _
    (fun b => ArithmeticSemantics.eval_AddScaled_ket_total d ((y.grow 1).grow 1) false sh b)
    RegEncoding.zero fun h => ?_
  have e := congrArg (RegEncoding.toNat d.active) h
  have hs1 : extToInt ((y.grow 1).grow 1) (flipBit q (RegEncoding.zero : qs.Basis))
      = -(2 ^ (regSize y.active + 1) : ℤ) := by
    rw [extToInt_grow_one hq, toNat_flipBit hqg, toNat_zero_basis, bit_flipBit_self,
      RegEncoding.bit_zero, regSize_grow_active hy1]
    simp
  have hlt : ∀ z : ℤ, tcModWidth d.width z < ASize d.active := fun z => by
    simpa [ASize, ExtReg.width] using tcModWidth_lt_two_pow d.width z
  simp only [addScaledBasis, hAD, dite_true, toNat_flipBit hqd,
    RegEncoding.toNat_writeNat_of_lt _ _ _ (hlt _), extToInt_flipBit hqd, extToInt_zero_basis,
    hs1] at e
  have key : (0 : ℤ) + (if false = true then (-1 : ℤ) else 1) * 2 ^ sh
      * -(2 ^ (regSize y.active + 1) : ℤ) = -(2 ^ (sh + (regSize y.active + 1)) : ℤ) := by
    simp only [Bool.false_eq_true, ite_false]; ring
  rw [key] at e
  simp only [mul_zero, add_zero] at e
  have h0 : tcModWidth d.width 0 = 0 := by simp [tcModWidth]
  rw [h0] at e
  exact tcModWidth_neg_two_pow_ne_zero (show sh + (regSize y.active + 1) < d.width by
    unfold ExtReg.width; omega) e

/-- Ket law of `PhaseProdUsing` on EVERY ket (no cleanliness): the signed product of the two
grown operands. -/
theorem eval_PhaseProdUsing_ket_total (phi : Angle) {x z : Reg} (ws : Gate.PhaseProdWorkspace x z)
    (b : qs.Basis) :
    qs.eval (Gate.PhaseProdUsing phi x z ws) (qs.ket b)
      = Complex.exp (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
          (((extToInt (ws.xExt.grow 1) b : ℤ) : ℂ) * (((extToInt (ws.zExt.grow 1) b : ℤ) : ℂ))))
        • qs.ket b := by
  simp only [Gate.PhaseProdUsing, qs.eval_seq, ExtensionSemantics.eval_zeroExtend,
    ExtensionSemantics.eval_zeroDealloc]
  rw [PhaseSemantics.eval_SignedPhaseProd_ket]

/-- **`PhaseProdUsing` reads the sign-extension bit of its `x` operand.** Hypotheses: `q` is the
first qubit of the `x` reserve of the workspace (`hq`), `z` has at least one qubit (`hz`), and
`0 < φ · 2^|x| < 2` (`hphi0`, `hphi2`). Then `Gate.PhaseProdUsing φ x z ws` does not commute
with `X q`: from the basis state with `z = 1` and everything else `0`, flipping `q` changes the
phase by `exp(-iπ φ 2^|x|) ≠ 1`. -/
theorem phaseProdUsing_not_commX_xSign {x z : Reg} (ws : Gate.PhaseProdWorkspace x z)
    (phi : Angle) {q : ℕ} (hq : q ∈ (ws.xExt.newBits 1).qubits) (hz : 1 ≤ regSize z)
    (hphi0 : 0 < phi * 2 ^ regSize x) (hphi2 : phi * 2 ^ regSize x < 2) :
    ¬ CommX qs (Gate.PhaseProdUsing phi x z ws) q := by
  obtain ⟨zr, hzr⟩ : ∃ zr, zr ∈ (ws.zExt.newBits 1).qubits := by
    have := ws.z_can_grow
    simp only [Gate.PhaseProdWorkspace.zExt, ExtReg.newBits, ExtReg.withReserve_reserve,
      Reg.take, regSize, Reg.width] at this ⊢
    rcases h : ws.zReserve.qubits with _ | ⟨a, t⟩
    · simp [h] at this
    · exact ⟨a, by simp⟩
  have hqx : q ∉ ws.xExt.active.qubits := not_mem_active_of_newBits hq
  have hqR : q ∈ ws.xReserve.qubits := List.mem_of_mem_take hq
  have hqz : q ∉ z.qubits := fun h => ws.xReserve_not_z hqR h
  have hzrR : zr ∈ ws.zReserve.qubits := List.mem_of_mem_take hzr
  have hzrz : zr ∉ z.qubits := not_mem_active_of_newBits hzr
  have hqzr : zr ≠ q := fun h => ws.reserve_disjoint hqR (h ▸ hzrR)
  have hqZ : q ∉ ws.zExt.active.qubits := hqz
  have hxz : ∀ p ∈ ws.xExt.active.qubits, p ∉ z.qubits := fun p hp hz' => ws.xz_disjoint hp hz'
  set b₀ : qs.Basis := RegEncoding.writeNat z 1 RegEncoding.zero with hb₀
  refine not_commX_of_diag _ (eval_PhaseProdUsing_ket_total phi ws) b₀ ?_
  have hz1 : RegEncoding.toNat ws.zExt.active b₀ = 1 :=
    RegEncoding.toNat_writeNat_of_lt _ _ _ (by
      unfold ASize
      exact Nat.one_lt_two_pow (show regSize ws.zExt.active ≠ 0 by change regSize z ≠ 0; omega))
  have hx0 : RegEncoding.toNat ws.xExt.active b₀ = 0 := by
    rw [hb₀, toNat_writeNat_disjoint hxz, toNat_zero_basis]
  have hbq : RegEncoding.bit q b₀ = false := by
    rw [hb₀, RegEncoding.bit_writeNat_out _ _ _ _ hqz, RegEncoding.bit_zero]
  have hbzr : RegEncoding.bit zr b₀ = false := by
    rw [hb₀, RegEncoding.bit_writeNat_out _ _ _ _ hzrz, RegEncoding.bit_zero]
  have hX0 : extToInt (ws.xExt.grow 1) b₀ = 0 := by
    rw [extToInt_grow_one hq, hx0, hbq]; simp
  have hX1 : extToInt (ws.xExt.grow 1) (flipBit q b₀) = -(2 ^ regSize x : ℤ) := by
    rw [extToInt_grow_one hq, toNat_flipBit hqx, hx0, bit_flipBit_self, hbq]; simp; rfl
  have hZ0 : extToInt (ws.zExt.grow 1) b₀ = 1 := by
    rw [extToInt_grow_one hzr, hz1, hbzr]; simp
  have hZ1 : extToInt (ws.zExt.grow 1) (flipBit q b₀) = 1 := by
    rw [extToInt_grow_one hzr, toNat_flipBit hqZ, hz1, bit_flipBit_ne hqzr, hbzr]; simp
  rw [hX0, hX1, hZ0, hZ1]
  simp only [Int.cast_zero, mul_zero, Complex.exp_zero, Int.cast_one, mul_one]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have him := congrArg Complex.im hn
  simp [Angle.toReal] at him
  have hre : ((2 : ℂ) ^ regSize x).re = 2 ^ regSize x := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hre] at him
  have hr0 : (0 : ℝ) < (phi : ℝ) * 2 ^ regSize x := by exact_mod_cast hphi0
  have hr2 : (phi : ℝ) * 2 ^ regSize x < 2 := by exact_mod_cast hphi2
  have hpi := Real.pi_pos
  have heq : Real.pi * ((phi : ℝ) * 2 ^ regSize x) = Real.pi * (-2 * n) := by linarith
  have heq' := mul_left_cancel₀ Real.pi_ne_zero heq
  have hn1 : (-1 : ℝ) < n := by linarith
  have hn2 : (n : ℝ) < 0 := by linarith
  have : (-1 : ℤ) < n := by exact_mod_cast hn1
  have : n < 0 := by exact_mod_cast hn2
  omega

/-- **Positive counterpart: a `SignedPhaseProd` whose angle is a multiple of `2 / 2^|e|`
commutes with `X` on the sign-extension bit of its grown `z` operand.** Hypotheses: `q` is the
first reserve qubit of `e` (`hq`), `q` is not an active qubit of `x` (`hx`), and
`φ · 2^|e| = 2k` for an integer `k` (`hphi`). Flipping `q` shifts `extToInt (e.grow 1)` by
`± 2^|e|`, so the phase changes by `exp(± iπ φ 2^|e| · x) = exp(± 2πi k x) = 1`. -/
theorem signedPhaseProd_grow_commX_top {phi : Angle} {x e : ExtReg} {q : ℕ}
    (hq : q ∈ (e.newBits 1).qubits) (hx : q ∉ x.active.qubits) (k : ℤ)
    (hphi : phi * 2 ^ regSize e.active = 2 * k) :
    CommX qs (Gate.SignedPhaseProd phi x (e.grow 1)) q := by
  refine commX_of_diag _ (PhaseSemantics.eval_SignedPhaseProd_ket phi x (e.grow 1)) fun b => ?_
  have hqe : q ∉ e.active.qubits := not_mem_active_of_newBits hq
  have hc : (phi : ℂ) * 2 ^ regSize e.active = 2 * (k : ℂ) := by
    have := congrArg (fun r : ℚ => (r : ℂ)) hphi
    push_cast at this
    exact this
  rw [extToInt_flipBit hx, extToInt_grow_one hq, extToInt_grow_one hq, toNat_flipBit hqe,
    bit_flipBit_self, Complex.exp_eq_exp_iff_exists_int]
  cases RegEncoding.bit q b
  · refine ⟨-(k * extToInt x b), ?_⟩
    simp only [Angle.toReal, Bool.not_false, Bool.toNat_true, Bool.toNat_false]
    push_cast
    linear_combination (-(Real.pi : ℂ) * Complex.I * (extToInt x b : ℂ)) * hc
  · refine ⟨k * extToInt x b, ?_⟩
    simp only [Angle.toReal, Bool.not_true, Bool.toNat_true, Bool.toNat_false]
    push_cast
    linear_combination ((Real.pi : ℂ) * Complex.I * (extToInt x b : ℂ)) * hc

end Shapes


/-! ## A finer spectator criterion: every node commutes -/

section Local
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [MeasureClass qs]

/-- `U` commutes with `X q` and with both Z projectors of `q`, on every state. -/
def GateLocal (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs] [MeasureClass qs]
    (U : Gate) (q : ℕ) : Prop :=
  CommX qs U q ∧ ∀ o, CommP qs U q o

theorem gateLocal_of_exact {U : Gate} (hU : U.NoIdeal) {q : ℕ} (hq : q ∉ U.exactSupport) :
    GateLocal qs U q :=
  ⟨gate_commX_exact U hU hq, fun o => gate_commP_exact U hU hq o⟩

theorem GateLocal.seq {U V : Gate} {q : ℕ} (hU : GateLocal qs U q) (hV : GateLocal qs V q) :
    GateLocal qs (U ;; V) q :=
  ⟨commX_seq hU.1 hV.1, fun o => commP_seq (hU.2 o) (hV.2 o)⟩

theorem GateLocal.adj {U : Gate} {q : ℕ} (hU : GateLocal qs U q) : GateLocal qs (Gate.adj U) q :=
  ⟨commX_adj hU.1, fun o => commP_adj (hU.2 o)⟩

/-- A diagonal gate that commutes with `X q` is `GateLocal` at `q` (diagonal gates commute
with every Z projector). -/
theorem gateLocal_of_diag {U : Gate} {q : ℕ} (s : qs.Basis → ℂ)
    (hU : ∀ b, qs.eval U (qs.ket b) = s b • qs.ket b) (hX : CommX qs U q) : GateLocal qs U q :=
  ⟨hX, fun _ => commP_of_diag s hU⟩

end Local

section LocalM
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- `P.LocalAt qs q`: every unitary node of `P` is `GateLocal` at `q`, and `q` is not the
qubit of any `measureReset` or `ffPhase` node. (Weaker than `q ∉ P.exactSupport` with
`P.NoIdeal`: a node may READ `q` in its ket-law formula and still commute, see
`signedPhaseProd_grow_commX_top`.) -/
def _root_.Shor.MGate.LocalAt (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs]
    [MeasureClass qs] (q : ℕ) : MGate → Prop
  | .unitary g => GateLocal qs g q
  | .seq a b => MGate.LocalAt qs q a ∧ MGate.LocalAt qs q b
  | .measureReset p => q ≠ p
  | .ffPhase p _ => q ≠ p

theorem MGate.eval_commX_of_localAt (P : MGate) {q : ℕ} (hP : P.LocalAt qs q) (ψ : MState qs) :
    P.eval (fun r => qs.eval (Gate.X q) (ψ r)) = fun r => qs.eval (Gate.X q) (P.eval ψ r) := by
  induction P generalizing ψ with
  | unitary g =>
    funext r
    exact hP.1 (ψ r)
  | seq a b iha ihb =>
    simp only [MGate.eval_seq]
    rw [iha hP.1, ihb hP.2]
  | measureReset p =>
    funext r
    simp only [MGate.eval]
    split
    · rw [MGate.gate_eval_zero_state]
    · exact measureResetBranch_commX hP _ _
  | ffPhase p j =>
    funext r
    exact phase_commX hP _ _

theorem MGate.eval_commProj_of_localAt (P : MGate) {q : ℕ} (hP : P.LocalAt qs q) (o : ℕ)
    (ψ : MState qs) :
    P.eval (fun r => measProj (qubitReg q) o (ψ r))
      = fun r => measProj (qubitReg q) o (P.eval ψ r) := by
  induction P generalizing ψ with
  | unitary g =>
    funext r
    exact hP.2 o (ψ r)
  | seq a b iha ihb =>
    simp only [MGate.eval_seq]
    rw [iha hP.1, ihb hP.2]
  | measureReset p =>
    funext r
    simp only [MGate.eval]
    split
    · simp
    · exact measureResetBranch_commProj hP o _ _
  | ffPhase p j =>
    funext r
    exact phase_commProj p q o _ _

/-- **A qubit at which every node of `P` is local is a spectator on every state.** -/
theorem MGate.spectatorOn_of_localAt (P : MGate) {q : ℕ} (hP : P.LocalAt qs q) :
    P.SpectatorOn q (⊤ : Submodule ℂ qs.State) :=
  ⟨fun ψ _ => MGate.eval_commX_of_localAt P hP ψ,
    fun o ψ _ => MGate.eval_commProj_of_localAt P hP o ψ⟩

end LocalM

/-! ## T5: a record probability that changes when an `x` sign-extension bit is flipped (toy) -/

section Toy
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- The toy phase-kick program on one-qubit operands `x = [xq]`, `z = [zq]`:
`H zq ; PhaseProdUsing (1/2) x z ws ; H zq ; measureReset zq`. -/
def toyPhaseKick (xq zq : ℕ) (ws : Gate.PhaseProdWorkspace (qubitReg xq) (qubitReg zq)) : MGate :=
  .seq (.unitary (Gate.H zq))
    (.seq (.unitary (Gate.PhaseProdUsing (1 / 2) (qubitReg xq) (qubitReg zq) ws))
      (.seq (.unitary (Gate.H zq)) (.measureReset zq)))

/-- **Toy record change.** In the 4-qubit toy program `toyPhaseKick` (operands `x = [xq]`,
`z = [zq]`, angle `1/2`), let `q` be the `x` sign-extension (first `x` reserve) qubit and `zr`
the first `z` reserve qubit. From a basis state `b` with bits `xq`, `zq`, `q`, `zr` all `0`,
record `[false]` has probability `1`; from `b` with bit `q` flipped, probability `0` (the
flipped sign bit makes the operand read `-2`, the phase becomes a `Z` on `zq` between the two
`H`s). NOT claimed: anything about the real order-finding circuit, whose record distribution
under such a flip is not computed in this development. -/
theorem toyPhaseKick_recordProb (xq zq : ℕ)
    (ws : Gate.PhaseProdWorkspace (qubitReg xq) (qubitReg zq)) {q zr : ℕ}
    (hq : q ∈ (ws.xExt.newBits 1).qubits) (hzr : zr ∈ (ws.zExt.newBits 1).qubits)
    (b : qs.Basis) (hxb : RegEncoding.bit xq b = false) (hzb : RegEncoding.bit zq b = false)
    (hqb : RegEncoding.bit q b = false) (hzrb : RegEncoding.bit zr b = false) :
    recordProb ((toyPhaseKick xq zq ws).eval (MState.init (qs.ket b))) [false] = 1 ∧
    recordProb ((toyPhaseKick xq zq ws).eval (MState.init (qs.ket (flipBit q b)))) [false]
      = 0 := by
  -- disjointness facts
  have mem1 : ∀ p : ℕ, p ∈ (qubitReg p).qubits := fun p => by simp [qubitReg, Reg.singleton]
  have hqR : q ∈ ws.xReserve.qubits := List.mem_of_mem_take hq
  have hzrR : zr ∈ ws.zReserve.qubits := List.mem_of_mem_take hzr
  have hqz : zq ≠ q := fun h => ws.xReserve_not_z hqR (h ▸ mem1 zq)
  have hqx : xq ≠ q := fun h => ws.x_reserve_disjoint (mem1 xq) (h ▸ hqR)
  have hxz : zq ≠ xq := fun h => ws.xz_disjoint (mem1 xq) (h ▸ mem1 zq)
  have hzrz : zr ≠ zq := fun h => ws.z_reserve_disjoint (mem1 zq) (h ▸ hzrR)
  have hzrq : zr ≠ q := fun h => ws.reserve_disjoint hqR (h ▸ hzrR)
  -- the two operand readings
  have hX : ∀ c : qs.Basis, extToInt (ws.xExt.grow 1) c
      = ((RegEncoding.bit xq c).toNat : ℤ) - 2 * (RegEncoding.bit q c).toNat := fun c => by
    rw [extToInt_grow_one hq]
    change ((RegEncoding.toNat (qubitReg xq) c : ℕ) : ℤ) - 2 ^ regSize (qubitReg xq) * _ = _
    rw [toNat_qubitReg_toNat]; rfl
  have hZ : ∀ c : qs.Basis, extToInt (ws.zExt.grow 1) c
      = ((RegEncoding.bit zq c).toNat : ℤ) - 2 * (RegEncoding.bit zr c).toNat := fun c => by
    rw [extToInt_grow_one hzr]
    change ((RegEncoding.toNat (qubitReg zq) c : ℕ) : ℤ) - 2 ^ regSize (qubitReg zq) * _ = _
    rw [toNat_qubitReg_toNat]; rfl
  -- Hadamard on kets
  have hH0 : ∀ c : qs.Basis, RegEncoding.bit zq c = false →
      qs.eval (Gate.H zq) (qs.ket c)
        = ((1 / Real.sqrt (2 : ℝ) : ℂ)) • (qs.ket c + qs.ket (flipBit zq c)) := fun c h => by
    have h0 : RegEncoding.writeNat (qubitReg zq) 0 c = c := by
      have := writeNat_qubitReg_self (qs := qs) zq c; rw [h] at this; simpa using this
    have h1 : RegEncoding.writeNat (qubitReg zq) 1 c = flipBit zq c := by
      unfold flipBit; rw [h]; rfl
    rw [HadamardSemantics.eval_H_ket, h, h0, h1]; simp
  have hH1 : ∀ c : qs.Basis, RegEncoding.bit zq c = true →
      qs.eval (Gate.H zq) (qs.ket c)
        = ((1 / Real.sqrt (2 : ℝ) : ℂ)) • (qs.ket (flipBit zq c) - qs.ket c) := fun c h => by
    have h1 : RegEncoding.writeNat (qubitReg zq) 1 c = c := by
      have := writeNat_qubitReg_self (qs := qs) zq c; rw [h] at this; simpa using this
    have h0 : RegEncoding.writeNat (qubitReg zq) 0 c = flipBit zq c := by
      unfold flipBit; rw [h]; rfl
    rw [HadamardSemantics.eval_H_ket, h, h0, h1]; simp [sub_eq_add_neg]
  have hc := invSqrtTwo_mul_self
  -- the run, branch `[false]`
  have hrun : ∀ ψ : qs.State, (toyPhaseKick xq zq ws).eval (MState.init ψ) [false]
      = measProj (qubitReg zq) 0 (qs.eval (Gate.H zq)
          (qs.eval (Gate.PhaseProdUsing (1 / 2) (qubitReg xq) (qubitReg zq) ws)
            (qs.eval (Gate.H zq) ψ))) := fun ψ => by
    have := MGate.eval_measureReset_append zq
      ((MGate.unitary (Gate.H zq)).eval ((MGate.unitary (Gate.PhaseProdUsing (1 / 2) (qubitReg xq)
        (qubitReg zq) ws)).eval ((MGate.unitary (Gate.H zq)).eval (MState.init ψ)))) [] false
    simpa [toyPhaseKick, MState.init, measureResetBranch] using this
  have hP := eval_PhaseProdUsing_ket_total (qs := qs) (1 / 2 : Angle) ws
  have hzf : RegEncoding.bit zq (flipBit zq b) = true := by rw [bit_flipBit_self, hzb]; rfl
  constructor
  · -- unflipped: the phase is trivial
    have hp0 : qs.eval (Gate.PhaseProdUsing (1 / 2) (qubitReg xq) (qubitReg zq) ws) (qs.ket b)
        = qs.ket b := by
      rw [hP, hX, hxb, hqb]; simp
    have hp1 : qs.eval (Gate.PhaseProdUsing (1 / 2) (qubitReg xq) (qubitReg zq) ws)
        (qs.ket (flipBit zq b)) = qs.ket (flipBit zq b) := by
      rw [hP, hX, bit_flipBit_ne (Ne.symm hxz), bit_flipBit_ne (Ne.symm hqz), hxb, hqb]; simp
    rw [recordProb, hrun, hH0 b hzb, gate_eval_smul, gate_eval_add, hp0, hp1, gate_eval_smul,
      gate_eval_add, hH0 b hzb, hH1 _ hzf, flipBit_flipBit]
    rw [show ((1 / Real.sqrt (2 : ℝ) : ℂ)) • (((1 / Real.sqrt (2 : ℝ) : ℂ)) •
        (qs.ket b + qs.ket (flipBit zq b)) + ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
        (qs.ket b - qs.ket (flipBit zq b))) = qs.ket b by
      rw [← smul_add, smul_smul, hc]; module]
    rw [measProj_qubitReg_ket, hzb]
    simp [ket_norm_one]
  · -- flipped sign bit: the phase is a `Z` on `zq`
    set b' := flipBit q b with hb'
    have hzb' : RegEncoding.bit zq b' = false := by rw [hb', bit_flipBit_ne hqz, hzb]
    have hxb' : RegEncoding.bit xq b' = false := by rw [hb', bit_flipBit_ne hqx, hxb]
    have hqb' : RegEncoding.bit q b' = true := by rw [hb', bit_flipBit_self, hqb]; rfl
    have hzrb' : RegEncoding.bit zr b' = false := by rw [hb', bit_flipBit_ne hzrq, hzrb]
    have hzf' : RegEncoding.bit zq (flipBit zq b') = true := by rw [bit_flipBit_self, hzb']; rfl
    have hp0 : qs.eval (Gate.PhaseProdUsing (1 / 2) (qubitReg xq) (qubitReg zq) ws) (qs.ket b')
        = qs.ket b' := by
      rw [hP, hX, hZ, hxb', hqb', hzb', hzrb']; simp
    have hp1 : qs.eval (Gate.PhaseProdUsing (1 / 2) (qubitReg xq) (qubitReg zq) ws)
        (qs.ket (flipBit zq b')) = -qs.ket (flipBit zq b') := by
      rw [hP, hX, hZ, bit_flipBit_ne (Ne.symm hxz), bit_flipBit_ne (Ne.symm hqz), bit_flipBit_ne hzrz,
        hzf', hxb', hqb', hzrb']
      have : Complex.exp (((Angle.toReal (1 / 2 : Angle) : ℝ) : ℂ) * Complex.I *
          ((((false.toNat : ℤ) - 2 * (true.toNat : ℤ) : ℤ) : ℂ) *
            ((((true.toNat : ℤ) - 2 * (false.toNat : ℤ) : ℤ) : ℂ)))) = -1 := by
        rw [show ((Angle.toReal (1 / 2 : Angle) : ℝ) : ℂ) * Complex.I *
            ((((false.toNat : ℤ) - 2 * (true.toNat : ℤ) : ℤ) : ℂ) *
              ((((true.toNat : ℤ) - 2 * (false.toNat : ℤ) : ℤ) : ℂ))) = -(Real.pi * Complex.I) by
          simp [Angle.toReal]; ring]
        rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
      rw [this, neg_one_smul]
    rw [recordProb, hrun, hH0 b' hzb', gate_eval_smul, gate_eval_add, hp0, hp1, gate_eval_smul,
      gate_eval_add, gate_eval_neg, hH0 b' hzb', hH1 _ hzf', flipBit_flipBit]
    rw [show ((1 / Real.sqrt (2 : ℝ) : ℂ)) • (((1 / Real.sqrt (2 : ℝ) : ℂ)) •
        (qs.ket b' + qs.ket (flipBit zq b')) + -(((1 / Real.sqrt (2 : ℝ) : ℂ)) •
        (qs.ket b' - qs.ket (flipBit zq b')))) = qs.ket (flipBit zq b') by
      rw [← smul_neg, ← smul_add, smul_smul, hc]; module]
    rw [measProj_qubitReg_ket, hzf']
    simp

end Toy

end Readout
end Shor
