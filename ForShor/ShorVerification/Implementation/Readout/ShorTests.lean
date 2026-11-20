import ForShor.ShorVerification.Implementation.Readout.Shor
import ForShor.ShorVerification.Implementation.Readout.Support

/-!
# Readout: tests of the semiclassical order-finding circuit

* `collision_concrete` / `layout_concrete`: a control that is a data qubit is
  rejected (`layout_collision_rejected`), and a control outside every register
  has a `SemiclassicalLayout` witness (so the structure is not empty).
* `multiplier_is_modExp_step`: round `j`'s multiplier is exactly the gate
  `modExpApproxStepsValid` applies for the exponent bit of weight
  `2^(m-1-j)` when that bit's control is `c` (same constant `a^(2^(m-1-j)) mod N`,
  same Step-5 constant, same workspaces): the relabelling `x_(m-1-j) ↔ c`.
* `multiplier_one_round`: with `m = 1` the only multiplier is by `a mod N`.
* `orderFindingSemiclassical_one_round`: with `m = 1` the circuit run from
  `|b0⟩` is one implemented round (`H c`, multiplier by `a mod N`, exact phase
  `ffAngle 0 = 0`, `H c`, measure and reset) from `initY1 |b0⟩ = |b0 with y := 1⟩`.
* `support_contains_control`: with `m ≥ 1` rounds the control `c` is named by the
  circuit (the support theorem `orderFindingSemiclassical_support` is not about
  an empty set).
* `globalPhase_dist_zero` / `globalPhase_not_exact_close`: rotations equal to the
  exact phase times a global phase `exp(iβ)` satisfy the up-to-phase hypothesis
  with `ρ = 0`, so the record distribution is exactly the ideal one; at `β = π`
  the same rotations are `2‖φ‖` away from the exact phase, so the exact-phase
  hypothesis of `semiclassical_dist_le_sum_errors` would only give `ρ = 2`.

The full hypotheses of the success theorems are instantiated at the concrete
model in `Model/Standard/SemiclassicalShorModel.lean`.
-/

namespace Shor
namespace Readout
namespace ShorTests

/-- Control `2` is a qubit of the data register `[2, 3]`: rejected. -/
theorem collision_concrete (work scratch : ExtReg) (flag : ℕ) :
    ¬ SemiclassicalLayout 2 (ExtReg.ofReg ⟨[2, 3], by decide⟩) work scratch flag :=
  layout_collision_rejected 2 _ work scratch flag (by simp [ExtReg.ownedQubits, ExtReg.ofReg])

/-- Control `4` outside data `[2, 3]`, work `[5]`, scratch `[6]`, flag `7`: a
`SemiclassicalLayout` exists. -/
theorem layout_concrete :
    SemiclassicalLayout 4 (ExtReg.ofReg ⟨[2, 3], by decide⟩) (ExtReg.ofReg ⟨[5], by decide⟩)
      (ExtReg.ofReg ⟨[6], by decide⟩) 7 where
  c_not_mem_data := by simp [ExtReg.ownedQubits, ExtReg.ofReg, Reg.empty]
  c_not_mem_work := by simp [ExtReg.ownedQubits, ExtReg.ofReg, Reg.empty]
  c_not_mem_scratch := by simp [ExtReg.ownedQubits, ExtReg.ofReg, Reg.empty]
  c_ne_flag := by decide

/-- **Relabelling `x_(m-1-j) ↔ c`.** The modular-exponentiation step for the
exponent position `e = m-1-j` with control `c` is round `j`'s multiplier
(followed by the empty rest). -/
theorem multiplier_is_modExp_step (a N c m j : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    modExpApproxStepsValid a N y work scratch flag hw hs4 (m - 1 - j) [c]
      = (semiclassicalMultipliers a N c m y work scratch flag hw hs4 j ;; Gate.id) :=
  rfl

/-- With one round the multiplier is by `a mod N`. -/
theorem multiplier_one_round (a N c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    semiclassicalMultipliers a N c 1 y work scratch flag hw hs4 0
      = CmodMulInPlaceCore (a % N) N c y work scratch flag hw hs4 := by
  simp [semiclassicalMultipliers]

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  [LowerGateClass qs] [MeasureClass qs]

/-- **One round (`m = 1`).** From `|b0⟩` with data `y = 0` (nonempty `y`), the
circuit is one implemented round with the multiplier by `a mod N` and the exact
phase, run from `|b0 with y := 1⟩`. -/
theorem orderFindingSemiclassical_one_round (a N c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 : qs.Basis)
    (hy : 0 < regSize y.active) (hy0 : RegEncoding.toNat y.active b0 = 0) :
    (orderFindingSemiclassical a N c 1 y work scratch flag hw hs4).eval (MState.init (qs.ket b0))
      = implRound c (CmodMulInPlaceCore (a % N) N c y work scratch flag hw hs4) (exactPhase c 0)
          (MState.init (qs.ket (RegEncoding.writeNat y.active 1 b0))) := by
  rw [orderFindingSemiclassical_eval a N c 1 y work scratch flag hw hs4 b0 hy hy0,
    ← multiplier_one_round a N c y work scratch flag hw hs4]
  rfl

omit [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
/-- With at least one round the control is in the circuit's qubit support. -/
theorem support_contains_control (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (hm : 1 ≤ m) :
    c ∈ (orderFindingSemiclassical a N c m y work scratch flag hw hs4).qubitSupport := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp [orderFindingSemiclassical, readoutRounds, MGate.qubitSupport, Gate.qubitSupport]

section GlobalPhase

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis]
  [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]
  [HadamardSemantics qs] [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs]

/-- The exact feed-forward phases times a global phase `exp(iβ)`. -/
noncomputable def globallyPhased (c : ℕ) (β : ℝ) : ℕ → Record → qs.State →ₗ[ℂ] qs.State :=
  fun j r => Complex.exp ((β : ℂ) * Complex.I) • exactPhase c j r

/-- **A global phase costs nothing.** With exact multipliers and rotations
`exp(iβ) · Phase c (ffAngle j r)`, the up-to-phase bound holds with `ε = ρ = 0`
(take `α = -β`), so the `ℓ¹` distance to the ideal record distribution is `≤ 0`. -/
theorem globalPhase_dist_zero
    (a N m : ℕ) (data : Reg) (c : ℕ) (P : qs.Basis → Prop)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hPc : ∀ x v, P x → P (RegEncoding.writeNat (qubitReg c) v x))
    (hPdata : ∀ x v, P x → P (RegEncoding.writeNat data v x))
    (ψ₀ : qs.State) (hψ₀ : InRangeOn c data N P ψ₀) (hnorm : ‖ψ₀‖ = 1) (β : ℝ) :
    ∑' r : Record, |recordProb (semiclassicalImpl c (schedule a N m data c) (globallyPhased c β) m
          (MState.init ψ₀)) r
        - recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r| ≤ 0 := by
  have hU : ∀ j < m, ∀ φ ∈ ValidSpan data N P,
      ‖qs.eval (schedule a N m data c j) φ
          - qs.eval (Gate.idealCtrlModMul ((a ^ (2 ^ (m - 1 - j))) % N) N data c) φ‖
        ≤ (fun _ => (0 : ℝ)) j * ‖φ‖ := fun j _ φ _ => by simp [schedule]
  have hRg : ∀ j < m, ∀ r : Record, r.length = j → ∃ α : ℝ, ∀ φ : qs.State,
      ‖Complex.exp ((α : ℂ) * Complex.I) • globallyPhased c β j r φ
          - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ (fun _ => (0 : ℝ)) j * ‖φ‖ :=
    fun j _ r _ => ⟨-β, fun φ => by
      simp only [globallyPhased, LinearMap.smul_apply, smul_smul, exactPhase, lowL_apply]
      rw [← Complex.exp_add, show ((-β : ℝ) : ℂ) * Complex.I + (β : ℂ) * Complex.I = 0 by
        push_cast; ring, Complex.exp_zero, one_smul, sub_self]
      simp⟩
  have hRc : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖globallyPhased c β j r φ‖ ≤ ‖φ‖ := fun j _ r _ φ => by
    simp only [globallyPhased, LinearMap.smul_apply, norm_smul, norm_exp_mul_I, one_mul,
      exactPhase, lowL_apply]
    rw [norm_evalL_phase]
  have h := semiclassical_dist_le_sum_errors_up_to_phase a N m data c P hN hNdata ha hc hPc
    hPdata ψ₀ hψ₀ hnorm _ _ (fun _ => 0) (fun _ => 0) hU hRg hRc
  simpa using h

omit [GateSemanticsCore qs] [MeasureClass qs] [HadamardSemantics qs] [PauliXSemantics qs]
  [IdealCtrlModMulExactSemantics qs] in
/-- At `β = π` the globally phased rotation is `-Phase`, at distance exactly
`2‖φ‖` from the exact phase: the exact-phase hypothesis `hR` would need
`ρ j ≥ 2` (vacuous bound), while the up-to-phase hypothesis holds with `ρ = 0`. -/
theorem globalPhase_not_exact_close (c j : ℕ) (r : Record) (φ : qs.State) :
    ‖globallyPhased c Real.pi j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖
      = 2 * ‖φ‖ := by
  simp only [globallyPhased, LinearMap.smul_apply, exactPhase, lowL_apply]
  rw [show ((Real.pi : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I by rfl, Complex.exp_pi_mul_I,
    neg_one_smul, ← neg_add', norm_neg, ← two_smul ℂ, norm_smul, norm_evalL_phase]
  norm_num

end GlobalPhase

end ShorTests
end Readout
end Shor
