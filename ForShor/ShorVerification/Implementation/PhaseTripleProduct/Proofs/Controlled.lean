import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Surface
/-!
# Controlled PTP by operand masking (blueprint item O3, masked-operand form)

`c`-controlled PTP: apply `exp(i·π·φ·⟦x₀⟧⟦x₁⟧⟦x₂⟧)` when the control qubit `c` is `|1⟩`, and the
identity when it is `|0⟩`. Scope: on the span of **clean** kets only (the fresh register `Y` and the
recursion workspace are `|0⟩`, the operands fit signed `n` bits, `n ≥ 1`); this is not a statement
about arbitrary states, and ForShor's leaf-controlled gate is not what is built.

**Construction (not ForShor's leaf control).** The phase is trilinear in integers, so
`c · x₀` can replace `x₀`: in two's complement, the bitwise AND of an `n`-bit register with a
single bit `c` is exactly the register holding `c · x₀` (`tcDecodeWidth_mask`). The circuit is

    mask ;; G(Y, X₁, X₂) ;; †mask,      mask = ∏ᵢ Toffoli c (X₀ᵢ) (Yᵢ),

with `Y` a fresh clean `n`-qubit register and `G` any circuit meeting the *uncontrolled* PTP
contract on `(Y, X₁, X₂)` (for instance `ptp_gate_full_exact`'s). No proof about the node or the
recursion is redone; the control costs `2n` Toffoli (`n` of them uncomputations), `n + 1` extra qubits (`Y` and the control)
and no extra rotations. ForShor's `controlPhaseLeaves` instead controls every leaf phase
(three rotations per leaf cell instead of one); the two constructions have different cost
profiles and neither is claimed optimal. The leaf-control construction remains open.

Contents: `maskGate`, `evalL_maskGate_ket` (basis behaviour), `toNat_mask` (register value),
`evalL_ctlGate_ket` (controlled correctness from an uncontrolled gate), and in
`ControlledPolicy` section the instantiation at the exact board.
-/

namespace Shor
namespace PTP

open Shor

/-! ## The mask gate -/


/-- Side conditions: targets distinct, the control and every source are not targets, and no
source equals the control. -/
structure MaskOK (c : ℕ) (ps : List (ℕ × ℕ)) : Prop where
  nodup : (ps.map Prod.snd).Nodup
  c_ne_x : ∀ p ∈ ps, c ≠ p.1
  c_ne_y : ∀ p ∈ ps, c ≠ p.2
  x_ne_y : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2

theorem MaskOK.tail {c : ℕ} {p : ℕ × ℕ} {ps : List (ℕ × ℕ)} (h : MaskOK c (p :: ps)) :
    MaskOK c ps where
  nodup := (List.nodup_cons.mp (by simpa using h.nodup)).2
  c_ne_x := fun q hq => h.c_ne_x q (List.mem_cons_of_mem _ hq)
  c_ne_y := fun q hq => h.c_ne_y q (List.mem_cons_of_mem _ hq)
  x_ne_y := fun q hq r hr =>
    h.x_ne_y q (List.mem_cons_of_mem _ hq) r (List.mem_cons_of_mem _ hr)


section Mask

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

/-- **Basis behaviour of the mask.** On a state whose targets are `|0⟩`, the mask writes
`c ∧ xᵢ` into every target `yᵢ`, leaves every other bit alone, and is a basis state again. -/
theorem evalL_maskGate_ket (c : ℕ) :
    ∀ (ps : List (ℕ × ℕ)), MaskOK c ps → ∀ (b : qs.Basis),
      (∀ p ∈ ps, RegEncoding.bit p.2 b = false) →
      ∃ b' : qs.Basis, LowerGateClass.evalL (qs := qs) (maskGate c ps) (qs.ket b) = qs.ket b' ∧
        (∀ p ∈ ps, RegEncoding.bit p.2 b' = (RegEncoding.bit c b && RegEncoding.bit p.1 b)) ∧
        (∀ q, q ∉ ps.map Prod.snd → RegEncoding.bit q b' = RegEncoding.bit q b)
  | [], _, b, _ => ⟨b, by simp [maskGate, LowerGateClass.evalL_id], by simp, by simp⟩
  | p :: ps, h, b, hz => by
      have hc1 : c ≠ p.1 := h.c_ne_x p (List.mem_cons_self ..)
      have hc2 : c ≠ p.2 := h.c_ne_y p (List.mem_cons_self ..)
      have hxy : p.1 ≠ p.2 := h.x_ne_y p (List.mem_cons_self ..) p (List.mem_cons_self ..)
      have hnd := List.nodup_cons.mp (by simpa using h.nodup : (p.2 :: ps.map Prod.snd).Nodup)
      set b1 := toffoliBasis c p.1 p.2 b with hb1
      -- bits at other positions are unchanged by the first Toffoli
      have hkeep : ∀ q, q ≠ p.2 → RegEncoding.bit q b1 = RegEncoding.bit q b := fun q hq =>
        LowerGateClass.bit_toffoliBasis_of_ne_target c p.1 p.2 q b hq
      have hz1 : ∀ r ∈ ps, RegEncoding.bit r.2 b1 = false := by
        intro r hr
        have hne : r.2 ≠ p.2 := fun e => hnd.1 (e ▸ List.mem_map_of_mem hr)
        rw [hkeep _ hne]; exact hz r (List.mem_cons_of_mem _ hr)
      obtain ⟨b', he, hb'1, hb'2⟩ := evalL_maskGate_ket c ps h.tail b1 hz1
      have hxne : ∀ r ∈ ps, r.1 ≠ p.2 := fun r hr =>
        h.x_ne_y r (List.mem_cons_of_mem _ hr) p (List.mem_cons_self ..)
      refine ⟨b', ?_, ?_, ?_⟩
      · simp only [maskGate, LowerGateClass.evalL_seq, LowerGateClass.evalL_Toffoli_ket]
        exact he
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [hb'2 _ hnd.1, bit_toffoliBasis_clean c r.1 r.2 b hc1 hc2 hxy (hz r (List.mem_cons_self ..))]
        · rw [hb'1 r hr, hkeep c hc2, hkeep r.1 (hxne r hr)]
      · intro q hq
        have hq1 : q ∉ ps.map Prod.snd := fun m => hq (List.mem_cons_of_mem _ m)
        have hq2 : q ≠ p.2 := fun e => hq (by simp [e])
        rw [hb'2 q hq1, hkeep q hq2]

/-- `unmaskGate` undoes `maskGate` on every state (gate-by-gate inverse, no commutation needed). -/
theorem evalL_unmask_mask (c : ℕ) : ∀ (ps : List (ℕ × ℕ)) (ψ : qs.State),
    LowerGateClass.evalL (qs := qs) (unmaskGate c ps)
      (LowerGateClass.evalL (qs := qs) (maskGate c ps) ψ) = ψ
  | [], ψ => by simp [maskGate, unmaskGate, LowerGateClass.evalL_id]
  | p :: ps, ψ => by
      simp only [maskGate, unmaskGate, LowerGateClass.evalL_seq]
      rw [evalL_unmask_mask c ps, LowerGateClass.evalL_adj_apply]

end Mask


/-! ## Register level -/

section Reg

variable {Basis : Type*} [RegEncoding Basis]

/-- A register's value depends only on the bits of its own qubits. -/
theorem toNat_congr_bits (r : Reg) (b b' : Basis)
    (h : ∀ q ∈ r.qubits, RegEncoding.bit q b = RegEncoding.bit q b') :
    RegEncoding.toNat r b = RegEncoding.toNat r b' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < regSize r
  · have e1 := RegEncoding.bit_eq_testBit_toNat r b ⟨i, hi⟩
    have e2 := RegEncoding.bit_eq_testBit_toNat r b' ⟨i, hi⟩
    rw [← e1, ← e2]
    exact h _ (List.get_mem _ _)
  · have hb := RegEncoding.toNat_lt_ASize r b
    have hb' := RegEncoding.toNat_lt_ASize r b'
    rw [ASize] at hb hb'
    have hle : 2 ^ regSize r ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb hle),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb' hle)]

/-- If every bit of `Y` is `c ∧` the matching bit of `X`, then the value of `Y` is `c · ⟦X⟧`. -/
theorem toNat_mask (X Y : Reg) (hlen : X.width = Y.width) (c : Bool) (b b' : Basis)
    (h : ∀ i : Fin Y.width,
      RegEncoding.bit (Y.get i) b' =
        (c && RegEncoding.bit (X.get ⟨i.1, by have := i.2; omega⟩) b)) :
    RegEncoding.toNat Y b' = if c then RegEncoding.toNat X b else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hXlt := RegEncoding.toNat_lt_ASize X b
  have hYlt := RegEncoding.toNat_lt_ASize Y b'
  rw [ASize] at hXlt hYlt
  by_cases hi : i < Y.width
  · have hiX : i < X.width := by omega
    have e1 := RegEncoding.bit_eq_testBit_toNat Y b' ⟨i, hi⟩
    have e2 := RegEncoding.bit_eq_testBit_toNat X b ⟨i, hiX⟩
    have hh := h ⟨i, hi⟩
    have e1' : Nat.testBit (RegEncoding.toNat Y b') i = RegEncoding.bit (Y.get ⟨i, hi⟩) b' :=
      e1.symm
    rw [e1', hh]
    cases c
    · simp
    · simp only [Bool.true_and, ↓reduceIte]
      exact e2
  · have hle : 2 ^ regSize Y ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by unfold regSize; omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hYlt hle)]
    cases c
    · simp
    · have hle' : 2 ^ regSize X ≤ 2 ^ i :=
        Nat.pow_le_pow_right (by norm_num) (by unfold regSize; omega)
      simp [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hXlt hle')]

/-- Two's-complement masking: AND with a bit is multiplication by that bit. -/
theorem tcDecodeWidth_mask (w : ℕ) (c : Bool) (m : ℕ) :
    tcDecodeWidth w (if c then m else 0) = if c then tcDecodeWidth w m else 0 := by
  cases c
  · cases w <;> simp [tcDecodeWidth]
  · simp

end Reg


/-! ## Masking a register by the control -/

section CtlGate

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]


theorem mem_zip_fst {X Y : Reg} {p : ℕ × ℕ} (h : p ∈ X.qubits.zip Y.qubits) : p.1 ∈ X.qubits :=
  (List.of_mem_zip h).1

theorem mem_zip_snd {X Y : Reg} {p : ℕ × ℕ} (h : p ∈ X.qubits.zip Y.qubits) : p.2 ∈ Y.qubits :=
  (List.of_mem_zip h).2

theorem maskOK_reg {c : ℕ} {X Y : Reg} (hlen : X.width = Y.width)
    (hd : ∀ q ∈ X.qubits, q ∉ Y.qubits) (hcX : c ∉ X.qubits) (hcY : c ∉ Y.qubits) :
    MaskOK c (X.qubits.zip Y.qubits) where
  nodup := by
    have : (X.qubits.zip Y.qubits).map Prod.snd = Y.qubits := by
      rw [List.map_snd_zip]
      · simp only [Reg.width] at hlen; omega
    rw [this]; exact Y.nodup
  c_ne_x := fun p hp h => hcX (h ▸ mem_zip_fst hp)
  c_ne_y := fun p hp h => hcY (h ▸ mem_zip_snd hp)
  x_ne_y := fun p hp q hq h => hd _ (mem_zip_fst hp) (h ▸ mem_zip_snd hq)

theorem pair_mem_zip (X Y : Reg) (hlen : X.width = Y.width) (i : Fin Y.width) :
    (X.get ⟨i.1, by have := i.2; omega⟩, Y.get i) ∈ X.qubits.zip Y.qubits := by
  have hi : i.1 < (X.qubits.zip Y.qubits).length := by
    simp only [List.length_zip]; have := i.2; simp only [Reg.width] at hlen this; omega
  refine List.mem_iff_getElem.mpr ⟨i.1, hi, ?_⟩
  simp [List.getElem_zip, Reg.get]

/-- **Register mask.** From a state with `Y` zero, the mask yields a basis state whose `Y` holds
`c · ⟦X⟧` (as an unsigned value) and which agrees with the input off `Y`. -/
theorem evalL_maskReg_ket {c : ℕ} {X Y : Reg} (hlen : X.width = Y.width)
    (hd : ∀ q ∈ X.qubits, q ∉ Y.qubits) (hcX : c ∉ X.qubits) (hcY : c ∉ Y.qubits)
    (b : qs.Basis) (hz : ∀ q ∈ Y.qubits, RegEncoding.bit q b = false) :
    ∃ b' : qs.Basis, LowerGateClass.evalL (qs := qs) (maskReg c X Y) (qs.ket b) = qs.ket b' ∧
      RegEncoding.toNat Y b' = (if RegEncoding.bit c b then RegEncoding.toNat X b else 0) ∧
      (∀ q, q ∉ Y.qubits → RegEncoding.bit q b' = RegEncoding.bit q b) := by
  obtain ⟨b', he, h1, h2⟩ := evalL_maskGate_ket (qs := qs) c _ (maskOK_reg hlen hd hcX hcY) b
    (fun p hp => hz _ (mem_zip_snd hp))
  refine ⟨b', he, ?_, ?_⟩
  · apply toNat_mask X Y hlen _ b b'
    intro i
    exact h1 _ (pair_mem_zip X Y hlen i)
  · intro q hq
    apply h2
    intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    exact hq (mem_zip_snd hp)



/-- **Generic control by masking.** If `G` acts as the scalar `Φ b₁` on every state `b₁` where `Y`
holds `c · ⟦X⟧` and the rest agrees with `b`, then the controlled gate maps `|b⟩` to `Φ b₁ |b⟩`
for that `b₁` (and the mask is undone). -/
theorem evalL_ctlGate_ket {c : ℕ} {X Y : Reg} (hlen : X.width = Y.width)
    (hd : ∀ q ∈ X.qubits, q ∉ Y.qubits) (hcX : c ∉ X.qubits) (hcY : c ∉ Y.qubits)
    (G : LowGate) (b : qs.Basis) (hz : ∀ q ∈ Y.qubits, RegEncoding.bit q b = false)
    (Φ : qs.Basis → ℂ)
    (hG : ∀ b₁ : qs.Basis, (∀ q, q ∉ Y.qubits → RegEncoding.bit q b₁ = RegEncoding.bit q b) →
      RegEncoding.toNat Y b₁ = (if RegEncoding.bit c b then RegEncoding.toNat X b else 0) →
      LowerGateClass.evalL (qs := qs) G (qs.ket b₁) = Φ b₁ • qs.ket b₁) :
    ∃ b₁ : qs.Basis, (∀ q, q ∉ Y.qubits → RegEncoding.bit q b₁ = RegEncoding.bit q b) ∧
      RegEncoding.toNat Y b₁ = (if RegEncoding.bit c b then RegEncoding.toNat X b else 0) ∧
      LowerGateClass.evalL (qs := qs) (ctlGate c X Y G) (qs.ket b) = Φ b₁ • qs.ket b := by
  obtain ⟨b₁, hm, hv, hk⟩ := evalL_maskReg_ket (qs := qs) hlen hd hcX hcY b hz
  refine ⟨b₁, hk, hv, ?_⟩
  unfold ctlGate
  rw [LowerGateClass.evalL_seq, LowerGateClass.evalL_seq, hm, hG b₁ hk hv,
    LowerGateClass.evalL_smul]
  congr 1
  rw [← hm]
  exact evalL_unmask_mask (qs := qs) c (X.qubits.zip Y.qubits) (qs.ket b)

end CtlGate


/-! ## The controlled PTP specification and correctness -/



theorem fitsSignedWidth_zero {n : ℕ} (h : 0 < n) : FitsSignedWidth n 0 := by
  refine ⟨h, ?_, ?_⟩
  · unfold signedMin; simp
  · unfold signedMax; positivity

section CtlPTP

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

/-- **Controlled PTP from an uncontrolled circuit.** Let `G` meet the uncontrolled PTP contract on
`(Y, X₁, X₂)` (`hGu`). Then `ctlGate c X₀ Y G` multiplies `|b⟩` by the controlled eigenphase of
`(X₀, X₁, X₂)` whenever the operands fit, `Y` and the workspace `W` are zero. -/
theorem evalL_ctl_ptp_ket {c n : ℕ} {X : Fin 3 → ExtReg} {Y : ExtReg} {W : List ℕ} {φ : Angle}
    {G : LowGate} (hn : ∀ s, (X s).width = n) (hY : Y.width = n)
    (hdisj : ∀ s, ∀ q ∈ (X s).active.qubits, q ∉ Y.active.qubits)
    (hcX : c ∉ (X 0).active.qubits) (hcY : c ∉ Y.active.qubits)
    (hW : ∀ q ∈ W, q ∉ Y.active.qubits)
    (hGu : ∀ b₁ : qs.Basis, (∀ s, FitsSignedWidth n (extToInt (Function.update X 0 Y s) b₁)) →
      (∀ q ∈ W, RegEncoding.bit q b₁ = false) →
      LowerGateClass.evalL (qs := qs) G (qs.ket b₁) =
        ptpEigenphase φ (Function.update X 0 Y) b₁ • qs.ket b₁)
    (b : qs.Basis) (hb : PTPCleanBasis qs X n (Y.active.qubits ++ W) b) :
    LowerGateClass.evalL (qs := qs) (ctlGate c (X 0).active Y.active G) (qs.ket b) =
      ptpCtlEigenphase φ c X b • qs.ket b := by
  have hz : ∀ q ∈ Y.active.qubits, RegEncoding.bit q b = false :=
    fun q hq => hb.2 q (List.mem_append_left _ hq)
  have hlen : (X 0).active.width = Y.active.width := by
    have h1 : (X 0).width = n := hn 0
    have h2 := hY
    simp only [ExtReg.width, regSize] at h1 h2; omega
  have hd0 : ∀ q ∈ (X 0).active.qubits, q ∉ Y.active.qubits := hdisj 0
  -- the value facts about the masked state, for any state agreeing with the mask output
  set Φ : qs.Basis → ℂ := fun b₁ => ptpEigenphase φ (Function.update X 0 Y) b₁ with hΦ
  have key : ∀ b₁ : qs.Basis, (∀ q, q ∉ Y.active.qubits → RegEncoding.bit q b₁ = RegEncoding.bit q b) →
      RegEncoding.toNat Y.active b₁ =
        (if RegEncoding.bit c b then RegEncoding.toNat (X 0).active b else 0) →
      extToInt Y b₁ = (if RegEncoding.bit c b then extToInt (X 0) b else 0) ∧
      (∀ s : Fin 3, s ≠ 0 → extToInt (X s) b₁ = extToInt (X s) b) := by
    intro b₁ hag hv
    refine ⟨?_, ?_⟩
    · have h0 : (X 0).width = Y.width := by rw [hn 0, hY]
      unfold extToInt ExtReg.toNat
      rw [hv, ← h0]
      exact tcDecodeWidth_mask _ _ _
    · intro s _
      unfold extToInt ExtReg.toNat
      rw [toNat_congr_bits (X s).active b₁ b (fun q hq => hag q (hdisj s q hq))]
  have hG : ∀ b₁ : qs.Basis,
      (∀ q, q ∉ Y.active.qubits → RegEncoding.bit q b₁ = RegEncoding.bit q b) →
      RegEncoding.toNat Y.active b₁ =
        (if RegEncoding.bit c b then RegEncoding.toNat (X 0).active b else 0) →
      LowerGateClass.evalL (qs := qs) G (qs.ket b₁) = Φ b₁ • qs.ket b₁ := by
    intro b₁ hag hv
    obtain ⟨k0, ks⟩ := key b₁ hag hv
    apply hGu b₁
    · intro s
      fin_cases s
      · simp only [Fin.zero_eta, Function.update_self]
        rw [k0]
        by_cases hc : RegEncoding.bit c b
        · simp only [hc, ↓reduceIte]; exact hb.1 0
        · simp only [hc]; exact fitsSignedWidth_zero (hb.1 0).1
      · have : (Function.update X 0 Y) 1 = X 1 := Function.update_of_ne (by decide) _ _
        simp only [Fin.mk_one, this]
        rw [ks 1 (by decide)]; exact hb.1 1
      · have : (Function.update X 0 Y) 2 = X 2 := Function.update_of_ne (by decide) _ _
        simp only [Fin.reduceFinMk, this]
        rw [ks 2 (by decide)]; exact hb.1 2
    · intro q hq
      rw [hag q (hW q hq)]
      exact hb.2 q (List.mem_append_right _ hq)
  obtain ⟨b₁, hag, hv, he⟩ := evalL_ctlGate_ket (qs := qs) hlen hd0 hcX hcY G b hz Φ hG
  rw [he]
  congr 1
  obtain ⟨k0, ks⟩ := key b₁ hag hv
  have e1 : (Function.update X 0 Y) 1 = X 1 := Function.update_of_ne (by decide) _ _
  have e2 : (Function.update X 0 Y) 2 = X 2 := Function.update_of_ne (by decide) _ _
  simp only [hΦ, ptpEigenphase, ptpCtlEigenphase, Function.update_self, e1, e2, k0,
    ks 1 (by decide), ks 2 (by decide)]
  by_cases hc : RegEncoding.bit c b
  · simp [hc]
  · simp [hc]

/-- **State-level controlled PTP.** -/
theorem evalL_ctl_ptp_state {c n : ℕ} {X : Fin 3 → ExtReg} {Y : ExtReg} {W : List ℕ} {φ : Angle}
    {G : LowGate} (hn : ∀ s, (X s).width = n) (hY : Y.width = n)
    (hdisj : ∀ s, ∀ q ∈ (X s).active.qubits, q ∉ Y.active.qubits)
    (hcX : c ∉ (X 0).active.qubits) (hcY : c ∉ Y.active.qubits)
    (hW : ∀ q ∈ W, q ∉ Y.active.qubits)
    (hGu : ∀ b₁ : qs.Basis, (∀ s, FitsSignedWidth n (extToInt (Function.update X 0 Y s) b₁)) →
      (∀ q ∈ W, RegEncoding.bit q b₁ = false) →
      LowerGateClass.evalL (qs := qs) G (qs.ket b₁) =
        ptpEigenphase φ (Function.update X 0 Y) b₁ • qs.ket b₁)
    (U : PTPCtlPhaseOp qs c X φ) {ψ : qs.State}
    (hψ : PTPCleanState qs X n (Y.active.qubits ++ W) ψ) :
    LowerGateClass.evalL (qs := qs) (ctlGate c (X 0).active Y.active G) ψ = U.op ψ := by
  have hU0 : U.op 0 = 0 := by
    have h := U.op_smul 0 (0 : qs.State); simpa using h
  exact evalL_eq_of_clean_kets U.op hU0 U.op_add U.op_smul
    (fun b hb => by
      rw [U.op_ket]
      exact evalL_ctl_ptp_ket hn hY hdisj hcX hcY hW hGu b hb) hψ

end CtlPTP


/-! ## Census of the mask -/

section Census

/-- The resources of `maskGate` / `unmaskGate`: `|ps|` Toffoli and nothing else. -/
theorem resources_maskGate (M : LowGateResourceModel) (c : ℕ) :
    ∀ ps : List (ℕ × ℕ),
      (LowGate.resources M (maskGate c ps)).toffoli = ps.length ∧
      (LowGate.resources M (maskGate c ps)).rz = 0 ∧ (LowGate.resources M (maskGate c ps)).cnot = 0 ∧
      (LowGate.resources M (maskGate c ps)).x = 0 ∧ (LowGate.resources M (maskGate c ps)).h = 0
  | [] => by simp [maskGate, LowGate.resources]
  | p :: ps => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := resources_maskGate M c ps
      simp [maskGate, LowGate.resources, GateResources.seq, h1, h2, h3, h4, h5]
      omega

theorem resources_unmaskGate (M : LowGateResourceModel) (c : ℕ) :
    ∀ ps : List (ℕ × ℕ),
      (LowGate.resources M (unmaskGate c ps)).toffoli = ps.length ∧
      (LowGate.resources M (unmaskGate c ps)).rz = 0 ∧
      (LowGate.resources M (unmaskGate c ps)).cnot = 0 ∧
      (LowGate.resources M (unmaskGate c ps)).x = 0 ∧ (LowGate.resources M (unmaskGate c ps)).h = 0
  | [] => by simp [unmaskGate, LowGate.resources]
  | p :: ps => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := resources_unmaskGate M c ps
      simp [unmaskGate, LowGate.resources, GateResources.seq, h1, h2, h3, h4, h5]

theorem adjToffCount_maskGate (c : ℕ) : ∀ ps : List (ℕ × ℕ), adjToffCount (maskGate c ps) = 0
  | [] => by simp [maskGate, adjToffCount]
  | p :: ps => by simp [maskGate, adjToffCount, adjToffCount_maskGate c ps]

/-- The uncomputation is `|ps|` `†Toffoli`: the And† count. -/
theorem adjToffCount_unmaskGate (c : ℕ) :
    ∀ ps : List (ℕ × ℕ), adjToffCount (unmaskGate c ps) = ps.length
  | [] => by simp [unmaskGate, adjToffCount]
  | p :: ps => by
      simp [unmaskGate, adjToffCount, adjToffCount_unmaskGate c ps]

theorem usedQubits_maskGate (c : ℕ) : ∀ (ps : List (ℕ × ℕ)) (q : ℕ),
    q ∈ LowGate.usedQubits (maskGate c ps) → q = c ∨ q ∈ ps.map Prod.fst ∨ q ∈ ps.map Prod.snd
  | [], q, h => by simp [maskGate, LowGate.usedQubits] at h
  | p :: ps, q, h => by
      simp only [maskGate, LowGate.usedQubits, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at h
      rcases h with (h | h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by simp [h]))
      · exact Or.inr (Or.inr (by simp [h]))
      · rcases usedQubits_maskGate c ps q h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (by simpa using h)))
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ (by simpa using h)))

theorem usedQubits_unmaskGate (c : ℕ) : ∀ (ps : List (ℕ × ℕ)) (q : ℕ),
    q ∈ LowGate.usedQubits (unmaskGate c ps) → q = c ∨ q ∈ ps.map Prod.fst ∨ q ∈ ps.map Prod.snd
  | [], q, h => by simp [unmaskGate, LowGate.usedQubits] at h
  | p :: ps, q, h => by
      simp only [unmaskGate, LowGate.usedQubits, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at h
      rcases h with h | (h | h | h)
      · rcases usedQubits_unmaskGate c ps q h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (by simpa using h)))
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ (by simpa using h)))
      · exact Or.inl h
      · exact Or.inr (Or.inl (by simp [h]))
      · exact Or.inr (Or.inr (by simp [h]))

end Census


/-! ## Exact-board controlled PTP (O3, masked form, clean subspace) -/

section Policy

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]



/-- **Main theorem: controlled PTP, exact board, state level, with census.** -/
theorem ptp_ctl_lowerExact_correct (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (Y : ExtReg)
    (c base : ℕ) : PTPCtlLowerExactCorrect qs P n X Y c base := by
  intro hP hn hG hdisj hcX hcY
  have e1 : (Function.update X 0 Y) 1 = X 1 := Function.update_of_ne (by decide) _ _
  have e2 : (Function.update X 0 Y) 2 = X 2 := Function.update_of_ne (by decide) _ _
  have hY : Y.width = n := by simpa using hG.1 0
  obtain ⟨W, G, hI, hB, _, hR⟩ := ptp_gate_full_exact (qs := qs) P hP n (Function.update X 0 Y)
    base hG
  have hYb : ∀ q ∈ Y.active.qubits, q < base := by
    intro q hq; simpa using hG.2.2 0 q (by simpa using hq)
  have hWY : ∀ q ∈ W, q ∉ Y.active.qubits := fun q hq hqY => by
    have := (hB q hq).1; have := hYb q hqY; omega
  have hlen : (X 0).active.qubits.length = n := by
    have := hn 0; simpa [ExtReg.width, regSize, Reg.width] using this
  have hlenY : Y.active.qubits.length = n := by
    simpa [ExtReg.width, regSize, Reg.width] using hY
  have hzip : ((X 0).active.qubits.zip Y.active.qubits).length = n := by
    simp [List.length_zip, hlen, hlenY]
  refine ⟨W, G, hI, hB, ?_, ?_⟩
  · intro φ U ψ hψ
    exact evalL_ctl_ptp_state hn hY hdisj hcX hcY hWY
      (fun b₁ hfit hclean => evalL_policyImplD_ket hP (admissible_exact P) hI φ b₁ hfit hclean)
      U hψ
  · intro φ
    obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := hR φ
    obtain ⟨m1, m2, m3, m4, m5⟩ := resources_maskGate shorGateResourceModel c
      ((X 0).active.qubits.zip Y.active.qubits)
    obtain ⟨u1, u2, u3, u4, u5⟩ := resources_unmaskGate shorGateResourceModel c
      ((X 0).active.qubits.zip Y.active.qubits)
    rw [hzip] at m1 u1
    have hA := adjToffCount_unmaskGate c ((X 0).active.qubits.zip Y.active.qubits)
    have hA0 := adjToffCount_maskGate c ((X 0).active.qubits.zip Y.active.qubits)
    rw [hzip] at hA
    have hAc : adjToffCount (ctlGate c (X 0).active Y.active (G φ)) =
        adjToffCount (maskGate c ((X 0).active.qubits.zip Y.active.qubits)) +
          (adjToffCount (G φ) +
            adjToffCount (unmaskGate c ((X 0).active.qubits.zip Y.active.qubits))) := by
      simp only [ctlGate, maskReg, unmaskReg, adjToffCount]
    have hRc : LowGate.resources shorGateResourceModel (ctlGate c (X 0).active Y.active (G φ)) =
        GateResources.seq
          (LowGate.resources shorGateResourceModel
            (maskGate c ((X 0).active.qubits.zip Y.active.qubits)))
          (GateResources.seq (LowGate.resources shorGateResourceModel (G φ))
            (LowGate.resources shorGateResourceModel
              (unmaskGate c ((X 0).active.qubits.zip Y.active.qubits)))) := by
      simp only [ctlGate, maskReg, unmaskReg, LowGate.resources]
    have hsub : LowGate.usedQubits (ctlGate c (X 0).active Y.active (G φ)) ⊆
        ((((X 0).active.qubits.toFinset ∪ Y.active.qubits.toFinset) ∪ (X 1).active.qubits.toFinset ∪
          (X 2).active.qubits.toFinset) ∪ Finset.Ico base (base + ptpWorkspaceX P n)) ∪ {c} := by
      intro q hq
      simp only [ctlGate, maskReg, unmaskReg, LowGate.usedQubits, Finset.mem_union] at hq
      simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_singleton, Finset.mem_Ico]
      rcases hq with hm | hg | hu
      · rcases usedQubits_maskGate c _ q hm with h | h | h
        · exact Or.inr h
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (mem_zip_fst hp)))))
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mem_zip_snd hp)))))
      · rcases hI.usedQubits φ q hg with ⟨s, hs⟩ | hw
        · refine Or.inl ?_
          fin_cases s
          · simp only [Fin.zero_eta, Function.update_self] at hs
            exact Or.inl (Or.inl (Or.inl (Or.inr hs)))
          · simp only [Fin.mk_one, e1] at hs
            exact Or.inl (Or.inl (Or.inr hs))
          · simp only [Fin.reduceFinMk, e2] at hs
            exact Or.inl (Or.inr hs)
        · exact Or.inl (Or.inr (by have := hB q hw; omega))
      · rcases usedQubits_unmaskGate c _ q hu with h | h | h
        · exact Or.inr h
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (mem_zip_fst hp)))))
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mem_zip_snd hp)))))
    have hcard : ∀ (r : Reg), r.width = n → r.qubits.toFinset.card ≤ n := fun r hr =>
      (List.toFinset_card_le _).trans (le_of_eq hr)
    have hw0 : (X 0).active.width = n := by simpa [ExtReg.width, regSize] using hn 0
    have hw1 : (X 1).active.width = n := by simpa [ExtReg.width, regSize] using hn 1
    have hw2 : (X 2).active.width = n := by simpa [ExtReg.width, regSize] using hn 2
    have hwY : Y.active.width = n := by simpa [ExtReg.width, regSize] using hY
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hRc]; simp only [GateResources.seq]; omega
    · rw [hRc]; simp only [GateResources.seq]; omega
    · rw [hRc]; simp only [GateResources.seq]; omega
    · rw [hRc]; simp only [GateResources.seq]; omega
    · rw [hRc]; simp only [GateResources.seq]; omega
    · rw [hAc]; omega
    · have hc := Finset.card_le_card hsub
      have hI : (Finset.Ico base (base + ptpWorkspaceX P n)).card ≤ ptpWorkspaceX P n := by simp
      have hS : ({c} : Finset ℕ).card ≤ 1 := by simp
      have h1 := hcard _ hw0
      have h2 := hcard _ hwY
      have h3 := hcard _ hw1
      have h4 := hcard _ hw2
      have s1 := Finset.card_union_le
        ((((X 0).active.qubits.toFinset ∪ Y.active.qubits.toFinset) ∪ (X 1).active.qubits.toFinset ∪
          (X 2).active.qubits.toFinset) ∪ Finset.Ico base (base + ptpWorkspaceX P n)) ({c} : Finset ℕ)
      have s2 := Finset.card_union_le
        (((X 0).active.qubits.toFinset ∪ Y.active.qubits.toFinset) ∪ (X 1).active.qubits.toFinset ∪
          (X 2).active.qubits.toFinset) (Finset.Ico base (base + ptpWorkspaceX P n))
      have s3 := Finset.card_union_le
        (((X 0).active.qubits.toFinset ∪ Y.active.qubits.toFinset) ∪ (X 1).active.qubits.toFinset)
        (X 2).active.qubits.toFinset
      have s4 := Finset.card_union_le ((X 0).active.qubits.toFinset ∪ Y.active.qubits.toFinset)
        (X 1).active.qubits.toFinset
      have s5 := Finset.card_union_le (X 0).active.qubits.toFinset Y.active.qubits.toFinset
      omega

end Policy

end PTP
end Shor
