import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Recursion.Census
/-!
# O2: a PTP node meets the child contract, so gate-level correctness recurses

* Register arithmetic: chunk `j` of a two's-complement register is the floor limb
  (`tcDecode_lower_chunk`, `tcDecode_top_chunk`).
* `SplitLayout`: the in-place split of three parent registers into child slots
  (ForShor `PhaseSplitLayout`, three operands), zero-extension of lower chunks,
  sign-extension of the top chunk (`alloc`, `slot_value`); undone by `† alloc`.
* `SpecOn`: a register-level phase contract with explicit workspace; the sandwich leaf
  meets it (`specOn_leafSandwich`), and a node over children that meet it meets it
  (`specOn_ptpSubNode`: "a PTP node satisfies `ChildSpec` given a clean reserve").
* `PolicyImpl`: gate-level recursions following a policy; correct (`PolicyImpl.specOn`)
  and with census `ptpResources` (Rz/Toffoli/X/H, `PolicyImpl.resources`) at every depth.
  Existence for every checked policy and width: `Build.lean`; CNOT/And†: `CensusFull.lean`.
-/

namespace Shor
namespace PTP

open Shor

/-! ## Register arithmetic: chunks of a two's-complement register -/

section Chunks

variable {Basis : Type*} [RegEncoding Basis]

theorem take_drop_disjoint (r : Reg) (a : ℕ) : Disjoint (r.take a) (r.drop a) := by
  have hn : (r.qubits.take a ++ r.qubits.drop a).Nodup := by
    rw [List.take_append_drop]; exact r.nodup
  intro x hx hy
  exact (List.nodup_append.mp hn).2.2 x hx x hy rfl

theorem reg_take_append_drop (r : Reg) (a : ℕ) :
    Reg.append (r.take a) (r.drop a) (take_drop_disjoint r a) = r := by
  cases r with
  | mk qs hq => simp [Reg.append, Reg.take, Reg.drop]

theorem regSize_take (r : Reg) {a : ℕ} (ha : a ≤ regSize r) : regSize (r.take a) = a := by
  simp only [regSize, Reg.width, Reg.take, List.length_take] at ha ⊢
  omega

theorem regSize_drop (r : Reg) (a : ℕ) : regSize (r.drop a) = regSize r - a := by
  simp [regSize, Reg.width, Reg.drop]

/-- `toNat r = toNat (take a) + 2^a · toNat (drop a)`. -/
theorem toNat_take_drop (r : Reg) {a : ℕ} (ha : a ≤ regSize r) (b : Basis) :
    RegEncoding.toNat r b =
      RegEncoding.toNat (r.take a) b + 2 ^ a * RegEncoding.toNat (r.drop a) b := by
  have h := RegEncoding.toNat_append (r.take a) (r.drop a) (take_drop_disjoint r a) b
  rw [reg_take_append_drop] at h
  rw [h, ASize, regSize_take r ha]

theorem toNat_take_lt (r : Reg) {a : ℕ} (ha : a ≤ regSize r) (b : Basis) :
    RegEncoding.toNat (r.take a) b < 2 ^ a := by
  have := RegEncoding.toNat_lt_ASize (r.take a) b
  rwa [ASize, regSize_take r ha] at this

/-- A lower chunk is the unsigned bit field `[a, a + L)`. -/
theorem toNat_chunk (r : Reg) {a L : ℕ} (h : a + L ≤ regSize r) (b : Basis) :
    RegEncoding.toNat ((r.drop a).take L) b = RegEncoding.toNat r b / 2 ^ a % 2 ^ L := by
  have h1 := toNat_take_drop r (a := a) (by omega) b
  have hlo := toNat_take_lt r (a := a) (by omega) b
  have hdiv : RegEncoding.toNat r b / 2 ^ a = RegEncoding.toNat (r.drop a) b := by
    rw [h1, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlo, zero_add]
  have hL : L ≤ regSize (r.drop a) := by rw [regSize_drop]; omega
  have h2 := toNat_take_drop (r.drop a) hL b
  have hlo2 := toNat_take_lt (r.drop a) hL b
  rw [hdiv, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo2]

/-- Two's-complement decoding of a value split at bit `m`. -/
theorem tcDecodeWidth_split {m w lo hi : ℕ} (hw : 0 < w) (hlo : lo < 2 ^ m) (hhi : hi < 2 ^ w) :
    tcDecodeWidth (m + w) (lo + 2 ^ m * hi) = (lo : ℤ) + 2 ^ m * tcDecodeWidth w hi := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  rw [show m + (w' + 1) = (m + w') + 1 by omega]
  simp only [tcDecodeWidth]
  have hpm : (0 : ℕ) < 2 ^ m := by positivity
  by_cases hh : hi < 2 ^ w'
  · have : lo + 2 ^ m * hi < 2 ^ (m + w') := by
      rw [pow_add]
      calc lo + 2 ^ m * hi < 2 ^ m + 2 ^ m * hi := by omega
        _ = 2 ^ m * (hi + 1) := by ring
        _ ≤ 2 ^ m * 2 ^ w' := Nat.mul_le_mul_left _ hh
    simp only [this, hh, ↓reduceDIte]
    push_cast; ring
  · have : ¬ lo + 2 ^ m * hi < 2 ^ (m + w') := by
      rw [pow_add]; push Not at hh ⊢
      calc 2 ^ m * 2 ^ w' ≤ 2 ^ m * hi := Nat.mul_le_mul_left _ hh
        _ ≤ lo + 2 ^ m * hi := Nat.le_add_left _ _
    simp only [this, hh, ↓reduceDIte]
    push_cast; ring

/-- The top chunk of a two's-complement register is the arithmetic shift of its value. -/
theorem tcDecode_top_chunk (r : Reg) {m : ℕ} (h : m < regSize r) (b : Basis) :
    tcDecodeWidth (regSize r - m) (RegEncoding.toNat (r.drop m) b) =
      tcDecodeWidth (regSize r) (RegEncoding.toNat r b) / 2 ^ m := by
  have h1 := toNat_take_drop r (a := m) (by omega) b
  have hlo := toNat_take_lt r (a := m) (by omega) b
  have hhi := RegEncoding.toNat_lt_ASize (r.drop m) b
  rw [ASize, regSize_drop] at hhi
  rw [h1, show regSize r = m + (regSize r - m) by omega,
    tcDecodeWidth_split (by omega) hlo hhi]
  rw [show m + (regSize r - m) - m = regSize r - m by omega]
  rw [Int.add_mul_ediv_left _ _ (by positivity),
    Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hlo), zero_add]

/-- A lower chunk of a two's-complement register is the floor-limb of its value. -/
theorem tcDecode_lower_chunk (r : Reg) {a L : ℕ} (h : a + L ≤ regSize r) (b : Basis) :
    ((RegEncoding.toNat ((r.drop a).take L) b : ℕ) : ℤ) =
      tcDecodeWidth (regSize r) (RegEncoding.toNat r b) / 2 ^ a % 2 ^ L := by
  rw [toNat_chunk r h b]
  set raw := RegEncoding.toNat r b
  have hraw : raw < 2 ^ regSize r := RegEncoding.toNat_lt_ASize r b
  have key : ∀ C : ℕ, 0 < L → a + L ≤ C → raw < 2 ^ C →
      tcDecodeWidth C raw / 2 ^ a % 2 ^ L = ((raw / 2 ^ a % 2 ^ L : ℕ) : ℤ) := by
    intro C hL hC hr
    obtain ⟨C', rfl⟩ : ∃ C', C = C' + 1 := ⟨C - 1, by omega⟩
    simp only [tcDecodeWidth]
    split
    · push_cast; rfl
    · push_cast
      have hsplit : ((2 : ℤ) ^ (C' + 1)) = 2 ^ a * (2 ^ L * 2 ^ (C' + 1 - a - L)) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [sub_eq_add_neg, hsplit, show -(2 ^ a * (2 ^ L * 2 ^ (C' + 1 - a - L)) : ℤ) =
          (-(2 ^ L * 2 ^ (C' + 1 - a - L))) * 2 ^ a by ring,
        Int.add_mul_ediv_right _ _ (by positivity),
        show -(2 ^ L * 2 ^ (C' + 1 - a - L) : ℤ) = 2 ^ L * (-(2 ^ (C' + 1 - a - L))) by ring,
        Int.add_mul_emod_self_left]
  rcases Nat.eq_zero_or_pos L with hL0 | hL
  · subst hL0; simp
  · exact (key _ hL h hraw).symm

end Chunks


/-! ## Bit-level frame facts -/

section Frame

variable {Basis : Type*} [RegEncoding Basis]

/-- A register's value is determined by its own qubits. -/
theorem toNat_congr (r : Reg) {b b' : Basis}
    (h : ∀ q ∈ r.qubits, RegEncoding.bit q b = RegEncoding.bit q b') :
    RegEncoding.toNat r b = RegEncoding.toNat r b' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < regSize r
  · have e1 := RegEncoding.bit_eq_testBit_toNat r b ⟨i, hi⟩
    have e2 := RegEncoding.bit_eq_testBit_toNat r b' ⟨i, hi⟩
    rw [← e1, ← e2]
    exact h _ (List.getElem_mem _)
  · push Not at hi
    have l1 := RegEncoding.toNat_lt_ASize r b
    have l2 := RegEncoding.toNat_lt_ASize r b'
    rw [ASize] at l1 l2
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le l1 (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le l2 (Nat.pow_le_pow_right (by norm_num) hi))]

theorem extToInt_congr (e : ExtReg) {b b' : Basis}
    (h : ∀ q ∈ e.active.qubits, RegEncoding.bit q b = RegEncoding.bit q b') :
    extToInt e b = extToInt e b' := by
  unfold extToInt ExtReg.toNat
  rw [toNat_congr e.active h]

/-- All qubits of `r` read `false`: `r` holds 0 (ForShor `FreshZero`). -/
theorem freshZero_of_bits (r : Reg) {b : Basis}
    (h : ∀ q ∈ r.qubits, RegEncoding.bit q b = false) : FreshZero r b := by
  unfold FreshZero
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  by_cases hi : i < regSize r
  · rw [← RegEncoding.bit_eq_testBit_toNat r b ⟨i, hi⟩]
    exact h _ (List.getElem_mem _)
  · push Not at hi
    have l1 := RegEncoding.toNat_lt_ASize r b
    rw [ASize] at l1
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le l1 (Nat.pow_le_pow_right (by norm_num) hi))

/-- Sign extension writes only the new bits. -/
theorem bit_signExtendBasis_out (r : ExtReg) (n : ℕ) (b : Basis) {q : ℕ}
    (hq : q ∉ (r.newBits n).qubits) :
    RegEncoding.bit q (signExtendBasis r n b) = RegEncoding.bit q b := by
  unfold signExtendBasis
  exact RegEncoding.bit_writeNat_out _ _ _ _ hq

/-- Sign extension into clean new bits keeps the signed value of the grown register. -/
theorem extToInt_grow_signExtendBasis (r : ExtReg) (n : ℕ) (b : Basis) (hcap : r.CanGrow n)
    (hfresh : r.FreshFor n b) :
    extToInt (r.grow n) (signExtendBasis r n b) = extToInt r b := by
  have hsz := Gate.ExtReg.newBits_size r n hcap
  unfold extToInt
  rw [Gate.ExtReg.toNat_grow, toNat_signExtendBasis, ExtReg.width_grow r n hcap]
  have hnew : RegEncoding.toNat (r.newBits n) (signExtendBasis r n b) =
      if tcDecodeWidth r.width (r.toNat b) < 0 then 2 ^ n - 1 else 0 := by
    rw [toNat_newBits_signExtendBasis, signExtendNewValue_of_fresh r n b hfresh]
    simp only [extToInt, ASize, hsz]
  rw [hnew]
  exact tcDecodeWidth_signExtend r.width n (r.toNat b) (ExtReg.toNat_lt r b)

end Frame

/-! ## The split of three parent registers into child slots -/



namespace SplitLayout

variable {X : Fin 3 → ExtReg} {k C' : ℕ} (SL : SplitLayout X k C')




theorem mem_R {s : Fin 3} {j : Fin k} {q : ℕ} (h : q ∈ ((SL.pre s j).newBits (SL.ext s j)).qubits) :
    q ∈ SL.R := by
  simp only [R, List.mem_flatMap, List.mem_finRange, true_and]
  exact ⟨s, j, h⟩

theorem newBits_sub_slot (s : Fin 3) (j : Fin k) {q : ℕ}
    (h : q ∈ ((SL.pre s j).newBits (SL.ext s j)).qubits) : q ∈ (SL.lay.slot s j).active.qubits := by
  simp only [lay, ExtReg.grow, Reg.append, List.mem_append]
  exact Or.inr h

theorem pre_sub_slot (s : Fin 3) (j : Fin k) {q : ℕ}
    (h : q ∈ (SL.pre s j).active.qubits) : q ∈ (SL.lay.slot s j).active.qubits := by
  simp only [lay, ExtReg.grow, Reg.append, List.mem_append]
  exact Or.inl h

/-- The reserve lies inside the child slots. -/
theorem R_sub_slots {q : ℕ} (h : q ∈ SL.R) : ∃ s j, q ∈ (SL.lay.slot s j).active.qubits := by
  simp only [R, List.mem_flatMap, List.mem_finRange, true_and] at h
  obtain ⟨s, j, hq⟩ := h
  exact ⟨s, j, SL.newBits_sub_slot s j hq⟩


/-- The basis map of the allocation. -/
noncomputable def allocBasis {Basis : Type*} [RegEncoding Basis] (b : Basis) : Basis :=
  signExtendBasis (SL.pre 2 SL.top) (SL.ext 2 SL.top)
    (signExtendBasis (SL.pre 1 SL.top) (SL.ext 1 SL.top)
      (signExtendBasis (SL.pre 0 SL.top) (SL.ext 0 SL.top) b))

theorem evalL_sequence_id {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (gs : List LowGate) (h : ∀ g ∈ gs, ∀ ψ, LowerGateClass.evalL (qs := qs) g ψ = ψ) (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.sequence gs) ψ = ψ := by
  induction gs generalizing ψ with
  | nil => exact LowerGateClass.evalL_id ψ
  | cons g gs ih =>
      simp only [LowGate.sequence]
      rw [LowerGateClass.evalL_seq, h g (by simp), ih (fun g' hg' => h g' (by simp [hg']))]

theorem evalL_alloc {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs] (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs) SL.alloc (qs.ket b) = qs.ket (SL.allocBasis b) := by
  unfold alloc allocBasis
  rw [LowerGateClass.evalL_seq, evalL_sequence_id]
  · rw [LowerGateClass.evalL_seq, LowerGateClass.evalL_signExtend_ket_total,
      LowerGateClass.evalL_seq, LowerGateClass.evalL_signExtend_ket_total,
      LowerGateClass.evalL_signExtend_ket_total]
  · intro g hg ψ
    simp only [List.mem_flatMap, List.mem_map] at hg
    obtain ⟨s, _, j, _, rfl⟩ := hg
    exact LowerGateClass.evalL_zeroExtend_id _ _ _

/-- The allocation changes only reserve qubits. -/
theorem bit_allocBasis_out {Basis : Type*} [RegEncoding Basis] (b : Basis) {q : ℕ} (hq : q ∉ SL.R) :
    RegEncoding.bit q (SL.allocBasis b) = RegEncoding.bit q b := by
  have h : ∀ s : Fin 3, q ∉ ((SL.pre s SL.top).newBits (SL.ext s SL.top)).qubits :=
    fun s hm => hq (SL.mem_R hm)
  unfold allocBasis
  rw [bit_signExtendBasis_out _ _ _ (h 2), bit_signExtendBasis_out _ _ _ (h 1),
    bit_signExtendBasis_out _ _ _ (h 0)]

end SplitLayout


namespace SplitLayout

variable {X : Fin 3 → ExtReg} {k C' : ℕ} (SL : SplitLayout X k C')

theorem not_mem_newBits {s : Fin 3} {j : Fin k} {s' : Fin 3} {j' : Fin k} (hne : (s, j) ≠ (s', j'))
    {q : ℕ} (hq : q ∈ (SL.lay.slot s j).active.qubits) :
    q ∉ ((SL.pre s' j').newBits (SL.ext s' j')).qubits := fun h =>
  (List.disjoint_left.mp (SL.disjoint s j s' j' hne)) hq (SL.newBits_sub_slot s' j' h)

theorem top_ne {s s' : Fin 3} (h : s ≠ s') : (s, SL.top) ≠ (s', SL.top) := fun e => h (Prod.mk.inj e).1

theorem fresh_of_clean {Basis : Type*} [RegEncoding Basis] {b : Basis}
    (hR : ∀ q ∈ SL.R, RegEncoding.bit q b = false) (s : Fin 3) (j : Fin k) :
    (SL.pre s j).FreshFor (SL.ext s j) b :=
  freshZero_of_bits _ fun q hq => hR q (SL.mem_R hq)

/-- After the allocation, a top slot holds the signed top chunk. -/
theorem top_value {Basis : Type*} [RegEncoding Basis] (b : Basis)
    (hR : ∀ q ∈ SL.R, RegEncoding.bit q b = false) (s : Fin 3) :
    extToInt (SL.lay.slot s SL.top) (SL.allocBasis b) = extToInt (SL.pre s SL.top) b := by
  have hcongr : ∀ (s₀ : Fin 3) (b₁ b₂ : Basis) (r : ExtReg) (n : ℕ),
      (∀ q ∈ (SL.lay.slot s₀ SL.top).active.qubits, q ∉ (r.newBits n).qubits) →
      b₁ = signExtendBasis r n b₂ →
      extToInt (SL.lay.slot s₀ SL.top) b₁ = extToInt (SL.lay.slot s₀ SL.top) b₂ := by
    intro s₀ b₁ b₂ r n hd e
    subst e
    exact extToInt_congr _ fun q hq => bit_signExtendBasis_out _ _ _ (hd q hq)
  have hpre : ∀ (s₀ : Fin 3) (b₁ b₂ : Basis) (r : ExtReg) (n : ℕ),
      (∀ q ∈ (SL.pre s₀ SL.top).active.qubits, q ∉ (r.newBits n).qubits) →
      b₁ = signExtendBasis r n b₂ →
      extToInt (SL.pre s₀ SL.top) b₁ = extToInt (SL.pre s₀ SL.top) b₂ := by
    intro s₀ b₁ b₂ r n hd e
    subst e
    exact extToInt_congr _ fun q hq => bit_signExtendBasis_out _ _ _ (hd q hq)
  have hfresh : ∀ (s₀ : Fin 3) (b₁ b₂ : Basis) (r : ExtReg) (n : ℕ),
      (∀ q ∈ ((SL.pre s₀ SL.top).newBits (SL.ext s₀ SL.top)).qubits, q ∉ (r.newBits n).qubits) →
      b₁ = signExtendBasis r n b₂ → (SL.pre s₀ SL.top).FreshFor (SL.ext s₀ SL.top) b₂ →
      (SL.pre s₀ SL.top).FreshFor (SL.ext s₀ SL.top) b₁ := by
    intro s₀ b₁ b₂ r n hd e hf
    subst e
    unfold ExtReg.FreshFor FreshZero at hf ⊢
    rw [← hf]
    exact toNat_congr _ fun q hq => bit_signExtendBasis_out _ _ _ (hd q hq)
  have sl : ∀ {s₀ s₁ : Fin 3}, s₀ ≠ s₁ → ∀ q ∈ (SL.lay.slot s₀ SL.top).active.qubits,
      q ∉ ((SL.pre s₁ SL.top).newBits (SL.ext s₁ SL.top)).qubits :=
    fun h q hq => SL.not_mem_newBits (SL.top_ne h) hq
  have pr : ∀ {s₀ s₁ : Fin 3}, s₀ ≠ s₁ → ∀ q ∈ (SL.pre s₀ SL.top).active.qubits,
      q ∉ ((SL.pre s₁ SL.top).newBits (SL.ext s₁ SL.top)).qubits :=
    fun h q hq => SL.not_mem_newBits (SL.top_ne h) (SL.pre_sub_slot _ _ hq)
  have nb : ∀ {s₀ s₁ : Fin 3}, s₀ ≠ s₁ → ∀ q ∈ ((SL.pre s₀ SL.top).newBits (SL.ext s₀ SL.top)).qubits,
      q ∉ ((SL.pre s₁ SL.top).newBits (SL.ext s₁ SL.top)).qubits :=
    fun h q hq => SL.not_mem_newBits (SL.top_ne h) (SL.newBits_sub_slot _ _ hq)
  have f0 := SL.fresh_of_clean hR
  set e0 := signExtendBasis (SL.pre 0 SL.top) (SL.ext 0 SL.top) b with he0
  set e1 := signExtendBasis (SL.pre 1 SL.top) (SL.ext 1 SL.top) e0 with he1
  have hab : SL.allocBasis b = signExtendBasis (SL.pre 2 SL.top) (SL.ext 2 SL.top) e1 := rfl
  fin_cases s
  · show extToInt (SL.lay.slot 0 SL.top) (SL.allocBasis b) = extToInt (SL.pre 0 SL.top) b
    rw [hcongr 0 _ _ _ _ (sl (by decide)) hab, hcongr 0 _ _ _ _ (sl (by decide)) he1]
    exact extToInt_grow_signExtendBasis _ _ _ (SL.can_grow 0 SL.top) (f0 0 SL.top)
  · show extToInt (SL.lay.slot 1 SL.top) (SL.allocBasis b) = extToInt (SL.pre 1 SL.top) b
    rw [hcongr 1 _ _ _ _ (sl (by decide)) hab]
    rw [show extToInt (SL.lay.slot 1 SL.top) e1 = extToInt (SL.pre 1 SL.top) e0 from
      extToInt_grow_signExtendBasis _ _ _ (SL.can_grow 1 SL.top)
        (hfresh 1 _ _ _ _ (nb (by decide)) he0 (f0 1 SL.top))]
    exact hpre 1 _ _ _ _ (pr (by decide)) he0
  · show extToInt (SL.lay.slot 2 SL.top) (SL.allocBasis b) = extToInt (SL.pre 2 SL.top) b
    rw [show extToInt (SL.lay.slot 2 SL.top) (SL.allocBasis b) = extToInt (SL.pre 2 SL.top) e1 from
      extToInt_grow_signExtendBasis _ _ _ (SL.can_grow 2 SL.top)
        (hfresh 2 _ _ _ _ (nb (by decide)) he1 (hfresh 2 _ _ _ _ (nb (by decide)) he0 (f0 2 SL.top)))]
    rw [hpre 2 _ _ _ _ (pr (by decide)) he1, hpre 2 _ _ _ _ (pr (by decide)) he0]

/-- After the allocation, a lower slot holds the unsigned lower chunk. -/
theorem lower_value {Basis : Type*} [RegEncoding Basis] (b : Basis)
    (hR : ∀ q ∈ SL.R, RegEncoding.bit q b = false) (s : Fin 3) (j : Fin k) (hj : (j : ℕ) + 1 ≠ k) :
    extToInt (SL.lay.slot s j) (SL.allocBasis b) = (ExtReg.toNat (SL.pre s j) b : ℤ) := by
  have hne : ∀ s', (s, j) ≠ (s', SL.top) := fun s' e => hj (by
    have := congrArg (fun p => (p.2 : ℕ)) e
    simp only [top] at this
    have := SL.two_le
    omega)
  rw [show extToInt (SL.lay.slot s j) (SL.allocBasis b) = extToInt (SL.lay.slot s j) b from
    extToInt_congr _ fun q hq => by
      unfold allocBasis
      rw [bit_signExtendBasis_out _ _ _ (SL.not_mem_newBits (hne 2) hq),
        bit_signExtendBasis_out _ _ _ (SL.not_mem_newBits (hne 1) hq),
        bit_signExtendBasis_out _ _ _ (SL.not_mem_newBits (hne 0) hq)]]
  exact Gate.ExtReg.extToInt_grow_of_fresh _ _ _ (SL.can_grow s j) (SL.fresh_of_clean hR s j)
    (SL.ext_pos s j hj)

/-- **Allocation correctness**: on a state with clean reserve, after the allocation child
slot `(s, j)` holds floor-limb `j` of `⟦X s⟧` at lower width `C / k`. -/
theorem slot_value {Basis : Type*} [RegEncoding Basis] {C : ℕ} (hX : ∀ s, (X s).width = C)
    (hC : 0 < C) (b : Basis) (hR : ∀ q ∈ SL.R, RegEncoding.bit q b = false) (s : Fin 3) (j : Fin k) :
    extToInt (SL.lay.slot s j) (SL.allocBasis b) = limbsAt k (limbWidth C k) (extToInt (X s) b) j := by
  have hk := SL.two_le
  have hLw : limbWidth C k = C / k := by simp [limbWidth, limbWidth3]
  have hXs : regSize (X s).active = C := hX s
  have hkL : k * (C / k) ≤ C := Nat.mul_div_le C k
  unfold limbsAt limbs
  rw [hLw, ← pow_mul]
  have hpre := SL.pre_active s j
  rw [hX s] at hpre
  by_cases hj : (j : ℕ) + 1 = k
  · simp only [hj, ↓reduceIte]
    have hjt : j = SL.top := Fin.ext (by simp only [top]; omega)
    subst hjt
    rw [SL.top_value b hR s]
    unfold extToInt ExtReg.toNat ExtReg.width
    rw [hpre]
    simp only [chunkReg, hj, ↓reduceIte]
    rw [regSize_drop, hXs]
    have hlt : (k - 1) * (C / k) < regSize (X s).active := by
      rw [hXs]
      rcases Nat.eq_zero_or_pos (C / k) with h0 | h0
      · rw [h0]; omega
      · have : (k - 1) * (C / k) < k * (C / k) := Nat.mul_lt_mul_of_pos_right (by omega) h0
        omega
    have := tcDecode_top_chunk (X s).active hlt b
    rw [hXs] at this
    simp only [top] at this ⊢
    rw [this, mul_comm]
  · simp only [hj, ↓reduceIte]; rw [SL.lower_value b hR s j hj]
    unfold ExtReg.toNat
    rw [hpre]
    simp only [chunkReg, hj, ↓reduceIte]
    have hle : (j : ℕ) * (C / k) + C / k ≤ regSize (X s).active := by
      rw [hXs]
      have : ((j : ℕ) + 1) * (C / k) ≤ k * (C / k) :=
        Nat.mul_le_mul_right _ (by have := j.2; omega)
      nlinarith
    rw [tcDecode_lower_chunk (X s).active hle b, hXs, mul_comm]
    unfold extToInt ExtReg.toNat
    rw [hX s]

end SplitLayout


/-! ## The register-level contract `SpecOn` -/

/-- **`g` implements the PTP phase `θ` on the registers `X` at width `C`, with workspace
`W`**: on every basis state whose three registers fit signed `C` bits and whose workspace
qubits are `|0⟩`, `g` multiplies by `exp(i π θ ⟦X 0⟧⟦X 1⟧⟦X 2⟧)` and returns the state. -/
def SpecOn {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (X : Fin 3 → ExtReg) (C : ℕ) (W : List ℕ) (θ : Angle) (g : LowGate) : Prop :=
  ∀ b : qs.Basis, (∀ s, FitsSignedWidth C (extToInt (X s) b)) →
    (∀ q ∈ W, RegEncoding.bit q b = false) →
    LowerGateClass.evalL (qs := qs) g (qs.ket b) =
      Complex.exp (((Angle.toReal (θ * (extToInt (X 0) b : ℚ) * (extToInt (X 1) b : ℚ) *
        (extToInt (X 2) b : ℚ)) : ℝ) : ℂ) * Complex.I) • qs.ket b

section Spec

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

theorem SpecOn.mono {X : Fin 3 → ExtReg} {C : ℕ} {W W' : List ℕ} {θ : Angle} {g : LowGate}
    (h : SpecOn (qs := qs) X C W θ g) (hW : ∀ q ∈ W, q ∈ W') : SpecOn (qs := qs) X C W' θ g :=
  fun b hfit hcl => h b hfit fun q hq => hcl q (hW q hq)

/-- `SpecOn` children give `ChildSpec`, when their workspace is off the slots and clean in
the reference state. -/
theorem childSpec_of_specOn {k : ℕ} (Lay : NodeLayout k) (θ : ℕ → ℚ) (b0 : qs.Basis)
    (child : ℕ → Fin k → LowGate) (W : List ℕ)
    (hW : ∀ q ∈ W, ∀ s j, q ∉ (Lay.slot s j).active.qubits)
    (h0 : ∀ q ∈ W, RegEncoding.bit q b0 = false)
    (h : ∀ t i, SpecOn (qs := qs) (fun s => Lay.slot s i) Lay.width W (θ t) (child t i)) :
    ChildSpec Lay θ b0 child := by
  intro t i b hfit hoff
  exact h t i b hfit fun q hq => (hoff q (hW q hq)).trans (h0 q hq)

/-- The sandwich leaf meets `SpecOn` with workspace `[t, u]`. -/
theorem specOn_leafSandwich (X : Fin 3 → ExtReg) (C : ℕ) (t u : ℕ)
    (hD : LeafActiveDisjoint (X 0) (X 1) (X 2)) (hA : SandwichAnc (X 0) (X 1) (X 2) t u)
    (θ : Angle) : SpecOn (qs := qs) X C [t, u] θ (ptpLeafSandwich θ (X 0) (X 1) (X 2) t u) := by
  intro b _ hcl
  rw [evalL_ptpLeafSandwich_ket θ _ _ _ t u b hD hA ⟨hcl t (by simp), hcl u (by simp)⟩]
  congr 2
  simp only [Angle.toReal]
  push_cast
  ring


/-- **O2 step: a PTP node meets the child contract given a clean reserve.** If `T` passes
the PTP contract, the split layout `SL` of the parent registers `X` (width `C > 0`) has
child width `C' ≥ childWidth C T.ops`, and every child `gc t j` meets `SpecOn` on child
slot triple `j` at width `C'` with angle `θ · cₜ` and a workspace `W'` that is off all
child slots, then the node meets `SpecOn` on `X` at width `C` with workspace `R ++ W'`
(`R` = the level's extension qubits). -/
theorem specOn_ptpSubNode {X : Fin 3 → ExtReg} {C C' : ℕ} (hX : ∀ s, (X s).width = C)
    (hC : 0 < C) (T : PTPTable) (hT : T.contract = true) (SL : SplitLayout X T.k C')
    (hCw : childWidth C T.ops ≤ C') (θ : Angle) (gc : ℕ → Fin T.k → LowGate) (W' : List ℕ)
    (hW' : ∀ q ∈ W', ∀ s j, q ∉ (SL.lay.slot s j).active.qubits)
    (hgc : ∀ t j, SpecOn (qs := qs) (fun s => SL.lay.slot s j) C' W' (θ * coeffN T C t) (gc t j)) :
    SpecOn (qs := qs) X C (SL.R ++ W') θ (ptpSubNode T SL gc) := by
  intro b hfit hcl
  have hR : ∀ q ∈ SL.R, RegEncoding.bit q b = false := fun q hq => hcl q (by simp [hq])
  have hW'b : ∀ q ∈ W', RegEncoding.bit q b = false := fun q hq => hcl q (by simp [hq])
  set b1 := SL.allocBasis b with hb1
  have hW'R : ∀ q ∈ W', q ∉ SL.R := fun q hq hR' => by
    obtain ⟨s, j, hm⟩ := SL.R_sub_slots hR'
    exact hW' q hq s j hm
  have hW'1 : ∀ q ∈ W', RegEncoding.bit q b1 = false := fun q hq => by
    rw [hb1, SL.bit_allocBasis_out b (hW'R q hq)]; exact hW'b q hq
  have hfitX : ∀ s, FitsSignedWidth C (extToInt (X s) b) := by
    intro s; rw [← hX s]; rw [hX s] at *; exact hfit s
  have hchild : ChildSpec SL.lay (fun t => θ * coeffN T C t) b1 gc :=
    childSpec_of_specOn SL.lay _ b1 gc W' hW' hW'1 hgc
  have hbody := evalL_nodeBody_ket (qs := qs) T hT C (fun s => extToInt (X s) b) hfitX SL.lay
    hCw θ b1 (fun s j => SL.slot_value hX hC b hR s j) gc hchild
  have hket : qs.ket b1 = LowerGateClass.evalL (qs := qs) SL.alloc (qs.ket b) :=
    (SL.evalL_alloc b).symm
  unfold ptpSubNode
  rw [LowerGateClass.evalL_seq, LowerGateClass.evalL_seq, SL.evalL_alloc, ← hb1, hbody,
    LowerGateClass.evalL_smul, hket, LowerGateClass.evalL_adj_apply]
  congr 2
  simp only [Angle.toReal]
  push_cast
  ring

end Spec


/-! ## Full recursion -/


/-- **O2: gate-level correctness through the full recursion.** If `P` passes the PTP
policy check, every gate-level recursion `G` following `P` at width `C` on registers `X`
with workspace `W` implements the PTP phase: on every basis state whose registers fit
signed `C` bits and whose workspace is `|0⟩`, `G θ` multiplies by
`exp(i π θ ⟦X 0⟧⟦X 1⟧⟦X 2⟧)` and returns the state (workspace clean again). -/
theorem PolicyImpl.specOn {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    {P : PTPPolicy} (hP : P.check = true) {X : Fin 3 → ExtReg} {C : ℕ} {W : List ℕ}
    {G : Angle → LowGate} (h : PolicyImpl P X C W G) (θ : Angle) :
    SpecOn (qs := qs) X C W θ (G θ) := by
  induction h generalizing θ with
  | leaf X C t u _ _ hD hA => exact specOn_leafSandwich X C t u hD hA θ
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' _ ih =>
      obtain ⟨b, hb, rfl⟩ := PTPPolicy.choose_mem hc
      exact specOn_ptpSubNode hX hC b.table (PTPPolicy.check_tables hP b hb) SL le_rfl θ _ W' hW'
        fun t j => (ih j (θ * coeffN b.table C t)).mono (hWc j)

/-- The headline form of O2 on basis states. -/
theorem evalL_policyImpl_ket {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    {P : PTPPolicy} (hP : P.check = true) {X : Fin 3 → ExtReg} {n : ℕ} {W : List ℕ}
    {G : Angle → LowGate} (h : PolicyImpl P X n W G) (φ : Angle) (b : qs.Basis)
    (hfit : ∀ s, FitsSignedWidth n (extToInt (X s) b))
    (hclean : ∀ q ∈ W, RegEncoding.bit q b = false) :
    LowerGateClass.evalL (qs := qs) (G φ) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((extToInt (X 0) b : ℤ) : ℂ) * ((extToInt (X 1) b : ℤ) : ℂ) *
          ((extToInt (X 2) b : ℤ) : ℂ))) • qs.ket b := by
  rw [h.specOn hP φ b hfit hclean]
  congr 2
  simp only [Angle.toReal]
  push_cast
  ring

/-! ## Census of the full recursion -/

theorem alloc_field_zero (m : NegationMethod) {X : Fin 3 → ExtReg} {k C' : ℕ}
    (SL : SplitLayout X k C') (F : AddField)
    (hn : ∀ n, F.f { cnot := n } = 0) :
    F.f (LowGate.resources (shorGateResourceModelFor m) SL.alloc) = 0 := by
  unfold SplitLayout.alloc
  simp only [LowGate.resources, F.seq, field_sequence, List.map_flatMap, List.map_map]
  simp only [shorGateResourceModelFor, shorGateResourceModel, hn, add_zero]
  apply List.sum_eq_zero
  intro a ha
  simp only [List.mem_flatMap, List.mem_map] at ha
  obtain ⟨_, _, _, _, rfl⟩ := ha
  exact F.zero

/-- **Census through the full recursion (Rz, Toffoli, X, H).** Every gate-level recursion
following `P` at width `C` has exactly the Rz, Toffoli, X and H counts of the policy
formula `ptpResources P C`, counted by the policy's resource model `P.resourceModel` (the negation
method `P.negation`; the extension gates are CNOT-only: `signExtend` is charged
`n` CNOTs by ForShor's model, so CNOT is not covered here). -/
theorem PolicyImpl.resources {P : PTPPolicy} {X : Fin 3 → ExtReg} {C : ℕ} {W : List ℕ}
    {G : Angle → LowGate} (h : PolicyImpl P X C W G) (θ : Angle) :
    let R := LowGate.resources P.resourceModel (G θ)
    R.rz = (ptpResources P C).rz ∧ R.toffoli = (ptpResources P C).toffoli ∧
      R.x = (ptpResources P C).x ∧ R.h = (ptpResources P C).h := by
  unfold PTPPolicy.resourceModel
  induction h generalizing θ with
  | leaf X C t u hX hstop hD hA =>
      have hl : ptpResources P C = leafCensus C := by
        rw [ptpResources]
        rcases hcC : P.choose C with _ | T
        · rfl
        · simp only [Nat.not_lt.mpr (hstop T hcC), ↓reduceDIte]
      obtain ⟨h1, h2, _, h4, h5, _⟩ := ptpLeafSandwich_resources _ θ
        (X 0) (X 1) (X 2) t u
      simp only [hl, leafCensus, hX] at h1 h2 h4 h5 ⊢
      exact ⟨h1, h2, h4, h5⟩
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' hsub ih =>
      have hn : ptpResources P C = nodeCensusFor P.negation (childWidth C T.ops) (addCount T.ops)
          (negCount T.ops) (cpCount T.ops) (ptpResources P (childWidth C T.ops)) := by
        rw [ptpResources, hc]
        simp only [hlt, ↓reduceDIte]
      have hch := fun j => ih j
      have key : ∀ (F : AddField), (∀ n, F.f { cnot := n } = 0) → ∀ (c : ℕ),
          (∀ j θ', F.f (LowGate.resources (shorGateResourceModelFor P.negation) (G j θ')) = c) →
          F.f (LowGate.resources (shorGateResourceModelFor P.negation)
            (ptpSubNode T SL (fun t j => G j (θ * coeffN T C t)))) =
          3 * (addCount T.ops * F.f (cuccaroModAddResources (childWidth C T.ops)) +
            negCount T.ops * F.f (opRes P.negation (childWidth C T.ops) (.negate (k := 1) 0))) +
              cpCount T.ops * c := by
        intro F hF c hc'
        unfold ptpSubNode
        simp only [LowGate.resources, F.seq, alloc_field_zero P.negation SL F hF, zero_add, add_zero]
        exact (body_field F P.negation SL.lay _ c (fun t j => hc' j _) T.ops 0).trans
          (bodyField_eq F P.negation SL.lay.width c T.ops)
      have hrz := key fRz (fun _ => rfl) _ fun j θ' => (hch j θ').1
      have hto := key fToff (fun _ => rfl) _ fun j θ' => (hch j θ').2.1
      have hx := key fX (fun _ => rfl) _ fun j θ' => (hch j θ').2.2.1
      have hh := key fH (fun _ => rfl) _ fun j θ' => (hch j θ').2.2.2
      simp only [fRz, fToff, fX, fH, opRes, cuccaroModAddResources] at hrz hto hx hh
      dsimp only
      rw [hn]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show (LowGate.resources (shorGateResourceModelFor P.negation) _).rz = _ from hrz]
        simp only [nodeCensusFor]; try ring
      · rw [show (LowGate.resources (shorGateResourceModelFor P.negation) _).toffoli = _ from hto]
        simp only [nodeCensusFor]
      · rw [show (LowGate.resources (shorGateResourceModelFor P.negation) _).x = _ from hx]
        simp only [nodeCensusFor]
      · rw [show (LowGate.resources (shorGateResourceModelFor P.negation) _).h = _ from hh]
        simp only [nodeCensusFor]; try ring

end PTP
end Shor
