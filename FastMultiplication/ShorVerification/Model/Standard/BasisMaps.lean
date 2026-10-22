import FastMultiplication.ShorVerification.Model.Standard.Basis
import FastMultiplication.ShorVerification.Model.Standard.Arith

/-!
# Every basis map is a bijection

Item 5 of the original construction plan. Each `*_ket_total` law in
`Framework/Semantics/GateSemantics.lean` sends `ket b` to `ket (f b)` for an
explicit `f : Basis → Basis`. This file exhibits, for each such `f`, an
`Equiv.Perm ModelBasis` whose forward map is literally `f`, which is what
`permLift` needs.

Risk 1 of the plan lives here: if one of these maps were not a bijection, the
corresponding law would be unsatisfiable. None of them fails.

Everything goes through `mWriteNat_mWriteNat`, `mWriteNat_mToNat` and
`mWriteNat_agree_off`; `mWriteNat` is never unfolded (risk 3).
-/

namespace Shor
namespace Model

/-! ## The shape all of these share

Every basis map writes one register and leaves the rest of the state alone.
Such a map is invertible as soon as the new value can be read back, which is
`regWrite_inv` below — no range side conditions needed.
-/

/-- Write `g b` into register `r`, leaving everything outside `r` alone. -/
def regWrite (r : Reg) (g : ModelBasis → ℕ) (b : ModelBasis) : ModelBasis :=
  mWriteNat r (g b) b

/-- If `h` recovers `r`'s old value from the written state, then `regWrite r h`
undoes `regWrite r g`. -/
theorem regWrite_inv {r : Reg} {g h : ModelBasis → ℕ}
    (key : ∀ b, h (regWrite r g b) = mToNat r b) (b : ModelBasis) :
    regWrite r h (regWrite r g b) = b := by
  show mWriteNat r (h (regWrite r g b)) (regWrite r g b) = b
  rw [key b, regWrite, mWriteNat_mWriteNat, mWriteNat_mToNat]

/-- The permutation built from two mutually recovering register writes. -/
def regWriteEquiv (r : Reg) (g h : ModelBasis → ℕ)
    (hgh : ∀ b, h (regWrite r g b) = mToNat r b)
    (hhg : ∀ b, g (regWrite r h b) = mToNat r b) : Equiv.Perm ModelBasis where
  toFun := regWrite r g
  invFun := regWrite r h
  left_inv := regWrite_inv hgh
  right_inv := regWrite_inv hhg

@[simp] theorem regWriteEquiv_apply (r : Reg) (g h : ModelBasis → ℕ) (hgh hhg)
    (b : ModelBasis) : regWriteEquiv r g h hgh hhg b = mWriteNat r (g b) b := rfl

/-- The involutive case. -/
def involutiveEquiv {f : ModelBasis → ModelBasis} (h : ∀ b, f (f b) = b) :
    Equiv.Perm ModelBasis := ⟨f, f, h, h⟩

@[simp] theorem involutiveEquiv_apply {f : ModelBasis → ModelBasis} (h : ∀ b, f (f b) = b)
    (b : ModelBasis) : involutiveEquiv h b = f b := rfl

/-! ## Updating one qubit -/

theorem update_apply_self (b : ModelBasis) (q : ℕ) (c : Bool) :
    Function.update b q c q = c := by simp

theorem update_apply_ne (b : ModelBasis) {q q' : ℕ} (h : q' ≠ q) (c : Bool) :
    Function.update b q c q' = b q' := by simp [h]

/-! ## `X` -/

/-- The basis action of `Gate.X`, as the law states it. -/
def xBasis (q : ℕ) (b : ModelBasis) : ModelBasis :=
  mWriteNat (qubitReg q) (if b q then 0 else 1) b

theorem xBasis_eq (q : ℕ) (b : ModelBasis) : xBasis q b = Function.update b q (!b q) := by
  cases h : b q <;> simp [xBasis, h, mWriteNat_qubitReg]

theorem xBasis_involutive (q : ℕ) (b : ModelBasis) : xBasis q (xBasis q b) = b := by
  rw [xBasis_eq, xBasis_eq, update_apply_self, Function.update_idem]
  simp

/-- `X` as a permutation of the computational basis. -/
def xPerm (q : ℕ) : Equiv.Perm ModelBasis := involutiveEquiv (xBasis_involutive q)

/-! ## `CNOT` and `Toffoli` -/

theorem cnotBasis_eq (ctrl target : ℕ) (b : ModelBasis) :
    cnotBasis (Basis := ModelBasis) ctrl target b =
      if ctrl = target then b
      else if b ctrl then Function.update b target (!b target) else b := by
  simp only [cnotBasis, bit_eq, writeNat_eq]
  by_cases hct : ctrl = target
  · rw [if_pos hct, if_pos hct]
  · rw [if_neg hct, if_neg hct]
    by_cases hc : b ctrl
    · rw [if_pos hc, if_pos hc]
      exact xBasis_eq target b
    · rw [if_neg hc, if_neg hc]

theorem cnotBasis_involutive (ctrl target : ℕ) (b : ModelBasis) :
    cnotBasis (Basis := ModelBasis) ctrl target (cnotBasis ctrl target b) = b := by
  by_cases hct : ctrl = target
  · rw [cnotBasis_eq, if_pos hct, cnotBasis_eq, if_pos hct]
  · by_cases hc : b ctrl
    · have h1 : cnotBasis (Basis := ModelBasis) ctrl target b
          = Function.update b target (!b target) := by
        rw [cnotBasis_eq, if_neg hct, if_pos hc]
      rw [h1, cnotBasis_eq, if_neg hct, update_apply_ne _ hct, if_pos hc,
        update_apply_self, Function.update_idem, Bool.not_not]
      exact Function.update_eq_self _ _
    · have h1 : cnotBasis (Basis := ModelBasis) ctrl target b = b := by
        rw [cnotBasis_eq, if_neg hct, if_neg hc]
      rw [h1, cnotBasis_eq, if_neg hct, if_neg hc]

/-- `CNOT` as a permutation of the computational basis. -/
def cnotPerm (ctrl target : ℕ) : Equiv.Perm ModelBasis :=
  involutiveEquiv (cnotBasis_involutive ctrl target)

theorem toffoliBasis_eq (c₁ c₂ target : ℕ) (b : ModelBasis) :
    toffoliBasis (Basis := ModelBasis) c₁ c₂ target b =
      if c₁ = c₂ ∨ c₁ = target ∨ c₂ = target then b
      else if b c₁ ∧ b c₂ then Function.update b target (!b target) else b := by
  simp only [toffoliBasis, bit_eq, writeNat_eq]
  by_cases hg : c₁ = c₂ ∨ c₁ = target ∨ c₂ = target
  · rw [if_pos hg, if_pos hg]
  · rw [if_neg hg, if_neg hg]
    by_cases hc : b c₁ ∧ b c₂
    · rw [if_pos hc, if_pos hc]
      exact xBasis_eq target b
    · rw [if_neg hc, if_neg hc]

theorem toffoliBasis_involutive (c₁ c₂ target : ℕ) (b : ModelBasis) :
    toffoliBasis (Basis := ModelBasis) c₁ c₂ target (toffoliBasis c₁ c₂ target b) = b := by
  by_cases hg : c₁ = c₂ ∨ c₁ = target ∨ c₂ = target
  · rw [toffoliBasis_eq, if_pos hg, toffoliBasis_eq, if_pos hg]
  · have h1t : c₁ ≠ target := fun h => hg (Or.inr (Or.inl h))
    have h2t : c₂ ≠ target := fun h => hg (Or.inr (Or.inr h))
    by_cases hc : b c₁ ∧ b c₂
    · have h1 : toffoliBasis (Basis := ModelBasis) c₁ c₂ target b
          = Function.update b target (!b target) := by
        rw [toffoliBasis_eq, if_neg hg, if_pos hc]
      rw [h1, toffoliBasis_eq, if_neg hg, update_apply_ne _ h1t, update_apply_ne _ h2t,
        if_pos hc, update_apply_self, Function.update_idem, Bool.not_not]
      exact Function.update_eq_self _ _
    · have h1 : toffoliBasis (Basis := ModelBasis) c₁ c₂ target b = b := by
        rw [toffoliBasis_eq, if_neg hg, if_neg hc]
      rw [h1, toffoliBasis_eq, if_neg hg, if_neg hc]

/-- `Toffoli` as a permutation of the computational basis. -/
def toffoliPerm (c₁ c₂ target : ℕ) : Equiv.Perm ModelBasis :=
  involutiveEquiv (toffoliBasis_involutive c₁ c₂ target)

/-! ## `CmpGeConst` -/

theorem cmpGeConstBasis_eq (N : ℕ) (data : Reg) (flag : ℕ) (b : ModelBasis) :
    cmpGeConstBasis (Basis := ModelBasis) N data flag b =
      if flag ∈ data.qubits then b
      else Function.update b flag (xor (b flag) (decide (N ≤ mToNat data b))) := by
  simp only [cmpGeConstBasis, bit_eq, writeNat_eq, toNat_eq]
  by_cases hf : flag ∈ data.qubits
  · rw [if_pos hf, if_pos hf]
  · rw [if_neg hf, if_neg hf]
    rcases Bool.eq_false_or_eq_true (b flag) with hb | hb <;>
      by_cases h : N ≤ mToNat data b <;>
      simp [h, hb, mWriteNat_qubitReg]

theorem cmpGeConstBasis_involutive (N : ℕ) (data : Reg) (flag : ℕ) (b : ModelBasis) :
    cmpGeConstBasis (Basis := ModelBasis) N data flag
        (cmpGeConstBasis N data flag b) = b := by
  by_cases hf : flag ∈ data.qubits
  · rw [cmpGeConstBasis_eq, if_pos hf, cmpGeConstBasis_eq, if_pos hf]
  · have h1 : cmpGeConstBasis (Basis := ModelBasis) N data flag b
        = Function.update b flag (xor (b flag) (decide (N ≤ mToNat data b))) := by
      rw [cmpGeConstBasis_eq, if_neg hf]
    have hne : ∀ q ∈ data.qubits, q ≠ flag := fun q hq hc => hf (hc ▸ hq)
    have hdata : mToNat data (Function.update b flag
        (xor (b flag) (decide (N ≤ mToNat data b)))) = mToNat data b :=
      mToNat_congr fun q hq => update_apply_ne _ (hne q hq) _
    rw [h1, cmpGeConstBasis_eq, if_neg hf, hdata, update_apply_self, Function.update_idem,
      show ∀ a g : Bool, xor (xor a g) g = a from fun a g => by cases a <;> cases g <;> rfl]
    exact Function.update_eq_self _ _

/-- `CmpGeConst` as a permutation of the computational basis. -/
def cmpGeConstPerm (N : ℕ) (data : Reg) (flag : ℕ) : Equiv.Perm ModelBasis :=
  involutiveEquiv (cmpGeConstBasis_involutive N data flag)

/-! ## Extendable registers

`ExtReg.width`, `ExtReg.toNat` and `extToInt` all read only `e.active`, so a
write to any register disjoint from `e.active` leaves them alone.
-/

@[simp] theorem extReg_toNat (e : ExtReg) (b : ModelBasis) :
    ExtReg.toNat e b = mToNat e.active b := rfl

@[simp] theorem extReg_width (e : ExtReg) : ExtReg.width e = regSize e.active := rfl

theorem extToInt_eq (e : ExtReg) (b : ModelBasis) :
    extToInt e b = tcDecodeWidth (regSize e.active) (mToNat e.active b) := rfl

theorem mToNat_active_lt (e : ExtReg) (b : ModelBasis) :
    mToNat e.active b < 2 ^ regSize e.active := mToNat_lt e.active b

theorem extToInt_mWriteNat_of_disjoint {e : ExtReg} {r : Reg}
    (h : ∀ q ∈ e.active.qubits, q ∉ r.qubits) (v : ℕ) (b : ModelBasis) :
    extToInt e (mWriteNat r v b) = extToInt e b := by
  rw [extToInt_eq, extToInt_eq, mToNat_mWriteNat_of_disjoint h]

theorem newBits_not_mem_active (e : ExtReg) (n : ℕ) :
    ∀ q ∈ e.active.qubits, q ∉ (e.newBits n).qubits := by
  intro q hq hmem
  have hdisj := e.active_reserve_disjoint
  rw [Disjoint, List.disjoint_left] at hdisj
  exact hdisj hq (List.mem_of_mem_take hmem)

theorem active_not_mem_of_activeDisjoint {x z : ExtReg} (h : ExtReg.ActiveDisjoint x z) :
    ∀ q ∈ z.active.qubits, q ∉ x.active.qubits := by
  intro q hq hc
  rw [ExtReg.ActiveDisjoint, Disjoint, List.disjoint_left] at h
  exact h hc hq

/-! ## `Negate` -/

theorem negateBasis_involutive (r : ExtReg) (b : ModelBasis) :
    negateBasis (Basis := ModelBasis) r (negateBasis r b) = b := by
  set w := regSize r.active with hw
  set u := mToNat r.active b with hu
  have hulti : u < 2 ^ w := mToNat_active_lt r b
  refine regWrite_inv (r := r.active)
    (g := fun b => tcModWidth w (-extToInt r b))
    (h := fun b => tcModWidth w (-extToInt r b)) ?_ b
  intro b'
  set v := tcModWidth w (-extToInt r b') with hv
  have hvlt : v < 2 ^ w := tcModWidth_lt w _
  have hread : mToNat r.active (mWriteNat r.active v b') = v :=
    mToNat_mWriteNat b' (by simpa [ASize] using hvlt)
  have hext : extToInt r (mWriteNat r.active v b') = tcDecodeWidth w v := by
    rw [extToInt_eq, hread]
  show tcModWidth w (-extToInt r (regWrite r.active (fun b => tcModWidth w (-extToInt r b)) b'))
      = mToNat r.active b'
  rw [regWrite, ← hv, hext]
  refine tcModWidth_eq_self (mToNat_active_lt r b') ?_
  have m1 : Int.ModEq (2 ^ w) (tcDecodeWidth w v) (-extToInt r b') :=
    (tcDecodeWidth_modEq w v).trans (tcModWidth_self_modEq w _)
  have m2 : Int.ModEq (2 ^ w) (-(tcDecodeWidth w v)) (extToInt r b') := by
    simpa using m1.neg
  exact m2.trans (by rw [extToInt_eq]; exact tcDecodeWidth_modEq w _)

/-- `Negate` as a permutation of the computational basis. -/
def negatePerm (r : ExtReg) : Equiv.Perm ModelBasis :=
  involutiveEquiv (negateBasis_involutive r)

/-! ## `signExtend` and `signDealloc` -/

theorem signExtendNewValue_eq (r : ExtReg) (n : ℕ) (b : ModelBasis) :
    signExtendNewValue (Basis := ModelBasis) r n b
      = if extToInt r b < 0 then ASize (r.newBits n) - 1 - mToNat (r.newBits n) b
        else mToNat (r.newBits n) b := rfl

theorem signExtendNewValue_lt (r : ExtReg) (n : ℕ) (b : ModelBasis) :
    signExtendNewValue (Basis := ModelBasis) r n b < ASize (r.newBits n) := by
  have h1 : mToNat (r.newBits n) b < ASize (r.newBits n) := mToNat_lt _ b
  have h2 : 0 < ASize (r.newBits n) := two_pow_pos' _
  rw [signExtendNewValue_eq]
  split <;> omega

theorem signExtendBasis_involutive (r : ExtReg) (n : ℕ) (b : ModelBasis) :
    signExtendBasis (Basis := ModelBasis) r n (signExtendBasis r n b) = b := by
  refine regWrite_inv (r := r.newBits n) (g := signExtendNewValue r n)
    (h := signExtendNewValue r n) ?_ b
  intro b'
  have h1 : mToNat (r.newBits n) b' < ASize (r.newBits n) := mToNat_lt _ b'
  have h2 : 0 < ASize (r.newBits n) := two_pow_pos' _
  have hread : mToNat (r.newBits n) (mWriteNat (r.newBits n) (signExtendNewValue r n b') b')
      = signExtendNewValue (Basis := ModelBasis) r n b' :=
    mToNat_mWriteNat b' (signExtendNewValue_lt r n b')
  have hext : extToInt r (mWriteNat (r.newBits n) (signExtendNewValue r n b') b')
      = extToInt r b' :=
    extToInt_mWriteNat_of_disjoint (newBits_not_mem_active r n) _ b'
  show signExtendNewValue r n (mWriteNat (r.newBits n) (signExtendNewValue r n b') b')
      = mToNat (r.newBits n) b'
  rw [signExtendNewValue_eq, hext, hread, signExtendNewValue_eq]
  by_cases hneg : extToInt r b' < 0
  · simp only [if_pos hneg]
    omega
  · simp only [if_neg hneg]

/-- `signExtend` (and `signDealloc`, the same map) as a permutation. -/
def signExtendPerm (r : ExtReg) (n : ℕ) : Equiv.Perm ModelBasis :=
  involutiveEquiv (signExtendBasis_involutive r n)

/-! ## `CSubConst`

`csubConstBasis` subtracts `N` from `data` modulo `ASize data` when `flag` is
set. Its inverse adds `N` back, which is the map named here.
-/

/-- The inverse of `csubConstBasis`: add the constant back. -/
def caddConstBasis (N : ℕ) (data : Reg) (flag : ℕ) (b : ModelBasis) : ModelBasis :=
  if flag ∈ data.qubits then b
  else mWriteNat data
      (if b flag then (mToNat data b + (N % ASize data)) % ASize data else mToNat data b) b

theorem mod_sub_then_add {A m x : ℕ} (_hA : 0 < A) (hm : m ≤ A) (hx : x < A) :
    ((x + A - m) % A + m) % A = x := by
  rw [Nat.mod_add_mod, Nat.sub_add_cancel (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt hx]

theorem mod_add_then_sub {A m x : ℕ} (_hA : 0 < A) (hm : m ≤ A) (hx : x < A) :
    ((x + m) % A + A - m) % A = x := by
  have hv : (x + m) % A < A := Nat.mod_lt _ (by omega)
  rw [show (x + m) % A + A - m = (x + m) % A + (A - m) from by omega, Nat.mod_add_mod,
    show x + m + (A - m) = x + A from by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

/-- The subtracting value written into `data`. -/
def csubVal (N : ℕ) (data : Reg) (flag : ℕ) (b : ModelBasis) : ℕ :=
  if b flag then (mToNat data b + ASize data - N % ASize data) % ASize data else mToNat data b

/-- The adding value written into `data`. -/
def caddVal (N : ℕ) (data : Reg) (flag : ℕ) (b : ModelBasis) : ℕ :=
  if b flag then (mToNat data b + N % ASize data) % ASize data else mToNat data b

theorem csubConstBasis_of_not_mem {N : ℕ} {data : Reg} {flag : ℕ}
    (hf : flag ∉ data.qubits) (b : ModelBasis) :
    csubConstBasis (Basis := ModelBasis) N data flag b = regWrite data (csubVal N data flag) b := by
  rw [csubConstBasis, if_neg hf]
  rfl

theorem caddConstBasis_of_not_mem {N : ℕ} {data : Reg} {flag : ℕ}
    (hf : flag ∉ data.qubits) (b : ModelBasis) :
    caddConstBasis N data flag b = regWrite data (caddVal N data flag) b := by
  rw [caddConstBasis, if_neg hf]
  rfl

theorem csubVal_lt {N : ℕ} {data : Reg} {flag : ℕ} (b : ModelBasis) :
    csubVal N data flag b < ASize data := by
  have hA : 0 < ASize data := two_pow_pos' _
  rw [csubVal]; split <;> [exact Nat.mod_lt _ hA; exact mToNat_lt data b]

theorem caddVal_lt {N : ℕ} {data : Reg} {flag : ℕ} (b : ModelBasis) :
    caddVal N data flag b < ASize data := by
  have hA : 0 < ASize data := two_pow_pos' _
  rw [caddVal]; split <;> [exact Nat.mod_lt _ hA; exact mToNat_lt data b]

theorem csub_cadd {N : ℕ} {data : Reg} {flag : ℕ} (hf : flag ∉ data.qubits) (b : ModelBasis) :
    caddConstBasis N data flag (csubConstBasis (Basis := ModelBasis) N data flag b) = b := by
  have hA : 0 < ASize data := two_pow_pos' _
  have hm : N % ASize data ≤ ASize data := le_of_lt (Nat.mod_lt _ hA)
  rw [csubConstBasis_of_not_mem hf, caddConstBasis_of_not_mem hf]
  refine regWrite_inv ?_ b
  intro b'
  have hflag : (mWriteNat data (csubVal N data flag b') b') flag = b' flag :=
    mWriteNat_agree_off _ _ _ _ hf
  have hread := mToNat_mWriteNat (r := data) b' (csubVal_lt (N := N) (flag := flag) b')
  show caddVal N data flag (mWriteNat data (csubVal N data flag b') b') = _
  rw [caddVal, hflag, hread, csubVal]
  by_cases hb : b' flag
  · rw [if_pos hb, if_pos hb]
    exact mod_sub_then_add hA hm (mToNat_lt data b')
  · rw [if_neg hb, if_neg hb]

theorem cadd_csub {N : ℕ} {data : Reg} {flag : ℕ} (hf : flag ∉ data.qubits) (b : ModelBasis) :
    csubConstBasis (Basis := ModelBasis) N data flag (caddConstBasis N data flag b) = b := by
  have hA : 0 < ASize data := two_pow_pos' _
  have hm : N % ASize data ≤ ASize data := le_of_lt (Nat.mod_lt _ hA)
  rw [caddConstBasis_of_not_mem hf, csubConstBasis_of_not_mem hf]
  refine regWrite_inv ?_ b
  intro b'
  have hflag : (mWriteNat data (caddVal N data flag b') b') flag = b' flag :=
    mWriteNat_agree_off _ _ _ _ hf
  have hread := mToNat_mWriteNat (r := data) b' (caddVal_lt (N := N) (flag := flag) b')
  show csubVal N data flag (mWriteNat data (caddVal N data flag b') b') = _
  rw [csubVal, hflag, hread, caddVal]
  by_cases hb : b' flag
  · rw [if_pos hb, if_pos hb]
    exact mod_add_then_sub hA hm (mToNat_lt data b')
  · rw [if_neg hb, if_neg hb]

/-- `CSubConst` as a permutation of the computational basis. -/
def csubConstPerm (N : ℕ) (data : Reg) (flag : ℕ) : Equiv.Perm ModelBasis := by
  classical
  by_cases hf : flag ∈ data.qubits
  · exact Equiv.refl _
  · exact ⟨csubConstBasis N data flag, caddConstBasis N data flag,
      csub_cadd hf, cadd_csub hf⟩

theorem csubConstPerm_apply (N : ℕ) (data : Reg) (flag : ℕ) (b : ModelBasis) :
    csubConstPerm N data flag b = csubConstBasis (Basis := ModelBasis) N data flag b := by
  classical
  rw [csubConstPerm]
  by_cases hf : flag ∈ data.qubits
  · rw [dif_pos hf]
    show b = _
    rw [csubConstBasis, if_pos hf]
  · rw [dif_neg hf]
    rfl

/-! ## `AddScaled` -/

/-- The value `AddScaled` writes into `dst`. -/
noncomputable def addScaledVal (dst src : ExtReg) (negSrc : Bool) (sh : ℕ) (b : ModelBasis) : ℕ :=
  tcModWidth (regSize dst.active)
    (extToInt dst b + (if negSrc then (-1 : ℤ) else 1) * 2 ^ sh * extToInt src b)

theorem addScaledBasis_of_disjoint {dst src : ExtReg} (hdisj : ExtReg.ActiveDisjoint dst src)
    (negSrc : Bool) (sh : ℕ) (b : ModelBasis) :
    addScaledBasis (Basis := ModelBasis) dst src negSrc sh b
      = regWrite dst.active (addScaledVal dst src negSrc sh) b := by
  rw [addScaledBasis, dif_pos hdisj]
  rfl

theorem addScaledBasis_of_not_disjoint {dst src : ExtReg}
    (hdisj : ¬ ExtReg.ActiveDisjoint dst src) (negSrc : Bool) (sh : ℕ) (b : ModelBasis) :
    addScaledBasis (Basis := ModelBasis) dst src negSrc sh b = b := by
  rw [addScaledBasis, dif_neg hdisj]

theorem addScaled_key {dst src : ExtReg} (hdisj : ExtReg.ActiveDisjoint dst src)
    (negSrc : Bool) (sh : ℕ) (b : ModelBasis) :
    addScaledVal dst src (!negSrc) sh (regWrite dst.active (addScaledVal dst src negSrc sh) b)
      = mToNat dst.active b := by
  set w := regSize dst.active with hw
  set c : ℤ := (if negSrc then (-1 : ℤ) else 1) * 2 ^ sh with hc
  have hcneg : (if (!negSrc) then (-1 : ℤ) else 1) * 2 ^ sh = -c := by
    cases negSrc <;> simp [hc]
  set v := addScaledVal dst src negSrc sh b with hv
  have hvlt : v < 2 ^ w := tcModWidth_lt w _
  have hread : mToNat dst.active (mWriteNat dst.active v b) = v :=
    mToNat_mWriteNat b (by simpa [ASize] using hvlt)
  have hsrc : extToInt src (mWriteNat dst.active v b) = extToInt src b :=
    extToInt_mWriteNat_of_disjoint (active_not_mem_of_activeDisjoint hdisj) v b
  have hdst : extToInt dst (mWriteNat dst.active v b) = tcDecodeWidth w v := by
    rw [extToInt_eq, hread]
  show addScaledVal dst src (!negSrc) sh (mWriteNat dst.active v b) = _
  rw [addScaledVal, hsrc, hdst, hcneg, ← hw]
  refine tcModWidth_eq_self (mToNat_active_lt dst b) ?_
  have m1 : Int.ModEq (2 ^ w) (tcDecodeWidth w v) (extToInt dst b + c * extToInt src b) :=
    (tcDecodeWidth_modEq w v).trans (tcModWidth_self_modEq w _)
  have m2 := m1.add_right ((-c) * extToInt src b)
  rw [show extToInt dst b + c * extToInt src b + -c * extToInt src b = extToInt dst b from by ring]
    at m2
  exact m2.trans (by rw [extToInt_eq]; exact tcDecodeWidth_modEq w _)

theorem addScaledBasis_inv {dst src : ExtReg} (hdisj : ExtReg.ActiveDisjoint dst src)
    (negSrc : Bool) (sh : ℕ) (b : ModelBasis) :
    addScaledBasis (Basis := ModelBasis) dst src (!negSrc) sh
      (addScaledBasis dst src negSrc sh b) = b := by
  rw [addScaledBasis_of_disjoint hdisj, addScaledBasis_of_disjoint hdisj]
  exact regWrite_inv (addScaled_key hdisj negSrc sh) b

/-- `AddScaled` as a permutation of the computational basis. -/
noncomputable def addScaledPerm (dst src : ExtReg) (negSrc : Bool) (sh : ℕ) :
    Equiv.Perm ModelBasis := by
  classical
  by_cases hdisj : ExtReg.ActiveDisjoint dst src
  · exact
      { toFun := addScaledBasis dst src negSrc sh
        invFun := addScaledBasis dst src (!negSrc) sh
        left_inv := addScaledBasis_inv hdisj negSrc sh
        right_inv := fun b => by
          have := addScaledBasis_inv hdisj (!negSrc) sh b
          simpa using this }
  · exact Equiv.refl _

theorem addScaledPerm_apply (dst src : ExtReg) (negSrc : Bool) (sh : ℕ) (b : ModelBasis) :
    addScaledPerm dst src negSrc sh b = addScaledBasis (Basis := ModelBasis) dst src negSrc sh b := by
  classical
  rw [addScaledPerm]
  by_cases hdisj : ExtReg.ActiveDisjoint dst src
  · rw [dif_pos hdisj]; rfl
  · rw [dif_neg hdisj, addScaledBasis_of_not_disjoint hdisj]; rfl

/-! ## `RadixReverse`

`radixReverseBasis r m` reads `r` as a two-digit number in base `2 ^ m` /
`2 ^ (w - m)` and swaps the digits. Its inverse is the same map at the
complementary split point, `w - m`.
-/

theorem ASize_splitLeft (r : Reg) (m : ℕ) (hm : m ≤ regSize r) :
    ASize (splitLeft r ⟨m, hm⟩) = 2 ^ m := by
  rw [ASize, regSize_splitLeft r m hm]

theorem ASize_splitRight (r : Reg) (m : ℕ) (hm : m ≤ regSize r) :
    ASize (splitRight r ⟨m, hm⟩) = 2 ^ (regSize r - m) := by
  rw [ASize, regSize_splitRight r m hm]

theorem radixReverseBasis_of_le {r : Reg} {m : ℕ} (hm : m ≤ regSize r) (b : ModelBasis) :
    radixReverseBasis (Basis := ModelBasis) r m b
      = mWriteNat r (2 ^ (regSize r - m) * mToNat (splitLeft r ⟨m, hm⟩) b
          + mToNat (splitRight r ⟨m, hm⟩) b) b := by
  rw [radixReverseBasis, dif_pos hm]
  show mWriteNat r (ASize (splitRight r ⟨m, hm⟩) * _ + _) b = _
  rw [ASize_splitRight r m hm]
  rfl

theorem radixReverseBasis_of_gt {r : Reg} {m : ℕ} (hm : ¬ m ≤ regSize r) (b : ModelBasis) :
    radixReverseBasis (Basis := ModelBasis) r m b = b := by
  rw [radixReverseBasis, dif_neg hm]

@[simp] theorem radixReverseBasis_zero (r : Reg) (b : ModelBasis) :
    radixReverseBasis (Basis := ModelBasis) r 0 b = b := by
  rw [radixReverseBasis_of_le (Nat.zero_le _)]
  have hL : mToNat (splitLeft r ⟨0, Nat.zero_le _⟩) b = 0 := rfl
  have hR : mToNat (splitRight r ⟨0, Nat.zero_le _⟩) b = mToNat r b := by
    show toNatList (r.qubits.drop 0) b = toNatList r.qubits b
    rw [List.drop_zero]
  rw [hL, hR, mul_zero, Nat.zero_add, mWriteNat_mToNat]

/-- The digit-swap at `m`, undone by the digit-swap at `w - m`. -/
theorem radixReverseBasis_inv {r : Reg} {m : ℕ} (hm : m ≤ regSize r) (b : ModelBasis) :
    radixReverseBasis (Basis := ModelBasis) r (regSize r - m)
      (radixReverseBasis r m b) = b := by
  set w := regSize r with hw
  have hk : w - m ≤ w := Nat.sub_le _ _
  have hwk : w - (w - m) = m := by omega
  have hsum : (w - m) + m = w := by omega
  set kL := mToNat (splitLeft r ⟨m, hm⟩) b with hkL
  set kH := mToNat (splitRight r ⟨m, hm⟩) b with hkH
  have hkLlt : kL < 2 ^ m := by
    have := mToNat_lt (splitLeft r ⟨m, hm⟩) b; rwa [ASize_splitLeft r m hm] at this
  have hkHlt : kH < 2 ^ (w - m) := by
    have := mToNat_lt (splitRight r ⟨m, hm⟩) b; rwa [ASize_splitRight r m hm] at this
  have hpow : (2:ℕ) ^ (w - m) * 2 ^ m = 2 ^ w := by rw [← pow_add, hsum]
  set v := 2 ^ (w - m) * kL + kH with hv
  have hvlt : v < 2 ^ w := by
    have h1 : (2:ℕ) ^ (w - m) * kL ≤ 2 ^ (w - m) * (2 ^ m - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (2:ℕ) ^ (w - m) * (2 ^ m - 1) = 2 ^ w - 2 ^ (w - m) := by
      rw [Nat.mul_sub, mul_one, hpow]
    have h3 : (2:ℕ) ^ (w - m) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hvASize : v < ASize r := by rwa [ASize, ← hw]
  -- the written state
  set b₁ := mWriteNat r v b with hb₁
  have hb₁read : mToNat r b₁ = v := mToNat_mWriteNat b hvASize
  -- re-split `b₁` at the complementary point
  set kL' := mToNat (splitLeft r ⟨w - m, hk⟩) b₁ with hkL'
  set kH' := mToNat (splitRight r ⟨w - m, hk⟩) b₁ with hkH'
  have hkL'lt : kL' < 2 ^ (w - m) := by
    have := mToNat_lt (splitLeft r ⟨w - m, hk⟩) b₁
    rwa [ASize_splitLeft r (w - m) hk] at this
  have hsplit1 : v = kL' + 2 ^ (w - m) * kH' := by
    rw [← hb₁read]; exact mToNat_split r (w - m) hk b₁
  have hswapL : kL' = kH := by
    have e1 : v % 2 ^ (w - m) = kL' := by
      rw [hsplit1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hkL'lt]
    have e2 : v % 2 ^ (w - m) = kH := by
      rw [hv, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hkHlt]
    omega
  have hswapH : kH' = kL := by
    have hp : 0 < (2:ℕ) ^ (w - m) := two_pow_pos' _
    have e1 : v / 2 ^ (w - m) = kH' := by
      rw [hsplit1, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hkL'lt, Nat.zero_add]
    have e2 : v / 2 ^ (w - m) = kL := by
      rw [hv, Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hkHlt, Nat.zero_add]
    omega
  -- and compute the second pass
  have hsplit0 : mToNat r b = kL + 2 ^ m * kH := mToNat_split r m hm b
  rw [radixReverseBasis_of_le hm, ← hkL, ← hkH, ← hv, ← hb₁,
    radixReverseBasis_of_le hk, ← hkL', ← hkH', hwk, hswapL, hswapH, hb₁,
    mWriteNat_mWriteNat, show 2 ^ m * kH + kL = mToNat r b from by omega, mWriteNat_mToNat]

/-- `RadixReverse` as a permutation of the computational basis. -/
def radixReversePerm (r : Reg) (m : ℕ) : Equiv.Perm ModelBasis := by
  classical
  by_cases hm : m ≤ regSize r
  · exact
      { toFun := radixReverseBasis r m
        invFun := radixReverseBasis r (regSize r - m)
        left_inv := radixReverseBasis_inv hm
        right_inv := fun b => by
          have h := radixReverseBasis_inv (r := r) (m := regSize r - m) (Nat.sub_le _ _) b
          rwa [show regSize r - (regSize r - m) = m from by omega] at h }
  · exact Equiv.refl _

theorem radixReversePerm_apply (r : Reg) (m : ℕ) (b : ModelBasis) :
    radixReversePerm r m b = radixReverseBasis (Basis := ModelBasis) r m b := by
  classical
  rw [radixReversePerm]
  by_cases hm : m ≤ regSize r
  · rw [dif_pos hm]; rfl
  · rw [dif_neg hm, radixReverseBasis_of_gt hm]; rfl

/-! ## `ShiftL` and `ShiftR`

`shiftLBasis` dispatches between an exact branch guarded by `FitsSignedWidth`
and the reversible completion `signedShiftLWord`. `Arith.lean` showed the two
agree wherever the guard fires, so each basis map *is* its raw version, and the
raw versions are mutually inverse word maps.
-/

theorem shiftLBasis_eq_raw (r : ExtReg) (n : ℕ) (b : ModelBasis) :
    shiftLBasis (Basis := ModelBasis) r n b = shiftLBasisRaw r n b := by
  rw [shiftLBasis]
  by_cases h : FitsSignedWidth r.width ((2 : ℤ) ^ n * extToInt r b)
  · rw [dif_pos h, shiftLBasisRaw]
    congr 1
    exact shiftLWord_fits_eq (mToNat_active_lt r b) h
  · rw [dif_neg h]

theorem shiftRBasis_eq_raw (r : ExtReg) (n : ℕ) (b : ModelBasis) :
    shiftRBasis (Basis := ModelBasis) r n b = shiftRBasisRaw r n b := by
  rw [shiftRBasis]
  by_cases h : ∃ q : ℤ, extToInt r b = (2 : ℤ) ^ n * q ∧ FitsSignedWidth r.width q
  · rw [dif_pos h, shiftRBasisRaw]
    congr 1
    obtain ⟨hq1, hq2⟩ := Classical.choose_spec h
    exact shiftRWord_fits_eq (mToNat_active_lt r b) hq1 hq2
  · rw [dif_neg h]

theorem shiftRBasisRaw_shiftLBasisRaw (r : ExtReg) (n : ℕ) (b : ModelBasis) :
    shiftRBasisRaw (Basis := ModelBasis) r n (shiftLBasisRaw r n b) = b := by
  refine regWrite_inv (r := r.active)
    (g := fun b => signedShiftLWord (regSize r.active) n (mToNat r.active b))
    (h := fun b => signedShiftRWord (regSize r.active) n (mToNat r.active b)) ?_ b
  intro b'
  have hlt : signedShiftLWord (regSize r.active) n (mToNat r.active b') < ASize r.active :=
    signedShiftLWord_lt (mToNat_active_lt r b')
  show signedShiftRWord (regSize r.active) n
      (mToNat r.active (mWriteNat r.active _ b')) = _
  rw [mToNat_mWriteNat b' hlt]
  exact signedShiftRWord_signedShiftLWord (mToNat_active_lt r b')

theorem shiftLBasisRaw_shiftRBasisRaw (r : ExtReg) (n : ℕ) (b : ModelBasis) :
    shiftLBasisRaw (Basis := ModelBasis) r n (shiftRBasisRaw r n b) = b := by
  refine regWrite_inv (r := r.active)
    (g := fun b => signedShiftRWord (regSize r.active) n (mToNat r.active b))
    (h := fun b => signedShiftLWord (regSize r.active) n (mToNat r.active b)) ?_ b
  intro b'
  have hlt : signedShiftRWord (regSize r.active) n (mToNat r.active b') < ASize r.active :=
    signedShiftRWord_lt (mToNat_active_lt r b')
  show signedShiftLWord (regSize r.active) n
      (mToNat r.active (mWriteNat r.active _ b')) = _
  rw [mToNat_mWriteNat b' hlt]
  exact signedShiftLWord_signedShiftRWord (mToNat_active_lt r b')

/-- `ShiftL` as a permutation of the computational basis. -/
noncomputable def shiftLPerm (r : ExtReg) (n : ℕ) : Equiv.Perm ModelBasis where
  toFun := shiftLBasis r n
  invFun := shiftRBasis r n
  left_inv b := by
    rw [shiftLBasis_eq_raw, shiftRBasis_eq_raw]
    exact shiftRBasisRaw_shiftLBasisRaw r n b
  right_inv b := by
    rw [shiftRBasis_eq_raw, shiftLBasis_eq_raw]
    exact shiftLBasisRaw_shiftRBasisRaw r n b

@[simp] theorem shiftLPerm_apply (r : ExtReg) (n : ℕ) (b : ModelBasis) :
    shiftLPerm r n b = shiftLBasis (Basis := ModelBasis) r n b := rfl

/-- `ShiftR` as a permutation of the computational basis. -/
noncomputable def shiftRPerm (r : ExtReg) (n : ℕ) : Equiv.Perm ModelBasis :=
  (shiftLPerm r n).symm

@[simp] theorem shiftRPerm_apply (r : ExtReg) (n : ℕ) (b : ModelBasis) :
    shiftRPerm r n b = shiftRBasis (Basis := ModelBasis) r n b := rfl

/-! ## `idealCtrlModMul`

`eval_idealCtrlModMul_ket_exact` is the one law stated under hypotheses, so the
model is free to choose anything outside them. §0.5 of the plan takes the
identity: inside the guard this permutes `{x < N}` by multiplication by a unit
mod `N`, outside it is the identity, and the two regions are disjoint.
-/

/-- The inverse of `c` mod `N`. -/
noncomputable def modInv (c N : ℕ) : ℕ := ((c : ZMod N)⁻¹).val

theorem modInv_mul_modEq {c N : ℕ} (hN : 1 < N) (hcop : Nat.Coprime c N) :
    c * modInv c N ≡ 1 [MOD N] := by
  haveI : NeZero N := ⟨by omega⟩
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  push_cast
  rw [modInv, ZMod.natCast_val, ZMod.cast_id]
  exact ZMod.coe_mul_inv_eq_one c hcop

/-- The guard of the model's `idealCtrlModMul`: exactly the hypotheses of
`eval_idealCtrlModMul_ket_exact`. -/
def IdealGuard (c N : ℕ) (data : Reg) (ctrl : ℕ) (b : ModelBasis) : Prop :=
  1 < N ∧ N ≤ ASize data ∧ Nat.Coprime c N ∧ ctrl ∉ data.qubits ∧ mToNat data b < N

instance (c N : ℕ) (data : Reg) (ctrl : ℕ) (b : ModelBasis) :
    Decidable (IdealGuard c N data ctrl b) := by
  unfold IdealGuard; infer_instance

/-- The model's basis action for `Gate.idealCtrlModMul`. -/
def idealCtrlModMulBasis (c N : ℕ) (data : Reg) (ctrl : ℕ) (b : ModelBasis) : ModelBasis :=
  if IdealGuard c N data ctrl b then
    mWriteNat data (if b ctrl then (c * mToNat data b) % N else mToNat data b) b
  else b

/-- Its inverse: the same guard, multiplying by `c⁻¹ mod N` instead. -/
noncomputable def idealCtrlModMulInv (c N : ℕ) (data : Reg) (ctrl : ℕ) (b : ModelBasis) :
    ModelBasis :=
  if IdealGuard c N data ctrl b then
    mWriteNat data (if b ctrl then (modInv c N * mToNat data b) % N else mToNat data b) b
  else b

section Ideal

variable {c N : ℕ} {data : Reg} {ctrl : ℕ}

/-- Both maps write a value below `N`, so the guard survives them. -/
theorem ideal_step (e : ℕ) (hg : IdealGuard c N data ctrl b) :
    IdealGuard c N data ctrl
        (mWriteNat data (if b ctrl then (e * mToNat data b) % N else mToNat data b) b)
      ∧ mToNat data (mWriteNat data
          (if b ctrl then (e * mToNat data b) % N else mToNat data b) b)
        = (if b ctrl then (e * mToNat data b) % N else mToNat data b)
      ∧ (mWriteNat data (if b ctrl then (e * mToNat data b) % N else mToNat data b) b) ctrl
        = b ctrl := by
  obtain ⟨hN, hNA, hcop, hctrl, hx⟩ := hg
  have hvN : (if b ctrl then (e * mToNat data b) % N else mToNat data b) < N := by
    split
    · exact Nat.mod_lt _ (by omega)
    · exact hx
  have hread := mToNat_mWriteNat (r := data) b (lt_of_lt_of_le hvN hNA)
  have hc : (mWriteNat data (if b ctrl then (e * mToNat data b) % N else mToNat data b) b) ctrl
      = b ctrl := mWriteNat_agree_off _ _ _ _ hctrl
  exact ⟨⟨hN, hNA, hcop, hctrl, by rw [hread]; exact hvN⟩, hread, hc⟩

theorem idealCtrlModMul_left_inv (b : ModelBasis) :
    idealCtrlModMulInv c N data ctrl (idealCtrlModMulBasis c N data ctrl b) = b := by
  rw [idealCtrlModMulBasis]
  by_cases hg : IdealGuard c N data ctrl b
  · rw [if_pos hg]
    obtain ⟨hg', hread, hc⟩ := ideal_step (b := b) c hg
    obtain ⟨hN, hNA, hcop, hctrl, hx⟩ := hg
    rw [idealCtrlModMulInv, if_pos hg', hread, hc]
    have hkey : (if b ctrl then
        (modInv c N * (if b ctrl then (c * mToNat data b) % N else mToNat data b)) % N
      else (if b ctrl then (c * mToNat data b) % N else mToNat data b)) = mToNat data b := by
      by_cases hb : b ctrl
      · rw [if_pos hb, if_pos hb]
        have hmod : modInv c N * ((c * mToNat data b) % N) ≡ mToNat data b [MOD N] := by
          calc modInv c N * ((c * mToNat data b) % N)
              ≡ modInv c N * (c * mToNat data b) [MOD N] :=
                Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
            _ = (c * modInv c N) * mToNat data b := by ring
            _ ≡ 1 * mToNat data b [MOD N] :=
                Nat.ModEq.mul_right _ (modInv_mul_modEq hN hcop)
            _ = mToNat data b := by ring
        rw [Nat.ModEq] at hmod
        rw [hmod, Nat.mod_eq_of_lt hx]
      · rw [if_neg hb, if_neg hb]
    rw [hkey, mWriteNat_mWriteNat, mWriteNat_mToNat]
  · rw [if_neg hg, idealCtrlModMulInv, if_neg hg]

theorem idealCtrlModMul_right_inv (b : ModelBasis) :
    idealCtrlModMulBasis c N data ctrl (idealCtrlModMulInv c N data ctrl b) = b := by
  rw [idealCtrlModMulInv]
  by_cases hg : IdealGuard c N data ctrl b
  · rw [if_pos hg]
    obtain ⟨hg', hread, hc⟩ := ideal_step (b := b) (modInv c N) hg
    obtain ⟨hN, hNA, hcop, hctrl, hx⟩ := hg
    rw [idealCtrlModMulBasis, if_pos hg', hread, hc]
    have hkey : (if b ctrl then
        (c * (if b ctrl then (modInv c N * mToNat data b) % N else mToNat data b)) % N
      else (if b ctrl then (modInv c N * mToNat data b) % N else mToNat data b))
        = mToNat data b := by
      by_cases hb : b ctrl
      · rw [if_pos hb, if_pos hb]
        have hmod : c * ((modInv c N * mToNat data b) % N) ≡ mToNat data b [MOD N] := by
          calc c * ((modInv c N * mToNat data b) % N)
              ≡ c * (modInv c N * mToNat data b) [MOD N] :=
                Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
            _ = (c * modInv c N) * mToNat data b := by ring
            _ ≡ 1 * mToNat data b [MOD N] :=
                Nat.ModEq.mul_right _ (modInv_mul_modEq hN hcop)
            _ = mToNat data b := by ring
        rw [Nat.ModEq] at hmod
        rw [hmod, Nat.mod_eq_of_lt hx]
      · rw [if_neg hb, if_neg hb]
    rw [hkey, mWriteNat_mWriteNat, mWriteNat_mToNat]
  · rw [if_neg hg, idealCtrlModMulBasis, if_neg hg]

end Ideal

/-- `idealCtrlModMul` as a permutation of the computational basis. -/
noncomputable def idealCtrlModMulPerm (c N : ℕ) (data : Reg) (ctrl : ℕ) :
    Equiv.Perm ModelBasis where
  toFun := idealCtrlModMulBasis c N data ctrl
  invFun := idealCtrlModMulInv c N data ctrl
  left_inv := idealCtrlModMul_left_inv
  right_inv := idealCtrlModMul_right_inv

@[simp] theorem idealCtrlModMulPerm_apply (c N : ℕ) (data : Reg) (ctrl : ℕ) (b : ModelBasis) :
    idealCtrlModMulPerm c N data ctrl b = idealCtrlModMulBasis c N data ctrl b := rfl

/-- Inside the guard, the model's map is exactly what
`eval_idealCtrlModMul_ket_exact` demands. -/
theorem idealCtrlModMulBasis_of_guard {c N : ℕ} {data : Reg} {ctrl : ℕ} {b : ModelBasis}
    (hN : 1 < N) (hNA : N ≤ ASize data) (hcop : Nat.Coprime c N) (hctrl : ctrl ∉ data.qubits)
    (hx : mToNat data b < N) :
    idealCtrlModMulBasis c N data ctrl b
      = mWriteNat data (if b ctrl then (c * mToNat data b) % N else mToNat data b) b := by
  rw [idealCtrlModMulBasis, if_pos ⟨hN, hNA, hcop, hctrl, hx⟩]

end Model
end Shor
