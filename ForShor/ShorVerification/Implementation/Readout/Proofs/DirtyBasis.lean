import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.GateLaws
import ForShor.ShorVerification.Implementation.Compiler.Statement
import ForShor.ShorVerification.Implementation.Readout.Proofs.Locality

/-!
# Dirty reserves: register values after growth (basis level)

Growth (`zeroExtend`, `signExtend`) never checks or clears a reserve qubit: `zeroExtend` is the
identity and `signExtend` XORs the sign into the new bits (`signExtendBasis`). This file gives the
signed value of the grown register when the new bits hold an ARBITRARY value `hi`.

Notation: `w = r.width`, `hi = toNat (r.newBits n) b`, `sd = tcDecodeWidth n hi` (the new bits
read as an `n`-bit two's-complement number).

* `extToInt_grow_dirty`: after `zeroExtend` (identity), for `n ≥ 1` and `r.CanGrow n`,
  `extToInt (r.grow n) b = r.toNat b + 2^w * sd`.
  The hypothesis `n ≥ 1` cannot be dropped: `extToInt_grow_zero` shows that at `n = 0` the grown
  register is `r` itself and reads `extToInt r b`, not the unsigned `r.toNat b`
  (they differ whenever `r` reads negative; a concrete instance is in
  `Model/Standard/SemiclassicalDirtyModel.lean`).
* `extToInt_grow_signExtendBasis_dirty`: after `signExtend`, for every `n` and `r.CanGrow n`,
  `extToInt (r.grow n) (signExtendBasis r n b) = extToInt r b + s * 2^w * sd`, with
  `s = -1` if `extToInt r b < 0` and `s = 1` otherwise. The clean case `hi = 0`
  (so `sd = 0`) is `extToInt_grow_signExtendBasis` in
  `PhaseTripleProduct/Proofs/Recursion/Recursion.lean`; it is re-derived here as
  `extToInt_grow_signExtendBasis_clean`.

## D3 (basis level): the constant-arithmetic lowerers on arbitrary input

`lowerCmpGeConst` and `lowerCSubConst` (`Compiler/Statement.lean`) are compute / act /
uncompute circuits whose compute part `prep` uses the unit qubit `u = scratch.newBits 1`[0] and
`scratch.active`. This file names the basis maps of their parts on ARBITRARY input:

* `copyBitsBasis` (the basis map of `lowerCopyBitPowers`), `cmpPrepBasis` (of
  `lowerPrepareNegConst`: flip `u`, copy `N` controlled on `u`, negate `scratch`),
  `cmpDiffBasis` (prep, then `scratch += data.grow 1`), `cmpDirtyToggle` (the flag is toggled iff
  the sign qubit of `scratch` reads `0` after `cmpDiffBasis`), `csubPrepBasis` and
  `csubDirtyValue` for the controlled subtraction.
* Commutation with flipping the flag (`cmpDiffBasis_flipBit`) and with writing `data`
  (`csubPrepBasis_writeNat`): the compute parts never touch those qubits.
* Value formulas in closed form, in terms of the INPUT values only (`s` = unsigned content of
  `scratch.active`, `w = scratch.width`, `u` the unit qubit, `N < 2^w`):
  * copying `N` controlled on a set qubit XORs `N` into `scratch.active`
    (`toNat_copyBitsBasis_xor`);
  * `extToInt_cmpPrepBasis`: the prepared value is `tcWrapInt w (-(extToInt scratch b))` if
    `u = 1` on input (nothing copied), and `tcWrapInt w (-(tcDecodeWidth w (s ^^^ N)))` if
    `u = 0` (on clean input, `s = 0`, this is `-N`);
  * `extToInt_csubPrepBasis`: the same two cases selected by `u xor flag`;
  * `cmpDirtyToggle_iff_closed`: the comparator toggles iff
    `0 ≤ tcWrapInt w (p + data + 2^(data.width) * tcDecodeWidth 1 hi)`, `p` the prepared value
    above and `hi` the data reserve qubit (D1);
  * `csubDirtyValue_eq_closed`: the value written into `data`.

Nothing here is quantum: these are statements about `RegEncoding` bases only.
-/

namespace Shor
namespace Dirty

variable {Basis : Type*} [RegEncoding Basis]

/-! ## Two's-complement arithmetic -/

/-- An unsigned `w`-bit value is its two's-complement reading plus `2^w` when that reading is
negative. -/
theorem natCast_eq_tcDecodeWidth_add (w u : ℕ) (hu : u < 2 ^ w) :
    (u : ℤ) = tcDecodeWidth w u + if tcDecodeWidth w u < 0 then (2 : ℤ) ^ w else 0 := by
  cases w with
  | zero =>
      have : u = 0 := by simpa using hu
      subst this; simp [tcDecodeWidth]
  | succ w =>
      simp only [tcDecodeWidth]
      split
      · simp
      · have hlt : ((u : ℤ) - ((2 ^ (w + 1) : ℕ) : ℤ)) < 0 := by
          have : (u:ℤ) < ((2 ^ (w+1) : ℕ) : ℤ) := by exact_mod_cast hu
          omega
        simp only [hlt, ↓reduceIte]; push_cast; ring

/-- Reading `u + 2^w * h` on `w + n` bits (`n ≥ 1`, `u < 2^w`, `h < 2^n`): the low part is
unsigned, the high part signed. -/
theorem tcDecodeWidth_append (w n u h : ℕ) (hn : 0 < n) (hu : u < 2 ^ w) (hh : h < 2 ^ n) :
    tcDecodeWidth (w + n) (u + 2 ^ w * h) = (u : ℤ) + 2 ^ w * tcDecodeWidth n h := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show w + (m + 1) = (w + m) + 1 by omega]
  simp only [tcDecodeWidth]
  have hpw : (2:ℕ) ^ (w + m) = 2 ^ w * 2 ^ m := pow_add 2 w m
  have hpw1 : (2:ℕ) ^ (w + m + 1) = 2 ^ w * 2 ^ (m + 1) := by rw [← pow_add]; ring_nf
  by_cases hm : h < 2 ^ m
  · have hlt : u + 2 ^ w * h < 2 ^ (w + m) := by
      rw [hpw]
      have : 2 ^ w * h + 2 ^ w ≤ 2 ^ w * 2 ^ m := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hm
      omega
    simp only [hlt, hm, ↓reduceDIte]; push_cast; ring
  · have hge : ¬ u + 2 ^ w * h < 2 ^ (w + m) := by
      rw [hpw]
      have : 2 ^ w * 2 ^ m ≤ 2 ^ w * h := Nat.mul_le_mul_left _ (by omega)
      omega
    simp only [hge, hm, ↓reduceDIte]; rw [hpw1]; push_cast; ring

/-- Complementing all `n ≥ 1` bits maps the two's-complement reading `v` to `-1 - v`. -/
theorem tcDecodeWidth_complement (n h : ℕ) (hn : 0 < n) (hh : h < 2 ^ n) :
    tcDecodeWidth n (2 ^ n - 1 - h) = -1 - tcDecodeWidth n h := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [tcDecodeWidth]
  have hp : (2:ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have h1 : 1 + h ≤ 2 ^ (m + 1) := by omega
  by_cases hm : h < 2 ^ m
  · have hge : ¬ 2 ^ (m + 1) - 1 - h < 2 ^ m := by omega
    simp only [hge, hm, ↓reduceDIte]
    push_cast [Nat.sub_sub, Nat.cast_sub h1]; ring
  · have hlt : 2 ^ (m + 1) - 1 - h < 2 ^ m := by omega
    simp only [hlt, hm, ↓reduceDIte]
    push_cast [Nat.sub_sub, Nat.cast_sub h1]; ring

/-- The new bits of a register that can grow by `n` hold a value below `2^n`. -/
theorem newBits_toNat_lt (r : ExtReg) (n : ℕ) (b : Basis) (hcap : r.CanGrow n) :
    RegEncoding.toNat (r.newBits n) b < 2 ^ n := by
  have h := RegEncoding.toNat_lt_ASize (r.newBits n) b
  rwa [ASize, Gate.ExtReg.newBits_size r n hcap] at h

/-! ## D1: the grown register on dirty reserve -/

/-- **Zero extension into dirty reserve.** For `n ≥ 1` new bits that `r` can grow into
(`r.CanGrow n`), on ANY basis state `b` the grown register reads the unsigned old value plus
`2^(r.width)` times the new bits read as an `n`-bit two's-complement number. `zeroExtend` is the
identity, so this is also the value after `zeroExtend r n`. No cleanliness is assumed. Not
claimed for `n = 0` (false there, see `extToInt_grow_zero`) nor without `r.CanGrow n`. -/
theorem extToInt_grow_dirty (r : ExtReg) (n : ℕ) (b : Basis) (hcap : r.CanGrow n) (hn : 0 < n) :
    extToInt (r.grow n) b =
      (r.toNat b : ℤ) + 2 ^ r.width * tcDecodeWidth n (RegEncoding.toNat (r.newBits n) b) := by
  unfold extToInt
  rw [Gate.ExtReg.toNat_grow, ExtReg.width_grow r n hcap]
  exact tcDecodeWidth_append _ _ _ _ hn (ExtReg.toNat_lt r b) (newBits_toNat_lt r n b hcap)

/-- At `n = 0` growth changes nothing: the register reads its signed value, which is why
`extToInt_grow_dirty` needs `n ≥ 1`. -/
theorem extToInt_grow_zero (r : ExtReg) (b : Basis) :
    extToInt (r.grow 0) b = extToInt r b := by
  have hcap : r.CanGrow 0 := Nat.zero_le _
  unfold extToInt
  rw [Gate.ExtReg.toNat_grow, ExtReg.width_grow r 0 hcap]
  have := newBits_toNat_lt r 0 b hcap
  simp only [pow_zero, Nat.lt_one_iff] at this
  simp [this]

/-- **Sign extension into dirty reserve.** For `r.CanGrow n` and ANY basis state `b`, after
`signExtendBasis r n` the grown register reads the old signed value shifted by
`± 2^(r.width) * sd`, where `sd` is the ORIGINAL content of the new bits read as an `n`-bit
two's-complement number, and the sign is `-` iff the old value is negative (the new bits were
complemented). No cleanliness is assumed; for clean new bits `sd = 0`
(`extToInt_grow_signExtendBasis_clean`). -/
theorem extToInt_grow_signExtendBasis_dirty (r : ExtReg) (n : ℕ) (b : Basis)
    (hcap : r.CanGrow n) :
    extToInt (r.grow n) (signExtendBasis r n b) =
      extToInt r b +
        (if extToInt r b < 0 then (-1 : ℤ) else 1) * 2 ^ r.width *
          tcDecodeWidth n (RegEncoding.toNat (r.newBits n) b) := by
  have hhi := newBits_toNat_lt r n b hcap
  have hu := ExtReg.toNat_lt r b
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : RegEncoding.toNat (r.newBits 0) (signExtendBasis r 0 b) = 0 := by
      have := newBits_toNat_lt r 0 (signExtendBasis r 0 b) hcap
      omega
    unfold extToInt
    rw [Gate.ExtReg.toNat_grow, ExtReg.width_grow r 0 hcap, toNat_signExtendBasis, h0]
    simp [tcDecodeWidth]
  · have hval := extToInt_grow_dirty r n (signExtendBasis r n b) hcap hn
    rw [hval, toNat_signExtendBasis, toNat_newBits_signExtendBasis]
    unfold signExtendNewValue
    simp only [ASize, Gate.ExtReg.newBits_size r n hcap]
    have hcast : (r.toNat b : ℤ) = extToInt r b +
        if extToInt r b < 0 then (2 : ℤ) ^ r.width else 0 :=
      natCast_eq_tcDecodeWidth_add r.width (r.toNat b) hu
    by_cases hneg : extToInt r b < 0
    · simp only [hneg, ↓reduceIte] at hcast ⊢
      rw [tcDecodeWidth_complement n _ hn hhi, hcast]; ring
    · simp only [hneg, ↓reduceIte] at hcast ⊢
      rw [hcast]; ring

/-- The clean case (`r.FreshFor n b`): sign extension keeps the signed value. Same statement as
`extToInt_grow_signExtendBasis` (PTP recursion), here as a corollary of the dirty form. -/
theorem extToInt_grow_signExtendBasis_clean (r : ExtReg) (n : ℕ) (b : Basis)
    (hcap : r.CanGrow n) (hfresh : r.FreshFor n b) :
    extToInt (r.grow n) (signExtendBasis r n b) = extToInt r b := by
  rw [extToInt_grow_signExtendBasis_dirty r n b hcap]
  have h0 : RegEncoding.toNat (r.newBits n) b = 0 := hfresh
  rw [h0]
  cases n <;> simp [tcDecodeWidth]

/-! ## D3: basis maps of the constant-arithmetic lowerers -/

open Readout

/-- The basis map of `lowerCopyBitPowers dst ctrl bits`: one `cnotBasis ctrl dst[i]` per index
`i` of `bits` below `dst.width`. -/
def copyBitsBasis (dst : ExtReg) (ctrl : ℕ) : List ℕ → Basis → Basis
  | [], b => b
  | i :: bits, b =>
      if hi : i < dst.width then
        copyBitsBasis dst ctrl bits
          (cnotBasis ctrl (dst.active.get ⟨i, by simpa [ExtReg.width] using! hi⟩) b)
      else
        copyBitsBasis dst ctrl bits b

/-- Every indexed qubit of a register is one of its qubits. -/
theorem reg_get_mem (r : Reg) (k : Fin r.width) : r.get k ∈ r.qubits := List.get_mem _ _

/-- `cnotBasis c t` does not change any qubit other than its target. -/
theorem bit_cnotBasis_ne {c t p : ℕ} (hp : p ≠ t) (b : Basis) :
    RegEncoding.bit p (cnotBasis c t b) = RegEncoding.bit p b := by
  unfold cnotBasis
  split_ifs <;> first
    | rfl
    | exact RegEncoding.bit_writeNat_out _ _ _ _ (by simpa [qubitReg, Reg.singleton] using hp)

/-- One step of `copyBitsBasis` at an index in range. -/
theorem copyBitsBasis_cons_of_lt (dst : ExtReg) (ctrl i : ℕ) (bits : List ℕ) (b : Basis)
    (hi : i < dst.width) :
    copyBitsBasis dst ctrl (i :: bits) b = copyBitsBasis dst ctrl bits
      (cnotBasis ctrl (dst.active.get ⟨i, by simpa [ExtReg.width] using! hi⟩) b) := by
  simp only [copyBitsBasis, hi, ↓reduceDIte]

/-- One step of `copyBitsBasis` at an index out of range. -/
theorem copyBitsBasis_cons_of_not_lt (dst : ExtReg) (ctrl i : ℕ) (bits : List ℕ) (b : Basis)
    (hi : ¬ i < dst.width) :
    copyBitsBasis dst ctrl (i :: bits) b = copyBitsBasis dst ctrl bits b := by
  simp only [copyBitsBasis, hi, ↓reduceDIte]

/-- Copying never touches a qubit other than the control and outside `dst.active`, so it
commutes with flipping such a qubit. -/
theorem copyBitsBasis_flipBit (dst : ExtReg) (ctrl : ℕ) (bits : List ℕ) {q : ℕ}
    (hc : q ≠ ctrl) (hd : q ∉ dst.active.qubits) (b : Basis) :
    copyBitsBasis dst ctrl bits (flipBit q b) = flipBit q (copyBitsBasis dst ctrl bits b) := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      by_cases hi : i < dst.width
      · rw [copyBitsBasis_cons_of_lt _ _ _ _ _ hi, copyBitsBasis_cons_of_lt _ _ _ _ _ hi,
          cnotBasis_flipBit hc (fun e => hd (e ▸ reg_get_mem _ _)), ih]
      · rw [copyBitsBasis_cons_of_not_lt _ _ _ _ _ hi, copyBitsBasis_cons_of_not_lt _ _ _ _ _ hi,
          ih]

/-- With a control qubit reading `0`, copying is the identity. -/
theorem copyBitsBasis_of_ctrl_false (dst : ExtReg) (ctrl : ℕ) (bits : List ℕ) (b : Basis)
    (hc : RegEncoding.bit ctrl b = false) :
    copyBitsBasis dst ctrl bits b = b := by
  induction bits with
  | nil => rfl
  | cons i bits ih =>
      by_cases hi : i < dst.width
      · rw [copyBitsBasis_cons_of_lt _ _ _ _ _ hi,
          show cnotBasis ctrl _ b = b by unfold cnotBasis; simp [hc]]
        exact ih
      · rw [copyBitsBasis_cons_of_not_lt _ _ _ _ _ hi]; exact ih

/-- `cnotBasis` commutes with writing a register that contains neither of its qubits. -/
theorem cnotBasis_writeNat {R : Reg} {c t : ℕ} (hc : c ∉ R.qubits) (ht : t ∉ R.qubits)
    (v : ℕ) (b : Basis) :
    cnotBasis c t (RegEncoding.writeNat R v b) = RegEncoding.writeNat R v (cnotBasis c t b) := by
  unfold cnotBasis
  rw [RegEncoding.bit_writeNat_out _ _ _ _ hc, RegEncoding.bit_writeNat_out _ _ _ _ ht]
  have hd : Disjoint (qubitReg t) R := by
    simpa [Disjoint, qubitReg, Reg.singleton] using ht
  split_ifs <;> first | rfl | exact writeNat_comm_of_disjoint _ _ hd _ _ _

/-- Copying commutes with writing a register disjoint from the control and from `dst.active`. -/
theorem copyBitsBasis_writeNat (dst : ExtReg) (ctrl : ℕ) (bits : List ℕ) {R : Reg}
    (hc : ctrl ∉ R.qubits) (hd : Disjoint dst.active R) (v : ℕ) (b : Basis) :
    copyBitsBasis dst ctrl bits (RegEncoding.writeNat R v b)
      = RegEncoding.writeNat R v (copyBitsBasis dst ctrl bits b) := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      by_cases hi : i < dst.width
      · rw [copyBitsBasis_cons_of_lt _ _ _ _ _ hi, copyBitsBasis_cons_of_lt _ _ _ _ _ hi,
          cnotBasis_writeNat hc (fun h => hd (reg_get_mem _ _) h), ih]
      · rw [copyBitsBasis_cons_of_not_lt _ _ _ _ _ hi, copyBitsBasis_cons_of_not_lt _ _ _ _ _ hi,
          ih]

/-- Copying does not change a register whose qubits avoid `dst.active`. -/
theorem toNat_copyBitsBasis (dst : ExtReg) (ctrl : ℕ) (bits : List ℕ) {R : Reg}
    (hd : Disjoint dst.active R) (b : Basis) :
    RegEncoding.toNat R (copyBitsBasis dst ctrl bits b) = RegEncoding.toNat R b := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      by_cases hi : i < dst.width
      · rw [copyBitsBasis_cons_of_lt _ _ _ _ _ hi, ih]
        refine toNat_congr_bits' R fun p hp => ?_
        exact bit_cnotBasis_ne (fun e => hd (reg_get_mem _ _) (e ▸ hp)) b
      · rw [copyBitsBasis_cons_of_not_lt _ _ _ _ _ hi]; exact ih b

/-- `negateBasis r` commutes with writing a register disjoint from `r.active`. -/
theorem negateBasis_writeNat {r : ExtReg} {R : Reg} (hd : Disjoint r.active R) (v : ℕ)
    (b : Basis) :
    negateBasis r (RegEncoding.writeNat R v b) = RegEncoding.writeNat R v (negateBasis r b) := by
  unfold negateBasis
  have : extToInt r (RegEncoding.writeNat R v b) = extToInt r b := by
    simp only [extToInt, ExtReg.toNat, RegEncoding.toNat_left_write_right _ _ hd]
  rw [this]
  exact writeNat_comm_of_disjoint _ _ hd _ _ _

/-- The unit qubit `u` (first reserve qubit of `scratch`) is a reserve qubit of `scratch`. -/
theorem unitQubit_mem_reserve (scratch : ExtReg) (hcap : scratch.CanGrow 1) :
    constArithmeticUnitQubit scratch hcap ∈ scratch.reserve.qubits :=
  List.mem_of_mem_take (List.get_mem _ _)

/-- The unit qubit is not an active qubit of `scratch`. -/
theorem unitQubit_not_mem_active (scratch : ExtReg) (hcap : scratch.CanGrow 1) :
    constArithmeticUnitQubit scratch hcap ∉ scratch.active.qubits := fun h =>
  scratch.active_reserve_disjoint h (unitQubit_mem_reserve scratch hcap)

section Workspace

variable {N : ℕ} {data scratch : ExtReg} {flag : ℕ}

/-- `data.active` and `scratch.active` are disjoint. -/
theorem ws_data_scratch_active (h : ConstArithmeticWorkspace N data scratch flag) :
    Disjoint data.active scratch.active := fun _ ha hs =>
  h.data_scratch_disjoint (List.mem_append_left _ ha) (List.mem_append_left _ hs)

/-- `(data.grow 1).active` and `scratch.active` are disjoint. -/
theorem ws_dataGrow_scratch_active (h : ConstArithmeticWorkspace N data scratch flag) :
    Disjoint (data.grow 1).active scratch.active := fun q ha hs => by
  have ho : q ∈ (data.grow 1).ownedQubits := List.mem_append_left _ ha
  rw [Gate.ExtReg.ownedQubits_grow] at ho
  exact h.data_scratch_disjoint ho (List.mem_append_left _ hs)

/-- The unit qubit is not an active qubit of `data.grow 1` (nor of `data`). -/
theorem ws_unit_not_mem_dataGrow (h : ConstArithmeticWorkspace N data scratch flag) :
    constArithmeticUnitQubit scratch h.scratch_can_grow ∉ (data.grow 1).active.qubits :=
  fun ha => by
    have ho : _ ∈ (data.grow 1).ownedQubits := List.mem_append_left _ ha
    rw [Gate.ExtReg.ownedQubits_grow] at ho
    exact h.data_scratch_disjoint ho
      (List.mem_append_right _ (unitQubit_mem_reserve scratch h.scratch_can_grow))

/-- The unit qubit is not an active qubit of `data`. -/
theorem ws_unit_not_mem_data (h : ConstArithmeticWorkspace N data scratch flag) :
    constArithmeticUnitQubit scratch h.scratch_can_grow ∉ data.active.qubits :=
  fun ha => h.data_scratch_disjoint (List.mem_append_left _ ha)
      (List.mem_append_right _ (unitQubit_mem_reserve scratch h.scratch_can_grow))

/-- The flag is not the unit qubit. -/
theorem ws_flag_ne_unit (h : ConstArithmeticWorkspace N data scratch flag) :
    flag ≠ constArithmeticUnitQubit scratch h.scratch_can_grow := fun e =>
  not_mem_reserve h.flag_not_scratch (e ▸ unitQubit_mem_reserve scratch h.scratch_can_grow)

/-- The flag is not an active qubit of `data.grow 1`. -/
theorem ws_flag_not_mem_dataGrow (h : ConstArithmeticWorkspace N data scratch flag) :
    flag ∉ (data.grow 1).active.qubits :=
  not_mem_active (by rw [Gate.ExtReg.ownedQubits_grow]; exact h.flag_not_data)

end Workspace

/-- The basis map of `lowerPrepareNegConst N scratch hcap` on an ARBITRARY basis state: flip the
unit qubit `u`, copy the bits of `N` into `scratch.active` controlled on `u`, negate
`scratch`. -/
def cmpPrepBasis (N : ℕ) (scratch : ExtReg) (hcap : scratch.CanGrow 1) (b : Basis) : Basis :=
  negateBasis scratch
    (copyBitsBasis scratch (constArithmeticUnitQubit scratch hcap) N.bitIndices
      (flipBit (constArithmeticUnitQubit scratch hcap) b))

/-- The basis map of `prep` followed by the difference `scratch += data.grow 1` in
`lowerCmpGeConst`. -/
noncomputable def cmpDiffBasis (N : ℕ) (data scratch : ExtReg) (hcap : scratch.CanGrow 1)
    (b : Basis) : Basis :=
  addScaledBasis scratch (data.grow 1) false 0 (cmpPrepBasis N scratch hcap b)

/-- The sign qubit of `scratch` read by `lowerCmpGeConst` (its top active qubit). -/
def cmpSignQubit (scratch : ExtReg) (hpos : 0 < scratch.width) : ℕ :=
  scratch.active.get ⟨scratch.width - 1, by
    have hlt : scratch.width - 1 < scratch.width := Nat.sub_lt hpos (by omega)
    simpa [ExtReg.width, regSize] using hlt⟩

/-- Whether `lowerCmpGeConst` toggles the flag on input `b` (any `b`): iff the sign qubit of
`scratch` reads `0` after `prep` and the difference. -/
noncomputable def cmpDirtyToggle (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : Basis) : Bool :=
  !RegEncoding.bit (cmpSignQubit scratch h.scratch_positive)
    (cmpDiffBasis N data scratch h.scratch_can_grow b)

/-- The flag qubit is outside every register the compute part of `lowerCmpGeConst` touches, so
that part commutes with flipping the flag. -/
theorem cmpDiffBasis_flipBit (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : Basis) :
    cmpDiffBasis N data scratch h.scratch_can_grow (flipBit flag b)
      = flipBit flag (cmpDiffBasis N data scratch h.scratch_can_grow b) := by
  have hfs : flag ∉ scratch.active.qubits := not_mem_active h.flag_not_scratch
  unfold cmpDiffBasis cmpPrepBasis
  rw [flipBit_comm, copyBitsBasis_flipBit _ _ _ (ws_flag_ne_unit h) hfs,
    negateBasis_flipBit hfs, addScaledBasis_flipBit hfs (ws_flag_not_mem_dataGrow h)]

/-- The sign qubit of a register of positive width reads `1` iff the register is negative. -/
theorem bit_cmpSignQubit (e : ExtReg) (hpos : 0 < e.width) (b : Basis) :
    RegEncoding.bit (cmpSignQubit e hpos) b = decide (extToInt e b < 0) := by
  have hw : e.width = (e.width - 1) + 1 := by omega
  unfold cmpSignQubit
  erw [RegEncoding.bit_eq_testBit_toNat]
  change Nat.testBit (e.toNat b) (e.width - 1) = _
  have hlt : e.toNat b < 2 ^ ((e.width - 1) + 1) := by rw [← hw]; exact e.toNat_lt b
  unfold extToInt
  rw [hw]
  simp only [tcDecodeWidth]
  rw [show e.width - 1 + 1 - 1 = e.width - 1 by omega]
  by_cases hs : e.toNat b < 2 ^ (e.width - 1)
  · rw [Nat.testBit_lt_two_pow hs]
    simp [hs]
  · have hlo : 1 * 2 ^ (e.width - 1) ≤ e.toNat b := by simpa using Nat.le_of_not_gt hs
    have hhi : e.toNat b < (1 + 1) * 2 ^ (e.width - 1) := by
      simpa [pow_succ, Nat.mul_comm] using hlt
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt_le hlo hhi]
    simp only [hs, ↓reduceDIte, Nat.one_mod, decide_true]
    symm
    simp only [decide_eq_true_eq]
    have : (e.toNat b : ℤ) < ((2 ^ (e.width - 1 + 1) : ℕ) : ℤ) := by exact_mod_cast hlt
    omega

/-- **D3, toggle condition on any input (basis-map form; the fully closed form in input values
is `cmpDirtyToggle_iff_closed`).** `lowerCmpGeConst` toggles the flag iff
`tcWrapInt scratch.width (p + extToInt (data.grow 1) b) ≥ 0`, where `p` is the signed value of
`scratch` after `prep` (`cmpPrepBasis`). The value `extToInt (data.grow 1) b` on dirty
`data.newBits 1` is given by `extToInt_grow_dirty`. Hypothesis: the static workspace record
`ConstArithmeticWorkspace` (no cleanliness). -/
theorem cmpDirtyToggle_iff (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : Basis) :
    cmpDirtyToggle N data scratch flag h b = true ↔
      0 ≤ tcWrapInt scratch.width
        (extToInt scratch (cmpPrepBasis N scratch h.scratch_can_grow b)
          + extToInt (data.grow 1) b) := by
  have hDS := ws_dataGrow_scratch_active h
  have hdisj : ExtReg.ActiveDisjoint scratch (data.grow 1) := fun q hs hd => hDS hd hs
  have hframe : extToInt (data.grow 1) (cmpPrepBasis N scratch h.scratch_can_grow b)
      = extToInt (data.grow 1) b := by
    unfold cmpPrepBasis
    rw [extToInt_negateBasis_of_activeDisjoint scratch (data.grow 1) _ hDS]
    simp only [extToInt, ExtReg.toNat]
    rw [toNat_copyBitsBasis _ _ _ (fun q hs hd => hDS hd hs),
      toNat_flipBit (ws_unit_not_mem_dataGrow h)]
  unfold cmpDirtyToggle cmpDiffBasis
  rw [bit_cmpSignQubit, extToInt_addScaledBasis_dst _ _ _ _ _ hdisj]
  simp only [addScaledValue, hframe, Bool.false_eq_true, ↓reduceIte, pow_zero, mul_one, one_mul,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt]

/-- **D3, `prep` with the unit qubit already set.** If `u` reads `1` on input, `prep` clears it,
copies nothing, and only negates `scratch`: the prepared value is `-s` wrapped, `s` the input
value of `scratch` (NOT `-N` as on clean input). -/
theorem extToInt_cmpPrepBasis_of_unit_set (N : ℕ) (scratch : ExtReg) (hcap : scratch.CanGrow 1)
    (b : Basis) (hu : RegEncoding.bit (constArithmeticUnitQubit scratch hcap) b = true) :
    extToInt scratch (cmpPrepBasis N scratch hcap b)
      = tcWrapInt scratch.width (-extToInt scratch b) := by
  have hua := unitQubit_not_mem_active scratch hcap
  unfold cmpPrepBasis
  rw [extToInt_negateBasis, copyBitsBasis_of_ctrl_false _ _ _ _ (by rw [bit_flipBit_self, hu]; rfl),
    extToInt_flipBit hua]

/-- The basis map of the compute part of `lowerCSubConst` on an ARBITRARY basis state:
`u ^= flag`, copy `N` into `scratch.active` controlled on `u`, negate `scratch`. -/
def csubPrepBasis (N : ℕ) (scratch : ExtReg) (flag : ℕ) (hcap : scratch.CanGrow 1)
    (b : Basis) : Basis :=
  negateBasis scratch
    (copyBitsBasis scratch (constArithmeticUnitQubit scratch hcap) N.bitIndices
      (cnotBasis flag (constArithmeticUnitQubit scratch hcap) b))

/-- The value `lowerCSubConst` writes into `data.active` on input `b` (any `b`):
`data + p` modulo `2^(data.width)`, with `p` the signed value of `scratch` after the compute
part. -/
noncomputable def csubDirtyValue (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (hcap : scratch.CanGrow 1) (b : Basis) : ℕ :=
  tcModWidth data.width
    (extToInt data b + extToInt scratch (csubPrepBasis N scratch flag hcap b))

/-- The compute part of `lowerCSubConst` commutes with writing `data.active`. -/
theorem csubPrepBasis_writeNat (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (v : ℕ) (b : Basis) :
    csubPrepBasis N scratch flag h.scratch_can_grow (RegEncoding.writeNat data.active v b)
      = RegEncoding.writeNat data.active v (csubPrepBasis N scratch flag h.scratch_can_grow b) := by
  unfold csubPrepBasis
  rw [cnotBasis_writeNat (not_mem_active h.flag_not_data) (ws_unit_not_mem_data h),
    copyBitsBasis_writeNat _ _ _ (ws_unit_not_mem_data h)
      (fun q hs hd => ws_data_scratch_active h hd hs),
    negateBasis_writeNat (fun q hs hd => ws_data_scratch_active h hd hs)]

/-- The compute part of `lowerCSubConst` does not change `data`. -/
theorem extToInt_data_csubPrepBasis (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : Basis) :
    extToInt data (csubPrepBasis N scratch flag h.scratch_can_grow b) = extToInt data b := by
  have hDS := ws_data_scratch_active h
  unfold csubPrepBasis
  rw [extToInt_negateBasis_of_activeDisjoint scratch data _ hDS]
  simp only [extToInt, ExtReg.toNat]
  rw [toNat_copyBitsBasis _ _ _ (fun q hs hd => hDS hd hs)]
  congr 1
  refine toNat_congr_bits' _ fun p hp => bit_cnotBasis_ne (fun e => ?_) b
  rw [e] at hp
  exact ws_unit_not_mem_data h hp

/-! ## D3: closed forms of the prepared values -/

/-- `cnotBasis c t` XORs the control into the target (for `c ≠ t`). -/
theorem bit_cnotBasis_target {c t : ℕ} (hct : c ≠ t) (b : Basis) :
    RegEncoding.bit t (cnotBasis c t b) = xor (RegEncoding.bit t b) (RegEncoding.bit c b) := by
  unfold cnotBasis
  simp only [hct, ↓reduceIte]
  cases hcb : RegEncoding.bit c b
  · simp
  · simp only [↓reduceIte]
    rw [bit_writeNat_qubitReg _ _ _ (by split <;> omega)]
    cases RegEncoding.bit t b <;> simp

/-- Copying the index list `L` (duplicate-free) controlled on a set qubit outside `dst.active`
flips exactly the qubits of `dst.active` whose index is in `L`. -/
theorem bit_copyBitsBasis_get (dst : ExtReg) (ctrl : ℕ) (L : List ℕ) (hL : L.Nodup)
    (hc : ctrl ∉ dst.active.qubits) (b : Basis) (hb : RegEncoding.bit ctrl b = true)
    (j : Fin (regSize dst.active)) :
    RegEncoding.bit (dst.active.get j) (copyBitsBasis dst ctrl L b)
      = xor (RegEncoding.bit (dst.active.get j) b) (decide (j.1 ∈ L)) := by
  induction L generalizing b with
  | nil => simp [copyBitsBasis]
  | cons i L ih =>
      obtain ⟨hiL, hL'⟩ := List.nodup_cons.mp hL
      by_cases hi : i < dst.width
      · rw [copyBitsBasis_cons_of_lt _ _ _ _ _ hi]
        have hct : ctrl ≠ dst.active.get ⟨i, by simpa [ExtReg.width] using! hi⟩ :=
          fun e => hc (e ▸ reg_get_mem _ _)
        rw [ih hL' _ (by rw [bit_cnotBasis_ne hct]; exact hb)]
        by_cases hji : j.1 = i
        · have hg : dst.active.get j = dst.active.get ⟨i, by simpa [ExtReg.width] using! hi⟩ := by
            simp [Reg.get, hji]
          rw [hg, bit_cnotBasis_target hct, hb, ← hg]
          simp [hji, hiL]
        · have hg : dst.active.get j ≠ dst.active.get ⟨i, by simpa [ExtReg.width] using! hi⟩ := by
            intro e
            apply hji
            have := (List.Nodup.getElem_inj_iff dst.active.nodup).mp e
            simpa using this
          rw [bit_cnotBasis_ne hg]
          simp [hji]
      · rw [copyBitsBasis_cons_of_not_lt _ _ _ _ _ hi, ih hL' _ hb]
        have hji : j.1 ≠ i := by
          have := j.2; simp only [ExtReg.width, regSize] at hi this ⊢; omega
        simp [hji]

/-- **Copy = XOR.** Copying `N < 2^(dst.width)` controlled on a set qubit outside `dst.active`
XORs `N` into the unsigned content of `dst.active`. -/
theorem toNat_copyBitsBasis_xor (dst : ExtReg) (ctrl N : ℕ) (hN : N < 2 ^ dst.width)
    (hc : ctrl ∉ dst.active.qubits) (b : Basis) (hb : RegEncoding.bit ctrl b = true) :
    RegEncoding.toNat dst.active (copyBitsBasis dst ctrl N.bitIndices b)
      = RegEncoding.toNat dst.active b ^^^ N := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < regSize dst.active
  · rw [← RegEncoding.bit_eq_testBit_toNat dst.active _ ⟨k, hk⟩, Nat.testBit_xor,
      ← RegEncoding.bit_eq_testBit_toNat dst.active b ⟨k, hk⟩,
      bit_copyBitsBasis_get dst ctrl _ Nat.bitIndices_nodup hc b hb ⟨k, hk⟩]
    simp
  · push Not at hk
    have hw : regSize dst.active = dst.width := rfl
    have l1 := RegEncoding.toNat_lt_ASize dst.active (copyBitsBasis dst ctrl N.bitIndices b)
    have l2 := RegEncoding.toNat_lt_ASize dst.active b
    rw [ASize] at l1 l2
    have l3 : RegEncoding.toNat dst.active b ^^^ N < 2 ^ regSize dst.active :=
      Nat.xor_lt_two_pow l2 (hw ▸ hN)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le l1 (Nat.pow_le_pow_right (by norm_num) hk)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le l3 (Nat.pow_le_pow_right (by norm_num) hk))]

/-- The value after "copy `N` controlled on `u`, then negate", on any basis state `c`. -/
theorem extToInt_negate_copy (N : ℕ) (scratch : ExtReg) (u : ℕ) (hu : u ∉ scratch.active.qubits)
    (hN : N < 2 ^ scratch.width) (c : Basis) :
    extToInt scratch (negateBasis scratch (copyBitsBasis scratch u N.bitIndices c))
      = if RegEncoding.bit u c then
          tcWrapInt scratch.width (-(tcDecodeWidth scratch.width
            (RegEncoding.toNat scratch.active c ^^^ N)))
        else tcWrapInt scratch.width (-extToInt scratch c) := by
  rw [extToInt_negateBasis]
  cases hc : RegEncoding.bit u c
  · rw [copyBitsBasis_of_ctrl_false _ _ _ _ hc]; simp
  · simp only [↓reduceIte]
    congr 2
    simp only [extToInt, ExtReg.toNat, ExtReg.width]
    rw [toNat_copyBitsBasis_xor scratch u N hN hu c hc]

/-- **D3, prepared value of the comparator, any input, closed form.** For `N < 2^(scratch.width)`:
if the unit qubit `u` reads `1` on input, `prep` clears it, copies nothing and negates:
`-(extToInt scratch b)` wrapped; if `u` reads `0`, `prep` sets it, XORs `N` into
`scratch.active` and negates: `-(tcDecodeWidth w (s ^^^ N))` wrapped, `s` the unsigned input
content of `scratch.active`. (Clean input `s = 0, u = 0` gives `-N`.) -/
theorem extToInt_cmpPrepBasis (N : ℕ) (scratch : ExtReg) (hcap : scratch.CanGrow 1)
    (hN : N < 2 ^ scratch.width) (b : Basis) :
    extToInt scratch (cmpPrepBasis N scratch hcap b)
      = if RegEncoding.bit (constArithmeticUnitQubit scratch hcap) b then
          tcWrapInt scratch.width (-extToInt scratch b)
        else tcWrapInt scratch.width (-(tcDecodeWidth scratch.width
          (RegEncoding.toNat scratch.active b ^^^ N))) := by
  have hua := unitQubit_not_mem_active scratch hcap
  unfold cmpPrepBasis
  rw [extToInt_negate_copy N scratch _ hua hN, bit_flipBit_self, extToInt_flipBit hua,
    toNat_flipBit hua]
  cases RegEncoding.bit (constArithmeticUnitQubit scratch hcap) b <;> simp

/-- **D3, comparator toggle, fully closed form.** Under the static workspace record only, the
lowered comparator toggles the flag on input `b` iff
`0 ≤ tcWrapInt w (p + d + 2^(data.width) * tcDecodeWidth 1 hi)`, where `w = scratch.width`,
`d` is the unsigned value of `data.active`, `hi` the content of the data reserve qubit
(`data.newBits 1`), and `p` the prepared value of `extToInt_cmpPrepBasis` (the case split on the
input value of `u`). Everything on the right is an input value. -/
theorem cmpDirtyToggle_iff_closed (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : Basis) :
    cmpDirtyToggle N data scratch flag h b = true ↔
      0 ≤ tcWrapInt scratch.width
        ((if RegEncoding.bit (constArithmeticUnitQubit scratch h.scratch_can_grow) b then
            tcWrapInt scratch.width (-extToInt scratch b)
          else tcWrapInt scratch.width (-(tcDecodeWidth scratch.width
            (RegEncoding.toNat scratch.active b ^^^ N))))
          + ((RegEncoding.toNat data.active b : ℤ) + 2 ^ data.width *
              tcDecodeWidth 1 (RegEncoding.toNat (data.newBits 1) b))) := by
  have hN : N < 2 ^ scratch.width := lt_of_lt_of_le h.constant_fits
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
  rw [cmpDirtyToggle_iff, extToInt_cmpPrepBasis N scratch _ hN,
    extToInt_grow_dirty data 1 b h.data_can_grow (by omega)]
  rfl

/-- **D3, prepared value of the controlled subtraction, any input, closed form.** The compute
part sets `u := u xor flag`, then copies and negates; so the prepared value is
`-(tcDecodeWidth w (s ^^^ N))` wrapped if `u xor flag` reads `1`, and `-(extToInt scratch b)`
wrapped otherwise. (Clean input `u = 0, s = 0`: `-N` if the flag is set, `0` if not.) -/
theorem extToInt_csubPrepBasis (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : Basis) :
    extToInt scratch (csubPrepBasis N scratch flag h.scratch_can_grow b)
      = if xor (RegEncoding.bit (constArithmeticUnitQubit scratch h.scratch_can_grow) b)
            (RegEncoding.bit flag b) then
          tcWrapInt scratch.width (-(tcDecodeWidth scratch.width
            (RegEncoding.toNat scratch.active b ^^^ N)))
        else tcWrapInt scratch.width (-extToInt scratch b) := by
  have hN : N < 2 ^ scratch.width := lt_of_lt_of_le h.constant_fits
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
  have hua := unitQubit_not_mem_active scratch h.scratch_can_grow
  have hfu := ws_flag_ne_unit h
  unfold csubPrepBasis
  rw [extToInt_negate_copy N scratch _ hua hN, bit_cnotBasis_target hfu]
  have hs : RegEncoding.toNat scratch.active
      (cnotBasis flag (constArithmeticUnitQubit scratch h.scratch_can_grow) b)
      = RegEncoding.toNat scratch.active b :=
    toNat_congr_bits' _ fun p hp => bit_cnotBasis_ne (fun e => by rw [e] at hp; exact hua hp) b
  have he : extToInt scratch
      (cnotBasis flag (constArithmeticUnitQubit scratch h.scratch_can_grow) b)
      = extToInt scratch b := by simp only [extToInt, ExtReg.toNat, hs]
  rw [hs, he]

/-- **D3, the value written into `data` by the controlled subtraction, closed form:**
`data + p` modulo `2^(data.width)`, `p` the prepared value of `extToInt_csubPrepBasis`. -/
theorem csubDirtyValue_eq_closed (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : Basis) :
    csubDirtyValue N data scratch flag h.scratch_can_grow b
      = tcModWidth data.width (extToInt data b +
          if xor (RegEncoding.bit (constArithmeticUnitQubit scratch h.scratch_can_grow) b)
              (RegEncoding.bit flag b) then
            tcWrapInt scratch.width (-(tcDecodeWidth scratch.width
              (RegEncoding.toNat scratch.active b ^^^ N)))
          else tcWrapInt scratch.width (-extToInt scratch b)) := by
  unfold csubDirtyValue
  rw [extToInt_csubPrepBasis N data scratch flag h b]

end Dirty
end Shor
