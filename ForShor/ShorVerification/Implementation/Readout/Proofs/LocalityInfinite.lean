import ForShor.ShorVerification.Implementation.Readout.Proofs.Locality
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Readout: locality for start kets that differ at INFINITELY many qubits

`MGate.recordProb_of_agree` (`Proofs/Locality.lean`) needs the two start kets to differ at
finitely many qubits (`hfin`), because it flips one unnamed qubit at a time. That hypothesis is
NOT vacuous: `RegEncoding` has an extensionality law (`basis_ext`: a basis state is determined
by its bits) but no finiteness law, and the concrete model basis `Model.ModelBasis := ℕ → Bool`
contains basis states that differ at infinitely many qubits (e.g. `fun _ => false` and
`fun _ => true`). This file removes `hfin`.

## Route (R1, normal form via matrix elements)

Fix a register `R` (an ordered duplicate-free list of qubits) containing everything a program
names. Write `AgreeOff R c b` for "`c` and `b` carry the same bit at every qubit outside `R`"
and `AgreeOn R b b'` for "the same bit at every qubit of `R`".

`LocalWith R L h` says: for all basis states `b`, `c`,
`⟪|c⟩, L |b⟩⟫ = if AgreeOff R c b then h (toNat R b) (toNat R c) else 0`.
So `L` never changes a qubit outside `R`, and its matrix on the `2^|R|`-dimensional block of
kets around `b` is one fixed matrix `h` that sees only the `R`-contents of `b` and `c`. Then
`L |b⟩ = ∑ w, h (toNat R b) w • |writeNat R w b⟩` (`LocalWith.expand`), and by orthonormality
`‖L |b⟩‖² = ∑ w, |h (toNat R b) w|²` depends on `b` only through `toNat R b`
(`LocalWith.norm_sq_eq`): two kets that agree on `R` (and differ ANYWHERE else, infinitely often
included) give the same norm.

`LocalWith` is closed under composition (`LocalWith.comp`) and under `adj` (`LocalWith.adj`:
`⟪x, eval (adj U) y⟫ = ⟪eval U x, y⟫` because every gate is an invertible isometry), holds for
every ket law of the classes whose operands lie in `R` (`localOn_of_sum`, built on the
`LocalMap` facts for every basis map), for the Born projectors and the phase gate, hence for
every `Gate` without an `idealCtrlModMul` node (`gate_localOn`). For `MGate` programs every
branch `r` of the output is `L (ψ pre)` for one record `pre` and one such `L`
(`mgate_mlocal`). The start state `MState.init |b⟩` then gives `recordProb = ‖L |b⟩‖²` or `0`.

Finally `MGate.qubitSupport` is finite (`MGate.qubitSupport_finite`), so `R` can be taken to
be exactly the support.

No new axiom, no class field: only the existing ket laws, `basis_ext`, `bit_writeNat_in/out`,
`toNat_writeNat_of_lt`, `bit_eq_testBit_toNat`, orthonormality of kets and `state_induction`.
-/

namespace Shor
namespace Readout

open MeasureClass

/-! ## Agreement on / off a register -/

section Basis
variable {B : Type*} [RegEncoding B]

/-- `c` and `b` carry the same bit at every qubit OUTSIDE `R`. -/
def AgreeOff (R : Reg) (c b : B) : Prop :=
  ∀ p, p ∉ R.qubits → RegEncoding.bit p c = RegEncoding.bit p b

/-- `b` and `b'` carry the same bit at every qubit OF `R`. -/
def AgreeOn (R : Reg) (b b' : B) : Prop :=
  ∀ p ∈ R.qubits, RegEncoding.bit p b = RegEncoding.bit p b'

theorem AgreeOff.refl (R : Reg) (b : B) : AgreeOff R b b := fun _ _ => rfl

theorem AgreeOff.symm {R : Reg} {c b : B} (h : AgreeOff R c b) : AgreeOff R b c :=
  fun p hp => (h p hp).symm

theorem AgreeOff.trans {R : Reg} {a c b : B} (h1 : AgreeOff R a c) (h2 : AgreeOff R c b) :
    AgreeOff R a b := fun p hp => (h1 p hp).trans (h2 p hp)

theorem AgreeOn.refl (R : Reg) (b : B) : AgreeOn R b b := fun _ _ => rfl

theorem AgreeOn.symm {R : Reg} {b b' : B} (h : AgreeOn R b b') : AgreeOn R b' b :=
  fun p hp => (h p hp).symm

theorem AgreeOn.trans {R : Reg} {a b c : B} (h1 : AgreeOn R a b) (h2 : AgreeOn R b c) :
    AgreeOn R a c := fun p hp => (h1 p hp).trans (h2 p hp)

/-- A write to a register inside `R` changes no bit outside `R`. -/
theorem agreeOff_writeNat_of_sub {R r : Reg} (hr : ∀ p ∈ r.qubits, p ∈ R.qubits) (v : ℕ)
    (b : B) : AgreeOff R (RegEncoding.writeNat r v b) b := fun p hp =>
  RegEncoding.bit_writeNat_out _ _ _ _ (fun h => hp (hr p h))

theorem agreeOff_writeNat (R : Reg) (v : ℕ) (b : B) :
    AgreeOff R (RegEncoding.writeNat R v b) b :=
  agreeOff_writeNat_of_sub (fun _ h => h) v b

/-- Writing the same value into ANY register preserves agreement on `R`. -/
theorem AgreeOn.writeNat {R : Reg} (r : Reg) (v : ℕ) {b b' : B} (h : AgreeOn R b b') :
    AgreeOn R (RegEncoding.writeNat r v b) (RegEncoding.writeNat r v b') := fun p hp => by
  by_cases hpr : p ∈ r.qubits
  · exact RegEncoding.bit_writeNat_in _ _ _ _ _ hpr
  · rw [RegEncoding.bit_writeNat_out _ _ _ _ hpr, RegEncoding.bit_writeNat_out _ _ _ _ hpr]
    exact h p hp

theorem AgreeOn.toNat {R r : Reg} (hr : ∀ p ∈ r.qubits, p ∈ R.qubits) {b b' : B}
    (h : AgreeOn R b b') : RegEncoding.toNat r b = RegEncoding.toNat r b' :=
  toNat_congr_bits' r fun p hp => h p (hr p hp)

theorem AgreeOn.bit {R : Reg} {p : ℕ} (hp : p ∈ R.qubits) {b b' : B} (h : AgreeOn R b b') :
    RegEncoding.bit p b = RegEncoding.bit p b' := h p hp

theorem AgreeOn.extToInt {R : Reg} {e : ExtReg} (he : ∀ p ∈ e.active.qubits, p ∈ R.qubits)
    {b b' : B} (h : AgreeOn R b b') : extToInt e b = extToInt e b' := by
  simp only [_root_.Shor.extToInt, ExtReg.toNat, h.toNat he]

theorem exists_get_of_mem_reg {R : Reg} {p : ℕ} (hp : p ∈ R.qubits) :
    ∃ i : Fin (regSize R), R.get i = p := by
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hp
  exact ⟨⟨i, hi⟩, by simpa [Reg.get] using hget⟩

/-- Equal register values mean equal bits on the register. -/
theorem agreeOn_of_toNat_eq {R : Reg} {b b' : B}
    (h : RegEncoding.toNat R b = RegEncoding.toNat R b') : AgreeOn R b b' := by
  intro p hp
  obtain ⟨i, rfl⟩ := exists_get_of_mem_reg hp
  rw [RegEncoding.bit_eq_testBit_toNat, RegEncoding.bit_eq_testBit_toNat, h]

theorem eq_of_agreeOff_agreeOn {R : Reg} {c b : B} (h1 : AgreeOff R c b) (h2 : AgreeOn R c b) :
    c = b :=
  RegEncoding.basis_ext _ _ fun p => by
    by_cases hp : p ∈ R.qubits
    · exact h2 p hp
    · exact h1 p hp

/-- Within one block (same bits outside `R`), a basis state is determined by its `R`-value. -/
theorem eq_iff_toNat_eq_of_agreeOff {R : Reg} {c d b : B} (hc : AgreeOff R c b)
    (hd : AgreeOff R d b) : c = d ↔ RegEncoding.toNat R c = RegEncoding.toNat R d := by
  constructor
  · rintro rfl; rfl
  · intro h; exact eq_of_agreeOff_agreeOn (hc.trans hd.symm) (agreeOn_of_toNat_eq h)

theorem toNat_writeNat_fin (R : Reg) (w : Fin (ASize R)) (b : B) :
    RegEncoding.toNat R (RegEncoding.writeNat R w b) = w :=
  RegEncoding.toNat_writeNat_of_lt _ _ _ w.2

/-- `c = writeNat R w b` iff `c` is in the block of `b` and has `R`-value `w`. -/
theorem eq_writeNat_iff {R : Reg} {c b : B} (w : Fin (ASize R)) :
    c = RegEncoding.writeNat R w b ↔ AgreeOff R c b ∧ RegEncoding.toNat R c = w := by
  constructor
  · rintro rfl; exact ⟨agreeOff_writeNat R _ b, toNat_writeNat_fin R w b⟩
  · rintro ⟨h1, h2⟩
    rw [eq_iff_toNat_eq_of_agreeOff h1 (agreeOff_writeNat R _ b), toNat_writeNat_fin, h2]

theorem writeNat_fin_injective (R : Reg) (b : B) :
    Function.Injective fun w : Fin (ASize R) => RegEncoding.writeNat R w b := by
  intro v w h
  apply Fin.ext
  have := congrArg (RegEncoding.toNat R) h
  simpa only [toNat_writeNat_fin] using this

/-- The canonical basis state with `R`-value `u` (zero elsewhere). -/
def canonR (R : Reg) (u : ℕ) : B := RegEncoding.writeNat R u RegEncoding.zero

theorem agreeOn_canonR (R : Reg) (b : B) : AgreeOn R b (canonR R (RegEncoding.toNat R b)) :=
  agreeOn_of_toNat_eq
    (RegEncoding.toNat_writeNat_of_lt _ _ _ (RegEncoding.toNat_lt_ASize _ _)).symm

/-- A basis map that changes no bit outside `R` and whose `R`-bits depend only on the `R`-bits
of its input. -/
structure LocalMap (R : Reg) (f : B → B) : Prop where
  off : ∀ b, AgreeOff R (f b) b
  on : ∀ b b', AgreeOn R b b' → AgreeOn R (f b) (f b')

theorem LocalMap.id (R : Reg) : LocalMap R (fun b : B => b) :=
  ⟨fun b => AgreeOff.refl R b, fun _ _ h => h⟩

/-- Writing into a sub-register a value that depends only on `R`. -/
theorem LocalMap.writeNat {R r : Reg} (hr : ∀ p ∈ r.qubits, p ∈ R.qubits) (v : B → ℕ)
    (hv : ∀ b b', AgreeOn R b b' → v b = v b') :
    LocalMap R (fun b : B => RegEncoding.writeNat r (v b) b) :=
  ⟨fun b => agreeOff_writeNat_of_sub hr _ b, fun b b' h => by
    rw [hv b b' h]; exact h.writeNat r _⟩

end Basis

/-! ### Every basis map of the gate classes is local to a register containing its operands -/

section BasisMaps
variable {B : Type*} [RegEncoding B] {R : Reg}

theorem qubitReg_sub {q : ℕ} (hq : q ∈ R.qubits) : ∀ p ∈ (qubitReg q).qubits, p ∈ R.qubits := by
  intro p hp
  rw [show p = q by simpa [qubitReg, Reg.singleton] using hp]
  exact hq

theorem localMap_flipBit {q : ℕ} (hq : q ∈ R.qubits) : LocalMap R (flipBit q : B → B) :=
  LocalMap.writeNat (qubitReg_sub hq) _ fun b b' h => by rw [h.bit hq]

theorem localMap_cnot {a t : ℕ} (ha : a ∈ R.qubits) (ht : t ∈ R.qubits) :
    LocalMap R (cnotBasis a t : B → B) := by
  refine ⟨fun b => ?_, fun b b' h => ?_⟩
  · unfold cnotBasis
    split_ifs <;> first
      | exact AgreeOff.refl R b | exact agreeOff_writeNat_of_sub (qubitReg_sub ht) _ b
  · unfold cnotBasis
    rw [h.bit ha, h.bit ht]
    split_ifs <;> first | exact h | exact h.writeNat _ _

theorem localMap_toffoli {a a' t : ℕ} (ha : a ∈ R.qubits) (ha' : a' ∈ R.qubits)
    (ht : t ∈ R.qubits) : LocalMap R (toffoliBasis a a' t : B → B) := by
  refine ⟨fun b => ?_, fun b b' h => ?_⟩
  · unfold toffoliBasis
    split_ifs <;> first
      | exact AgreeOff.refl R b | exact agreeOff_writeNat_of_sub (qubitReg_sub ht) _ b
  · unfold toffoliBasis
    rw [h.bit ha, h.bit ha', h.bit ht]
    split_ifs <;> first | exact h | exact h.writeNat _ _

theorem localMap_cmpGeConst {N f : ℕ} {data : Reg} (hd : ∀ p ∈ data.qubits, p ∈ R.qubits)
    (hf : f ∈ R.qubits) : LocalMap R (cmpGeConstBasis N data f : B → B) := by
  refine ⟨fun b => ?_, fun b b' h => ?_⟩
  · unfold cmpGeConstBasis
    split_ifs <;> first
      | exact AgreeOff.refl R b | exact agreeOff_writeNat_of_sub (qubitReg_sub hf) _ b
  · unfold cmpGeConstBasis
    rw [h.bit hf, h.toNat hd]
    split_ifs <;> first | exact h | exact h.writeNat _ _

theorem localMap_csubConst {N f : ℕ} {data : Reg} (hd : ∀ p ∈ data.qubits, p ∈ R.qubits)
    (hf : f ∈ R.qubits) : LocalMap R (csubConstBasis N data f : B → B) := by
  refine ⟨fun b => ?_, fun b b' h => ?_⟩
  · unfold csubConstBasis
    split_ifs <;> first | exact AgreeOff.refl R b | exact agreeOff_writeNat_of_sub hd _ b
  · unfold csubConstBasis
    rw [h.bit hf, h.toNat hd]
    split_ifs <;> first | exact h | exact h.writeNat _ _

theorem localMap_negate {r : ExtReg} (hr : ∀ p ∈ r.active.qubits, p ∈ R.qubits) :
    LocalMap R (negateBasis r : B → B) :=
  LocalMap.writeNat hr _ fun b b' h => by rw [h.extToInt hr]

theorem localMap_addScaled {d s : ExtReg} {neg : Bool} {sh : ℕ}
    (hd : ∀ p ∈ d.active.qubits, p ∈ R.qubits) (hs : ∀ p ∈ s.active.qubits, p ∈ R.qubits) :
    LocalMap R (addScaledBasis d s neg sh : B → B) := by
  by_cases hdis : ExtReg.ActiveDisjoint d s
  · have : (addScaledBasis d s neg sh : B → B) = fun b => RegEncoding.writeNat d.active
        (tcModWidth d.width (extToInt d b + (if neg then (-1 : ℤ) else 1) * (2 : ℤ) ^ sh
          * extToInt s b)) b := by
      funext b; unfold addScaledBasis; simp only [hdis, ↓reduceDIte]
    rw [this]
    exact LocalMap.writeNat hd _ fun b b' h => by rw [h.extToInt hd, h.extToInt hs]
  · have : (addScaledBasis d s neg sh : B → B) = fun b => b := by
      funext b; unfold addScaledBasis; simp only [hdis, ↓reduceDIte]
    rw [this]
    exact LocalMap.id R

theorem localMap_shiftL {r : ExtReg} {n : ℕ} (hr : ∀ p ∈ r.active.qubits, p ∈ R.qubits) :
    LocalMap R (shiftLBasis r n : B → B) := by
  classical
  have : (shiftLBasis r n : B → B) = fun b => RegEncoding.writeNat r.active
      (if FitsSignedWidth r.width ((2 : ℤ) ^ n * extToInt r b) then
        tcModWidth r.width ((2 : ℤ) ^ n * extToInt r b)
      else signedShiftLWord r.width n (ExtReg.toNat r b)) b := by
    funext b; unfold shiftLBasis shiftLBasisRaw; dsimp only; split_ifs <;> rfl
  rw [this]
  exact LocalMap.writeNat hr _ fun b b' h => by
    simp only [h.extToInt hr, ExtReg.toNat, h.toNat hr]

theorem localMap_shiftR {r : ExtReg} {n : ℕ} (hr : ∀ p ∈ r.active.qubits, p ∈ R.qubits) :
    LocalMap R (shiftRBasis r n : B → B) := by
  classical
  have : (shiftRBasis r n : B → B) = fun b => RegEncoding.writeNat r.active
      (if h : ∃ q : ℤ, extToInt r b = (2 : ℤ) ^ n * q ∧ FitsSignedWidth r.width q then
        tcModWidth r.width (Classical.choose h)
      else signedShiftRWord r.width n (ExtReg.toNat r b)) b := by
    funext b; unfold shiftRBasis shiftRBasisRaw; split_ifs <;> rfl
  rw [this]
  exact LocalMap.writeNat hr _ fun b b' h => by
    rw [h.extToInt hr]; simp only [ExtReg.toNat, h.toNat hr]

theorem localMap_signExtend {r : ExtReg} {n : ℕ} (hr : ∀ p ∈ r.ownedQubits, p ∈ R.qubits) :
    LocalMap R (signExtendBasis r n : B → B) := by
  have hn : ∀ p ∈ (r.newBits n).qubits, p ∈ R.qubits := fun p h =>
    hr p (List.mem_append_right _ (List.mem_of_mem_take h))
  have ha : ∀ p ∈ r.active.qubits, p ∈ R.qubits := fun p h => hr p (List.mem_append_left _ h)
  exact LocalMap.writeNat hn _ fun b b' h => by
    unfold signExtendNewValue; rw [h.extToInt ha, h.toNat hn]

theorem localMap_radixReverse {r : Reg} {m : ℕ} (hr : ∀ p ∈ r.qubits, p ∈ R.qubits) :
    LocalMap R (radixReverseBasis r m : B → B) := by
  by_cases hm : m ≤ regSize r
  · have hL : ∀ p ∈ (splitLeft r ⟨m, hm⟩).qubits, p ∈ R.qubits := fun p h =>
      hr p (List.mem_of_mem_take h)
    have hR : ∀ p ∈ (splitRight r ⟨m, hm⟩).qubits, p ∈ R.qubits := fun p h =>
      hr p (List.mem_of_mem_drop h)
    have : (radixReverseBasis r m : B → B) = fun b => RegEncoding.writeNat r
        (radixReverseIndex r m hm (RegEncoding.toNat (splitLeft r ⟨m, hm⟩) b)
          (RegEncoding.toNat (splitRight r ⟨m, hm⟩) b)) b := by
      funext b; unfold radixReverseBasis; simp only [hm, ↓reduceDIte]
    rw [this]
    exact LocalMap.writeNat hr _ fun b b' h => by rw [h.toNat hL, h.toNat hR]
  · have : (radixReverseBasis r m : B → B) = fun b => b := by
      funext b; unfold radixReverseBasis; simp only [hm, ↓reduceDIte]
    rw [this]
    exact LocalMap.id R

end BasisMaps

/-! ## Local linear maps -/

section Kets
variable {qs : QSemantics}

open Classical in
theorem inner_ket_ket (c b : qs.Basis) :
    inner ℂ (qs.ket c) (qs.ket b) = if c = b then 1 else 0 := by
  split_ifs with h
  · exact qs.ket_inner_eq_of_eq h
  · exact qs.ket_inner_eq_zero_of_ne h

/-- Two states with the same coefficient on every basis ket are equal. -/
theorem state_eq_of_inner_ket {x y : qs.State}
    (h : ∀ c, inner ℂ (qs.ket c) x = inner ℂ (qs.ket c) y) : x = y := by
  have hz : ∀ z : qs.State, inner ℂ z (x - y) = 0 := by
    intro z
    refine qs.state_induction (fun z => inner ℂ z (x - y) = 0) (by simp) ?_ ?_ ?_ z
    · intro a b ha hb; rw [inner_add_left, ha, hb, add_zero]
    · intro a z hz; rw [inner_smul_left, hz, mul_zero]
    · intro c; rw [inner_sub_right, h c, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (hz _))

end Kets

section Local
variable {qs : QSemantics} [RegEncoding qs.Basis]

open Classical in
/-- **Locality of a linear map, with its block matrix.** `L` never changes a qubit outside `R`
(its matrix element between kets that differ outside `R` is `0`), and between kets that agree
outside `R` it is `h (R-value of the input) (R-value of the output)`: a single matrix that does
not see any bit outside `R`. -/
def LocalWith (R : Reg) (L : qs.State →ₗ[ℂ] qs.State) (h : ℕ → ℕ → ℂ) : Prop :=
  ∀ b c : qs.Basis, inner ℂ (qs.ket c) (L (qs.ket b))
    = if AgreeOff R c b then h (RegEncoding.toNat R b) (RegEncoding.toNat R c) else 0

/-- `L` is local to `R` (for some block matrix). -/
def LocalOn (R : Reg) (L : qs.State →ₗ[ℂ] qs.State) : Prop := ∃ h, LocalWith R L h

/-- **Normal form.** A local map sends `|b⟩` to a combination of the `2^|R|` kets of the block
of `b`, with coefficients that depend only on `toNat R b`. -/
theorem LocalWith.expand {R : Reg} {L : qs.State →ₗ[ℂ] qs.State} {h : ℕ → ℕ → ℂ}
    (hL : LocalWith R L h) (b : qs.Basis) :
    L (qs.ket b) = ∑ w : Fin (ASize R),
      h (RegEncoding.toNat R b) w • qs.ket (RegEncoding.writeNat R w b) := by
  classical
  refine state_eq_of_inner_ket fun c => ?_
  rw [hL b c, inner_sum]
  simp_rw [inner_smul_right, inner_ket_ket]
  by_cases hA : AgreeOff R c b
  · rw [ite_eq_left hA]
    have hlt := RegEncoding.toNat_lt_ASize R c
    rw [Finset.sum_eq_single ⟨_, hlt⟩]
    · rw [ite_eq_left ((eq_writeNat_iff _).2 ⟨hA, rfl⟩), mul_one]
    · intro w _ hw
      rw [ite_eq_right, mul_zero]
      intro hc
      exact hw (Fin.ext ((eq_writeNat_iff w).1 hc).2.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right hA]
    refine (Finset.sum_eq_zero fun w _ => ?_).symm
    rw [ite_eq_right, mul_zero]
    intro hc; exact hA ((eq_writeNat_iff w).1 hc).1

/-- The kets of one block are orthonormal. -/
theorem orthonormal_block (R : Reg) (b : qs.Basis) :
    Orthonormal ℂ fun w : Fin (ASize R) => qs.ket (RegEncoding.writeNat R w b) := by
  classical
  rw [orthonormal_iff_ite]
  intro v w
  rw [inner_ket_ket]
  by_cases h : v = w
  · subst h; simp
  · rw [ite_eq_right (fun e => h (writeNat_fin_injective R b e)), ite_eq_right h]

/-- **Norm.** `‖L |b⟩‖²` depends on `b` only through its bits on `R`. -/
theorem LocalWith.norm_sq_eq {R : Reg} {L : qs.State →ₗ[ℂ] qs.State} {h : ℕ → ℕ → ℂ}
    (hL : LocalWith R L h) {b b' : qs.Basis} (hb : AgreeOn R b b') :
    ‖L (qs.ket b)‖ ^ 2 = ‖L (qs.ket b')‖ ^ 2 := by
  have ht : RegEncoding.toNat R b = RegEncoding.toNat R b' := hb.toNat (fun _ h => h)
  rw [hL.expand b, hL.expand b', ht, norm_sq_eq_re_inner (𝕜 := ℂ),
    norm_sq_eq_re_inner (𝕜 := ℂ)]
  have e1 := (orthonormal_block (qs := qs) R b).inner_sum
    (fun w => h (RegEncoding.toNat R b') w) (fun w => h (RegEncoding.toNat R b') w) Finset.univ
  have e2 := (orthonormal_block (qs := qs) R b').inner_sum
    (fun w => h (RegEncoding.toNat R b') w) (fun w => h (RegEncoding.toNat R b') w) Finset.univ
  rw [e1, e2]

theorem LocalWith.comp {R : Reg} {L₁ L₂ : qs.State →ₗ[ℂ] qs.State} {h₁ h₂ : ℕ → ℕ → ℂ}
    (hL₁ : LocalWith R L₁ h₁) (hL₂ : LocalWith R L₂ h₂) :
    LocalWith R (L₂.comp L₁) (fun u x => ∑ w : Fin (ASize R), h₁ u w * h₂ w x) := by
  classical
  have hL₂' : ∀ b c : qs.Basis, inner ℂ (qs.ket c) (L₂ (qs.ket b))
      = if AgreeOff R c b then h₂ (RegEncoding.toNat R b) (RegEncoding.toNat R c) else 0 := hL₂
  intro b c
  simp only [LinearMap.comp_apply]
  rw [hL₁.expand b, map_sum, inner_sum]
  simp_rw [map_smul, inner_smul_right, hL₂']
  by_cases hA : AgreeOff R c b
  · rw [ite_eq_left hA]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ite_eq_left (hA.trans (agreeOff_writeNat R _ b).symm), toNat_writeNat_fin]
  · rw [ite_eq_right hA]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [ite_eq_right (fun h => hA (h.trans (agreeOff_writeNat R _ b))), mul_zero]

theorem LocalOn.comp {R : Reg} {L₁ L₂ : qs.State →ₗ[ℂ] qs.State} (hL₁ : LocalOn R L₁)
    (hL₂ : LocalOn R L₂) : LocalOn R (L₂.comp L₁) := by
  obtain ⟨h₁, hL₁⟩ := hL₁
  obtain ⟨h₂, hL₂⟩ := hL₂
  exact ⟨_, hL₁.comp hL₂⟩

theorem localOn_zero (R : Reg) : LocalOn R (0 : qs.State →ₗ[ℂ] qs.State) :=
  ⟨fun _ _ => 0, fun b c => by simp⟩

/-- **Ket laws give local maps.** If `L |b⟩ = ∑ i, a i b • |g i b⟩` for finitely many local
basis maps `g i` and coefficients `a i` that see only the bits of `R`, then `L` is local to
`R`. -/
theorem localOn_of_sum {ι : Type*} [Fintype ι] {R : Reg} (L : qs.State →ₗ[ℂ] qs.State)
    (a : ι → qs.Basis → ℂ) (g : ι → qs.Basis → qs.Basis)
    (hL : ∀ b, L (qs.ket b) = ∑ i, a i b • qs.ket (g i b))
    (hg : ∀ i, LocalMap R (g i))
    (ha : ∀ i b b', AgreeOn R b b' → a i b = a i b') : LocalOn R L := by
  classical
  refine ⟨fun u x => ∑ i, a i (canonR R u)
    * (if RegEncoding.toNat R (g i (canonR R u)) = x then 1 else 0), ?_⟩
  intro b c
  rw [hL, inner_sum]
  simp_rw [inner_smul_right, inner_ket_ket]
  have hb := agreeOn_canonR R b
  by_cases hA : AgreeOff R c b
  · rw [ite_eq_left hA]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hgi := (hg i).on _ _ hb
    rw [← ha i _ _ hb, ← hgi.toNat (fun _ h => h)]
    have key := eq_iff_toNat_eq_of_agreeOff hA ((hg i).off b)
    by_cases he : c = g i b
    · rw [ite_eq_left he, ite_eq_left (key.1 he).symm]
    · rw [ite_eq_right he, ite_eq_right (fun e => he (key.2 e.symm))]
  · rw [ite_eq_right hA]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right, mul_zero]
    intro hc
    exact hA (hc ▸ (hg i).off b)

theorem localOn_of_basis {R : Reg} (L : qs.State →ₗ[ℂ] qs.State) (f : qs.Basis → qs.Basis)
    (hL : ∀ b, L (qs.ket b) = qs.ket (f b)) (hf : LocalMap R f) : LocalOn R L :=
  localOn_of_sum (ι := Unit) L (fun _ _ => 1) (fun _ => f) (fun b => by simp [hL])
    (fun _ => hf) (fun _ _ _ _ => rfl)

theorem localOn_of_diag {R : Reg} (L : qs.State →ₗ[ℂ] qs.State) (s : qs.Basis → ℂ)
    (hL : ∀ b, L (qs.ket b) = s b • qs.ket b) (hs : ∀ b b', AgreeOn R b b' → s b = s b') :
    LocalOn R L :=
  localOn_of_sum (ι := Unit) L (fun _ => s) (fun _ b => b) (fun b => by simp [hL])
    (fun _ => LocalMap.id R) (fun _ => hs)

end Local

/-! ## Gates -/

section Gates
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]

/-- Every gate is a unitary: `⟪x, adj U y⟫ = ⟪U x, y⟫`. -/
theorem inner_eval_adj (U : Gate) (x y : qs.State) :
    inner ℂ x (qs.eval (Gate.adj U) y) = inner ℂ (qs.eval U x) y := by
  conv_rhs => rw [← gate_eval_apply_adj U y]
  rw [GateSemanticsCore.inner_preserved]

theorem LocalWith.adj {R : Reg} {U : Gate} {h : ℕ → ℕ → ℂ} (hU : LocalWith R (gateL U) h) :
    LocalWith R (gateL (Gate.adj U)) (fun u x => starRingEnd ℂ (h x u)) := by
  classical
  intro b c
  have hcb := hU c b
  simp only [gateL_apply] at hcb ⊢
  rw [inner_eval_adj, ← inner_conj_symm, hcb]
  by_cases hA : AgreeOff R c b
  · rw [ite_eq_left hA.symm, ite_eq_left hA]
  · rw [ite_eq_right (fun h => hA h.symm), ite_eq_right hA, map_zero]

theorem LocalOn.adj {R : Reg} {U : Gate} (hU : LocalOn R (gateL (qs := qs) U)) :
    LocalOn R (gateL (qs := qs) (Gate.adj U)) := by
  obtain ⟨h, hU⟩ := hU
  exact ⟨_, hU.adj⟩

theorem gateL_seq (U V : Gate) :
    gateL (qs := qs) (U ;; V) = (gateL V).comp (gateL U) :=
  LinearMap.ext fun ψ => GateSemanticsCore.eval_seq U V ψ

/-- `R` as a set of qubits. -/
def regSet (R : Reg) : Set ℕ := {q | q ∈ R.qubits}

/-- **Per-gate locality, any start ket.** A gate with no `idealCtrlModMul` node, all of whose
named qubits lie in `R`, is local to `R`. -/
theorem gate_localOn (U : Gate) (hU : U.NoIdeal) {R : Reg} (hS : U.qubitSupport ⊆ regSet R) :
    LocalOn R (gateL (qs := qs) U) := by
  induction U with
  | id =>
    exact localOn_of_basis (gateL _) (fun b => b) (fun b => GateSemanticsCore.eval_id _)
      (LocalMap.id R)
  | seq U V ihU ihV =>
    simp only [Gate.qubitSupport, Set.union_subset_iff] at hS
    rw [gateL_seq]
    exact (ihU hU.1 hS.1).comp (ihV hU.2 hS.2)
  | adj U ih =>
    exact (ih hU hS).adj
  | H p =>
    have hp : p ∈ R.qubits := hS (by simp [Gate.qubitSupport])
    refine localOn_of_sum (ι := Bool) _
      (fun i b => if i then (1 / (Real.sqrt (2 : ℝ) : ℂ))
        * (if RegEncoding.bit p b then (-1 : ℂ) else 1) else (1 / (Real.sqrt (2 : ℝ) : ℂ)))
      (fun i b => RegEncoding.writeNat (qubitReg p) (if i then 1 else 0) b) (fun b => ?_)
      (fun i => LocalMap.writeNat (qubitReg_sub hp) _ fun _ _ _ => rfl)
      (fun i b b' h => by cases i <;> simp only [h.bit hp, Bool.false_eq_true, ↓reduceIte])
    rw [gateL_apply, HadamardSemantics.eval_H_ket, Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [smul_add, smul_smul, add_comm]
  | X p =>
    exact localOn_of_basis _ (flipBit p) (eval_X_ket_flipBit p)
      (localMap_flipBit (hS (by simp [Gate.qubitSupport])))
  | CNOT a t =>
    exact localOn_of_basis _ _ (ClassicalReversibleSemantics.eval_CNOT_ket a t)
      (localMap_cnot (hS (by simp [Gate.qubitSupport])) (hS (by simp [Gate.qubitSupport])))
  | Toffoli a a' t =>
    exact localOn_of_basis _ _ (ClassicalReversibleSemantics.eval_Toffoli_ket a a' t)
      (localMap_toffoli (hS (by simp [Gate.qubitSupport])) (hS (by simp [Gate.qubitSupport]))
        (hS (by simp [Gate.qubitSupport])))
  | QFT r =>
    have hr : ∀ p ∈ r.active.qubits, p ∈ R.qubits := fun p hp =>
      hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp])
    refine localOn_of_sum (ι := Fin (2 ^ r.width)) _
      (fun y b => ((1 / Real.sqrt ((2 ^ r.width : ℕ) : ℝ) : ℂ))
        * qftPhase (2 ^ r.width) (ExtReg.toNat r b) y.1)
      (fun y b => RegEncoding.writeNat r.active y.1 b) (fun b => ?_)
      (fun y => LocalMap.writeNat hr _ fun _ _ _ => rfl)
      (fun y b b' h => by simp only [ExtReg.toNat, h.toNat hr])
    rw [gateL_apply, QFTSemantics.eval_QFT_ket, Finset.smul_sum]
    simp_rw [smul_smul]
  | RadixReverse r m =>
    exact localOn_of_basis _ _ (RadixReverseSemantics.eval_RadixReverse_ket_total r m)
      (localMap_radixReverse fun p hp => hS (by simp [Gate.qubitSupport, hp]))
  | SignedPhaseProd phi x z =>
    have hx : ∀ p ∈ x.active.qubits, p ∈ R.qubits := fun p hp =>
      hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp])
    have hz : ∀ p ∈ z.active.qubits, p ∈ R.qubits := fun p hp =>
      hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp])
    exact localOn_of_diag _ _ (PhaseSemantics.eval_SignedPhaseProd_ket phi x z)
      (fun b b' h => by rw [h.extToInt hx, h.extToInt hz])
  | CSignedPhaseProd ctrl phi x z =>
    have hc : ctrl ∈ R.qubits := hS (by simp [Gate.qubitSupport])
    have hx : ∀ p ∈ x.active.qubits, p ∈ R.qubits := fun p hp =>
      hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp])
    have hz : ∀ p ∈ z.active.qubits, p ∈ R.qubits := fun p hp =>
      hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp])
    refine localOn_of_diag _ (fun b => if RegEncoding.bit ctrl b then
        Complex.exp (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
          (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ)))) else 1) (fun b => ?_)
      (fun b b' h => by rw [h.bit hc, h.extToInt hx, h.extToInt hz])
    rw [gateL_apply, PhaseSemantics.eval_CSignedPhaseProd_ket]
    split_ifs <;> simp
  | CmpGeConst N d s f =>
    exact localOn_of_basis _ _ (ModularArithmeticSemantics.eval_CmpGeConst_ket N d s f)
      (localMap_cmpGeConst (fun p hp => hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp]))
        (hS (by simp [Gate.qubitSupport])))
  | CSubConst N d s f =>
    exact localOn_of_basis _ _ (ModularArithmeticSemantics.eval_CSubConst_ket N d s f)
      (localMap_csubConst (fun p hp => hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp]))
        (hS (by simp [Gate.qubitSupport])))
  | ShiftL r n =>
    exact localOn_of_basis _ _ (ArithmeticSemantics.eval_ShiftL_ket_total r n)
      (localMap_shiftL fun p hp => hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp]))
  | ShiftR r n =>
    exact localOn_of_basis _ _ (ArithmeticSemantics.eval_ShiftR_ket_total r n)
      (localMap_shiftR fun p hp => hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp]))
  | Negate r =>
    exact localOn_of_basis _ _ (ArithmeticSemantics.eval_Negate_ket_total r)
      (localMap_negate fun p hp => hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp]))
  | AddScaled d s neg sh =>
    exact localOn_of_basis _ _ (ArithmeticSemantics.eval_AddScaled_ket_total d s neg sh)
      (localMap_addScaled (fun p hp => hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp]))
        (fun p hp => hS (by simp [Gate.qubitSupport, ExtReg.ownedQubits, hp])))
  | zeroExtend r n =>
    exact localOn_of_basis _ (fun b => b) (fun b => ExtensionSemantics.eval_zeroExtend r n _)
      (LocalMap.id R)
  | signExtend r n =>
    exact localOn_of_basis _ _ (ExtensionSemantics.eval_signExtend_ket_total r n)
      (localMap_signExtend fun p hp => hS (by simpa [Gate.qubitSupport] using hp))
  | zeroDealloc r n =>
    exact localOn_of_basis _ (fun b => b) (fun b => ExtensionSemantics.eval_zeroDealloc r n _)
      (LocalMap.id R)
  | signDealloc r n =>
    exact localOn_of_basis _ _ (ExtensionSemantics.eval_signDealloc_ket_total r n)
      (localMap_signExtend fun p hp => hS (by simpa [Gate.qubitSupport] using hp))
  | idealCtrlModMul _ _ _ _ =>
    exact hU.elim

end Gates

/-! ## Measurement programs -/

section MGates
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- One child of `measureReset q` as a linear map. -/
noncomputable def measResetL (q : ℕ) (o : Bool) : qs.State →ₗ[ℂ] qs.State :=
  if o then (gateL (Gate.X q)).comp (measProj (qubitReg q) 1).toLinearMap
  else (measProj (qubitReg q) 0).toLinearMap

omit [LowerGateClass qs] in
theorem measResetL_apply (q : ℕ) (o : Bool) (ψ : qs.State) :
    measResetL q o ψ = measureResetBranch q o ψ := by
  cases o <;> rfl

omit [GateSemanticsFacts qs] [LowerGateClass qs] in
theorem measProj_localOn {R : Reg} {q : ℕ} (hq : q ∈ R.qubits) (o : ℕ) :
    LocalOn R (measProj (qs := qs) (qubitReg q) o).toLinearMap :=
  localOn_of_diag _ (fun b => if RegEncoding.toNat (qubitReg q) b = o then 1 else 0)
    (fun b => by
      rw [ContinuousLinearMap.coe_coe, MeasureClass.measProj_ket]
      split_ifs <;> simp)
    (fun b b' h => by rw [h.toNat (qubitReg_sub hq)])

omit [LowerGateClass qs] in
theorem measResetL_localOn {R : Reg} {q : ℕ} (hq : q ∈ R.qubits) (o : Bool) :
    LocalOn R (measResetL (qs := qs) q o) := by
  cases o
  · exact measProj_localOn hq 0
  · exact (measProj_localOn hq 1).comp (localOn_of_basis _ (flipBit q) (eval_X_ket_flipBit q)
      (localMap_flipBit hq))

/-- Every branch `r` of `P.eval ψ` is one local linear map applied to one branch `pre` of the
input. -/
def MLocal (R : Reg) (P : MGate) : Prop :=
  ∀ r : Record, ∃ (pre : Record) (L : qs.State →ₗ[ℂ] qs.State),
    LocalOn R L ∧ ∀ ψ : MState qs, P.eval ψ r = L (ψ pre)

theorem mgate_mlocal (P : MGate) (hP : P.NoIdeal) {R : Reg} (hS : P.qubitSupport ⊆ regSet R) :
    MLocal (qs := qs) R P := by
  induction P with
  | unitary g =>
    intro r
    exact ⟨r, gateL g, gate_localOn g hP hS, fun ψ => rfl⟩
  | seq a b iha ihb =>
    simp only [MGate.qubitSupport, Set.union_subset_iff] at hS
    intro r
    obtain ⟨pre₂, L₂, hL₂, he₂⟩ := ihb hP.2 hS.2 r
    obtain ⟨pre₁, L₁, hL₁, he₁⟩ := iha hP.1 hS.1 pre₂
    exact ⟨pre₁, L₂.comp L₁, hL₁.comp hL₂, fun ψ => by
      rw [MGate.eval_seq, he₂, he₁]; rfl⟩
  | measureReset q =>
    have hq : q ∈ R.qubits := hS (by simp [MGate.qubitSupport])
    intro r
    by_cases hr : r = []
    · exact ⟨[], 0, localOn_zero R, fun ψ => by subst hr; rfl⟩
    · refine ⟨r.dropLast, measResetL q (r.getLast hr), measResetL_localOn hq _, fun ψ => ?_⟩
      simp only [MGate.eval, dite_eq_right hr, measResetL_apply]
  | ffPhase q j =>
    have hq : q ∈ R.qubits := hS (by simp [MGate.qubitSupport])
    intro r
    refine ⟨r, lowL (LowGate.Phase q (ffAngle j r)), ?_, fun ψ => rfl⟩
    exact localOn_of_diag _ (fun b => if RegEncoding.bit q b then
        Complex.exp (((Angle.toReal (ffAngle j r) : ℝ) : ℂ) * Complex.I) else 1)
      (fun b => by
        rw [lowL_apply, LowerGateClass.evalL_Phase_ket]
        split_ifs <;> simp)
      (fun b b' h => by rw [h.bit hq])

/-- **Locality, any register containing the support.** If `P` has no `idealCtrlModMul` node,
every qubit `P` names is in `R`, and the start kets `b`, `b'` agree on `R`, then every record
has the same probability, however many qubits outside `R` they differ at. -/
theorem MGate.recordProb_of_agreeOn (P : MGate) (hP : P.NoIdeal) {R : Reg}
    (hS : P.qubitSupport ⊆ regSet R) (b b' : qs.Basis) (hb : AgreeOn R b b') (r : Record) :
    recordProb (P.eval (MState.init (qs.ket b'))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  obtain ⟨pre, L, ⟨h, hL⟩, he⟩ := mgate_mlocal (qs := qs) P hP hS r
  rw [recordProb, recordProb, he, he]
  unfold MState.init
  by_cases hp : pre = []
  · simp only [hp, ↓reduceIte]
    exact (hL.norm_sq_eq hb).symm
  · simp only [hp, ↓reduceIte]

end MGates

/-! ## The support is finite -/

theorem Gate.qubitSupport_finite (U : Gate) : U.qubitSupport.Finite := by
  induction U with
  | seq U V ihU ihV =>
    exact ihU.union ihV
  | adj U ih =>
    exact ih
  | _ =>
    simp only [Gate.qubitSupport, Set.ofPred_or, Set.ofPred_eq_eq_singleton]
    repeat' apply Set.Finite.union
    all_goals first
      | exact Set.finite_empty
      | exact Set.finite_singleton _
      | exact List.finite_toSet _
      | exact Set.toFinite _

theorem MGate.qubitSupport_finite (P : MGate) : P.qubitSupport.Finite := by
  induction P with
  | unitary g =>
    exact Gate.qubitSupport_finite g
  | seq a b iha ihb =>
    exact iha.union ihb
  | measureReset q =>
    exact Set.finite_singleton q
  | ffPhase q j =>
    exact Set.finite_singleton q

/-- The support of `P` as a register. -/
noncomputable def _root_.Shor.MGate.supportReg (P : MGate) : Reg :=
  ⟨(MGate.qubitSupport_finite P).toFinset.toList, Finset.nodup_toList _⟩

theorem MGate.mem_supportReg (P : MGate) (q : ℕ) :
    q ∈ P.supportReg.qubits ↔ q ∈ P.qubitSupport := by
  simp [MGate.supportReg]

section Main
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- **Locality without `hfin`.** If `P` has no `idealCtrlModMul` node and the start
kets `b`, `b'` agree on every qubit `P` names, then every record has the same probability from
`|b'⟩` as from `|b⟩`. `b` and `b'` may differ at INFINITELY many (unnamed) qubits. -/
theorem MGate.recordProb_of_agree_inf (P : MGate) (hP : P.NoIdeal) (b b' : qs.Basis)
    (hagree : ∀ p ∈ P.qubitSupport, RegEncoding.bit p b' = RegEncoding.bit p b) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket b'))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r :=
  MGate.recordProb_of_agreeOn P hP (R := P.supportReg)
    (fun q hq => (MGate.mem_supportReg P q).2 hq) b b'
    (fun p hp => (hagree p ((MGate.mem_supportReg P p).1 hp)).symm) r

end Main

end Readout
end Shor
