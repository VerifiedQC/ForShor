import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.ConstArithmeticLowering
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.EvalLLemmas

/-!
# Correctness of concrete Step-3 constant arithmetic lowering
-/

namespace Shor

open LowGate

private noncomputable def addBitPowersBasis
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) : List ℕ → Basis → Basis
  | [], b => b
  | i :: bits, b =>
      addBitPowersBasis dst src bits
        (addScaledBasis dst src false i b)

private lemma evalL_lowerAddBitPowers_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (dst src : ExtReg) (bits : List ℕ) (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs)
        (lowerAddBitPowers dst src bits) (qs.ket b) =
      qs.ket (addBitPowersBasis dst src bits b) := by
  induction bits generalizing b with
  | nil =>
      simp [lowerAddBitPowers, addBitPowersBasis,
        LowerGateClass.evalL_id]
  | cons i bits ih =>
      simp only [lowerAddBitPowers, LowerGateClass.evalL_seq,
        LowerGateClass.evalL_addScaled_ket_total]
      exact ih (addScaledBasis dst src false i b)

private lemma activeDisjoint_of_ownedDisjoint
    {x z : ExtReg} (h : x.OwnedDisjoint z) : x.ActiveDisjoint z := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h
  rw [ExtReg.ActiveDisjoint, Disjoint, List.disjoint_left]
  intro q hx hz
  exact h (List.mem_append_left _ hx) (List.mem_append_left _ hz)

private lemma ownedDisjoint_grow_left
    (x z : ExtReg) (n : ℕ) (h : x.OwnedDisjoint z) :
    (x.grow n).OwnedDisjoint z := by
  rw [ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow]
  exact h

private lemma constArithmeticUnitQubit_mem_newBits
    (scratch : ExtReg) (h : scratch.CanGrow 1) :
    constArithmeticUnitQubit scratch h ∈ (scratch.newBits 1).qubits := by
  exact List.get_mem _ _

private lemma scratch_unit_activeDisjoint
    (scratch : ExtReg) (h : scratch.CanGrow 1) :
    scratch.ActiveDisjoint (constArithmeticUnit scratch h) := by
  rw [ExtReg.ActiveDisjoint, Disjoint, List.disjoint_left]
  intro q hqScratch hqUnit
  have hq : q = constArithmeticUnitQubit scratch h := by
    simpa [constArithmeticUnit, ExtReg.ofReg, qubitReg, Reg.singleton] using hqUnit
  subst q
  have hdisj := scratch.active_reserve_disjoint
  rw [Disjoint, List.disjoint_left] at hdisj
  exact hdisj hqScratch
      (List.mem_of_mem_take
        (constArithmeticUnitQubit_mem_newBits scratch h))

private lemma active_qubit_disjoint_of_not_owned
    (e : ExtReg) (q : ℕ) (hq : q ∉ e.ownedQubits) :
    Disjoint e.active (qubitReg q) := by
  rw [Disjoint, List.disjoint_left]
  intro p hp hpsingle
  have hpq : p = q := by
    simpa [qubitReg, Reg.singleton] using hpsingle
  subst p
  exact hq (List.mem_append_left _ hp)

private lemma addScaledBasis_write_qubit
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (sh q value : ℕ) (b : Basis)
    (hds : dst.ActiveDisjoint src)
    (hqdst : q ∉ dst.ownedQubits)
    (hqsrc : q ∉ src.ownedQubits) :
    addScaledBasis dst src false sh
        (RegEncoding.writeNat (qubitReg q) value b) =
      RegEncoding.writeNat (qubitReg q) value
        (addScaledBasis dst src false sh b) := by
  rw [addScaledBasis_eq dst src false sh _ hds,
    addScaledBasis_eq dst src false sh b hds]
  have hdstDisj := active_qubit_disjoint_of_not_owned dst q hqdst
  have hsrcDisj := active_qubit_disjoint_of_not_owned src q hqsrc
  have hdst :
      extToInt dst (RegEncoding.writeNat (qubitReg q) value b) =
        extToInt dst b := by
    unfold extToInt ExtReg.toNat
    rw [RegEncoding.toNat_left_write_right
      dst.active (qubitReg q) hdstDisj b value]
  have hsrc :
      extToInt src (RegEncoding.writeNat (qubitReg q) value b) =
        extToInt src b := by
    unfold extToInt ExtReg.toNat
    rw [RegEncoding.toNat_left_write_right
      src.active (qubitReg q) hsrcDisj b value]
  rw [show addScaledValue dst src false sh
        (RegEncoding.writeNat (qubitReg q) value b) =
      addScaledValue dst src false sh b by
        simp [addScaledValue, hdst, hsrc]]
  exact RegEncoding.writeNat_comm_of_disjoint
    dst.active (qubitReg q) hdstDisj _ value b

private lemma cnotBasis_writeNat_of_outside
    {Basis : Type u} [RegEncoding Basis]
    (ctrl target : ℕ) (r : Reg) (value : ℕ) (b : Basis)
    (hctrl : ctrl ∉ r.qubits)
    (htarget : target ∉ r.qubits) :
    cnotBasis ctrl target (RegEncoding.writeNat r value b) =
      RegEncoding.writeNat r value (cnotBasis ctrl target b) := by
  unfold cnotBasis
  by_cases hsame : ctrl = target
  · simp [hsame]
  · simp only [hsame, if_false]
    rw [RegEncoding.bit_writeNat_out r value b ctrl hctrl]
    by_cases hbit : RegEncoding.bit ctrl b
    · simp only [hbit, if_true]
      rw [RegEncoding.bit_writeNat_out r value b target htarget]
      have hdisj : Disjoint (qubitReg target) r := by
        rw [Disjoint, List.disjoint_left]
        intro q hqTarget hqR
        have hq : q = target := by
          simpa [qubitReg, Reg.singleton] using hqTarget
        subst q
        exact htarget hqR
      exact RegEncoding.writeNat_comm_of_disjoint
        (qubitReg target) r hdisj _ value b
    · simp [hbit]

private lemma addScaledBasis_writeNat_of_disjoint
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (sh : ℕ) (r : Reg) (value : ℕ) (b : Basis)
    (hds : dst.ActiveDisjoint src)
    (hdr : Disjoint dst.active r)
    (hsr : Disjoint src.active r) :
    addScaledBasis dst src false sh (RegEncoding.writeNat r value b) =
      RegEncoding.writeNat r value
        (addScaledBasis dst src false sh b) := by
  rw [addScaledBasis_eq dst src false sh _ hds,
    addScaledBasis_eq dst src false sh b hds]
  have hdst :
      extToInt dst (RegEncoding.writeNat r value b) = extToInt dst b := by
    unfold extToInt ExtReg.toNat
    rw [RegEncoding.toNat_left_write_right dst.active r hdr b value]
  have hsrc :
      extToInt src (RegEncoding.writeNat r value b) = extToInt src b := by
    unfold extToInt ExtReg.toNat
    rw [RegEncoding.toNat_left_write_right src.active r hsr b value]
  rw [show addScaledValue dst src false sh
        (RegEncoding.writeNat r value b) =
      addScaledValue dst src false sh b by
        simp [addScaledValue, hdst, hsrc]]
  exact RegEncoding.writeNat_comm_of_disjoint
    dst.active r hdr _ value b

private lemma addBitPowersBasis_writeNat_of_disjoint
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (bits : List ℕ)
    (r : Reg) (value : ℕ) (b : Basis)
    (hds : dst.ActiveDisjoint src)
    (hdr : Disjoint dst.active r)
    (hsr : Disjoint src.active r) :
    addBitPowersBasis dst src bits (RegEncoding.writeNat r value b) =
      RegEncoding.writeNat r value
        (addBitPowersBasis dst src bits b) := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      simp only [addBitPowersBasis]
      rw [addScaledBasis_writeNat_of_disjoint
        dst src i r value b hds hdr hsr]
      exact ih (addScaledBasis dst src false i b)

private lemma addBitPowersBasis_write_qubit
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (bits : List ℕ) (q value : ℕ) (b : Basis)
    (hds : dst.ActiveDisjoint src)
    (hqdst : q ∉ dst.ownedQubits)
    (hqsrc : q ∉ src.ownedQubits) :
    addBitPowersBasis dst src bits
        (RegEncoding.writeNat (qubitReg q) value b) =
      RegEncoding.writeNat (qubitReg q) value
        (addBitPowersBasis dst src bits b) := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      simp only [addBitPowersBasis]
      rw [addScaledBasis_write_qubit dst src i q value b
        hds hqdst hqsrc]
      exact ih (addScaledBasis dst src false i b)

private lemma addBitPowersBasis_bit_out
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (bits : List ℕ) (q : ℕ) (b : Basis)
    (hds : dst.ActiveDisjoint src)
    (hqdst : q ∉ dst.ownedQubits) :
    RegEncoding.bit q (addBitPowersBasis dst src bits b) =
      RegEncoding.bit q b := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      simp only [addBitPowersBasis]
      rw [ih]
      rw [addScaledBasis_eq dst src false i b hds]
      exact RegEncoding.bit_writeNat_out dst.active _ b q
        (fun hmem => hqdst (List.mem_append_left _ hmem))

private lemma addBitPowersBasis_bit_out_active
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (bits : List ℕ) (q : ℕ) (b : Basis)
    (hds : dst.ActiveDisjoint src)
    (hqdst : q ∉ dst.active.qubits) :
    RegEncoding.bit q (addBitPowersBasis dst src bits b) =
      RegEncoding.bit q b := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      simp only [addBitPowersBasis]
      rw [ih]
      rw [addScaledBasis_eq dst src false i b hds]
      exact RegEncoding.bit_writeNat_out dst.active _ b q hqdst

private lemma writeNat_override
    {Basis : Type u} [RegEncoding Basis]
    (r : Reg) (outer inner : ℕ) (b : Basis) :
    RegEncoding.writeNat r outer (RegEncoding.writeNat r inner b) =
      RegEncoding.writeNat r outer b := by
  apply RegEncoding.basis_ext
  intro q
  by_cases hq : q ∈ r.qubits
  · exact RegEncoding.bit_writeNat_in r outer _ _ q hq
  · rw [RegEncoding.bit_writeNat_out r outer _ q hq,
      RegEncoding.bit_writeNat_out r inner b q hq,
      RegEncoding.bit_writeNat_out r outer b q hq]

private lemma bit_write_qubit_zero
    {Basis : Type u} [RegEncoding Basis]
    (q : ℕ) (b : Basis) :
    RegEncoding.bit q (RegEncoding.writeNat (qubitReg q) 0 b) = false := by
  have hread := RegEncoding.toNat_writeNat_of_lt
    (qubitReg q) 0 b (by simp [ASize])
  have hbit := RegEncoding.bit_eq_testBit_toNat
    (qubitReg q) (RegEncoding.writeNat (qubitReg q) 0 b)
    (⟨0, by simp⟩ : Fin (regSize (qubitReg q)))
  rw [hread] at hbit
  simpa [qubitReg, Reg.singleton, Reg.get, regSize, Reg.width] using hbit

private lemma bit_write_qubit_one
    {Basis : Type u} [RegEncoding Basis]
    (q : ℕ) (b : Basis) :
    RegEncoding.bit q (RegEncoding.writeNat (qubitReg q) 1 b) = true := by
  have hread := RegEncoding.toNat_writeNat_of_lt
    (qubitReg q) 1 b (by simp [ASize])
  have hbit := RegEncoding.bit_eq_testBit_toNat
    (qubitReg q) (RegEncoding.writeNat (qubitReg q) 1 b)
    (⟨0, by simp⟩ : Fin (regSize (qubitReg q)))
  rw [hread] at hbit
  simpa [qubitReg, Reg.singleton, Reg.get, regSize, Reg.width] using hbit

private lemma xBasis_write_qubit
    {Basis : Type u} [RegEncoding Basis]
    (q target value : ℕ) (b : Basis) (hne : q ≠ target) :
    RegEncoding.writeNat (qubitReg q)
        (if RegEncoding.bit q
            (RegEncoding.writeNat (qubitReg target) value b)
          then 0 else 1)
        (RegEncoding.writeNat (qubitReg target) value b) =
      RegEncoding.writeNat (qubitReg target) value
        (RegEncoding.writeNat (qubitReg q)
          (if RegEncoding.bit q b then 0 else 1) b) := by
  have hqout : q ∉ (qubitReg target).qubits := by
    simpa [qubitReg, Reg.singleton] using hne
  have hdisj : Disjoint (qubitReg q) (qubitReg target) := by
    rw [Disjoint, List.disjoint_left]
    simp [qubitReg, Reg.singleton, hne]
  rw [RegEncoding.bit_writeNat_out (qubitReg target) value b q hqout]
  exact RegEncoding.writeNat_comm_of_disjoint
    (qubitReg q) (qubitReg target) hdisj _ value b

private lemma unit_bit_false_of_fresh
    {Basis : Type u} [RegEncoding Basis]
    (scratch : ExtReg) (h : scratch.CanGrow 1) (b : Basis)
    (hfresh : scratch.FreshFor 1 b) :
    RegEncoding.bit (constArithmeticUnitQubit scratch h) b = false := by
  unfold ExtReg.FreshFor FreshZero at hfresh
  let i : Fin (regSize (scratch.newBits 1)) :=
    ⟨0, by
      have hsize := Gate.ExtReg.newBits_size scratch 1 h
      omega⟩
  have hbit := RegEncoding.bit_eq_testBit_toNat
    (scratch.newBits 1) b i
  have hget :
      (scratch.newBits 1).get i = constArithmeticUnitQubit scratch h := by
    rfl
  rw [hget, hfresh] at hbit
  simpa using hbit

private lemma unit_extToInt_after_X
    {Basis : Type u} [RegEncoding Basis]
    (scratch : ExtReg) (h : scratch.CanGrow 1) (b : Basis) :
    let q := constArithmeticUnitQubit scratch h
    let unit := constArithmeticUnit scratch h
    extToInt unit
      (RegEncoding.writeNat (qubitReg q) 1 b) = -1 := by
  dsimp
  unfold extToInt ExtReg.toNat constArithmeticUnit ExtReg.ofReg ExtReg.width
  rw [RegEncoding.toNat_writeNat_of_lt]
  · norm_num [tcDecodeWidth]
  · simp [ASize]

private theorem toNat_qubitReg_eq_bit_local
    {Basis : Type*} [RegEncoding Basis]
    (q : ℕ) (b : Basis) :
    RegEncoding.toNat (qubitReg q) b =
      (RegEncoding.bit q b).toNat := by
  let n := RegEncoding.toNat (qubitReg q) b
  have hn : n < 2 := by
    simpa [n, ASize] using
      RegEncoding.toNat_lt_ASize (r := qubitReg q) (b := b)
  have hbit : RegEncoding.bit q b = Nat.testBit n 0 := by
    simpa [n, qubitReg, Reg.singleton, Reg.get, regSize, Reg.width] using
      RegEncoding.bit_eq_testBit_toNat
        (qubitReg q) b (⟨0, by simp⟩ : Fin (regSize (qubitReg q)))
  change n = (RegEncoding.bit q b).toNat
  rw [hbit]
  interval_cases n <;> simp

private lemma unit_extToInt_zero_of_fresh
    {Basis : Type u} [RegEncoding Basis]
    (scratch : ExtReg) (h : scratch.CanGrow 1) (b : Basis)
    (hfresh : scratch.FreshFor 1 b) :
    extToInt (constArithmeticUnit scratch h) b = 0 := by
  have hbit : RegEncoding.bit (constArithmeticUnitQubit scratch h) b = false :=
    unit_bit_false_of_fresh scratch h b hfresh
  unfold extToInt ExtReg.toNat constArithmeticUnit ExtReg.ofReg ExtReg.width
  rw [toNat_qubitReg_eq_bit_local, hbit]
  norm_num [tcDecodeWidth]

private lemma freshFor_write_qubit_of_not_owned
    {Basis : Type u} [RegEncoding Basis]
    (e : ExtReg) (n q value : ℕ) (b : Basis)
    (hq : q ∉ e.ownedQubits)
    (hfresh : e.FreshFor n b) :
    e.FreshFor n (RegEncoding.writeNat (qubitReg q) value b) := by
  unfold ExtReg.FreshFor at hfresh ⊢
  apply FreshZero.of_eq_on_bits (e.newBits n) b
    (RegEncoding.writeNat (qubitReg q) value b) ?_ hfresh
  intro p hp
  rw [RegEncoding.bit_writeNat_out]
  intro hpq
  have hp_eq : p = q := by
    simpa [qubitReg, Reg.singleton] using hpq
  subst p
  exact hq (List.mem_append_right _ (List.mem_of_mem_take hp))

private lemma addBitPowersBasis_src
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (bits : List ℕ) (b : Basis)
    (hdisj : dst.ActiveDisjoint src) :
    extToInt src (addBitPowersBasis dst src bits b) = extToInt src b := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      simp only [addBitPowersBasis]
      rw [ih]
      exact extToInt_addScaledBasis_src dst src false i b hdisj

private lemma addBitPowersBasis_observed
    {Basis : Type u} [RegEncoding Basis]
    (dst src observed : ExtReg) (bits : List ℕ) (b : Basis)
    (hds : dst.ActiveDisjoint src)
    (hod : observed.ActiveDisjoint dst) :
    extToInt observed (addBitPowersBasis dst src bits b) =
      extToInt observed b := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      simp only [addBitPowersBasis]
      rw [ih]
      exact extToInt_addScaledBasis_of_activeDisjoint
        dst src observed false i b hds hod

private lemma fits_neg_nat_of_lt_half
    {w n : ℕ} (hw : 0 < w) (hn : n < 2 ^ (w - 1)) :
    FitsSignedWidth w (-(n : ℤ)) := by
  unfold FitsSignedWidth signedMin signedMax
  refine ⟨hw, ?_, ?_⟩
  · exact neg_le_neg (by exact_mod_cast hn.le)
  · have hn0 : (0 : ℤ) ≤ n := by positivity
    have hp : (0 : ℤ) < (2 : ℤ) ^ (w - 1) := by positivity
    omega

private lemma fits_nat_of_lt_half
    {w n : ℕ} (hw : 0 < w) (hn : n < 2 ^ (w - 1)) :
    FitsSignedWidth w (n : ℤ) := by
  unfold FitsSignedWidth signedMin signedMax
  refine ⟨hw, ?_, ?_⟩
  · have hp : (0 : ℤ) ≤ (2 : ℤ) ^ (w - 1) := by positivity
    have hn0 : (0 : ℤ) ≤ n := by positivity
    omega
  · exact_mod_cast hn

private lemma tcModWidth_tcDecodeWidth_sub
    {w n k : ℕ} (hn : n < 2 ^ w) :
    tcModWidth w (tcDecodeWidth w n - (k : ℤ)) =
      (n + 2 ^ w - (k % 2 ^ w)) % 2 ^ w := by
  unfold tcModWidth
  have hM : 0 < 2 ^ w := by positivity
  have hkM : k % 2 ^ w < 2 ^ w := Nat.mod_lt _ hM
  have hsub : k % 2 ^ w ≤ n + 2 ^ w := by omega
  have hnonneg :
      0 ≤ (tcDecodeWidth w n - (k : ℤ)) % ((2 ^ w : ℕ) : ℤ) :=
    Int.emod_nonneg _ (by positivity)
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg hnonneg]
  rw [Int.natCast_emod]
  rw [Nat.cast_sub hsub]
  change
    (tcDecodeWidth w n - (k : ℤ)) % ((2 ^ w : ℕ) : ℤ) =
      (((n : ℤ) + ((2 ^ w : ℕ) : ℤ) - (k % 2 ^ w : ℕ)) %
        ((2 ^ w : ℕ) : ℤ))
  have hkmod :
      (k : ℤ) % ((2 ^ w : ℕ) : ℤ) = (k % 2 ^ w : ℕ) := by
    symm
    exact Int.natCast_emod k (2 ^ w)
  have hdecode :
      tcDecodeWidth w n % ((2 ^ w : ℕ) : ℤ) = (n : ℤ) := by
    cases w with
    | zero =>
      have : n = 0 := by simpa using hn
      subst n
      simp [tcDecodeWidth]
    | succ w =>
      by_cases hs : n < 2 ^ w
      · simp only [tcDecodeWidth, dif_pos hs]
        exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hn)
      · simp only [tcDecodeWidth, dif_neg hs]
        have hnmod :
            (n : ℤ) % ((2 ^ (w + 1) : ℕ) : ℤ) = (n : ℤ) :=
          Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hn)
        rw [Int.sub_emod]
        rw [hnmod]
        simpa using hnmod
  rw [Int.sub_emod, hdecode, hkmod]
  conv_rhs =>
    rw [show (n : ℤ) + ((2 ^ w : ℕ) : ℤ) - (k % 2 ^ w : ℕ) =
      ((n : ℤ) - (k % 2 ^ w : ℕ)) + ((2 ^ w : ℕ) : ℤ) by ring]
  rw [Int.add_emod]
  simp

private lemma addScaledBasis_eq_writeNat_mod_sub
    {Basis : Type u} [RegEncoding Basis]
    (N : ℕ) (dst src : ExtReg) (b : Basis)
    (hdisj : dst.ActiveDisjoint src)
    (hsrc : extToInt src b = -(N : ℤ)) :
    addScaledBasis dst src false 0 b =
      RegEncoding.writeNat dst.active
        ((dst.toNat b + ASize dst.active - (N % ASize dst.active)) %
          ASize dst.active) b := by
  rw [addScaledBasis_eq dst src false 0 b hdisj]
  apply congrArg (fun value => RegEncoding.writeNat dst.active value b)
  simp only [addScaledValue, Bool.false_eq_true, if_false, one_mul,
    pow_zero, hsrc, mul_one]
  change tcModWidth dst.width
      (tcDecodeWidth dst.width (dst.toNat b) - (N : ℤ)) = _
  rw [tcModWidth_tcDecodeWidth_sub (dst.toNat_lt b)]
  rfl

private lemma addBitPowersBasis_neg_sum
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (bits : List ℕ) (b : Basis)
    (hdisj : dst.ActiveDisjoint src)
    (hw : 0 < dst.width)
    (acc : ℕ)
    (hdst : extToInt dst b = -(acc : ℤ))
    (hsrc : extToInt src b = -1)
    (hbound :
      acc + (bits.map (fun i => 2 ^ i)).sum < 2 ^ (dst.width - 1)) :
    extToInt dst (addBitPowersBasis dst src bits b) =
      -((acc + (bits.map (fun i => 2 ^ i)).sum : ℕ) : ℤ) := by
  induction bits generalizing b acc with
  | nil =>
      simpa using hdst
  | cons i bits ih =>
      let b₁ := addScaledBasis dst src false i b
      have hstepBound : acc + 2 ^ i < 2 ^ (dst.width - 1) := by
        have hbound' :
            acc + 2 ^ i + (bits.map (fun j => 2 ^ j)).sum <
              2 ^ (dst.width - 1) := by
          simpa [Nat.add_assoc] using hbound
        omega
      have hstepFit : FitsSignedWidth dst.width
          (-((acc + 2 ^ i : ℕ) : ℤ)) :=
        fits_neg_nat_of_lt_half hw hstepBound
      have hb₁ : extToInt dst b₁ = -((acc + 2 ^ i : ℕ) : ℤ) := by
        dsimp [b₁]
        rw [extToInt_addScaledBasis_dst dst src false i b hdisj]
        simp [addScaledValue, hdst, hsrc]
        have harg :
            -(acc : ℤ) + -(2 : ℤ) ^ i =
              -((acc + 2 ^ i : ℕ) : ℤ) := by
          push_cast
          ring
        rw [harg]
        rw [tcWrapInt_eq_of_fits hstepFit.1 hstepFit]
        push_cast
        ring
      have hsrc₁ : extToInt src b₁ = -1 := by
        dsimp [b₁]
        rw [extToInt_addScaledBasis_src dst src false i b hdisj, hsrc]
      have htailBound :
          (acc + 2 ^ i) + (bits.map (fun j => 2 ^ j)).sum <
            2 ^ (dst.width - 1) := by
        simpa [Nat.add_assoc] using hbound
      simpa [addBitPowersBasis, Nat.add_assoc] using
        ih b₁ (acc + 2 ^ i) hb₁ hsrc₁ htailBound

private lemma addBitPowersBasis_nat_sub_sum
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (bits : List ℕ) (b : Basis)
    (hdisj : dst.ActiveDisjoint src)
    (hw : 0 < dst.width)
    (value acc : ℕ)
    (hdst : extToInt dst b = (value - acc : ℕ))
    (hsrc : extToInt src b = -1)
    (hbound : acc + (bits.map (fun i => 2 ^ i)).sum ≤ value)
    (hvalue : value < 2 ^ (dst.width - 1)) :
    extToInt dst (addBitPowersBasis dst src bits b) =
      (value - (acc + (bits.map (fun i => 2 ^ i)).sum) : ℕ) := by
  induction bits generalizing b acc with
  | nil =>
      simpa using hdst
  | cons i bits ih =>
      let b₁ := addScaledBasis dst src false i b
      have hstepLe : acc + 2 ^ i ≤ value := by
        have hbound' :
            acc + 2 ^ i + (bits.map (fun j => 2 ^ j)).sum ≤ value := by
          simpa [Nat.add_assoc] using hbound
        omega
      have hstepLt : value - (acc + 2 ^ i) < 2 ^ (dst.width - 1) := by
        exact lt_of_le_of_lt (Nat.sub_le value _) hvalue
      have hstepFit : FitsSignedWidth dst.width
          ((value - (acc + 2 ^ i) : ℕ) : ℤ) :=
        fits_nat_of_lt_half hw hstepLt
      have hb₁ :
          extToInt dst b₁ = (value - (acc + 2 ^ i) : ℕ) := by
        dsimp [b₁]
        rw [extToInt_addScaledBasis_dst dst src false i b hdisj]
        simp only [addScaledValue, Bool.false_eq_true, if_false, one_mul,
          hdst, hsrc]
        have harg :
            ((value - acc : ℕ) : ℤ) + (2 : ℤ) ^ i * -1 =
              ((value - (acc + 2 ^ i) : ℕ) : ℤ) := by
          have haccLe : acc ≤ value := by omega
          rw [Nat.cast_sub haccLe, Nat.cast_sub hstepLe]
          push_cast
          ring
        rw [harg]
        exact tcWrapInt_eq_of_fits hstepFit.1 hstepFit
      have hsrc₁ : extToInt src b₁ = -1 := by
        dsimp [b₁]
        rw [extToInt_addScaledBasis_src dst src false i b hdisj, hsrc]
      have htailBound :
          (acc + 2 ^ i) + (bits.map (fun j => 2 ^ j)).sum ≤ value := by
        simpa [Nat.add_assoc] using hbound
      simpa [addBitPowersBasis, Nat.add_assoc] using
        ih b₁ (acc + 2 ^ i) hb₁ hsrc₁ htailBound

private lemma addBitPowersBasis_zero_source
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (bits : List ℕ) (b : Basis)
    (hdisj : dst.ActiveDisjoint src)
    (hw : 0 < dst.width)
    (value : ℕ)
    (hdst : extToInt dst b = (value : ℤ))
    (hsrc : extToInt src b = 0)
    (hvalue : value < 2 ^ (dst.width - 1)) :
    extToInt dst (addBitPowersBasis dst src bits b) = (value : ℤ) := by
  induction bits generalizing b with
  | nil => exact hdst
  | cons i bits ih =>
      let b₁ := addScaledBasis dst src false i b
      have hfit : FitsSignedWidth dst.width (value : ℤ) :=
        fits_nat_of_lt_half hw hvalue
      have hb₁ : extToInt dst b₁ = (value : ℤ) := by
        dsimp [b₁]
        rw [extToInt_addScaledBasis_dst dst src false i b hdisj]
        simp [addScaledValue, hdst, hsrc,
          tcWrapInt_eq_of_fits hfit.1 hfit]
      have hsrc₁ : extToInt src b₁ = 0 := by
        dsimp [b₁]
        rw [extToInt_addScaledBasis_src dst src false i b hdisj, hsrc]
      simpa [addBitPowersBasis] using ih b₁ hb₁ hsrc₁

private lemma extToInt_writeNat_of_lt_signed
    {Basis : Type u} [RegEncoding Basis]
    (e : ExtReg) (value : ℕ) (b : Basis)
    (hvalue : value < 2 ^ (e.width - 1))
    (hpos : 0 < e.width) :
    extToInt e (RegEncoding.writeNat e.active value b) = (value : ℤ) := by
  have hwidth : e.width = (e.width - 1) + 1 := by omega
  have hvalueFull : value < ASize e.active := by
    have hp : 2 ^ (e.width - 1) ≤ 2 ^ e.width :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    exact lt_of_lt_of_le hvalue (by simpa [ASize, ExtReg.width] using hp)
  unfold extToInt ExtReg.toNat
  rw [RegEncoding.toNat_writeNat_of_lt e.active value b hvalueFull]
  rw [hwidth]
  exact Gate.tcDecodeWidth_add_eq_of_lt (n := 1) (by omega) hvalue

private lemma toNat_eq_of_extToInt_eq_local
    {Basis : Type u} [RegEncoding Basis]
    {e : ExtReg} {b₁ b₂ : Basis}
    (h : extToInt e b₁ = extToInt e b₂) :
    ExtReg.toNat e b₁ = ExtReg.toNat e b₂ := by
  apply tcDecodeWidth_inj_of_lt
    (ExtReg.toNat_lt e b₁) (ExtReg.toNat_lt e b₂)
  simpa [extToInt] using h

private lemma bit_eq_of_toNat_eq_on_reg_local
    {Basis : Type u} [RegEncoding Basis]
    {r : Reg} {b₁ b₂ : Basis} {q : ℕ}
    (hNat : RegEncoding.toNat r b₁ = RegEncoding.toNat r b₂)
    (hq : q ∈ r.qubits) :
    RegEncoding.bit q b₁ = RegEncoding.bit q b₂ := by
  calc
    RegEncoding.bit q b₁ =
        RegEncoding.bit q
          (RegEncoding.writeNat r (RegEncoding.toNat r b₁) b₁) := by
      rw [RegEncoding.writeNat_toNat]
    _ = RegEncoding.bit q
          (RegEncoding.writeNat r (RegEncoding.toNat r b₂) b₂) := by
      simpa [hNat] using
        (RegEncoding.bit_writeNat_in
          (r := r) (v := RegEncoding.toNat r b₁)
          (b₁ := b₁) (b₂ := b₂) (q := q) hq)
    _ = RegEncoding.bit q b₂ := by
      rw [RegEncoding.writeNat_toNat]

private lemma addBitPowersBasis_eq_writeNat_of_value
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (bits : List ℕ) (b : Basis)
    (hdisj : dst.ActiveDisjoint src)
    (value : ℕ)
    (hout : extToInt dst (addBitPowersBasis dst src bits b) = (value : ℤ))
    (hvalue : value < 2 ^ (dst.width - 1))
    (hpos : 0 < dst.width) :
    addBitPowersBasis dst src bits b =
      RegEncoding.writeNat dst.active value b := by
  let bout := addBitPowersBasis dst src bits b
  let btarget := RegEncoding.writeNat dst.active value b
  have htarget : extToInt dst btarget = (value : ℤ) := by
    simpa [btarget] using extToInt_writeNat_of_lt_signed
      dst value b hvalue hpos
  have hNat : ExtReg.toNat dst bout = ExtReg.toNat dst btarget := by
    apply toNat_eq_of_extToInt_eq_local
    simp [bout, btarget, hout, htarget]
  apply RegEncoding.basis_ext
  intro q
  by_cases hq : q ∈ dst.active.qubits
  · exact bit_eq_of_toNat_eq_on_reg_local hNat hq
  · dsimp [bout, btarget]
    rw [addBitPowersBasis_bit_out_active dst src bits q b hdisj hq]
    exact (RegEncoding.bit_writeNat_out dst.active value b q hq).symm

private lemma writeNat_grow_one_eq_writeNat_of_fresh
    {Basis : Type u} [RegEncoding Basis]
    (e : ExtReg) (value : ℕ) (b : Basis)
    (hfresh : e.FreshFor 1 b)
    (hvalue : value < ASize e.active) :
    RegEncoding.writeNat (e.grow 1).active value b =
      RegEncoding.writeNat e.active value b := by
  let hdisj : Disjoint e.active (e.newBits 1) := by
    have h := e.active_reserve_disjoint
    rw [Disjoint, List.disjoint_left] at h ⊢
    intro q hqActive hqNew
    exact h hqActive (List.mem_of_mem_take hqNew)
  let grownActive := Reg.append e.active (e.newBits 1) hdisj
  have hgrow : (e.grow 1).active = grownActive := by rfl
  rw [hgrow]
  let m : SplitPoint grownActive :=
    ⟨regSize e.active, by
      simp [grownActive, regSize, Reg.width, Reg.append]⟩
  have hleft : splitLeft grownActive m = e.active := by
    simp [grownActive, m]
  have hright : splitRight grownActive m = e.newBits 1 := by
    simp [grownActive, m]
  have hhigh : 0 < ASize (splitRight grownActive m) := by
    rw [hright]
    exact Nat.two_pow_pos _
  have hsplit := RegEncoding.writeNat_split
    grownActive m 0 value b
    (by simpa [hleft] using hvalue) hhigh
  rw [hleft, hright] at hsplit
  simp only [Nat.mul_zero, Nat.add_zero] at hsplit
  have hnewZero :
      RegEncoding.toNat (e.newBits 1)
          (RegEncoding.writeNat e.active value b) = 0 := by
    have hread := RegEncoding.toNat_left_write_right
      (e.newBits 1) e.active (Disjoint.symm hdisj) b value
    simpa [ExtReg.FreshFor, FreshZero] using hread.trans hfresh
  have hzeroWrite :
      RegEncoding.writeNat (e.newBits 1) 0
          (RegEncoding.writeNat e.active value b) =
        RegEncoding.writeNat e.active value b := by
    rw [← hnewZero]
    exact RegEncoding.writeNat_toNat _ _
  exact hsplit.trans hzeroWrite

private lemma evalL_lowerPrepareNegConst_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (N : ℕ) (scratch : ExtReg) (hcap : scratch.CanGrow 1)
    (b : qs.Basis)
    (hscratch : extToInt scratch b = 0)
    (hfresh : scratch.FreshFor 1 b)
    (hpos : 0 < scratch.width)
    (hN : N < 2 ^ (scratch.width - 1)) :
    let q := constArithmeticUnitQubit scratch hcap
    let unit := constArithmeticUnit scratch hcap
    let bX := RegEncoding.writeNat (qubitReg q) 1 b
    let bout := addBitPowersBasis scratch unit N.bitIndices bX
    LowerGateClass.evalL (qs := qs)
        (lowerPrepareNegConst N scratch hcap) (qs.ket b) = qs.ket bout ∧
      extToInt scratch bout = -(N : ℤ) ∧
      extToInt unit bout = -1 := by
  dsimp
  let q := constArithmeticUnitQubit scratch hcap
  let unit := constArithmeticUnit scratch hcap
  let bX := RegEncoding.writeNat (qubitReg q) 1 b
  let bout := addBitPowersBasis scratch unit N.bitIndices bX
  have hbit : RegEncoding.bit q b = false := by
    exact unit_bit_false_of_fresh scratch hcap b hfresh
  have hdisj : scratch.ActiveDisjoint unit := by
    exact scratch_unit_activeDisjoint scratch hcap
  have hscratchX : extToInt scratch bX = 0 := by
    have hx := extToInt_writeNat_active_of_disjoint
      unit scratch 1 b hdisj
    simpa [bX, unit, constArithmeticUnit, ExtReg.ofReg, hscratch] using hx
  have hunitX : extToInt unit bX = -1 := by
    exact unit_extToInt_after_X scratch hcap b
  have hbound :
      0 + (N.bitIndices.map (fun i => 2 ^ i)).sum <
        2 ^ (scratch.width - 1) := by
    simpa using hN
  have hout : extToInt scratch bout = -(N : ℤ) := by
    dsimp [bout]
    have := addBitPowersBasis_neg_sum
      scratch unit N.bitIndices bX hdisj hpos 0 hscratchX hunitX hbound
    simpa using this
  have hunitOut : extToInt unit bout = -1 := by
    dsimp [bout]
    rw [addBitPowersBasis_src scratch unit N.bitIndices bX hdisj,
      hunitX]
  refine ⟨?_, hout, hunitOut⟩
  simp only [lowerPrepareNegConst, LowerGateClass.evalL_seq,
    LowerGateClass.evalL_X_ket]
  rw [hbit]
  simpa [lowerAddConstFromUnit, bX] using
    evalL_lowerAddBitPowers_ket scratch unit N.bitIndices bX

private lemma constUnit_ne_of_not_owned
    (scratch : ExtReg) (hcap : scratch.CanGrow 1)
    (q : ℕ) (hq : q ∉ scratch.ownedQubits) :
    constArithmeticUnitQubit scratch hcap ≠ q := by
  intro heq
  apply hq
  rw [← heq]
  exact List.mem_append_right _
    (List.mem_of_mem_take
      (constArithmeticUnitQubit_mem_newBits scratch hcap))

private lemma ownedDisjoint_constUnit
    (data scratch : ExtReg) (hcap : scratch.CanGrow 1)
    (hdisj : data.OwnedDisjoint scratch) :
    data.OwnedDisjoint (constArithmeticUnit scratch hcap) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left]
  intro q hqData hqUnit
  have hq : q = constArithmeticUnitQubit scratch hcap := by
    simpa [constArithmeticUnit, ExtReg.ofReg, ExtReg.ownedQubits,
      qubitReg, Reg.singleton, Reg.empty] using hqUnit
  subst q
  rw [ExtReg.OwnedDisjoint, List.disjoint_left] at hdisj
  exact hdisj hqData
    (List.mem_append_right _
      (List.mem_of_mem_take
        (constArithmeticUnitQubit_mem_newBits scratch hcap)))

private lemma evalL_lowerPrepareNegConst_write_qubit
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (N : ℕ) (scratch : ExtReg) (hcap : scratch.CanGrow 1)
    (target value : ℕ) (b : qs.Basis)
    (htarget : target ∉ scratch.ownedQubits) :
    let q := constArithmeticUnitQubit scratch hcap
    let unit := constArithmeticUnit scratch hcap
    let bX := RegEncoding.writeNat (qubitReg q)
      (if RegEncoding.bit q b then 0 else 1) b
    let bout := addBitPowersBasis scratch unit N.bitIndices bX
    LowerGateClass.evalL (qs := qs)
        (lowerPrepareNegConst N scratch hcap)
        (qs.ket (RegEncoding.writeNat (qubitReg target) value b)) =
      qs.ket (RegEncoding.writeNat (qubitReg target) value bout) := by
  dsimp
  let q := constArithmeticUnitQubit scratch hcap
  let unit := constArithmeticUnit scratch hcap
  let bX := RegEncoding.writeNat (qubitReg q)
    (if RegEncoding.bit q b then 0 else 1) b
  let bout := addBitPowersBasis scratch unit N.bitIndices bX
  have hne : q ≠ target := constUnit_ne_of_not_owned scratch hcap target htarget
  have hqScratch : target ∉ scratch.ownedQubits := htarget
  have hqUnit : target ∉ unit.ownedQubits := by
    intro hmem
    have heq : target = q := by
      simpa [unit, constArithmeticUnit, ExtReg.ofReg,
        ExtReg.ownedQubits, qubitReg, Reg.singleton, Reg.empty] using hmem
    exact hne heq.symm
  have hdisj : scratch.ActiveDisjoint unit :=
    scratch_unit_activeDisjoint scratch hcap
  simp only [lowerPrepareNegConst, LowerGateClass.evalL_seq,
    LowerGateClass.evalL_X_ket]
  rw [xBasis_write_qubit q target value b hne]
  simp only [lowerAddConstFromUnit]
  rw [evalL_lowerAddBitPowers_ket]
  rw [addBitPowersBasis_write_qubit scratch unit N.bitIndices
    target value bX hdisj hqScratch hqUnit]

private lemma testBit_top_eq_decide_ge
    {w value : ℕ} (hvalue : value < 2 ^ (w + 1)) :
    Nat.testBit value w = decide (2 ^ w ≤ value) := by
  by_cases h : value < 2 ^ w
  · rw [Nat.testBit_lt_two_pow h]
    simp [Nat.not_le.mpr h]
  · have hlo : 1 * 2 ^ w ≤ value := by simpa using Nat.le_of_not_gt h
    have hhi : value < (1 + 1) * 2 ^ w := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hvalue
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rw [Nat.div_eq_of_lt_le hlo hhi]
    simp [Nat.le_of_not_gt h]

private lemma bit_sign_eq_decide_extToInt_neg
    {Basis : Type u} [RegEncoding Basis]
    (e : ExtReg) (hpos : 0 < e.width) (b : Basis) :
    RegEncoding.bit
        (e.active.get ⟨e.width - 1, by
          have hlt : e.width - 1 < e.width := by omega
          simpa [ExtReg.width, regSize] using hlt⟩) b =
      decide (extToInt e b < 0) := by
  have hw : e.width = (e.width - 1) + 1 := by omega
  rw [RegEncoding.bit_eq_testBit_toNat]
  change Nat.testBit (e.toNat b) (e.width - 1) = _
  have hlt0 := e.toNat_lt b
  have hlt : e.toNat b < 2 ^ ((e.width - 1) + 1) := by
    rw [← hw]
    exact hlt0
  rw [testBit_top_eq_decide_ge hlt]
  unfold extToInt
  rw [hw]
  simp only [tcDecodeWidth]
  by_cases h : e.toNat b < 2 ^ (e.width - 1)
  · simp [h, Nat.not_le.mpr h]
  · have hge := Nat.le_of_not_gt h
    simp [h, hge]
    exact_mod_cast hlt

private lemma evalL_X_CNOT_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (sign flag : ℕ) (b : qs.Basis) (hne : sign ≠ flag) :
    LowerGateClass.evalL (qs := qs)
        (LowGate.X flag ;; LowGate.CNOT sign flag) (qs.ket b) =
      qs.ket
        (RegEncoding.writeNat (qubitReg flag)
          (if RegEncoding.bit flag b then
            if RegEncoding.bit sign b then 1 else 0
          else
            if RegEncoding.bit sign b then 0 else 1)
          b) := by
  have hsignOut : sign ∉ (qubitReg flag).qubits := by
    simpa [qubitReg, Reg.singleton] using hne
  rw [LowerGateClass.evalL_seq, LowerGateClass.evalL_X_ket,
    LowerGateClass.evalL_CNOT_ket]
  unfold cnotBasis
  rw [if_neg hne]
  rw [RegEncoding.bit_writeNat_out (qubitReg flag)
    (if RegEncoding.bit flag b then 0 else 1) b sign hsignOut]
  cases hflag : RegEncoding.bit flag b <;>
    cases hsign : RegEncoding.bit sign b <;>
    simp [writeNat_override]

private lemma fits_difference
    {N dataValue dataWidth scratchWidth : ℕ}
    (hspos : 0 < scratchWidth)
    (hN : N < 2 ^ (scratchWidth - 1))
    (hdata : dataValue < 2 ^ dataWidth)
    (hwidth : dataWidth ≤ scratchWidth - 1) :
    FitsSignedWidth scratchWidth ((dataValue : ℤ) - N) := by
  unfold FitsSignedWidth signedMin signedMax
  refine ⟨hspos, ?_, ?_⟩
  · have hNz : (N : ℤ) < (2 : ℤ) ^ (scratchWidth - 1) := by
      exact_mod_cast hN
    have hdata0 : (0 : ℤ) ≤ dataValue := by positivity
    push_cast
    omega
  · have hp : 2 ^ dataWidth ≤ 2 ^ (scratchWidth - 1) :=
      Nat.pow_le_pow_right (by omega) hwidth
    have hdata' : dataValue < 2 ^ (scratchWidth - 1) :=
      lt_of_lt_of_le hdata hp
    have hdataZ : (dataValue : ℤ) < (2 : ℤ) ^ (scratchWidth - 1) := by
      exact_mod_cast hdata'
    have hN0 : (0 : ℤ) ≤ N := by positivity
    push_cast
    omega

private lemma evalL_compute_uncompute
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (prep diff middle : LowGate) (b b' : qs.Basis)
    (hprefix :
      LowerGateClass.evalL (qs := qs) middle
          (LowerGateClass.evalL (qs := qs) diff
            (LowerGateClass.evalL (qs := qs) prep (qs.ket b))) =
        LowerGateClass.evalL (qs := qs) diff
          (LowerGateClass.evalL (qs := qs) prep (qs.ket b'))) :
    LowerGateClass.evalL (qs := qs)
        (prep ;; diff ;; middle ;; †diff ;; †prep) (qs.ket b) =
      qs.ket b' := by
  simp only [LowerGateClass.evalL_seq]
  rw [hprefix]
  rw [LowerGateClass.evalL_adj_apply]
  rw [LowerGateClass.evalL_adj_apply]

/-- The concrete comparison lowerer implements the typed high-level basis
semantics and restores its real scratch workspace. -/
theorem evalL_lowerCmpGeConst_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag)
    (b : qs.Basis)
    (hclean : ConstArithmeticCleanBasis data scratch b) :
    LowerGateClass.evalL (qs := qs)
        (lowerCmpGeConst N data scratch flag h) (qs.ket b) =
      qs.ket (cmpGeConstBasis N data.active flag b) := by
  let q := constArithmeticUnitQubit scratch h.scratch_can_grow
  let unit := constArithmeticUnit scratch h.scratch_can_grow
  let prep := lowerPrepareNegConst N scratch h.scratch_can_grow
  let sign := scratch.active.get
    ⟨scratch.width - 1, by
      have hpos : 0 < scratch.width := h.scratch_positive
      have hlt : scratch.width - 1 < scratch.width := by omega
      simpa [ExtReg.width, regSize] using hlt⟩
  let diff :=
    LowGate.zeroExtend data 1 ;;
    LowGate.AddScaled scratch (data.grow 1) false 0 ;;
    LowGate.zeroDealloc data 1
  let middle := LowGate.X flag ;; LowGate.CNOT sign flag
  let bX := RegEncoding.writeNat (qubitReg q) 1 b
  let bprep := addBitPowersBasis scratch unit N.bitIndices bX
  let bdiff := addScaledBasis scratch (data.grow 1) false 0 bprep
  let dataValue := RegEncoding.toNat data.active b
  let flagValue :=
    if RegEncoding.bit flag b then
      if N ≤ dataValue then 0 else 1
    else
      if N ≤ dataValue then 1 else 0
  let bout := RegEncoding.writeNat (qubitReg flag) flagValue b

  have hscratchUnit : scratch.ActiveDisjoint unit :=
    scratch_unit_activeDisjoint scratch h.scratch_can_grow
  have hdataScratchGrowOwned :
      (data.grow 1).OwnedDisjoint scratch :=
    ownedDisjoint_grow_left data scratch 1 h.data_scratch_disjoint
  have hdataScratchGrow :
      (data.grow 1).ActiveDisjoint scratch :=
    activeDisjoint_of_ownedDisjoint hdataScratchGrowOwned
  have hscratchDataGrow :
      scratch.ActiveDisjoint (data.grow 1) :=
    Disjoint.symm hdataScratchGrow
  have hdataUnitOwned : data.OwnedDisjoint unit :=
    ownedDisjoint_constUnit data scratch h.scratch_can_grow
      h.data_scratch_disjoint
  have hdataUnitGrowOwned : (data.grow 1).OwnedDisjoint unit :=
    ownedDisjoint_grow_left data unit 1 hdataUnitOwned
  have hdataUnitGrow : (data.grow 1).ActiveDisjoint unit :=
    activeDisjoint_of_ownedDisjoint hdataUnitGrowOwned

  have hprep := evalL_lowerPrepareNegConst_ket
    (qs := qs) N scratch h.scratch_can_grow b
    hclean.2.1 hclean.2.2 h.scratch_positive h.constant_fits
  have hprepEval :
      LowerGateClass.evalL (qs := qs) prep (qs.ket b) = qs.ket bprep := by
    simpa [prep, bprep, bX, q, unit] using hprep.1
  have hprepScratch : extToInt scratch bprep = -(N : ℤ) := by
    simpa [bprep, bX, q, unit] using hprep.2.1

  have hdataAtB : extToInt (data.grow 1) b = (dataValue : ℤ) := by
    simpa [dataValue, ExtReg.toNat] using
      Gate.ExtReg.extToInt_grow_of_fresh data 1 b
        h.data_can_grow hclean.1 (by omega)
  have hdataAtBX : extToInt (data.grow 1) bX = (dataValue : ℤ) := by
    have hx := extToInt_writeNat_active_of_disjoint
      unit (data.grow 1) 1 b hdataUnitGrow
    simpa [bX, unit, constArithmeticUnit, ExtReg.ofReg, q, hdataAtB] using hx
  have hdataAtPrep :
      extToInt (data.grow 1) bprep = (dataValue : ℤ) := by
    have hx := addBitPowersBasis_observed
      scratch unit (data.grow 1) N.bitIndices bX
      hscratchUnit hdataScratchGrow
    simpa [bprep, hdataAtBX] using hx

  have hdataBound : dataValue < 2 ^ data.width := by
    simpa [dataValue, ExtReg.width, ASize] using
      RegEncoding.toNat_lt_ASize (r := data.active) (b := b)
  have hdiffFit :
      FitsSignedWidth scratch.width ((dataValue : ℤ) - (N : ℤ)) :=
    fits_difference h.scratch_positive h.constant_fits hdataBound
      h.data_width_fits
  have hdiffValue :
      extToInt scratch bdiff = (dataValue : ℤ) - (N : ℤ) := by
    dsimp [bdiff]
    rw [extToInt_addScaledBasis_dst
      scratch (data.grow 1) false 0 bprep hscratchDataGrow]
    simp [addScaledValue, hprepScratch, hdataAtPrep]
    have harg : -(N : ℤ) + (dataValue : ℤ) =
        (dataValue : ℤ) - (N : ℤ) := by ring
    rw [harg]
    exact tcWrapInt_eq_of_fits hdiffFit.1 hdiffFit

  have hdiffEval (z : qs.Basis) :
      LowerGateClass.evalL (qs := qs) diff (qs.ket z) =
        qs.ket (addScaledBasis scratch (data.grow 1) false 0 z) := by
    simp [diff, LowerGateClass.evalL_seq,
      LowerGateClass.evalL_zeroExtend_id,
      LowerGateClass.evalL_addScaled_ket_total,
      LowerGateClass.evalL_zeroDealloc_id]
  have hdiffEvalPrep :
      LowerGateClass.evalL (qs := qs) diff
          (LowerGateClass.evalL (qs := qs) prep (qs.ket b)) =
        qs.ket bdiff := by
    rw [hprepEval]
    simpa [bdiff] using hdiffEval bprep

  have hsignMem : sign ∈ scratch.active.qubits := by
    exact List.get_mem _ _
  have hsignNe : sign ≠ flag := by
    intro heq
    apply h.flag_not_scratch
    rw [← heq]
    exact List.mem_append_left _ hsignMem
  have hsignBit :
      RegEncoding.bit sign bdiff = decide (dataValue < N) := by
    have hs := bit_sign_eq_decide_extToInt_neg
      scratch h.scratch_positive bdiff
    have hlt :
        ((dataValue : ℤ) - (N : ℤ) < 0) ↔ dataValue < N := by
      omega
    simpa [sign, hdiffValue, hlt] using hs

  have hflagUnitNe : q ≠ flag :=
    constUnit_ne_of_not_owned scratch h.scratch_can_grow
      flag h.flag_not_scratch
  have hflagBX : RegEncoding.bit flag bX = RegEncoding.bit flag b := by
    dsimp [bX]
    apply RegEncoding.bit_writeNat_out
    simpa [qubitReg, Reg.singleton] using hflagUnitNe.symm
  have hflagPrep : RegEncoding.bit flag bprep = RegEncoding.bit flag b := by
    dsimp [bprep]
    rw [addBitPowersBasis_bit_out scratch unit N.bitIndices flag bX
      hscratchUnit h.flag_not_scratch]
    exact hflagBX
  have hflagDiff : RegEncoding.bit flag bdiff = RegEncoding.bit flag b := by
    dsimp [bdiff]
    rw [addScaledBasis_eq scratch (data.grow 1) false 0 bprep
      hscratchDataGrow]
    rw [RegEncoding.bit_writeNat_out]
    · exact hflagPrep
    · exact fun hmem => h.flag_not_scratch (List.mem_append_left _ hmem)

  have hmiddle :
      LowerGateClass.evalL (qs := qs) middle (qs.ket bdiff) =
        qs.ket (RegEncoding.writeNat (qubitReg flag) flagValue bdiff) := by
    rw [show middle = LowGate.X flag ;; LowGate.CNOT sign flag by rfl]
    rw [evalL_X_CNOT_ket sign flag bdiff hsignNe]
    apply congrArg qs.ket
    rw [hflagDiff, hsignBit]
    dsimp [flagValue]
    by_cases hge : N ≤ dataValue
    · have hnotlt : ¬ dataValue < N := Nat.not_lt.mpr hge
      simp [hge, hnotlt]
    · have hlt : dataValue < N := Nat.lt_of_not_ge hge
      simp [hge, hlt]

  have hprefix :
      LowerGateClass.evalL (qs := qs) middle
          (LowerGateClass.evalL (qs := qs) diff
            (LowerGateClass.evalL (qs := qs) prep (qs.ket b))) =
        LowerGateClass.evalL (qs := qs) diff
          (LowerGateClass.evalL (qs := qs) prep (qs.ket bout)) := by
    rw [hdiffEvalPrep, hmiddle]
    have hprepBout := evalL_lowerPrepareNegConst_write_qubit
      (qs := qs) N scratch h.scratch_can_grow flag flagValue b
      h.flag_not_scratch
    have hunitBit : RegEncoding.bit q b = false :=
      unit_bit_false_of_fresh scratch h.scratch_can_grow b hclean.2.2
    have hprepBout' :
        LowerGateClass.evalL (qs := qs) prep (qs.ket bout) =
          qs.ket (RegEncoding.writeNat (qubitReg flag) flagValue bprep) := by
      simpa [prep, bout, bprep, bX, unit, q, hunitBit] using hprepBout
    rw [hprepBout']
    rw [hdiffEval]
    apply congrArg qs.ket
    simpa [bdiff, bprep, bX, unit, q] using
      (addScaledBasis_write_qubit
        scratch (data.grow 1) 0 flag flagValue bprep
        hscratchDataGrow h.flag_not_scratch
        (by simpa [Gate.ExtReg.ownedQubits_grow] using h.flag_not_data)).symm

  have hresult := evalL_compute_uncompute
    (qs := qs) prep diff middle b bout hprefix
  rw [show lowerCmpGeConst N data scratch flag h =
      prep ;; diff ;; middle ;; †diff ;; †prep by rfl]
  rw [hresult]
  apply congrArg qs.ket
  have hflagActive : flag ∉ data.active.qubits := by
    intro hmem
    exact h.flag_not_data (List.mem_append_left _ hmem)
  simp [bout, cmpGeConstBasis, flagValue, dataValue, hflagActive]

/-- Comparison changes only its flag and restores both data and scratch
workspace, so the same clean predicate is available to the following
controlled subtraction. -/
theorem evalL_lowerCmpGeConst_preserves_clean
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag)
    (ψ : qs.State)
    (hclean : CmpGeConstCleanState qs data scratch ψ) :
    CmpGeConstCleanState qs data scratch
      (LowerGateClass.evalL (qs := qs)
        (lowerCmpGeConst N data scratch flag h) ψ) := by
  induction hclean with
  | zero =>
      rw [LowerGateClass.evalL_zero]
      exact CleanClosure.zero
  | ket b hbasis =>
      rw [evalL_lowerCmpGeConst_ket N data scratch flag h b hbasis]
      apply CleanClosure.ket
      have hflagActive : flag ∉ data.active.qubits := by
        intro hmem
        exact h.flag_not_data (List.mem_append_left _ hmem)
      let value :=
        if RegEncoding.bit flag b then
          if N ≤ RegEncoding.toNat data.active b then 0 else 1
        else if N ≤ RegEncoding.toNat data.active b then 1 else 0
      rw [show cmpGeConstBasis N data.active flag b =
          RegEncoding.writeNat (qubitReg flag) value b by
        simp [cmpGeConstBasis, hflagActive, value]]
      refine ⟨?_, ?_, ?_⟩
      · exact freshFor_write_qubit_of_not_owned
          data 1 flag value b h.flag_not_data hbasis.1
      · have hdisj := active_qubit_disjoint_of_not_owned
          scratch flag h.flag_not_scratch
        have hs := extToInt_writeNat_active_of_disjoint
          (ExtReg.ofReg (qubitReg flag)) scratch value b hdisj
        simpa [ExtReg.ofReg] using hs.trans hbasis.2.1
      · exact freshFor_write_qubit_of_not_owned
          scratch 1 flag value b h.flag_not_scratch hbasis.2.2
  | add hψ hφ ihψ ihφ =>
      rw [LowerGateClass.evalL_add]
      exact CleanClosure.add ihψ ihφ
  | smul a hψ ihψ =>
      rw [LowerGateClass.evalL_smul]
      exact CleanClosure.smul a ihψ

/-- The concrete controlled-subtraction lowerer implements the typed
high-level modular basis semantics for every control/data value and restores
the borrowed scratch workspace. -/
theorem evalL_lowerCSubConst_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag)
    (b : qs.Basis)
    (hclean : CSubConstCleanBasis N data scratch flag b) :
    LowerGateClass.evalL (qs := qs)
        (lowerCSubConst N data scratch flag h) (qs.ket b) =
      qs.ket (csubConstBasis N data.active flag b) := by
  let q := constArithmeticUnitQubit scratch h.scratch_can_grow
  let unit := constArithmeticUnit scratch h.scratch_can_grow
  let prep :=
    LowGate.CNOT flag q ;;
    lowerAddConstFromUnit N scratch unit
  let bctrl := cnotBasis flag q b
  let bprep := addBitPowersBasis scratch unit N.bitIndices bctrl
  let dataValue := data.toNat b
  let result :=
    if RegEncoding.bit flag b then
      (dataValue + ASize data.active - (N % ASize data.active)) %
        ASize data.active
    else
      dataValue
  let bout := csubConstBasis N data.active flag b

  have hqNeFlag : q ≠ flag :=
    constUnit_ne_of_not_owned scratch h.scratch_can_grow
      flag h.flag_not_scratch
  have hflagNeQ : flag ≠ q := hqNeFlag.symm
  have hunitBit : RegEncoding.bit q b = false :=
    unit_bit_false_of_fresh scratch h.scratch_can_grow b hclean.2.2
  have hscratchUnit : scratch.ActiveDisjoint unit :=
    scratch_unit_activeDisjoint scratch h.scratch_can_grow
  have hdataScratch : data.ActiveDisjoint scratch :=
    activeDisjoint_of_ownedDisjoint h.data_scratch_disjoint
  have hscratchData : scratch.ActiveDisjoint data :=
    Disjoint.symm hdataScratch
  have hdataUnitOwned : data.OwnedDisjoint unit :=
    ownedDisjoint_constUnit data scratch h.scratch_can_grow
      h.data_scratch_disjoint
  have hdataUnit : data.ActiveDisjoint unit :=
    activeDisjoint_of_ownedDisjoint hdataUnitOwned
  have hunitData : unit.ActiveDisjoint data :=
    Disjoint.symm hdataUnit
  have hqNotData : q ∉ data.ownedQubits := by
    intro hqData
    rw [ExtReg.OwnedDisjoint, List.disjoint_left] at hdataUnitOwned
    apply hdataUnitOwned hqData
    simp [unit, q, constArithmeticUnit, ExtReg.ofReg,
      ExtReg.ownedQubits, qubitReg, Reg.singleton, Reg.empty]
  have hqOutside : q ∉ data.active.qubits := by
    intro hqData
    exact hqNotData (List.mem_append_left _ hqData)
  have hflagOutside : flag ∉ data.active.qubits := by
    intro hmem
    exact h.flag_not_data (List.mem_append_left _ hmem)

  have hprepEval :
      LowerGateClass.evalL (qs := qs) prep (qs.ket b) =
        qs.ket bprep := by
    simp only [prep, LowerGateClass.evalL_seq,
      LowerGateClass.evalL_CNOT_ket, lowerAddConstFromUnit]
    rw [evalL_lowerAddBitPowers_ket]

  have hscratchPrep :
      extToInt scratch bprep =
        if RegEncoding.bit flag b then -(N : ℤ) else 0 := by
    by_cases hflag : RegEncoding.bit flag b = true
    · have hctrl :
          bctrl = RegEncoding.writeNat (qubitReg q) 1 b := by
        simp [bctrl, cnotBasis, hflagNeQ, hflag, hunitBit]
      have hscratchCtrl : extToInt scratch bctrl = 0 := by
        rw [hctrl]
        have hx := extToInt_writeNat_active_of_disjoint
          unit scratch 1 b hscratchUnit
        simpa [unit, q, constArithmeticUnit, ExtReg.ofReg,
          hclean.2.1] using hx
      have hunitCtrl : extToInt unit bctrl = -1 := by
        simpa [hctrl, unit, q] using
          unit_extToInt_after_X scratch h.scratch_can_grow b
      have hbound :
          0 + (N.bitIndices.map (fun i => 2 ^ i)).sum <
            2 ^ (scratch.width - 1) := by
        simpa using h.constant_fits
      have hneg := addBitPowersBasis_neg_sum
        scratch unit N.bitIndices bctrl hscratchUnit
        h.scratch_positive 0 hscratchCtrl hunitCtrl hbound
      simpa [bprep, hflag] using hneg
    · have hflagFalse : RegEncoding.bit flag b = false :=
        Bool.eq_false_iff.mpr hflag
      have hctrl : bctrl = b := by
        simp [bctrl, cnotBasis, hflagNeQ, hflagFalse]
      have hunitZero : extToInt unit bctrl = 0 := by
        rw [hctrl]
        exact unit_extToInt_zero_of_fresh
          scratch h.scratch_can_grow b hclean.2.2
      have hzero := addBitPowersBasis_zero_source
        scratch unit N.bitIndices bctrl hscratchUnit
        h.scratch_positive 0 (by simpa [hctrl] using hclean.2.1)
        hunitZero (by positivity)
      simpa [bprep, hflagFalse] using hzero

  have hdataCtrl : extToInt data bctrl = extToInt data b := by
    by_cases hflag : RegEncoding.bit flag b = true
    · have hctrl :
          bctrl = RegEncoding.writeNat (qubitReg q) 1 b := by
        simp [bctrl, cnotBasis, hflagNeQ, hflag, hunitBit]
      rw [hctrl]
      have hx := extToInt_writeNat_active_of_disjoint
        unit data 1 b hdataUnit
      simpa [unit, q, constArithmeticUnit, ExtReg.ofReg] using hx
    · have hflagFalse : RegEncoding.bit flag b = false :=
        Bool.eq_false_iff.mpr hflag
      simp [bctrl, cnotBasis, hflagNeQ, hflagFalse]

  have hdataPrepInt : extToInt data bprep = extToInt data b := by
    calc
      extToInt data bprep = extToInt data bctrl := by
        exact addBitPowersBasis_observed
          scratch unit data N.bitIndices bctrl
          hscratchUnit hdataScratch
      _ = extToInt data b := hdataCtrl

  have hdataPrepNat : data.toNat bprep = dataValue := by
    dsimp [dataValue]
    exact toNat_eq_of_extToInt_eq_local hdataPrepInt

  have hflagCtrl :
      RegEncoding.bit flag bctrl = RegEncoding.bit flag b := by
    by_cases hflag : RegEncoding.bit flag b = true
    · have hctrl :
          bctrl = RegEncoding.writeNat (qubitReg q) 1 b := by
        simp [bctrl, cnotBasis, hflagNeQ, hflag, hunitBit]
      rw [hctrl, RegEncoding.bit_writeNat_out]
      simpa [qubitReg, Reg.singleton] using hflagNeQ
    · have hflagFalse : RegEncoding.bit flag b = false :=
        Bool.eq_false_iff.mpr hflag
      simp [bctrl, cnotBasis, hflagNeQ, hflagFalse]

  have hflagPrep :
      RegEncoding.bit flag bprep = RegEncoding.bit flag b := by
    calc
      RegEncoding.bit flag bprep = RegEncoding.bit flag bctrl := by
        exact addBitPowersBasis_bit_out
          scratch unit N.bitIndices flag bctrl
          hscratchUnit h.flag_not_scratch
      _ = RegEncoding.bit flag b := hflagCtrl

  have hmiddle :
      addScaledBasis data scratch false 0 bprep =
        RegEncoding.writeNat data.active result bprep := by
    by_cases hflag : RegEncoding.bit flag b = true
    · have hs : extToInt scratch bprep = -(N : ℤ) := by
        simpa [hflag] using hscratchPrep
      have hx := addScaledBasis_eq_writeNat_mod_sub
        N data scratch bprep hdataScratch hs
      simpa [result, hflag, hdataPrepNat] using hx
    · have hflagFalse : RegEncoding.bit flag b = false :=
        Bool.eq_false_iff.mpr hflag
      have hs : extToInt scratch bprep = 0 := by
        simpa [hflagFalse] using hscratchPrep
      have hx := addScaledBasis_eq_writeNat_mod_sub
        0 data scratch bprep hdataScratch (by simpa using hs)
      rw [hx]
      apply congrArg
        (fun value => RegEncoding.writeNat data.active value bprep)
      simp only [Nat.zero_mod, Nat.sub_zero]
      have hlt : dataValue < ASize data.active := by
        simpa [dataValue, ExtReg.toNat] using
          RegEncoding.toNat_lt_ASize
            (r := data.active) (b := b)
      simp [result, hflagFalse, hdataPrepNat,
        Nat.mod_eq_of_lt hlt]

  have hbout :
      bout = RegEncoding.writeNat data.active result b := by
    simp [bout, csubConstBasis, hflagOutside, result, dataValue,
      ExtReg.toNat]

  have hprepWrite (value : ℕ) :
      LowerGateClass.evalL (qs := qs) prep
          (qs.ket (RegEncoding.writeNat data.active value b)) =
        qs.ket (RegEncoding.writeNat data.active value bprep) := by
    simp only [prep, LowerGateClass.evalL_seq,
      LowerGateClass.evalL_CNOT_ket, lowerAddConstFromUnit]
    rw [cnotBasis_writeNat_of_outside
      flag q data.active value b hflagOutside hqOutside]
    rw [evalL_lowerAddBitPowers_ket]
    rw [addBitPowersBasis_writeNat_of_disjoint
      scratch unit N.bitIndices data.active value bctrl
      hscratchUnit hscratchData hunitData]

  have hprepBout :
      LowerGateClass.evalL (qs := qs) prep (qs.ket bout) =
        qs.ket (RegEncoding.writeNat data.active result bprep) := by
    rw [hbout]
    exact hprepWrite result

  rw [show lowerCSubConst N data scratch flag h =
      prep ;;
      LowGate.AddScaled data scratch false 0 ;;
      †prep by rfl]
  simp only [LowerGateClass.evalL_seq]
  rw [hprepEval, LowerGateClass.evalL_addScaled_ket_total, hmiddle]
  rw [← hprepBout]
  exact LowerGateClass.evalL_adj_apply
    (qs := qs) prep (qs.ket bout)
/-- Linear extension of concrete comparison correctness to every state in the
clean-workspace span. -/
theorem evalL_lowerCmpGeConst
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ModularArithmeticSemantics qs]
    [LowerGateClass qs]
    (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag)
    (ψ : qs.State)
    (hclean : CmpGeConstCleanState qs data scratch ψ) :
    LowerGateClass.evalL (qs := qs)
        (lowerCmpGeConst N data scratch flag h) ψ =
      qs.eval (Gate.CmpGeConst N data scratch flag) ψ := by
  induction hclean with
  | zero =>
      rw [LowerGateClass.evalL_zero, QSemantics.eval_zero]
  | ket b hcleanBasis =>
      rw [evalL_lowerCmpGeConst_ket N data scratch flag h b hcleanBasis,
        ModularArithmeticSemantics.eval_CmpGeConst_ket]
  | add hψ hφ ihψ ihφ =>
      rw [LowerGateClass.evalL_add, QSemantics.eval_add, ihψ, ihφ]
  | smul a hψ ihψ =>
      rw [LowerGateClass.evalL_smul, QSemantics.eval_smul, ihψ]

/-- Linear extension of concrete controlled-subtraction correctness to every
state in the clean no-underflow span. -/
theorem evalL_lowerCSubConst
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ModularArithmeticSemantics qs]
    [LowerGateClass qs]
    (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag)
    (ψ : qs.State)
    (hclean : CSubConstCleanState qs N data scratch flag ψ) :
    LowerGateClass.evalL (qs := qs)
        (lowerCSubConst N data scratch flag h) ψ =
      qs.eval (Gate.CSubConst N data scratch flag) ψ := by
  induction hclean with
  | zero =>
      rw [LowerGateClass.evalL_zero, QSemantics.eval_zero]
  | ket b hcleanBasis =>
      rw [evalL_lowerCSubConst_ket N data scratch flag h b hcleanBasis,
        ModularArithmeticSemantics.eval_CSubConst_ket]
  | add hψ hφ ihψ ihφ =>
      rw [LowerGateClass.evalL_add, QSemantics.eval_add, ihψ, ihφ]
  | smul a hψ ihψ =>
      rw [LowerGateClass.evalL_smul, QSemantics.eval_smul, ihψ]

end Shor
