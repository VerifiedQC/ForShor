import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.ConstArithmeticLowering
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.EvalLLemmas

/-!
# Correctness of concrete Step-3 constant arithmetic lowering
-/

namespace Shor

open LowGate

private noncomputable def copyBitPowersBasis
    {Basis : Type u} [RegEncoding Basis]
    (dst : ExtReg) (ctrl : ℕ) : List ℕ → Basis → Basis
  | [], b => b
  | i :: bits, b =>
      if hi : i < dst.width then
        copyBitPowersBasis dst ctrl bits
          (cnotBasis ctrl
            (dst.active.get
              ⟨i, by simpa [ExtReg.width] using hi⟩) b)
      else
        copyBitPowersBasis dst ctrl bits b

private lemma evalL_lowerCopyBitPowers_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (dst : ExtReg) (ctrl : ℕ) (bits : List ℕ) (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs)
        (lowerCopyBitPowers dst ctrl bits) (qs.ket b) =
      qs.ket (copyBitPowersBasis dst ctrl bits b) := by
  induction bits generalizing b with
  | nil =>
      simp [lowerCopyBitPowers, copyBitPowersBasis,
        LowerGateClass.evalL_id]
  | cons i bits ih =>
      simp only [lowerCopyBitPowers, copyBitPowersBasis]
      split
      · simp only [LowerGateClass.evalL_seq,
          LowerGateClass.evalL_CNOT_ket]
        exact ih _
      · exact ih _

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

private lemma bit_cnotBasis_of_ne_target
    {Basis : Type u} [RegEncoding Basis]
    (ctrl target q : ℕ) (b : Basis)
    (hq : q ≠ target) :
    RegEncoding.bit q (cnotBasis ctrl target b) =
      RegEncoding.bit q b := by
  unfold cnotBasis
  by_cases hct : ctrl = target
  · simp [hct]
  · simp only [hct, if_false]
    by_cases hc : RegEncoding.bit ctrl b
    · simp only [hc, if_true]
      rw [RegEncoding.bit_writeNat_out]
      simpa [qubitReg, Reg.singleton] using hq
    · simp [hc]

private lemma bit_cnotBasis_target_of_true_false
    {Basis : Type u} [RegEncoding Basis]
    (ctrl target : ℕ) (b : Basis)
    (hne : ctrl ≠ target)
    (hctrl : RegEncoding.bit ctrl b = true)
    (htarget : RegEncoding.bit target b = false) :
    RegEncoding.bit target (cnotBasis ctrl target b) = true := by
  simp [cnotBasis, hne, hctrl, htarget]

private lemma copyBitPowersBasis_bit_out
    {Basis : Type u} [RegEncoding Basis]
    (dst : ExtReg) (ctrl : ℕ) (bits : List ℕ)
    (q : ℕ) (b : Basis)
    (hq : q ∉ dst.active.qubits) :
    RegEncoding.bit q (copyBitPowersBasis dst ctrl bits b) =
      RegEncoding.bit q b := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      simp only [copyBitPowersBasis]
      split
      · rw [ih]
        apply bit_cnotBasis_of_ne_target
        intro heq
        apply hq
        rw [heq]
        exact List.get_mem _ _
      · exact ih _

private lemma copyBitPowersBasis_bit_get_of_zero
    {Basis : Type u} [RegEncoding Basis]
    (dst : ExtReg) (ctrl : ℕ) (bits : List ℕ)
    (b : Basis)
    (hvalid : ∀ i ∈ bits, i < dst.width)
    (hnodup : bits.Nodup)
    (hctrlOut : ctrl ∉ dst.active.qubits)
    (hctrl : RegEncoding.bit ctrl b = true)
    (hzero : ∀ i (hi : i ∈ bits),
      RegEncoding.bit
        (dst.active.get
          ⟨i, by simpa [ExtReg.width] using hvalid i hi⟩) b = false)
    (j : Fin (regSize dst.active)) :
    RegEncoding.bit (dst.active.get j)
        (copyBitPowersBasis dst ctrl bits b) =
      if j.1 ∈ bits then true else RegEncoding.bit (dst.active.get j) b := by
  induction bits generalizing b with
  | nil => simp [copyBitPowersBasis]
  | cons i bits ih =>
      have hi : i < dst.width := hvalid i (by simp)
      have htailValid : ∀ t ∈ bits, t < dst.width := by
        intro t ht
        exact hvalid t (by simp [ht])
      have htailNodup : bits.Nodup := by
        exact (List.nodup_cons.mp hnodup).2
      have hiTail : i ∉ bits := (List.nodup_cons.mp hnodup).1
      let idx : Fin (regSize dst.active) :=
        ⟨i, by simpa [ExtReg.width] using hi⟩
      let target := dst.active.get idx
      have hctrlTarget : ctrl ≠ target := by
        intro heq
        apply hctrlOut
        rw [heq]
        exact List.get_mem _ _
      let b₁ := cnotBasis ctrl target b
      have hctrl₁ : RegEncoding.bit ctrl b₁ = true := by
        dsimp [b₁]
        rw [bit_cnotBasis_of_ne_target ctrl target ctrl b hctrlTarget]
        exact hctrl
      have htailZero : ∀ t (ht : t ∈ bits),
          RegEncoding.bit
            (dst.active.get
              ⟨t, by simpa [ExtReg.width] using htailValid t ht⟩) b₁ = false := by
        intro t ht
        have hti : t ≠ i := by
          intro heq
          apply hiTail
          simpa [heq] using ht
        have htargetNe :
            dst.active.get
                ⟨t, by simpa [ExtReg.width] using htailValid t ht⟩ ≠
              target := by
          intro heq
          have hfin := dst.active.nodup.get_inj_iff.mp heq
          exact hti (by simpa [idx] using hfin)
        dsimp [b₁]
        rw [bit_cnotBasis_of_ne_target ctrl target _ b htargetNe]
        exact hzero t (by simp [ht])
      have hrec := ih b₁ htailValid htailNodup hctrl₁ htailZero
      simp only [copyBitPowersBasis, dif_pos hi]
      rw [hrec]
      by_cases hji : j.1 = i
      · have hjidx : j = idx := Fin.ext hji
        simp only [List.mem_cons, hji, true_or, if_true]
        rw [if_neg hiTail]
        rw [hjidx]
        exact bit_cnotBasis_target_of_true_false
          ctrl target b hctrlTarget hctrl
          (by simpa [idx, target] using hzero i (by simp))
      · have htargetNe : dst.active.get j ≠ target := by
          intro heq
          have hfin := dst.active.nodup.get_inj_iff.mp heq
          apply hji
          exact congrArg Fin.val hfin
        rw [bit_cnotBasis_of_ne_target ctrl target _ b htargetNe]
        simp [hji]

private lemma mem_bitIndices_iff_testBit
    (n i : ℕ) :
    i ∈ n.bitIndices ↔ n.testBit i = true := by
  induction n using Nat.binaryRec generalizing i with
  | zero => simp
  | bit bit n ih =>
      cases bit
      · cases i with
        | zero => simp
        | succ i =>
          simp only [Nat.bitIndices_bit_false, List.mem_map,
            Nat.add_left_inj, exists_eq_right, Nat.testBit_succ]
          rw [Nat.bit_false, show (2 * n) / 2 = n by omega]
          exact ih i
      · cases i with
        | zero => simp
        | succ i =>
          simp only [Nat.bitIndices_bit_true, List.mem_cons,
            Nat.succ_ne_zero, false_or, List.mem_map, Nat.add_left_inj,
            exists_eq_right, Nat.testBit_succ]
          rw [Nat.bit_true, show (2 * n + 1) / 2 = n by omega]
          exact ih i

private lemma copyBitPowersBasis_eq_writeNat
    {Basis : Type u} [RegEncoding Basis]
    (N : ℕ) (dst : ExtReg) (ctrl : ℕ) (b : Basis)
    (hN : N < ASize dst.active)
    (hctrlOut : ctrl ∉ dst.active.qubits)
    (hctrl : RegEncoding.bit ctrl b = true)
    (hzero : RegEncoding.toNat dst.active b = 0) :
    copyBitPowersBasis dst ctrl N.bitIndices b =
      RegEncoding.writeNat dst.active N b := by
  have hvalid : ∀ i ∈ N.bitIndices, i < dst.width := by
    intro i hi
    have hpow : 2 ^ i ≤ N := Nat.two_pow_le_of_mem_bitIndices hi
    by_contra hnot
    have hwidth : dst.width ≤ i := Nat.le_of_not_gt hnot
    have hmono : 2 ^ dst.width ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) hwidth
    have hN' : N < 2 ^ dst.width := by
      simpa [ASize, ExtReg.width] using hN
    omega
  have hzeroBits : ∀ i (hi : i ∈ N.bitIndices),
      RegEncoding.bit
        (dst.active.get
          ⟨i, by simpa [ExtReg.width] using hvalid i hi⟩) b = false := by
    intro i hi
    have hbit := RegEncoding.bit_eq_testBit_toNat
      dst.active b
      ⟨i, by simpa [ExtReg.width] using hvalid i hi⟩
    rw [hzero] at hbit
    simpa using hbit
  apply RegEncoding.basis_ext
  intro q
  by_cases hq : q ∈ dst.active.qubits
  · obtain ⟨j, hj⟩ := List.get_of_mem hq
    let idx : Fin (regSize dst.active) :=
      ⟨j.1, by
        change j.1 < dst.active.qubits.length
        exact j.2⟩
    have hget : dst.active.get idx = q := by
      simpa [idx, Reg.get, regSize, Reg.width] using hj
    have hout := copyBitPowersBasis_bit_get_of_zero
      dst ctrl N.bitIndices b hvalid Nat.bitIndices_nodup
      hctrlOut hctrl hzeroBits idx
    rw [hget] at hout
    rw [hout]
    rw [← hget]
    rw [RegEncoding.bit_writeNat_of_lt dst.active N b hN idx]
    have hbase : RegEncoding.bit q b = false := by
      have hbit := RegEncoding.bit_eq_testBit_toNat dst.active b idx
      rw [hget, hzero] at hbit
      simpa using hbit
    have hbaseIdx : RegEncoding.bit (dst.active.get idx) b = false := by
      simpa [hget] using hbase
    rw [hbaseIdx]
    by_cases hmem : idx.1 ∈ N.bitIndices
    · simp [hmem, (mem_bitIndices_iff_testBit N idx.1).mp hmem]
    · have htest : N.testBit idx.1 = false := by
        exact Bool.eq_false_iff.mpr
          (fun htrue => hmem ((mem_bitIndices_iff_testBit N idx.1).mpr htrue))
      simp [hmem, htest]
  · rw [copyBitPowersBasis_bit_out dst ctrl N.bitIndices q b hq]
    exact (RegEncoding.bit_writeNat_out dst.active N b q hq).symm

private lemma copyBitPowersBasis_writeNat_of_disjoint
    {Basis : Type u} [RegEncoding Basis]
    (dst : ExtReg) (ctrl : ℕ) (bits : List ℕ)
    (r : Reg) (value : ℕ) (b : Basis)
    (hdr : Disjoint dst.active r)
    (hctrl : ctrl ∉ r.qubits) :
    copyBitPowersBasis dst ctrl bits
        (RegEncoding.writeNat r value b) =
      RegEncoding.writeNat r value
        (copyBitPowersBasis dst ctrl bits b) := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      simp only [copyBitPowersBasis]
      split
      · rw [cnotBasis_writeNat_of_outside ctrl
          (dst.active.get
            ⟨i, by simpa [ExtReg.width] using ‹i < dst.width›⟩)
          r value b hctrl]
        · exact ih _
        · rw [Disjoint, List.disjoint_left] at hdr
          exact fun hmem => hdr (List.get_mem _ _) hmem
      · exact ih _

private lemma extToInt_cnotBasis_of_target_out
    {Basis : Type u} [RegEncoding Basis]
    (observed : ExtReg) (ctrl target : ℕ) (b : Basis)
    (htarget : target ∉ observed.active.qubits) :
    extToInt observed (cnotBasis ctrl target b) =
      extToInt observed b := by
  unfold cnotBasis
  by_cases hsame : ctrl = target
  · simp [hsame]
  · simp only [hsame, if_false]
    by_cases hctrl : RegEncoding.bit ctrl b
    · simp only [hctrl, if_true]
      unfold extToInt ExtReg.toNat
      rw [RegEncoding.toNat_left_write_right]
      rw [Disjoint, List.disjoint_left]
      intro q hqObserved hqTarget
      have hq : q = target := by
        simpa [qubitReg, Reg.singleton] using hqTarget
      exact htarget (hq ▸ hqObserved)
    · simp [hctrl]

private lemma copyBitPowersBasis_observed
    {Basis : Type u} [RegEncoding Basis]
    (dst observed : ExtReg) (ctrl : ℕ) (bits : List ℕ) (b : Basis)
    (hod : observed.ActiveDisjoint dst) :
    extToInt observed (copyBitPowersBasis dst ctrl bits b) =
      extToInt observed b := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      simp only [copyBitPowersBasis]
      split
      · rw [ih]
        apply extToInt_cnotBasis_of_target_out observed ctrl _ b
        rw [ExtReg.ActiveDisjoint, Disjoint, List.disjoint_left] at hod
        exact fun hmem => hod hmem (List.get_mem _ _)
      · exact ih _

private lemma copyBitPowersBasis_of_ctrl_false
    {Basis : Type u} [RegEncoding Basis]
    (dst : ExtReg) (ctrl : ℕ) (bits : List ℕ) (b : Basis)
    (hctrl : RegEncoding.bit ctrl b = false) :
    copyBitPowersBasis dst ctrl bits b = b := by
  induction bits generalizing b with
  | nil => rfl
  | cons i bits ih =>
      simp only [copyBitPowersBasis]
      split
      · have hcnot : cnotBasis ctrl
            (dst.active.get
              ⟨i, by simpa [ExtReg.width] using ‹i < dst.width›⟩) b = b := by
          simp [cnotBasis, hctrl]
        rw [hcnot]
        exact ih b hctrl
      · exact ih b hctrl

private lemma negateBasis_writeNat_of_disjoint
    {Basis : Type u} [RegEncoding Basis]
    (r : ExtReg) (observed : Reg) (value : ℕ) (b : Basis)
    (hdisj : Disjoint r.active observed) :
    negateBasis r (RegEncoding.writeNat observed value b) =
      RegEncoding.writeNat observed value (negateBasis r b) := by
  unfold negateBasis
  have hint :
      extToInt r (RegEncoding.writeNat observed value b) =
        extToInt r b := by
    unfold extToInt ExtReg.toNat
    rw [RegEncoding.toNat_left_write_right
      r.active observed hdisj b value]
  rw [hint]
  exact RegEncoding.writeNat_comm_of_disjoint
    r.active observed hdisj _ value b

private lemma negateBasis_bit_out
    {Basis : Type u} [RegEncoding Basis]
    (r : ExtReg) (q : ℕ) (b : Basis)
    (hq : q ∉ r.active.qubits) :
    RegEncoding.bit q (negateBasis r b) = RegEncoding.bit q b := by
  unfold negateBasis
  exact RegEncoding.bit_writeNat_out r.active _ b q hq

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
    let bcopy := copyBitPowersBasis scratch q N.bitIndices bX
    let bout := negateBasis scratch bcopy
    LowerGateClass.evalL (qs := qs)
        (lowerPrepareNegConst N scratch hcap) (qs.ket b) = qs.ket bout ∧
      extToInt scratch bout = -(N : ℤ) ∧
      extToInt unit bout = -1 := by
  dsimp
  let q := constArithmeticUnitQubit scratch hcap
  let unit := constArithmeticUnit scratch hcap
  let bX := RegEncoding.writeNat (qubitReg q) 1 b
  let bcopy := copyBitPowersBasis scratch q N.bitIndices bX
  let bout := negateBasis scratch bcopy
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
  have hqOut : q ∉ scratch.active.qubits := by
    intro hq
    rw [ExtReg.ActiveDisjoint, Disjoint, List.disjoint_left] at hdisj
    apply hdisj hq
    simp [unit, q, constArithmeticUnit, ExtReg.ofReg,
      qubitReg, Reg.singleton]
  have hNFull : N < ASize scratch.active := by
    have hpow : 2 ^ (scratch.width - 1) ≤ 2 ^ scratch.width :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    exact lt_of_lt_of_le hN
      (by simpa [ASize, ExtReg.width] using hpow)
  let bzero := RegEncoding.writeNat scratch.active 0 b
  have hbzeroInt : extToInt scratch bzero = 0 := by
    simpa [bzero] using
      extToInt_writeNat_of_lt_signed scratch 0 b (by positivity) hpos
  have hscratchNatX : RegEncoding.toNat scratch.active bX = 0 := by
    have hnat := toNat_eq_of_extToInt_eq_local
      (e := scratch) (b₁ := bX) (b₂ := bzero)
      (hscratchX.trans hbzeroInt.symm)
    rw [show ExtReg.toNat scratch bzero = 0 by
      dsimp [ExtReg.toNat, bzero]
      exact RegEncoding.toNat_writeNat_of_lt
        scratch.active 0 b
          (by simp [ASize])] at hnat
    exact hnat
  have hcopyEq :
      bcopy = RegEncoding.writeNat scratch.active N bX := by
    dsimp [bcopy]
    exact copyBitPowersBasis_eq_writeNat
      N scratch q bX hNFull hqOut
        (bit_write_qubit_one q b) hscratchNatX
  have hcopyInt : extToInt scratch bcopy = (N : ℤ) := by
    rw [hcopyEq]
    exact extToInt_writeNat_of_lt_signed scratch N bX hN hpos
  have hout : extToInt scratch bout = -(N : ℤ) := by
    dsimp [bout]
    rw [extToInt_negateBasis, hcopyInt]
    exact tcWrapInt_eq_of_fits hpos
      (fits_neg_nat_of_lt_half hpos hN)
  have hunitOut : extToInt unit bout = -1 := by
    dsimp [bout]
    rw [extToInt_negateBasis_of_activeDisjoint
      scratch unit bcopy (Disjoint.symm hdisj)]
    dsimp [bcopy]
    rw [copyBitPowersBasis_observed
      scratch unit q N.bitIndices bX (Disjoint.symm hdisj), hunitX]
  refine ⟨?_, hout, hunitOut⟩
  simp only [lowerPrepareNegConst, LowerGateClass.evalL_seq,
    LowerGateClass.evalL_X_ket]
  rw [hbit]
  simp only [lowerCopyConstFromUnit]
  rw [evalL_lowerCopyBitPowers_ket]
  rw [LowerGateClass.evalL_negate_ket_total]
  rfl

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
    let bX := RegEncoding.writeNat (qubitReg q)
      (if RegEncoding.bit q b then 0 else 1) b
    let bcopy := copyBitPowersBasis scratch q N.bitIndices bX
    let bout := negateBasis scratch bcopy
    LowerGateClass.evalL (qs := qs)
        (lowerPrepareNegConst N scratch hcap)
        (qs.ket (RegEncoding.writeNat (qubitReg target) value b)) =
      qs.ket (RegEncoding.writeNat (qubitReg target) value bout) := by
  dsimp
  let q := constArithmeticUnitQubit scratch hcap
  let bX := RegEncoding.writeNat (qubitReg q)
    (if RegEncoding.bit q b then 0 else 1) b
  let bcopy := copyBitPowersBasis scratch q N.bitIndices bX
  let bout := negateBasis scratch bcopy
  have hne : q ≠ target := constUnit_ne_of_not_owned scratch hcap target htarget
  have hdisj : Disjoint scratch.active (qubitReg target) :=
    active_qubit_disjoint_of_not_owned scratch target htarget
  have hctrlOut : q ∉ (qubitReg target).qubits := by
    simpa [qubitReg, Reg.singleton] using hne
  simp only [lowerPrepareNegConst, LowerGateClass.evalL_seq,
    LowerGateClass.evalL_X_ket]
  rw [xBasis_write_qubit q target value b hne]
  simp only [lowerCopyConstFromUnit]
  rw [evalL_lowerCopyBitPowers_ket]
  rw [copyBitPowersBasis_writeNat_of_disjoint
    scratch q N.bitIndices (qubitReg target) value bX hdisj hctrlOut]
  rw [LowerGateClass.evalL_negate_ket_total]
  rw [negateBasis_writeNat_of_disjoint
    scratch (qubitReg target) value bcopy hdisj]

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
  let bcopy := copyBitPowersBasis scratch q N.bitIndices bX
  let bprep := negateBasis scratch bcopy
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
    simpa [prep, bprep, bcopy, bX, q, unit] using hprep.1
  have hprepScratch : extToInt scratch bprep = -(N : ℤ) := by
    simpa [bprep, bcopy, bX, q, unit] using hprep.2.1

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
    dsimp [bprep]
    rw [extToInt_negateBasis_of_activeDisjoint
      scratch (data.grow 1) bcopy hdataScratchGrow]
    dsimp [bcopy]
    rw [copyBitPowersBasis_observed
      scratch (data.grow 1) q N.bitIndices bX hdataScratchGrow,
      hdataAtBX]

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
    rw [negateBasis_bit_out scratch flag bcopy
      (fun hmem => h.flag_not_scratch (List.mem_append_left _ hmem))]
    dsimp [bcopy]
    rw [copyBitPowersBasis_bit_out scratch q N.bitIndices flag bX
      (fun hmem => h.flag_not_scratch (List.mem_append_left _ hmem))]
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
      simpa [prep, bout, bprep, bcopy, bX, unit, q, hunitBit] using hprepBout
    rw [hprepBout']
    rw [hdiffEval]
    apply congrArg qs.ket
    simpa [bdiff, bprep, bcopy, bX, unit, q] using
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
    lowerCopyConstFromUnit N scratch q ;;
    LowGate.Negate scratch
  let bctrl := cnotBasis flag q b
  let bcopy := copyBitPowersBasis scratch q N.bitIndices bctrl
  let bprep := negateBasis scratch bcopy
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
  have hqOutsideScratch : q ∉ scratch.active.qubits := by
    intro hmem
    rw [ExtReg.ActiveDisjoint, Disjoint, List.disjoint_left] at hscratchUnit
    apply hscratchUnit hmem
    simp [unit, q, constArithmeticUnit, ExtReg.ofReg,
      qubitReg, Reg.singleton]
  have hNFull : N < ASize scratch.active := by
    have hpow : 2 ^ (scratch.width - 1) ≤ 2 ^ scratch.width :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    exact lt_of_lt_of_le h.constant_fits
      (by simpa [ASize, ExtReg.width] using hpow)

  have hprepEval :
      LowerGateClass.evalL (qs := qs) prep (qs.ket b) =
        qs.ket bprep := by
    simp only [prep, LowerGateClass.evalL_seq,
      LowerGateClass.evalL_CNOT_ket, lowerCopyConstFromUnit]
    rw [evalL_lowerCopyBitPowers_ket]
    rw [LowerGateClass.evalL_negate_ket_total]

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
      let bzero := RegEncoding.writeNat scratch.active 0 bctrl
      have hbzeroInt : extToInt scratch bzero = 0 := by
        simpa [bzero] using extToInt_writeNat_of_lt_signed
          scratch 0 bctrl (by positivity) h.scratch_positive
      have hscratchNatCtrl :
          RegEncoding.toNat scratch.active bctrl = 0 := by
        have hnat := toNat_eq_of_extToInt_eq_local
          (e := scratch) (b₁ := bctrl) (b₂ := bzero)
          (hscratchCtrl.trans hbzeroInt.symm)
        rw [show ExtReg.toNat scratch bzero = 0 by
          dsimp [ExtReg.toNat, bzero]
          exact RegEncoding.toNat_writeNat_of_lt
            scratch.active 0 bctrl
              (by simp [ASize])] at hnat
        exact hnat
      have hcopyEq :
          bcopy = RegEncoding.writeNat scratch.active N bctrl := by
        dsimp [bcopy]
        exact copyBitPowersBasis_eq_writeNat
          N scratch q bctrl hNFull hqOutsideScratch
            (by rw [hctrl]; exact bit_write_qubit_one q b)
            hscratchNatCtrl
      have hcopyInt : extToInt scratch bcopy = (N : ℤ) := by
        rw [hcopyEq]
        exact extToInt_writeNat_of_lt_signed scratch N bctrl
          h.constant_fits h.scratch_positive
      dsimp [bprep]
      rw [extToInt_negateBasis, hcopyInt]
      simpa [hflag] using tcWrapInt_eq_of_fits h.scratch_positive
        (fits_neg_nat_of_lt_half h.scratch_positive h.constant_fits)
    · have hflagFalse : RegEncoding.bit flag b = false :=
        Bool.eq_false_iff.mpr hflag
      have hctrl : bctrl = b := by
        simp [bctrl, cnotBasis, hflagNeQ, hflagFalse]
      have hqCtrl : RegEncoding.bit q bctrl = false := by
        simpa [hctrl] using hunitBit
      have hcopyEq : bcopy = bctrl := by
        dsimp [bcopy]
        exact copyBitPowersBasis_of_ctrl_false
          scratch q N.bitIndices bctrl hqCtrl
      have hfit : FitsSignedWidth scratch.width (0 : ℤ) :=
        fits_nat_of_lt_half h.scratch_positive (n := 0) (by positivity)
      dsimp [bprep]
      rw [extToInt_negateBasis, hcopyEq, hctrl, hclean.2.1]
      simpa [hflagFalse] using
        tcWrapInt_eq_of_fits h.scratch_positive hfit

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
      extToInt data bprep = extToInt data bcopy := by
        exact extToInt_negateBasis_of_activeDisjoint
          scratch data bcopy hdataScratch
      _ = extToInt data bctrl := by
        exact copyBitPowersBasis_observed
          scratch data q N.bitIndices bctrl hdataScratch
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
      RegEncoding.bit flag bprep = RegEncoding.bit flag bcopy := by
        exact negateBasis_bit_out scratch flag bcopy
          (fun hmem => h.flag_not_scratch
            (List.mem_append_left _ hmem))
      _ = RegEncoding.bit flag bctrl := by
        exact copyBitPowersBasis_bit_out
          scratch q N.bitIndices flag bctrl
          (fun hmem => h.flag_not_scratch
            (List.mem_append_left _ hmem))
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
      LowerGateClass.evalL_CNOT_ket, lowerCopyConstFromUnit]
    rw [cnotBasis_writeNat_of_outside
      flag q data.active value b hflagOutside hqOutside]
    rw [evalL_lowerCopyBitPowers_ket]
    rw [copyBitPowersBasis_writeNat_of_disjoint
      scratch q N.bitIndices data.active value bctrl
      hscratchData hqOutside]
    rw [LowerGateClass.evalL_negate_ket_total]
    rw [negateBasis_writeNat_of_disjoint
      scratch data.active value bcopy hscratchData]

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
