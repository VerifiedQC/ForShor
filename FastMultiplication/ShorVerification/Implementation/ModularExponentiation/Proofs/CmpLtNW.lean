import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.CmpLtNW
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Decomposition
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.NaiveShor.Lemmas

/-!
# Exact correctness of the concrete `CmpLtNW` circuit

The comparator computes `N * work` into a clean scratch register with a
QFT/phase-product/IQFT sandwich, forms the signed difference
`2^|work| * data - N * work`, copies its sign bit to `flag`, and then
uncomputes both temporary stages.  The final theorem is exact on basis states;
all scratch and reserve qubits are restored.
-/

namespace Shor
open Gate

private lemma cmpLtNW_testBit_top_eq_decide_ge
    {w u : ℕ} (hu : u < 2 ^ (w + 1)) :
    Nat.testBit u w = decide (2 ^ w ≤ u) := by
  by_cases h : u < 2 ^ w
  · rw [Nat.testBit_lt_two_pow h]
    simp [Nat.not_le.mpr h]
  · have hlo : 1 * 2 ^ w ≤ u := by simpa using Nat.le_of_not_gt h
    have hhi : u < (1 + 1) * 2 ^ w := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hu
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rw [Nat.div_eq_of_lt_le hlo hhi]
    simp [Nat.le_of_not_gt h]

private lemma cmpLtNW_bit_msb_eq_decide_extToInt_neg
    {Basis : Type u} [RegEncoding Basis]
    (e : ExtReg) (hpos : 0 < regSize e.active) (b : Basis) :
    RegEncoding.bit
        (e.active.get ⟨regSize e.active - 1, by
          have hlt : regSize e.active - 1 < regSize e.active := by omega
          simpa [regSize] using hlt⟩) b
      = decide (extToInt e b < 0) := by
  have hw : e.width = (e.width - 1) + 1 := by
    unfold ExtReg.width at *
    omega
  rw [RegEncoding.bit_eq_testBit_toNat]
  change Nat.testBit (e.toNat b) (regSize e.active - 1) = _
  change Nat.testBit (e.toNat b) (e.width - 1) = _
  have hlt0 := e.toNat_lt b
  have hlt : e.toNat b < 2 ^ ((e.width - 1) + 1) := by
    rw [← hw]
    exact hlt0
  rw [cmpLtNW_testBit_top_eq_decide_ge hlt]
  unfold extToInt
  rw [hw]
  simp only [tcDecodeWidth]
  by_cases h : e.toNat b < 2 ^ (e.width - 1)
  · simp [h, Nat.not_le.mpr h]
  · have hge := Nat.le_of_not_gt h
    simp [h, hge]
    exact_mod_cast hlt

private theorem cmpLtNW_value_bounds
    (N d w dataValue workValue : ℕ)
    (hdata : dataValue < 2 ^ d)
    (hwork : workValue < 2 ^ w) :
    let width :=
      2 + max (d + w) (Nat.log2 (N + 1) + 1 + w)
    N * workValue < 2 ^ (width - 1) ∧
      FitsSignedWidth width
        ((2 : ℤ) ^ w * (dataValue : ℤ) - (N * workValue : ℕ)) := by
  dsimp only
  let m := max (d + w) (Nat.log2 (N + 1) + 1 + w)
  have hN1 : N + 1 ≠ 0 := by omega
  have hNsucc :
      N + 1 < 2 ^ (Nat.log2 (N + 1) + 1) :=
    (Nat.log2_lt hN1).mp (by omega)
  have hN : N < 2 ^ (Nat.log2 (N + 1) + 1) := by omega
  have hproduct0 :
      N * workValue <
        2 ^ (Nat.log2 (N + 1) + 1) * 2 ^ w := by
    nlinarith [show 0 < 2 ^ w by positivity,
      show 0 < 2 ^ (Nat.log2 (N + 1) + 1) by positivity]
  have hproduct1 :
      N * workValue <
        2 ^ (Nat.log2 (N + 1) + 1 + w) := by
    simpa [pow_add] using hproduct0
  have hproduct : N * workValue < 2 ^ m := by
    exact lt_of_lt_of_le hproduct1
      (Nat.pow_le_pow_right (by omega)
        (le_max_right (d + w) (Nat.log2 (N + 1) + 1 + w)))
  have hscaled0 : dataValue * 2 ^ w < 2 ^ d * 2 ^ w := by
    nlinarith [show 0 < 2 ^ w by positivity]
  have hscaled1 : dataValue * 2 ^ w < 2 ^ (d + w) := by
    simpa [pow_add] using hscaled0
  have hscaled : dataValue * 2 ^ w < 2 ^ m := by
    exact lt_of_lt_of_le hscaled1
      (Nat.pow_le_pow_right (by omega)
        (le_max_left (d + w) (Nat.log2 (N + 1) + 1 + w)))
  constructor
  · have hm : m < (2 + m) - 1 := by omega
    exact lt_of_lt_of_le hproduct
      (Nat.pow_le_pow_right (by omega) hm.le)
  unfold FitsSignedWidth signedMin signedMax
  constructor
  · omega
  constructor
  · have hproductZ : (N * workValue : ℕ) < 2 ^ m := hproduct
    have hscaledNonneg : (0 : ℤ) ≤ (2 : ℤ) ^ w * dataValue := by positivity
    have hpow :
        (((2 ^ ((2 + m) - 1) : ℕ) : ℤ)) =
          2 * ((2 ^ m : ℕ) : ℤ) := by
      rw [show (2 + m) - 1 = m + 1 by omega, pow_succ]
      simp [Nat.mul_comm]
    rw [hpow]
    have hproductCast :
        ((N * workValue : ℕ) : ℤ) < ((2 ^ m : ℕ) : ℤ) := by
      exact_mod_cast hproduct
    nlinarith
  · have hscaledZ : (dataValue * 2 ^ w : ℕ) < 2 ^ m := hscaled
    have hproductNonneg : (0 : ℤ) ≤ (N * workValue : ℕ) := by positivity
    have hpow :
        (((2 ^ ((2 + m) - 1) : ℕ) : ℤ)) =
          2 * ((2 ^ m : ℕ) : ℤ) := by
      rw [show (2 + m) - 1 = m + 1 by omega, pow_succ]
      simp [Nat.mul_comm]
    rw [hpow]
    have hscaledCast :
        ((dataValue * 2 ^ w : ℕ) : ℤ) < ((2 ^ m : ℕ) : ℤ) := by
      exact_mod_cast hscaled
    push_cast at hscaledCast
    norm_num at hscaledCast ⊢
    nlinarith

private lemma cmpLtNW_fitsSignedWidth_neg_nat_of_lt_pow
    {w q : ℕ} (hq : q < 2 ^ w) :
    FitsSignedWidth (w + 1) (-(q : ℤ)) := by
  unfold FitsSignedWidth signedMin signedMax
  simp only [Nat.add_sub_cancel]
  refine ⟨by omega, ?_, ?_⟩
  · exact neg_le_neg (by exact_mod_cast hq.le)
  · have hq0 : (0 : ℤ) ≤ (q : ℤ) := by positivity
    have hp : (0 : ℤ) < (2 : ℤ) ^ w := by positivity
    omega

private lemma cmpLtNW_activeDisjoint_of_ownedDisjoint
    {x z : ExtReg} (h : x.OwnedDisjoint z) : x.ActiveDisjoint z := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h
  rw [ExtReg.ActiveDisjoint, Disjoint, List.disjoint_left]
  intro q hx hz
  exact h (List.mem_append_left _ hx) (List.mem_append_left _ hz)

private lemma cmpLtNW_ownedDisjoint_grow_left
    (x z : ExtReg) (n : ℕ)
    (h : x.OwnedDisjoint z) : (x.grow n).OwnedDisjoint z := by
  rw [ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow]
  exact h

private lemma eval_cmpLtNWDifference_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (data work scratch : ExtReg) (hdata : data.CanGrow 1)
    (b : qs.Basis) (hdataFresh : data.FreshFor 1 b)
    (q x : ℕ)
    (hscratch : extToInt scratch b = (q : ℤ))
    (hx : RegEncoding.toNat data.active b = x)
    (hnegfit : FitsSignedWidth scratch.width (-(q : ℤ)))
    (hdifffit : FitsSignedWidth scratch.width
      (-(q : ℤ) + (2 : ℤ) ^ (regSize work.active) * (x : ℤ)))
    (hdisj : data.OwnedDisjoint scratch) :
    let bneg := negateBasis scratch b
    let bout := addScaledBasis scratch (data.grow 1) false
      (regSize work.active) bneg
    qs.eval (cmpLtNWDifference data work scratch hdata) (qs.ket b) = qs.ket bout ∧
    extToInt scratch bout =
      -(q : ℤ) + (2 : ℤ) ^ (regSize work.active) * (x : ℤ) := by
  dsimp
  let bneg := negateBasis scratch b
  let bout := addScaledBasis scratch (data.grow 1) false
    (regSize work.active) bneg
  have hdg_s : (data.grow 1).ActiveDisjoint scratch :=
    cmpLtNW_activeDisjoint_of_ownedDisjoint
      (cmpLtNW_ownedDisjoint_grow_left data scratch 1 hdisj)
  have hs_dg : scratch.ActiveDisjoint (data.grow 1) := Disjoint.symm hdg_s
  have hsrc0 : extToInt (data.grow 1) b = (x : ℤ) := by
    rw [Gate.ExtReg.extToInt_grow_of_fresh data 1 b hdata hdataFresh (by omega)]
    simp [ExtReg.toNat, hx]
  have hneg : extToInt scratch bneg = -(q : ℤ) := by
    dsimp [bneg]
    rw [extToInt_negateBasis, hscratch]
    exact tcWrapInt_eq_of_fits hnegfit.1 hnegfit
  have hsrc : extToInt (data.grow 1) bneg = (x : ℤ) := by
    dsimp [bneg]
    rw [extToInt_negateBasis_of_activeDisjoint scratch (data.grow 1) b hdg_s]
    exact hsrc0
  constructor
  · simp [cmpLtNWDifference, qs.eval_seq,
      ExtensionSemantics.eval_zeroExtend, ExtensionSemantics.eval_zeroDealloc,
      ArithmeticSemantics.eval_Negate_ket_total,
      ArithmeticSemantics.eval_AddScaled_ket_total]
  · dsimp [bout]
    rw [extToInt_addScaledBasis_dst scratch (data.grow 1) false
      (regSize work.active) bneg hs_dg]
    simp [addScaledValue, hneg, hsrc]
    exact tcWrapInt_eq_of_fits hdifffit.1 hdifffit

private lemma cmpLtNW_active_qubit_disjoint_of_not_owned
    (e : ExtReg) (q : ℕ) (hq : q ∉ e.ownedQubits) :
    Disjoint e.active (qubitReg q) := by
  rw [Disjoint, List.disjoint_left]
  intro p hp hpsingle
  have hpq : p = q := by
    simpa [qubitReg, Reg.singleton] using hpsingle
  subst p
  exact hq (List.mem_append_left _ hp)

private lemma cmpLtNW_grow_active_qubit_disjoint_of_not_owned
    (e : ExtReg) (n q : ℕ) (hq : q ∉ e.ownedQubits) :
    Disjoint (e.grow n).active (qubitReg q) := by
  rw [Disjoint, List.disjoint_left]
  intro p hp hpsingle
  have hpq : p = q := by
    simpa [qubitReg, Reg.singleton] using hpsingle
  subst p
  apply hq
  have howned : q ∈ (e.grow n).ownedQubits :=
    List.mem_append_left _ hp
  simpa [Gate.ExtReg.ownedQubits_grow] using howned

private lemma cmpLtNW_freshFor_write_qubit_of_not_owned
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

private lemma cmpLtNW_freshFor_write_active_disjoint
    {Basis : Type u} [RegEncoding Basis]
    (x z : ExtReg) (n value : ℕ) (b : Basis)
    (hdisj : ExtReg.OwnedDisjoint x z)
    (hfresh : x.FreshFor n b) :
    x.FreshFor n (RegEncoding.writeNat z.active value b) := by
  unfold ExtReg.FreshFor at hfresh ⊢
  apply FreshZero.of_eq_on_bits (x.newBits n) b
    (RegEncoding.writeNat z.active value b) ?_ hfresh
  intro q hq
  apply RegEncoding.bit_writeNat_out
  intro hqz
  rw [ExtReg.OwnedDisjoint, List.disjoint_left] at hdisj
  apply hdisj (a := q)
  · exact List.mem_append_right _ (List.mem_of_mem_take hq)
  · exact List.mem_append_left _ hqz

private lemma cmpLtNW_negateBasis_write_qubit
    {Basis : Type u} [RegEncoding Basis]
    (r : ExtReg) (q value : ℕ) (b : Basis)
    (hq : q ∉ r.ownedQubits) :
    negateBasis r (RegEncoding.writeNat (qubitReg q) value b) =
      RegEncoding.writeNat (qubitReg q) value (negateBasis r b) := by
  have hdisj := cmpLtNW_active_qubit_disjoint_of_not_owned r q hq
  unfold negateBasis
  have hint :
      extToInt r (RegEncoding.writeNat (qubitReg q) value b) =
        extToInt r b := by
    unfold extToInt ExtReg.toNat
    rw [RegEncoding.toNat_left_write_right
      r.active (qubitReg q) hdisj b value]
  rw [hint]
  exact RegEncoding.writeNat_comm_of_disjoint
    r.active (qubitReg q) hdisj _ value b

private lemma cmpLtNW_addScaledBasis_write_qubit
    {Basis : Type u} [RegEncoding Basis]
    (dst src : ExtReg) (negSrc : Bool) (sh q value : ℕ) (b : Basis)
    (hds : dst.ActiveDisjoint src)
    (hqdst : q ∉ dst.ownedQubits)
    (hqsrc : q ∉ src.ownedQubits) :
    addScaledBasis dst src negSrc sh
        (RegEncoding.writeNat (qubitReg q) value b) =
      RegEncoding.writeNat (qubitReg q) value
        (addScaledBasis dst src negSrc sh b) := by
  rw [addScaledBasis_eq dst src negSrc sh _ hds,
    addScaledBasis_eq dst src negSrc sh b hds]
  have hdstDisj := cmpLtNW_active_qubit_disjoint_of_not_owned dst q hqdst
  have hsrcDisj := cmpLtNW_active_qubit_disjoint_of_not_owned src q hqsrc
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
  rw [show addScaledValue dst src negSrc sh
        (RegEncoding.writeNat (qubitReg q) value b) =
      addScaledValue dst src negSrc sh b by
        simp [addScaledValue, hdst, hsrc]]
  exact RegEncoding.writeNat_comm_of_disjoint
    dst.active (qubitReg q) hdstDisj _ value b

private lemma cmpLtNW_extToInt_writeNat_of_lt_signed
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

private lemma cmpLtNWSignQubit_bit
    {Basis : Type u} [RegEncoding Basis]
    (scratch : ExtReg) (hpos : 0 < regSize scratch.active) (b : Basis) :
    RegEncoding.bit (cmpLtNWSignQubit scratch hpos) b =
      decide (extToInt scratch b < 0) := by
  simpa [cmpLtNWSignQubit] using
    cmpLtNW_bit_msb_eq_decide_extToInt_neg scratch hpos b

private lemma cmpLtNW_eval_compute_cnot_uncompute
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs]
    (mul diff : Gate) (sign flag : ℕ) (b b' : qs.Basis)
    (hprefix :
      qs.eval (Gate.CNOT sign flag)
          (qs.eval diff (qs.eval mul (qs.ket b))) =
        qs.eval diff (qs.eval mul (qs.ket b'))) :
    qs.eval
        (mul ;; diff ;; Gate.CNOT sign flag ;; †diff ;; †mul)
        (qs.ket b) = qs.ket b' := by
  simp only [qs.eval_seq]
  rw [hprefix]
  rw [qs.eval_adj_apply]
  rw [qs.eval_adj_apply]

private theorem cmpLtNW_toNat_qubitReg_eq_bit
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

private theorem cmpLtNW_writeNat_current_qubit
    {Basis : Type*} [RegEncoding Basis]
    (q : ℕ) (b : Basis) :
    RegEncoding.writeNat (qubitReg q)
        (if RegEncoding.bit q b then 1 else 0) b = b := by
  rw [show (if RegEncoding.bit q b then 1 else 0) =
      RegEncoding.toNat (qubitReg q) b by
        rw [cmpLtNW_toNat_qubitReg_eq_bit]
        cases RegEncoding.bit q b <;> rfl]
  exact RegEncoding.writeNat_toNat (qubitReg q) b

private theorem cmpLtNW_mulWorkspace_clean
    {qs : QSemantics} [RegEncoding qs.Basis]
    (N : ℕ) (data work scratch : ExtReg) (flag : ℕ)
    (hws : CmpLtNWWorkspace N data work scratch flag)
    (b : qs.Basis)
    (hworkFresh : work.FreshFor 1 b)
    (hscratchFresh : scratch.FreshFor 1 b) :
    hws.mulWorkspace.Clean b := by
  constructor
  · simpa [Gate.PhaseProdWorkspace.xExt, ExtReg.FreshFor,
      ExtReg.newBits, ExtReg.withReserve, hws.mul_xReserve_eq] using hworkFresh
  · simpa [Gate.PhaseProdWorkspace.zExt, ExtReg.FreshFor,
      ExtReg.newBits, ExtReg.withReserve, hws.mul_zReserve_eq] using hscratchFresh

private theorem eval_fastConstMulInto_ket
    {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (N : ℕ) (work scratch : ExtReg)
    (ws : Gate.PhaseProdWorkspace work.active scratch.active)
    (b : qs.Basis) (hclean : ws.Clean b)
    (hscratchZero : RegEncoding.toNat scratch.active b = 0) :
    qs.eval (fastConstMulInto N work scratch ws) (qs.ket b) =
      qs.ket (RegEncoding.writeNat scratch.active
        ((N * RegEncoding.toNat work.active b) % ASize scratch.active) b) := by
  classical
  let M : ℕ := ASize scratch.active
  let a : ℕ := (N * RegEncoding.toNat work.active b) % M
  let target : qs.Basis := RegEncoding.writeNat scratch.active a b
  have hM : 0 < M := by simp [M, ASize]
  have ha : a < M := Nat.mod_lt _ hM
  have hzactive : ws.zExt.active = scratch.active := rfl
  have hzwidth : ws.zExt.width = regSize scratch.active := rfl
  have hphase (y : Fin M) :
      qs.eval (Gate.PhaseProdUsing
          ((2 * Real.pi * (N : ℝ)) / (ASize ws.zExt.active : ℝ))
          work.active scratch.active ws)
          (qs.ket (RegEncoding.writeNat scratch.active y.1 b)) =
        qftPhase M (N * RegEncoding.toNat work.active b) y.1 •
          qs.ket (RegEncoding.writeNat scratch.active y.1 b) := by
    have hcleanY : ws.Clean (RegEncoding.writeNat scratch.active y.1 b) :=
      Gate.PhaseProdWorkspace.Clean.writeRight qs ws b y.1 hclean
    rw [GateSemanticsFacts.eval_PhaseProdUsing_ket qs
      ((2 * Real.pi * (N : ℝ)) / (ASize ws.zExt.active : ℝ))
      work.active scratch.active ws
      (RegEncoding.writeNat scratch.active y.1 b) hcleanY]
    have hwork := RegEncoding.toNat_left_write_right
      work.active scratch.active ws.xz_disjoint b y.1
    have hscratch := RegEncoding.toNat_writeNat_of_lt
      scratch.active y.1 b y.isLt
    rw [hwork, hscratch]
    have hmain := exp_phaseProd_eq_qftPhase M
      (N * RegEncoding.toNat work.active b) y.1
    rw [show Complex.exp
      (↑((2 * Real.pi * (N : ℝ)) / (ASize ws.zExt.active : ℝ)) * Complex.I *
        (↑(RegEncoding.toNat work.active b) * ↑y.1)) =
      qftPhase M (N * RegEncoding.toNat work.active b) y.1 by
        simpa [M, hzactive, Nat.cast_mul, div_eq_mul_inv,
          mul_assoc, mul_left_comm, mul_comm] using hmain]
  have hmiddle :
      qs.eval (Gate.PhaseProdUsing
          ((2 * Real.pi * (N : ℝ)) / (ASize ws.zExt.active : ℝ))
          work.active scratch.active ws)
          (qs.eval (Gate.QFT ws.zExt) (qs.ket b)) =
        qs.eval (Gate.QFT ws.zExt) (qs.ket target) := by
    rw [QFTSemantics.eval_QFT_ket, QFTSemantics.eval_QFT_ket]
    rw [qs.eval_smul, eval_sum_univ_qs]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    rw [qs.eval_smul]
    let yM : Fin M := ⟨y.1, by simpa [M, hzwidth] using y.isLt⟩
    have hphase' := hphase yM
    simp only [yM] at hphase'
    rw [show RegEncoding.writeNat ws.zExt.active y.1 b =
      RegEncoding.writeNat scratch.active y.1 b by rw [hzactive]]
    rw [hphase']
    simp only [smul_smul]
    have hmod := qftPhase_mod_left_shor M
      (N * RegEncoding.toNat work.active b) y.1 hM
    have htargetRead : ExtReg.toNat ws.zExt target = a := by
      change RegEncoding.toNat ws.zExt.active target = a
      rw [hzactive]
      exact RegEncoding.toNat_writeNat_of_lt scratch.active a b ha
    have htargetWrite :
        RegEncoding.writeNat ws.zExt.active y.1 target =
          RegEncoding.writeNat scratch.active y.1 b := by
      rw [hzactive]
      exact RegEncoding.writeNat_overwrite scratch.active y.1 a b
    have hbaseRead : ExtReg.toNat ws.zExt b = 0 := by
      simpa [ExtReg.toNat, hzactive] using hscratchZero
    rw [hbaseRead, htargetRead, htargetWrite]
    change (qftPhase M 0 y.1 *
      qftPhase M (N * RegEncoding.toNat work.active b) y.1) •
        qs.ket (RegEncoding.writeNat scratch.active y.1 b) =
      qftPhase M a y.1 •
        qs.ket (RegEncoding.writeNat scratch.active y.1 b)
    rw [hmod]
    simp [a, qftPhase, ωPow]
  simp only [fastConstMulInto, qs.eval_seq]
  rw [hmiddle]
  simpa [target, a, M] using
    qs.eval_adj_apply (Gate.QFT ws.zExt) (qs.ket target)

theorem eval_cmp_lt_nw_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (N : ℕ)
    (data work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace : CmpLtNWWorkspace N data work scratch flag)
    (b : qs.Basis)
    (hdataFresh : data.FreshFor 1 b)
    (hworkFresh : work.FreshFor 1 b)
    (hscratchZero : RegEncoding.toNat scratch.active b = 0)
    (hscratchFresh : scratch.FreshFor 1 b) :
    qs.eval (cmpLtNW N data work scratch flag hworkspace) (qs.ket b) =
      qs.ket
        (RegEncoding.writeNat (qubitReg flag)
          (if RegEncoding.bit flag b then
            if RegEncoding.toNat data.active b * ASize work.active <
                N * RegEncoding.toNat work.active b then 0 else 1
          else
            if RegEncoding.toNat data.active b * ASize work.active <
                N * RegEncoding.toNat work.active b then 1 else 0)
          b) := by
  classical
  let dataValue := RegEncoding.toNat data.active b
  let workValue := RegEncoding.toNat work.active b
  let d := regSize data.active
  let w := regSize work.active
  let q := N * workValue
  let difference : ℤ := -(q : ℤ) + (2 : ℤ) ^ w * (dataValue : ℤ)
  let comparison : Prop := dataValue * ASize work.active < q
  let out : ℕ :=
    if RegEncoding.bit flag b then
      if comparison then 0 else 1
    else
      if comparison then 1 else 0
  let bOut : qs.Basis := RegEncoding.writeNat (qubitReg flag) out b

  have hscratchWidth :
      scratch.width =
        2 + max (d + w) (Nat.log2 (N + 1) + 1 + w) := by
    simpa [ExtReg.width, cmpLtNWWidth, d, w] using hworkspace.scratch_width
  have hscratchPos : 0 < scratch.width := by
    rw [hscratchWidth]
    omega
  have hscratchRegPos : 0 < regSize scratch.active := by
    simpa [ExtReg.width] using hscratchPos
  have hdataLt : dataValue < 2 ^ d := by
    simpa [dataValue, d, ASize] using
      (RegEncoding.toNat_lt_ASize (r := data.active) (b := b))
  have hworkLt : workValue < 2 ^ w := by
    simpa [workValue, w, ASize] using
      (RegEncoding.toNat_lt_ASize (r := work.active) (b := b))
  have hbounds := cmpLtNW_value_bounds N d w dataValue workValue hdataLt hworkLt
  dsimp only at hbounds
  rw [← hscratchWidth] at hbounds
  have hqSigned : q < 2 ^ (scratch.width - 1) := by
    simpa [q] using hbounds.1
  have hdiffFit : FitsSignedWidth scratch.width difference := by
    simpa [difference, q, sub_eq_add_neg, add_comm] using hbounds.2
  have hnegFit : FitsSignedWidth scratch.width (-(q : ℤ)) := by
    have hfit := cmpLtNW_fitsSignedWidth_neg_nat_of_lt_pow hqSigned
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hscratchPos))] using hfit
  have hqFull : q < ASize scratch.active := by
    have hp : 2 ^ (scratch.width - 1) ≤ 2 ^ scratch.width :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    exact lt_of_lt_of_le hqSigned (by simpa [ASize, ExtReg.width] using hp)

  let mul := fastConstMulInto N work scratch hworkspace.mulWorkspace
  let diff := cmpLtNWDifference data work scratch hworkspace.data_can_grow
  let sign := cmpLtNWSignQubit scratch hscratchRegPos
  let bMul : qs.Basis := RegEncoding.writeNat scratch.active q b
  let bNeg : qs.Basis := negateBasis scratch bMul
  let bDiff : qs.Basis :=
    addScaledBasis scratch (data.grow 1) false w bNeg

  have hclean := cmpLtNW_mulWorkspace_clean
    N data work scratch flag hworkspace b hworkFresh hscratchFresh
  have hmul : qs.eval mul (qs.ket b) = qs.ket bMul := by
    have h := eval_fastConstMulInto_ket
      N work scratch hworkspace.mulWorkspace b hclean hscratchZero
    simpa [mul, bMul, q, workValue, Nat.mod_eq_of_lt hqFull] using h

  have hdataScratchActive : Disjoint data.active scratch.active :=
    cmpLtNW_activeDisjoint_of_ownedDisjoint hworkspace.data_scratch_disjoint
  have hdataFreshMul : data.FreshFor 1 bMul := by
    dsimp [bMul]
    exact cmpLtNW_freshFor_write_active_disjoint data scratch 1 q b
      hworkspace.data_scratch_disjoint hdataFresh
  have hdataMul : RegEncoding.toNat data.active bMul = dataValue := by
    dsimp [bMul, dataValue]
    exact RegEncoding.toNat_left_write_right
      data.active scratch.active hdataScratchActive b q
  have hscratchMul : extToInt scratch bMul = (q : ℤ) := by
    dsimp [bMul]
    exact cmpLtNW_extToInt_writeNat_of_lt_signed
      scratch q b hqSigned hscratchPos
  have hdiffFacts := eval_cmpLtNWDifference_ket
    data work scratch hworkspace.data_can_grow bMul hdataFreshMul
    q dataValue hscratchMul hdataMul hnegFit hdiffFit
    hworkspace.data_scratch_disjoint
  have hdiff : qs.eval diff (qs.ket bMul) = qs.ket bDiff := by
    simpa [diff, bNeg, bDiff, w] using hdiffFacts.1
  have hdiffInt : extToInt scratch bDiff = difference := by
    simpa [bNeg, bDiff, difference, w] using hdiffFacts.2

  have hscratchFlagDisjoint : Disjoint scratch.active (qubitReg flag) :=
    cmpLtNW_active_qubit_disjoint_of_not_owned
      scratch flag hworkspace.flag_not_scratch
  have hdataFlagDisjoint : Disjoint data.active (qubitReg flag) :=
    cmpLtNW_active_qubit_disjoint_of_not_owned
      data flag hworkspace.flag_not_data
  have hdataGrowFlagDisjoint :
      Disjoint (data.grow 1).active (qubitReg flag) :=
    cmpLtNW_grow_active_qubit_disjoint_of_not_owned
      data 1 flag hworkspace.flag_not_data
  have hdataGrowScratch : (data.grow 1).ActiveDisjoint scratch :=
    cmpLtNW_activeDisjoint_of_ownedDisjoint
      (cmpLtNW_ownedDisjoint_grow_left data scratch 1
        hworkspace.data_scratch_disjoint)
  have hscratchDataGrow : scratch.ActiveDisjoint (data.grow 1) :=
    Disjoint.symm hdataGrowScratch
  have hflagNotScratchActive : flag ∉ scratch.active.qubits := by
    intro hmem
    exact hworkspace.flag_not_scratch (List.mem_append_left _ hmem)
  have hflagMul : RegEncoding.bit flag bMul = RegEncoding.bit flag b := by
    dsimp [bMul]
    exact RegEncoding.bit_writeNat_out scratch.active q b flag hflagNotScratchActive
  have hflagNeg : RegEncoding.bit flag bNeg = RegEncoding.bit flag b := by
    dsimp [bNeg]
    unfold negateBasis
    rw [RegEncoding.bit_writeNat_out]
    exact hflagMul
    exact hflagNotScratchActive
  have hflagDiff : RegEncoding.bit flag bDiff = RegEncoding.bit flag b := by
    dsimp [bDiff]
    rw [addScaledBasis_eq scratch (data.grow 1) false w bNeg hscratchDataGrow]
    rw [RegEncoding.bit_writeNat_out]
    exact hflagNeg
    exact hflagNotScratchActive

  have hdiffNegIff :
      difference < 0 ↔ comparison := by
    change
      (-(q : ℤ) + (2 : ℤ) ^ w * (dataValue : ℤ) < 0) ↔
        dataValue * 2 ^ w < q
    constructor
    · intro h
      have hcast :
          ((dataValue * 2 ^ w : ℕ) : ℤ) < (q : ℤ) := by
        push_cast
        nlinarith
      exact_mod_cast hcast
    · intro h
      have hcast :
          ((dataValue * 2 ^ w : ℕ) : ℤ) < (q : ℤ) := by
        exact_mod_cast h
      push_cast at hcast
      nlinarith
  have hsignBit :
      RegEncoding.bit sign bDiff = decide comparison := by
    dsimp [sign]
    rw [cmpLtNWSignQubit_bit, hdiffInt]
    by_cases hcmp : comparison
    · simp [hcmp, hdiffNegIff.mpr hcmp]
    · have hnot : ¬ difference < 0 := fun h => hcmp (hdiffNegIff.mp h)
      simp [hcmp, hnot]
  have hsignMem : sign ∈ scratch.active.qubits := by
    dsimp [sign, cmpLtNWSignQubit]
    exact List.get_mem scratch.active.qubits _
  have hsignNeFlag : sign ≠ flag := by
    intro heq
    apply hworkspace.flag_not_scratch
    rw [← heq]
    exact List.mem_append_left _ hsignMem
  have hcnotBasis :
      cnotBasis sign flag bDiff =
        RegEncoding.writeNat (qubitReg flag) out bDiff := by
    by_cases hcmp : comparison
    · simp [cnotBasis, hsignNeFlag, hsignBit, hcmp, hflagDiff, out]
    · rw [show cnotBasis sign flag bDiff = bDiff by
          simp [cnotBasis, hsignNeFlag, hsignBit, hcmp]]
      simpa [out, hcmp, hflagDiff] using
        (cmpLtNW_writeNat_current_qubit flag bDiff).symm
  have hleftPrefix :
      qs.eval (Gate.CNOT sign flag)
          (qs.eval diff (qs.eval mul (qs.ket b))) =
        qs.ket (RegEncoding.writeNat (qubitReg flag) out bDiff) := by
    rw [hmul, hdiff, ClassicalReversibleSemantics.eval_CNOT_ket]
    exact congrArg qs.ket hcnotBasis

  have hworkFlagDisjoint : Disjoint work.active (qubitReg flag) :=
    cmpLtNW_active_qubit_disjoint_of_not_owned work flag hworkspace.flag_not_work
  have hworkOut : RegEncoding.toNat work.active bOut = workValue := by
    dsimp [bOut, workValue]
    exact RegEncoding.toNat_left_write_right
      work.active (qubitReg flag) hworkFlagDisjoint b out
  have hscratchZeroOut : RegEncoding.toNat scratch.active bOut = 0 := by
    dsimp [bOut]
    rw [RegEncoding.toNat_left_write_right
      scratch.active (qubitReg flag) hscratchFlagDisjoint b out]
    exact hscratchZero
  have hworkFreshOut : work.FreshFor 1 bOut := by
    dsimp [bOut]
    exact cmpLtNW_freshFor_write_qubit_of_not_owned
      work 1 flag out b hworkspace.flag_not_work hworkFresh
  have hscratchFreshOut : scratch.FreshFor 1 bOut := by
    dsimp [bOut]
    exact cmpLtNW_freshFor_write_qubit_of_not_owned
      scratch 1 flag out b hworkspace.flag_not_scratch hscratchFresh
  have hcleanOut := cmpLtNW_mulWorkspace_clean
    N data work scratch flag hworkspace bOut hworkFreshOut hscratchFreshOut
  let bMulOut : qs.Basis := RegEncoding.writeNat scratch.active q bOut
  let bNegOut : qs.Basis := negateBasis scratch bMulOut
  let bDiffOut : qs.Basis :=
    addScaledBasis scratch (data.grow 1) false w bNegOut
  have hmulOut : qs.eval mul (qs.ket bOut) = qs.ket bMulOut := by
    have h := eval_fastConstMulInto_ket
      N work scratch hworkspace.mulWorkspace bOut hcleanOut hscratchZeroOut
    simpa [mul, bMulOut, q, hworkOut, Nat.mod_eq_of_lt hqFull] using h
  have hbMulOut :
      bMulOut = RegEncoding.writeNat (qubitReg flag) out bMul := by
    dsimp [bMulOut, bOut, bMul]
    exact RegEncoding.writeNat_comm_of_disjoint
      scratch.active (qubitReg flag) hscratchFlagDisjoint q out b
  have hdataFreshOut : data.FreshFor 1 bOut := by
    dsimp [bOut]
    exact cmpLtNW_freshFor_write_qubit_of_not_owned
      data 1 flag out b hworkspace.flag_not_data hdataFresh
  have hdataFreshMulOut : data.FreshFor 1 bMulOut := by
    dsimp [bMulOut]
    exact cmpLtNW_freshFor_write_active_disjoint data scratch 1 q bOut
      hworkspace.data_scratch_disjoint hdataFreshOut
  have hscratchMulOut : extToInt scratch bMulOut = (q : ℤ) := by
    dsimp [bMulOut]
    exact cmpLtNW_extToInt_writeNat_of_lt_signed
      scratch q bOut hqSigned hscratchPos
  have hdataMulOut : RegEncoding.toNat data.active bMulOut = dataValue := by
    dsimp [bMulOut, bOut, dataValue]
    rw [RegEncoding.toNat_left_write_right
      data.active scratch.active hdataScratchActive]
    exact RegEncoding.toNat_left_write_right
      data.active (qubitReg flag) hdataFlagDisjoint b out
  have hdiffOutFacts := eval_cmpLtNWDifference_ket
    data work scratch hworkspace.data_can_grow bMulOut hdataFreshMulOut
    q dataValue hscratchMulOut hdataMulOut hnegFit hdiffFit
    hworkspace.data_scratch_disjoint
  have hdiffOut : qs.eval diff (qs.ket bMulOut) = qs.ket bDiffOut := by
    simpa [diff, bNegOut, bDiffOut, w] using hdiffOutFacts.1
  have hflagNotDataGrow : flag ∉ (data.grow 1).ownedQubits := by
    simpa [Gate.ExtReg.ownedQubits_grow] using hworkspace.flag_not_data
  have hbNegOut :
      bNegOut = RegEncoding.writeNat (qubitReg flag) out bNeg := by
    dsimp [bNegOut]
    rw [hbMulOut]
    exact cmpLtNW_negateBasis_write_qubit
      scratch flag out bMul hworkspace.flag_not_scratch
  have hbDiffOut :
      bDiffOut = RegEncoding.writeNat (qubitReg flag) out bDiff := by
    dsimp [bDiffOut]
    rw [hbNegOut]
    exact cmpLtNW_addScaledBasis_write_qubit
      scratch (data.grow 1) false w flag out bNeg
      hscratchDataGrow hworkspace.flag_not_scratch hflagNotDataGrow
  have hrightPrefix :
      qs.eval diff (qs.eval mul (qs.ket bOut)) =
        qs.ket (RegEncoding.writeNat (qubitReg flag) out bDiff) := by
    rw [hmulOut, hdiffOut, hbDiffOut]
  have hprefix :
      qs.eval (Gate.CNOT sign flag)
          (qs.eval diff (qs.eval mul (qs.ket b))) =
        qs.eval diff (qs.eval mul (qs.ket bOut)) := by
    rw [hleftPrefix, hrightPrefix]

  have hfinal := cmpLtNW_eval_compute_cnot_uncompute
    qs mul diff sign flag b bOut hprefix
  simpa [cmpLtNW, mul, diff, sign, bOut, out, comparison,
    dataValue, workValue, q] using hfinal

end Shor
