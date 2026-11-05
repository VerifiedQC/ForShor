import ForShor.ShorVerification.Implementation.QubitCount.Proofs.QFT
import ForShor.ShorVerification.Implementation.Compiler.Statement

/-!
# Qubit count: the walk of `Policy.lowerGate`

A walk on high-level gates in which the QFT, the two phase products and the
two constant-arithmetic gates are opaque, each costing what the earlier files
showed its lowering costs, and a theorem that the walk of `Policy.lowerGate P G`
agrees with it in both directions, for every gate `G` whose blocks start from
suitable live sets.

Two blocks need care.

* A QFT walked forwards may start with the first qubit of its x-side pool
  already live, and then ends without it.
* `CmpGeConst` and `CSubConst` use the first reserve qubit of their scratch
  register without activating it, so it stays live after them. They are only
  walked forwards.
-/

namespace Shor
namespace QubitCount

open Gate

/-! ## The walk -/

/-- A high-level gate that `Policy.lowerGate` sends to one low-level gate. -/
def sPrim : Gate → Option LowGate
  | .H q => some (.H q)
  | .X q => some (.X q)
  | .CNOT c t => some (.CNOT c t)
  | .Toffoli a b t => some (.Toffoli a b t)
  | .ShiftL r n => some (.ShiftL r n)
  | .ShiftR r n => some (.ShiftR r n)
  | .Negate r => some (.Negate r)
  | .AddScaled d s b n => some (.AddScaled d s b n)
  | .zeroExtend r n => some (.zeroExtend r n)
  | .signExtend r n => some (.signExtend r n)
  | .zeroDealloc r n => some (.zeroDealloc r n)
  | .signDealloc r n => some (.signDealloc r n)
  | .RadixReverse r m => some (.RadixReverse r m)
  | _ => none

variable (P : ShorLoweringPolicy)

/-- Live set after a high-level gate, its blocks opaque. -/
def sAfter : Gate → Bool → Finset ℕ → Finset ℕ
  | .id, _, L => L
  | .seq U V, true, L => sAfter V true (sAfter U true L)
  | .seq U V, false, L => sAfter U false (sAfter V false L)
  | .adj U, d, L => sAfter U (!d) L
  | .QFT r, _, L => if 2 ≤ r.width then L \ firstOf (Policy.qftXWork P r) else L
  | .SignedPhaseProd _ _ _, _, L => L
  | .CSignedPhaseProd _ _ _ _, _, L => L
  | .CmpGeConst _ _ s _, _, L => L ∪ allocBits s 1
  | .CSubConst _ _ s _, _, L => L ∪ allocBits s 1
  | .idealCtrlModMul _ _ _ _, _, L => L
  | g, d, L => match sPrim g with
    | some u => after u d L
    | none => L

/-- Peak of a high-level gate, its blocks opaque, scratch included, when a
phase product on operands of widths `wx`, `wz` and spare capacities `cx`, `cz`
peaks `pc wx cx wz cz` above its start. The constant arithmetic peaks at the negation of its scratch register,
or, for the comparison, at the addition with the data register grown by one. -/
def sPeak (pc : ℕ → ℕ → ℕ → ℕ → ℕ) : Gate → Bool → Finset ℕ → ℕ
  | .id, _, L => L.card
  | .seq U V, true, L => max (sPeak pc U true L) (sPeak pc V true (sAfter P U true L))
  | .seq U V, false, L => max (sPeak pc V false L) (sPeak pc U false (sAfter P V false L))
  | .adj U, d, L => sPeak pc U (!d) L
  | .QFT r, _, L =>
      if 2 ≤ r.width then (L \ firstOf (Policy.qftXWork P r)).card + Rec.qftPeak P r.width
      else L.card
  | .SignedPhaseProd _ x z, _, L => L.card + pc x.width x.capacity z.width z.capacity
  | .CSignedPhaseProd _ _ x z, _, L => L.card + pc x.width x.capacity z.width z.capacity
  | .CmpGeConst _ _ s _, _, L => (L ∪ allocBits s 1).card + max 2 (s.width + 1)
  | .CSubConst _ _ s _, _, L => (L ∪ allocBits s 1).card + (s.width + 1)
  | .idealCtrlModMul _ _ _ _, _, L => L.card
  | g, d, L => match sPrim g with
    | some u => peak scratch u d L
    | none => L.card

/-- The operands of a phase product are live and their reserves are not. -/
def ppLive (x z : ExtReg) (L : Finset ℕ) : Prop :=
  regQubitSet x.active ⊆ L ∧ regQubitSet z.active ⊆ L ∧
    _root_.Disjoint L (regQubitSet x.reserve ∪ regQubitSet z.reserve)

/-- Every block of a high-level gate starts from a live set it can be counted
from. -/
def sGood : Gate → Bool → Finset ℕ → Prop
  | .id, _, _ => True
  | .seq U V, true, L => sGood U true L ∧ sGood V true (sAfter P U true L)
  | .seq U V, false, L => sGood V false L ∧ sGood U false (sAfter P V false L)
  | .adj U, d, L => sGood U (!d) L
  | .QFT r, true, L =>
      regQubitSet r.active ⊆ L ∧ _root_.Disjoint L (regQubitSet (Policy.qftZWork P r)) ∧
        L ∩ regQubitSet (Policy.qftXWork P r) ⊆ firstOf (Policy.qftXWork P r)
  | .QFT r, false, L => regQubitSet r.active ⊆ L ∧ _root_.Disjoint L (regQubitSet r.reserve)
  | .SignedPhaseProd _ x z, _, L => ppLive x z L
  | .CSignedPhaseProd c _ x z, _, L => c ∈ L ∧ ppLive x z L
  | .CmpGeConst _ data s flag, true, L =>
      regQubitSet data.active ⊆ L ∧ regQubitSet s.active ⊆ L ∧ flag ∈ L ∧
        _root_.Disjoint (allocBits data 1) (L ∪ allocBits s 1)
  | .CSubConst _ data s flag, true, L =>
      regQubitSet data.active ⊆ L ∧ regQubitSet s.active ⊆ L ∧ flag ∈ L
  | .CmpGeConst _ _ _ _, false, _ => False
  | .CSubConst _ _ _ _, false, _ => False
  | .idealCtrlModMul _ _ _ _, _, _ => False
  | g, d, L => match sPrim g with
    | some u => WellFormed u d L
    | none => False

/-! ## Blocks -/

/-- A balanced, well-formed circuit walks backwards as it walks forwards. -/
lemma backward_of_forward {g : LowGate} {L : Finset ℕ} (hw : WellFormed g true L)
    (ha : after g true L = L) :
    after g false L = L ∧ peak scratch g false L = peak scratch g true L := by
  obtain ⟨_, h2, h3⟩ := reverse scratch g true L hw
  rw [ha] at h2 h3
  exact ⟨h2, h3⟩

lemma qft_block (hP : P.Admissible) (r : ExtReg) (hws : Policy.QFTReserveOK P r) (d : Bool)
    (L : Finset ℕ) (h : sGood P (.QFT r) d L) :
    after (Policy.lowerQFT P r hws) d L = sAfter P (.QFT r) d L ∧
    peak scratch (Policy.lowerQFT P r hws) d L = sPeak P (Rec.ppPeak P) (.QFT r) d L := by
  have hpools := qftPools_subset P r
  cases d
  · obtain ⟨hr, hres⟩ := h
    obtain ⟨a, p, w⟩ := qftPeak_claim P hP r hws L hr hres
    obtain ⟨a', p'⟩ := backward_of_forward w a
    have hfirst : L \ firstOf (Policy.qftXWork P r) = L := Finset.sdiff_eq_self_of_disjoint
      (Finset.disjoint_of_subset_right ((firstOf_subset _).trans hpools.1) hres)
    simp only [sAfter, sPeak, hfirst]
    refine ⟨by rw [a']; split <;> rfl, ?_⟩
    rw [p', show peak scratch (Policy.lowerQFT P r hws) true L = _ from p]
    split
    · rfl
    · next h2 => rw [qftPeak_lt_two P (by omega)]; rfl
  · obtain ⟨hr, hz, hx⟩ := h
    obtain ⟨a, p, _⟩ := qftPlan_walk P hP _ _ r.active hws.explicitWorkspace L hr hz hx
    exact ⟨a, p⟩

lemma signed_block (hP : P.Admissible) (phi : Angle) (x z : ExtReg) (hws : Policy.WorkspaceOK P x z)
    (d : Bool) (L : Finset ℕ) (h : ppLive x z L) :
    after (Policy.lowerSignedPhaseProd P phi x z) d L = L ∧
    peak scratch (Policy.lowerSignedPhaseProd P phi x z) d L
      = L.card + Rec.peakReserve P x.width z.width := by
  obtain ⟨a, p, w⟩ := signedPhaseProductPeak P hP phi x z hws L h.1 h.2.1 h.2.2
  cases d
  · obtain ⟨a', p'⟩ := backward_of_forward w a
    exact ⟨a', p'.trans p⟩
  · exact ⟨a, p⟩

lemma csigned_block (hP : P.Admissible) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (hws : Policy.CWorkspaceOK P ctrl x z) (d : Bool) (L : Finset ℕ) (hc : ctrl ∈ L)
    (h : ppLive x z L) :
    after (Policy.lowerCSignedPhaseProd P ctrl phi x z) d L = L ∧
    peak scratch (Policy.lowerCSignedPhaseProd P ctrl phi x z) d L
      = L.card + Rec.peakReserve P x.width z.width := by
  obtain ⟨a, p, w⟩ := cSignedPhaseProductPeak P hP ctrl phi x z hws L hc h.1 h.2.1 h.2.2
  cases d
  · obtain ⟨a', p'⟩ := backward_of_forward w a
    exact ⟨a', p'.trans p⟩
  · exact ⟨a, p⟩

/-! ## The constant arithmetic -/

lemma allocBits_one_eq (s : ExtReg) (h : s.CanGrow 1) :
    allocBits s 1 = {constArithmeticUnitQubit s h} := by
  have hlen : (s.newBits 1).qubits.length = 1 := by
    have := card_allocBits s h
    rw [allocBits, card_regQubitSet] at this
    simpa [regSize, Reg.width] using this
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  simp only [allocBits, regQubitSet, constArithmeticUnitQubit, Reg.get]
  simp [ha]

lemma touchIn_copyBitPowers {L : Finset ℕ} (dst : ExtReg) {ctrl : ℕ} (hc : ctrl ∈ L)
    (hd : regQubitSet dst.active ⊆ L) :
    ∀ bits : List ℕ, TouchIn L (lowerCopyBitPowers dst ctrl bits) := by
  intro bits
  induction bits with
  | nil => simp [lowerCopyBitPowers, TouchIn]
  | cons i bits ih =>
      unfold lowerCopyBitPowers
      split
      · refine ⟨?_, ih⟩
        simp only [TouchIn, LowGate.usedQubits, Finset.insert_subset_iff,
          Finset.singleton_subset_iff]
        refine ⟨hc, hd ?_⟩
        rw [mem_regQubitSet]
        exact List.get_mem _ _
      · exact ih

lemma tmax_copyBitPowers (dst : ExtReg) (ctrl : ℕ) :
    ∀ bits : List ℕ, tmax scratch (lowerCopyBitPowers dst ctrl bits) = 0 := by
  intro bits
  induction bits with
  | nil => simp [lowerCopyBitPowers]
  | cons i bits ih =>
      unfold lowerCopyBitPowers
      split
      · simp [ih]
      · exact ih

lemma touchIn_mono {L L' : Finset ℕ} (h : L ⊆ L') : ∀ g : LowGate, TouchIn L g → TouchIn L' g := by
  intro g
  induction g with
  | id => intro _; trivial
  | seq U V ihU ihV => intro hg; exact ⟨ihU hg.1, ihV hg.2⟩
  | adj U ih => intro hg; exact ih hg
  | H _ | X _ | Phase _ _ | CNOT _ _ | Toffoli _ _ _ | ShiftL _ _ | ShiftR _ _ | Negate _
  | AddScaled _ _ _ _ | RadixReverse _ _ =>
      intro hg; exact (show _ ⊆ L from hg).trans h
  | zeroExtend _ _ | signExtend _ _ | zeroDealloc _ _ | signDealloc _ _ => intro hg; exact hg.elim

/-- Walks compose along a sequence. -/
lemma chain {U V : LowGate} {L M K : Finset ℕ} {a b : ℕ}
    (hU : after U true L = M ∧ peak scratch U true L = a)
    (hV : after V true M = K ∧ peak scratch V true M = b) :
    after (U ;; V) true L = K ∧ peak scratch (U ;; V) true L = max a b := by
  simp only [after, peak]
  rw [hU.1, hU.2, hV.1, hV.2]
  exact ⟨rfl, rfl⟩

/-- An adjoint walks its body backwards. -/
lemma adjoint {U : LowGate} {L M : Finset ℕ} {a : ℕ}
    (h : after U false L = M ∧ peak scratch U false L = a) :
    after (†U) true L = M ∧ peak scratch (†U) true L = a := h

/-- A circuit acting on live qubits. -/
lemma touch_fact {g : LowGate} {L : Finset ℕ} (h : TouchIn L g) (d : Bool) :
    after g d L = L ∧ peak scratch g d L = L.card + tmax scratch g :=
  ⟨(touch_walk_anc scratch L g h d).1, (touch_walk_anc scratch L g h d).2.1⟩

lemma cmpGe_arith (c w : ℕ) :
    max (max c (c + max 0 (w + 1)))
      (max (max (c + 1) (max (c + 1 + 1) (c + 1)))
        (max (c + max 0 0)
          (max (max (c + 1) (max (c + 1 + 1) (c + 1))) (c + max 0 (max 0 (w + 1)))))) =
    c + max 2 (w + 1) := by
  omega

lemma cSub_arith (c w : ℕ) :
    max (max c (c + max 0 (w + 1))) (max (c + 1) (c + max 0 (max 0 (w + 1)))) = c + (w + 1) := by
  omega

lemma cmpGe_block (N : ℕ) (data s : ExtReg) (flag : ℕ) (hws : ConstArithmeticWorkspace N data s flag)
    (L : Finset ℕ) (h : sGood P (.CmpGeConst N data s flag) true L) :
    after (lowerCmpGeConst N data s flag hws) true L = L ∪ allocBits s 1 ∧
    peak scratch (lowerCmpGeConst N data s flag hws) true L
      = (L ∪ allocBits s 1).card + max 2 (s.width + 1) := by
  obtain ⟨hd, hs, hf, hfresh⟩ := h
  set q := constArithmeticUnitQubit s hws.scratch_can_grow with hq
  have hbits : allocBits s 1 = {q} := allocBits_one_eq s hws.scratch_can_grow
  set L1 := L ∪ allocBits s 1 with hL1
  have hqL1 : q ∈ L1 := by rw [hL1, hbits]; simp
  have hsL1 : regQubitSet s.active ⊆ L1 := hs.trans Finset.subset_union_left
  have hdL1 : regQubitSet data.active ⊆ L1 := hd.trans Finset.subset_union_left
  have hfL1 : flag ∈ L1 := Finset.mem_union_left _ hf
  -- the preparation
  have hrest : TouchIn L1 (lowerCopyConstFromUnit N s q ;; LowGate.Negate s) :=
    ⟨touchIn_copyBitPowers s hqL1 hsL1 _, hsL1⟩
  have hprep : TouchIn L1 (lowerPrepareNegConst N s hws.scratch_can_grow) :=
    ⟨by show {q} ⊆ L1; exact Finset.singleton_subset_iff.mpr hqL1, hrest⟩
  have hXq : after (LowGate.X q) true L = L1 ∧ peak scratch (LowGate.X q) true L = L1.card := by
    have : L ∪ LowGate.usedQubits (LowGate.X q) = L1 := by
      simp [LowGate.usedQubits, hL1, hbits]
    refine ⟨?_, ?_⟩ <;> simp only [after, peak, this, scratch_X, add_zero]
  have fprep := chain hXq (touch_fact hrest true)
  -- the difference
  set b := allocBits data 1 with hb
  have hcb : b.card = 1 := card_allocBits data hws.data_can_grow
  have hdiff_add : LowGate.usedQubits (LowGate.AddScaled s (data.grow 1) false 0) ⊆ L1 ∪ b := by
    show regQubitSet s.active ∪ regQubitSet (data.grow 1).active ⊆ L1 ∪ b
    rw [grow_active]
    exact Finset.union_subset (hsL1.trans Finset.subset_union_left)
      (Finset.union_subset_union hdL1 le_rfl)
  have hfresh' : _root_.Disjoint b L1 := hfresh
  have hc : (L1 ∪ b).card = L1.card + 1 := by
    rw [Finset.card_union_of_disjoint hfresh'.symm, hcb]
  have f1 : after (LowGate.zeroExtend data 1) true L1 = L1 ∪ b ∧
      peak scratch (LowGate.zeroExtend data 1) true L1 = L1.card + 1 := by
    simp only [after, peak, move_true]
    rw [← hb, hc]; exact ⟨rfl, max_eq_right (Nat.le_succ _)⟩
  have f2 : after (LowGate.AddScaled s (data.grow 1) false 0) true (L1 ∪ b) = L1 ∪ b ∧
      peak scratch (LowGate.AddScaled s (data.grow 1) false 0) true (L1 ∪ b) = L1.card + 1 + 1 := by
    rw [← hc]
    exact touch_fact (g := LowGate.AddScaled s (data.grow 1) false 0) (L := L1 ∪ b) hdiff_add true
  have f3 : after (LowGate.zeroDealloc data 1) true (L1 ∪ b) = L1 ∧
      peak scratch (LowGate.zeroDealloc data 1) true (L1 ∪ b) = L1.card + 1 := by
    simp only [after, peak, Bool.not_true, move_false]
    rw [← hb, Finset.union_sdiff_cancel_right hfresh'.symm, hc]
    exact ⟨rfl, max_eq_left (Nat.le_succ _)⟩
  have fdiff := chain f1 (chain f2 f3)
  have hdw : WellFormed (LowGate.zeroExtend data 1 ;; LowGate.AddScaled s (data.grow 1) false 0 ;;
      LowGate.zeroDealloc data 1) true L1 := by
    simp only [WellFormed, after, move_true, moveOK_true, moveOK_false, Bool.not_true]
    rw [← hb, Finset.union_eq_left.mpr hdiff_add]
    exact ⟨hfresh', hdiff_add, Finset.subset_union_right⟩
  obtain ⟨da', dp'⟩ := backward_of_forward hdw fdiff.1
  have fdiff' := adjoint ⟨da', dp'.trans fdiff.2⟩
  have fprep' := adjoint (touch_fact hprep false)
  have hsign : ∀ hlt, s.active.get ⟨s.width - 1, hlt⟩ ∈ L1 := fun hlt => by
    apply hsL1; rw [mem_regQubitSet]; exact List.get_mem _ _
  have fflag : ∀ hlt, after (LowGate.X flag ;; LowGate.CNOT (s.active.get ⟨s.width - 1, hlt⟩) flag)
      true L1 = L1 ∧ peak scratch
        (LowGate.X flag ;; LowGate.CNOT (s.active.get ⟨s.width - 1, hlt⟩) flag) true L1
        = L1.card + tmax scratch
          (LowGate.X flag ;; LowGate.CNOT (s.active.get ⟨s.width - 1, hlt⟩) flag) :=
    fun hlt => by
      have := touch_fact (L := L1)
        (g := LowGate.X flag ;; LowGate.CNOT (s.active.get ⟨s.width - 1, hlt⟩) flag)
        ⟨by simp [TouchIn, LowGate.usedQubits, hfL1],
          by simp [TouchIn, LowGate.usedQubits, Finset.insert_subset_iff, hfL1, hsign]⟩ true
      exact this
  have hall := chain fprep (chain fdiff (chain (fflag (Nat.sub_lt hws.scratch_positive Nat.one_pos))
    (chain fdiff' fprep')))
  refine ⟨hall.1, ?_⟩
  rw [show peak scratch (lowerCmpGeConst N data s flag hws) true L = _ from hall.2]
  simp only [lowerPrepareNegConst, lowerCopyConstFromUnit, tmax_seq, tmax_X, tmax_CNOT,
    tmax_Negate, scratch_X, scratch_CNOT, scratch_Negate, tmax_copyBitPowers]
  exact cmpGe_arith _ _

lemma cSub_block (N : ℕ) (data s : ExtReg) (flag : ℕ) (hws : ConstArithmeticWorkspace N data s flag)
    (L : Finset ℕ) (h : sGood P (.CSubConst N data s flag) true L) :
    after (lowerCSubConst N data s flag hws) true L = L ∪ allocBits s 1 ∧
    peak scratch (lowerCSubConst N data s flag hws) true L
      = (L ∪ allocBits s 1).card + (s.width + 1) := by
  obtain ⟨hd, hs, hf⟩ := h
  set q := constArithmeticUnitQubit s hws.scratch_can_grow with hq
  have hbits : allocBits s 1 = {q} := allocBits_one_eq s hws.scratch_can_grow
  set L1 := L ∪ allocBits s 1 with hL1
  have hqL1 : q ∈ L1 := by rw [hL1, hbits]; simp
  have hsL1 : regQubitSet s.active ⊆ L1 := hs.trans Finset.subset_union_left
  have hdL1 : regQubitSet data.active ⊆ L1 := hd.trans Finset.subset_union_left
  have hfL1 : flag ∈ L1 := Finset.mem_union_left _ hf
  have hrest : TouchIn L1 (lowerCopyConstFromUnit N s q ;; LowGate.Negate s) :=
    ⟨touchIn_copyBitPowers s hqL1 hsL1 _, hsL1⟩
  have hprep : TouchIn L1 (LowGate.CNOT flag q ;; lowerCopyConstFromUnit N s q ;; LowGate.Negate s) :=
    ⟨by simp [TouchIn, LowGate.usedQubits, Finset.insert_subset_iff, hqL1, hfL1], hrest⟩
  have hadd : TouchIn L1 (LowGate.AddScaled data s false 0) :=
    Finset.union_subset hdL1 hsL1
  have hC : after (LowGate.CNOT flag q) true L = L1 ∧
      peak scratch (LowGate.CNOT flag q) true L = L1.card := by
    have : L ∪ LowGate.usedQubits (LowGate.CNOT flag q) = L1 := by
      show L ∪ insert flag {q} = L1
      rw [Finset.union_insert, Finset.insert_eq_of_mem (Finset.mem_union_left _ hf), hL1, hbits]
    refine ⟨?_, ?_⟩ <;> simp only [after, peak, this, scratch_CNOT, add_zero]
  have hall := chain (chain hC (touch_fact hrest true))
    (chain (touch_fact hadd true) (adjoint (touch_fact hprep false)))
  refine ⟨hall.1, ?_⟩
  rw [show peak scratch (lowerCSubConst N data s flag hws) true L = _ from hall.2]
  simp only [lowerCopyConstFromUnit, tmax_seq, tmax_CNOT, tmax_Negate, tmax_AddScaled,
    scratch_CNOT, scratch_Negate, scratch_AddScaled, tmax_copyBitPowers]
  exact cSub_arith _ _

/-! ## The theorem -/

/-- The walk of `Policy.lowerGate P G` is the walk of `G` with its blocks
opaque. -/
theorem lower_walk (hP : P.Admissible) :
    ∀ (G : Gate) (hws : Policy.GateWorkspaceOK P G) (d : Bool) (L : Finset ℕ),
      sGood P G d L →
      after (Policy.lowerGate P G hws) d L = sAfter P G d L ∧
      peak scratch (Policy.lowerGate P G hws) d L = sPeak P (Rec.ppPeak P) G d L := by
  intro G
  induction G with
  | id => intro _ d L _; simp [Policy.lowerGate, after, peak, sAfter, sPeak]
  | seq U V ihU ihV =>
      intro hws d L h
      cases d
      · obtain ⟨hV, hU⟩ := h
        obtain ⟨aV, pV⟩ := ihV hws.2 false L hV
        obtain ⟨aU, pU⟩ := ihU hws.1 false _ hU
        simp only [Policy.lowerGate, after, peak, sAfter, sPeak]
        rw [aV, aU, pV, pU]
        exact ⟨rfl, rfl⟩
      · obtain ⟨hU, hV⟩ := h
        obtain ⟨aU, pU⟩ := ihU hws.1 true L hU
        obtain ⟨aV, pV⟩ := ihV hws.2 true _ hV
        simp only [Policy.lowerGate, after, peak, sAfter, sPeak]
        rw [aU, aV, pU, pV]
        exact ⟨rfl, rfl⟩
  | adj U ih =>
      intro hws d L h
      exact ih hws (!d) L h
  | H _ | X _ | CNOT _ _ | Toffoli _ _ _ | RadixReverse _ _ | ShiftL _ _ | ShiftR _ _
  | Negate _ | AddScaled _ _ _ _ | zeroExtend _ _ | signExtend _ _ | zeroDealloc _ _
  | signDealloc _ _ =>
      intro _ d L _; exact ⟨rfl, rfl⟩
  | QFT r => intro hws d L h; exact qft_block P hP r hws d L h
  | SignedPhaseProd phi x z =>
      intro hws d L h
      exact signed_block P hP phi x z hws d L h
  | CSignedPhaseProd c phi x z =>
      intro hws d L h
      exact csigned_block P hP c phi x z hws d L h.1 h.2
  | CmpGeConst N data s flag =>
      intro hws d L h
      cases d
      · exact h.elim
      · exact cmpGe_block P N data s flag hws L h
  | CSubConst N data s flag =>
      intro hws d L h
      cases d
      · exact h.elim
      · exact cSub_block P N data s flag hws L h
  | idealCtrlModMul _ _ _ _ => intro hws; exact hws.elim

end QubitCount
end Shor
