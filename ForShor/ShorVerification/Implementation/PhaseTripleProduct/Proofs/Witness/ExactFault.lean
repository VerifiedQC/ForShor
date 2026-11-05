import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.ExactBoard.ExactBuild
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Witness.FaultChallenge

/-!
# O5 fault challenge: one bit below the exact width, the GATE-LEVEL circuit is wrong

FaultChallenge's accepted table `fixedTable` (k = 2, policy `fixed`, one band at 20) has exact
width `ptpTightWidth fixedTable 20 = 12` (`fixed_tight`). Here the gate-level circuit of a node
whose children run at `11 = 12 - 1` bits is built and evaluated in ForShor's `LowGate`
semantics, with every arithmetic gate WRAPPING at 11 bits (ForShor's basis laws
`extToInt_addScaledBasis_dst`, `extToInt_negateBasis`, no fit hypothesis):

* `body_eval_wrap`: classical simulation of a node body whose arithmetic wraps (programs
  without shifts), any children meeting `ChildSpecW` (sandwich leaves do);
* `fault_body_eval`: on slots holding the limbs `(1023, 511)` of `big = 2^19 - 1` (all three
  operands), the 11-bit node body applies `exp(iπ φ S₁₁)` with `S₁₁ = Σₜ cₜ wₜ³`, wrapped
  children `w = (1023, 511, -514, 512)` (the checkpoint `x₀ + x₁ = 1534` overflows 11 bits and is
  READ by child 2), while the correct phase is `φ · big³`; `S₁₁ - big³ = Δ = -1965658367590400`;
* `fault_impl`: the concrete split layout (20-bit parent registers, one extension qubit per
  slot) assembled as a `PolicyImplD fixed (fun _ _ => 11)`: a gate-level recursion following the
  policy with an INADMISSIBLE node width (`11 < ptpTightWidth = 12`);
* `gate_fault_wrong` (headline): there is a basis state with operands `big` (fitting 20 bits),
  clean workspace, on which that circuit, at angle `φ₀ = 1/Δ`, does NOT produce
  `exp(iπ φ₀ big³) · |b⟩`: it produces `-exp(iπ φ₀ big³) · |b⟩` (`fault_subnode_eval`);
* contrast: `ptp_gate_full_exact` (width 12) is correct on the same registers.

Per HG7 X1: minimality of `ptpTightWidth` is overflow-minimality; a wrong gate-level result needs
the overflowing value to be READ (here 1534 is a checkpoint). Ring operations commute with
`mod 2^W`, so where the overflowing value is only an intermediate that is later undone, the
one-bit-narrower circuit can still be correct (X1 example: Sfb4e5db96f73 band 1).
-/

namespace Shor.PTP.Instances.ExactFault

open Shor Operations Shor.PTP
  Shor.PTP.Instances.FaultChallenge

/-! ## Wrapping simulation of a node body (programs without shifts) -/

/-- No `shiftL`/`shiftR` (their basis laws need a fit hypothesis). -/
def noShift {k : ℕ} : Prog k → Bool
  | [] => true
  | .shiftL _ _ :: _ => false
  | .shiftR _ _ :: _ => false
  | _ :: ops => noShift ops

/-- The phase a body accumulates when every write goes through `f`. -/
def bodyPhaseF {k : ℕ} (f : ℤ → ℤ) (θ : ℕ → ℚ) : ℕ → Files k → Prog k → ℚ
  | _, _, [] => 0
  | t, V, .phaseProduct i :: ops =>
      θ t * (V 0 i : ℚ) * (V 1 i : ℚ) * (V 2 i : ℚ) + bodyPhaseF f θ (t + 1) V ops
  | t, V, .shiftL i n :: ops => bodyPhaseF f θ t (fun s => vStepF f (V s) (.shiftL i n)) ops
  | t, V, .shiftR i n :: ops => bodyPhaseF f θ t (fun s => vStepF f (V s) (.shiftR i n)) ops
  | t, V, .negate i :: ops => bodyPhaseF f θ t (fun s => vStepF f (V s) (.negate i)) ops
  | t, V, .addScaled d s neg sh :: ops =>
      bodyPhaseF f θ t (fun s' => vStepF f (V s') (.addScaled d s neg sh)) ops

theorem bodyPhaseF_eq {k : ℕ} (f : ℤ → ℤ) (θ : ℕ → ℚ) :
    ∀ (ops : Prog k) (t : ℕ) (V : Files k),
      bodyPhaseF f θ t V ops =
        ∑ j ∈ Finset.range (cpCount ops), θ (t + j) *
          ((runF f (V 0) ops).1.getD j 0 : ℚ) * ((runF f (V 1) ops).1.getD j 0 : ℚ) *
          ((runF f (V 2) ops).1.getD j 0 : ℚ)
  | [], t, V => by simp [bodyPhaseF, cpCount]
  | op :: ops, t, V => by
      cases op with
      | phaseProduct i =>
          simp only [bodyPhaseF, cpCount, runF]
          rw [Finset.sum_range_succ', bodyPhaseF_eq f θ ops (t + 1) V]
          simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
          rw [add_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show t + (j + 1) = t + 1 + j by omega]
      | shiftL i n => simp only [bodyPhaseF, cpCount, runF]; exact bodyPhaseF_eq f θ ops t _
      | shiftR i n => simp only [bodyPhaseF, cpCount, runF]; exact bodyPhaseF_eq f θ ops t _
      | negate i => simp only [bodyPhaseF, cpCount, runF]; exact bodyPhaseF_eq f θ ops t _
      | addScaled d s neg sh =>
          simp only [bodyPhaseF, cpCount, runF]; exact bodyPhaseF_eq f θ ops t _

theorem vStepF_neF {k : ℕ} (f : ℤ → ℤ) (V : Vals k) (op : valid_ops k) (j : Fin k)
    (hj : j ≠ dstOf op) : vStepF f V op j = V j := by
  cases op <;> simp_all [vStepF, upd, dstOf]

/-- One operand's gate with WRAPPING writes keeps the invariant (no fit hypothesis). -/
theorem opBasis_invW {k : ℕ} {Basis : Type*} [RegEncoding Basis] (Lay : NodeLayout k)
    {b0 b : Basis} {V : Files k} (hI : Inv Lay b0 b V) (s : Fin 3) (op : valid_ops k)
    (hns : ∀ i n, op ≠ .shiftL i n ∧ op ≠ .shiftR i n) (hok : opOK? op = true) :
    Inv Lay b0 (opBasis Lay s b op) (updF V s (vStepF (tcWrapInt Lay.width) (V s) op)) := by
  obtain ⟨hval, hbit⟩ := hI
  have hdst : extToInt (Lay.slot s (dstOf op)) (opBasis Lay s b op) =
      vStepF (tcWrapInt Lay.width) (V s) op (dstOf op) := by
    cases op with
    | shiftL i n => exact absurd rfl (hns i n).1
    | shiftR i n => exact absurd rfl (hns i n).2
    | negate i =>
        simp only [opBasis, dstOf, vStepF, upd, ↓reduceIte]
        rw [extToInt_negateBasis, hval s i, Lay.slot_width]
    | addScaled d src neg sh =>
        simp only [opBasis, dstOf, vStepF, upd, ↓reduceIte]
        have hne : d ≠ src := by simpa [opOK?] using hok
        have hds : ExtReg.ActiveDisjoint (Lay.slot s d) (Lay.slot s src) :=
          Lay.disjoint s d s src (by simp [hne])
        rw [extToInt_addScaledBasis_dst _ _ _ _ _ hds, Lay.slot_width]
        congr 1
        simp only [addScaledValue, hval]; ring
    | phaseProduct i => simp [opBasis, dstOf, vStepF, hval]
  have hother : ∀ s' i', (s', i') ≠ (s, dstOf op) →
      extToInt (Lay.slot s' i') (opBasis Lay s b op) = extToInt (Lay.slot s' i') b := by
    intro s' i' hne
    have hd : ExtReg.ActiveDisjoint (Lay.slot s' i') (Lay.slot s (dstOf op)) :=
      Lay.disjoint s' i' s (dstOf op) hne
    cases op with
    | shiftL i n => exact extToInt_shiftLBasis_of_activeDisjoint _ _ _ _ hd
    | shiftR i n => exact extToInt_shiftRBasis_of_activeDisjoint _ _ _ _ hd
    | negate i => exact extToInt_negateBasis_of_activeDisjoint _ _ _ hd
    | addScaled d src neg sh =>
        have hne' : d ≠ src := by simpa [opOK?] using hok
        exact extToInt_addScaledBasis_of_activeDisjoint _ _ _ _ _ _
          (Lay.disjoint s d s src (by simp [hne'])) hd
    | phaseProduct i => rfl
  refine ⟨?_, ?_⟩
  · intro s' i'
    by_cases h : (s', i') = (s, dstOf op)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [hdst]; simp [updF]
    · rw [hother s' i' h, hval s' i']
      by_cases hs : s' = s
      · subst hs
        have hi : i' ≠ dstOf op := fun e => h (by rw [e])
        simp [updF, vStepF_neF _ (V s') op i' hi]
      · simp [updF, hs]
  · intro q hq
    have hq' : q ∉ (Lay.slot s (dstOf op)).active.qubits := hq s (dstOf op)
    rw [← hbit q hq]
    cases op with
    | shiftL i n => exact bit_shiftLBasis_out _ _ _ _ hq'
    | shiftR i n => exact bit_shiftRBasis_out _ _ _ _ hq'
    | negate i => exact bit_negateBasis_out _ _ _ hq'
    | addScaled d src neg sh => exact bit_addScaledBasis_out _ _ _ _ _ _ hq'
    | phaseProduct i => rfl

theorem opGates_stepW {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) {b0 b : qs.Basis} {V : Files k} (hI : Inv Lay b0 b V) (op : valid_ops k)
    (hns : ∀ i n, op ≠ .shiftL i n ∧ op ≠ .shiftR i n) (hok : opOK? op = true) :
    ∃ b', LowerGateClass.evalL (qs := qs) (opGates Lay op) (qs.ket b) = qs.ket b' ∧
      Inv Lay b0 b' (fun s => vStepF (tcWrapInt Lay.width) (V s) op) := by
  set f := tcWrapInt Lay.width
  have h1 := opBasis_invW Lay hI 0 op hns hok
  have h2 := opBasis_invW Lay h1 1 op hns hok
  have h3 := opBasis_invW Lay h2 2 op hns hok
  refine ⟨opBasis Lay 2 (opBasis Lay 1 (opBasis Lay 0 b op) op) op, ?_, ?_⟩
  · rw [opGates, LowerGateClass.evalL_seq, LowerGateClass.evalL_seq, evalL_opGate, evalL_opGate,
      evalL_opGate]
  · have e : updF (updF (updF V 0 (vStepF f (V 0) op)) 1
        (vStepF f ((updF V 0 (vStepF f (V 0) op)) 1) op)) 2
        (vStepF f ((updF (updF V 0 (vStepF f (V 0) op)) 1
          (vStepF f ((updF V 0 (vStepF f (V 0) op)) 1) op)) 2) op) =
        fun s => vStepF f (V s) op := by
      funext s
      fin_cases s <;> simp [updF]
    rw [← e]; exact h3

/-- `ChildSpec` without the fit premise (what a leaf needs: nothing about the values). -/
def ChildSpecW {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) (θ : ℕ → ℚ) (b0 : qs.Basis) (child : ℕ → Fin k → LowGate) : Prop :=
  ∀ (t : ℕ) (i : Fin k) (b : qs.Basis),
    (∀ q, (∀ s j, q ∉ (Lay.slot s j).active.qubits) →
      RegEncoding.bit q b = RegEncoding.bit q b0) →
    LowerGateClass.evalL (qs := qs) (child t i) (qs.ket b) =
      Complex.exp (((Angle.toReal (θ t * (extToInt (Lay.slot 0 i) b : ℚ) *
        (extToInt (Lay.slot 1 i) b : ℚ) * (extToInt (Lay.slot 2 i) b : ℚ)) : ℝ) : ℂ) *
        Complex.I) • qs.ket b

theorem leafSandwich_childSpecW {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis]
    [LowerGateClass qs] (Lay : NodeLayout k) (θ : ℕ → ℚ) (b0 : qs.Basis) (ta ua : ℕ)
    (hA : NodeAnc Lay ta ua) (h0 : AncClean ta ua b0) :
    ChildSpecW Lay θ b0
      (fun t i => ptpLeafSandwich (θ t) (Lay.slot 0 i) (Lay.slot 1 i) (Lay.slot 2 i) ta ua) := by
  intro t i b hoff
  have hclean : AncClean ta ua b :=
    ⟨(hoff ta fun s j => (hA.2 s j).1).trans h0.1, (hoff ua fun s j => (hA.2 s j).2).trans h0.2⟩
  rw [evalL_ptpLeafSandwich_ket _ _ _ _ _ _ b (triple_disjoint Lay i) (hA.sandwichAnc i) hclean]
  congr 2
  simp only [Angle.toReal]
  push_cast
  ring

/-- **Body simulation with wrapping arithmetic** (no shifts): the body maps `ket b` to
`exp(iπ · bodyPhaseF (wrap C)) • ket b'`, `b'` holding the wrapped run's final values. -/
theorem body_eval_wrap {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) (θ : ℕ → ℚ) (b0 : qs.Basis)
    (child : ℕ → Fin k → LowGate) (hchild : ChildSpecW Lay θ b0 child) :
    ∀ (ops : Prog k) (t : ℕ) (V : Files k) (b : qs.Basis), Inv Lay b0 b V →
      noShift ops = true → wellFormed? ops = true →
      ∃ b', LowerGateClass.evalL (qs := qs) (body Lay child t ops) (qs.ket b) =
        Complex.exp (((Angle.toReal (bodyPhaseF (tcWrapInt Lay.width) θ t V ops) : ℝ) : ℂ) *
          Complex.I) • qs.ket b' ∧
        Inv Lay b0 b' (fun s => (runF (tcWrapInt Lay.width) (V s) ops).2)
  | [], t, V, b, hI, _, _ => ⟨b, by simp [body, bodyPhaseF, LowerGateClass.evalL_id], by
      simpa [runF] using hI⟩
  | op :: ops, t, V, b, hI, hS, hW => by
      have hok : opOK? op = true := by
        simp only [wellFormed?, Bool.and_eq_true] at hW; exact hW.1
      have hW' : wellFormed? ops = true := by
        simp only [wellFormed?, Bool.and_eq_true] at hW; exact hW.2
      cases op with
      | shiftL i n => simp [noShift] at hS
      | shiftR i n => simp [noShift] at hS
      | phaseProduct i =>
          have hS' : noShift ops = true := by simpa [noShift] using hS
          obtain ⟨b', he, hI'⟩ := body_eval_wrap Lay θ b0 child hchild ops (t + 1) V b hI hS' hW'
          refine ⟨b', ?_, by simpa [runF] using hI'⟩
          simp only [body, bodyPhaseF, LowerGateClass.evalL_seq]
          rw [hchild t i b hI.2, hI.1, hI.1, hI.1, LowerGateClass.evalL_smul, he, smul_smul,
            ← Complex.exp_add, Angle.toReal_add]
          congr 2
          push_cast
          ring
      | negate i =>
          have hS' : noShift ops = true := by simpa [noShift] using hS
          obtain ⟨b1, he1, hI1⟩ := opGates_stepW Lay hI _ (fun _ _ => ⟨by simp, by simp⟩) hok
          obtain ⟨b', he, hI'⟩ := body_eval_wrap Lay θ b0 child hchild ops t _ b1 hI1 hS' hW'
          exact ⟨b', by simp only [body, bodyPhaseF, LowerGateClass.evalL_seq]; rw [he1, he], by
            simpa [runF] using hI'⟩
      | addScaled d src neg sh =>
          have hS' : noShift ops = true := by simpa [noShift] using hS
          obtain ⟨b1, he1, hI1⟩ := opGates_stepW Lay hI _ (fun _ _ => ⟨by simp, by simp⟩) hok
          obtain ⟨b', he, hI'⟩ := body_eval_wrap Lay θ b0 child hchild ops t _ b1 hI1 hS' hW'
          exact ⟨b', by simp only [body, bodyPhaseF, LowerGateClass.evalL_seq]; rw [he1, he], by
            simpa [runF] using hI'⟩

/-! ## The FaultChallenge node at 11 = exact - 1 bits -/

/-- The wrapped weighted sum `Σₜ cₜ wₜ³`, `w = (1023, 511, -514, 512)`. -/
def S11 : ℚ :=
  (1 - B ^ 2) * 1023 ^ 3 + (B ^ 3 - B) * 511 ^ 3 + (B ^ 2 + B) / 2 * (-514) ^ 3 +
    (B ^ 2 - B) / 2 * 512 ^ 3

/-- `S₁₁ - big³ = Δ`. -/
theorem S11_sub : S11 - (big : ℚ) ^ 3 = -1965658367590400 := by
  simp only [S11, B, big]; norm_num

theorem fixed_noShift : noShift fixedTable.ops = true := by decide +kernel
theorem fixed_wf : wellFormed? fixedTable.ops = true := by decide +kernel
theorem fixed_cp : cpCount fixedTable.ops = 4 := by decide +kernel

/-- The limbs of `big` at the node (`limbWidth 20 2 = 10`). -/
def Lbig : Files fixedTable.k := fun _ => limbsAt fixedTable.k (limbWidth 20 fixedTable.k) big

theorem wrap11_returns (s : Fin 3) : (runF (tcWrapInt 11) (Lbig s) fixedTable.ops).2 = Lbig s := by
  have e : Lbig s = Lbig 0 := rfl
  rw [e]; funext j; fin_cases j <;> decide +kernel

theorem phase11 (φ : Angle) :
    bodyPhaseF (tcWrapInt 11) (fun t => φ * coeffN fixedTable 20 t) 0 Lbig fixedTable.ops =
      φ * S11 := by
  rw [bodyPhaseF_eq]
  have hch : ∀ s, (runF (tcWrapInt 11) (Lbig s) fixedTable.ops).1 = [1023, 511, -514, 512] :=
    fun _ => wrapped11_children
  simp only [hch, fixed_cp, Finset.sum_range_succ, Finset.sum_range_zero]
  have hc : ∀ t : Fin 4, coeffN fixedTable 20 t =
      ![1 - B ^ 2, B ^ 3 - B, (B ^ 2 + B) / 2, (B ^ 2 - B) / 2] t := fun t => by
    rw [coeffN]; simp only [show (t : ℕ) < fixedTable.pts.length from t.2, ↓reduceDIte]; exact fixed_coeff t
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2; have h3 := hc 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  have h3' : coeffN fixedTable 20 3 = (B ^ 2 - B) / 2 := h3
  simp only [zero_add, List.getD_cons_zero, List.getD_cons_succ, h0, h1, h2, h3', S11]
  simp
  ring

/-- **The 11-bit node body on the limbs of `big`** (sandwich leaves, any layout of width 11):
it applies `exp(iπ φ S₁₁)` and returns the basis state. -/
theorem fault_body_eval {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout fixedTable.k) (hw : Lay.width = 11) (φ : Angle) (ta ua : ℕ)
    (hA : NodeAnc Lay ta ua) (b : qs.Basis) (hcl : AncClean ta ua b)
    (hb : ∀ s i, extToInt (Lay.slot s i) b = Lbig s i) :
    LowerGateClass.evalL (qs := qs) (ptpNode fixedTable Lay 20 φ ta ua) (qs.ket b) =
      Complex.exp (((Angle.toReal (φ * S11) : ℝ) : ℂ) * Complex.I) • qs.ket b := by
  have hI0 : Inv Lay b b Lbig := ⟨hb, fun _ _ => rfl⟩
  obtain ⟨b', he, hI'⟩ := body_eval_wrap Lay (fun t => φ * coeffN fixedTable 20 t) b _
    (leafSandwich_childSpecW Lay _ b ta ua hA hcl) fixedTable.ops 0 Lbig b hI0 fixed_noShift fixed_wf
  rw [hw] at he hI'
  have hfin : (fun s => (runF (tcWrapInt 11) (Lbig s) fixedTable.ops).2) = Lbig :=
    funext wrap11_returns
  rw [hfin] at hI'
  have hb' : b' = b := inv_unique Lay hI' hI0
  unfold ptpNode
  rw [he, hb', phase11]

/-! ## A concrete gate-level recursion with the node one bit below exact -/

theorem disj_of_check {l1 l2 : List ℕ} (h : (l1.all fun a => !l2.contains a) = true) :
    l1.Disjoint l2 := by
  intro a h1 h2
  have := List.all_eq_true.mp h a h1
  exact (by simpa using this : a ∉ l2) h2

/-- Parent register `s`: qubits `[20s, 20s + 20)`. -/
def X (s : Fin 3) : ExtReg := ExtReg.ofReg (Reg.interval (20 * s) 20)

/-- Chunk register of child slot `(s, j)` with a 1-qubit reserve at `60 + 2s + j`. -/
def pre (s : Fin 3) (j : Fin 2) : ExtReg :=
  ExtReg.withReserve (chunkReg (X s).active 2 ((X s).width / 2) j) (Reg.interval (60 + 2 * s + j) 1)
    (disj_of_check (by revert s j; decide +kernel))

/-- The split at child width `11` (= exact − 1): chunks of 10 bits, one extension bit each. -/
def SL11 : SplitLayout X fixedTable.k 11 where
  pre := pre
  ext := fun _ _ => 1
  two_le := by decide +kernel
  pre_active := fun s j => rfl
  can_grow := by intro s j; show 1 ≤ (pre s j).capacity; revert s j; decide +kernel
  ext_width := by decide +kernel
  ext_pos := by decide +kernel
  disjoint := by
    intro s j s' j' h
    apply disj_of_check
    revert h
    revert s j s' j'
    decide +kernel

/-- Child slot triple `j` (width 11). -/
def Y (j : Fin 2) : Fin 3 → ExtReg := fun s => SL11.lay.slot s j

/-- The circuit family: split, 11-bit node body with sandwich leaves (ancillas 66, 67), unsplit. -/
noncomputable def G (φ : Angle) : LowGate :=
  ptpSubNode fixedTable SL11 (fun t j => ptpLeafSandwich (φ * coeffN fixedTable 20 t)
    (Y j 0) (Y j 1) (Y j 2) 66 67)

/-- Its workspace. -/
def W : List ℕ := SL11.R ++ [66, 67]

/-- **`G` is a gate-level recursion following `fixed`**, with the inadmissible node width
`fun _ _ => 11` (`11 < ptpTightWidth fixedTable 20 = 12`). -/
theorem fault_impl : PolicyImplD fixed (fun _ _ => 11) X 20 W G := by
  refine PolicyImplD.node (wd := fun _ _ => 11) X 20 fixedTable (by decide +kernel) (by decide)
    rfl (by decide) SL11 (fun j θ => ptpLeafSandwich θ (Y j 0) (Y j 1) (Y j 2) 66 67) [66, 67]
    (fun _ => [66, 67]) (fun _ _ h => h) (by unfold SplitLayout.lay; decide +kernel) ?_
  intro j
  refine PolicyImplD.leaf (Y j) 11 66 67 ?_ ?_ ?_ ?_
  · intro s; exact SL11.lay.slot_width s j
  · intro T hT
    have h11 : fixed.choose 11 = none := rfl
    simp [h11] at hT
  · refine ⟨disj_of_check ?_, disj_of_check ?_, disj_of_check ?_⟩ <;> revert j <;> decide +kernel
  · unfold SandwichAnc; revert j; decide +kernel

/-- The node width of `fault_impl` is NOT admissible: one bit below exact. -/
theorem fault_not_admissible : ¬ Admissible fixed (fun _ _ => 11) := by
  intro h
  have := h ⟨20, fixedTable⟩ (by simp [fixed]) 20 (by decide)
  simp only [fixed_tight] at this
  omega

theorem nodeAnc11 : NodeAnc SL11.lay 66 67 := by
  unfold NodeAnc SplitLayout.lay; decide +kernel

/-- **The full 11-bit circuit on registers holding `big`** applies `exp(iπ φ S₁₁)`. -/
theorem fault_subnode_eval {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (φ : Angle) (b : qs.Basis) (hX : ∀ s, extToInt (X s) b = big)
    (hcl : ∀ q ∈ W, RegEncoding.bit q b = false) :
    LowerGateClass.evalL (qs := qs) (G φ) (qs.ket b) =
      Complex.exp (((Angle.toReal (φ * S11) : ℝ) : ℂ) * Complex.I) • qs.ket b := by
  have hR : ∀ q ∈ SL11.R, RegEncoding.bit q b = false := fun q hq => hcl q (by simp [W, hq])
  set b1 := SL11.allocBasis b with hb1
  have hXw : ∀ s, (X s).width = 20 := by decide +kernel
  have hslot : ∀ s j, extToInt (SL11.lay.slot s j) b1 = Lbig s j := by
    intro s j
    rw [hb1, SL11.slot_value hXw (by decide) b hR s j, hX s]
    rfl
  have hoff : ∀ q, q = 66 ∨ q = 67 → q ∉ SL11.R := by
    intro q hq hm
    have : ∀ q ∈ SL11.R, q < 66 := by unfold SplitLayout.R; decide +kernel
    have := this q hm
    omega
  have hcl1 : AncClean 66 67 b1 := by
    refine ⟨?_, ?_⟩
    · rw [hb1, SL11.bit_allocBasis_out b (hoff 66 (Or.inl rfl))]; exact hcl 66 (by simp [W])
    · rw [hb1, SL11.bit_allocBasis_out b (hoff 67 (Or.inr rfl))]; exact hcl 67 (by simp [W])
  have hbody := fault_body_eval (qs := qs) SL11.lay rfl φ 66 67 nodeAnc11 b1 hcl1 hslot
  have hket : qs.ket b1 = LowerGateClass.evalL (qs := qs) SL11.alloc (qs.ket b) :=
    (SL11.evalL_alloc b).symm
  unfold G ptpSubNode
  unfold ptpNode at hbody
  rw [LowerGateClass.evalL_seq, LowerGateClass.evalL_seq, SL11.evalL_alloc, ← hb1]
  simp only [Y]
  rw [hbody, LowerGateClass.evalL_smul, hket, LowerGateClass.evalL_adj_apply]

/-! ## A witness basis state -/

/-- `big` written into the three parent registers of the all-zero basis state. -/
noncomputable def bigState {Basis : Type*} [RegEncoding Basis] : Basis :=
  RegEncoding.writeNat (X 2).active 524287 (RegEncoding.writeNat (X 1).active 524287
    (RegEncoding.writeNat (X 0).active 524287 RegEncoding.zero))

theorem X_disjoint : ∀ s s' : Fin 3, s ≠ s' → ∀ q ∈ (X s).active.qubits, q ∉ (X s').active.qubits := by
  decide +kernel

theorem bigState_bit_off {Basis : Type*} [RegEncoding Basis] (q : ℕ) (hq : 60 ≤ q) :
    RegEncoding.bit q (bigState : Basis) = false := by
  have hX : ∀ s : Fin 3, q ∉ (X s).active.qubits := by
    intro s hm
    have : ∀ s : Fin 3, ∀ q ∈ (X s).active.qubits, q < 60 := by decide +kernel
    have := this s q hm
    omega
  unfold bigState
  rw [RegEncoding.bit_writeNat_out _ _ _ _ (hX 2), RegEncoding.bit_writeNat_out _ _ _ _ (hX 1),
    RegEncoding.bit_writeNat_out _ _ _ _ (hX 0), RegEncoding.bit_zero]

theorem bigState_val {Basis : Type*} [RegEncoding Basis] (s : Fin 3) :
    extToInt (X s) (bigState : Basis) = big := by
  have hsz : ∀ s : Fin 3, 524287 < ASize (X s).active := by decide +kernel
  have hw : ∀ s : Fin 3, (X s).width = 20 := by decide +kernel
  have hnat : RegEncoding.toNat (X s).active (bigState : Basis) = 524287 := by
    unfold bigState
    fin_cases s
    · show RegEncoding.toNat (X 0).active _ = _
      rw [toNat_congr (X 0).active (b' := RegEncoding.writeNat (X 0).active 524287
          (RegEncoding.zero : Basis)) fun q hq => by
        rw [RegEncoding.bit_writeNat_out _ _ _ _ (X_disjoint 0 2 (by decide) q hq),
          RegEncoding.bit_writeNat_out _ _ _ _ (X_disjoint 0 1 (by decide) q hq)]]
      exact RegEncoding.toNat_writeNat_of_lt _ _ _ (hsz 0)
    · show RegEncoding.toNat (X 1).active _ = _
      rw [toNat_congr (X 1).active (b' := RegEncoding.writeNat (X 1).active 524287
          (RegEncoding.writeNat (X 0).active 524287 (RegEncoding.zero : Basis))) fun q hq => by
        rw [RegEncoding.bit_writeNat_out _ _ _ _ (X_disjoint 1 2 (by decide) q hq)]]
      exact RegEncoding.toNat_writeNat_of_lt _ _ _ (hsz 1)
    · exact RegEncoding.toNat_writeNat_of_lt _ _ _ (hsz 2)
  unfold extToInt ExtReg.toNat
  rw [hnat, hw s]
  decide +kernel

/-- **O5 fault (gate level).** One bit below the exact width at the node (children at 11 bits,
`ptpTightWidth fixedTable 20 = 12`), the gate-level recursion `G` (a `PolicyImplD` following
`fixed`, `fault_impl`) is WRONG: on the basis state `bigState` (all three operands
`big = 2^19 - 1`, which fit 20 signed bits; workspace clean), at angle `φ₀ = 1/Δ` it applies
`-exp(iπ φ₀ big³)` instead of `exp(iπ φ₀ big³)`. The overflowing value `1534` is a checkpoint,
i.e. it is read by a child (HG7 X1). -/
theorem gate_fault_wrong {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs] :
    let φ₀ : Angle := 1 / (-1965658367590400)
    (∀ s, FitsSignedWidth 20 (extToInt (X s) (bigState : qs.Basis))) ∧
      (∀ q ∈ W, RegEncoding.bit q (bigState : qs.Basis) = false) ∧
      LowerGateClass.evalL (qs := qs) (G φ₀) (qs.ket bigState) ≠
        Complex.exp (((Angle.toReal φ₀ : ℝ) : ℂ) * Complex.I *
          (((extToInt (X 0) (bigState : qs.Basis) : ℤ) : ℂ) *
            ((extToInt (X 1) (bigState : qs.Basis) : ℤ) : ℂ) *
            ((extToInt (X 2) (bigState : qs.Basis) : ℤ) : ℂ))) • qs.ket bigState := by
  intro φ₀
  have hW : ∀ q ∈ W, 60 ≤ q := by unfold W SplitLayout.R; decide +kernel
  refine ⟨fun s => by rw [bigState_val]; exact big_fits, fun q hq => bigState_bit_off q (hW q hq),
    ?_⟩
  rw [fault_subnode_eval φ₀ _ bigState_val fun q hq => bigState_bit_off q (hW q hq)]
  simp only [bigState_val]
  intro h
  have hk := qs.ket_ne_zero (bigState : qs.Basis)
  have he := smul_left_injective ℂ hk h
  -- the two exponents differ by `iπ`
  have hd : (((Angle.toReal (φ₀ * S11) : ℝ) : ℂ) * Complex.I) =
      ((Angle.toReal φ₀ : ℝ) : ℂ) * Complex.I * (((big : ℤ) : ℂ) * ((big : ℤ) : ℂ) * ((big : ℤ) : ℂ)) +
        (Real.pi : ℂ) * Complex.I := by
    have hs : S11 = (big : ℚ) ^ 3 + (-1965658367590400) := by rw [← S11_sub]; ring
    simp only [Angle.toReal, φ₀, hs]
    push_cast
    ring
  rw [hd, Complex.exp_add, Complex.exp_pi_mul_I] at he
  have hne := Complex.exp_ne_zero (((Angle.toReal φ₀ : ℝ) : ℂ) * Complex.I *
    (((big : ℤ) : ℂ) * ((big : ℤ) : ℂ) * ((big : ℤ) : ℂ)))
  exact hne (by linear_combination (-1 / 2 : ℂ) * he)

/-- Contrast: on the same registers, the exact-board circuit (`ptp_gate_full_exact`, node at
`ptpTightWidth = 12`) is correct for every angle. -/
theorem exact_contrast {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs] :
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplX fixed X 20 W G ∧
      ∀ (φ : Angle) (b : qs.Basis), (∀ s, FitsSignedWidth 20 (extToInt (X s) b)) →
        (∀ q ∈ W, RegEncoding.bit q b = false) →
        LowerGateClass.evalL (qs := qs) (G φ) (qs.ket b) =
          Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
            (((extToInt (X 0) b : ℤ) : ℂ) * ((extToInt (X 1) b : ℤ) : ℂ) *
              ((extToInt (X 2) b : ℤ) : ℂ))) • qs.ket b := by
  have hG : Good X 20 60 := by
    refine ⟨by decide +kernel, fun s s' h q h1 h2 => X_disjoint s s' h q h1 h2, ?_⟩
    decide +kernel
  obtain ⟨W, G, hI, -, hC, -⟩ := ptp_gate_full_exact (qs := qs) fixed fixed_accepted 20 X 60 hG
  exact ⟨W, G, hI, hC⟩

end Shor.PTP.Instances.ExactFault
