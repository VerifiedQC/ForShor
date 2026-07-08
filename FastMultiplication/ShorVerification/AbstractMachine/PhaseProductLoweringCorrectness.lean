import FastMultiplication.ShorVerification.AbstractMachine.LowGate
import FastMultiplication.ShorVerification.AlgorithmCorrectness.PhaseProduct.CompilationCorrectness

namespace Shor
open Gate
open Operations

/-!
# Phase-Product Lowering Correctness

This file defines the recursive lowering pass and its correctness theorems.
The translation from the high-level `Gate` language to the low-level `LowGate`
machine is kept here, while the high-level circuit identities it depends on
live under `AlgorithmCorrectness`.
-/

/-! =========================================================
    Section 1: Recursive lowering definitions

    These definitions lower high-level gates structurally, delegating
    phase-product and QFT nodes to specialized recursive lowerers.
========================================================= -/

/-- Recursively lower a gate into the low-level language using a size cutoff. -/
noncomputable def lowerGateRec
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (initSize : ℕ) (k : ℕ) (hk : 1 < k)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (ops : Prog k) :
  Gate → LowGate
  | Gate.id => LowGate.id
  | Gate.seq U V =>
      LowGate.seq
        (lowerGateRec (Basis := Basis) initSize k hk pts hpts ops U)
        (lowerGateRec (Basis := Basis) initSize k hk pts hpts ops V)
  | Gate.adj U =>
      LowGate.adj (lowerGateRec (Basis := Basis) initSize k hk pts hpts ops U)
  | Gate.H q => LowGate.H q
  | Gate.X q => LowGate.X q
  | Gate.Prim s qs => LowGate.Prim s qs
  | Gate.ShiftL r n => LowGate.ShiftL r n
  | Gate.ShiftR r n => LowGate.ShiftR r n
  | Gate.Negate r => LowGate.Negate r
  | Gate.AddScaled dst src negSrc sh =>
      LowGate.AddScaled dst src negSrc sh
  | Gate.QFT r =>
      LowGate.Prim "QFT" [r.lo, r.hi]
  | Gate.SignedPhaseProd phi x z =>
      let Wrec := nextSignedWidth x z ops
      if _hrec : Wrec < initSize then
        let Wphase := phaseLimbWidth x z k
        let coeff := phaseCoeffFromPtsWidth k Wphase pts hpts
        let g :=
          compileOpsToSignedGate
            (Basis := Basis) k hk phi x z coeff ops
        lowerGateRec (Basis := Basis) Wrec k hk pts hpts ops g
      else
        LowGate.Naive_SignedPhaseProd phi x z
  | Gate.CSignedPhaseProd ctrl phi x z =>
      by
        classical
        let Wrec := nextSignedWidth x z ops
        exact
          if _hctrl : ExtReg.CtrlDisjoint ctrl x z then
            if _hrec : Wrec < initSize then
              let Wphase := phaseLimbWidth x z k
              let coeff := phaseCoeffFromPtsWidth k Wphase pts hpts
              let g :=
                compileOpsToCSignedGate
                  (Basis := Basis) k hk ctrl phi x z coeff ops
              lowerGateRec (Basis := Basis) Wrec k hk pts hpts ops g
            else
              LowGate.Naive_CSignedPhaseProd ctrl phi x z
          else
            LowGate.Naive_CSignedPhaseProd ctrl phi x z
  | Gate.zeroExtend r n =>
      LowGate.zeroExtend r n
  | Gate.signExtend r n =>
      LowGate.signExtend r n
  | Gate.zeroDealloc r n =>
      LowGate.zeroDealloc r n
  | Gate.signDealloc r n =>
      LowGate.signDealloc r n
  | Gate.RadixReverse r m =>
      LowGate.RadixReverse r m

/-- Lower a signed phase product by interpolation-based decomposition. -/
noncomputable def lowerSignedPhaseProd
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (k : ℕ) (hk : 1 < k) (phi : ℝ) (x z : ExtReg) (ops : Prog k) :=
  let pts := genInterpolationPoints k
  let hpts : pts.length = q k := by
    simp [pts, genInterpolationPoints, q]
  let Wrec := nextSignedWidth x z ops
  if _hrec : Wrec < phaseInputSize x z then
    let Wphase := phaseLimbWidth x z k
    let coeff := phaseCoeffFromPtsWidth k Wphase pts hpts
    let g :=
      compileOpsToSignedGate
        (Basis := Basis) k hk phi x z coeff ops
    lowerGateRec (Basis := Basis) Wrec k hk pts hpts ops g
  else
    LowGate.Naive_SignedPhaseProd phi x z

/-- Lower a controlled signed phase product by the same interpolation path as
    signed phase products when the control is disjoint from both operands. -/
noncomputable def lowerCSignedPhaseProd
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (phi : ℝ) (x z : ExtReg)
  (ops : Prog k) : LowGate := by
  classical
  let pts := genInterpolationPoints k
  let hpts : pts.length = q k := by
    simp [pts, genInterpolationPoints, q]
  let Wrec := nextSignedWidth x z ops
  exact
    if _hctrl : ExtReg.CtrlDisjoint ctrl x z then
      if _hrec : Wrec < phaseInputSize x z then
        let Wphase := phaseLimbWidth x z k
        let coeff := phaseCoeffFromPtsWidth k Wphase pts hpts
        let g :=
          compileOpsToCSignedGate
            (Basis := Basis) k hk ctrl phi x z coeff ops
        lowerGateRec (Basis := Basis) Wrec k hk pts hpts ops g
      else
        LowGate.Naive_CSignedPhaseProd ctrl phi x z
    else
      LowGate.Naive_CSignedPhaseProd ctrl phi x z

/-- Lower an unsigned phase product by interpolation-based decomposition. -/
noncomputable def lowerPhaseProd
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (k : ℕ) (hk : 1 < k) (phi : ℝ) (x z : Reg) (ops : Prog k) :=
  let pts := genInterpolationPoints k
  let hpts : pts.length = q k := by
    simp [pts, genInterpolationPoints, q]
  let op1 := Gate.PhaseProd phi x z
  lowerGateRec
    (Basis := Basis)
    (phaseInputSize (Gate.unsignedView x) (Gate.unsignedView z))
    k hk pts hpts ops op1

noncomputable def lowerQFTAux
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (k : ℕ) (hk : 1 < k) (ops : Prog k) : ℕ → Reg → LowGate
  | 0,   _ => .id
  | 1,   r => .H r.lo
  | n+2, r =>
      let nTot : ℕ := n + 2
      let m : ℕ := nTot / 2
      let left  : Reg := { lo := r.lo, size := m }
      let right : Reg := { lo := r.lo + m, size := regSize r - m }
      (lowerQFTAux (Basis := Basis) k hk ops (nTot - m) right) ;;
      (lowerPhaseProd (Basis := Basis) k hk (qftPhi nTot) left right ops) ;;
      (lowerQFTAux (Basis := Basis) k hk ops m left) ;;
      (LowGate.RadixReverse r m)

noncomputable def lowerQFT
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (k : ℕ) (hk : 1 < k) (r : Reg) (ops : Prog k) : LowGate :=
  lowerQFTAux (Basis := Basis) k hk ops (regSize r) r

/-- Global lowering function from `Gate` to `LowGate`. -/
noncomputable def lowerGate
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (k : ℕ) (hk : 1 < k) (ops : Prog k) : Gate → LowGate
  | .id => .id
  | .seq U V =>
      (lowerGate (Basis := Basis) k hk ops U) ;;
      (lowerGate (Basis := Basis) k hk ops V)
  | .adj U => †(lowerGate (Basis := Basis) k hk ops U)
  | .H q => .H q
  | .X q => .X q
  | .QFT r => lowerQFT (Basis := Basis) k hk r ops
  | .SignedPhaseProd p x z =>
      lowerSignedPhaseProd (Basis := Basis) k hk p x z ops
  | .CSignedPhaseProd c p x z =>
      lowerCSignedPhaseProd (Basis := Basis) k hk c p x z ops
  | .Prim tag args => .Prim tag args
  | .ShiftL r n => .ShiftL r n
  | .ShiftR r n => .ShiftR r n
  | .AddScaled dst src negSrc shift => .AddScaled dst src negSrc shift
  | .Negate r => .Negate r
  | Gate.zeroExtend r n => LowGate.zeroExtend r n
  | Gate.signExtend r n => LowGate.signExtend r n
  | Gate.zeroDealloc r n => LowGate.zeroDealloc r n
  | Gate.signDealloc r n => LowGate.signDealloc r n
  | Gate.RadixReverse r m => LowGate.RadixReverse r m

/-! =========================================================
    Section 2: Low-level semantic interface
========================================================= -/

class LowerGateClass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis] : Type where

  evalL : LowGate → qs.State → qs.State

  evalL_id :
    ∀ ψ, evalL LowGate.id ψ = ψ

  evalL_seq :
    ∀ (U V : LowGate) (ψ : qs.State),
      evalL (U ;; V) ψ = evalL V (evalL U ψ)

  evalL_H :
    ∀ (q : ℕ) (ψ : qs.State),
      evalL (.H q) ψ = qs.eval (.H q) ψ

  evalL_X :
    ∀ (q : ℕ) (ψ : qs.State),
      evalL (.X q) ψ = qs.eval (.X q) ψ

  evalL_Prim :
    ∀ (tag : String) (args : List ℕ) (ψ : qs.State),
      evalL (.Prim tag args) ψ = qs.eval (Gate.Prim tag args) ψ

  evalL_shiftL :
    ∀ r n ψ,
      evalL (LowGate.ShiftL r n) ψ = qs.eval (Gate.ShiftL r n) ψ

  evalL_shiftR :
    ∀ r n ψ,
      evalL (LowGate.ShiftR r n) ψ = qs.eval (Gate.ShiftR r n) ψ

  evalL_negate :
    ∀ r ψ,
      evalL (LowGate.Negate r) ψ = qs.eval (Gate.Negate r) ψ

  evalL_addScaled :
    ∀ dst src negSrc sh ψ,
      evalL (LowGate.AddScaled dst src negSrc sh) ψ
        = qs.eval (Gate.AddScaled dst src negSrc sh) ψ

  evalL_naive_signedPhaseProd :
    ∀ p x z ψ,
      evalL (LowGate.Naive_SignedPhaseProd p x z) ψ
        = qs.eval (Gate.SignedPhaseProd p x z) ψ

  evalL_naive_csignedPhaseProd :
    ∀ c p x z ψ,
      evalL (LowGate.Naive_CSignedPhaseProd c p x z) ψ
        = qs.eval (Gate.CSignedPhaseProd c p x z) ψ

  evalL_adj_of_lowered :
    ∀ (k : ℕ) (hk : 1 < k) (U : Gate) (ψ : qs.State) (ops : Prog k),
      evalL (†(lowerGate (Basis := qs.Basis) k hk ops U)) ψ = qs.eval (†U) ψ

  evalL_zeroExtend :
    ∀ r n ψ,
      evalL (LowGate.zeroExtend r n) ψ = qs.eval (Gate.zeroExtend r n) ψ

  evalL_signExtend :
    ∀ r n ψ,
      evalL (LowGate.signExtend r n) ψ = qs.eval (Gate.signExtend r n) ψ

  evalL_zeroDealloc :
    ∀ r n ψ,
      evalL (LowGate.zeroDealloc r n) ψ = qs.eval (Gate.zeroDealloc r n) ψ

  evalL_signDealloc :
    ∀ r n ψ,
      evalL (LowGate.signDealloc r n) ψ = qs.eval (Gate.signDealloc r n) ψ

  evalL_lowerRadixReverse:
    ∀ r m ψ,
      evalL (LowGate.RadixReverse r m) ψ = qs.eval (Gate.RadixReverse r m) ψ

namespace LowerGateClass

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [ExtRegEncoding qs.Basis]
variable [ExtRegSplitSemantics qs.Basis]
variable [LowerGateClass qs]

theorem evalL_naive_phaseProd
  (p : ℝ) (x z : ExtReg) (ψ : qs.State) :
  LowerGateClass.evalL (qs := qs) (LowGate.Naive_SignedPhaseProd p x z) ψ
    =
  qs.eval (Gate.SignedPhaseProd p x z) ψ := by
  simp[(LowerGateClass.evalL_naive_signedPhaseProd (qs := qs) (p := p))]

theorem evalL_naive_cphaseProd
  (c : ℕ) (p : ℝ) (x z : ExtReg) (ψ : qs.State) :
  LowerGateClass.evalL (qs := qs) (LowGate.Naive_CSignedPhaseProd c p x z) ψ
    =
  qs.eval (Gate.CSignedPhaseProd c p x z) ψ := by
  simp[(LowerGateClass.evalL_naive_csignedPhaseProd (qs := qs) (c := c) (p := p))]

end LowerGateClass

/-! =========================================================
    Section 3: Basic simplification lemmas for lowering
========================================================= -/

namespace LowGate

variable {Basis : Type u}
variable [RegEncoding Basis]
variable [ExtRegEncoding Basis]
variable [ExtRegSplitSemantics Basis]

variable (k : ℕ) (hk : 1 < k)

@[simp] lemma lowerGate_id (ops : Prog k) :
    lowerGate (Basis := Basis) k hk ops Gate.id = LowGate.id := rfl

@[simp] lemma lowerGate_seq (U V : Gate) (ops : Prog k) :
    lowerGate (Basis := Basis) k hk ops (U ;; V)
      =
    (lowerGate (Basis := Basis) k hk ops U) ;;
    (lowerGate (Basis := Basis) k hk ops V) := by
  simp [lowerGate]

@[simp] lemma lowerGate_adj (U : Gate) (ops : Prog k) :
    lowerGate (Basis := Basis) k hk ops (†U)
      =
    †(lowerGate (Basis := Basis) k hk ops U) := rfl

@[simp] lemma lowerGate_QFT (r : Reg) (ops : Prog k) :
    lowerGate (Basis := Basis) k hk ops (Gate.QFT r)
      =
    lowerQFT (Basis := Basis) k hk r ops := rfl

end LowGate

/-! =========================================================
    Section 4: Lowerable phase-gate fragment
========================================================= -/

/-- Gates that can appear during recursive phase-product lowering. -/
inductive LowerablePhaseGate : Gate → Prop where
  | id :
      LowerablePhaseGate Gate.id

  | seq :
      ∀ (U V : Gate),
        LowerablePhaseGate U →
        LowerablePhaseGate V →
        LowerablePhaseGate (Gate.seq U V)

  | H :
      ∀ (q : ℕ),
        LowerablePhaseGate (Gate.H q)

  | X :
      ∀ (q : ℕ),
        LowerablePhaseGate (Gate.X q)

  | Prim :
      ∀ (s : String) (qs : List ℕ),
        LowerablePhaseGate (Gate.Prim s qs)

  | ShiftL :
      ∀ (r : ExtReg) (n : ℕ),
        LowerablePhaseGate (Gate.ShiftL r n)

  | ShiftR :
      ∀ (r : ExtReg) (n : ℕ),
        LowerablePhaseGate (Gate.ShiftR r n)

  | Negate :
      ∀ (r : ExtReg),
        LowerablePhaseGate (Gate.Negate r)

  | AddScaled :
      ∀ (dst src : ExtReg) (negSrc : Bool) (sh : ℕ),
        LowerablePhaseGate (Gate.AddScaled dst src negSrc sh)

  | SignedPhaseProd :
      ∀ (phi : ℝ) (x z : ExtReg),
        LowerablePhaseGate (Gate.SignedPhaseProd phi x z)

  | CSignedPhaseProd :
      ∀ (ctrl : ℕ) (phi : ℝ) (x z : ExtReg),
        LowerablePhaseGate (Gate.CSignedPhaseProd ctrl phi x z)

  | zeroExtend :
      ∀ (r : ExtReg) (n : ℕ),
        LowerablePhaseGate (Gate.zeroExtend r n)

  | signExtend :
      ∀ (r : ExtReg) (n : ℕ),
        LowerablePhaseGate (Gate.signExtend r n)

  | zeroDealloc :
      ∀ (r : ExtReg) (n : ℕ),
        LowerablePhaseGate (Gate.zeroDealloc r n)

  | signDealloc :
      ∀ (r : ExtReg) (n : ℕ),
        LowerablePhaseGate (Gate.signDealloc r n)

namespace LowerablePhaseGate

@[simp] theorem not_adj (U : Gate) : ¬ LowerablePhaseGate (Gate.adj U) := by
  intro h
  cases h

@[simp] theorem not_QFT (r : Reg) : ¬ LowerablePhaseGate (Gate.QFT r) := by
  intro h
  cases h

@[simp] theorem lowerable_PhaseProd (p : ℝ) (x z : Reg) :
    LowerablePhaseGate (Gate.PhaseProd p x z) := by
  unfold Gate.PhaseProd
  refine LowerablePhaseGate.seq _ _ ?_ ?_
  · exact LowerablePhaseGate.zeroExtend (ExtReg.ofReg x) 1
  · refine LowerablePhaseGate.seq _ _ ?_ ?_
    · exact LowerablePhaseGate.zeroExtend (ExtReg.ofReg z) 1
    · refine LowerablePhaseGate.seq _ _ ?_ ?_
      · exact
          LowerablePhaseGate.SignedPhaseProd
            p (Gate.unsignedView x) (Gate.unsignedView z)
      · refine LowerablePhaseGate.seq _ _ ?_ ?_
        · exact LowerablePhaseGate.zeroDealloc (ExtReg.ofReg z) 1
        · exact LowerablePhaseGate.zeroDealloc (ExtReg.ofReg x) 1

end LowerablePhaseGate

/-! =========================================================
    Section 5: Lowerability of compiled signed op lists
========================================================= -/

lemma lowerable_allocChunkGate
  {k : ℕ} (i : Fin k) (src dst : ExtReg) :
  LowerablePhaseGate (allocChunkGate i src dst) := by
  unfold allocChunkGate
  simp
  split_ifs <;> simp [LowerablePhaseGate.zeroExtend,LowerablePhaseGate.id,LowerablePhaseGate.signExtend]

lemma lowerable_deallocChunkGate
  {k : ℕ} (i : Fin k) (src dst : ExtReg) :
  LowerablePhaseGate (deallocChunkGate i src dst) := by
  unfold deallocChunkGate
  simp
  split_ifs <;> simp [LowerablePhaseGate.id,
    LowerablePhaseGate.zeroDealloc, LowerablePhaseGate.signDealloc]

lemma lowerable_compileSignedAllocationsAux
  {k : ℕ} (src dst : LayoutState k) :
  ∀ (n : ℕ) (hn : n ≤ k),
    LowerablePhaseGate (compileSignedAllocationsAux src dst n hn) := by
  intro n hn
  induction n with
  | zero =>
      simp [compileSignedAllocationsAux, LowerablePhaseGate.id]
  | succ n ih =>
      rw [compileSignedAllocationsAux_succ (src := src) (dst := dst) (n := n) (hn := hn)]
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      have htail :
          LowerablePhaseGate (compileSignedAllocationsAux src dst n hk') :=
        ih hk'
      have hx :
          LowerablePhaseGate (allocChunkGate i (src.xslot i) (dst.xslot i)) :=
        lowerable_allocChunkGate i (src.xslot i) (dst.xslot i)
      have hz :
          LowerablePhaseGate (allocChunkGate i (src.zslot i) (dst.zslot i)) :=
        lowerable_allocChunkGate i (src.zslot i) (dst.zslot i)
      have hseq :
          LowerablePhaseGate
            (compileSignedAllocationsAux src dst n hk' ;;
              allocChunkGate i (src.xslot i) (dst.xslot i) ;;
              allocChunkGate i (src.zslot i) (dst.zslot i)) :=
        LowerablePhaseGate.seq _ _
          htail
          (LowerablePhaseGate.seq _ _ hx hz)
      simpa [hk', i] using hseq

lemma lowerable_compileSignedAllocations
  (k : ℕ) (src dst : LayoutState k) :
  LowerablePhaseGate (compileSignedAllocations k src dst) := by
  unfold compileSignedAllocations
  simpa using lowerable_compileSignedAllocationsAux (src := src) (dst := dst) k le_rfl

lemma lowerable_compileSignedDeallocationsAux
  {k : ℕ} (src dst : LayoutState k) :
  ∀ (n : ℕ) (hn : n ≤ k),
    LowerablePhaseGate (compileSignedDeallocationsAux src dst n hn) := by
  intro n hn
  induction n with
  | zero =>
      simp [compileSignedDeallocationsAux, LowerablePhaseGate.id]
  | succ n ih =>
      rw [compileSignedDeallocationsAux_succ (src := src) (dst := dst) (n := n) (hn := hn)]
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      have hz :
          LowerablePhaseGate (deallocChunkGate i (src.zslot i) (dst.zslot i)) :=
        lowerable_deallocChunkGate i (src.zslot i) (dst.zslot i)
      have hx :
          LowerablePhaseGate (deallocChunkGate i (src.xslot i) (dst.xslot i)) :=
        lowerable_deallocChunkGate i (src.xslot i) (dst.xslot i)
      have htail :
          LowerablePhaseGate (compileSignedDeallocationsAux src dst n hk') :=
        ih hk'
      have hseq :
          LowerablePhaseGate
            (deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
              deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
              compileSignedDeallocationsAux src dst n hk') :=
        LowerablePhaseGate.seq _ _
          hz
          (LowerablePhaseGate.seq _ _ hx htail)
      simpa [hk', i] using hseq

lemma lowerable_compileSignedDeallocations
  (k : ℕ) (src dst : LayoutState k) :
  LowerablePhaseGate (compileSignedDeallocations k src dst) := by
  unfold compileSignedDeallocations
  simpa using lowerable_compileSignedDeallocationsAux (src := src) (dst := dst) k le_rfl

lemma lowerable_compileAnnotatedOpsToSignedGateAux
  (k : ℕ) (hk : 1 < k) (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k) (ops : List (AnnotatedOp k)) :
  LowerablePhaseGate (compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st ops) := by
  induction ops generalizing st with
  | nil =>
      simp [compileAnnotatedOpsToSignedGateAux, LowerablePhaseGate.id]
  | cons a rest ih =>
      rcases a with ⟨op, term?⟩
      cases op <;>
        cases term? <;>
        simp [compileAnnotatedOpsToSignedGateAux, ih,
          LowerablePhaseGate.seq,
          LowerablePhaseGate.ShiftL,
          LowerablePhaseGate.ShiftR,
          LowerablePhaseGate.Negate,
          LowerablePhaseGate.AddScaled,
          LowerablePhaseGate.SignedPhaseProd]

@[simp] lemma lowerGate_PP
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (p : ℝ) (x z : Reg) (ops : Prog k) :
    lowerGate (Basis := Basis) k hk ops (Gate.PhaseProd p x z)
      =
    lowerPhaseProd (Basis := Basis) k hk p x z ops := by
  simp [lowerGate, lowerPhaseProd, lowerSignedPhaseProd, lowerGateRec, Gate.PhaseProd]

@[simp] lemma lowerGate_SPP
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (p : ℝ) (x z : ExtReg) (ops : Prog k) :
    lowerGate (Basis := Basis) k hk ops (Gate.SignedPhaseProd p x z)
      =
    lowerSignedPhaseProd (Basis := Basis) k hk p x z ops := by
  simp [lowerGate, lowerSignedPhaseProd]

lemma lowerable_compileOpsToSignedGate
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (k : ℕ) (hk : 1 < k) (phi : ℝ)
  (x z : ExtReg)
  (coeff : Fin (q k) → ℚ)
  (ops : List (valid_ops k)) :
  LowerablePhaseGate
    (compileOpsToSignedGate (Basis := Basis) k hk phi x z coeff ops) := by
  dsimp [compileOpsToSignedGate]
  refine LowerablePhaseGate.seq _ _ ?_ ?_
  · exact
      lowerable_compileSignedAllocations
        k
        (initSignedLayoutState (Basis := Basis) x z k)
        (targetSignedLayoutState
          (Basis := Basis) x z k (scanNeededWidths x z ops))
  · refine LowerablePhaseGate.seq _ _ ?_ ?_
    · exact
        lowerable_compileAnnotatedOpsToSignedGateAux
          k hk phi coeff
          (targetSignedLayoutState
            (Basis := Basis) x z k (scanNeededWidths x z ops))
          (annotatePhaseTermsAux k 0 ops)
    · exact
        lowerable_compileSignedDeallocations
          k
          (initSignedLayoutState (Basis := Basis) x z k)
          (targetSignedLayoutState
            (Basis := Basis) x z k (scanNeededWidths x z ops))

lemma lowerable_controlPhaseLeaves
  (ctrl : ℕ) {U : Gate}
  (hU : LowerablePhaseGate U) :
  LowerablePhaseGate (controlPhaseLeaves ctrl U) := by
  induction hU with
  | id =>
      simp [controlPhaseLeaves, LowerablePhaseGate.id]
  | seq U V _ _ ihU ihV =>
      simp [controlPhaseLeaves, LowerablePhaseGate.seq, ihU, ihV]
  | H q =>
      simp [controlPhaseLeaves, LowerablePhaseGate.H]
  | X q =>
      simp [controlPhaseLeaves, LowerablePhaseGate.X]
  | Prim s args =>
      simp [controlPhaseLeaves, LowerablePhaseGate.Prim]
  | ShiftL r n =>
      simp [controlPhaseLeaves, LowerablePhaseGate.ShiftL]
  | ShiftR r n =>
      simp [controlPhaseLeaves, LowerablePhaseGate.ShiftR]
  | Negate r =>
      simp [controlPhaseLeaves, LowerablePhaseGate.Negate]
  | AddScaled dst src negSrc sh =>
      simp [controlPhaseLeaves, LowerablePhaseGate.AddScaled]
  | SignedPhaseProd phi x z =>
      simp [controlPhaseLeaves, LowerablePhaseGate.CSignedPhaseProd]
  | CSignedPhaseProd ctrl' phi x z =>
      simp [controlPhaseLeaves, LowerablePhaseGate.CSignedPhaseProd]
  | zeroExtend r n =>
      simp [controlPhaseLeaves, LowerablePhaseGate.zeroExtend]
  | signExtend r n =>
      simp [controlPhaseLeaves, LowerablePhaseGate.signExtend]
  | zeroDealloc r n =>
      simp [controlPhaseLeaves, LowerablePhaseGate.zeroDealloc]
  | signDealloc r n =>
      simp [controlPhaseLeaves, LowerablePhaseGate.signDealloc]

lemma lowerable_compileOpsToCSignedGate
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (phi : ℝ)
  (x z : ExtReg)
  (coeff : Fin (q k) → ℚ)
  (ops : List (valid_ops k)) :
  LowerablePhaseGate
    (compileOpsToCSignedGate (Basis := Basis) k hk ctrl phi x z coeff ops) := by
  unfold compileOpsToCSignedGate
  exact
    lowerable_controlPhaseLeaves ctrl
      (lowerable_compileOpsToSignedGate
        (Basis := Basis) k hk phi x z coeff ops)

/-! =========================================================
    Section 6: Signed phase-product side condition
========================================================= -/

/-- Extra recursive side-condition needed only for signed phase-product nodes. -/
def SignedPhaseProdOK : Gate → Prop
  | Gate.id => True
  | Gate.seq U V => SignedPhaseProdOK U ∧ SignedPhaseProdOK V
  | Gate.adj _ => False
  | Gate.H _ => True
  | Gate.X _ => True
  | Gate.Prim _ _ => True
  | Gate.ShiftL _ _ => True
  | Gate.ShiftR _ _ => True
  | Gate.Negate _ => True
  | Gate.AddScaled _ _ _ _ => True
  | Gate.QFT _ => False
  | Gate.SignedPhaseProd _ x z =>
      Disjoint x.base z.base
  | Gate.CSignedPhaseProd _ _ x z =>
      Disjoint x.base z.base
  | Gate.zeroExtend _ _ => True
  | Gate.signExtend _ _ => True
  | Gate.zeroDealloc _ _ => True
  | Gate.signDealloc _ _ => True
  | Gate.RadixReverse _ _ => True

lemma signedPhaseProdOK_allocChunkGate
  {k : ℕ} (i : Fin k) (src dst : ExtReg) :
  SignedPhaseProdOK (allocChunkGate i src dst) := by
  unfold allocChunkGate
  simp
  split_ifs <;> simp [SignedPhaseProdOK]

lemma signedPhaseProdOK_deallocChunkGate
  {k : ℕ} (i : Fin k) (src dst : ExtReg) :
  SignedPhaseProdOK (deallocChunkGate i src dst) := by
  unfold deallocChunkGate
  simp
  split_ifs <;> simp [SignedPhaseProdOK]

lemma signedPhaseProdOK_compileSignedAllocationsAux
  {k : ℕ} (src dst : LayoutState k) :
  ∀ (n : ℕ) (hn : n ≤ k),
    SignedPhaseProdOK (compileSignedAllocationsAux src dst n hn) := by
  intro n hn
  induction n with
  | zero =>
      simp [compileSignedAllocationsAux, SignedPhaseProdOK]
  | succ n ih =>
      rw [compileSignedAllocationsAux_succ (src := src) (dst := dst) (n := n) (hn := hn)]
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      have htail :
          SignedPhaseProdOK (compileSignedAllocationsAux src dst n hk') :=
        ih hk'
      have hx :
          SignedPhaseProdOK (allocChunkGate i (src.xslot i) (dst.xslot i)) :=
        signedPhaseProdOK_allocChunkGate i (src.xslot i) (dst.xslot i)
      have hz :
          SignedPhaseProdOK (allocChunkGate i (src.zslot i) (dst.zslot i)) :=
        signedPhaseProdOK_allocChunkGate i (src.zslot i) (dst.zslot i)
      simpa [SignedPhaseProdOK, hk', i] using And.intro htail (And.intro hx hz)

lemma signedPhaseProdOK_compileSignedAllocations
  (k : ℕ) (src dst : LayoutState k) :
  SignedPhaseProdOK (compileSignedAllocations k src dst) := by
  unfold compileSignedAllocations
  simpa using signedPhaseProdOK_compileSignedAllocationsAux (src := src) (dst := dst) k le_rfl

lemma signedPhaseProdOK_compileSignedDeallocationsAux
  {k : ℕ} (src dst : LayoutState k) :
  ∀ (n : ℕ) (hn : n ≤ k),
    SignedPhaseProdOK (compileSignedDeallocationsAux src dst n hn) := by
  intro n hn
  induction n with
  | zero =>
      simp [compileSignedDeallocationsAux, SignedPhaseProdOK]
  | succ n ih =>
      rw [compileSignedDeallocationsAux_succ (src := src) (dst := dst) (n := n) (hn := hn)]
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      have htail :
          SignedPhaseProdOK (compileSignedDeallocationsAux src dst n hk') :=
        ih hk'
      have hz :
          SignedPhaseProdOK (deallocChunkGate i (src.zslot i) (dst.zslot i)) :=
        signedPhaseProdOK_deallocChunkGate i (src.zslot i) (dst.zslot i)
      have hx :
          SignedPhaseProdOK (deallocChunkGate i (src.xslot i) (dst.xslot i)) :=
        signedPhaseProdOK_deallocChunkGate i (src.xslot i) (dst.xslot i)
      simpa [SignedPhaseProdOK, hk', i] using And.intro hz (And.intro hx htail)

lemma signedPhaseProdOK_compileSignedDeallocations
  (k : ℕ) (src dst : LayoutState k) :
  SignedPhaseProdOK (compileSignedDeallocations k src dst) := by
  unfold compileSignedDeallocations
  simpa using signedPhaseProdOK_compileSignedDeallocationsAux (src := src) (dst := dst) k le_rfl

lemma signedPhaseProdOK_compileAnnotatedOpsToSignedGateAux
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (ops : List (AnnotatedOp k))
  (hdisj : ∀ i : Fin k, Disjoint (st.xslot i).base (st.zslot i).base) :
  SignedPhaseProdOK (compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st ops) := by
  induction ops with
  | nil =>
      simp [compileAnnotatedOpsToSignedGateAux, SignedPhaseProdOK]
  | cons a ops ih =>
      cases a with
      | mk op term? =>
        cases op with
        | shiftL i n =>
            simp [compileAnnotatedOpsToSignedGateAux, SignedPhaseProdOK, ih]
        | shiftR i n =>
            simp [compileAnnotatedOpsToSignedGateAux, SignedPhaseProdOK, ih]
        | negate i =>
            simp [compileAnnotatedOpsToSignedGateAux, SignedPhaseProdOK, ih]
        | addScaled dst src negsrc sh =>
            simp [compileAnnotatedOpsToSignedGateAux, SignedPhaseProdOK, ih]
        | phaseProduct i =>
            cases term? with
            | none =>
                simp [compileAnnotatedOpsToSignedGateAux, ih]
            | some l =>
                simp [compileAnnotatedOpsToSignedGateAux, SignedPhaseProdOK, ih, hdisj i]

lemma signedPhaseProdOK_compileOpsToSignedGate
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ) (x z : ExtReg)
  (coeff : Fin (q k) → ℚ)
  (ops : Prog k)
  (hxz : Disjoint x.base z.base) :
  SignedPhaseProdOK
    (compileOpsToSignedGate (Basis := Basis) k hk phi x z coeff ops) := by
  unfold compileOpsToSignedGate

  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := Basis) x z k
  let stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := Basis) x z k need
  let annOps : List (AnnotatedOp k) := annotatePhaseTermsAux k 0 ops

  have hAlloc : SignedPhaseProdOK (compileSignedAllocations k stInit stFinal) := by
    exact signedPhaseProdOK_compileSignedAllocations k stInit stFinal

  have hDealloc : SignedPhaseProdOK (compileSignedDeallocations k stInit stFinal) := by
    exact signedPhaseProdOK_compileSignedDeallocations k stInit stFinal

  have hdisj :
      ∀ i : Fin k, Disjoint (stFinal.xslot i).base (stFinal.zslot i).base := by
    intro i
    have hsrc :
        Disjoint
          ((initSignedLayoutState (Basis := Basis) x z k).xslot i).base
          ((initSignedLayoutState (Basis := Basis) x z k).zslot i).base := by
      simpa [initSignedLayoutState] using
        splitExtReg_disjoint_of_disjoint
          (Basis := Basis)
          x z k (phaseLimbWidth x z k) i i hxz
    simpa [stFinal, targetSignedLayoutState, widenExtRegTo] using hsrc

  have hBody :
      SignedPhaseProdOK
        (compileAnnotatedOpsToSignedGateAux
          k hk phi coeff stFinal annOps) := by
    exact signedPhaseProdOK_compileAnnotatedOpsToSignedGateAux
      k hk phi coeff stFinal annOps hdisj

  simpa [need, stInit, stFinal, annOps, SignedPhaseProdOK] using
    And.intro hAlloc (And.intro hBody hDealloc)

lemma signedPhaseProdOK_controlPhaseLeaves
  (ctrl : ℕ) :
  ∀ U : Gate,
    SignedPhaseProdOK U →
    SignedPhaseProdOK (controlPhaseLeaves ctrl U)
  | Gate.id, hOK => hOK
  | Gate.seq U V, hOK => by
      rcases hOK with ⟨hU, hV⟩
      exact
        And.intro
          (signedPhaseProdOK_controlPhaseLeaves ctrl U hU)
          (signedPhaseProdOK_controlPhaseLeaves ctrl V hV)
  | Gate.adj U, hOK => False.elim hOK
  | Gate.H q, hOK => hOK
  | Gate.X q, hOK => hOK
  | Gate.Prim tag args, hOK => hOK
  | Gate.ShiftL r n, hOK => hOK
  | Gate.ShiftR r n, hOK => hOK
  | Gate.Negate r, hOK => hOK
  | Gate.AddScaled dst src negSrc sh, hOK => hOK
  | Gate.QFT r, hOK => False.elim hOK
  | Gate.SignedPhaseProd phi x z, hOK => hOK
  | Gate.CSignedPhaseProd ctrl' phi x z, hOK => hOK
  | Gate.zeroExtend r n, hOK => hOK
  | Gate.signExtend r n, hOK => hOK
  | Gate.zeroDealloc r n, hOK => hOK
  | Gate.signDealloc r n, hOK => hOK
  | Gate.RadixReverse r m, hOK => hOK

lemma signedPhaseProdOK_compileOpsToCSignedGate
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (k : ℕ) (hk : 1 < k)
  (ctrl : ℕ) (phi : ℝ) (x z : ExtReg)
  (coeff : Fin (q k) → ℚ)
  (ops : Prog k)
  (hxz : Disjoint x.base z.base) :
  SignedPhaseProdOK
    (compileOpsToCSignedGate (Basis := Basis) k hk ctrl phi x z coeff ops) := by
  unfold compileOpsToCSignedGate
  exact
    signedPhaseProdOK_controlPhaseLeaves ctrl
      (compileOpsToSignedGate (Basis := Basis) k hk phi x z coeff ops)
      (signedPhaseProdOK_compileOpsToSignedGate
        (Basis := Basis) k hk phi x z coeff ops hxz)

/-- Unsigned PhaseProd is SignedPhaseProdOK when its registers are disjoint and well formed. -/
lemma signedPhaseProdOK_PhaseProd
  (p : ℝ) (x z : Reg)
  (hxz : Disjoint x z) :
  SignedPhaseProdOK (Gate.PhaseProd p x z) := by
  unfold Gate.PhaseProd
  simp [SignedPhaseProdOK, Gate.unsignedView, ExtReg.ofReg, hxz]

/-! =========================================================
    Section 7: Strong correctness theorem for recursive lowering
========================================================= -/

lemma evalL_lowerGateRec_strong_of_compile
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [LowerGateClass qs]
  [GateSemanticsFacts qs] :
  ∀ n,
    ∀ (k : ℕ) (hk : 1 < k)
      (pts : List Point) (hpts : pts.length = q k)
      (_hInterp : GoodToomCookPoints k pts hpts)
      (ops : Prog k)
      (_hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
      (_run_ops_start_state : run? ops State.start_state = some State.start_state)
      (U : Gate) (_hU : LowerablePhaseGate U) (_hOK : SignedPhaseProdOK U) (ψ : qs.State),
      LowerGateClass.evalL
          (lowerGateRec (Basis := qs.Basis) n k hk pts hpts ops U) ψ
        =
      qs.eval U ψ := by
  intro n
  induction' n using Nat.strong_induction_on with n IH
  intro k hk pts hpts hInterp ops hC run_ops_start_state U hU hOK ψ
  induction hU generalizing ψ with
  | id =>
      simp [lowerGateRec, LowerGateClass.evalL_id, qs.eval_id]

  | seq U V hU hV ihU ihV =>
      rcases hOK with ⟨hOKU, hOKV⟩
      simp [lowerGateRec, LowerGateClass.evalL_seq, qs.eval_seq,
        ihU hOKU, ihV hOKV]

  | H =>
      simp [lowerGateRec, LowerGateClass.evalL_H]

  | X =>
      simp [lowerGateRec, LowerGateClass.evalL_X]

  | Prim =>
      simp [lowerGateRec, LowerGateClass.evalL_Prim]

  | ShiftL =>
      simp [lowerGateRec, LowerGateClass.evalL_shiftL]

  | ShiftR =>
      simp [lowerGateRec, LowerGateClass.evalL_shiftR]

  | Negate =>
      simp [lowerGateRec, LowerGateClass.evalL_negate]

  | AddScaled =>
      simp [lowerGateRec, LowerGateClass.evalL_addScaled]

  | SignedPhaseProd phi x z =>
      have hxz : Disjoint x.base z.base := by
        simp [SignedPhaseProdOK] at hOK
        simp[hOK]

      unfold lowerGateRec
      dsimp

      let Wrec : ℕ := nextSignedWidth x z ops

      by_cases hrec : Wrec < n
      · simp [Wrec, hrec]

        let Wphase : ℕ := phaseLimbWidth x z k
        let coeff : Fin (q k) → ℚ :=
          phaseCoeffFromPtsWidth k Wphase pts hpts
        let g : Gate :=
          compileOpsToSignedGate
            (Basis := qs.Basis) k hk phi x z coeff ops

        have hg : LowerablePhaseGate g := by
          dsimp [g, coeff]
          exact
            lowerable_compileOpsToSignedGate
              (Basis := qs.Basis)
              k hk phi x z coeff ops

        have hgOK : SignedPhaseProdOK g := by
          dsimp [g, coeff]
          exact
            signedPhaseProdOK_compileOpsToSignedGate
              (Basis := qs.Basis)
              k hk phi x z coeff ops hxz

        have hIH :
            LowerGateClass.evalL
                (lowerGateRec (Basis := qs.Basis) Wrec k hk pts hpts ops g) ψ
              =
            qs.eval g ψ := by
          exact
            IH Wrec hrec
              k hk pts hpts hInterp ops
              hC run_ops_start_state
              g hg hgOK ψ

        rw [hIH]

        simpa [g, coeff, Wphase] using
          (eval_compileOpsToSignedGate_correct
            (qs := qs)
            (k := k) (hk := hk)
            (phi := phi)
            (x := x) (z := z)
            (hxz := hxz)
            (pts := pts) (hpts := hpts)
            (hInterp := hInterp)
            (ψ := ψ)
            (ops := ops)
            (hC := hC)
            (run_ops_start_state := run_ops_start_state))

      ·
        simp [Wrec, hrec, LowerGateClass.evalL_naive_phaseProd]

  | CSignedPhaseProd ctrl phi x z =>
      have hxz : Disjoint x.base z.base := by
        simpa [SignedPhaseProdOK] using hOK

      unfold lowerGateRec
      dsimp

      let Wrec : ℕ := nextSignedWidth x z ops

      by_cases hctrl : ExtReg.CtrlDisjoint ctrl x z
      · by_cases hrec : Wrec < n
        · simp [Wrec, hctrl, hrec]

          let Wphase : ℕ := phaseLimbWidth x z k
          let coeff : Fin (q k) → ℚ :=
            phaseCoeffFromPtsWidth k Wphase pts hpts
          let g : Gate :=
            compileOpsToCSignedGate
              (Basis := qs.Basis) k hk ctrl phi x z coeff ops

          have hg : LowerablePhaseGate g := by
            dsimp [g, coeff]
            exact
              lowerable_compileOpsToCSignedGate
                (Basis := qs.Basis)
                k hk ctrl phi x z coeff ops

          have hgOK : SignedPhaseProdOK g := by
            dsimp [g, coeff]
            exact
              signedPhaseProdOK_compileOpsToCSignedGate
                (Basis := qs.Basis)
                k hk ctrl phi x z coeff ops hxz

          have hIH :
              LowerGateClass.evalL
                  (lowerGateRec (Basis := qs.Basis) Wrec k hk pts hpts ops g) ψ
                =
              qs.eval g ψ := by
            exact
              IH Wrec hrec
                k hk pts hpts hInterp ops
                hC run_ops_start_state
                g hg hgOK ψ

          rw [hIH]

          simpa [g, coeff, Wphase] using
            (eval_compileOpsToCSignedGate_correct
              (qs := qs)
              (k := k) (hk := hk)
              (ctrl := ctrl) (phi := phi)
              (x := x) (z := z)
              (hxz := hxz)
              (hctrl := hctrl)
              (pts := pts) (hpts := hpts)
              (hInterp := hInterp)
              (ops := ops)
              (hC := hC)
              (hRun := run_ops_start_state)
              (ψ := ψ))

        ·
          simp [Wrec, hctrl, hrec, LowerGateClass.evalL_naive_cphaseProd]

      ·
        simp [hctrl, LowerGateClass.evalL_naive_cphaseProd]

  | zeroExtend r m =>
      simp [lowerGateRec, LowerGateClass.evalL_zeroExtend]

  | signExtend r m =>
      simp [lowerGateRec, LowerGateClass.evalL_signExtend]

  | zeroDealloc r m =>
      simp [lowerGateRec, LowerGateClass.evalL_zeroDealloc]

  | signDealloc r m =>
      simp [lowerGateRec, LowerGateClass.evalL_signDealloc]

lemma evalL_lowerGateRec_strong
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [LowerGateClass qs]
  [GateSemanticsFacts qs] :
  ∀ n,
    ∀ (k : ℕ) (hk : 1 < k)
      (pts : List Point) (hpts : pts.length = q k)
      (_hInterp : GoodToomCookPoints k pts hpts)
      (ops : Prog k)
      (_hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
      (_run_ops_start_state : run? ops State.start_state = some State.start_state)
      (U : Gate) (_hU : LowerablePhaseGate U) (_hOK : SignedPhaseProdOK U) (ψ : qs.State),
      LowerGateClass.evalL
          (lowerGateRec (Basis := qs.Basis) n k hk pts hpts ops U) ψ
        =
      qs.eval U ψ := by
  intro n k hk pts hpts hInterp ops hC run_ops_start_state U hU hOK ψ
  exact
    evalL_lowerGateRec_strong_of_compile
      (qs := qs)
      n k hk pts hpts hInterp ops
      hC run_ops_start_state
      U hU hOK ψ


/-! =========================================================
    Section 8: Final correctness lemmas for lowered phase products
========================================================= -/

lemma evalL_lowerSignedPhaseProd
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [LowerGateClass qs]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k) (p : ℝ) (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (ψ : qs.State) (ops : Prog k)
  (hC : ProgConsumesPtsSafe
    (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  LowerGateClass.evalL
      (lowerSignedPhaseProd (Basis := qs.Basis) k hk p x z ops) ψ
    =
  qs.eval (Gate.SignedPhaseProd p x z) ψ := by
  unfold lowerSignedPhaseProd

  let pts : List Point := genInterpolationPoints k
  have hInterp : GoodToomCookPoints k pts (by simp[pts,genInterpolationPoints,q]) := by
    simpa [pts] using genInterpolationPoints_good k
  have hpts : pts.length = q k := by
    simp [pts, genInterpolationPoints, q]

  let Wrec : ℕ := nextSignedWidth x z ops

  by_cases hrec : Wrec < phaseInputSize x z
  · simp [Wrec, hrec]

    let Wphase : ℕ := phaseLimbWidth x z k
    let coeff : Fin (q k) → ℚ :=
      phaseCoeffFromPtsWidth k Wphase pts hpts
    let g : Gate :=
      compileOpsToSignedGate
        (Basis := qs.Basis) k hk p x z coeff ops

    have hg : LowerablePhaseGate g := by
      dsimp [g, coeff]
      exact
        lowerable_compileOpsToSignedGate
          (Basis := qs.Basis)
          k hk p x z coeff ops

    have hgOK : SignedPhaseProdOK g := by
      dsimp [g, coeff]
      exact
        signedPhaseProdOK_compileOpsToSignedGate
          (Basis := qs.Basis)
          k hk p x z coeff ops hxz

    have hInterpPts : GoodToomCookPoints k pts hpts := by
      simpa [pts] using hInterp

    have h1 :
        LowerGateClass.evalL
            (lowerGateRec (Basis := qs.Basis) Wrec k hk pts hpts ops g) ψ
          =
        qs.eval g ψ := by
      exact
        evalL_lowerGateRec_strong
          (qs := qs)
          Wrec k hk pts hpts hInterpPts ops
          (by simpa [pts] using hC)
          run_ops_start_state
          g hg hgOK ψ

    rw [h1]

    simpa [g, coeff, Wphase] using
      (eval_compileOpsToSignedGate_correct
        (qs := qs)
        (k := k) (hk := hk)
        (phi := p)
        (x := x) (z := z)
        (hxz := hxz)
        (pts := pts) (hpts := hpts)
        (hInterp := hInterpPts)
        (ψ := ψ)
        (ops := ops)
        (hC := by simpa [pts] using hC)
        (run_ops_start_state := run_ops_start_state))

  ·
    simpa [pts, hpts, Wrec, hrec] using
      (LowerGateClass.evalL_naive_phaseProd
        (qs := qs) (p := p) (x := x) (z := z) (ψ := ψ))

lemma evalL_lowerCSignedPhaseProd
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [LowerGateClass qs]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (p : ℝ) (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (ψ : qs.State) (ops : Prog k)
  (hC : ProgConsumesPtsSafe
    (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  LowerGateClass.evalL
      (lowerCSignedPhaseProd (Basis := qs.Basis) k hk ctrl p x z ops) ψ
    =
  qs.eval (Gate.CSignedPhaseProd ctrl p x z) ψ := by
  unfold lowerCSignedPhaseProd

  let pts : List Point := genInterpolationPoints k
  have hpts : pts.length = q k := by
    simp [pts, genInterpolationPoints, q]

  let Wrec : ℕ := nextSignedWidth x z ops

  by_cases hctrl' : ExtReg.CtrlDisjoint ctrl x z
  · by_cases hrec : Wrec < phaseInputSize x z
    · simp [Wrec, hctrl', hrec]

      let Wphase : ℕ := phaseLimbWidth x z k
      let coeff : Fin (q k) → ℚ :=
        phaseCoeffFromPtsWidth k Wphase pts hpts
      let g : Gate :=
        compileOpsToCSignedGate
          (Basis := qs.Basis) k hk ctrl p x z coeff ops

      have hInterpPts : GoodToomCookPoints k pts hpts := by
        simpa [pts] using genInterpolationPoints_good k

      have hg : LowerablePhaseGate g := by
        dsimp [g, coeff]
        exact
          lowerable_compileOpsToCSignedGate
            (Basis := qs.Basis)
            k hk ctrl p x z coeff ops

      have hgOK : SignedPhaseProdOK g := by
        dsimp [g, coeff]
        exact
          signedPhaseProdOK_compileOpsToCSignedGate
            (Basis := qs.Basis)
            k hk ctrl p x z coeff ops hxz

      have h1 :
          LowerGateClass.evalL
              (lowerGateRec (Basis := qs.Basis) Wrec k hk pts hpts ops g) ψ
            =
          qs.eval g ψ := by
        exact
          evalL_lowerGateRec_strong
            (qs := qs)
            Wrec k hk pts hpts hInterpPts ops
            (by simpa [pts] using hC)
            run_ops_start_state
            g hg hgOK ψ

      rw [h1]

      simpa [g, coeff, Wphase] using
        (eval_compileOpsToCSignedGate_correct
          (qs := qs)
          (k := k) (hk := hk)
          (ctrl := ctrl) (phi := p)
          (x := x) (z := z)
          (hxz := hxz)
          (hctrl := hctrl')
          (pts := pts) (hpts := hpts)
          (hInterp := hInterpPts)
          (ops := ops)
          (hC := by simpa [pts] using hC)
          (hRun := run_ops_start_state)
          (ψ := ψ))

    ·
      simpa [pts, hpts, Wrec, hctrl', hrec] using
        (LowerGateClass.evalL_naive_cphaseProd
          (qs := qs) (c := ctrl) (p := p) (x := x) (z := z) (ψ := ψ))

  ·
    simpa [pts, hpts, Wrec, hctrl'] using
      (LowerGateClass.evalL_naive_cphaseProd
        (qs := qs) (c := ctrl) (p := p) (x := x) (z := z) (ψ := ψ))

lemma evalL_lowerPhaseProd
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [LowerGateClass qs]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k) (p : ℝ) (x z : Reg)
  (hxz : Disjoint x z)
  (ψ : qs.State) (ops : Prog k)
  (hC : ProgConsumesPtsSafe
    (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  LowerGateClass.evalL
      (lowerPhaseProd (Basis := qs.Basis) k hk p x z ops) ψ
    =
  qs.eval (Gate.PhaseProd p x z) ψ := by
  unfold lowerPhaseProd

  let pts : List Point := genInterpolationPoints k

  have hpts : pts.length = q k := by
    simp [pts, genInterpolationPoints, q]

  have hInterpPts : GoodToomCookPoints k pts hpts := by
    apply genInterpolationPoints_good
  have hU : LowerablePhaseGate (Gate.PhaseProd p x z) := by
    simp

  have hOK : SignedPhaseProdOK (Gate.PhaseProd p x z) := by
    exact signedPhaseProdOK_PhaseProd p x z hxz

  simpa [pts] using
    (evalL_lowerGateRec_strong
      (qs := qs)
      (n := phaseInputSize (Gate.unsignedView x) (Gate.unsignedView z))
      (k := k) (hk := hk)
      (pts := pts) (hpts := hpts)
      (_hInterp := hInterpPts)
      (ops := ops)
      (_hC := by simpa [pts] using hC)
      (_run_ops_start_state := run_ops_start_state)
      (U := Gate.PhaseProd p x z)
      (_hU := hU)
      (_hOK := hOK)
      (ψ := ψ))

end Shor
