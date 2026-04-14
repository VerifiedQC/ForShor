import FastMultiplication.ShorVerification.LowGate_compilation

namespace Shor
open Gate
open Operations

/-! =========================================================
    Section 15: Lowering helpers
========================================================= -/

/-- Controlled signed phase lowering currently stays at the naive low-level node. -/
def lowerCSignedPhaseProd
  (k : ℕ) (_hk : 1 < k) (ctrl : ℕ) (phi : ℝ) (x z : ExtReg) : LowGate :=
  LowGate.Naive_CSignedPhaseProd ctrl phi x z

/-- Recursively lower a gate into the low-level language using a size cutoff. -/
noncomputable def lowerGateRec
  (initSize : ℕ) (k : ℕ) (hk : 1 < k)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (ops : Prog k)
  :
  Gate → LowGate
  | Gate.id => LowGate.id
  | Gate.seq U V =>
      LowGate.seq
        (lowerGateRec initSize k hk pts hpts ops U)
        (lowerGateRec initSize k hk pts hpts ops V)
  | Gate.adj U =>
      LowGate.adj (lowerGateRec initSize k hk pts hpts ops U)
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
      let W := nextSignedWidth x z ops
      if _hrec : W < initSize then
        let coeff := phaseCoeffFromPtsWidth k W pts hpts
        let g := compileOpsToSignedGate k hk phi x z coeff ops
        lowerGateRec W k hk pts hpts ops g
      else
        LowGate.Naive_SignedPhaseProd phi x z
  | Gate.CSignedPhaseProd ctrl phi x z =>
      lowerCSignedPhaseProd k hk ctrl phi x z
  | Gate.zeroExtend r n =>
      LowGate.zeroExtend r n
  | Gate.signExtend r n =>
      LowGate.signExtend r n
  | Gate.zeroDealloc r n =>
      LowGate.zeroDealloc r n
  | Gate.signDealloc r n =>
      LowGate.signDealloc r n

/-- Alternating integer interpolation points around zero. -/
def alternatingPoint (i : ℕ) : Point :=
  if i % 2 == 0 then
    Point.int (i / 2 : ℤ)
  else
    Point.int (-((i + 1) / 2 : ℤ))

/-- Generate the canonical `2k - 1` interpolation points. -/
def genInterpolationPoints (k : ℕ) : List Point :=
  (List.range (2 * k - 1)).map alternatingPoint



/-- Lower a signed phase product by interpolation-based decomposition. -/
noncomputable def lowerSignedPhaseProd
  (k : ℕ) (hk : 1 < k) (phi : ℝ) (x z : ExtReg) (ops : Prog k) :=
  let pts := genInterpolationPoints k
  let hpts : pts.length = q k := by
    simp [pts, genInterpolationPoints, q]
  let W := nextSignedWidth x z ops
  if _hrec : W < phaseInputSize x z then
    let coeff := phaseCoeffFromPtsWidth k W pts hpts
    let g := compileOpsToSignedGate k hk phi x z coeff ops
    lowerGateRec W k hk pts hpts ops g
  else
    LowGate.Naive_SignedPhaseProd phi x z

/-- Lower an unsigned phase product by interpolation-based decomposition. -/
noncomputable def lowerPhaseProd
  (k : ℕ) (hk : 1 < k) (phi : ℝ) (x z : Reg) (ops : Prog k) :=
  let pts := genInterpolationPoints k
  let hpts : pts.length = q k := by
    simp [pts,genInterpolationPoints, q]
  let op1 := Gate.PhaseProd phi x z
  lowerGateRec
    (phaseInputSize (Gate.unsignedView x) (Gate.unsignedView z))
    k hk pts hpts ops op1

/-- Recursive QFT lowering on a register of known size. -/
noncomputable def lowerQFTAux (k : ℕ) (hk : 1 < k) (ops: Prog k): ℕ → Reg → LowGate
  | 0,   _ => .id
  | 1,   r => .H r.lo
  | n+2, r =>
      let nTot : ℕ := n + 2
      let m : ℕ := nTot / 2
      let left  : Reg := ⟨r.lo, r.lo + m⟩
      let right : Reg := ⟨r.lo + m, r.hi⟩
      (lowerQFTAux k hk ops m left) ;;
      (lowerPhaseProd k hk (qftPhi nTot) left right ops) ;;
      (lowerQFTAux k hk ops (nTot - m) right)

/-- Lower a full QFT gate. -/
noncomputable def lowerQFT (k : ℕ) (hk : 1 < k) (r : Reg) (ops: Prog k): LowGate :=
  lowerQFTAux k hk ops (regSize r) r

/-- Global lowering function from `Gate` to `LowGate`. -/
noncomputable def lowerGate (k : ℕ) (hk : 1 < k) (ops: Prog k): Gate → LowGate
  | .id => .id
  | .seq U V => (lowerGate k hk ops U ) ;; (lowerGate k hk ops V)
  | .adj U => †(lowerGate k hk ops U)
  | .H q => .H q
  | .X q => .X q
  | .QFT r => lowerQFT k hk r ops
  | .SignedPhaseProd p x z =>
      lowerSignedPhaseProd k hk p x z ops
  | .CSignedPhaseProd c p x z =>
      LowGate.Naive_CSignedPhaseProd c p x z
  | .Prim tag args => .Prim tag args
  | .ShiftL r n => .ShiftL r n
  | .ShiftR r n => .ShiftR r n
  | .AddScaled dst src negSrc shift => .AddScaled dst src negSrc shift
  | .Negate r => .Negate r
  | Gate.zeroExtend r n => LowGate.zeroExtend r n
  | Gate.signExtend r n => LowGate.signExtend r n
  | Gate.zeroDealloc r n =>  LowGate.zeroDealloc r n
  | Gate.signDealloc r n => LowGate.signDealloc r n

/-- Semantics of the low-level target language. -/
class LowerGateClass (qs : QSemantics) [RegEncoding qs.Basis] : Type where
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
    ∀ (k : ℕ) (hk : 1 < k) (U : Gate) (ψ : qs.State) (ops: Prog k),
      evalL (†(lowerGate k hk ops U)) ψ = qs.eval (†U) ψ

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


namespace LowerGateClass

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

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
    Section 9: Basic simplification lemmas for lowering
========================================================= -/

namespace LowGate

variable (k : ℕ) (hk : 1 < k)

/-- Simplification rule for lowering the identity gate. -/
@[simp] lemma lowerGate_id (ops: Prog k): lowerGate k hk ops Gate.id = (LowGate.id) := rfl

/-- Simplification rule for lowering sequential composition. -/
@[simp] lemma lowerGate_seq (U V : Gate) (ops: Prog k):
    lowerGate k hk ops (U ;; V) = (lowerGate k hk ops U) ;; (lowerGate k hk ops V) := by
  simp [lowerGate]

/-- Simplification rule for lowering adjoints. -/
@[simp] lemma lowerGate_adj (U : Gate) (ops: Prog k):
    lowerGate k hk ops (†U) = †(lowerGate k hk ops U) := rfl

/-- Simplification rule for lowering QFT. -/
@[simp] lemma lowerGate_QFT (r : Reg) (ops: Prog k):
    lowerGate k hk ops (Gate.QFT r) = lowerQFT k hk r  ops:= rfl

-- /-- Simplification rule for lowering phase products. -/
-- @[simp] lemma lowerGate_PP (p : ℝ) (x z : Reg) (ops: Prog k):
--     lowerGate k hk ops (Gate.PhaseProd p x z) = lowerPhaseProd k hk p x z ops := by
--   simp [Gate.PhaseProd, lowerGate, lowerPhaseProd]

-- /-- Simplification rule for lowering signed phase products on sign-extended inputs. -/
-- @[simp] lemma lowerGate_SPP (p : ℝ) (x z : Reg) (ops : Prog k) :
--     lowerGate k hk ops
--       (Gate.SignedPhaseProd p
--         (ExtReg.signExtend (ExtReg.ofReg x))
--         (ExtReg.signExtend (ExtReg.ofReg z)))
--       =
--     lowerSignedPhaseProd k hk p x z ops := by
--   simp [lowerGate, lowerSignedPhaseProd]

-- /-- Simplification rule for lowering controlled phase products. -/
-- @[simp] lemma lowerGate_CPP (c : ℕ) (p : ℝ) (x z : Reg) (ops: Prog k):
--     lowerGate k hk ops (Gate.CPhaseProd c p x z) = lowerCPhaseProd k hk c p x z := by
--   simp [Gate.CPhaseProd, lowerGate, lowerCPhaseProd, lowerCSignedPhaseProd]

-- @[simp] lemma lowerGate_CSPP (c : ℕ) (p : ℝ) (x z : ExtReg) (ops : Prog k) :
--     lowerGate k hk ops (Gate.CSignedPhaseProd c p x z)
--       =
--     match ExtReg.asZeroBaseReg? x, ExtReg.asZeroBaseReg? z with
--     | some x₀, some z₀ => lowerCPhaseProd k hk c p x₀ z₀
--     | _, _ => lowerCSignedPhaseProd k hk c p x z := rfl

end LowGate


/-! =========================================================
    Section 16: Lowerable phase-gate fragment
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

@[simp] theorem not_CSignedPhaseProd (c : ℕ) (phi : ℝ) (x z : ExtReg) :
    ¬ LowerablePhaseGate (Gate.CSignedPhaseProd c phi x z) := by
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

@[simp] theorem not_CPhaseProd (c : ℕ) (phi : ℝ) (x z : Reg) :
    ¬ LowerablePhaseGate (Gate.CPhaseProd c phi x z) := by
  intro h
  unfold Gate.CPhaseProd at h
  cases h with
  | seq _ _ _ h =>
      cases h with
      | seq _ _ _ h =>
          cases h with
          | seq _ _ h _ =>
              exact
                not_CSignedPhaseProd c phi
                  (Gate.unsignedView x) (Gate.unsignedView z) h

end LowerablePhaseGate

/-! =========================================================
    Section 17: Lowerability of compiled signed op lists
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

lemma lowerable_compileSignedAllocations
  (k : ℕ) (src dst : LayoutState k) :
  LowerablePhaseGate (compileSignedAllocations k src dst) := by
  unfold compileSignedAllocations
  induction List.finRange k with
  | nil =>
      simp [LowerablePhaseGate.id]
  | cons i xs ih =>
      simp [lowerable_allocChunkGate, ih, LowerablePhaseGate.seq]

lemma lowerable_compileSignedDeallocations
  (k : ℕ) (src dst : LayoutState k) :
  LowerablePhaseGate (compileSignedDeallocations k src dst) := by
  unfold compileSignedDeallocations
  induction (List.finRange k).reverse with
  | nil =>
      simp [LowerablePhaseGate.id]
  | cons i xs ih =>
      simp [lowerable_deallocChunkGate, ih, LowerablePhaseGate.seq]

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

@[simp] lemma lowerGate_PP (p : ℝ) (x z : Reg) (ops : Prog k) :
    lowerGate k hk ops (Gate.PhaseProd p x z) = lowerPhaseProd k hk p x z ops := by
  simp [lowerGate, lowerPhaseProd, lowerSignedPhaseProd, lowerGateRec, Gate.PhaseProd]

/-! =========================================================
    Section 17: Lowerability of compiled signed op lists
========================================================= -/


lemma lowerable_compileOpsToSignedGate
  (k : ℕ) (hk : 1 < k) (phi : ℝ)
  (x z : ExtReg) (pts : List Point) (hpts : pts.length = q k)
  (ops : List (valid_ops k)) :
  let W := commonNeededWidth (scanNeededWidths x z ops)
  let coeff := phaseCoeffFromPtsWidth k W pts hpts
  LowerablePhaseGate
    (compileOpsToSignedGate k hk phi x z coeff ops) := by
  dsimp [compileOpsToSignedGate]
  refine LowerablePhaseGate.seq _ _ ?_ ?_
  · exact
      lowerable_compileSignedAllocations
        k
        (initSignedLayoutState x z k)
        (targetSignedLayoutState x z k (scanNeededWidths x z ops))
  · refine LowerablePhaseGate.seq _ _ ?_ ?_
    · exact
        lowerable_compileAnnotatedOpsToSignedGateAux
          k hk phi
          (phaseCoeffFromPtsWidth k
            (commonNeededWidth (scanNeededWidths x z ops)) pts hpts)
          (targetSignedLayoutState x z k (scanNeededWidths x z ops))
          (annotatePhaseTermsAux k 0 ops)
    · exact
        lowerable_compileSignedDeallocations
          k
          (initSignedLayoutState x z k)
          (targetSignedLayoutState x z k (scanNeededWidths x z ops))

/-- Strong induction theorem for semantic correctness of `lowerGateRec`,
    parameterized by a correctness hypothesis for `compileOpsToGate`
    with the chosen program `ops`. -/
lemma evalL_lowerGateRec_strong_of_compile
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  [LowerGateClass qs] [GateSemanticsFacts qs] :
  ∀ n,
    ∀ (k : ℕ) (hk : 1 < k)
      (pts : List Point) (hpts : pts.length = q k)
      (ops : Prog k)
      (_hC : ProgConsumesPts (k := k) (by omega) State.start_state ops pts)
      (_run_ops_start_state : run? ops State.start_state = some State.start_state)
      (U : Gate) (_hU : LowerablePhaseGate U) (ψ : qs.State),
      LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops U) ψ
        =
      qs.eval U ψ := by
  intro n
  induction' n using Nat.strong_induction_on with n IH
  intro k hk pts hpts ops hC run_ops_start_state U hU ψ
  induction hU generalizing ψ with
  | id =>
      simp [lowerGateRec, LowerGateClass.evalL_id, qs.eval_id]

  | seq h1 h2 hU hV ihU ihV =>
      simp [lowerGateRec, LowerGateClass.evalL_seq, qs.eval_seq, ihU, ihV]

  | H  =>
      simp [lowerGateRec, LowerGateClass.evalL_H]

  | X  =>
      simp [lowerGateRec, LowerGateClass.evalL_X]

  | Prim =>
      simp [lowerGateRec, LowerGateClass.evalL_Prim]

  | ShiftL =>
      simp [lowerGateRec, LowerGateClass.evalL_shiftL]

  | ShiftR =>
      simp [lowerGateRec, LowerGateClass.evalL_shiftR]

  | Negate =>
      simp [lowerGateRec, LowerGateClass.evalL_negate]

  | AddScaled  =>
      simp [lowerGateRec, LowerGateClass.evalL_addScaled]

  | SignedPhaseProd phi x z =>
      unfold lowerGateRec
      dsimp
      let W := nextSignedWidth x z ops
      by_cases hrec : W < n
      · simp [W, hrec]
        let coeff := phaseCoeffFromPtsWidth k W pts hpts
        let g := compileOpsToSignedGate k hk phi x z coeff ops

        have hg : LowerablePhaseGate g := by
          dsimp [g, coeff]
          simpa [W, nextSignedWidth] using
            (lowerable_compileOpsToSignedGate k hk phi x z pts hpts ops)

        have hIH :
            LowerGateClass.evalL (lowerGateRec W k hk pts hpts ops g) ψ
              =
            qs.eval g ψ := by
          exact IH W hrec k hk pts hpts ops hC run_ops_start_state g hg ψ

        rw [hIH]
        simpa [g, coeff, W, nextSignedWidth] using
          (eval_compileOpsToSignedGate_correct
            (qs := qs)
            (k := k) (hk := hk)
            (phi := phi)
            (x := x) (z := z)
            (pts := pts) (hpts := hpts)
            (ψ := ψ)
            (ops := ops)
            (hC := hC)
            (run_ops_start_state := run_ops_start_state))

      · simp [W, hrec, LowerGateClass.evalL_naive_phaseProd]

  | zeroExtend r m =>
      simp [lowerGateRec, LowerGateClass.evalL_zeroExtend]

  | signExtend r m =>
      simp [lowerGateRec, LowerGateClass.evalL_signExtend]

  | zeroDealloc r m =>
      simp [lowerGateRec, LowerGateClass.evalL_zeroDealloc]

  | signDealloc r m =>
      simp [lowerGateRec, LowerGateClass.evalL_signDealloc]

lemma evalL_lowerGateRec_strong
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  [LowerGateClass qs] [GateSemanticsFacts qs] :
  ∀ n,
    ∀ (k : ℕ) (hk : 1 < k)
      (pts : List Point) (hpts : pts.length = q k)
      (ops : Prog k)
      (_hC : ProgConsumesPts (k := k) (by omega) State.start_state ops pts)
      (_run_ops_start_state : run? ops State.start_state = some State.start_state)
      (U : Gate) (_hU : LowerablePhaseGate U) (ψ : qs.State),
      LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops U) ψ
        =
      qs.eval U ψ := by
  intro n k hk pts hpts ops hC run_ops_start_state U hU ψ
  apply evalL_lowerGateRec_strong_of_compile (qs := qs) n k hk pts hpts ops
  · exact hC
  · exact run_ops_start_state
  · exact hU

/-! =========================================================
    Section 18: Semantic correctness of lowering helpers
========================================================= -/



@[simp] lemma lowerGate_SPP (p : ℝ) (x z : ExtReg) (ops : Prog k) :
    lowerGate k hk ops (Gate.SignedPhaseProd p x z) = lowerSignedPhaseProd k hk p x z ops := by
  simp [lowerGate, lowerSignedPhaseProd]

lemma evalL_lowerSignedPhaseProd
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  [LowerGateClass qs] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k) (p : ℝ) (x z : ExtReg) (ψ : qs.State) (ops : Prog k)
  (hC : ProgConsumesPts (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
  (run_ops_start_state : run? ops State.start_state = some State.start_state)
  :
  LowerGateClass.evalL (lowerSignedPhaseProd k hk p x z ops) ψ
    =
  qs.eval (Gate.SignedPhaseProd p x z) ψ := by
  unfold lowerSignedPhaseProd
  let pts := genInterpolationPoints k
  have hpts : pts.length = q k := by
    simp [pts, genInterpolationPoints, q]
  let W := nextSignedWidth x z ops
  by_cases hrec : W < phaseInputSize x z
  · simp [W, hrec]
    let coeff := phaseCoeffFromPtsWidth k W pts hpts
    let g := compileOpsToSignedGate k hk p x z coeff ops

    have hg : LowerablePhaseGate g := by
      dsimp [g, coeff]
      simpa [W, nextSignedWidth] using
        (lowerable_compileOpsToSignedGate k hk p x z pts hpts ops)

    have h1 :
        LowerGateClass.evalL (lowerGateRec W k hk pts hpts ops g) ψ
          =
        qs.eval g ψ := by
      apply evalL_lowerGateRec_strong
      · simpa [pts] using hC
      · exact run_ops_start_state
      · exact hg

    rw [h1]

    simpa [g, coeff, W, nextSignedWidth] using
      (eval_compileOpsToSignedGate_correct
        (qs := qs)
        (k := k) (hk := hk)
        (phi := p)
        (x := x) (z := z)
        (pts := pts) (hpts := hpts)
        (ψ := ψ)
        (ops := ops)
        (hC := by simpa [pts] using hC)
        (run_ops_start_state := run_ops_start_state))
  · simpa [pts, hpts, W, hrec] using
      (LowerGateClass.evalL_naive_phaseProd
        (qs := qs) (p := p) (x := x) (z := z) (ψ := ψ))

lemma evalL_lowerPhaseProd
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  [LowerGateClass qs] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k) (p : ℝ) (x z : Reg) (ψ : qs.State) (ops : Prog k)
  (hC : ProgConsumesPts (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
  (run_ops_start_state : run? ops State.start_state = some State.start_state)
  :
  LowerGateClass.evalL (lowerPhaseProd k hk p x z ops) ψ
    =
  qs.eval (Gate.PhaseProd p x z) ψ := by
  unfold lowerPhaseProd
  let pts := genInterpolationPoints k
  have hpts : pts.length = q k := by
    simp [pts, genInterpolationPoints, q]

  have hU : LowerablePhaseGate (Gate.PhaseProd p x z) := by
    simp

  simpa [pts] using
    (evalL_lowerGateRec_strong
      (qs := qs)
      (n := phaseInputSize (Gate.unsignedView x) (Gate.unsignedView z))
      (k := k) (hk := hk)
      (pts := pts) (hpts := hpts)
      (ops := ops)
      (_hC := by simpa [pts] using hC)
      (_run_ops_start_state := run_ops_start_state)
      (U := Gate.PhaseProd p x z)
      (ψ := ψ)
      hU)

-- /-- Semantic correctness of `lowerPhaseProd`. -/
-- lemma evalL_lowerPhaseProd
--   (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
--   [LowerGateClass qs] [GateSemanticsFacts qs]
--   (k : ℕ) (hk : 1 < k) (p : ℝ) (x z : Reg) (ψ : qs.State) (ops : Prog k)
--   (hC : ProgConsumesPts (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
--   (run_ops_start_state : run? ops State.start_state = some State.start_state)
--   :
--   LowerGateClass.evalL (lowerPhaseProd k hk p x z ops) ψ
--     =
--   qs.eval (Gate.PhaseProd p x z) ψ := by
--   unfold lowerPhaseProd
--   let pts := genInterpolationPoints k
--   have hpts : pts.length = q k := by
--     dsimp [pts]
--     simp [genInterpolationPoints, q]
--   let coeff := phaseCoeffOfPts k x pts hpts
--   let g := compileOpsToGate k hk p x z coeff ops

--   have hg : LowerablePhaseGate g := by
--     dsimp [g]
--     exact lowerable_compileOpsToGate k hk p x z pts hpts ops

--   have h1 :
--       LowerGateClass.evalL (lowerGateRec (regSize x) k hk pts hpts ops g) ψ
--         =
--       qs.eval g ψ := by
--     apply evalL_lowerGateRec_strong
--     · simpa [pts] using hC
--     · exact run_ops_start_state
--     · exact hg

--   unfold pts g coeff at h1
--   rw [h1]

--   simpa [phaseCoeffOfPts] using
--     (eval_compileOpsToGate_correct
--       (qs := qs)
--       (k := k) (hk := hk)
--       (phi := p)
--       (x := x) (z := z)
--       (pts := pts) (hpts := hpts)
--       (ψ := ψ)
--       (ops := ops)
--       (hC := by simpa [pts] using hC)
--       (run_ops_start_state := run_ops_start_state))

-- /-- Semantic correctness of `lowerSignedPhaseProd`. -/
-- lemma evalL_lowerSignedPhaseProd
--   (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
--   [LowerGateClass qs] [GateSemanticsFacts qs]
--   (k : ℕ) (hk : 1 < k) (p : ℝ) (x z : ExtReg) (ψ : qs.State) (ops : Prog k)
--   (hC : ProgConsumesPts (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
--   (run_ops_start_state : run? ops State.start_state = some State.start_state)
--   :
--   LowerGateClass.evalL (lowerSignedPhaseProd k hk p x z ops) ψ
--     =
--   qs.eval
--     (Gate.SignedPhaseProd p x z) ψ := by
--   unfold lowerSignedPhaseProd
--   let pts := genInterpolationPoints k
--   have hpts : pts.length = q k := by
--     dsimp [pts]
--     simp [genInterpolationPoints, q]
--   let coeff := phaseCoeffOfPts k x pts hpts
--   let g := compileOpsToSignedGate k hk p x z coeff ops

--   have hg : LowerablePhaseGate g := by
--     dsimp [g]
--     exact lowerable_compileOpsToSignedGate k hk p x z pts hpts ops

--   have h1 :
--       LowerGateClass.evalL (lowerGateRec (regSize x) k hk pts hpts ops g) ψ
--         =
--       qs.eval g ψ := by
--     apply evalL_lowerGateRec_strong
--     · simpa [pts] using hC
--     · exact run_ops_start_state
--     · exact hg

--   unfold pts g coeff at h1
--   rw [h1]

--   simpa [phaseCoeffOfPts] using
--     (eval_compileOpsToSignedGate_correct
--       (qs := qs)
--       (k := k) (hk := hk)
--       (phi := p)
--       (x := x) (z := z)
--       (pts := pts) (hpts := hpts)
--       (ψ := ψ)
--       (ops := ops)
--       (hC := by simpa [pts] using hC)
--       (run_ops_start_state := run_ops_start_state))

-- /-- Semantic correctness of `lowerCSignedPhaseProd`. -/
-- lemma evalL_lowerCSignedPhaseProd
--   (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]
--   (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (p : ℝ) (x z : ExtReg) (ψ : qs.State) :
--   LowerGateClass.evalL (lowerCSignedPhaseProd k hk ctrl p x z) ψ
--     =
--   qs.eval (Gate.CSignedPhaseProd ctrl p x z) ψ := by
--   simpa [lowerCSignedPhaseProd] using
--     (LowerGateClass.evalL_naive_csignedPhaseProd
--       (qs := qs) (c := ctrl) (p := p) (x := x) (z := z) (ψ := ψ))

-- -- /-- Semantic correctness of `lowerCPhaseProd`. -/
-- -- lemma evalL_lowerCPhaseProd
-- --   (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]
-- --   (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (p : ℝ) (x z : Reg) (ψ : qs.State) :
-- --   LowerGateClass.evalL (lowerCPhaseProd k hk ctrl p x z) ψ
-- --     =
-- --   qs.eval (Gate.CPhaseProd ctrl p x z) ψ := by
-- --   sorry
