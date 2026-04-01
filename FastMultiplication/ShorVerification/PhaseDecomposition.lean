import FastMultiplication.ShorVerification.LowGate_compilation

namespace Shor
open Gate
open Operations


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
      LowGate.seq (lowerGateRec initSize k hk pts hpts ops U) (lowerGateRec initSize k hk pts hpts ops V)
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
  | Gate.CPhaseProd ctrl phi x z =>
      LowGate.Naive_CPhaseProd ctrl phi x z
  | Gate.PhaseProd phi x z =>
    if (regSize x) / k + 1 < initSize then
      let coeff := phaseCoeffOfPts k x pts hpts
      let g := compileOpsToGate k hk phi x z coeff
        (ops)
      lowerGateRec ((regSize x) / k) k hk pts hpts ops g
    else
      LowGate.Naive_PhaseProd phi x z

/-- Alternating integer interpolation points around zero. -/
def alternatingPoint (i : ℕ) : Point :=
  if i % 2 == 0 then
    Point.int (i / 2 : ℤ)
  else
    Point.int (-((i + 1) / 2 : ℤ))

/-- Generate the canonical `2k - 1` interpolation points. -/
def genInterpolationPoints (k : ℕ) : List Point :=
  (List.range (2 * k - 1)).map alternatingPoint

/-- Lower a phase product by interpolation-based decomposition. -/
noncomputable def lowerPhaseProd (k : ℕ) (hk : 1 < k) (phi : ℝ) (x z : Reg) (ops: Prog k):=
  let pts := genInterpolationPoints k
  let hpts : pts.length = q k := by
    unfold pts
    simp [genInterpolationPoints, q]
  let coeff := phaseCoeffOfPts k x pts hpts
  let op1 := compileOpsToGate k hk phi x z coeff
    (ops)
  lowerGateRec (regSize x) k hk pts hpts ops op1


/-- Lower a controlled phase product. -/
def lowerCPhaseProd : (k : ℕ) → (hk : 1 < k) → (ctrl : ℕ) → (phi : ℝ) → (x z : Reg) → LowGate :=
  sorry

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
  | .PhaseProd p x z => lowerPhaseProd k hk p x z ops
  | .CPhaseProd c p x z => lowerCPhaseProd k hk c p x z
  | .Prim tag args => .Prim tag args
  | .ShiftL r n => .ShiftL r n
  | .ShiftR r n => .ShiftR r n
  | .AddScaled dst src negSrc shift => .AddScaled dst src negSrc shift
  | .Negate r => .Negate r


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

  evalL_naive_phaseProd :
    ∀ p x z ψ,
      evalL (LowGate.Naive_PhaseProd p x z) ψ
        = qs.eval (Gate.PhaseProd p x z) ψ

  evalL_adj_of_lowered :
    ∀ (k : ℕ) (hk : 1 < k) (U : Gate) (ψ : qs.State) (ops: Prog k),
      evalL (†(lowerGate k hk ops U)) ψ = qs.eval (†U) ψ
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

/-- Simplification rule for lowering phase products. -/
@[simp] lemma lowerGate_PP (p : ℝ) (x z : Reg) (ops: Prog k):
    lowerGate k hk ops (Gate.PhaseProd p x z) = lowerPhaseProd k hk p x z ops := rfl

/-- Simplification rule for lowering controlled phase products. -/
@[simp] lemma lowerGate_CPP (c : ℕ) (p : ℝ) (x z : Reg) (ops: Prog k):
    lowerGate k hk ops (Gate.CPhaseProd c p x z) = lowerCPhaseProd k hk c p x z := rfl

end LowGate



/-! =========================================================
    Section 15: Lowerable phase-gate fragment
========================================================= -/

/-- Gates that can appear during recursive phase-product lowering. -/
inductive LowerablePhaseGate : Gate → Prop where
  | id : LowerablePhaseGate Gate.id
  | seq : ∀ {U V : Gate},
      LowerablePhaseGate U →
      LowerablePhaseGate V →
      LowerablePhaseGate (Gate.seq U V)
  | H : ∀ {q : ℕ}, LowerablePhaseGate (Gate.H q)
  | X : ∀ {q : ℕ}, LowerablePhaseGate (Gate.X q)
  | Prim : ∀ {s : String} {qs : List ℕ},
      LowerablePhaseGate (Gate.Prim s qs)
  | ShiftL : ∀ {r : Reg} {n : ℕ},
      LowerablePhaseGate (Gate.ShiftL r n)
  | ShiftR : ∀ {r : Reg} {n : ℕ},
      LowerablePhaseGate (Gate.ShiftR r n)
  | Negate : ∀ {r : Reg},
      LowerablePhaseGate (Gate.Negate r)
  | AddScaled : ∀ {dst src : Reg} {negSrc : Bool} {sh : ℕ},
      LowerablePhaseGate (Gate.AddScaled dst src negSrc sh)
  | PhaseProd : ∀ {phi : ℝ} {x z : Reg},
      LowerablePhaseGate (Gate.PhaseProd phi x z)

namespace LowerablePhaseGate

/-- Adjoint gates are excluded from the lowerable phase fragment. -/
@[simp] theorem not_adj (U : Gate) : ¬ LowerablePhaseGate (Gate.adj U) := by
  intro h
  cases h

/-- QFT gates are excluded from the lowerable phase fragment. -/
@[simp] theorem not_QFT (r : Reg) : ¬ LowerablePhaseGate (Gate.QFT r) := by
  intro h
  cases h

/-- Controlled phase products are excluded from the lowerable phase fragment. -/
@[simp] theorem not_CPhaseProd (c : ℕ) (phi : ℝ) (x z : Reg) :
    ¬ LowerablePhaseGate (Gate.CPhaseProd c phi x z) := by
  intro h
  cases h

end LowerablePhaseGate

/-! =========================================================
    Section 16: Lowerability of compiled op lists
========================================================= -/

/-- The annotated auxiliary compiler always produces a lowerable phase gate. -/
lemma lowerable_compileAnnotatedOpsToGateAux
  (k : ℕ) (hk : 1 < k) (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k) (ops : List (AnnotatedOp k)) :
  LowerablePhaseGate (compileAnnotatedOpsToGateAux k hk phi phaseCoeff st ops) := by
  induction ops generalizing st with
  | nil =>
      simp [compileAnnotatedOpsToGateAux, LowerablePhaseGate.id]
  | cons a rest ih =>
      rcases a with ⟨op, term?⟩
      cases op <;>
        cases term? <;>
        simp [compileAnnotatedOpsToGateAux, ih, LowerablePhaseGate.seq,
          LowerablePhaseGate.ShiftL, LowerablePhaseGate.ShiftR,
          LowerablePhaseGate.Negate, LowerablePhaseGate.AddScaled,
          LowerablePhaseGate.PhaseProd]

lemma lowerable_compileOpsToGate
  (k : ℕ) (hk : 1 < k) (phi : ℝ)
  (x z : Reg) (pts : List Point) (hpts : pts.length = q k)
  (ops : List (valid_ops k)) :
  LowerablePhaseGate
    (compileOpsToGate k hk phi x z (phaseCoeffOfPts k x pts hpts) ops) := by
  rw [compileOpsToGate_ofPts_eq_aux]
  simp only
  exact lowerable_compileAnnotatedOpsToGateAux
    k hk phi
    (phaseCoeffOfPts k x pts hpts)
    (initLayoutState x z k)
    (annotatePhaseTermsAux k 0 ops)


-- /-! =========================================================
--     Section 17: Correctness of recursive lowering
-- ========================================================= -/

-- /-- Strong induction theorem for semantic correctness of `lowerGateRec`. -/
-- lemma evalL_lowerGateRec_strong
--   (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs] [GateSemanticsFacts qs]:
--   ∀ n,
--     ∀ (k : ℕ) (hk : 1 < k) (pts : List Point) (hpts : pts.length = q k)
--       (U : Gate) (_hU : LowerablePhaseGate U) (ψ : qs.State),
--       LowerGateClass.evalL (lowerGateRec n k hk pts hpts U) ψ
--         =
--       qs.eval U ψ := by
--   intro n
--   induction' n using Nat.strong_induction_on with n IH
--   intro k hk pts hpts U hU ψ
--   revert hU ψ
--   induction U generalizing n with
--   | id =>
--       intro hU ψ
--       cases hU
--       simp [lowerGateRec, LowerGateClass.evalL_id, QSemantics.eval_id]

--   | seq U V ihU ihV =>
--       intro hUV ψ
--       cases hUV with
--       | seq hU hV =>
--           have h1 :
--               LowerGateClass.evalL (lowerGateRec n k hk pts hpts (U ;; V)) ψ
--                 =
--               LowerGateClass.evalL
--                 ((lowerGateRec n k hk pts hpts U) ;; (lowerGateRec n k hk pts hpts V)) ψ := by
--             simp [lowerGateRec]

--           have h2 :
--               LowerGateClass.evalL
--                 ((lowerGateRec n k hk pts hpts U) ;; (lowerGateRec n k hk pts hpts V)) ψ
--                 =
--               LowerGateClass.evalL (lowerGateRec n k hk pts hpts V)
--                 (LowerGateClass.evalL (lowerGateRec n k hk pts hpts U) ψ) := by
--             simpa using
--               (LowerGateClass.evalL_seq
--                 (qs := qs)
--                 (U := lowerGateRec n k hk pts hpts U)
--                 (V := lowerGateRec n k hk pts hpts V)
--                 (ψ := ψ))

--           have h3 :
--               LowerGateClass.evalL (lowerGateRec n k hk pts hpts U) ψ
--                 =
--               qs.eval U ψ := by
--             simpa using ihU n IH hU ψ

--           have h4 :
--               LowerGateClass.evalL (lowerGateRec n k hk pts hpts V) (qs.eval U ψ)
--                 =
--               qs.eval V (qs.eval U ψ) := by
--               exact ihV n IH hV (QSemantics.eval U ψ)

--           have h5 :
--               qs.eval (U ;; V) ψ
--                 =
--               qs.eval V (qs.eval U ψ) := by
--             exact QSemantics.eval_seq U V ψ

--           calc
--             LowerGateClass.evalL (lowerGateRec n k hk pts hpts (U ;; V)) ψ
--                 =
--               LowerGateClass.evalL
--                 ((lowerGateRec n k hk pts hpts U) ;; (lowerGateRec n k hk pts hpts V)) ψ := h1
--             _ =
--               LowerGateClass.evalL (lowerGateRec n k hk pts hpts V)
--                 (LowerGateClass.evalL (lowerGateRec n k hk pts hpts U) ψ) := h2
--             _ =
--               LowerGateClass.evalL (lowerGateRec n k hk pts hpts V) (qs.eval U ψ) := by
--                 rw [h3]
--             _ =
--               qs.eval V (qs.eval U ψ) := h4
--             _ =
--               qs.eval (U ;; V) ψ := by
--                 symm
--                 exact h5

--   | adj U ihU =>
--       intro hU ψ
--       cases hU

--   | H q =>
--       intro hU ψ
--       cases hU
--       simp [lowerGateRec, LowerGateClass.evalL_H]

--   | X q =>
--       intro hU ψ
--       cases hU
--       simp [lowerGateRec, LowerGateClass.evalL_X]

--   | QFT r =>
--       intro hU ψ
--       cases hU

--   | PhaseProd phi x z =>
--       intro hU ψ
--       cases hU with
--       | PhaseProd =>
--           by_cases hrec : regSize x / k + 1 < n
--           ·
--             simp [lowerGateRec, hrec]
--             let coeff := phaseCoeffOfPts k x pts hpts
--             let g := compileOpsToGate k hk phi x z coeff
--               (genOpsWithProduct (by omega) pts)

--             have hg : LowerablePhaseGate g := by
--               dsimp [g]
--               exact lowerable_compileOpsToGate k hk phi x z pts hpts
--                 (genOpsWithProduct (by omega) pts)

--             have hlt : regSize x / k < n := by
--               omega

--             have hIH :
--                 LowerGateClass.evalL
--                   (lowerGateRec (regSize x / k) k hk pts hpts g) ψ
--                   =
--                 qs.eval g ψ := by
--               exact IH (regSize x / k) hlt k hk pts hpts g hg ψ

--             rw [hIH]
--             dsimp [g]
--             exact eval_compileOpsToGate_genOpsWithProduct qs k hk phi x z pts hpts ψ
--           ·
--             simp [lowerGateRec, hrec, LowerGateClass.evalL_naive_phaseProd]

--   | CPhaseProd ctrl phi x z =>
--       intro hU ψ
--       cases hU

--   | Prim s qs' =>
--       intro hU ψ
--       cases hU
--       simp [lowerGateRec, LowerGateClass.evalL_Prim]

--   | ShiftL r m =>
--       intro hU ψ
--       cases hU
--       simp [lowerGateRec, LowerGateClass.evalL_shiftL]

--   | ShiftR r m =>
--       intro hU ψ
--       cases hU
--       simp [lowerGateRec, LowerGateClass.evalL_shiftR]

--   | Negate r =>
--       intro hU ψ
--       cases hU
--       simp [lowerGateRec, LowerGateClass.evalL_negate]

--   | AddScaled dst src negSrc sh =>
--       intro hU ψ
--       cases hU
--       simp [lowerGateRec, LowerGateClass.evalL_addScaled]


/-- Strong induction theorem for semantic correctness of `lowerGateRec`,
    parameterized by a correctness hypothesis for `compileOpsToGate`
    with the chosen program `ops`. -/
lemma evalL_lowerGateRec_strong_of_compile
  (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs] [GateSemanticsFacts qs] :
  ∀ n,
    ∀ (k : ℕ) (hk : 1 < k)
      (pts : List Point) (hpts : pts.length = q k)
      (ops : Prog k)
      (_hPC : PhaseProductCoverage (by omega) ops State.start_state pts)
      (U : Gate) (_hU : LowerablePhaseGate U) (ψ : qs.State),
      LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops U) ψ
        =
      qs.eval U ψ := by
  intro n
  induction' n using Nat.strong_induction_on with n IH
  intro k hk pts hpts ops hPC U hU ψ
  revert hU ψ
  induction U generalizing n with
  | id =>
      intro hU ψ
      cases hU
      simp [lowerGateRec, LowerGateClass.evalL_id, QSemantics.eval_id]

  | seq U V ihU ihV =>
      intro hUV ψ
      cases hUV with
      | seq hU hV =>
          have h1 :
              LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops (U ;; V)) ψ
                =
              LowerGateClass.evalL
                ((lowerGateRec n k hk pts hpts ops U) ;; (lowerGateRec n k hk pts hpts ops V)) ψ := by
            simp [lowerGateRec]

          have h2 :
              LowerGateClass.evalL
                ((lowerGateRec n k hk pts hpts ops U) ;; (lowerGateRec n k hk pts hpts ops V)) ψ
                =
              LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops V)
                (LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops U) ψ) := by
            simpa using
              (LowerGateClass.evalL_seq
                (qs := qs)
                (U := lowerGateRec n k hk pts hpts ops U)
                (V := lowerGateRec n k hk pts hpts ops V)
                (ψ := ψ))

          have h3 :
              LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops U) ψ
                =
              qs.eval U ψ := by
            simpa using ihU n IH hU ψ

          have h4 :
              LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops V) (qs.eval U ψ)
                =
              qs.eval V (qs.eval U ψ) := by
            exact ihV n IH hV (QSemantics.eval U ψ)

          have h5 :
              qs.eval (U ;; V) ψ
                =
              qs.eval V (qs.eval U ψ) := by
            exact QSemantics.eval_seq U V ψ

          calc
            LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops (U ;; V)) ψ
                =
              LowerGateClass.evalL
                ((lowerGateRec n k hk pts hpts ops U) ;; (lowerGateRec n k hk pts hpts ops V)) ψ := h1
            _ =
              LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops V)
                (LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops U) ψ) := h2
            _ =
              LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops V) (qs.eval U ψ) := by
                rw [h3]
            _ =
              qs.eval V (qs.eval U ψ) := h4
            _ =
              qs.eval (U ;; V) ψ := by
                symm
                exact h5

  | adj U ihU =>
      intro hU ψ
      cases hU

  | H q =>
      intro hU ψ
      cases hU
      simp [lowerGateRec, LowerGateClass.evalL_H]

  | X q =>
      intro hU ψ
      cases hU
      simp [lowerGateRec, LowerGateClass.evalL_X]

  | QFT r =>
      intro hU ψ
      cases hU

  | PhaseProd phi x z =>
      intro hU ψ
      cases hU with
      | PhaseProd =>
          by_cases hrec : regSize x / k + 1 < n
          ·
            simp [lowerGateRec, hrec]
            let g := compileOpsToGate k hk phi x z (phaseCoeffOfPts k x pts hpts) ops

            have hg : LowerablePhaseGate g := by
              dsimp [g]
              exact lowerable_compileOpsToGate k hk phi x z pts hpts ops

            have hlt : regSize x / k < n := by
              omega

            have hIH :
                LowerGateClass.evalL
                  (lowerGateRec (regSize x / k) k hk pts hpts ops g) ψ
                  =
                qs.eval g ψ := by
              exact IH (regSize x / k) hlt
                k hk pts hpts ops hPC g hg ψ

            rw [hIH]
            dsimp [g]
            simpa [phaseCoeffOfPts] using
              (eval_compileOpsToGate_correct
                (qs := qs)
                (k := k) (hk := hk)
                (phi := phi)
                (x := x) (z := z)
                (pts := pts) (hpts := hpts)
                (ψ := ψ)
                (ops := ops)
                (hPC := hPC))
          ·
            simp [lowerGateRec, hrec, LowerGateClass.evalL_naive_phaseProd]

  | CPhaseProd ctrl phi x z =>
      intro hU ψ
      cases hU

  | Prim s qs' =>
      intro hU ψ
      cases hU
      simp [lowerGateRec, LowerGateClass.evalL_Prim]

  | ShiftL r m =>
      intro hU ψ
      cases hU
      simp [lowerGateRec, LowerGateClass.evalL_shiftL]

  | ShiftR r m =>
      intro hU ψ
      cases hU
      simp [lowerGateRec, LowerGateClass.evalL_shiftR]

  | Negate r =>
      intro hU ψ
      cases hU
      simp [lowerGateRec, LowerGateClass.evalL_negate]

  | AddScaled dst src negSrc sh =>
      intro hU ψ
      cases hU
      simp [lowerGateRec, LowerGateClass.evalL_addScaled]


lemma evalL_lowerGateRec_strong
  (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs] [GateSemanticsFacts qs] :
  ∀ n,
    ∀ (k : ℕ) (hk : 1 < k)
      (pts : List Point) (hpts : pts.length = q k)
      (ops : Prog k)
      (_hPC : PhaseProductCoverage (k:=k) (by omega) ops State.start_state pts)
      (U : Gate) (_hU : LowerablePhaseGate U) (ψ : qs.State),
      LowerGateClass.evalL (lowerGateRec n k hk pts hpts ops U) ψ
        =
      qs.eval U ψ := by
  intro n k hk pts hpts ops hPC U hU ψ
  apply evalL_lowerGateRec_strong_of_compile (qs := qs) n k hk pts hpts ops
  exact hPC
  exact hU

/-- Semantic correctness of `lowerPhaseProd`. -/
lemma evalL_lowerPhaseProd
  (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k) (p : ℝ) (x z : Reg) (ψ : qs.State) (ops: Prog k)
  (hPC: PhaseProductCoverage (by omega) ops State.start_state (genInterpolationPoints k))
  :
  LowerGateClass.evalL (lowerPhaseProd k hk p x z ops) ψ
    =
  qs.eval (Gate.PhaseProd p x z) ψ := by
  unfold lowerPhaseProd
  let pts := genInterpolationPoints k
  have hpts : pts.length = q k := by
    dsimp [pts]
    simp [genInterpolationPoints, q]
  let coeff := phaseCoeffOfPts k x pts hpts
  let g := compileOpsToGate k hk p x z coeff
    (ops)

  have hg : LowerablePhaseGate g := by
    dsimp [g]
    exact lowerable_compileOpsToGate k hk p x z pts hpts ops

  have h1 :
      LowerGateClass.evalL (lowerGateRec (regSize x) k hk pts hpts ops g) ψ
        =
      qs.eval g ψ := by
      apply evalL_lowerGateRec_strong
      apply hPC; apply hg

  unfold pts g coeff at h1;simp

  rw [h1]

  apply eval_compileOpsToGate_correct qs k hk p x z pts hpts ψ ops
  apply hPC

/-- Semantic correctness of `lowerCPhaseProd`. -/
lemma evalL_lowerCPhaseProd
  (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]
  (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (p : ℝ) (x z : Reg) (ψ : qs.State) :
  LowerGateClass.evalL (lowerCPhaseProd k hk ctrl p x z) ψ
    =
  qs.eval (Gate.CPhaseProd ctrl p x z) ψ := by
  sorry

end Shor
