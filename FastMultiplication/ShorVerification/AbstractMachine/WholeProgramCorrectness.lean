import FastMultiplication.ShorVerification.AbstractMachine.QFTLoweringCorrectness

namespace Shor

/-!
# Whole-Program Lowering Correctness

This file is the outer correctness theorem for the abstract machine: every
geometrically well-formed high-level gate lowers to a `LowGate` circuit with
the same semantics.
-/

/-! =========================================================
    Section 1: Geometric side conditions

    `GateGeomOK` records the disjointness and well-formedness assumptions that
    the recursive lowering theorem needs at the high-level syntax boundary.
========================================================= -/

def GateGeomOK : Gate → Prop
  | Gate.seq U V => GateGeomOK U ∧ GateGeomOK V
  | Gate.adj U => GateGeomOK U
  | Gate.AddScaled dst src _ _ =>
      Disjoint dst.base src.base
  | Gate.QFT r => WellFormedReg r
  | Gate.SignedPhaseProd _ x z =>
      Disjoint x.base z.base
  | Gate.CSignedPhaseProd _ _ x z =>
      Disjoint x.base z.base
  | _ => True

/-! =========================================================
    Section 2: Whole-program lowering correctness
========================================================= -/

theorem lowerGate_correctness
  (G : Gate) (hGeom: GateGeomOK G)
  (qs : QSemantics) (RE : RegEncoding qs.Basis)
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [LowerGateClass qs]
  [GateSemanticsFacts qs]
  (ops : Prog k)
  (hC : ProgConsumesPtsSafe
    (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  ∀ ψ, LowerGateClass.evalL
    (qs := qs)
    (lowerGate (Basis := qs.Basis) k hk ops G)
    ψ = qs.eval G ψ := by
  intro ψ
  induction G generalizing ψ with
  | id =>
      simp [lowerGate, LowerGateClass.evalL_id, qs.eval_id]

  | seq U V ihU ihV =>
      rcases hGeom with ⟨h1, h2⟩
      simp [lowerGate, LowerGateClass.evalL_seq, qs.eval_seq, ihU h1, ihV h2]

  | adj U ih =>
      simpa [lowerGate] using
        (LowerGateClass.evalL_adj_of_lowered
          (qs := qs) (k := k) (hk := hk) (U := U) (ψ := ψ) (ops := ops))

  | H q =>
      simp [lowerGate, LowerGateClass.evalL_H]

  | X q =>
      simp [lowerGate, LowerGateClass.evalL_X]

  | QFT r =>
      have:= (eval_lowerQFT
          (qs := qs) (RE := RE) (k := k) (hk := hk)
          (ops := ops) (hC := hC) run_ops_start_state r ψ)
      simp[this]

  | SignedPhaseProd p x z =>
      simp[GateGeomOK] at hGeom
      simpa [lowerGate] using
        (evalL_lowerSignedPhaseProd
          (qs := qs) (k := k) (hk := hk) (p := p)
          (x := x) (z := z)
          (hxz := hGeom)
          (ψ := ψ) (ops := ops)
          (hC := hC)
          (run_ops_start_state := run_ops_start_state))

  | CSignedPhaseProd c p x z =>
      simp[GateGeomOK] at hGeom
      simpa [lowerGate] using
        (evalL_lowerCSignedPhaseProd
          (qs := qs) (k := k) (hk := hk) (ctrl := c) (p := p)
          (x := x) (z := z)
          (hxz := hGeom)
          (ψ := ψ) (ops := ops)
          (hC := hC)
          (run_ops_start_state := run_ops_start_state))

  | Prim tag args =>
      simp [lowerGate, LowerGateClass.evalL_Prim]

  | ShiftL r n =>
      simp [lowerGate, LowerGateClass.evalL_shiftL]

  | ShiftR r n =>
      simp [lowerGate, LowerGateClass.evalL_shiftR]

  | Negate r =>
      simp [lowerGate, LowerGateClass.evalL_negate]

  | AddScaled dst src negSrc sh =>
      simp [lowerGate, LowerGateClass.evalL_addScaled]

  | zeroExtend r n =>
      simp [lowerGate, LowerGateClass.evalL_zeroExtend]

  | signExtend r n =>
      simp [lowerGate, LowerGateClass.evalL_signExtend]

  | zeroDealloc r n =>
      simp [lowerGate, LowerGateClass.evalL_zeroDealloc]

  | signDealloc r n =>
      simp [lowerGate, LowerGateClass.evalL_signDealloc]

  | RadixReverse r m =>
      simp [lowerGate, LowerGateClass.evalL_lowerRadixReverse]
