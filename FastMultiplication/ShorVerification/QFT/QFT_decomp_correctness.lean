import FastMultiplication.ShorVerification.QFT.QFT_decomposition_one_layer

/-! =========================================================
    Section 10: Correctness of lowered QFT
========================================================= -/
namespace Shor
variable {k : ℕ} (hk : 1 < k)

lemma eval_lowerQFTAux_strong
  (qs : QSemantics)
  (RE : RegEncoding qs.Basis)
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [LowerGateClass qs]
  [GateSemanticsFacts qs]
  (ops : Prog k)
  (hC : ProgConsumesPtsSafe
    (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  ∀ n : ℕ, ∀ (r : Reg) (ψ : qs.State),
    regSize r = n →
    LowerGateClass.evalL
      (qs := qs)
      (lowerQFTAux (Basis := qs.Basis) k hk ops n r)
      ψ
      =
    qs.eval (Gate.QFT r) ψ := by
  classical
  letI : RegEncoding qs.Basis := RE

  let P : ℕ → Prop :=
    fun n =>
      ∀ (r : Reg) (ψ : qs.State),
        regSize r = n →
        LowerGateClass.evalL
          (qs := qs)
          (lowerQFTAux (Basis := qs.Basis) k hk ops n r)
          ψ
          =
        qs.eval (Gate.QFT r) ψ

  intro n
  change P n

  induction n using Nat.strong_induction_on with
  | _ n IH =>
      intro r ψ hsz

      cases n with
      | zero =>
          simp [lowerQFTAux]
          have h0 :=
            QFTSemantics.eval_QFT_size0
              (qs := qs) (r := r) (ψ := ψ) hsz
          simpa [qs.eval_id] using h0.symm

      | succ n1 =>
          cases n1 with
          | zero =>
              simp [lowerQFTAux]
              have h1 :=
                QFTSemantics.eval_QFT_size1
                  (qs := qs) (r := r) (ψ := ψ) hsz
              simpa [LowerGateClass.evalL_H] using h1.symm

          | succ n2 =>
              let nTot : ℕ := n2 + 2
              let m : ℕ := nTot / 2
              let left  : Reg := { lo := r.lo, size := m }
              let right : Reg := { lo := r.lo + m, size := regSize r - m }

              have hsz' : regSize r = nTot := by
                simpa [nTot] using hsz

              have hleft : regSize left = m := by
                simp [left, regSize]

              have hm_le : m ≤ regSize r := by
                rw [hsz']
                unfold m
                exact Nat.div_le_self _ _

              have hright : regSize right = nTot - m := by
                simpa [right, regSize] using
                  congrArg (fun t => t - m) hsz'

              have hm_pos : 0 < m := by
                unfold m nTot
                exact Nat.div_pos (by omega : 2 ≤ n2 + 2) (by decide : 0 < 2)

              have hnm_lt : nTot - m < nTot := by
                exact Nat.sub_lt (by omega) hm_pos

              have ihR :
                  ∀ χ : qs.State,
                    LowerGateClass.evalL
                      (qs := qs)
                      (lowerQFTAux
                        (Basis := qs.Basis) k hk ops (nTot - m) right)
                      χ
                    =
                    qs.eval (Gate.QFT right) χ := by
                intro χ
                have hIH := IH (nTot - m) (by omega)
                simpa [P] using hIH right χ hright

              have ihL :
                  ∀ χ : qs.State,
                    LowerGateClass.evalL
                      (qs := qs)
                      (lowerQFTAux
                        (Basis := qs.Basis) k hk ops m left)
                      χ
                    =
                    qs.eval (Gate.QFT left) χ := by
                intro χ
                have hIH := IH m (by omega)
                simpa [P] using hIH left χ hleft

              have hge : regSize r ≥ 2 := by
                have : (2 : ℕ) ≤ nTot := by
                  unfold nTot
                  omega
                simpa [hsz'] using this

              have hSplit :
                  qs.eval (Gate.QFT r) ψ
                    =
                  qs.eval
                    ((Gate.QFT right) ;;
                     (Gate.PhaseProd (qftPhi nTot) left right) ;;
                     (Gate.QFT left) ;;
                     (Gate.RadixReverse r m)) ψ := by
                have hs :=
                  eval_QFT_split
                    (qs := qs) (r := r) (ψ := ψ) hge
                simpa [nTot, m, left, right, hsz'] using hs

              have hSplit' :
                  qs.eval
                    ((Gate.QFT right) ;;
                     (Gate.PhaseProd (qftPhi nTot) left right) ;;
                     (Gate.QFT left) ;;
                     (Gate.RadixReverse r m)) ψ
                    =
                  qs.eval (Gate.QFT r) ψ := by
                exact hSplit.symm

              have hdisj : Disjoint left right := by
                simp [Disjoint, left, right]

              have hWF_left : WellFormedReg left := by
                simp [WellFormedReg, left]

              have hWF_right : WellFormedReg right := by
                simp [WellFormedReg, right, regSize]

              calc
                LowerGateClass.evalL
                    (qs := qs)
                    (lowerQFTAux
                      (Basis := qs.Basis) k hk ops (n2 + 1 + 1) r)
                    ψ
                    =
                  LowerGateClass.evalL
                    (qs := qs)
                    ((lowerQFTAux
                        (Basis := qs.Basis) k hk ops (nTot - m) right) ;;
                     (lowerPhaseProd
                        (Basis := qs.Basis) k hk (qftPhi nTot) left right ops) ;;
                     (lowerQFTAux
                        (Basis := qs.Basis) k hk ops m left) ;;
                     (LowGate.RadixReverse r m))
                    ψ := by
                      simp [lowerQFTAux, nTot, m, left, right]

                _ =
                  LowerGateClass.evalL (qs := qs) (LowGate.RadixReverse r m)
                    (LowerGateClass.evalL
                      (qs := qs)
                      (lowerQFTAux
                        (Basis := qs.Basis) k hk ops m left)
                      (LowerGateClass.evalL
                        (qs := qs)
                        (lowerPhaseProd
                          (Basis := qs.Basis) k hk (qftPhi nTot) left right ops)
                        (LowerGateClass.evalL
                          (qs := qs)
                          (lowerQFTAux
                            (Basis := qs.Basis) k hk ops (nTot - m) right)
                          ψ))) := by
                      simp [LowerGateClass.evalL_seq]

                _ =
                  qs.eval (Gate.RadixReverse r m)
                    (qs.eval (Gate.QFT left)
                      (qs.eval (Gate.PhaseProd (qftPhi nTot) left right)
                        (qs.eval (Gate.QFT right) ψ))) := by
                      rw [ihR ψ]

                      have hPhase :=
                        evalL_lowerPhaseProd
                          (qs := qs)
                          (k := k) (hk := hk)
                          (p := qftPhi nTot)
                          (x := left) (z := right)
                          (hxz := hdisj)
                          (ψ := qs.eval (Gate.QFT right) ψ)
                          (ops := ops)
                          (hC := hC)
                          (run_ops_start_state := run_ops_start_state)
                      rw [hPhase]

                      rw [ihL
                        (qs.eval (Gate.PhaseProd (qftPhi nTot) left right)
                          (qs.eval (Gate.QFT right) ψ))]

                      have hRR :=
                        LowerGateClass.evalL_lowerRadixReverse
                          (qs := qs)
                          (r := r) (m := m)
                          (ψ :=
                            qs.eval (Gate.QFT left)
                              (qs.eval (Gate.PhaseProd (qftPhi nTot) left right)
                                (qs.eval (Gate.QFT right) ψ)))
                      rw [hRR]

                _ =
                  qs.eval
                    ((Gate.QFT right) ;;
                     (Gate.PhaseProd (qftPhi nTot) left right) ;;
                     (Gate.QFT left) ;;
                     (Gate.RadixReverse r m)) ψ := by
                      simp [qs.eval_seq]

                _ =
                  qs.eval (Gate.QFT r) ψ := by
                      exact hSplit'

lemma eval_lowerQFT
  (qs : QSemantics)
  (RE : RegEncoding qs.Basis)
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [LowerGateClass qs]
  [GateSemanticsFacts qs]
  (ops : Prog k)
  (hC : ProgConsumesPtsSafe
    (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  ∀ (r : Reg) (ψ : qs.State),
    LowerGateClass.evalL
      (qs := qs)
      (lowerQFT (Basis := qs.Basis) k hk r ops)
      ψ
      =
    qs.eval (Gate.QFT r) ψ := by
  intro r ψ
  simpa [lowerQFT] using
    (eval_lowerQFTAux_strong
      (qs := qs) (RE := RE) (k := k) (hk := hk)
      (ops := ops)
      (hC := hC)
      (run_ops_start_state := run_ops_start_state)
      (regSize r) r ψ rfl)

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
    Section 11: Whole-program lowering correctness
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
      simpa [lowerGate] using
        (LowerGateClass.evalL_naive_cphaseProd
          (qs := qs) (c := c) (p := p) (x := x) (z := z) (ψ := ψ))

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

end Shor
