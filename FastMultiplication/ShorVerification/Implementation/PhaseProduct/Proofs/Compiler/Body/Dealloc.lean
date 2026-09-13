import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Body.Controlled

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Deallocation And Body/Deallocation Composition

    Allocation followed by deallocation cancels slot-by-slot, so the proved body
    scalar can be transported from the allocated basis state back to the original
    input basis state.
========================================================= -/

/-- One chunk allocation immediately followed by its matching deallocation is identity. -/
lemma allocChunkGate_deallocChunkGate_cancel
    (qs : QSemantics)
    [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    {k : ℕ} (i : Fin k) (src dst : ExtReg) (ψ : qs.State) :
    qs.eval (allocChunkGate i src dst ;; deallocChunkGate i src dst) ψ = ψ := by
  unfold allocChunkGate deallocChunkGate
  set n := extraDelta src dst
  by_cases h0 : n = 0
  · simp [h0, qs.eval_seq, qs.eval_id]
  · by_cases htop : isTopChunk i
    · simp [
        h0, htop, qs.eval_seq, ExtensionSemantics.eval_signDealloc_eq_adj, qs.eval_adj_apply
      ]
    · simp [h0, htop, qs.eval_seq, ExtensionSemantics.eval_zeroExtend, ExtensionSemantics.eval_zeroDealloc]

/-- Allocation and deallocation prefixes cancel for any prefix length. -/
lemma alloc_dealloc_aux_cancel
    (qs : QSemantics)
    [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    {k : ℕ}
    (src dst : LayoutState k)
    (n : ℕ) (hn : n ≤ k)
    (ψ : qs.State) :
    qs.eval
      (compileSignedAllocationsAux src dst n hn ;; compileSignedDeallocationsAux src dst n hn)
      ψ = ψ := by
  induction n with
  | zero =>
      simp [compileSignedAllocationsAux_zero, compileSignedDeallocationsAux_zero,
            qs.eval_seq, qs.eval_id]
  | succ n ih =>
      have hn' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      rw [compileSignedAllocationsAux_succ, compileSignedDeallocationsAux_succ]
      set i : Fin k := ⟨n, by omega⟩
      have := allocChunkGate_deallocChunkGate_cancel qs i
      simp at *
      simp [this, ih]

/-- Full allocation followed by full deallocation evaluates to identity. -/
lemma eval_compileSignedDeallocations_alloc_id
    (qs : QSemantics)
    [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    {k : ℕ}
    (src dst : LayoutState k)
    (ψ : qs.State) :
    qs.eval (compileSignedAllocations k src dst ;; compileSignedDeallocations k src dst) ψ = ψ := by
  have := alloc_dealloc_aux_cancel qs (k := k) src dst (n := k) (by simp) ψ
  simp at this
  simp [compileSignedAllocations, compileSignedDeallocations, this]

/-- Deallocation sends an allocated basis ket back to the original basis ket. -/
lemma eval_compileSignedDeallocations_ket_from_alloc
    (qs : QSemantics)
    [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    {k : ℕ}
    (src dst : LayoutState k)
    (b0 bCur : qs.Basis)
    (hAlloc : qs.eval (compileSignedAllocations k src dst) (qs.ket b0) = qs.ket bCur) :
    qs.eval (compileSignedDeallocations k src dst) (qs.ket bCur) = qs.ket b0 := by
  have := eval_compileSignedDeallocations_alloc_id qs (k := k) src dst (QSemantics.ket b0)
  rw [← hAlloc]; simp at this
  simp [this]

/-- Alias of the allocated-ket deallocation theorem with shorter argument names. -/
lemma eval_compileSignedDeallocations_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    {k : ℕ}
    (src dst : LayoutState k)
    (b bAlloc : qs.Basis)
    (hAlloc : qs.eval (compileSignedAllocations k src dst) (qs.ket b) = qs.ket bAlloc) :
    qs.eval (compileSignedDeallocations k src dst) (qs.ket bAlloc) = qs.ket b := by
  have := eval_compileSignedDeallocations_ket_from_alloc qs (k := k) src dst b bAlloc hAlloc
  apply this

/-- Body evaluation followed by deallocation returns the phase scalar on the original basis ket. -/
lemma eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc
    (qs : QSemantics)
    [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k)
    (phi : Angle)
    (pts : List Point)
    (hpts : pts.length = q k)
    (coeff : Fin (q k) → ℚ)
    (src dst : LayoutState k)
    (b0 bMid : qs.Basis)
    (ops : Prog k)
    (hdisj : LayoutSlotsDisjoint dst)
    (hFits :
      ∀ {τ : State k},
        (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
          (∀ j : Fin k,
            FitsSignedWidth (ExtReg.width (dst.xslot j))
              (evalRowX (qs := qs) src (τ j) b0)) ∧
          (∀ j : Fin k,
            FitsSignedWidth (ExtReg.width (dst.zslot j))
              (evalRowZ (qs := qs) src (τ j) b0)))
    (hSafeAdd :
      ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
        ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s)
    (hEnc : EncodesStateFromFits (qs := qs) src dst State.start_state b0 bMid)
    (hAlloc : qs.eval (compileSignedAllocations k src dst) (qs.ket b0) = qs.ket bMid)
    (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
    (run_ops_start_state : run? ops State.start_state = some State.start_state) :
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst (annotatePhaseTermsAux k 0 ops) ;;
         compileSignedDeallocations k src dst)
        (qs.ket bMid)
      = phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) • qs.ket b0 := by
  have hBody :
      qs.eval
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst (annotatePhaseTermsAux k 0 ops))
          (qs.ket bMid)
      = phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) • qs.ket bMid := by
    exact eval_compileAnnotatedOpsToSignedGateAux_of_blocks
      (qs := qs) (k := k) (hk := hk) (phi := phi) (pts := pts) (hpts := hpts) (coeff := coeff)
      (src := src) (dst := dst) (b0 := b0) (bMid := bMid) (ops := ops)
      hdisj hFits hSafeAdd hEnc hB run_ops_start_state
  have hDealloc : qs.eval (compileSignedDeallocations k src dst) (qs.ket bMid) = qs.ket b0 := by
    exact eval_compileSignedDeallocations_ket
      (qs := qs) (src := src) (dst := dst) (b := b0) (bAlloc := bMid) hAlloc
  rw [qs.eval_seq]
  rw [hBody]
  rw [qs.eval_smul]
  rw [hDealloc]

/-- Controlled body evaluation followed by deallocation returns the conditional scalar on the original ket. -/
lemma eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc
    (qs : QSemantics)
    [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (pts : List Point)
    (hpts : pts.length = q k)
    (coeff : Fin (q k) → ℚ)
    (src dst : LayoutState k)
    (b0 bMid : qs.Basis)
    (ops : Prog k)
    (hdisj : LayoutSlotsDisjoint dst)
    (hCtrlOutside : OutsideLayout dst (ExtReg.ofReg (qubitReg ctrl)))
    (hCtrlMid : RegEncoding.bit ctrl bMid = RegEncoding.bit ctrl b0)
    (hFits :
      ∀ {τ : State k},
        (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
          (∀ j : Fin k,
            FitsSignedWidth (ExtReg.width (dst.xslot j))
              (evalRowX (qs := qs) src (τ j) b0)) ∧
          (∀ j : Fin k,
            FitsSignedWidth (ExtReg.width (dst.zslot j))
              (evalRowZ (qs := qs) src (τ j) b0)))
    (hSafeAdd :
      ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
        ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s)
    (hEnc : EncodesStateFromFits (qs := qs) src dst State.start_state b0 bMid)
    (hAlloc : qs.eval (compileSignedAllocations k src dst) (qs.ket b0) = qs.ket bMid)
    (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
    (run_ops_start_state : run? ops State.start_state = some State.start_state) :
    qs.eval
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst (annotatePhaseTermsAux k 0 ops)) ;;
         compileSignedDeallocations k src dst)
        (qs.ket bMid)
      = (if RegEncoding.bit ctrl b0 then
      phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts)
    else
      1) • qs.ket b0 := by
  have hBody :
      qs.eval
          (controlPhaseLeaves ctrl
            (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst (annotatePhaseTermsAux k 0 ops)))
          (qs.ket bMid)
      = (if RegEncoding.bit ctrl b0 then
        phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts)
      else
        1) • qs.ket bMid := by
    exact eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_blocks
      (qs := qs) (k := k) (hk := hk) (ctrl := ctrl) (phi := phi) (pts := pts) (hpts := hpts)
      (coeff := coeff) (src := src) (dst := dst) (b0 := b0) (bMid := bMid) (ops := ops)
      hdisj hCtrlOutside hCtrlMid hFits hSafeAdd hEnc hB run_ops_start_state
  have hDealloc : qs.eval (compileSignedDeallocations k src dst) (qs.ket bMid) = qs.ket b0 := by
    exact eval_compileSignedDeallocations_ket
      (qs := qs) (src := src) (dst := dst) (b := b0) (bAlloc := bMid) hAlloc
  rw [qs.eval_seq]
  rw [hBody]
  rw [qs.eval_smul]
  rw [hDealloc]

end Shor
