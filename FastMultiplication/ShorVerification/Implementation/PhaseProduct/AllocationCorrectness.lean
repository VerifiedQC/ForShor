import FastMultiplication.ShorVerification.Implementation.PhaseProduct.WidthSoundness

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-!
# Phase-Product Allocation Correctness

This file proves that the allocation half of the compiled phase-product circuit
copies each symbolic source chunk into the widened target layout while preserving
the values, outside-layout locality, and clean reserves needed by the remaining
allocation steps. The proof builds from local disjointness/freshness facts, to
single-chunk allocation, to the full allocation prefix induction.
-/

/-! =========================================================
    Section 1: Disjointness, freshness, and source-read helpers

    Allocation relies on one operation touching only the chunk currently being
    grown. These lemmas move between owned-disjointness, active-disjointness,
    freshness of remaining reserve bits, and equality of source chunk reads.
========================================================= -/

/-- Owned-disjointness of extendable registers is symmetric. -/
lemma ExtReg.ownedDisjoint_symm {a b : ExtReg} (h : ExtReg.OwnedDisjoint a b) : ExtReg.OwnedDisjoint b a := by
  exact List.Disjoint.symm h

/-- Owned-disjoint registers have active parts that are disjoint. -/
lemma ExtReg.activeDisjoint_of_ownedDisjoint {a b : ExtReg} (h : ExtReg.OwnedDisjoint a b) : ExtReg.ActiveDisjoint a b := by
  intro q hqa hqb; exact h (List.mem_append_left _ hqa) (List.mem_append_left _ hqb)

/-- Growing the right register preserves active-disjointness from an owned-disjoint left register. -/
lemma ExtReg.activeDisjoint_of_ownedDisjoint_right_grow {a b : ExtReg} (h : ExtReg.OwnedDisjoint a b) (n : ℕ) :
    ExtReg.ActiveDisjoint a (b.grow n) := by
  intro q hqa hqGrow
  have hqb : q ∈ b.ownedQubits := by
    have : q ∈ (b.grow n).ownedQubits := List.mem_append_left _ hqGrow
    simpa [ExtReg.ownedQubits_grow] using this
  exact h (List.mem_append_left _ hqa) hqb

/-- Growing both owned-disjoint registers preserves active-disjointness. -/
lemma ExtReg.activeDisjoint_of_ownedDisjoint_grow_grow {a b : ExtReg} (h : ExtReg.OwnedDisjoint a b) (m n : ℕ) :
    ExtReg.ActiveDisjoint (a.grow m) (b.grow n) := by
  intro q hqGrowA hqGrowB
  have hqa : q ∈ a.ownedQubits := by
    have : q ∈ (a.grow m).ownedQubits := List.mem_append_left _ hqGrowA
    simpa [ExtReg.ownedQubits_grow] using this
  have hqb : q ∈ b.ownedQubits := by
    have : q ∈ (b.grow n).ownedQubits := List.mem_append_left _ hqGrowB
    simpa [ExtReg.ownedQubits_grow] using this
  exact h hqa hqb

/-- Fresh reserve bits of one owned-disjoint register are active-disjoint from a grown other register. -/
lemma ExtReg.activeDisjoint_newBits_of_ownedDisjoint_right_grow
  {a b : ExtReg}
  (h : ExtReg.OwnedDisjoint a b)
  (m n : ℕ) :
    ExtReg.ActiveDisjoint (ExtReg.ofReg (a.newBits m)) (b.grow n) := by
  intro q hqNew hqGrow
  have hqa : q ∈ a.ownedQubits := List.mem_append_right _ (List.mem_of_mem_take hqNew)
  have hqb : q ∈ b.ownedQubits := by
    have : q ∈ (b.grow n).ownedQubits := List.mem_append_left _ hqGrow
    simpa [ExtReg.ownedQubits_grow] using this
  exact h hqa hqb

/-- Reserve freshness still required for chunks whose index is at least `n`. -/
def RemainingClean
  {Basis : Type u} [RegEncoding Basis]
  {k : ℕ} (src : LayoutState k) (need : NeededWidths k)
  (n : ℕ) (b : Basis) : Prop :=
  let Wwork := commonNeededWidth need
  (∀ i : Fin k, n ≤ i.1 → ExtReg.FreshFor (src.xslot i) (Wwork - (src.xslot i).width) b) ∧
  (∀ i : Fin k, n ≤ i.1 → ExtReg.FreshFor (src.zslot i) (Wwork - (src.zslot i).width) b)

/-- At allocation index zero, the workspace hypothesis gives freshness for every chunk. -/
lemma remainingClean_zero_of_workspaceOK
  {Basis : Type u} [RegEncoding Basis]
  {k : ℕ} {src : LayoutState k}
  {need : NeededWidths k} {b : Basis}
    (hwork : CompilerWorkspaceOK src need b) : RemainingClean src need 0 b := by
  dsimp [CompilerWorkspaceOK, LayoutState.CleanForGrowth] at hwork
  rcases hwork with ⟨_hcap, hx, hz⟩
  exact ⟨fun i _ => hx i, fun i _ => hz i⟩

/-- Local preservation of raw values transfers freshness of a disjoint reserve slice. -/
lemma freshFor_of_local_toNat
    {Basis : Type u}
    [RegEncoding Basis]
    {r target : ExtReg}
    {m : ℕ}
    {b b' : Basis}
    (hloc : ∀ e : ExtReg,
        ExtReg.ActiveDisjoint e target → ExtReg.toNat e b' = ExtReg.toNat e b)
    (hdisj : ExtReg.ActiveDisjoint (ExtReg.ofReg (r.newBits m)) target)
    (hfresh : r.FreshFor m b) :
    r.FreshFor m b' := by
  unfold ExtReg.FreshFor FreshZero at *
  calc
    RegEncoding.toNat (r.newBits m) b'
        = ExtReg.toNat (ExtReg.ofReg (r.newBits m)) b' := rfl
    _ = ExtReg.toNat (ExtReg.ofReg (r.newBits m)) b :=
        hloc (ExtReg.ofReg (r.newBits m)) hdisj
    _ = RegEncoding.toNat (r.newBits m) b := rfl
    _ = 0 := hfresh

/-- Equal raw active values give equal signed interpretations. -/
lemma extToInt_eq_of_toNat_eq {Basis : Type u} [RegEncoding Basis] {e : ExtReg} {b₁ b₂ : Basis}
    (h : ExtReg.toNat e b₁ = ExtReg.toNat e b₂) : extToInt e b₁ = extToInt e b₂ := by
  simp [extToInt, h]

/-- Equal raw `x` slot values preserve the mixed signed/unsigned source read. -/
lemma sourceChunkXInt_eq_of_toNat_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    {src : LayoutState k}
    {i : Fin k}
    {b₁ b₂ : qs.Basis}
    (h : ExtReg.toNat (src.xslot i) b₁ =
      ExtReg.toNat (src.xslot i) b₂) :
    sourceChunkXInt (qs := qs) src i b₁ =
      sourceChunkXInt (qs := qs) src i b₂ := by
  unfold sourceChunkXInt
  by_cases htop : isTopChunk i <;>
    simp [htop, extToInt, h]

/-- Equal raw `z` slot values preserve the mixed signed/unsigned source read. -/
lemma sourceChunkZInt_eq_of_toNat_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    {src : LayoutState k}
    {i : Fin k}
    {b₁ b₂ : qs.Basis}
    (h : ExtReg.toNat (src.zslot i) b₁ =
      ExtReg.toNat (src.zslot i) b₂) :
    sourceChunkZInt (qs := qs) src i b₁ =
      sourceChunkZInt (qs := qs) src i b₂ := by
  unfold sourceChunkZInt
  by_cases htop : isTopChunk i <;>
    simp [htop, extToInt, h]

/-- The scanned target `z` slot strictly grows beyond its initial width. -/
lemma extraDelta_zslot_pos
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops)) :
    let stInit := initSignedLayoutState layout
    let stFinal :=
      targetSignedLayoutState stInit
        (scanNeededWidths x z ops)
    0 < extraDelta
      (stInit.zslot i)
      (stFinal.zslot i) := by
  dsimp
  unfold extraDelta
  rw [targetSignedLayoutState_zslot_width_scan layout ops i hcap, stInit_zslot_width layout i]
  have hscan :=
    scanNeededWidths_z_ge_init x z ops i
  have hneed :=
    commonNeededWidth_ge_zneed
      (scanNeededWidths x z ops) i
  omega

/-! =========================================================
    Section 2: Single-chunk allocation correctness

    A single chunk allocation either sign-extends the top chunk or zero-extends
    a lower chunk. In both cases it produces a basis state whose widened slot
    reads as the original source chunk, while registers active-disjoint from the
    grown slot keep their raw values.
========================================================= -/

/-- Correctness of allocating one `x` chunk. -/
lemma eval_allocChunkGate_x_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (ops : Prog k)
  (i : Fin k)
  (bcur : qs.Basis)
  (hcap : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops))
  (hfresh :
    let need := scanNeededWidths x z ops
    let stInit := initSignedLayoutState layout
    ExtReg.FreshFor (stInit.xslot i) (commonNeededWidth need - (stInit.xslot i).width) bcur) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  ∃ bX : qs.Basis,
    qs.eval (allocChunkGate i (stInit.xslot i) (stFinal.xslot i)) (qs.ket bcur)
      =
    qs.ket bX
      ∧
    extToInt (stFinal.xslot i) bX = sourceChunkXInt (qs := qs) stInit i bcur ∧
    (∀ e : ExtReg,
      ExtReg.ActiveDisjoint e (stFinal.xslot i) →
      ExtReg.toNat e bX = ExtReg.toNat e bcur) := by
  dsimp
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  let δ : ℕ := extraDelta (stInit.xslot i) (stFinal.xslot i)
  have hδpos : 0 < δ := by
    simpa [δ, need, stInit, stFinal] using
      extraDelta_xslot_pos layout ops i hcap
  have hδne : δ ≠ 0 := Nat.ne_of_gt hδpos
  have hδeq :
      δ = commonNeededWidth need - (stInit.xslot i).width := by
    unfold δ extraDelta
    rw [targetSignedLayoutState_xslot_width_scan layout ops i hcap]
  have hslot :
      stFinal.xslot i = (stInit.xslot i).grow δ := by
    simpa [stInit, stFinal, need, hδeq] using
      stFinal_xslot_eq_grow layout need i
  have hcapδ :
      (stInit.xslot i).CanGrow δ := by
    simpa [stInit, need, hδeq] using hcap.1 i
  have hfreshδ :
      ExtReg.FreshFor (stInit.xslot i) δ bcur := by
    simpa [stInit, need, hδeq] using hfresh
  by_cases htop : isTopChunk i
  · have hgate :
        allocChunkGate i (stInit.xslot i) (stFinal.xslot i)
          =
        Gate.signExtend (stInit.xslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]
    rcases ExtensionSemantics.eval_signExtend_ket
        (qs := qs)
        (r := stInit.xslot i)
        (n := δ)
        (b := bcur)
        hcapδ
        hfreshδ with
      ⟨bX, hEval0, _hToNat, hWide, hLoc⟩
    refine ⟨bX, ?_, ?_, ?_⟩
    · rw [hgate]
      exact hEval0
    · calc
        extToInt (stFinal.xslot i) bX
            = extToInt ((stInit.xslot i).grow δ) bX := by
                rw [hslot]
        _ = extToInt (stInit.xslot i) bcur := hWide
        _ = sourceChunkXInt (qs := qs) stInit i bcur := by
              unfold sourceChunkXInt
              simp [htop]
    · intro e he
      exact hLoc e (by simpa [stInit, stFinal, need, hslot] using he)
  · have hgate :
        allocChunkGate i (stInit.xslot i) (stFinal.xslot i)
          =
        Gate.zeroExtend (stInit.xslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]
    refine ⟨bcur, ?_, ?_, ?_⟩
    · rw [hgate]
      exact ExtensionSemantics.eval_zeroExtend
        (stInit.xslot i) δ (qs.ket bcur)
    · calc
        extToInt (stFinal.xslot i) bcur
            = extToInt ((stInit.xslot i).grow δ) bcur := by
                rw [hslot]
        _ = (ExtReg.toNat (stInit.xslot i) bcur : ℤ) :=
              ExtReg.extToInt_grow_of_fresh
                (e := stInit.xslot i) (n := δ) (b := bcur)
                hcapδ hfreshδ hδpos
        _ = sourceChunkXInt (qs := qs) stInit i bcur := by
              unfold sourceChunkXInt
              simp [htop]
    · intro e _he
      rfl

/-- Correctness of allocating one `z` chunk. -/
lemma eval_allocChunkGate_z_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (ops : Prog k)
  (i : Fin k)
  (bcur : qs.Basis)
  (hcap : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops))
  (hfresh :
    let need := scanNeededWidths x z ops
    let stInit := initSignedLayoutState layout
    ExtReg.FreshFor
      (stInit.zslot i)
      (commonNeededWidth need - (stInit.zslot i).width)
      bcur) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  ∃ bZ : qs.Basis,
    qs.eval
        (allocChunkGate i (stInit.zslot i) (stFinal.zslot i))
        (qs.ket bcur)
      =
      qs.ket bZ ∧
    extToInt (stFinal.zslot i) bZ =
      sourceChunkZInt (qs := qs) stInit i bcur ∧
    (∀ e : ExtReg,
      ExtReg.ActiveDisjoint e (stFinal.zslot i) →
      ExtReg.toNat e bZ = ExtReg.toNat e bcur) := by
  dsimp
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  let δ : ℕ := extraDelta (stInit.zslot i) (stFinal.zslot i)
  have hδpos : 0 < δ := by
    simpa [δ, need, stInit, stFinal] using
      extraDelta_zslot_pos layout ops i hcap
  have hδne : δ ≠ 0 := Nat.ne_of_gt hδpos
  have hδeq :
      δ = commonNeededWidth need - (stInit.zslot i).width := by
    unfold δ extraDelta
    rw [targetSignedLayoutState_zslot_width_scan layout ops i hcap]
  have hslot :
      stFinal.zslot i = (stInit.zslot i).grow δ := by
    simpa [stInit, stFinal, need, hδeq] using
      stFinal_zslot_eq_grow layout need i
  have hcapδ :
      (stInit.zslot i).CanGrow δ := by
    simpa [stInit, need, hδeq] using hcap.2 i
  have hfreshδ :
      ExtReg.FreshFor (stInit.zslot i) δ bcur := by
    simpa [stInit, need, hδeq] using hfresh
  by_cases htop : isTopChunk i
  · have hgate :
        allocChunkGate i (stInit.zslot i) (stFinal.zslot i)
          =
        Gate.signExtend (stInit.zslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]
    rcases ExtensionSemantics.eval_signExtend_ket
        (qs := qs)
        (r := stInit.zslot i)
        (n := δ)
        (b := bcur)
        hcapδ
        hfreshδ with
      ⟨bZ, hEval0, _hToNat, hWide, hLoc⟩
    refine ⟨bZ, ?_, ?_, ?_⟩
    · rw [hgate]
      exact hEval0
    · calc
        extToInt (stFinal.zslot i) bZ
            = extToInt ((stInit.zslot i).grow δ) bZ := by
                rw [hslot]
        _ = extToInt (stInit.zslot i) bcur := hWide
        _ = sourceChunkZInt (qs := qs) stInit i bcur := by
              unfold sourceChunkZInt
              simp [htop]
    · intro e he
      exact hLoc e (by simpa [stInit, stFinal, need, hslot] using he)
  · have hgate :
        allocChunkGate i (stInit.zslot i) (stFinal.zslot i)
          =
        Gate.zeroExtend (stInit.zslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]
    refine ⟨bcur, ?_, ?_, ?_⟩
    · rw [hgate]
      exact ExtensionSemantics.eval_zeroExtend
        (stInit.zslot i) δ (qs.ket bcur)
    · calc
        extToInt (stFinal.zslot i) bcur
            = extToInt ((stInit.zslot i).grow δ) bcur := by
                rw [hslot]
        _ = (ExtReg.toNat (stInit.zslot i) bcur : ℤ) :=
              ExtReg.extToInt_grow_of_fresh
                (e := stInit.zslot i)
                (n := δ)
                (b := bcur)
                hcapδ
                hfreshδ
                hδpos
        _ = sourceChunkZInt (qs := qs) stInit i bcur := by
              unfold sourceChunkZInt
              simp [htop]
    · intro e _he
      rfl

/-! =========================================================
    Section 3: Prefix allocation induction

    The auxiliary allocation program allocates chunks in increasing order. The
    induction maintains values for allocated slots, source-read stability for
    unallocated slots, and freshness for all remaining reserve slices.
========================================================= -/

/-- Prefix allocation creates a basis state with allocated slot values and remaining cleanliness. -/
lemma eval_compileSignedAllocationsAux_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (ops : Prog k)
  (b : qs.Basis)
  (hworkspace :
    CompilerWorkspaceOK
      (initSignedLayoutState layout)
      (scanNeededWidths x z ops)
      b) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  ∀ (n : ℕ) (hn : n ≤ k),
    ∃ bAlloc : qs.Basis,
      qs.eval (compileSignedAllocationsAux stInit stFinal n hn) (qs.ket b) = qs.ket bAlloc ∧
      (∀ i : Fin k, i.1 < n →
        extToInt (stFinal.xslot i) bAlloc =
          evalRowX (qs := qs) stInit (State.start_state i) b) ∧
      (∀ i : Fin k, i.1 < n →
        extToInt (stFinal.zslot i) bAlloc =
          evalRowZ (qs := qs) stInit (State.start_state i) b) ∧
      (∀ i : Fin k, n ≤ i.1 →
        sourceChunkXInt (qs := qs) stInit i bAlloc =
          sourceChunkXInt (qs := qs) stInit i b) ∧
      (∀ i : Fin k, n ≤ i.1 →
        sourceChunkZInt (qs := qs) stInit i bAlloc =
          sourceChunkZInt (qs := qs) stInit i b) ∧
      RemainingClean stInit need n bAlloc := by
  dsimp
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  let Wwork : ℕ := commonNeededWidth need
  have hcap : stInit.CanGrowToNeeds need := by simpa [stInit, need] using hworkspace.1
  have hInitOwned : stInit.OwnedPairwiseDisjoint := by simpa [stInit] using initSignedLayoutState_owned_disjoint layout
  have hFinalOwned : stFinal.OwnedPairwiseDisjoint := by simpa [stInit, stFinal, need] using targetSignedLayoutState_owned_disjoint layout need
  intro n hn
  induction n with
  | zero =>
      refine ⟨b, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [compileSignedAllocationsAux_zero, QSemantics.eval_id]
      · intro i hi; omega
      · intro i hi; omega
      · intro i _hi; rfl
      · intro i _hi; rfl
      · simpa [stInit, need] using
          remainingClean_zero_of_workspaceOK
            (src := initSignedLayoutState layout)
            (need := scanNeededWidths x z ops)
            (b := b)
            hworkspace
  | succ n ih =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let idx : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      rcases ih hk' with
        ⟨bMid, hMidEval, hMidX, hMidZ, hKeepX, hKeepZ, hCleanMid⟩
      have hxFresh : ExtReg.FreshFor (stInit.xslot idx) (Wwork - (stInit.xslot idx).width) bMid := by
        simpa [RemainingClean, Wwork] using hCleanMid.1 idx (by simp [idx])
      rcases
        eval_allocChunkGate_x_ket
          (qs := qs)
          (layout := layout)
          (ops := ops)
          (i := idx)
          (bcur := bMid)
          hcap
          (by simpa [stInit, need, Wwork] using hxFresh) with
        ⟨bX, hXEval, hXVal, hXLoc⟩
      have hXSlot : stFinal.xslot idx = (stInit.xslot idx).grow (Wwork - (stInit.xslot idx).width) := by
        simpa [stInit, stFinal, need, Wwork] using stFinal_xslot_eq_grow layout need idx
      have hzFreshMid : ExtReg.FreshFor (stInit.zslot idx) (Wwork - (stInit.zslot idx).width) bMid := by
        simpa [RemainingClean, Wwork] using hCleanMid.2 idx (by simp [idx])
      have hzFreshX :
          ExtReg.FreshFor
            (stInit.zslot idx)
            (Wwork - (stInit.zslot idx).width)
            bX := by
        have howned :
            ExtReg.OwnedDisjoint
              (stInit.zslot idx)
              (stInit.xslot idx) := by
          exact ExtReg.ownedDisjoint_symm (hInitOwned.2.2 idx idx)
        apply freshFor_of_local_toNat (r := stInit.zslot idx) hXLoc
        · simpa [hXSlot] using
            ExtReg.activeDisjoint_newBits_of_ownedDisjoint_right_grow
              howned
              (Wwork - (stInit.zslot idx).width)
              (Wwork - (stInit.xslot idx).width)
        · exact hzFreshMid
      rcases
        eval_allocChunkGate_z_ket
          (qs := qs)
          (layout := layout)
          (ops := ops)
          (i := idx)
          (bcur := bX)
          hcap
          (by simpa [stInit, need, Wwork] using hzFreshX) with
        ⟨bAlloc, hZEval, hZVal, hZLoc⟩
      have hZSlot : stFinal.zslot idx = (stInit.zslot idx).grow (Wwork - (stInit.zslot idx).width) := by
        simpa [stInit, stFinal, need, Wwork] using stFinal_zslot_eq_grow layout need idx
      refine ⟨bAlloc, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [compileSignedAllocationsAux_succ (src := stInit) (dst := stFinal) (n := n) (hn := hn)]
        rw [QSemantics.eval_seq, hMidEval, QSemantics.eval_seq, hXEval]
        simpa [QSemantics.eval_seq, hk', idx] using hZEval
      · intro j hj
        by_cases hji : j = idx
        · subst hji
          calc
            extToInt (stFinal.xslot idx) bAlloc
                = extToInt (stFinal.xslot idx) bX := by
                    apply extToInt_eq_of_toNat_eq
                    exact hZLoc (stFinal.xslot idx)
                      (ExtReg.activeDisjoint_of_ownedDisjoint
                        (hFinalOwned.2.2 idx idx))
            _ = sourceChunkXInt (qs := qs) stInit idx bMid := hXVal
            _ = sourceChunkXInt (qs := qs) stInit idx b := hKeepX idx (by simp [idx])
            _ = evalRowX (qs := qs) stInit (State.start_state idx) b := by
                  symm
                  simpa using evalRowX_start_state (qs := qs) stInit idx b
        · have hjn : j.1 < n := by
            have hjne : j.1 ≠ n := by intro hEq; exact hji (Fin.ext (by simpa [idx] using hEq))
            omega
          calc
            extToInt (stFinal.xslot j) bAlloc
                = extToInt (stFinal.xslot j) bX := by
                    apply extToInt_eq_of_toNat_eq
                    exact hZLoc (stFinal.xslot j)
                      (ExtReg.activeDisjoint_of_ownedDisjoint
                        (hFinalOwned.2.2 j idx))
            _ = extToInt (stFinal.xslot j) bMid := by
                  apply extToInt_eq_of_toNat_eq
                  exact hXLoc (stFinal.xslot j)
                    (ExtReg.activeDisjoint_of_ownedDisjoint
                      (hFinalOwned.1 j idx hji))
            _ = evalRowX (qs := qs) stInit (State.start_state j) b :=
                  hMidX j hjn
      · intro j hj
        by_cases hji : j = idx
        · subst hji
          calc
            extToInt (stFinal.zslot idx) bAlloc
                = sourceChunkZInt (qs := qs) stInit idx bX := hZVal
            _ = sourceChunkZInt (qs := qs) stInit idx bMid := by
                  apply sourceChunkZInt_eq_of_toNat_eq (qs := qs)
                  exact hXLoc (stInit.zslot idx)
                    (by
                      simpa [hXSlot] using
                        ExtReg.activeDisjoint_of_ownedDisjoint_right_grow
                          (ExtReg.ownedDisjoint_symm
                            (hInitOwned.2.2 idx idx))
                          (Wwork - (stInit.xslot idx).width))
            _ = sourceChunkZInt (qs := qs) stInit idx b :=
                  hKeepZ idx (by simp [idx])
            _ = evalRowZ (qs := qs) stInit (State.start_state idx) b := by
                  symm
                  simpa using evalRowZ_start_state (qs := qs) stInit idx b
        · have hjn : j.1 < n := by
            have hjne : j.1 ≠ n := by intro hEq; exact hji (Fin.ext (by simpa [idx] using hEq))
            omega
          calc
            extToInt (stFinal.zslot j) bAlloc
                = extToInt (stFinal.zslot j) bX := by
                    apply extToInt_eq_of_toNat_eq
                    exact hZLoc (stFinal.zslot j)
                      (ExtReg.activeDisjoint_of_ownedDisjoint
                        (hFinalOwned.2.1 j idx hji))
            _ = extToInt (stFinal.zslot j) bMid := by
                  apply extToInt_eq_of_toNat_eq
                  exact hXLoc (stFinal.zslot j)
                    (ExtReg.activeDisjoint_of_ownedDisjoint
                      (ExtReg.ownedDisjoint_symm
                        (hFinalOwned.2.2 idx j)))
            _ = evalRowZ (qs := qs) stInit (State.start_state j) b :=
                  hMidZ j hjn
      · intro j hj
        have hjne : j ≠ idx := by intro h; subst h; simp [idx] at hj
        calc
          sourceChunkXInt (qs := qs) stInit j bAlloc
              = sourceChunkXInt (qs := qs) stInit j bX := by
                  apply sourceChunkXInt_eq_of_toNat_eq (qs := qs)
                  exact hZLoc (stInit.xslot j)
                    (by
                      simpa [hZSlot] using
                        ExtReg.activeDisjoint_of_ownedDisjoint_right_grow
                          (hInitOwned.2.2 j idx)
                          (Wwork - (stInit.zslot idx).width))
          _ = sourceChunkXInt (qs := qs) stInit j bMid := by
                apply sourceChunkXInt_eq_of_toNat_eq (qs := qs)
                exact hXLoc (stInit.xslot j)
                  (by
                    simpa [hXSlot] using
                      ExtReg.activeDisjoint_of_ownedDisjoint_right_grow
                        (hInitOwned.1 j idx hjne)
                        (Wwork - (stInit.xslot idx).width))
          _ = sourceChunkXInt (qs := qs) stInit j b := hKeepX j (by omega)
      · intro j hj
        have hjne : j ≠ idx := by intro h; subst h; simp [idx] at hj
        calc
          sourceChunkZInt (qs := qs) stInit j bAlloc
              = sourceChunkZInt (qs := qs) stInit j bX := by
                  apply sourceChunkZInt_eq_of_toNat_eq (qs := qs)
                  exact hZLoc (stInit.zslot j)
                    (by
                      simpa [hZSlot] using
                        ExtReg.activeDisjoint_of_ownedDisjoint_right_grow
                          (hInitOwned.2.1 j idx hjne)
                          (Wwork - (stInit.zslot idx).width))
          _ = sourceChunkZInt (qs := qs) stInit j bMid := by
                apply sourceChunkZInt_eq_of_toNat_eq (qs := qs)
                exact hXLoc (stInit.zslot j)
                  (by
                    simpa [hXSlot] using
                      ExtReg.activeDisjoint_of_ownedDisjoint_right_grow
                        (ExtReg.ownedDisjoint_symm
                          (hInitOwned.2.2 idx j))
                        (Wwork - (stInit.xslot idx).width))
          _ = sourceChunkZInt (qs := qs) stInit j b := hKeepZ j (by omega)
      · constructor
        · intro j hj
          have hjne : j ≠ idx := by intro h; subst h; simp [idx] at hj
          have hf0 : ExtReg.FreshFor
              (stInit.xslot j)
              (Wwork - (stInit.xslot j).width)
              bMid := hCleanMid.1 j (by omega)
          have hfX : ExtReg.FreshFor
              (stInit.xslot j)
              (Wwork - (stInit.xslot j).width)
              bX := by
            apply freshFor_of_local_toNat (r := stInit.xslot j) hXLoc
            · simpa [hXSlot] using
                ExtReg.activeDisjoint_newBits_of_ownedDisjoint_right_grow
                  (hInitOwned.1 j idx hjne)
                  (Wwork - (stInit.xslot j).width)
                  (Wwork - (stInit.xslot idx).width)
            · exact hf0
          apply freshFor_of_local_toNat (r := stInit.xslot j) hZLoc
          · simpa [hZSlot] using
              ExtReg.activeDisjoint_newBits_of_ownedDisjoint_right_grow
                (hInitOwned.2.2 j idx)
                (Wwork - (stInit.xslot j).width)
                (Wwork - (stInit.zslot idx).width)
          · exact hfX
        · intro j hj
          have hjne : j ≠ idx := by intro h; subst h; simp [idx] at hj
          have hf0 : ExtReg.FreshFor
              (stInit.zslot j)
              (Wwork - (stInit.zslot j).width)
              bMid := hCleanMid.2 j (by omega)
          have hfX : ExtReg.FreshFor
              (stInit.zslot j)
              (Wwork - (stInit.zslot j).width)
              bX := by
            apply freshFor_of_local_toNat (r := stInit.zslot j) hXLoc
            · simpa [hXSlot] using
                ExtReg.activeDisjoint_newBits_of_ownedDisjoint_right_grow
                  (ExtReg.ownedDisjoint_symm
                    (hInitOwned.2.2 idx j))
                  (Wwork - (stInit.zslot j).width)
                  (Wwork - (stInit.xslot idx).width)
            · exact hf0
          apply freshFor_of_local_toNat (r := stInit.zslot j) hZLoc
          · simpa [hZSlot] using
              ExtReg.activeDisjoint_newBits_of_ownedDisjoint_right_grow
                (hInitOwned.2.1 j idx hjne)
                (Wwork - (stInit.zslot j).width)
                (Wwork - (stInit.zslot idx).width)
          · exact hfX

/-- Prefix allocation preserves all registers outside the final layout. -/
lemma eval_compileSignedAllocationsAux_sameOutside
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (ops : Prog k)
  (b : qs.Basis)
  (hworkspace :
    CompilerWorkspaceOK
      (initSignedLayoutState layout)
      (scanNeededWidths x z ops)
      b) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  ∀ (n : ℕ) (hn : n ≤ k),
    ∃ bAlloc : qs.Basis,
      qs.eval (compileSignedAllocationsAux stInit stFinal n hn) (qs.ket b) = qs.ket bAlloc ∧
      SameOutsideLayout qs stFinal b bAlloc := by
  dsimp
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  have hmain :=
    eval_compileSignedAllocationsAux_ket
      (qs := qs)
      (layout := layout)
      (ops := ops)
      (b := b)
      hworkspace
  intro n hn
  induction n with
  | zero =>
      refine ⟨b, ?_, ?_⟩
      · simp [compileSignedAllocationsAux_zero, QSemantics.eval_id]
      · exact SameOutsideLayout.refl qs stFinal b
  | succ n ih =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let idx : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      rcases hmain n hk' with
        ⟨bMid, hMidEval, _hMidX, _hMidZ, _hKeepX, _hKeepZ, hCleanMid⟩
      rcases ih hk' with ⟨bMid', hMidEval', hMidSO⟩
      have hbMid : bMid' = bMid := by
        apply qs.ket_inj
        rw [← hMidEval, ← hMidEval']
      subst bMid'
      have hcap : stInit.CanGrowToNeeds need := by simpa [stInit, need] using hworkspace.1
      let Wwork : ℕ := commonNeededWidth need
      have hxFresh : ExtReg.FreshFor (stInit.xslot idx) (Wwork - (stInit.xslot idx).width) bMid := by
        simpa [RemainingClean, Wwork] using hCleanMid.1 idx (by simp [idx])
      rcases
        eval_allocChunkGate_x_ket
          (qs := qs)
          (layout := layout)
          (ops := ops)
          (i := idx)
          (bcur := bMid)
          hcap
          (by simpa [stInit, need, Wwork] using hxFresh) with
        ⟨bX, hXEval, _hXVal, hXLoc⟩
      have hInitOwned : stInit.OwnedPairwiseDisjoint := by simpa [stInit] using initSignedLayoutState_owned_disjoint layout
      have hXSlot : stFinal.xslot idx = (stInit.xslot idx).grow (Wwork - (stInit.xslot idx).width) := by
        simpa [stInit, stFinal, need, Wwork] using stFinal_xslot_eq_grow layout need idx
      have hzFreshMid : ExtReg.FreshFor (stInit.zslot idx) (Wwork - (stInit.zslot idx).width) bMid := by
        simpa [RemainingClean, Wwork] using hCleanMid.2 idx (by simp [idx])
      have hzFreshX :
          ExtReg.FreshFor
            (stInit.zslot idx)
            (Wwork - (stInit.zslot idx).width)
            bX := by
        apply freshFor_of_local_toNat (r := stInit.zslot idx) hXLoc
        · simpa [hXSlot] using
            ExtReg.activeDisjoint_newBits_of_ownedDisjoint_right_grow
              (ExtReg.ownedDisjoint_symm (hInitOwned.2.2 idx idx))
              (Wwork - (stInit.zslot idx).width)
              (Wwork - (stInit.xslot idx).width)
        · exact hzFreshMid
      rcases
        eval_allocChunkGate_z_ket
          (qs := qs)
          (layout := layout)
          (ops := ops)
          (i := idx)
          (bcur := bX)
          hcap
          (by simpa [stInit, need, Wwork] using hzFreshX) with
        ⟨bAlloc, hZEval, _hZVal, hZLoc⟩
      refine ⟨bAlloc, ?_, ?_⟩
      · rw [compileSignedAllocationsAux_succ (src := stInit) (dst := stFinal) (n := n) (hn := hn)]
        rw [QSemantics.eval_seq, hMidEval, QSemantics.eval_seq, hXEval]
        simpa [QSemantics.eval_seq, hk', idx] using hZEval
      ·
        have hXSO : SameOutsideLayout qs stFinal bMid bX := by
          intro e he
          apply extToInt_eq_of_toNat_eq
          symm
          exact hXLoc e (he.1 idx)
        have hZSO : SameOutsideLayout qs stFinal bX bAlloc := by
          intro e he
          apply extToInt_eq_of_toNat_eq
          symm
          exact hZLoc e (he.2 idx)
        exact SameOutsideLayout.trans (qs := qs)
          (SameOutsideLayout.trans (qs := qs) hMidSO hXSO) hZSO

/-! =========================================================
    Section 4: Public allocation theorems
========================================================= -/

/-- The full allocation program establishes the start-state encoding in the final layout. -/
lemma eval_compileSignedAllocations_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (ops : Prog k)
  (b : qs.Basis)
  (hworkspace :
    CompilerWorkspaceOK
      (initSignedLayoutState layout)
      (scanNeededWidths x z ops)
      b) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  ∃ bAlloc : qs.Basis,
    qs.eval (compileSignedAllocations k stInit stFinal) (qs.ket b) = qs.ket bAlloc ∧
    EncodesStateFrom (qs := qs) stInit stFinal State.start_state b bAlloc := by
  dsimp [compileSignedAllocations]
  rcases
    eval_compileSignedAllocationsAux_ket
      (qs := qs)
      (layout := layout)
      (ops := ops)
      (b := b)
      hworkspace
      k le_rfl with
    ⟨bAlloc, hEval, hX, hZ, _hKeepX, _hKeepZ, _hClean⟩
  refine ⟨bAlloc, hEval, ?_⟩
  exact ⟨fun i => hX i i.is_lt, fun i => hZ i i.is_lt⟩

/-- The full allocation program preserves all outside-layout registers. -/
lemma eval_compileSignedAllocations_sameOutside
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (ops : Prog k)
  (b : qs.Basis)
  (hworkspace :
    CompilerWorkspaceOK
      (initSignedLayoutState layout)
      (scanNeededWidths x z ops)
      b) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  ∃ bAlloc : qs.Basis,
    qs.eval (compileSignedAllocations k stInit stFinal) (qs.ket b) = qs.ket bAlloc ∧
    SameOutsideLayout qs stFinal b bAlloc := by
  dsimp [compileSignedAllocations]
  exact
    eval_compileSignedAllocationsAux_sameOutside
      (qs := qs)
      (layout := layout)
      (ops := ops)
      (b := b)
      hworkspace
      k le_rfl

/-- Full allocation establishes encoding plus signed-fit obligations for every target slot. -/
lemma eval_compileSignedAllocations_ket_fits
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (ops : Prog k)
  (b : qs.Basis)
  (hworkspace : CompilerWorkspaceOK (initSignedLayoutState layout) (scanNeededWidths x z ops) b) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  ∃ bAlloc : qs.Basis,
    qs.eval (compileSignedAllocations k stInit stFinal) (qs.ket b) = qs.ket bAlloc ∧
    EncodesStateFromFits (qs := qs) stInit stFinal State.start_state b bAlloc := by
  have hAlloc :=
    eval_compileSignedAllocations_ket
      (qs := qs)
      (layout := layout)
      (ops := ops)
      (b := b)
      hworkspace
  rcases hAlloc with ⟨bAlloc, hEval, hEnc⟩
  have hFits :
      let src := initSignedLayoutState layout
      let dst :=
        targetSignedLayoutState
          src
          (scanNeededWidths x z ops)
      (∀ i : Fin k,
        FitsSignedWidth (ExtReg.width (dst.xslot i))
          (evalRowX (qs := qs) src (State.start_state i) b)) ∧
      (∀ i : Fin k,
        FitsSignedWidth (ExtReg.width (dst.zslot i))
          (evalRowZ (qs := qs) src (State.start_state i) b)) := by
    exact allocated_widths_sound
      (qs := qs)
      layout
      ops
      hworkspace.1
      b
      (σ := State.start_state)
      ⟨[], ops, by simp, by simp [run?]⟩
  refine ⟨bAlloc, hEval, ?_⟩
  dsimp at hFits
  exact ⟨hEnc, hFits.1, hFits.2⟩

end Shor
