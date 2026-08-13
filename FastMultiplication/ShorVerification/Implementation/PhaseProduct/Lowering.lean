import FastMultiplication.ShorVerification.Implementation.PhaseProduct.LoweringCorrectness.Linearity
import FastMultiplication.ShorVerification.Implementation.GateSemanticsLemmas

namespace Shor
open Gate
open Operations

/-!
# Phase-Product Workspace Correctness

This file moves reserve-cleanliness facts through the concrete layouts created
by recursive phase-product lowering. Its main result shows that signed
allocation produces a fitted target encoding while leaving every child reserve
clean for later recursive calls.

Main declarations:

* `FreshZero.of_subset` and
  `PhaseSplitLayout.child_newBits_subset_parent_reserve` move reserve-zero
  facts along the allocation layout.
* `compilerWorkspaceOK_of_recursiveWorkspaceCleanBasis` turns root reserve
  cleanliness into the compiler workspace invariant.
* `eval_compileSignedAllocations_ket_fits_and_child_clean` is the final theorem:
  allocation both fits the target layout and preserves recursive reserve
  cleanliness for every child.
-/

/-! =========================================================
    Section 1: Moving reserve-cleanliness facts between layouts
    Allocation creates child layouts inside the parent's reserve. These lemmas
    move fresh-zero facts across subsets and turn the static layout/capacity
    proofs into the concrete cleanliness hypotheses required by recursive calls.
========================================================= -/

/--
If every qubit of `big` is zero and every qubit of `small` belongs to `big`,
then `small` is also zero.
-/
lemma FreshZero.of_subset
    {Basis : Type u}
    [RegEncoding Basis]
    (small big : Reg)
    (b : Basis)
    (hsub : ∀ q : ℕ, q ∈ small.qubits → q ∈ big.qubits)
    (hzero : FreshZero big b) :
    FreshZero small b := by
  unfold FreshZero at hzero ⊢
  apply Nat.zero_of_testBit_eq_false
  intro j
  by_cases hj : j < regSize small
  · let iSmall : Fin (regSize small) :=
      ⟨j, hj⟩
    let q : ℕ :=
      small.get iSmall
    have hqSmall :
        q ∈ small.qubits := by
      dsimp [q, iSmall, Reg.get]
      exact List.get_mem small.qubits _
    have hqBig :
        q ∈ big.qubits :=
      hsub q hqSmall
    let jBig : ℕ :=
      big.qubits.idxOf q
    have hjBig :
        jBig < big.qubits.length := by
      exact
        List.idxOf_lt_length_of_mem
          hqBig
    let iBig : Fin (regSize big) :=
      ⟨
        jBig,
        by
          simpa [
            jBig,
            regSize,
            Reg.width
          ] using hjBig
      ⟩
    have hgetBig :
        big.get iBig = q := by
      simp [
        Reg.get,
        iBig,
        jBig,
        q,
        List.getElem_idxOf
      ]
    calc
      Nat.testBit
          (RegEncoding.toNat small b)
          j
          =
        RegEncoding.bit q b := by
          symm
          simpa [q, iSmall] using
            RegEncoding.bit_eq_testBit_toNat
              small b iSmall
      _ =
        RegEncoding.bit (big.get iBig) b := by
          rw [hgetBig]
      _ =
        Nat.testBit
          (RegEncoding.toNat big b)
          iBig.1 :=
        RegEncoding.bit_eq_testBit_toNat
          big b iBig
      _ = false := by
        rw [hzero]
        simp
  · have hwidth :
        regSize small ≤ j :=
      Nat.le_of_not_gt hj
    have hToNat :
        RegEncoding.toNat small b
          <
        2 ^ regSize small := by
      simpa [ASize] using
        RegEncoding.toNat_lt_ASize
          (r := small)
          (b := b)
    have hpow :
        2 ^ regSize small ≤ 2 ^ j := by
      exact
        Nat.pow_le_pow_right
          (by omega)
          hwidth
    exact
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hToNat hpow)

/-- New reserve bits introduced for a child layout are contained in the parent reserve. -/
lemma PhaseSplitLayout.child_newBits_subset_parent_reserve
    {parent : ExtReg}
    {k W : ℕ}
    (layout : PhaseSplitLayout parent k W)
    (i : Fin k)
    (n : ℕ)
    (qbit : ℕ)
    (hq : qbit ∈ ((layout.child i).newBits n).qubits) :
    qbit ∈ parent.reserve.qubits := by
  have hqChildReserve :
      qbit ∈ (layout.reserve i).qubits := by
    apply List.mem_of_mem_take
    simpa [
      PhaseSplitLayout.child,
      ExtReg.newBits,
      ExtReg.withReserve,
      Reg.take
    ] using hq
  have hqFlatten :
      qbit ∈
        (List.ofFn fun j : Fin k =>
          (layout.reserve j).qubits).flatten := by
    rw [List.mem_flatten]
    refine
      ⟨
        (layout.reserve i).qubits,
        ?_,
        hqChildReserve
      ⟩
    simp
  rw [layout.reserve_partition] at hqFlatten
  exact hqFlatten

/-! =========================================================
    Section 2: Root reserve cleanliness to compiler workspace cleanliness

    These lemmas translate from compact recursive cleanliness on the input
    operands to the detailed compiler invariant expected by allocation
    correctness.
========================================================= -/

/-- A complete `FreshFor` proof makes every reserve bit of the target layout zero. -/
lemma freshZero_reserve_of_freshFor_capacity
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg)
    (b : Basis)
    (hclean :
      ExtReg.FreshFor e e.capacity b) :
    FreshZero e.reserve b := by
  have hnewBits :
      e.newBits e.capacity = e.reserve := by
    cases e with
    | mk active reserve hdisj =>
      cases reserve with
      | mk qubits nodup =>
        simp [
          ExtReg.newBits,
          ExtReg.capacity,
          Reg.take,
          regSize,
          Reg.width
        ]
  simpa [
    ExtReg.FreshFor,
    hnewBits
  ] using hclean

/-- Recursive reserve cleanliness supplies the compiler workspace invariant for one allocation layer. -/
lemma compilerWorkspaceOK_of_recursiveWorkspaceCleanBasis
    {Basis : Type u}
    [RegEncoding Basis]
    {k : ℕ}
    (ops : Prog k)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hcapacity : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops))
    (b : Basis)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    CompilerWorkspaceOK (initSignedLayoutState layout) (scanNeededWidths x z ops) b := by
  let src : LayoutState k :=
    initSignedLayoutState layout
  let need : NeededWidths k :=
    scanNeededWidths x z ops
  let Wwork : ℕ :=
    commonNeededWidth need
  have hxReserve :
      FreshZero x.reserve b := by
    exact
      freshZero_reserve_of_freshFor_capacity
        (e := x)
        (b := b)
        hclean.1
  have hzReserve :
      FreshZero z.reserve b := by
    exact
      freshZero_reserve_of_freshFor_capacity
        (e := z)
        (b := b)
        hclean.2
  change
    src.CanGrowTo Wwork ∧
    src.CleanForGrowth Wwork b
  constructor
  · simpa [
      src,
      need,
      Wwork,
      LayoutState.CanGrowToNeeds
    ] using hcapacity
  · constructor
    · intro i
      change
        ExtReg.FreshFor
          (layout.xSplit.child i)
          (Wwork -
            (layout.xSplit.child i).width)
          b
      unfold ExtReg.FreshFor
      apply FreshZero.of_subset
        (small :=
          (layout.xSplit.child i).newBits
            (Wwork -
              (layout.xSplit.child i).width))
        (big := x.reserve)
        (b := b)
      · exact
          PhaseSplitLayout.child_newBits_subset_parent_reserve
            layout.xSplit
            i
            (Wwork -
              (layout.xSplit.child i).width)
      · exact hxReserve
    · intro i
      change
        ExtReg.FreshFor
          (layout.zSplit.child i)
          (Wwork -
            (layout.zSplit.child i).width)
          b
      unfold ExtReg.FreshFor
      apply FreshZero.of_subset
        (small :=
          (layout.zSplit.child i).newBits
            (Wwork -
              (layout.zSplit.child i).width))
        (big := z.reserve)
        (b := b)
      · exact
          PhaseSplitLayout.child_newBits_subset_parent_reserve
            layout.zSplit
            i
            (Wwork -
              (layout.zSplit.child i).width)
      · exact hzReserve

/-- Basis-ket form of the compiler workspace cleanliness consequence. -/
lemma cleanWorkspaceState_ket_of_recursiveWorkspaceCleanBasis
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hcapacity : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops))
    (b : qs.Basis)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    CleanWorkspaceState  qs (initSignedLayoutState layout) (scanNeededWidths x z ops) (qs.ket b) := by
  exact
    CleanClosure.ket b (compilerWorkspaceOK_of_recursiveWorkspaceCleanBasis ops x z layout hcapacity b hclean)

/-! =========================================================
    Section 3: Main allocation theorem
========================================================= -/

/--
Main theorem for this file.

After `compileSignedAllocations` runs on a clean basis state, the resulting
basis state fits the target layout and every child `(xslot i, zslot i)` still
has clean recursive reserve workspace. This is the allocation cleanliness fact
used by recursive phase-product lowering.
-/
lemma eval_compileSignedAllocations_ket_fits_and_child_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {k : ℕ}
    (ops : Prog k)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (b : qs.Basis)
    (hworkspace : CompilerWorkspaceOK (initSignedLayoutState layout) (scanNeededWidths x z ops) b)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    let src := initSignedLayoutState layout
    let dst := targetSignedLayoutState src (scanNeededWidths x z ops)
    ∃ bAlloc : qs.Basis,
      qs.eval (compileSignedAllocations k src dst) (qs.ket b)
        =
      qs.ket bAlloc
      ∧
      EncodesStateFromFits qs src dst State.start_state b bAlloc
      ∧
      ∀ b' : qs.Basis,
        SameOutsideLayout qs dst bAlloc b' →
        ∀ i : Fin k,
          RecursiveWorkspaceCleanBasis (dst.xslot i) (dst.zslot i) b' := by
  let src : LayoutState k :=
    initSignedLayoutState layout
  let need : NeededWidths k :=
    scanNeededWidths x z ops
  let dst : LayoutState k :=
    targetSignedLayoutState src need
  change
    ∃ bAlloc : qs.Basis,
      qs.eval
          (compileSignedAllocations k src dst)
          (qs.ket b)
        =
      qs.ket bAlloc
      ∧
      EncodesStateFromFits
        qs src dst State.start_state b bAlloc
      ∧
      ∀ b' : qs.Basis,
        SameOutsideLayout qs dst bAlloc b' →
        ∀ i : Fin k,
          RecursiveWorkspaceCleanBasis
            (dst.xslot i)
            (dst.zslot i)
            b'
  rcases
      eval_compileSignedAllocations_ket_fits
        (qs := qs)
        (layout := layout)
        (ops := ops)
        (b := b)
        hworkspace
    with
      ⟨bAlloc, hEval, hEnc⟩
  rcases
      eval_compileSignedAllocations_sameOutside
        (qs := qs)
        (layout := layout)
        (ops := ops)
        (b := b)
        hworkspace
    with
      ⟨bOutside, hEvalOutside, hOutside⟩
  have hbOutside :
      bOutside = bAlloc := by
    apply qs.ket_inj
    rw [← hEval, ← hEvalOutside]
  subst bOutside
  have hOwned :
      dst.OwnedPairwiseDisjoint := by
    simpa [src, dst, need] using
      targetSignedLayoutState_owned_disjoint
        layout
        need
  have hxRootZero :
      FreshZero x.reserve b :=
    freshZero_reserve_of_freshFor_capacity
      x b hclean.1
  have hzRootZero :
      FreshZero z.reserve b :=
    freshZero_reserve_of_freshFor_capacity
      z b hclean.2
  have outsideXReserve :
      ∀ (i : Fin k) (qbit : ℕ),
        qbit ∈ (dst.xslot i).reserve.qubits →
        OutsideLayout
          dst
          (ExtReg.ofReg (qubitReg qbit)) := by
    intro i qbit hqReserve
    constructor
    · intro j
      rw [
        ExtReg.ActiveDisjoint,
        Disjoint,
        List.disjoint_left
      ]
      intro q hqSingleton hqActive
      simp [
        ExtReg.ofReg,
        qubitReg,
        Reg.singleton
      ] at hqSingleton
      subst q
      by_cases hij : i = j
      · subst j
        exact
          (dst.xslot i).active_reserve_disjoint
            hqActive
            hqReserve
      · exact
          hOwned.1 i j hij
            (List.mem_append_right _ hqReserve)
            (List.mem_append_left _ hqActive)
    · intro j
      rw [
        ExtReg.ActiveDisjoint,
        Disjoint,
        List.disjoint_left
      ]
      intro q hqSingleton hqActive
      simp [
        ExtReg.ofReg,
        qubitReg,
        Reg.singleton
      ] at hqSingleton
      subst q
      exact
        hOwned.2.2 i j
          (List.mem_append_right _ hqReserve)
          (List.mem_append_left _ hqActive)
  have outsideZReserve :
      ∀ (i : Fin k) (qbit : ℕ),
        qbit ∈ (dst.zslot i).reserve.qubits →
        OutsideLayout
          dst
          (ExtReg.ofReg (qubitReg qbit)) := by
    intro i qbit hqReserve
    constructor
    · intro j
      rw [
        ExtReg.ActiveDisjoint,
        Disjoint,
        List.disjoint_left
      ]
      intro q hqSingleton hqActive
      simp [
        ExtReg.ofReg,
        qubitReg,
        Reg.singleton
      ] at hqSingleton
      subst q
      exact
        hOwned.2.2 j i
          (List.mem_append_left _ hqActive)
          (List.mem_append_right _ hqReserve)
    · intro j
      rw [
        ExtReg.ActiveDisjoint,
        Disjoint,
        List.disjoint_left
      ]
      intro q hqSingleton hqActive
      simp [
        ExtReg.ofReg,
        qubitReg,
        Reg.singleton
      ] at hqSingleton
      subst q
      by_cases hij : i = j
      · subst j
        exact
          (dst.zslot i).active_reserve_disjoint
            hqActive
            hqReserve
      · exact
          hOwned.2.1 i j hij
            (List.mem_append_right _ hqReserve)
            (List.mem_append_left _ hqActive)
  refine ⟨bAlloc, hEval, hEnc, ?_⟩
  intro b' hAllocOutside i
  have hOutsideTotal :
      SameOutsideLayout qs dst b b' :=
    SameOutsideLayout.trans
      (qs := qs)
      hOutside
      hAllocOutside
  constructor
  · unfold ExtReg.FreshFor
    have hZeroInOriginal :
        FreshZero
          ((dst.xslot i).newBits
            (dst.xslot i).capacity)
          b := by
      apply FreshZero.of_subset
        (((dst.xslot i).newBits
          (dst.xslot i).capacity))
        x.reserve
        b
        ?_
        hxRootZero
      intro qbit hqNew
      have hqTargetReserve :
          qbit ∈
            (dst.xslot i).reserve.qubits := by
        exact List.mem_of_mem_take hqNew
      have hqDropped :
          qbit ∈
            List.drop
              (commonNeededWidth need -
                (layout.xSplit.child i).width)
              (layout.xSplit.child i).reserve.qubits := by
        simpa [
          dst,
          src,
          targetSignedLayoutState,
          growExtRegTo,
          ExtReg.grow,
          ExtReg.remainingReserve,
          Reg.drop
        ] using hqTargetReserve
      have hqChildReserve :
          qbit ∈
            (layout.xSplit.child i).reserve.qubits :=
        List.mem_of_mem_drop hqDropped
      apply
        PhaseSplitLayout.child_newBits_subset_parent_reserve
          layout.xSplit
          i
          (layout.xSplit.child i).capacity
      simpa [
        ExtReg.newBits,
        ExtReg.capacity,
        Reg.take,
        regSize,
        Reg.width
      ] using hqChildReserve
    apply
      FreshZero.of_eq_on_bits
        ((dst.xslot i).newBits
          (dst.xslot i).capacity)
        b
        b'
        ?_
        hZeroInOriginal
    intro qbit hqNew
    have hqTargetReserve :
        qbit ∈
          (dst.xslot i).reserve.qubits :=
      List.mem_of_mem_take hqNew
    exact
      SameOutsideLayout.bit_eq_of_outside
        qs
        hOutsideTotal
        qbit
        (outsideXReserve i qbit hqTargetReserve)
  · unfold ExtReg.FreshFor
    have hZeroInOriginal :
        FreshZero
          ((dst.zslot i).newBits
            (dst.zslot i).capacity)
          b := by
      apply FreshZero.of_subset
        (((dst.zslot i).newBits
          (dst.zslot i).capacity))
        z.reserve
        b
        ?_
        hzRootZero
      intro qbit hqNew
      have hqTargetReserve :
          qbit ∈
            (dst.zslot i).reserve.qubits := by
        exact List.mem_of_mem_take hqNew
      have hqDropped :
          qbit ∈
            List.drop
              (commonNeededWidth need -
                (layout.zSplit.child i).width)
              (layout.zSplit.child i).reserve.qubits := by
        simpa [
          dst,
          src,
          targetSignedLayoutState,
          growExtRegTo,
          ExtReg.grow,
          ExtReg.remainingReserve,
          Reg.drop
        ] using hqTargetReserve
      have hqChildReserve :
          qbit ∈
            (layout.zSplit.child i).reserve.qubits :=
        List.mem_of_mem_drop hqDropped
      apply
        PhaseSplitLayout.child_newBits_subset_parent_reserve
          layout.zSplit
          i
          (layout.zSplit.child i).capacity
      simpa [
        ExtReg.newBits,
        ExtReg.capacity,
        Reg.take,
        regSize,
        Reg.width
      ] using hqChildReserve
    apply
      FreshZero.of_eq_on_bits
        ((dst.zslot i).newBits
          (dst.zslot i).capacity)
        b
        b'
        ?_
        hZeroInOriginal
    intro qbit hqNew
    have hqTargetReserve :
        qbit ∈
          (dst.zslot i).reserve.qubits :=
      List.mem_of_mem_take hqNew
    exact
      SameOutsideLayout.bit_eq_of_outside
        qs
        hOutsideTotal
        qbit
        (outsideZReserve i qbit hqTargetReserve)

end Shor
