import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateSemanticsLemmas

namespace Shor
open Gate
open Operations

section RowSemantics
/-! =========================================================
    Section 9: Legacy ordinary-register modular helpers
========================================================= -/

/-- Ordinary-register modular reduction retained for legacy arithmetic gate statements. -/
def tcMod (r : Reg) (z : ℤ) : ℕ := Int.toNat (z % (ASize r : ℤ))

/-- Two's-complement negation value for an ordinary register. -/
def tcNegVal (r : Reg) (x : ℕ) : ℕ := tcMod r (-(x : ℤ))

/-- Ordinary-register value update for an add-scaled arithmetic step. -/
def tcAddScaledVal
    {β : Type} [RegEncoding β]
    (dst src : Reg) (negSrc : Bool) (sh : ℕ) (b : β) : ℕ :=
  let sgn : ℤ := if negSrc then -1 else 1
  tcMod dst
    ((RegEncoding.toNat dst b : ℤ) +
      sgn * (RegEncoding.toNat src b : ℤ) * ((2 : ℤ) ^ sh))
variable (qs : QSemantics) [RegEncoding qs.Basis]

/-! =========================================================
    Section 10: Source-row semantics
========================================================= -/

/-- How the original source basis should be read when forming chunk rows:
    lower chunks are ordinary radix digits, while the top chunk is signed. -/

def sourceChunkXInt
  (st : LayoutState k) (i : Fin k) (b : qs.Basis) : ℤ :=
  if isTopChunk i then
    extToInt (st.xslot i) b
  else
    (ExtReg.toNat (st.xslot i) b : ℤ)

/-- Same mixed source interpretation for the `z` slots. -/
def sourceChunkZInt
  (st : LayoutState k) (i : Fin k) (b : qs.Basis) : ℤ :=
  if isTopChunk i then
    extToInt (st.zslot i) b
  else
    (ExtReg.toNat (st.zslot i) b : ℤ)

/-- Row evaluation of `x` against the original basis:
    lower chunks contribute as unsigned digits, top chunk as signed. -/

def evalRowX
  (st : LayoutState k) (r : Register k) (b : qs.Basis) : ℤ :=
  ∑ j : Fin k, r j * sourceChunkXInt (qs := qs) st j b

/-- Row evaluation of `z` against the original basis:
    lower chunks contribute as unsigned digits, top chunk as signed. -/

def evalRowZ
  (st : LayoutState k) (r : Register k) (b : qs.Basis) : ℤ :=
  ∑ j : Fin k, r j * sourceChunkZInt (qs := qs) st j b

/-! =========================================================
    Section 10: Encoding invariants
========================================================= -/

/-- Two-layout version: the current widened machine state is read signed on `dst`,
    while the original basis is interpreted using the mixed chunk semantics on `src`. -/

def EncodesStateFrom
  (src dst : LayoutState k) (σ : State k) (b0 b : qs.Basis) : Prop :=
  (∀ i : Fin k,
    extToInt (dst.xslot i) b
      = evalRowX (qs := qs) src (σ i) b0) ∧
  (∀ i : Fin k,
    extToInt (dst.zslot i) b
      = evalRowZ (qs := qs) src (σ i) b0)

/-- `EncodesStateFrom` plus signed-fit obligations for every widened destination slot. -/
def EncodesStateFromFits
  (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ}
  (src dst : LayoutState k) (σ : State k) (b0 b : qs.Basis) : Prop :=
  EncodesStateFrom (qs := qs) src dst σ b0 b ∧
  (∀ i : Fin k,
    FitsSignedWidth (ExtReg.width (dst.xslot i))
      (evalRowX (qs := qs) src (σ i) b0)) ∧
  (∀ i : Fin k,
    FitsSignedWidth (ExtReg.width (dst.zslot i))
      (evalRowZ (qs := qs) src (σ i) b0))

/-- Current symbolic row values fit one sign bit beyond the scanned unsigned widths. -/
def WidthStateSoundPlus
    (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ}
    (src : LayoutState k) (cur : WidthState k) (σ : State k) (b0 : qs.Basis) : Prop :=
  (∀ i : Fin k,
    FitsSignedWidth (cur.xw i + 1) (evalRowX (qs := qs) src (σ i) b0))
    ∧
  (∀ i : Fin k,
    FitsSignedWidth (cur.zw i + 1) (evalRowZ (qs := qs) src (σ i) b0))

/-- The concrete destination layout is at least as wide as the symbolic scan says. -/
def WidthStateDominatedByLayout {k : ℕ} (cur : WidthState k) (dst : LayoutState k) : Prop :=
  (∀ i : Fin k, cur.xw i + 1 ≤ (dst.xslot i).width) ∧ (∀ i : Fin k, cur.zw i + 1 ≤ (dst.zslot i).width)

/-- Main body invariant: encoded rows, symbolic fit bounds, and layout domination. -/
def EncodesStateFromWithWidths
  (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ}
  (src dst : LayoutState k) (cur : WidthState k) (σ : State k) (b0 b : qs.Basis) : Prop :=
  EncodesStateFrom (qs := qs) src dst σ b0 b ∧
  WidthStateSoundPlus (qs := qs) src cur σ b0 ∧
  WidthStateDominatedByLayout cur dst

/-! =========================================================
    Section 11: Phase scalar
========================================================= -/

/-- The accumulated scalar now uses the same mixed source-row semantics as
    `EncodesStateFrom`, so the body lemma stays aligned with the invariant. -/
noncomputable def phaseScalarFrom
  (k : ℕ) (phi : ℝ) (coeff : Fin (q k) → ℚ)
  (st : LayoutState k) (b0 : qs.Basis) :
  (pts : List Point) → (n : ℕ) → (hn : n + pts.length = q k) → ℂ
| [], n, hn => 1
| pt :: pts, n, hn =>
    let l : Fin (q k) := ⟨n, by
      have hlt : n < n + (pt :: pts).length := by
        simp
      aesop
    ⟩
    let hn' : n + 1 + pts.length = q k := by
      simp at hn
      omega
    Complex.exp
      ((phi * ((coeff l : ℚ) : ℝ)) * Complex.I *
        (((evalRowX (qs := qs) st (expectedRow (k := k) pt) b0 : ℤ) : ℂ) *
         (((evalRowZ (qs := qs) st (expectedRow (k := k) pt) b0 : ℤ) : ℂ))))
    * phaseScalarFrom k phi coeff st b0 pts (n + 1) hn'

/-- All reserve bits that would be activated when growing to `W` are zero in basis `b`. -/
def LayoutState.CleanForGrowth {Basis : Type u} [RegEncoding Basis] {k : ℕ} (src : LayoutState k) (W : ℕ) (b : Basis) : Prop :=
  (∀ i, ExtReg.FreshFor (src.xslot i) (W - (src.xslot i).width) b) ∧
  (∀ i, ExtReg.FreshFor (src.zslot i) (W - (src.zslot i).width) b)

/-- Concrete workspace hypothesis for running allocation gates from `src` to the scanned width. -/
def CompilerWorkspaceOK {Basis : Type u} [RegEncoding Basis] {k : ℕ} (src : LayoutState k) (need : NeededWidths k) (b : Basis) : Prop :=
  let Wwork := commonNeededWidth need
  src.CanGrowTo Wwork ∧ src.CleanForGrowth Wwork b

/-- Linear closure of basis states whose relevant compiler workspace is clean
(`CleanClosure` at the compiler-workspace-clean predicate). -/
abbrev CleanWorkspaceState (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ}
    (src : LayoutState k) (need : NeededWidths k) : qs.State → Prop :=
  CleanClosure (fun b => CompilerWorkspaceOK src need b)

/-- Drop the scan-width bookkeeping from the stronger body invariant. -/
lemma EncodesStateFromWithWidths.toFits
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    {src dst : LayoutState k}
    {cur : WidthState k}
    {σ : State k}
    {b0 b : qs.Basis}
    (h :
      EncodesStateFromWithWidths
        (qs := qs)
        src dst cur σ b0 b) :
    EncodesStateFromFits
      (qs := qs)
      src dst σ b0 b := by
  rcases h with
    ⟨hEnc, ⟨hSoundX, hSoundZ⟩,
      ⟨hDomX, hDomZ⟩⟩
  refine ⟨hEnc, ?_, ?_⟩
  · intro i
    exact FitsSignedWidth_mono
      (hDomX i)
      (hSoundX i)
  · intro i
    exact FitsSignedWidth_mono
      (hDomZ i)
      (hSoundZ i)

/-! =========================================================
    Section 4: Start-state and initial layout facts
========================================================= -/

/-- Start-state row evaluation picks out the requested x-slot. -/
lemma evalRowX_start_state (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} (st : LayoutState k) (i : Fin k) (b : qs.Basis) :
  evalRowX (qs := qs) st (State.start_state i) b = sourceChunkXInt (qs := qs) st i b := by unfold evalRowX State.start_state; simp

/-- Start-state row evaluation picks out the requested z-slot. -/
lemma evalRowZ_start_state (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} (st : LayoutState k) (i : Fin k) (b : qs.Basis) :
  evalRowZ (qs := qs) st (State.start_state i) b = sourceChunkZInt (qs := qs) st i b := by unfold evalRowZ State.start_state; simp

/-! =========================================================
    Section 5: Source-row arithmetic
    These facts mirror the algebra of `Register` operations at the integer row
    evaluation level for both `x` and `z`.
========================================================= -/

/-- Left shift scales `x` row evaluation by `2^m`. -/
lemma evalRowX_shiftL_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (m : ℕ)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (r.shiftL m) b
    =
  ((2 : ℤ)^m) * evalRowX (qs := qs) src r b := by
  unfold evalRowX Register.shiftL
  calc
    (∑ j : Fin k, (r j * (2 : ℤ)^m) * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

/-- Left shift scales `z` row evaluation by `2^m`. -/
lemma evalRowZ_shiftL_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (m : ℕ)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (r.shiftL m) b
    =
  ((2 : ℤ)^m) * evalRowZ (qs := qs) src r b := by
  unfold evalRowZ Register.shiftL
  calc
    (∑ j : Fin k, (r j * (2 : ℤ)^m) * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

/-- Negation negates `x` row evaluation. -/
lemma evalRowX_negate_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (Register.negate r) b
    =
  - evalRowX (qs := qs) src r b := by
  unfold evalRowX Register.negate
  calc
    (∑ j : Fin k, (-r j) * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, -(r j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = - ∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.sum_neg_distrib]

/-- Negation negates `z` row evaluation. -/
lemma evalRowZ_negate_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (Register.negate r) b
    =
  - evalRowZ (qs := qs) src r b := by
  unfold evalRowZ Register.negate
  calc
    (∑ j : Fin k, (-r j) * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, -(r j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = - ∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.sum_neg_distrib]

/-- Exact right shift gives an `x` row quotient relation. -/
lemma evalRowX_shiftR_exact
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r r' : Register k)
  (m : ℕ)
  (b : qs.Basis)
  (hshift : Register.shiftR? r m = some r') :
  evalRowX (qs := qs) src r b
    =
  ((2 : ℤ)^m) * evalRowX (qs := qs) src r' b := by
  have hdiv := Register.shiftR?_some_divisible hshift
  have hval := Register.shiftR?_some_value hshift
  unfold evalRowX
  calc
    (∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, (((2 : ℤ)^m) * r' j) * sourceChunkXInt (qs := qs) src j b := by
        apply Finset.sum_congr rfl
        intro j hj
        have hdvd : ((2 : ℤ)^m) ∣ r j := Int.dvd_of_emod_eq_zero (hdiv j)
        have hrj : r j = ((2 : ℤ)^m) * r' j := by
          calc
            r j = ((2 : ℤ)^m) * (r j / ((2 : ℤ)^m)) := by
              symm
              exact Int.mul_ediv_cancel' hdvd
            _ = ((2 : ℤ)^m) * r' j := by
              rw [hval j]
        rw [hrj]
    _ =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r' j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r' j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

/-- Exact right shift gives a `z` row quotient relation. -/
lemma evalRowZ_shiftR_exact
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r r' : Register k)
  (m : ℕ)
  (b : qs.Basis)
  (hshift : Register.shiftR? r m = some r') :
  evalRowZ (qs := qs) src r b
    =
  ((2 : ℤ)^m) * evalRowZ (qs := qs) src r' b := by
  have hdiv := Register.shiftR?_some_divisible hshift
  have hval := Register.shiftR?_some_value hshift
  unfold evalRowZ
  calc
    (∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, (((2 : ℤ)^m) * r' j) * sourceChunkZInt (qs := qs) src j b := by
        apply Finset.sum_congr rfl
        intro j hj
        have hdvd : ((2 : ℤ)^m) ∣ r j := Int.dvd_of_emod_eq_zero (hdiv j)
        have hrj : r j = ((2 : ℤ)^m) * r' j := by
          calc
            r j = ((2 : ℤ)^m) * (r j / ((2 : ℤ)^m)) := by
              symm
              exact Int.mul_ediv_cancel' hdvd
            _ = ((2 : ℤ)^m) * r' j := by
              rw [hval j]
        rw [hrj]
    _ =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r' j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r' j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

/-- Add-scaled operation expands linearly on `x` rows. -/
lemma evalRowX_addScaled_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (dstReg srcReg : Register k)
  (negSrc : Bool)
  (sh : ℕ)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (Register.addScaled dstReg srcReg negSrc sh) b
    =
  evalRowX (qs := qs) src dstReg b
    + (if negSrc then (-1 : ℤ) else 1)
        * ((2 : ℤ)^sh)
        * evalRowX (qs := qs) src srcReg b := by
  unfold evalRowX Register.addScaled
  calc
    (∑ j : Fin k,
        (dstReg j + (if negSrc then (-1 : ℤ) else 1) * srcReg j * (2 : ℤ) ^ sh)
          * sourceChunkXInt (qs := qs) src j b)
        =
    (∑ j : Fin k,
      (dstReg j * sourceChunkXInt (qs := qs) src j b
        +
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkXInt (qs := qs) src j b))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkXInt (qs := qs) src j b)
      +
    ∑ j : Fin k,
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkXInt (qs := qs) src j b) := by
          rw [Finset.sum_add_distrib]
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkXInt (qs := qs) src j b)
      +
    ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
      * ∑ j : Fin k, srcReg j * sourceChunkXInt (qs := qs) src j b := by
          rw [Finset.mul_sum]

/-- Add-scaled operation expands linearly on `z` rows. -/
lemma evalRowZ_addScaled_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (dstReg srcReg : Register k)
  (negSrc : Bool)
  (sh : ℕ)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (Register.addScaled dstReg srcReg negSrc sh) b
    =
  evalRowZ (qs := qs) src dstReg b
    + (if negSrc then (-1 : ℤ) else 1)
        * ((2 : ℤ)^sh)
        * evalRowZ (qs := qs) src srcReg b := by
  unfold evalRowZ Register.addScaled
  calc
    (∑ j : Fin k,
        (dstReg j + (if negSrc then (-1 : ℤ) else 1) * srcReg j * (2 : ℤ) ^ sh)
          * sourceChunkZInt (qs := qs) src j b)
        =
    (∑ j : Fin k,
      (dstReg j * sourceChunkZInt (qs := qs) src j b
        +
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkZInt (qs := qs) src j b))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkZInt (qs := qs) src j b)
      +
    ∑ j : Fin k,
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkZInt (qs := qs) src j b) := by
          rw [Finset.sum_add_distrib]
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkZInt (qs := qs) src j b)
      +
    ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
      * ∑ j : Fin k, srcReg j * sourceChunkZInt (qs := qs) src j b := by
          rw [Finset.mul_sum]

/-! =========================================================
    Section 7: Layout locality and basis extensionality
    The compiler often proves that a gate changes only layout slots and leaves
    everything outside unchanged. These predicates and extensionality lemmas turn
    those slot/outside facts back into equality of basis states.
========================================================= -/

/-- Short name for the layout-wide owned-disjointness invariant. -/
abbrev LayoutSlotsDisjoint
    {k : ℕ}
    (st : LayoutState k) : Prop :=
  st.OwnedPairwiseDisjoint

/-- Register `e` is actively disjoint from every slot in a layout. -/
def OutsideLayout
    {k : ℕ}
    (dst : LayoutState k)
    (e : ExtReg) : Prop :=
  (∀ i : Fin k, ExtReg.ActiveDisjoint e (dst.xslot i)) ∧
  (∀ i : Fin k, ExtReg.ActiveDisjoint e (dst.zslot i))

/-- Two basis states agree on every register outside a layout. -/
def SameOutsideLayout
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    (dst : LayoutState k)
    (b₁ b₂ : qs.Basis) : Prop :=
  ∀ e : ExtReg,
    OutsideLayout dst e →
    extToInt e b₁ = extToInt e b₂

lemma SameOutsideLayout.refl (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} (dst : LayoutState k) (b : qs.Basis) :
  SameOutsideLayout qs dst b b := by intro e he; rfl

lemma SameOutsideLayout.symm (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} {dst : LayoutState k} {b1 b2 : qs.Basis}
    (h : SameOutsideLayout qs dst b1 b2) : SameOutsideLayout qs dst b2 b1 := by
  intro e he; exact (h e he).symm

lemma SameOutsideLayout.trans
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ} {dst : LayoutState k} {b1 b2 b3 : qs.Basis}
  (h12 : SameOutsideLayout qs dst b1 b2)
  (h23 : SameOutsideLayout qs dst b2 b3) :
  SameOutsideLayout qs dst b1 b3 := by
  intro e he
  calc
    extToInt e b1 = extToInt e b2 := h12 e he
    _ = extToInt e b3 := h23 e he

/-- Every physical qubit is either in a slot or can be read by an outside singleton register. -/
def CoversLayoutBits
    {k : ℕ}
    (dst : LayoutState k) : Prop :=
  ∀ q : ℕ,
    (∃ i : Fin k, q ∈ (dst.xslot i).active.qubits) ∨
    (∃ i : Fin k, q ∈ (dst.zslot i).active.qubits) ∨
    OutsideLayout dst (ExtReg.ofReg (qubitReg q))

/-- Equal register values imply equal bits for qubits inside that register. -/
lemma bit_eq_of_toNat_eq_on_reg
    {Basis : Type u}
    [RegEncoding Basis]
    {r : Reg}
    {b₁ b₂ : Basis}
    {q : ℕ}
    (hNat :
      RegEncoding.toNat r b₁ =
        RegEncoding.toNat r b₂)
    (hq : q ∈ r.qubits) :
    RegEncoding.bit q b₁ =
      RegEncoding.bit q b₂ := by
  calc
    RegEncoding.bit q b₁
        =
    RegEncoding.bit q
      (RegEncoding.writeNat
        r (RegEncoding.toNat r b₁) b₁) := by
          rw [RegEncoding.writeNat_toNat]
    _ =
    RegEncoding.bit q
      (RegEncoding.writeNat
        r (RegEncoding.toNat r b₂) b₂) := by
          simpa [hNat] using
            (RegEncoding.bit_writeNat_in
              (r := r)
              (v := RegEncoding.toNat r b₁)
              (b₁ := b₁)
              (b₂ := b₂)
              (q := q)
              hq)
    _ = RegEncoding.bit q b₂ := by
          rw [RegEncoding.writeNat_toNat]

/-- Equal signed interpretations imply equal raw active-register values. -/
lemma toNat_eq_of_extToInt_eq
    {Basis : Type u}
    [RegEncoding Basis]
    {e : ExtReg}
    {b₁ b₂ : Basis}
    (h :
      extToInt e b₁ =
        extToInt e b₂) :
    ExtReg.toNat e b₁ =
      ExtReg.toNat e b₂ := by
  apply tcDecodeWidth_inj_of_lt
    (ExtReg.toNat_lt e b₁)
    (ExtReg.toNat_lt e b₂)
  simpa [extToInt] using h

/-- Equal signed interpretations imply equal active bits. -/
lemma bit_eq_of_extToInt_eq_on_active
    {Basis : Type u}
    [RegEncoding Basis]
    {e : ExtReg}
    {b₁ b₂ : Basis}
    {q : ℕ}
    (h :
      extToInt e b₁ = extToInt e b₂)
    (hq : q ∈ e.active.qubits) :
    RegEncoding.bit q b₁ =
      RegEncoding.bit q b₂ := by
  exact bit_eq_of_toNat_eq_on_reg
    (toNat_eq_of_extToInt_eq h)
    hq

lemma SameOutsideLayout.bit_eq_of_outside
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    {dst : LayoutState k}
    {b₁ b₂ : qs.Basis}
    (hSO : SameOutsideLayout qs dst b₁ b₂)
    (q : ℕ)
    (hout :
      OutsideLayout dst
        (ExtReg.ofReg (qubitReg q))) :
    RegEncoding.bit q b₂ =
      RegEncoding.bit q b₁ := by
  apply bit_eq_of_extToInt_eq_on_active
  · exact
      (hSO
        (ExtReg.ofReg (qubitReg q))
        hout).symm
  · simp [ExtReg.ofReg, qubitReg, Reg.singleton]

/-- Classify any qubit as lying in an `x` slot, a `z` slot, or outside the layout. -/
lemma qubit_in_layout_or_outside
    {k : ℕ}
    (dst : LayoutState k)
    (q : ℕ) :
    (∃ i : Fin k,
      q ∈ (dst.xslot i).active.qubits) ∨
    (∃ i : Fin k,
      q ∈ (dst.zslot i).active.qubits) ∨
    OutsideLayout dst
      (ExtReg.ofReg (qubitReg q)) := by
  by_cases hx :
      ∃ i : Fin k,
        q ∈ (dst.xslot i).active.qubits
  · exact Or.inl hx
  by_cases hz :
      ∃ i : Fin k,
        q ∈ (dst.zslot i).active.qubits
  · exact Or.inr (Or.inl hz)
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · intro i
    have hqi :
        q ∉ (dst.xslot i).active.qubits := by
      intro h
      exact hx ⟨i, h⟩
    simpa [ExtReg.ActiveDisjoint, ExtReg.ofReg, qubitReg, Reg.singleton, Disjoint] using hqi
  · intro i
    have hqi :
        q ∉ (dst.zslot i).active.qubits := by
      intro h
      exact hz ⟨i, h⟩
    simpa [ExtReg.ActiveDisjoint, ExtReg.ofReg, qubitReg, Reg.singleton, Disjoint] using hqi

/-- The qubit classifier packaged as the layout coverage predicate. -/
theorem layout_covers_bits {k : ℕ} (dst : LayoutState k) : CoversLayoutBits dst := qubit_in_layout_or_outside dst

/-- Agreement on all layout slots plus outside agreement determines the whole basis state. -/
lemma basis_eq_of_sameOutside_and_slots
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    (dst : LayoutState k)
    (bMid bNext : qs.Basis)
    (hSO :
      SameOutsideLayout qs dst bMid bNext)
    (hXslots :
      ∀ i : Fin k, extToInt (dst.xslot i) bNext  = extToInt (dst.xslot i) bMid)
    (hZslots :
      ∀ i : Fin k, extToInt (dst.zslot i) bNext = extToInt  (dst.zslot i) bMid) :
    bNext = bMid := by
  apply RegEncoding.basis_ext
  intro q
  rcases qubit_in_layout_or_outside dst q with
    hx | hz | hout
  · rcases hx with ⟨i, hq⟩
    exact bit_eq_of_extToInt_eq_on_active
      (hXslots i) hq
  · rcases hz with ⟨i, hq⟩
    exact bit_eq_of_extToInt_eq_on_active
      (hZslots i) hq
  · exact bit_eq_of_extToInt_eq_on_active
      ((hSO
        (ExtReg.ofReg (qubitReg q))
        hout).symm)
      (by simp [ExtReg.ofReg, qubitReg, Reg.singleton])

/-- The accumulated phase scalar is never zero. -/
lemma phaseScalarFrom_ne_zero
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  (k : ℕ) (phi : ℝ) (coeff : Fin (q k) → ℚ)
  (src : LayoutState k) (b0 : qs.Basis) :
  ∀ (pts : List Point) (n : ℕ) (hn : n + pts.length = q k),
    phaseScalarFrom (qs := qs) k phi coeff src b0 pts n hn ≠ 0 := by
  intro pts
  induction pts with
  | nil =>
      intro n hn
      simp [phaseScalarFrom]
  | cons pt pts ih =>
      intro n hn
      simp [phaseScalarFrom]
      have htail :
          phaseScalarFrom (qs := qs) k phi coeff src b0 pts (n + 1)
            (by
              simp at hn
              omega) ≠ 0 := by
        exact ih (n + 1) (by
          simp at hn
          omega)
      aesop

/-- Nonzero equal scalar multiples of basis kets have the same basis label. -/
lemma ket_eq_of_same_nonzero_smul
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {a : ℂ} {b1 b2 : qs.Basis}
  (ha : a ≠ 0)
  (h : a • qs.ket b1 = a • qs.ket b2) :
  b1 = b2 := by
  have hket : qs.ket b1 = qs.ket b2 := by
    simp_all only [ne_eq, not_false_eq_true, smul_right_inj]
  exact qs.ket_inj hket

/-- Start-state encodings are unique once slot values determine the basis state. -/
lemma encodesStateFrom_start_unique_of_ext
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (b0 b1 b2 : qs.Basis)
  (h1 : EncodesStateFrom (qs := qs) src dst State.start_state b0 b1)
  (h2 : EncodesStateFrom (qs := qs) src dst State.start_state b0 b2)
  (hdet :
    (∀ i : Fin k,
      extToInt (dst.xslot i) b1 =
      extToInt (dst.xslot i) b2) ∧
    (∀ i : Fin k,
      extToInt (dst.zslot i) b1 =
      extToInt (dst.zslot i) b2) →
    b1 = b2) :
  b1 = b2 := by
  apply hdet
  constructor
  · intro i
    calc
      extToInt (dst.xslot i) b1
          = evalRowX (qs := qs) src (State.start_state i) b0 := h1.1 i
      _ = extToInt (dst.xslot i) b2 := (h2.1 i).symm
  · intro i
    calc
      extToInt (dst.zslot i) b1
          = evalRowZ (qs := qs) src (State.start_state i) b0 := h1.2 i
      _ = extToInt (dst.zslot i) b2 := (h2.2 i).symm


def WellFormedReg (r : Reg) : Prop := r.qubits.Nodup

@[simp] theorem wellFormedReg (r : Reg) : WellFormedReg r := r.nodup

/-- Annotating phase leaves commutes with appending programs, after shifting the second index. -/
lemma annotatePhaseTermsAux_append (k n : ℕ) (ops₁ ops₂ : List (valid_ops k)) :
  annotatePhaseTermsAux k n (ops₁ ++ ops₂) =
    annotatePhaseTermsAux k n ops₁ ++
      annotatePhaseTermsAux k (n + phaseProductCount ops₁) ops₂ := by
  induction ops₁ generalizing n with
  | nil =>
      simp [annotatePhaseTermsAux, phaseProductCount]
  | cons op ops₁ ih =>
      cases op <;>simp [annotatePhaseTermsAux, phaseProductCount, ih, Nat.add_assoc, Nat.add_comm]

/-- Append rule specialized to the usual initial phase index `0`. -/
lemma annotatePhaseTermsAux_append_zero (k : ℕ) (ops₁ ops₂ : List (valid_ops k)) :
  annotatePhaseTermsAux k 0 (ops₁ ++ ops₂) =
    annotatePhaseTermsAux k 0 ops₁ ++
      annotatePhaseTermsAux k (phaseProductCount ops₁) ops₂ := by
  simpa using annotatePhaseTermsAux_append k 0 ops₁ ops₂

/-- Constant-addition helper programs contain no phase-product leaves. -/
@[simp] lemma phaseProductCount_addConstAux
  {k : ℕ} (dst src : Fin k) (neg' : Bool) (n sh : ℕ) :
  phaseProductCount (addConstAux (k := k) dst src neg' n sh) = 0 := by
  rw [addConstAux_eq_shifts (k := k) (dst := dst) (src := src) (neg' := neg') n sh]
  induction shiftsOfAux n sh with
  | nil =>
      simp [phaseProductCount]
  | cons s ss ih =>
      simp [phaseProductCount, ih]

@[simp] lemma phaseProductCount_addConstFrom {k : ℕ} (dst src : Fin k) (c : Int) :
  phaseProductCount (addConstFrom (k := k) dst src c) = 0 := by
  by_cases hc : c = 0 <;> simp [addConstFrom, hc, phaseProductCount, phaseProductCount_addConstAux]

/-- Phase-product leaf counts add over program append. -/
@[simp] lemma phaseProductCount_append
  {k : ℕ} (xs ys : List (valid_ops k)) :
  phaseProductCount (xs ++ ys) =
    phaseProductCount xs + phaseProductCount ys := by
  induction xs with
  | nil =>
      simp [phaseProductCount]
  | cons op xs ih =>
      cases op <;> simp [phaseProductCount, ih,  Nat.add_comm, Nat.add_left_comm]

@[simp] lemma phaseProductCount_computeLocalAux
  {k : ℕ} (hk : 0 < k) (z : Int) :
  ∀ js : List (Fin k), phaseProductCount (computeLocalAux (k := k) hk z js) = 0
  | [] => by
      simp [computeLocalAux, phaseProductCount]
  | j :: js => by
      simp [computeLocalAux, phaseProductCount_append, phaseProductCount_addConstFrom, phaseProductCount_computeLocalAux]

@[simp] lemma phaseProductCount_computeLocal2 {k : ℕ} (hk : 0 < k) (z : Int) :
  phaseProductCount (computeLocal2 (k := k) hk z) = 0 := by simp [computeLocal2, phaseProductCount_computeLocalAux]
lemma FitsSignedWidth_of_nonneg_lt_pow
  {w : ℕ} {n : ℕ}
  (h : n < 2 ^ w) :
  FitsSignedWidth (w + 1) (n : ℤ) := by
  unfold FitsSignedWidth signedMin signedMax
  constructor <;> simp
  constructor
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hneg : (-(2 : ℤ) ^ (w + 1)) ≤ 0 := by
    have hpow0 : (0 : ℤ) ≤ (2 : ℤ) ^ (w + 1) := by positivity
    omega
  omega
  norm_cast

/-- Decoding any `w`-bit pattern gives a signed value fitting width `w+1`. -/
lemma tcDecodeWidth_fits_succ
  {w n : ℕ}
  (h : n < 2 ^ w) :
  FitsSignedWidth (w + 1) (tcDecodeWidth w n) := by
  unfold FitsSignedWidth signedMin signedMax tcDecodeWidth
  by_cases hs : n < 2 ^ (w - 1)
  · simp
    constructor <;> split
    next x x_1 =>
      simp_all only [pow_zero, Nat.lt_one_iff, zero_tsub, zero_lt_one, Int.reduceNeg, Left.neg_nonpos_iff,
        zero_le_one]
    next x x_1 w =>
      simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
        exact_mod_cast Nat.zero_le n
      have hneg : (-(2 : ℤ) ^ (w + 1)) ≤ 0 := by
        have hpow0 : (0 : ℤ) ≤ (2 : ℤ) ^ (w + 1) := by positivity
        omega
      omega
    simp
    simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
    norm_cast
  · simp
    constructor <;> split
    next x x_1 =>
      simp_all only [pow_zero, Nat.lt_one_iff, zero_tsub, zero_lt_one, Int.reduceNeg, Left.neg_nonpos_iff,
        zero_le_one]
      simp at hs
    next x x_1 w =>
      simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
      have hge : 2 ^ w ≤ n := Nat.le_of_not_lt hs
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
        exact_mod_cast Nat.zero_le n
      omega
    simp
    simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, not_lt]
    split
    next h_1 => norm_cast
    next h_1 =>
      simp_all only [not_lt]; rename_i x1 x w
      have hlt : (n : ℤ) < (2 : ℤ) ^ (w + 1) := by
        exact_mod_cast h
      omega

/-- Child registers from the same split layout inherit owned-disjointness. -/
lemma phaseSplitChild_owned_disjoint {parent : ExtReg} {k W : ℕ} (layout : PhaseSplitLayout parent k W) {i j : Fin k} (hij : i ≠ j) :
    ExtReg.OwnedDisjoint (layout.child i) (layout.child j) := layout.child_owned_disjoint hij

/-- Cross operand children of a phase-product layout are owned-disjoint. -/
lemma phaseProductLayout_cross_disjoint {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (i j : Fin k) :
    ExtReg.OwnedDisjoint (layout.xSplit.child i) (layout.zSplit.child j) := layout.cross_owned_disjoint i j

/-- The signed interpretation of an `ExtReg` always fits one bit wider than its active width. -/
lemma extToInt_fits_width_succ (e : ExtReg) (b : qs.Basis) : FitsSignedWidth (ExtReg.width e + 1) (extToInt e b) := by
  unfold extToInt
  exact tcDecodeWidth_fits_succ (by simpa using (ExtReg.toNat_lt (Basis := qs.Basis) (e := e) (b := b)))

/-- If `z` fits signed width `w+1`, then `(2^n) * z` fits signed width `w+n+1`. -/
lemma FitsSignedWidth_shiftL_raw
  {w n : ℕ} {z : ℤ}
  (hfit : FitsSignedWidth (w + 1) z) :
  FitsSignedWidth (w + n + 1) (((2 : ℤ)^n) * z) := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  have hp0 : (0 : ℤ) ≤ (2 : ℤ)^n := by positivity
  have hp : (0 : ℤ) < (2 : ℤ)^n := by positivity
  have hpow :
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ))
        = (((2 ^ (w + n) : ℕ) : ℤ)) := by
    calc
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ))
          = (((2 ^ n : ℕ) : ℤ)) * (((2 ^ w : ℕ) : ℤ)) := by norm_num
      _ = (((2 ^ n * 2 ^ w : ℕ) : ℤ)) := by norm_num
      _ = (((2 ^ (n + w) : ℕ) : ℤ)) := by
            exact_mod_cast (pow_add 2 n w).symm
      _ = (((2 ^ (w + n) : ℕ) : ℤ)) := by rw [Nat.add_comm]
  have hpow_neg :
      ((2 : ℤ)^n) * (-(((2 ^ w : ℕ) : ℤ)))
        = -(((2 ^ (w + n) : ℕ) : ℤ)) := by
    simp
    rw[pow_add,mul_comm]
  have hL :
      ((2 : ℤ)^n) * (-(((2 ^ w : ℕ) : ℤ)))
        ≤
      ((2 : ℤ)^n) * z := by
    exact mul_le_mul_of_nonneg_left (by simp_all) hp0
  have hU :
      ((2 : ℤ)^n) * z
        <
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ)) := by
    exact mul_lt_mul_of_pos_left (by simp_all) hp
  constructor
  · simp
  · aesop

/-- If `z = 2^n * q` and `z` fits signed width `w+1`, then the exact quotient
    fits signed width `(w - n) + 1`. -/
lemma FitsSignedWidth_shiftR_of_mul
  {w n : ℕ} {z q : ℤ}
  (hfit : FitsSignedWidth (w + 1) z)
  (hz : z = ((2 : ℤ)^n) * q) :
  FitsSignedWidth (w - n + 1) q := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  by_cases hnw : n ≤ w
  · have hpos : (0 : ℤ) < (2 : ℤ)^n := by positivity
    have hpow :
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ))
          = (((2 ^ w : ℕ) : ℤ)) := by
      calc
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ))
            = (((2 ^ n : ℕ) : ℤ)) * (((2 ^ (w - n) : ℕ) : ℤ)) := by norm_num
        _ = (((2 ^ n * 2 ^ (w - n) : ℕ) : ℤ)) := by norm_num
        _ = (((2 ^ (n + (w - n)) : ℕ) : ℤ)) := by
              exact_mod_cast (pow_add 2 n (w - n)).symm
        _ = (((2 ^ w : ℕ) : ℤ)) := by rw [Nat.add_sub_of_le hnw]
    have hupper :
        ((2 : ℤ)^n) * q
          <
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ)) := by
      simp_all
    have hlower :
        ((2 : ℤ)^n) * (-(((2 ^ (w - n) : ℕ) : ℤ)))
          ≤
        ((2 : ℤ)^n) * q := by
      have : -(((2 ^ w : ℕ) : ℤ)) ≤ ((2 : ℤ)^n) * q := by
        simp_all
      simp_all
    constructor
    · simp_all
    · simp_all
      constructor
      · have h1 : -(2 ^ n * 2 ^ (w - n) : ℤ) ≤ 2 ^ n * q := by
          rw [hpow]; exact hhi.1
        have h2 : (2 ^ n : ℤ) * -(2 ^ (w - n)) ≤ 2 ^ n * q := by
          rw [mul_neg]; exact h1
        exact le_of_mul_le_mul_left h2 (by positivity)
      · have h1 : (2 ^ n * q : ℤ) < 2 ^ n * 2 ^ (w - n) := by
          rw [hpow]; exact hhi.2
        exact lt_of_mul_lt_mul_left h1 (by positivity)
  · have hwn : w < n := lt_of_not_ge hnw
    have hpowNat : 2 ^ w < 2 ^ n := by
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) hwn
    have hpowInt : (((2 ^ w : ℕ) : ℤ)) < ((2 : ℤ)^n) := by
      exact_mod_cast hpowNat
    have hq0 : q = 0 := by
      by_cases hq : q = 0
      · exact hq
      · rcases lt_or_gt_of_ne hq with hqneg | hqpos
        · have hqle : q ≤ -1 := by omega
          have hmul : ((2 : ℤ)^n) * q ≤ -((2 : ℤ)^n) := by
            calc
              ((2 : ℤ)^n) * q ≤ ((2 : ℤ)^n) * (-1) := by
                gcongr
              _ = -((2 : ℤ)^n) := by ring
          have hzlt : z < -(((2 ^ w : ℕ) : ℤ)) := by
            rw [hz]
            have hnegpow : -((2 : ℤ)^n) < -(((2 ^ w : ℕ) : ℤ)) := by
              omega
            exact lt_of_le_of_lt hmul hnegpow
          simp_all
          rcases hhi with ⟨hlo, hhi⟩
          omega
        · have hqge : (1 : ℤ) ≤ q := by omega
          have hmul : ((2 : ℤ)^n) ≤ ((2 : ℤ)^n) * q := by
            calc
              ((2 : ℤ)^n) = ((2 : ℤ)^n) * 1 := by ring
              _ ≤ ((2 : ℤ)^n) * q := by
                gcongr
          have hzgt : (((2 ^ w : ℕ) : ℤ)) < z := by
            rw [hz]
            exact lt_of_lt_of_le hpowInt hmul
          simp_all
          rcases hhi with ⟨hlo, hhi⟩
          omega
    subst hq0
    have hw0 : w - n = 0 := by omega
    rw [hw0]
    constructor <;> norm_num [signedMin, signedMax]

/-- Negation is always safe if we widen by one additional bit. -/
lemma FitsSignedWidth_neg_widen
  {w : ℕ} {z : ℤ}
  (hfit : FitsSignedWidth (w + 1) z) :
  FitsSignedWidth (w + 2) (-z) := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  have hpow : (((2 ^ w : ℕ) : ℤ)) ≤ (((2 ^ (w + 1) : ℕ) : ℤ)) := by
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ w))
  constructor <;> simp_all
  refine ⟨?_, ?_⟩
  · linarith [hhi.2, hpow]
  · have hpos : (0 : ℤ) < 2 ^ w := by positivity
    omega

/-- Adding a shifted source into a destination is safe in the width prescribed
    by `updateWidthState` (plus the proof-only extra sign bit). -/

lemma FitsSignedWidth_addScaled_widen
  {wd ws sh : ℕ} {dstv srcv : ℤ} (negSrc : Bool)
  (hdst : FitsSignedWidth (wd + 1) dstv)
  (hsrc : FitsSignedWidth (ws + 1) srcv) :
  FitsSignedWidth (max wd (ws + sh) + 2)
    (dstv + (if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ)^sh) * srcv) := by
  have hscaled :
      FitsSignedWidth (ws + sh + 1) (((2 : ℤ)^sh) * srcv) := by
    exact FitsSignedWidth_shiftL_raw (w := ws) (n := sh) (z := srcv) hsrc
  unfold FitsSignedWidth signedMin signedMax at hdst hscaled ⊢
  rcases hdst with ⟨hdlo, hdhi⟩
  rcases hscaled with ⟨hslo, hshi⟩
  set M : ℕ := max wd (ws + sh)
  have hwdM : (((2 ^ wd : ℕ) : ℤ)) ≤ (((2 ^ M : ℕ) : ℤ)) := by
    dsimp [M]
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_left wd (ws + sh)))
  have hwsM : (((2 ^ (ws + sh) : ℕ) : ℤ)) ≤ (((2 ^ M : ℕ) : ℤ)) := by
    dsimp [M]
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_right wd (ws + sh)))
  cases hsgn : negSrc <;> simp_all
  · constructor <;> omega
  · constructor <;> omega

/-! =========================================================
    Section 3: Concrete split layouts and budgeted construction

    These arithmetic and list-slicing facts turn the abstract top-heavy layout
    definitions from `Core` into concrete child registers. They live here because
    they are proof/construction support rather than compiler data definitions.
========================================================= -/

def GoodToomCookPoints
  (k : ℕ)
  (pts : List Point)
  (hpts : pts.length = q k) : Prop :=
  ToomCookMath.GoodInterpolationPoints
    (row := interpEntry k)
    (pts := ToomCookMath.listToFin pts hpts)

/--
Convert a compiler interpolation point to the pure-math point representation.
-/

def toMathPoint : Point → ToomCookMath.Point
  | Point.int z  => ToomCookMath.Point.int z
  | Point.frac c => ToomCookMath.Point.frac c

/--
The compiler's interpolation row is definitionally the pure-math adjusted row.
-/

lemma toMathPoint_interpEntry
    {k : ℕ}
    (p : Point)
    (j : Fin (q k)) :
    ToomCookMath.pointRow
      (q k) (toMathPoint p) j
      =
    interpEntry k p j := by
  cases p <;> rfl

lemma toMathPoint_alternatingPoint
    (i : ℕ) :
    toMathPoint (alternatingPoint i)
      =
    ToomCookMath.alternatingPoint i := by
  unfold alternatingPoint ToomCookMath.alternatingPoint
  unfold ToomCookMath.alternatingInt
  by_cases h : i % 2 == 0
  · simp [h, toMathPoint]
  · simp [h, toMathPoint]

lemma listToFin_genInterpolationPoints_toMathPoint
    (k : ℕ)
    (hpts : (genInterpolationPoints k).length = q k)
    (hmath :
      (ToomCookMath.genFiniteInterpolationPoints (q k)).length = q k)
    (i : Fin (q k)) :
    ToomCookMath.listToFin
        (ToomCookMath.genFiniteInterpolationPoints (q k)) hmath i
      =
    toMathPoint
      (ToomCookMath.listToFin (genInterpolationPoints k) hpts i) := by
  simp [ToomCookMath.listToFin, genInterpolationPoints, ToomCookMath.genFiniteInterpolationPoints, toMathPoint_alternatingPoint]

lemma genInterpolationPoints_good
    (k : ℕ) :
    GoodToomCookPoints k
      (genInterpolationPoints k)
      (by simp [genInterpolationPoints, q]) := by
  let hpts : (genInterpolationPoints k).length = q k := by
    simp [genInterpolationPoints, q]
  let hmath :
      (ToomCookMath.genFiniteInterpolationPoints (q k)).length = q k := by
    simp [ToomCookMath.genFiniteInterpolationPoints]
  unfold GoodToomCookPoints
  have hgoodMath :
      ToomCookMath.GoodInterpolationPoints
        (row := ToomCookMath.pointRow (q k))
        (pts :=
          ToomCookMath.listToFin
            (ToomCookMath.genFiniteInterpolationPoints (q k)) hmath) := by
    exact ToomCookMath.genFiniteInterpolationPoints_good (q k) hmath
  apply ToomCookMath.GoodInterpolationPoints.congr_matrix
    (rowA := ToomCookMath.pointRow (q k))
    (rowB := interpEntry k)
    (ptsA :=
      ToomCookMath.listToFin
        (ToomCookMath.genFiniteInterpolationPoints (q k)) hmath)
    (ptsB :=
      ToomCookMath.listToFin (genInterpolationPoints k) hpts)
  · intro i j
    rw [listToFin_genInterpolationPoints_toMathPoint (k := k) (hpts := hpts) (hmath := hmath) (i := i)]
    exact toMathPoint_interpEntry
      (k := k)
      ((ToomCookMath.listToFin (genInterpolationPoints k) hpts) i)
      j
  · exact hgoodMath


end RowSemantics

/-- Evaluation of compiled annotated programs respects append as sequential composition. -/
lemma eval_compileAnnotatedOpsToSignedGateAux_append
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (xs ys : List (AnnotatedOp k))
  (ψ : qs.State) :
  qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff st (xs ++ ys))
      ψ
    =
  qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff st ys)
      (qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff st xs)
        ψ) := by
  induction xs generalizing ψ with
  | nil =>
      simp [compileAnnotatedOpsToSignedGateAux, qs.eval_id]
  | cons a xs ih =>
      cases a with
      | mk op term? =>
          cases op <;>
            simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, ih]
          aesop

end Shor
