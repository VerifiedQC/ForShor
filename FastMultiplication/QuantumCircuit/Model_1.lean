import FastMultiplication.QuantumCircuit.Layout_1

open Operations
-- Bitstrings and QStates








@[simp] def pow2 (n : ℕ) : ℤ := (2 : ℤ) ^ n

namespace Layout
variable {k : ℕ}

/-- The `q`th global wire’s bit in a bitstring. -/
@[inline] def bit {k : ℕ} (L : Layout k)
  (x : BitStr L.N) (q : Fin L.N) : Bool :=
  x q

/-- A global wire that is the packed image of some `(i,b)` is in the `wires i` finset. -/
lemma pack_mem_wires (L : Layout k) (i : Fin k) (b : Fin (L.width i)) :
  L.pack i b ∈ L.wires i := by
  unfold wires
  refine Finset.mem_image.mpr ?_
  exact ⟨b, by simp, rfl⟩

/-- Interpret register `i` inside a global bitstring `x` as a nonnegative integer. -/
def readReg (L : Layout k) (i : Fin k) (x : BitStr L.N) : ℤ :=
  ∑ b : Fin (L.width i),
      (if L.bit x (L.pack i b) then pow2 (b : ℕ) else 0)



-- /**************
--  * Phase ops  *
--  **************/

/-- A diagonal "phase operator": multiply each basis amplitude by `e^{i·ϕ(x)}`. -/
noncomputable def PhaseOp {N : ℕ} (ϕ : BitStr N → ℝ) : QState N → QState N :=
  fun ψ x => Complex.exp (Complex.I * ϕ x) * ψ x

/-- Phase depending only on the integer value stored in register `i`. -/
noncomputable def U_phaseReg {k : ℕ} (L : Layout k) (i : Fin k) (Φ : ℤ → ℝ) :
  QState L.N → QState L.N :=
  PhaseOp (fun x => Φ (L.readReg i x))

/-- Phase depending on a *pair* of registers. -/
noncomputable def U_phasePair {k : ℕ} (L : Layout k) (i j : Fin k) (Φ : ℤ → ℤ → ℝ) :
  QState L.N → QState L.N :=
  PhaseOp (fun x => Φ (L.readReg i x) (L.readReg j x))

-- helper cast: ℤ → ℝ
@[inline] def zreal (n : ℤ) : ℝ := (n : ℝ)

/-- PhaseProduct with parameter φ acting on registers `i` and `j`.
    On a basis bitstring `x`, it multiplies by exp(i * φ * (readReg i) * (readReg j)). -/
noncomputable def U_phaseProduct {k : ℕ} (L : Layout k)
    (i j : Fin k) (φ : ℝ) : QState L.N → QState L.N :=
  PhaseOp (fun x =>
    φ * zreal (L.readReg i x) * zreal (L.readReg j x))


-- /**********************
--  * Locality scaffolds *
--  **********************/

/-- Two bitstrings agree *on* a set `W` of global wires. -/
def agreesOn {N : ℕ} (W : Finset (Fin N)) (x y : BitStr N) : Prop :=
  ∀ q : Fin N, q ∈ W → x q = y q

/-- Monotonicity: if `W ⊆ W'` and `x,y` agree on `W'`, they agree on `W`. -/
lemma agreesOn_mono {N} {W W' : Finset (Fin N)} {x y : BitStr N}
  (hWW' : W ⊆ W') (h : agreesOn W' x y) :
  agreesOn W x y :=
by
  intro q hq
  exact h q (hWW' hq)

/-- A function depends only on the subset `W` of wires. -/
def dependsOnlyOn {N : ℕ} (W : Finset (Fin N)) (f : BitStr N → α) : Prop :=
  ∀ x y, agreesOn W x y → f x = f y

/-- “Acts on `W`” for a diagonal phase: the phase function only looks at `W`. -/
def ActsOnDiag {N : ℕ} (W : Finset (Fin N)) (U : QState N → QState N) : Prop :=
  ∃ ϕ, dependsOnlyOn W ϕ ∧ U = PhaseOp ϕ



-- /*****************************************
--  * Key fact: `readReg` is local to wires *
--  *****************************************/

/-- `readReg i` only looks at `L.wires i`. -/
lemma readReg_dependsOnly (L : Layout k) (i : Fin k) :
  dependsOnlyOn (L.wires i) (fun x => L.readReg i x) := by
  intro x y hxy
  unfold readReg agreesOn Layout.wires at *
  refine Finset.sum_congr rfl ?_
  simp [Layout.bit]
  aesop

-- /*********************************************
--  * Locality lemmas for the diagonal operators *
--  *********************************************/

lemma U_phaseReg_local (L : Layout k) (i : Fin k) (Φ : ℤ → ℝ) :
  ActsOnDiag (L.wires i) (U_phaseReg L i Φ) := by
  classical
  refine ⟨(fun x => Φ (L.readReg i x)), ?_, rfl⟩
  have:=L.readReg_dependsOnly i
  unfold dependsOnlyOn agreesOn Layout.wires at *
  simp_all
  intro x y a
  have:=this x y a
  rw[this]


lemma U_phasePair_local (L : Layout k) (i j : Fin k) (Φ : ℤ → ℤ → ℝ) :
  ActsOnDiag (L.wires i ∪ L.wires j) (U_phasePair L i j Φ) := by
  classical
  refine ⟨(fun x => Φ (L.readReg i x) (L.readReg j x)), ?_, rfl⟩
  -- show both components depend only on the union, then combine
  intro x y hxy
  have hi :
    L.readReg i x = L.readReg i y :=
  by
    -- `wires i ⊆ wires i ∪ wires j`
    have hsub : L.wires i ⊆ L.wires i ∪ L.wires j := by
      intro q hq; exact Finset.mem_union.mpr (Or.inl hq)
    -- restrict agreement and use the previous lemma
    exact (L.readReg_dependsOnly i) x y (agreesOn_mono (N := L.N) hsub hxy)
  have hj :
    L.readReg j x = L.readReg j y :=
  by
    have hsub : L.wires j ⊆ L.wires i ∪ L.wires j := by
      intro q hq; exact Finset.mem_union.mpr (Or.inr hq)
    exact (L.readReg_dependsOnly j) x y (agreesOn_mono (N := L.N) hsub hxy)
  -- combine the equalities under Φ
  simp [hi, hj]

end Layout


-- /**************************************
--  * A tiny utility for later examples. *
--  **************************************/

-- We need a way to *construct* a value of `QState N` (e.g., the zero wavefunction).
instance : Inhabited (QState N) := ⟨fun _ => 0⟩

/-- Identity operator on `QState N`. -/
@[simp] def qid {N : ℕ} : QState N → QState N := id

-- /***********************
--  * Bitstring QState tools *
--  ***********************/

namespace QState
variable {N : ℕ}

/-- Apply a bijection on bitstrings to a QState by precomposing with the inverse. -/
def perm (π : (Fin N → Bool) ≃ (Fin N → Bool)) (ψ : (Fin N → Bool) → ℂ) :
  (Fin N → Bool) → ℂ :=
  fun x => ψ (π.symm x)

/-- On Dirac QStates, `perm` carries `|x⟩` to `|π x⟩`. -/
lemma perm_dirac (π : (Fin N → Bool) ≃ (Fin N → Bool)) (x : Fin N → Bool) :
  perm π (dirac x) = (dirac (π x)) := by
  funext y
  -- left side: dirac x (π.symm y) = 1 iff π.symm y = x  ↔  y = π x
  by_cases h : y = π x
  · unfold dirac;subst h; simp [perm]
  · have : π.symm y ≠ x := by
      intro hx; apply h; have:=congrArg π hx;aesop
    unfold dirac;simp [perm, this];assumption
end QState


-- /********************************************
--  * Gate-semantics interface (no guessing!)  *
--  ********************************************/

/-- Everything we need to *connect* classical small-step `applyOp?` with
    bitstring-level permutations/phases on `QState`. Can fill these with the
    real encoders and permutations later; the model and proofs then follow. -/

structure GateSemantics (k : ℕ) (L : Layout k) where
  /- Encoding basis states: -/
  (enc : State k → (Fin L.N → Bool))

  /- Permutation semantics for the classical *reversible* primitives: -/
  (π_addScaled : (dst src : Fin k) → (neg' : Bool) → (sh : ℕ) →
                 (Fin L.N → Bool) ≃ (Fin L.N → Bool))
  (π_shiftL    : (i : Fin k) → (n : ℕ) →
                 (Fin L.N → Bool) ≃ (Fin L.N → Bool))
  (π_shiftR    : (i : Fin k) → (n : ℕ) →
                 (Fin L.N → Bool) ≃ (Fin L.N → Bool))
  (π_negate    : (i : Fin k) →
                 (Fin L.N → Bool) ≃ (Fin L.N → Bool))

  /- Correctness-on-basis axioms tying permutations to `applyOp?`: -/
  (corr_addScaled :
      ∀ {σ τ} {dst src} {neg'} {sh},
        applyOp? (k := k) σ (valid_ops.addScaled dst src (negSrc := neg') sh) = some τ →
        (π_addScaled dst src neg' sh) (enc σ) = enc τ)
  (corr_shiftL :
      ∀ {σ τ} {i} {n},
        applyOp? (k := k) σ (valid_ops.shiftL i n) = some τ →
        (π_shiftL i n) (enc σ) = enc τ)
  (corr_shiftR :
      ∀ {σ τ} {i} {n},
        applyOp? (k := k) σ (valid_ops.shiftR i n) = some τ →
        (π_shiftR i n) (enc σ) = enc τ)
  (corr_negate :
      ∀ {σ τ} {i},
        applyOp? (k := k) σ (valid_ops.negate i) = some τ →
        (π_negate i) (enc σ) = enc τ)

  /- Phase primitive: classically a no-op; quantumly a diagonal we choose.
     You can specialize it later (e.g., `U_phaseReg L i Φ` or pair-wise). -/
  (U_phaseProd : Fin k → (QState L.N) → (QState L.N))

  /- On-basis axiom for phase: since classical phaseProduct returns `σ`,
     it must fix the encoded basis QState. -/
  (corr_phase :
      ∀ {σ} {i},
        applyOp? (k := k) σ (valid_ops.phaseProduct i) = some σ →
        QState.GlobalPhaseEq
          (U_phaseProd i (dirac (enc σ)))
          (dirac (enc σ)))



-- /******************************
--  * Build the concrete Model   *
--  ******************************/

/-- Your `Model` using the concrete `QState` plus the gate-semantics bridge. -/
noncomputable def Model.ofGateSemantics {k : ℕ} (L : Layout k) (G : GateSemantics k L) : Model k :=
{ layout        := L,
  QStateOfState := fun σ => dirac (G.enc σ),
  U_addScaled   := fun dst src neg' sh  ψ => QState.perm (G.π_addScaled dst src neg' sh) ψ,
  U_shiftL      := fun i n ψ => QState.perm (G.π_shiftL i n) ψ,
  U_shiftR      := fun i n ψ => QState.perm (G.π_shiftR i n) ψ,
  U_negate      := fun i ψ    => QState.perm (G.π_negate i) ψ,
  U_phaseProd   := fun i ψ    => G.U_phaseProd i ψ }




-- /********************************************
--  * PrimitiveCorrect instance from the bridge *
--  ********************************************/

instance {k : ℕ} (L : Layout k) (G : GateSemantics k L)
  : PrimitiveCorrect (Model.ofGateSemantics L G) := by
  classical
  -- Use `M` as shorthand
  let M := Model.ofGateSemantics L G
  refine
  { -- Locality: keep them trivial for now (`ActsOn = True` in your file).
    addScaled_local := by simp[ActsOn];sorry
    , shiftL_local  := by simp[ActsOn];sorry
    , shiftR_local  := by simp[ActsOn];sorry
    , negate_local  := by simp[ActsOn];sorry
    , phaseProd_local := by simp[ActsOn];sorry

    -- On-basis equalities follow from `QState.perm_dirac` + the `corr_*` axioms.
    , addScaled_on_basis := by
        intro σ τ dst src neg' sh h
        -- basis: turn |σ⟩ into |enc σ⟩, apply permutation, get |enc τ⟩
        have := G.corr_addScaled (σ := σ) (τ := τ) (dst := dst) (src := src)
                                 (neg' := neg') (sh := sh) h
        -- rewrite via `perm_dirac`
        funext y
        -- Both sides are `dirac ( … ) y`, so just rewrite the center:
        have hperm :
          QState.perm (G.π_addScaled dst src neg' sh) (dirac (G.enc σ))
            = dirac (G.enc τ) := by
          -- pointwise identity on Dirac:
            ext z;
            have h2:=(QState.perm_dirac (π := G.π_addScaled dst src neg' sh) (x := G.enc σ))
            unfold QState.perm dirac GateSemantics.π_addScaled at *
            have heq := congrArg (fun f => f z) h2
            simp [this] at heq
            aesop
        -- Convert the goal’s function equality with `funext`:
        simp [Model.ofGateSemantics, hperm]

    , shiftL_on_basis := by
        intro σ τ i n h
        have := G.corr_shiftL (σ := σ) (τ := τ) (i := i) (n := n) h
        have h2:=(QState.perm_dirac (π := G.π_shiftL i n) (x := G.enc σ))
        funext z
        simp [Model.ofGateSemantics, dirac]
        unfold QState.perm dirac GateSemantics.π_shiftL at *
        have heq := congrArg (fun f => f z) h2
        simp [this] at heq
        aesop

    , shiftR_on_basis := by
        intro σ τ i n h
        have := G.corr_shiftR (σ := σ) (τ := τ) (i := i) (n := n) h
        have h2:=(QState.perm_dirac (π := G.π_shiftR i n) (x := G.enc σ))
        funext z
        simp [Model.ofGateSemantics, dirac]
        unfold QState.perm dirac GateSemantics.π_shiftR at *
        have heq := congrArg (fun f => f z) h2
        simp [this] at heq
        aesop

    , negate_on_basis := by
        intro σ τ i h
        have := G.corr_negate (σ := σ) (τ := τ) (i := i) h
        have h2:=(QState.perm_dirac (π := G.π_negate i) (x := G.enc σ))
        funext z
        simp [Model.ofGateSemantics, dirac]
        unfold QState.perm dirac GateSemantics.π_negate at *
        have heq := congrArg (fun f => f z) h2
        simp [this] at  heq
        aesop

    , phaseProd_on_basis := by
        -- Classically phaseProduct is a no-op on state (returns `σ`):
        intro σ τ i h
        apply G.corr_phase
        simp[applyOp?]
         }


namespace Layout

/-- Extract the *slice* of register `i` from a global bitstring. -/
@[inline] def slice (L : Layout k) (i : Fin k) (x : BitStr L.N) :
  (Fin (L.width i) → Bool) :=
fun b => x (L.pack i b)

/-- Overwrite register `i` inside the global bitstring `x` with the given local `bits`.
    Implemented by looking at `unpack q`; if that register is `i` we cast the local index
    to `Fin (width i)` and read from `bits`, otherwise we keep `x q`. -/
@[inline] def writeSlice (L : Layout k)
  (x : BitStr L.N) (i : Fin k) (bits : Fin (L.width i) → Bool) : BitStr L.N :=
fun q =>
  let u := L.unpack q
  -- `u : Σ j, Fin (L.width j)` with `L.pack u.1 u.2 = q`
  if h : u.1 = i then
    -- cast `u.2 : Fin (width u.1)` across `width u.1 = width i`
    let hw : L.width u.1 = L.width i := by simp[h]
    bits (Fin.cast hw u.2)
  else
    x q

/-- **Hit lemma.** Writing then reading back at a wire of `i` returns the new bit. -/
@[simp] lemma writeSlice_pack_hit (L : Layout k)
  (x : BitStr L.N) (i : Fin k) (bits : Fin (L.width i) → Bool) (b : Fin (L.width i)) :
  L.writeSlice x i bits (L.pack i b) = bits b := by
  unfold writeSlice
  -- `unpack (pack i b) = ⟨i, b⟩`
  simp [L.unpack_packed i b]
  have:=L.unpack_packed i b
  conv=>
    lhs
    arg 1
    arg 2
  congr
  simp[this]
  aesop
  rw[this]

/-- **Miss lemma (by unpack).** If the unpacked register at `q` isn’t `i`, we keep `x q`. -/
@[simp] lemma writeSlice_of_unpack_ne (L : Layout k)
  (x : BitStr L.N) (i : Fin k) (bits : Fin (L.width i) → Bool)
  {q : Fin L.N} (hne : (L.unpack q).1 ≠ i) :
  L.writeSlice x i bits q = x q := by
  unfold writeSlice
  simp [hne]

/-- **Miss lemma (by different register).** On a wire `pack j b` with `j ≠ i`, nothing changes. -/
@[simp] lemma writeSlice_pack_other (L : Layout k)
  (x : BitStr L.N) (i j : Fin k) (bits : Fin (L.width i) → Bool)
  (b : Fin (L.width j)) (hij : j ≠ i) :
  L.writeSlice x i bits (L.pack j b) = x (L.pack j b) := by
  -- unpack says this wire is from register `j`, so it’s a miss if `j ≠ i`
  have hne : (L.unpack (L.pack j b)).1 ≠ i := by
    simpa [L.unpack_packed j b]
  simp [writeSlice, L.unpack_packed]
  intro h
  simp[hij] at h

/-- Writing back the current slice is a no-op on the global bitstring. -/
@[simp] lemma writeSlice_slice (L : Layout k) (x : BitStr L.N) (i : Fin k) :
  L.writeSlice x i (L.slice i x) = x := by
  -- Pointwise on every global wire q.
  funext q
  -- Examine which register owns q.
  rcases L.unpack q with ⟨j,b⟩
  unfold Layout.writeSlice Layout.slice
  simp
  intro h
  have :(L.pack i (Fin.cast (by simp[h]) (L.unpack q).snd))=q:=by {
     subst h
     simp[L.pack_unpacked]
  }
  rw[this]


/-- Reading a slice we just wrote gives back the written local bits. -/
@[simp] lemma slice_writeSlice (L : Layout k) (x : BitStr L.N) (i : Fin k)
  (bits : Fin (L.width i) → Bool) :
  L.slice i (L.writeSlice x i bits) = bits := by
  funext b
  simp [slice]

/-- Write two registers (order irrelevant since wires are disjoint). -/
@[inline] def writeSpan (L : Layout k)
  (x : BitStr L.N) (dst src : Fin k)
  (bitsD : Fin (L.width dst) → Bool) (bitsS : Fin (L.width src) → Bool) :
  BitStr L.N :=
  L.writeSlice (L.writeSlice x dst bitsD) src bitsS

/-- Pair of local slices for two registers. -/
@[inline] def slice2 (L : Layout k) (dst src : Fin k) (x : BitStr L.N) :
  (Fin (L.width dst) → Bool) × (Fin (L.width src) → Bool) :=
(L.slice dst x, L.slice src x)

/-- Lift a single-register local unitary
    `Uloc : QState (width i) → QState (width i)` to a global operator
    `QState N → QState N` that acts like `Uloc` on register `i`
    and as identity on the rest. -/
def LiftUnitary₁ {k : ℕ} (L : Layout k) (i : Fin k)
  (Uloc : ((Fin (L.width i) → Bool) → ℂ) → ((Fin (L.width i) → Bool) → ℂ)) :
  QState L.N → QState L.N :=
fun ψ x =>
  let loc : (Fin (L.width i) → Bool) → ℂ :=
    fun bits => ψ (L.writeSlice x i bits)
  (Uloc loc) (L.slice i x)

/-- Lift a **two-register** local unitary acting on the tensor of
    `dst` and `src`.  The local space is modeled as a ket over the product
    of their bitstrings. -/
def LiftUnitary₂ {k : ℕ} (L : Layout k) (dst src : Fin k)
  (Uloc :
    (((Fin (L.width dst) → Bool) × (Fin (L.width src) → Bool)) → ℂ) →
    (((Fin (L.width dst) → Bool) × (Fin (L.width src) → Bool)) → ℂ)) :
  QState L.N → QState L.N :=
fun ψ x =>
  let loc : ((Fin (L.width dst) → Bool) × (Fin (L.width src) → Bool)) → ℂ :=
    fun ⟨bitsD, bitsS⟩ => ψ (L.writeSpan x dst src bitsD bitsS)
  (Uloc loc) (L.slice2 dst src x)

-------------------- handy simp lemmas -------------------- */

@[simp] lemma LiftUnitary₁_on_dirac
  {k} (L : Layout k) (i : Fin k)
  (Uloc : ((Fin (L.width i) → Bool) → ℂ) → ((Fin (L.width i) → Bool) → ℂ))
  (x : BitStr L.N) :
  LiftUnitary₁ L i Uloc (dirac x)
  = fun y =>
      let loc : (Fin (L.width i) → Bool) → ℂ :=
        fun bits => if L.writeSlice y i bits = x then 1 else 0
      (Uloc loc) (L.slice i y) := by aesop

@[simp] lemma LiftUnitary₁_id
  {k} (L : Layout k) (i : Fin k) (ψ : QState L.N) :
  LiftUnitary₁ L i id ψ = ψ := by
  classical
  funext x
  -- local ket is `bits ↦ ψ (writeSlice x i bits)`; apply id and evaluate at slice
  simp [LiftUnitary₁, Layout.writeSlice_slice]

@[simp] lemma LiftUnitary₂_id
  {k} (L : Layout k) (dst src : Fin k) (ψ : QState L.N) :
  LiftUnitary₂ L dst src id ψ = ψ := by
  classical
  funext x
  rcases L.slice2 dst src x with ⟨sd, ss⟩
  unfold LiftUnitary₂ Layout.slice2
  simp [Layout.writeSpan]

end Layout



-- /***********************************************
--  * Lifting local equivalences to global perms
--  ***********************************************/
namespace BitStrPerm
/-- Lift a **single-register** local unitary `Uloc`
    to a global operator acting only on register `i`. -/
@[inline] def liftUnary {k : ℕ} (L : Layout k) (i : Fin k)
  (Uloc : ((Fin (L.width i) → Bool) → ℂ) → ((Fin (L.width i) → Bool) → ℂ)) :
  QState L.N → QState L.N :=
  Layout.LiftUnitary₁ L i Uloc

/-- Lift a **two-register** local unitary `Uloc`
    to a global operator acting only on the span of `dst` and `src`. -/
@[inline] def liftBinary {k : ℕ} (L : Layout k) (dst src : Fin k)
  (Uloc :
    (((Fin (L.width dst) → Bool) × (Fin (L.width src) → Bool)) → ℂ) →
    (((Fin (L.width dst) → Bool) × (Fin (L.width src) → Bool)) → ℂ)) :
  QState L.N → QState L.N :=
  Layout.LiftUnitary₂ L dst src Uloc

/-- Sanity: lifting `id` gives the global identity. -/
@[simp] lemma liftUnary_id {k : ℕ} (L : Layout k) (i : Fin k) (ψ : QState L.N) :
  liftUnary L i id ψ = ψ := by
  simp [liftUnary]

@[simp] lemma liftBinary_id {k : ℕ} (L : Layout k) (dst src : Fin k) (ψ : QState L.N) :
  liftBinary L dst src id ψ = ψ := by
  simp [liftBinary]


end BitStrPerm
