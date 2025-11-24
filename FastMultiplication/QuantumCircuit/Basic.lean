import FastMultiplication.one_reg_synth_proof_2

open scoped BigOperators
open Classical

/-! ########################
     Register → Qubit Layout
######################## -/


structure Layout (k : ℕ) where
  (width  : Fin k → ℕ) -- Number of qubits in register i
  (N      : ℕ) -- Total number of qubits in the state
  (pack   : ∀ i : Fin k, Fin (width i) → Fin N) -- Takes a register index and an index within the register and returns the global qubit index
  (unpack : Fin N → Σ i : Fin k, Fin (width i)) -- Takes a global qubit index and returns the register i and the index within the register
  (pack_unpacked : ∀ q, pack (unpack q).1 (unpack q).2 = q) -- Packing can invert unpacking
  (unpack_packed : ∀ i b, unpack (pack i b) = ⟨i, b⟩) -- Unpacking can invert packing

namespace Layout

variable {k : ℕ} (L : Layout k)

/-- Finset of global wires used by register `i`. -/
def wires (i : Fin k) : Finset (Fin L.N) :=
  (Finset.univ : Finset (Fin (L.width i))).image (fun b => L.pack i b)

/-- For two registers, the union of their wires. -/
def span (dst src : Fin k) : Finset (Fin L.N) :=
  L.wires dst ∪ L.wires src

/-- Strong injectivity fact packaged at the σ-type level. -/
lemma pack_sigma_inj
  {i j : Fin k} {a : Fin (L.width i)} {b : Fin (L.width j)}
  (h : L.pack i a = L.pack j b) :
  (Sigma.mk i a : Σ t, Fin (L.width t)) = ⟨j, b⟩ := by
  have := congrArg L.unpack h
  -- `unpack (pack i a) = ⟨i,a⟩`, same for the RHS
  simpa [L.unpack_packed] using this

/-- First components coincide if the globals coincide. -/
lemma pack_fst_inj
  {i j : Fin k} {a : Fin (L.width i)} {b : Fin (L.width j)}
  (h : L.pack i a = L.pack j b) :
  i = j :=
  congrArg Sigma.fst (L.pack_sigma_inj h)

/-- No two distinct registers share a global wire. -/
lemma wires_disjoint {i j : Fin k} (hij : i ≠ j) :
  Disjoint (L.wires i) (L.wires j) := by
  refine Finset.disjoint_left.mpr ?_
  intro q hqi hqj
  rcases Finset.mem_image.mp hqi with ⟨ai, _, hpacki⟩
  rcases Finset.mem_image.mp hqj with ⟨bj, _, hpackj⟩
  have h : L.pack i ai = L.pack j bj := by
    -- both equal `q`
    simp [hpacki, hpackj]
  exact hij (L.pack_fst_inj h)

/-- Every global wire belongs to (the image of) some register. -/
lemma mem_wires_of_cover (q : Fin L.N) :
  ∃ i, q ∈ L.wires i := by
  have :=L.pack_unpacked q
  rcases L.unpack q with ⟨i, b⟩
  use (L.unpack q).fst
  -- Show `q` is in the image of `pack i` over all local bits of `i`.
  change q ∈ (Finset.univ : Finset (Fin (L.width ((L.unpack q).fst)))).image (fun b => L.pack ((L.unpack q).fst) b)
  simp
  use (L.unpack q).snd

end Layout

/-- Classical state of `N` qubits: just an `N`-bit string. -/
abbrev BitStr (N : ℕ) := Fin N → Bool

/-- Update a single wire. -/
def setBit {N : ℕ} (x : BitStr N) (q : Fin N) (b : Bool) : BitStr N :=
  fun r => if h : r = q then b else x r


namespace Layout


/-- Value of a bitvector at position `b`. -/
def bitOf {n} (v : BitVec n) (b : Fin n) : Bool :=
  Nat.testBit v.toNat b

/-- Interpret register `i` as a bitvector, reading from the global bitstring `x`.
    We treat local index `b` as the bit with weight `2^b`. -/
def readReg {k : ℕ} (L : Layout k) (x : BitStr L.N) (i : Fin k) : BitVec (L.width i) :=
  let val : Nat :=
    ∑ b : Fin (L.width i),
      if x (L.pack i b) then (2 : Nat) ^ (b : Nat) else 0
  BitVec.ofNat (L.width i) val

/-- Overwrite all wires of register `i` with the bits of the bitvector `v`
    (in little-endian order: position `b` has weight `2^b`). -/
def writeReg {k : ℕ} (L : Layout k) (x : BitStr L.N) (i : Fin k) (v : BitVec (L.width i)) :
  BitStr L.N :=
  fun q =>
    match L.unpack q with
    | ⟨j, b⟩ =>
      if h : j = i then
        -- cast the local index to match `i` and read that bit from `v`
        let b' : Fin (L.width i) := cast (by cases h; rfl) b
        bitOf v b'
      else
        x q

/-- A classical circuit on global states of size `N`. -/
abbrev Circuit (N : ℕ) := BitStr N → BitStr N

namespace Circuit
/-- Sequential composition: run `c₁` then `c₂`. -/
def seq {N} (c₁ c₂ : Circuit N) : Circuit N :=
  fun s => c₂ (c₁ s)

infixl:80 " ⋙ " => Circuit.seq
end Circuit


/-- ADD on a triple `(x : m bits, y : n bits, c : 1 bit)`.

    Semantics: interpret `(y,c)` as an (n+1)-bit integer, add `x`, and
    write the result back into `(y',c')` modulo `2^(n+1)`.
-/
def ADD_gate (m n : Nat) :
    BitVec m × BitVec n × Bool →
    BitVec m × BitVec n × Bool
| (x, y, c) =>
  let base  := Nat.pow 2 n
  let base1 := Nat.pow 2 (n+1)

  let xNat  := x.toNat
  let yNat  := y.toNat
  let cNat  := if c then base else 0
  let sum   := xNat + yNat + cNat

  let sum'    := sum % base1
  let lowNat  := sum' % base
  let highNat := sum' / base   -- in {0,1}

  let y' : BitVec n := BitVec.ofNat n lowNat
  let c' : Bool     := (highNat % 2 = 1)

  (x, y', c')


/-- Precondition you’ll usually assume: the carry wire does not belong
    to either register `dst` or `src`. -/
def carryFresh{k : ℕ} (L : Layout k) (dst src : Fin k) (carry : Fin L.N) : Prop :=
  carry ∉ L.wires dst ∧ carry ∉ L.wires src

/-- Classical ADD on the global layout:
    given registers `src`, `dst` and a single overflow wire `carry`,
    perform `(x, y, carry) ↦ (x, y+x, carry')` where `x` is `src` and
    `y,carry` are `dst` plus overflow.
-/

def ADD_on_layout{k : ℕ} (L : Layout k) (dst src : Fin k) (carry : Fin L.N) :
    Circuit L.N :=
  fun σ =>
    let xVal : BitVec (L.width src) := L.readReg σ src
    let yVal : BitVec (L.width dst) := L.readReg σ dst
    let cVal : Bool := σ carry

    let triple' := ADD_gate (L.width src) (L.width dst) (xVal, yVal, cVal)
    let xVal'   := triple'.1
    let yVal'   := triple'.2.1
    let cVal'   := triple'.2.2

    -- update the two registers and the carry wire
    let σ₁ := L.writeReg σ src xVal'   -- x is unchanged, but this keeps spec symmetric
    let σ₂ := L.writeReg σ₁ dst yVal'
    let σ₃ := setBit σ₂ carry cVal'
    σ₃


namespace Example

variable (L : Layout 2)

-- names for the two registers:
def xReg : Fin 2 := ⟨0, by decide⟩
def yReg : Fin 2 := ⟨1, by decide⟩

/-- Interpret `(y,c)` as an (n+1)-bit integer. -/
def ycVal {n : ℕ} (y : BitVec n) (c : Bool) : ℕ :=
  let base := 2 ^ n
  y.toNat + (if c then base else 0)


-- convenience:
abbrev N : ℕ := L.N
abbrev State := BitStr L.N

lemma ADD_gate_spec (m n : ℕ) (x : BitVec m) (y : BitVec n) (c : Bool) :
  let base1 := 2 ^ (n+1)
  let sum   := x.toNat + ycVal y c
  let triple' := ADD_gate m n (x,y,c)
  let x' := triple'.1
  let y' := triple'.2.1
  let c' := triple'.2.2
  x' = x ∧ ycVal y' c' = sum % base1 := by
  -- TODO: prove using BitVec.ofNat/toNat lemmas + modular arithmetic
  admit



open Layout

/-- Layout-level ADD on `L`, adding `xReg` into `yReg` using a chosen carry wire. -/
def add2 (carry : Fin L.N) : Circuit L.N :=
  fun σ =>
    -- read local values
    let xVal : BitVec (L.width (xReg)) := L.readReg σ (xReg)
    let yVal : BitVec (L.width (yReg)) := L.readReg σ (yReg)
    let cVal : Bool := σ carry

    let triple' := ADD_gate (L.width (xReg)) (L.width (yReg)) (xVal, yVal, cVal)
    let xVal'   := triple'.1
    let yVal'   := triple'.2.1
    let cVal'   := triple'.2.2

    -- write back
    let σ₁ := L.writeReg σ (xReg) xVal'   -- x is unchanged, but we stick with the pattern
    let σ₂ := L.writeReg σ₁ (yReg) yVal'
    let σ₃ := setBit σ₂ carry cVal'
    σ₃
















/-! ########################
     Quantum-side scaffolding
######################## -/

/-- Abstract QState type for `N` qubits. -/
def BitStr (N : ℕ) := Fin N → Bool
def QState (N : ℕ) := BitStr N
-- QState n is a type for all n-qubit states

/-- `sameOutside W x y` means `x` and `y` agree on all qubits *outside* `W`. -/
def sameOutside {N : ℕ}
    (W : Finset (Fin N)) (x y : BitStr N) : Prop :=
  ∀ q : Fin N, q ∉ W → x q = y q
-- Tell Lean that bitstrings have decidable equality.
instance instDecidableEqBitstr (N : ℕ) : DecidableEq (BitStr N) := by
  dsimp [BitStr]; infer_instance


/-- Your denotational model, now carrying the fixed layout. -/
structure Model (k : ℕ) where
  (layout     : Layout k) --Layout of the model (How many qubits per register and how many total qubits. Packing and unpacking, etc.)
  (QStateOfState : State k → QState layout.N) -- Function to turn the classical state to a QState
  (U_addScaled : (dst src : Fin k) → (neg' : Bool) → (sh : ℕ) → (QState layout.N → QState layout.N))
  (U_shiftL    : (i : Fin k) → (n : ℕ) → (QState layout.N → QState layout.N))
  (U_shiftR    : (i : Fin k) → (n : ℕ) → (QState layout.N → QState layout.N))
  (U_negate    : (i : Fin k) →           (QState layout.N → QState layout.N))
  (U_phaseProd : (i : Fin k) →           (QState layout.N → QState layout.N))

namespace Model
variable {k : ℕ} (M : Model k)

def wires (i : Fin k) : Finset (Fin M.layout.N) := M.layout.wires i

def span  (dst src : Fin k) : Finset (Fin M.layout.N) := M.layout.span dst src
end Model

namespace QState
def GlobalPhaseEq {N} (ψ ψ' : QState N) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∀ x, ψ' x = c * ψ x
end QState

open Operations
/-- Strengthened primitive-correctness relative to the layout. -/
class PrimitiveCorrect (M : Model k) : Prop where

  (addScaled_local : ∀ dst src neg' sh, ActsOn (M.span dst src) (M.U_addScaled dst src neg' sh))
  (shiftL_local    : ∀ i n, ActsOn (M.wires i) (M.U_shiftL i n))
  (shiftR_local    : ∀ i n, ActsOn (M.wires i) (M.U_shiftR i n))
  (negate_local    : ∀ i,   ActsOn (M.wires i) (M.U_negate i))
  (phaseProd_local : ∀ i,   ActsOn (M.wires i) (M.U_phaseProd i))
  -- On-basis agreement
  (addScaled_on_basis :
    ∀ {σ τ} {dst src} {neg'} {sh} ,
      applyOp? (k := k) σ (valid_ops.addScaled dst src (negSrc := neg') sh) = some τ →
      M.U_addScaled dst src neg' sh (M.QStateOfState σ) = M.QStateOfState τ)
  (shiftL_on_basis :
    ∀ {σ τ i n},
      applyOp? (k := k) σ (valid_ops.shiftL i n) = some τ →
      M.U_shiftL i n (M.QStateOfState σ) = M.QStateOfState τ)
  (shiftR_on_basis :
    ∀ {σ τ i n},
      applyOp? (k := k) σ (valid_ops.shiftR i n) = some τ →
      M.U_shiftR i n (M.QStateOfState σ) = M.QStateOfState τ)
  (negate_on_basis :
    ∀ {σ τ i},
      applyOp? (k := k) σ (valid_ops.negate i) = some τ →
      M.U_negate i (M.QStateOfState σ) = M.QStateOfState τ)
  (phaseProd_on_basis :
    ∀ {σ τ i},
      applyOp? (k := k) σ (valid_ops.phaseProduct i) = some τ →
      QState.GlobalPhaseEq
      (M.U_phaseProd i (M.QStateOfState σ))
      (M.QStateOfState σ))


/-- One addScaled never changes any register `t ≠ dst`. -/
@[simp] lemma addScaledReg_preserves_of_ne
  (σ : State k) (dst src t : Fin k) (neg' : Bool) (sh : ℕ)
  (hne : t ≠ dst) :
  (State.addScaledReg σ dst src (negSrc := neg') sh) t = σ t := by
  simp [State.addScaledReg, hne]

/-- In particular, an addScaled into `dst` preserves the **source** register,
    provided `dst ≠ src`. -/
@[simp] lemma addScaledReg_preserves_src
  (σ : State k) (dst src : Fin k) (neg' : Bool) (sh : ℕ)
  (hne : dst ≠ src) :
  (State.addScaledReg σ dst src (negSrc := neg') sh) src = σ src := by
  have : src ≠ dst := by simpa [ne_comm] using hne
  simpa using addScaledReg_preserves_of_ne (σ := σ) (dst := dst) (src := src) (t := src) (neg' := neg') (sh := sh) this


/-- **Classical no-touch for a whole block**:
    running a list of `addScaled dst src (neg',sh)` leaves `src` unchanged
    (diagram: `X` preserved). -/
lemma run_map_pairToOp_preserves_src
  (dst src : Fin k) (pairs : List (Bool × Nat))
  (hne : dst ≠ src) :
  ∀ {σ τ : State k},
    run? (pairs.map (pairToOp (k := k) dst src)) σ = some τ →
    τ src = σ src := by
  intro σ τ hrun
  revert σ
  induction pairs with
  | nil =>
      intro σ h; simp_all
  | cons p ps ih =>
      intro σ h
      -- first step is an addScaled, then recurse
      have hstep :
        applyOp? (k := k) σ (pairToOp (k := k) dst src p)
          = some (State.addScaledReg σ dst src (negSrc := p.1) p.2) := by
        cases p;simp [pairToOp]
      have htail := run_tail_of_head (k := k) (op := pairToOp (k := k) dst src p)
                       (ps := ps.map (pairToOp (k := k) dst src))
                       (σ := σ) (τ := State.addScaledReg σ dst src (negSrc := p.1) p.2)
                       (σ₂ := τ) hstep h
      -- src after whole run = src after tail run = src after head step
      calc
        τ src
            = (State.addScaledReg σ dst src (negSrc := p.1) p.2) src := by
                -- unwrap the previous line (just a rewrite trick)
                simpa using ih (σ := State.addScaledReg σ dst src (negSrc := p.1) p.2) htail
        _ = (State.addScaledReg σ dst src (negSrc := p.1) p.2) src := rfl
        _ = σ src := addScaledReg_preserves_src (σ := σ) (dst := dst) (src := src)
                        (neg' := p.1) (sh := p.2) hne


/-! ########################################
    2) Quantum on-basis for that block
######################################## -/

open Model

/-- Compose the denotation for a whole add-block (left-to-right). -/
def U_addBlock (M : Model k) (dst src : Fin k) :
  List (Bool × Nat) → (QState M.layout.N → QState M.layout.N)
| []        => id
| (b,sh)::t => fun ψ => U_addBlock M dst src t (M.U_addScaled dst src b sh ψ)

/-- On-basis correctness for the whole add-block, provided primitives are correct. -/
lemma U_addBlock_on_basis
  (M : Model k) [PrimitiveCorrect M]
  (dst src : Fin k) (pairs : List (Bool × Nat))
  {σ τ : State k}
  (hrun : run? (pairs.map (pairToOp (k := k) dst src)) σ = some τ) :
  U_addBlock M dst src pairs (M.QStateOfState σ) = M.QStateOfState τ := by {
    revert σ
    induction pairs with
    | nil =>
        intro σ h; simp at h; unfold U_addBlock; simp[h]
    | cons p ps ih =>
        intro σ h
        -- first operational step
        have hstep :
          applyOp? (k := k) σ (pairToOp (k := k) dst src p)
            = some (State.addScaledReg σ dst src (negSrc := p.1) p.2) := by
          cases p; simp [pairToOp]
        have htail := run_tail_of_head (k := k) (op := pairToOp (k := k) dst src p)
                        (ps := ps.map (pairToOp (k := k) dst src))
                        (σ := σ) (τ := State.addScaledReg σ dst src (negSrc := p.1) p.2)
                        (σ₂ := τ) hstep h
        -- use primitive on-basis correctness for the head, then IH for the tail
        cases p with
        | mk b sh =>
          simp [U_addBlock]     -- unfold one layer of composition
          -- head primitive step on basis:
          have hhead :
            M.U_addScaled dst src b sh (M.QStateOfState σ)
              = M.QStateOfState (State.addScaledReg σ dst src (negSrc := b) sh) := by
            have:= (PrimitiveCorrect.addScaled_on_basis
                    (M := M) (σ := σ)
                    (τ := State.addScaledReg σ dst src (negSrc := b) sh)
                    (dst := dst) (src := src) (neg' := b) (sh := sh) hstep)
            apply this
          -- tail
          have:= ih (σ := State.addScaledReg σ dst src (negSrc := b) sh) htail
          have hfull :
              U_addBlock M dst src ((b, sh) :: ps) (M.QStateOfState σ)
                = M.QStateOfState τ := by
            -- apply the IH to the tail, started from the post-head classical state,
            -- and rewrite the starting ket using the on-basis head correctness `hhead`.
            simp[U_addBlock];rw[← this]
            simp_all
          simpa [U_addBlock] using hfull
  }

  /-! ########################################
    3) A combined statement matching the picture
######################################## -/

/-- “Adder block correctness”: if we build Y := Y + X by a list of
    `addScaled Y X (…)`, then (i) the **source X is preserved** classically,
    and (ii) the **quantum denotation** on basis states lines up with `run?`. -/
theorem inplaceAdder_block_correct
  (M : Model k) [PrimitiveCorrect M]
  (X Y : Fin k) (pairs : List (Bool × Nat))
  (hne : Y ≠ X)
  {σ τ : State k}
  (hrun : run? (pairs.map (pairToOp (k := k) Y X)) σ = some τ) :
  (τ X = σ X) ∧
  (U_addBlock M Y X pairs (M.QStateOfState σ) = M.QStateOfState τ) := by
  apply And.intro
  ·
    exact run_map_pairToOp_preserves_src (dst := Y) (src := X) (pairs := pairs) hne hrun
  ·
    exact U_addBlock_on_basis (M := M) (dst := Y) (src := X) (pairs := pairs) hrun
