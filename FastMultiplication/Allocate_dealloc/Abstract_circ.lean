import FastMultiplication.one_reg_synth_proof_2
import FastMultiplication.one_reg_synth_proof_2

namespace AbstractFM

universe u

class QuantumModel where
  Qubit : Type u
  fresh : Qubit

structure Reg [QuantumModel] : Type u where
  len  : ℕ
  data : ℕ  → QuantumModel.Qubit

def St (k:ℕ) [QuantumModel] := Fin k → Reg

def allocReg [QuantumModel] (r : Reg) (lsb : Bool) (n : Nat) : Reg :=
  if lsb then
    { len  := r.len + n
      data := fun i =>
        if i < n then QuantumModel.fresh else r.data (i - n) }
  else
    { len  := r.len + n
      data := fun i =>
        if i < r.len then r.data i
        else if i < r.len + n then QuantumModel.fresh
        else r.data i }


def freeReg [QuantumModel] (r : Reg) (lsb : Bool) (n : Nat) : Reg :=
  if _h : n ≤ r.len then
    if lsb then
      { len  := r.len - n
        data := fun i => r.data (i + n) }
    else
      { len  := r.len - n
        data := r.data }
  else
    { len  := 0
      data := r.data }

class RegOps [QuantumModel] where
  add    : Reg → Reg → Reg
  negate : Reg → Reg

inductive prim_ops (k : ℕ) where
  | Alloc         (i : Fin k) (lsb: Bool) (n : ℕ)
  | Free          (i : Fin k) (lsb: Bool) (n : ℕ)
  | negate        (i : Fin k)
  | Add           (dst src : Fin k)
  | phaseProduct  (i : Fin k)

def eval_prim_op_single [QuantumModel] [RegOps] {k : ℕ}
    (op : prim_ops k) (σ : St k) : St k :=
  match op with
  | prim_ops.Alloc i lsb n =>
      fun j => if j = i then allocReg (σ i) lsb n else σ j

  | prim_ops.Free i lsb n =>
      fun j => if j = i then freeReg (σ i) lsb n else σ j

  | prim_ops.negate i =>
      fun j => if j = i then RegOps.negate (σ i) else σ j

  | prim_ops.Add dst src =>
      fun j => if j = dst then RegOps.add (σ dst) (σ src) else σ j

  | prim_ops.phaseProduct _ =>
      σ

open Operations

/-- Set the `idx`-th entry of a list (if in range). Otherwise leave the list unchanged. -/
def setAt {α : Type} : List α → Nat → α → List α
  | [],      _,      _ => []
  | _ :: xs, 0,      a => a :: xs
  | x :: xs, idx+1,  a => x :: setAt xs idx a
/-- Get `lens[idx]` with a default if out of range. -/
def getLen (curLen : List Nat) (idx : Nat) : Nat :=
  curLen.getD idx 1

def setLen {k : ℕ} (curLen : List Nat) (i : Fin k) (v : Nat) : List Nat :=
  setAt curLen i.val v

def incLen {k : ℕ} (curLen : List Nat) (i : Fin k) (n : Nat) : List Nat :=
  setLen curLen i (getLen curLen i.val + n)

def decLen {k : ℕ} (curLen : List Nat) (i : Fin k) (n : Nat) : List Nat :=
  setLen curLen i (getLen curLen i.val - n)


def compiled_addScaled (dst src: Fin k) (negSrc:Bool) (sh:ℕ) (curLen : List Nat):=
  if dst = src then
        ([], curLen, [])
  else
    let negops : List (prim_ops k) :=
      if negSrc then [prim_ops.negate src] else []

    -- (1) src <<= sh  (LSB alloc)
    let shiftOps : List (prim_ops k) :=
      if sh = 0 then [] else [prim_ops.Alloc src true sh]
    let curLen1 := incLen curLen src sh

    -- (2) optional negate(src) (no length change)
    let curLen2 := curLen1

    -- lengths *after* the shift (and possible negate doesn't change length)
    let lenDst := getLen curLen2 dst.val
    let lenSrc := getLen curLen2 src.val

    -- choose a common target width
    let target := 1 + Nat.max lenDst lenSrc

    -- (3a) widen dst at MSB to target (remember to free at end)
    let deltaDst := target - lenDst
    let widenDstOps : List (prim_ops k) :=
      if deltaDst = 0 then [] else [prim_ops.Alloc dst false deltaDst]
    let curLen3 := incLen curLen2 dst deltaDst
    let msbAdds : List (Fin k × Nat) :=
      if deltaDst = 0 then [] else [(dst, deltaDst)]

    -- (3b) widen src at MSB to target (temporary; free immediately later)
    let deltaSrc := target - lenSrc
    let widenSrcOps : List (prim_ops k) :=
      if deltaSrc = 0 then [] else [prim_ops.Alloc src false deltaSrc]
    let curLen4 := incLen curLen3 src deltaSrc

    -- (4) dst += src  (now same width)
    let adder : List (prim_ops k) := [prim_ops.Add dst src]

    -- (5) undo negate(src)
    let unNegOps : List (prim_ops k) := negops

    -- (6) undo shift (LSB free)
    let unShiftOps : List (prim_ops k) :=
      if sh = 0 then [] else [prim_ops.Free src true sh]
    let curLen5 := decLen curLen4 src sh

    -- (7) free the temporary MSB widen of src
    let freeSrcOps : List (prim_ops k) :=
      if deltaSrc = 0 then [] else [prim_ops.Free src false deltaSrc]
    let curLen6 := decLen curLen5 src deltaSrc

    (negops ++ shiftOps ++ widenDstOps ++ widenSrcOps ++ adder ++ unNegOps ++ unShiftOps ++ freeSrcOps,
      curLen6,
      msbAdds)

/-- Just the program part. -/
def compiled_addScaled_prog {k : ℕ}
  (dst src : Fin k) (negSrc : Bool) (sh : ℕ) (curLen : List Nat) : List (prim_ops k) :=
  (compiled_addScaled (k := k) dst src negSrc sh curLen).1


def compile_op_to_prim_single {k : ℕ} (op : valid_ops k) (curLen : List Nat) :
    (List (prim_ops k)) × (List Nat) × (List (Fin k × Nat)) :=
match op with
  | .shiftL i n =>
      -- LSB shift scaffolding => lsb = true in your evaluator
      ([prim_ops.Alloc i true n], incLen curLen i n, [])

  | .shiftR i n =>
      ([prim_ops.Free i true n], decLen curLen i n, [])

  | .negate i =>
      ([prim_ops.negate i], curLen, [])

  | .phaseProduct i =>
      ([prim_ops.phaseProduct i], curLen, [])

  | .addScaled dst src negSrc sh =>
      compiled_addScaled dst src negSrc sh curLen

def compile_valid_ops {k : ℕ} (ops : List (valid_ops k)) :
    List (prim_ops k) :=
  let initLen : Nat := 0
  let initCurLen : List Nat := List.replicate k initLen
  -- main loop: build primOps in forward order (we'll accumulate with ++ for clarity)
  let rec go (ops : List (valid_ops k))
             (curLen : List Nat)
             (msbStack : List (Fin k × Nat))
             (out : List (prim_ops k)) : List (prim_ops k) :=
    match ops with
    | [] =>
        let frees : List (prim_ops k) :=
          msbStack.map (fun p => prim_ops.Free p.1 false p.2)
        out ++ frees
    | op :: ops' =>
        let (ops1, curLen1, msbAdds) := compile_op_to_prim_single (k := k) op curLen
        let msbStack1 := msbAdds ++ msbStack
        go ops' curLen1 msbStack1 (out ++ ops1)

  go ops initCurLen [] []



def compile1 {k : ℕ} (v : valid_ops k) (curLen : List Nat) : List (prim_ops k) :=
  (compile_op_to_prim_single (k := k) v curLen).1

def evalPrimProg [QuantumModel] [RegOps] {k : ℕ} :
    List (prim_ops k) → St k → St k
  | [],      σ => σ
  | op :: ps, σ => evalPrimProg ps (eval_prim_op_single (k := k) op σ)



lemma evalPrimProg_cons [QuantumModel] [RegOps] {k : ℕ}
  (op : prim_ops k) (ps : List (prim_ops k)) (σ : St k) :
  evalPrimProg (k := k) (op :: ps) σ
    = evalPrimProg (k := k) ps (eval_prim_op_single (k := k) op σ) := rfl

lemma evalPrimProg_append [QuantumModel] [RegOps] {k : ℕ}
  (p q : List (prim_ops k)) (σ : St k) :
  evalPrimProg (k := k) (p ++ q) σ
    = evalPrimProg (k := k) q (evalPrimProg (k := k) p σ) := by
  induction p generalizing σ with
  | nil =>
      simp [evalPrimProg]
  | cons op ps ih =>
      simp [evalPrimProg, ih]



abbrev MatchesAtStateBit [QuantumModel] (k : ℕ) := St k → Fin k → Operations.Point → Bool

/-- Remove the first element satisfying a Bool predicate; fail if none. -/
def eraseFirstMatchB {α : Type} (p : α → Bool) : List α → Option (List α)
  | []      => none
  | x :: xs =>
      if p x then
        some xs
      else
        match eraseFirstMatchB p xs with
        | none      => none
        | some xs'  => some (x :: xs')


def runPhaseCoverage {k : ℕ} [QuantumModel] [RegOps] (M : MatchesAtStateBit k) :
    List (prim_ops k) → St k → List Operations.Point → Option (St k × List Operations.Point)
  | [], σ, pts => some (σ, pts)
  | op :: ps, σ, pts =>
      match op with
      | prim_ops.phaseProduct i =>
          match eraseFirstMatchB (fun pt => M σ i pt) pts with
          | none      => none
          | some pts' => runPhaseCoverage M ps σ pts'
      | _ =>
          -- your semantics are total, so we always step
          let σ' := eval_prim_op_single (k := k) op σ
          runPhaseCoverage M ps σ' pts

/-- Bool check: true iff all points get consumed by phaseProduct steps. -/
def phaseProductCoverage? {k : ℕ} [QuantumModel] [RegOps](M : MatchesAtStateBit k)
    (prog : List (prim_ops k)) (σ : St k) (pts : List Operations.Point) : Bool :=
  match runPhaseCoverage (k := k) M prog σ pts with
  | some (_, []) => true
  | _            => false

/-- Update a single register in a `St k` state. -/
def St.set {k : ℕ} [QuantumModel] (σ : St k) (i : Fin k) (r : Reg) : St k :=
  fun j => if j = i then r else σ j

/-- Allocate `n` fresh qubits into register `i` (LSB/MSB controlled by `lsb`). -/
def St.alloc {k : ℕ} [QuantumModel] (σ : St k) (i : Fin k) (lsb : Bool) (n : ℕ) : St k :=
  St.set (k := k) σ i (allocReg (σ i) lsb n)

/-- Free `n` qubits from register `i` (LSB/MSB controlled by `lsb`). -/
def St.free {k : ℕ} [QuantumModel] (σ : St k) (i : Fin k) (lsb : Bool) (n : ℕ) : St k :=
  St.set (k := k) σ i (freeReg (σ i) lsb n)

/-- Negate register `i`. -/
def St.negate {k : ℕ} [QuantumModel] [RegOps] (σ : St k) (i : Fin k) : St k :=
  St.set (k := k) σ i (RegOps.negate (σ i))

/-- Add register `src` into `dst`. -/
def St.add {k : ℕ} [QuantumModel] [RegOps] (σ : St k) (dst src : Fin k) : St k :=
  St.set (k := k) σ dst (RegOps.add (σ dst) (σ src))





class DecodeBackend (k : ℕ) [QuantumModel] [RegOps] where
  decodeRegister : Reg → Register k

  /-- Decode a whole abstract state into a classical state. -/
  decodeState : St k → State k :=
    fun σ => fun i => decodeRegister (σ i)

  decode_allocLsb_ax :
    ∀ (σQ : St k) (i : Fin k) (n : ℕ),
      decodeState (St.alloc (k := k) σQ i true n)
        = State.shiftLReg (decodeState σQ) i n

  decode_freeLsb_ax :
    ∀ (σQ : St k) (i : Fin k) (n : ℕ),
      State.shiftRReg? (decodeState σQ) i n
        = some (decodeState (St.free (k := k) σQ i true n))

  decode_negate_ax :
    ∀ (σQ : St k) (i : Fin k),
      decodeState (St.negate (k := k) σQ i)
        = State.negateReg (decodeState σQ) i

  decode_add_ax :
    ∀ (σQ : St k) (dst src : Fin k),
      decodeState (St.add (k := k) σQ dst src)
        = State.addScaledReg (decodeState σQ) dst src false 0

  decode_allocMsb_ax :
    ∀ (σQ : St k) (i : Fin k) (n : ℕ),
      decodeState (St.alloc (k := k) σQ i false n)
        = decodeState σQ

  decode_freeMsb_ax :
    ∀ (σQ : St k) (i : Fin k) (n : ℕ),
      decodeState (St.free (k := k) σQ i false n)
        = decodeState σQ

  decode_compiled_addScaled_ax :
    ∀ (σQ : St k) (dst src : Fin k) (negSrc : Bool) (sh : ℕ) (curLen : List Nat) (_hds : dst≠src),
      some (decodeState (evalPrimProg (k := k)
              (compiled_addScaled_prog (k := k) dst src negSrc sh curLen) σQ))
        = some (State.addScaledReg (decodeState σQ) dst src negSrc sh)

open DecodeBackend

theorem decode_allocLsb
  {k : ℕ} [QuantumModel] [RegOps] [DecodeBackend k]
  (σQ : St k) (i : Fin k) (n : ℕ) :
  decodeState (fun j => if j = i then allocReg (σQ i) true n else σQ j)
    = State.shiftLReg (decodeState σQ) i n := by
  -- literally the axiom, rewritten through decodeState
  simpa [decodeState] using (DecodeBackend.decode_allocLsb_ax (k := k) σQ i n)

theorem decode_freeLsb
  {k : ℕ} [QuantumModel] [RegOps] [DecodeBackend k]
  (σQ : St k) (i : Fin k) (n : ℕ) :
  State.shiftRReg? (decodeState σQ) i n
    = some (decodeState (fun j => if j = i then freeReg (σQ i) true n else σQ j)) := by
  simpa [decodeState] using (DecodeBackend.decode_freeLsb_ax (k := k) σQ i n)

theorem decode_negateReg
  {k : ℕ} [QuantumModel] [RegOps] [DecodeBackend k]
  (σQ : St k) (i : Fin k) :
  decodeState (fun j => if j = i then RegOps.negate (σQ i) else σQ j)
    = State.negateReg (decodeState σQ) i := by
  simpa [decodeState] using (DecodeBackend.decode_negate_ax (k := k) σQ i)

theorem decode_addReg
  {k : ℕ} [QuantumModel] [RegOps] [DecodeBackend k]
  (σQ : St k) (dst src : Fin k) :
  decodeState (fun j => if j = dst then RegOps.add (σQ dst) (σQ src) else σQ j)
    = State.addScaledReg (decodeState σQ) dst src false 0 := by
  simpa [decodeState] using (DecodeBackend.decode_add_ax (k := k) σQ dst src)


theorem decode_allocMsb
  {k : ℕ} [QuantumModel] [RegOps] [DecodeBackend k]
  (σQ : St k) (i : Fin k) (n : ℕ) :
  decodeState (fun j => if j = i then allocReg (σQ i) false n else σQ j)
    = decodeState σQ := by
  simpa [decodeState] using (DecodeBackend.decode_allocMsb_ax (k := k) σQ i n)

theorem decode_freeMsb
  {k : ℕ} [QuantumModel] [RegOps] [DecodeBackend k]
  (σQ : St k) (i : Fin k) (n : ℕ) :
  decodeState (fun j => if j = i then freeReg (σQ i) false n else σQ j)
    = decodeState σQ := by
  simpa [decodeState] using (DecodeBackend.decode_freeMsb_ax (k := k) σQ i n)





theorem compile1_respects_decode_addScaled
  {k : ℕ} [QuantumModel] [RegOps] [DecodeBackend k]
  (St1 : St k) (curLen : List Nat)
  (dst src : Fin k) (negSrc : Bool) (sh : ℕ)
  (hWF : dst≠src) :
  some (decodeState (k := k)
        (evalPrimProg (k := k) (compile1 (k := k) (.addScaled dst src negSrc sh) curLen) St1))
    =
  applyOp? (k := k) (decodeState (k := k) St1) (.addScaled dst src negSrc sh) := by
  simp [compile1, compile_op_to_prim_single]
  have hdec :=
    DecodeBackend.decode_compiled_addScaled_ax
      (k := k) (σQ := St1) (dst := dst) (src := src)
      (negSrc := negSrc) (sh := sh) (curLen := curLen) hWF
  simpa [applyOp?] using hdec


theorem compile1_respects_decode
  {k : ℕ} [QuantumModel] [RegOps] [DecodeBackend k]
  (St1 : St k) (v : valid_ops k) (curLen : List Nat) (hWF:Prog.OpOK v):
  some (decodeState (k := k) (evalPrimProg (k := k) (compile1 (k := k) v curLen) St1))
    = applyOp? (k := k) (decodeState (k := k) St1) v := by
  cases v with
  | shiftL i n =>
      simp [compile1, compile_op_to_prim_single, evalPrimProg, eval_prim_op_single,
            applyOp?]
      apply decode_allocLsb

  | shiftR i n =>
      have h := (decode_freeLsb (k := k) (σQ := St1) i n).symm
      simp [compile1, compile_op_to_prim_single, evalPrimProg, eval_prim_op_single,
            applyOp?] at *
      simp[h]

  | negate i =>
      simp [compile1, compile_op_to_prim_single, evalPrimProg, eval_prim_op_single,
            applyOp?, decode_negateReg]

  | phaseProduct i =>
      simp [compile1, compile_op_to_prim_single, evalPrimProg, eval_prim_op_single,
            applyOp?]
  | addScaled dst src negSrc sh =>
      apply compile1_respects_decode_addScaled
      simp[Prog.OpOK] at hWF
      simp[hWF]



end AbstractFM
