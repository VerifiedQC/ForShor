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




end AbstractFM
