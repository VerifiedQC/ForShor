import TableGeneration.Language

namespace TableGeneration

open Operations

def arithmeticOperationCount {k : Nat} : Prog k -> Nat
  | [] => 0
  | op :: ops =>
      match op with
      | .phaseProduct _ => arithmeticOperationCount ops
      | _ => arithmeticOperationCount ops + 1

def phaseProductCount {k : Nat} : Prog k -> Nat
  | [] => 0
  | op :: ops =>
      match op with
      | .phaseProduct _ => phaseProductCount ops + 1
      | _ => phaseProductCount ops

def parallelPhaseProductLayerCountAux {k : Nat} : Bool -> Prog k -> Nat
  | _, [] => 0
  | inLayer, op :: ops =>
      match op with
      | .phaseProduct _ =>
          (if inLayer then 0 else 1) + parallelPhaseProductLayerCountAux true ops
      | _ => parallelPhaseProductLayerCountAux false ops

def parallelPhaseProductLayerCount {k : Nat} (ops : Prog k) : Nat :=
  parallelPhaseProductLayerCountAux false ops

end TableGeneration
