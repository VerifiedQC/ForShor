import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Language

open Operations

namespace Table_Generation

def arithmeticOperationCount {k : ℕ} : Prog k → ℕ
  | [] => 0
  | op :: ops =>
      match op with
      | .phaseProduct _ => arithmeticOperationCount ops
      | _ => arithmeticOperationCount ops + 1

def phaseProductCount {k : ℕ} : Prog k → ℕ
  | [] => 0
  | op :: ops =>
      match op with
      | .phaseProduct _ => phaseProductCount ops + 1
      | _ => phaseProductCount ops

def parallelPhaseProductLayerCountAux {k : ℕ} : Bool → Prog k → ℕ
  | _, [] => 0
  | inLayer, op :: ops =>
      match op with
      | .phaseProduct _ =>
          (if inLayer then 0 else 1) + parallelPhaseProductLayerCountAux true ops
      | _ => parallelPhaseProductLayerCountAux false ops

def parallelPhaseProductLayerCount {k : ℕ} (ops : Prog k) : ℕ :=
  parallelPhaseProductLayerCountAux false ops

end Table_Generation
