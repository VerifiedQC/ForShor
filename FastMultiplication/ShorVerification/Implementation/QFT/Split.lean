import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.Shared.Registers

/-!
# QFT Register Splitting

Recursive QFT splits a register into a low/right half and a high/left half.
These definitions fix that convention and provide the small containment
facts used when reusing the same workspace pools recursively.
-/

namespace Shor

open Gate

/-! =========================================================
    Register splitting and clean workspaces

    Recursive QFT splits a register into a low/right half and a high/left
    half. These definitions fix that convention and provide the small
    containment facts used when reusing the same workspace pools recursively.
========================================================= -/

variable (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]

def splitM (r : Reg) : ℕ := (regSize r) / 2
def halfSplitPoint (r : Reg) : SplitPoint r :=
  ⟨splitM r, by
    simpa [splitM] using Nat.div_le_self (regSize r) 2⟩

def leftReg  (r : Reg) : Reg := splitLeft r (halfSplitPoint r)
def rightReg (r : Reg) : Reg := splitRight r (halfSplitPoint r)

lemma leftReg_mem_parent (r : Reg) {q : ℕ} (hq : q ∈ (leftReg r).qubits) : q ∈ r.qubits := by
  simpa [leftReg, halfSplitPoint, splitM, splitLeft, Reg.take] using List.mem_of_mem_take hq

lemma rightReg_mem_parent (r : Reg) {q : ℕ} (hq : q ∈ (rightReg r).qubits) : q ∈ r.qubits := by
  simpa [rightReg, halfSplitPoint, splitM, splitRight, Reg.drop] using List.mem_of_mem_drop hq

lemma disjoint_left_right (r : Reg) :
    Disjoint (leftReg r) (rightReg r) := by
  simpa [leftReg, rightReg] using
    (splitLeft_splitRight_disjoint (r := r) (m := halfSplitPoint r))

end Shor
