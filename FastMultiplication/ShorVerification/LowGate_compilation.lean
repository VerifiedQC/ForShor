import FastMultiplication.ShorVerification.Basic

namespace Shor
open Gate


/-- A 1-qubit register at index `q`. -/
def qubitReg (q : ℕ) : Reg := ⟨q, q + 1⟩

/-- Standard QFT phase schedule. -/
noncomputable def qftPhi (m : ℕ) : ℝ := (2 * Real.pi) / (2^m)

/-!
## A lower-level gate language (post-lowering)
-/
inductive LowGate : Type
  | id : LowGate
  | seq : LowGate → LowGate → LowGate
  | adj : LowGate → LowGate
  | H : ℕ → LowGate
  | X : ℕ → LowGate
  | Prim : String → List ℕ → LowGate
deriving Inhabited

namespace LowGate
infixr:80 " ;; " => LowGate.seq
prefix:90 "†" => LowGate.adj
end LowGate

/-!
## Abstract lowering hooks for PhaseProd
We don't define how PhaseProd is decomposed yet; we just assume
there is some lowering procedure that produces LowGate code.
-/
opaque lowerPhaseProd  : (phi : ℝ) → (x z : Reg) → LowGate
opaque lowerCPhaseProd : (ctrl : ℕ) → (phi : ℝ) → (x z : Reg) → LowGate

/-!
## Lower QFT into `LowGate`
-/
noncomputable def lowerQFTAux : ℕ → Reg → LowGate
  | 0,   _ => .id
  | 1,   r => .H r.lo
  | n+2, r =>
      let nTot : ℕ := n + 2
      let m : ℕ := nTot / 2
      let left  : Reg := ⟨r.lo, r.lo + m⟩
      let right : Reg := ⟨r.lo + m, r.hi⟩
      (lowerQFTAux (nTot - m) right) ;;
      (lowerPhaseProd (qftPhi nTot) left right) ;;
      (lowerQFTAux m left)

noncomputable def lowerQFT (r : Reg) : LowGate :=
  lowerQFTAux (regSize r) r

/--
Lower a high-level `Gate` into `LowGate` by eliminating `QFT`, `PhaseProd`,
and `CPhaseProd`.
-/
noncomputable def lowerGate : Gate → LowGate
  | .id => .id
  | .seq U V => (lowerGate U) ;; (lowerGate V)
  | .adj U => †(lowerGate U)
  | .H q => .H q
  | .X q => .X q
  | .QFT r => lowerQFT r
  | .PhaseProd p x z => lowerPhaseProd p x z
  | .CPhaseProd c p x z => lowerCPhaseProd c p x z
  | .Prim tag args => .Prim tag args

namespace LowGate
@[simp] lemma lowerGate_id : lowerGate Gate.id = (LowGate.id) := rfl
@[simp] lemma lowerGate_seq (U V : Gate) :
    lowerGate (U ;; V) = (lowerGate U) ;; (lowerGate V) := by
  simp [lowerGate]
@[simp] lemma lowerGate_adj (U : Gate) :
    lowerGate (†U) = †(lowerGate U) := rfl
@[simp] lemma lowerGate_QFT (r : Reg) :
    lowerGate (Gate.QFT r) = lowerQFT r := rfl
@[simp] lemma lowerGate_PP (p : ℝ) (x z : Reg) :
    lowerGate (Gate.PhaseProd p x z) = lowerPhaseProd p x z := rfl
@[simp] lemma lowerGate_CPP (c : ℕ) (p : ℝ) (x z : Reg) :
    lowerGate (Gate.CPhaseProd c p x z) = lowerCPhaseProd c p x z := rfl
end LowGate

/-- Rest-size arithmetic used in the peel induction. -/
@[simp] lemma regSize_rest (r : Reg) :
    regSize (⟨r.lo + 1, r.hi⟩ : Reg) = regSize r - 1 := by
  simp [regSize, Nat.sub_sub]

/-!
## Semantics interface (no embedding LowGate → Gate)
We assume an evaluator for LowGate on the same state space as `qs.eval`,
plus compatibility axioms for shared primitives, and correctness axioms
for the abstract lowering hooks.
-/
class LowerGateClass (qs : QSemantics) : Type where
  /- low-level evaluator -/
  evalL : LowGate → qs.State → qs.State
  evalL_id  : ∀ ψ, evalL LowGate.id ψ = ψ
  evalL_seq : ∀ (U V : LowGate) (ψ : qs.State),
      evalL (U ;; V) ψ = evalL V (evalL U ψ)

  /- compatibility for overlapping primitives -/
  evalL_H :
    ∀ (q : ℕ) (ψ : qs.State),
      evalL (.H q) ψ = qs.eval (.H q) ψ

  evalL_X :
    ∀ (q : ℕ) (ψ : qs.State),
      evalL (.X q) ψ = qs.eval (.X q) ψ

  evalL_Prim :
    ∀ (tag : String) (args : List ℕ) (ψ : qs.State),
      evalL (.Prim tag args) ψ = qs.eval (Gate.Prim tag args) ψ

  /- correctness of PhaseProd lowering -/
  evalL_lowerPhaseProd :
    ∀ (p : ℝ) (x z : Reg) (ψ : qs.State),
      evalL (lowerPhaseProd p x z) ψ = qs.eval (Gate.PhaseProd p x z) ψ

  evalL_lowerCPhaseProd :
    ∀ (c : ℕ) (p : ℝ) (x z : Reg) (ψ : qs.State),
      evalL (lowerCPhaseProd c p x z) ψ = qs.eval (Gate.CPhaseProd c p x z) ψ

  /- dagger bridge for lowered programs -/
  evalL_adj_of_lowered :
    ∀ (U : Gate) (ψ : qs.State),
      evalL (†(lowerGate U)) ψ = qs.eval (†U) ψ

  /- QFT axioms  -/
  eval_QFT_size0 :
    ∀ (r : Reg) (ψ : qs.State),
      regSize r = 0 → qs.eval (Gate.QFT r) ψ = qs.eval Gate.id ψ

  eval_QFT_size1 :
    ∀ (r : Reg) (ψ : qs.State),
      regSize r = 1 → qs.eval (Gate.QFT r) ψ = qs.eval (Gate.H r.lo) ψ

  eval_QFT_split :
    ∀ (r : Reg) (ψ : qs.State),
      regSize r ≥ 2 →
      let nTot  : ℕ := regSize r
      let m     : ℕ := nTot / 2
      let left  : Reg := ⟨r.lo, r.lo + m⟩
      let right : Reg := ⟨r.lo + m, r.hi⟩
      qs.eval (Gate.QFT r) ψ
        =
      qs.eval ((Gate.QFT right) ;;
               (Gate.PhaseProd (qftPhi nTot) left right) ;;
               (Gate.QFT left)) ψ

attribute [simp] LowerGateClass.evalL_id
attribute [simp] LowerGateClass.evalL_seq


/-- Useful arithmetic lemmas about register sizes. -/
@[simp] lemma regSize_mk (a m : ℕ) :
    regSize (⟨a, a + m⟩ : Reg) = m := by
  simp [regSize]

@[simp] lemma regSize_right_of_split (r : Reg) (m : ℕ) :
    regSize (⟨r.lo + m, r.hi⟩ : Reg) = regSize r - m := by
  simp [regSize, Nat.sub_sub]


lemma eval_lowerQFTAux_strong
  (qs : QSemantics) [LowerGateClass qs] :
  ∀ n : ℕ, ∀ (r : Reg) (ψ : qs.State),
    regSize r = n →
    (LowerGateClass.evalL (qs := qs) (lowerQFTAux n r) ψ) = qs.eval (Gate.QFT r) ψ := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n IH r ψ hsz
  cases n with
  | zero =>
      -- n = 0
      have hQ := LowerGateClass.eval_QFT_size0 (qs := qs) r ψ hsz
      simpa [lowerQFTAux, QSemantics.eval_id] using hQ.symm

  | succ n1 =>
      cases n1 with
      | zero =>
          have hQ := LowerGateClass.eval_QFT_size1 (qs := qs) r ψ hsz
          simpa [lowerQFTAux, LowerGateClass.evalL_H (qs := qs)] using hQ.symm

      | succ n' =>

          let nTot : ℕ := n' + 2

          let m : ℕ := nTot / 2
          let left  : Reg := ⟨r.lo,     r.lo + m⟩
          let right : Reg := ⟨r.lo + m, r.hi⟩

          have hleft : regSize left = m := by
            simp [left, regSize_mk]
          have hright : regSize right = nTot - m := by
            have : regSize right = regSize r - m := by
              simp [right, regSize_right_of_split]
            simp [this, hsz, nTot]

          have hm_lt : m < nTot := by
            have hnTot_pos : 0 < nTot := Nat.succ_pos _
            simpa [m] using Nat.div_lt_self hnTot_pos (by decide : 1 < (2 : ℕ))

          have hm_ne0 : m ≠ 0 := by
            intro hm0
            have hdiv0 : nTot / 2 = 0 ↔ nTot < 2 := by simp
            have hnTot_lt2 : nTot < 2 := (hdiv0).1 (by simpa [m] using hm0)
            have : ¬ nTot < 2 := by
              exact Nat.not_lt_of_ge (Nat.le_add_left 2 n')
            exact this hnTot_lt2
          have hright_lt : nTot - m < nTot := by
            have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne0
            omega

          have ihL :
              LowerGateClass.evalL (qs := qs) (lowerQFTAux m left) ψ
                = qs.eval (Gate.QFT left) ψ :=
            (IH m hm_lt) left ψ hleft

          have ihR :
              LowerGateClass.evalL (qs := qs) (lowerQFTAux (nTot - m) right) ψ
                = qs.eval (Gate.QFT right) ψ :=
            (IH (nTot - m) hright_lt) right ψ hright

          -- QFT split axiom
          have hsplit :
              qs.eval (Gate.QFT r) ψ
                =
              qs.eval ((Gate.QFT right) ;;
                       (Gate.PhaseProd (qftPhi nTot) left right) ;;
                       (Gate.QFT left)) ψ := by
            have : regSize r ≥ 2 := by simp[hsz]
            have :=(LowerGateClass.eval_QFT_split (qs := qs) r ψ this)
            simp
            rw[this]
            simp
            have hnTot : nTot = regSize r := by
              simpa [nTot] using hsz.symm
            simp [left, right, m, hnTot, qftPhi]

          calc
            LowerGateClass.evalL (qs := qs) (lowerQFTAux nTot r) ψ
                =
              LowerGateClass.evalL (qs := qs) (lowerQFTAux m left)
                (LowerGateClass.evalL (qs := qs) (lowerPhaseProd (qftPhi nTot) left right)
                  (LowerGateClass.evalL (qs := qs) (lowerQFTAux (nTot - m) right) ψ)) := by
                  simp [lowerQFTAux, nTot, m, left, right, LowerGateClass.evalL_seq (qs := qs)]
            _ =
              qs.eval (Gate.QFT left)
                (qs.eval (Gate.PhaseProd (qftPhi nTot) left right)
                  (qs.eval (Gate.QFT right) ψ)) := by
                  simp [LowerGateClass.evalL_lowerPhaseProd (qs := qs),ihR]
                  aesop
            _ =
              qs.eval ((Gate.QFT right) ;;
                       (Gate.PhaseProd (qftPhi nTot) left right) ;;
                       (Gate.QFT left)) ψ := by
                  simp
            _ =
              qs.eval (Gate.QFT r) ψ := by
                  simpa using hsplit.symm
/-!
## Derived: lowered QFT simulates primitive QFT
-/
lemma eval_lowerQFT
  (qs : QSemantics) [LowerGateClass qs] :
  ∀ (r : Reg) (ψ : qs.State),
    (LowerGateClass.evalL (qs := qs) (lowerQFT r) ψ) = qs.eval (Gate.QFT r) ψ := by
  intro r ψ
  have main :
    ∀ (n : ℕ) (r : Reg) (ψ : qs.State),
      regSize r = n →
      (LowerGateClass.evalL (qs := qs) (lowerQFTAux n r) ψ) = qs.eval (Gate.QFT r) ψ := by
    intro n
    induction n with
    | zero =>
        intro r ψ hsz
        have hQ := LowerGateClass.eval_QFT_size0 (qs := qs) r ψ hsz
        simpa [lowerQFTAux, QSemantics.eval_id] using hQ.symm
    | succ n ih =>
        cases n with
        | zero =>
            intro r ψ hsz
            have hQ := LowerGateClass.eval_QFT_size1 (qs := qs) r ψ hsz
            simpa [lowerQFTAux, LowerGateClass.evalL_H (qs := qs)] using hQ.symm
        | succ n =>
            intro r ψ hsz
            simpa using (eval_lowerQFTAux_strong (qs := qs) (n + 2) r ψ hsz)

  simpa [lowerQFT] using main (regSize r) r ψ rfl

/-!
## Whole-program correctness
-/
theorem lowerGate_correctness (G : Gate) (qs : QSemantics) [LowerGateClass qs] :
  ∀ ψ, (LowerGateClass.evalL (qs := qs) (lowerGate G) ψ) = qs.eval G ψ := by
  intro ψ
  induction G generalizing ψ with
  | id =>
      simp [lowerGate, QSemantics.eval_id]
  | H q =>
      simp [lowerGate, LowerGateClass.evalL_H (qs := qs)]
  | X q =>
      simp [lowerGate, LowerGateClass.evalL_X (qs := qs) q]
  | PhaseProd p x z =>
      simpa [lowerGate] using (LowerGateClass.evalL_lowerPhaseProd (qs := qs) p x z ψ)
  | CPhaseProd c p x z =>
      simpa [lowerGate] using (LowerGateClass.evalL_lowerCPhaseProd (qs := qs) c p x z ψ)
  | QFT r =>
      simpa [lowerGate] using (eval_lowerQFT (qs := qs) r ψ)
  | seq U V ihU ihV =>
      calc
        LowerGateClass.evalL (qs := qs) (lowerGate (U ;; V)) ψ
            =
        LowerGateClass.evalL (qs := qs) (lowerGate V)
          (LowerGateClass.evalL (qs := qs) (lowerGate U) ψ) := by
              simp [lowerGate, LowerGateClass.evalL_seq (qs := qs)]
        _ =
        LowerGateClass.evalL (qs := qs) (lowerGate V) (qs.eval U ψ) := by
              simpa using congrArg
                (fun t => LowerGateClass.evalL (qs := qs) (lowerGate V) t) (ihU ψ)
        _ =
        qs.eval V (qs.eval U ψ) := by
              simpa using (ihV (qs.eval U ψ))
        _ =
        qs.eval (U ;; V) ψ := by
              simp
  | adj U ih =>
      simpa [lowerGate] using (LowerGateClass.evalL_adj_of_lowered (qs := qs) U ψ)
  | Prim tag args =>
      simp[lowerGate, LowerGateClass.evalL_Prim (qs := qs) tag args ψ]

end Shor
