import ILPEncoding.Labels.Final

/-! # Checked ILP Rows
Defines the integer variables and `AffineExpr` with its evaluation, the row builders `terminalRow`, `contractionRows` and `budgetRow`, and the predicate `Feasible`. Proves evaluation and iff lemmas for these rows, and `feasible_to_actual_cost` and `canonical_to_feasible` linking feasibility to actual costs.
-/

/- BEGIN Affine.lean transformed_from_sha256=fd7421d85002f650f841fbfa8fc716c21f128453c467508a531eb50e0a6a4625 -/
namespace Paper.F6ILP

open Paper.AffineNat Paper.AffineILP

def usedArities (labels : List Paper.AffineNat.Label) : Finset Nat :=
  (labels.map Paper.AffineNat.Label.k).toFinset

abbrev Variable (labels : List Paper.AffineNat.Label) :=
  { k : Nat // k ∈ usedArities labels }

theorem variable_count (labels : List Paper.AffineNat.Label) :
    Fintype.card (Variable labels) = (usedArities labels).card := by
  simp [Variable]

structure AffineExpr (keys : Finset Nat) where
  intercept : ℤ
  coeff : { k : Nat // k ∈ keys } → ℤ

def AffineExpr.eval {keys : Finset Nat} (e : AffineExpr keys)
    (a : Nat → Nat) : ℤ :=
  e.intercept + ∑ key : { k : Nat // k ∈ keys },
    e.coeff key * (a key.val : ℤ)

def startExpr (keys : Finset Nat) (x : ℤ) : AffineExpr keys where
  intercept := x
  coeff := fun _ => 0

theorem startExpr_eval (keys : Finset Nat) (x : ℤ) (a : Nat → Nat) :
    (startExpr keys x).eval a = x := by
  simp [AffineExpr.eval, startExpr]

def offsetConstant (label : Paper.AffineNat.Label) : ℤ :=
  1 + max 0 ((label.r : ℤ) - label.d)

def stepExpr {keys : Finset Nat} (e : AffineExpr keys) (P : ℤ)
    (label : Paper.AffineNat.Label) (hk : label.k ∈ keys) :
    AffineExpr keys where
  intercept := e.intercept + (P * label.k) * offsetConstant label - P * label.r
  coeff := fun j => e.coeff j +
    if j = (⟨label.k, hk⟩ : { k : Nat // k ∈ keys }) then P * label.k else 0

theorem stepExpr_eval {keys : Finset Nat} (e : AffineExpr keys)
    (P : ℤ) (label : Paper.AffineNat.Label) (hk : label.k ∈ keys)
    (a : Nat → Nat) :
    (stepExpr e P label hk).eval a =
      nextWidth P (e.eval a) (Paper.AffineNat.instantiate a label) := by
  simp [AffineExpr.eval, stepExpr, offsetConstant,
    Finset.sum_add_distrib, add_mul, Finset.sum_ite_eq']
  simp [Paper.AffineILP.nextWidth, Paper.AffineNat.instantiate,
    Paper.AffineShared.instantiate, Paper.AffineShared.offset,
    Paper.AffineNat.aInt, Paper.AffineNat.Label.toInt]
  ring

end Paper.F6ILP
/- END Affine.lean -/

/- BEGIN Constraints.lean transformed_from_sha256=facadaf21bc431afe43e732d78ae4779d381f2a895a53dab5d06507a2d59025b -/
namespace Paper.F6ILPRows

open Paper.F6ILP Paper.AffineNat Paper.AffineILP Paper.AffineChain

def subExpr {keys : Finset Nat} (e f : AffineExpr keys) :
    AffineExpr keys where
  intercept := e.intercept - f.intercept
  coeff := fun k => e.coeff k - f.coeff k

def scaleExpr {keys : Finset Nat} (z : ℤ) (e : AffineExpr keys) :
    AffineExpr keys where
  intercept := z * e.intercept
  coeff := fun k => z * e.coeff k

theorem eval_subExpr {keys : Finset Nat} (e f : AffineExpr keys)
    (a : Nat → Nat) :
    (subExpr e f).eval a = e.eval a - f.eval a := by
  simp [AffineExpr.eval, subExpr, sub_mul, Finset.sum_sub_distrib]
  ring

theorem eval_scaleExpr {keys : Finset Nat} (z : ℤ)
    (e : AffineExpr keys) (a : Nat → Nat) :
    (scaleExpr z e).eval a = z * e.eval a := by
  simp [AffineExpr.eval, scaleExpr, mul_add,
    mul_assoc, Finset.mul_sum]

def terminalExpr {keys : Finset Nat} (P : ℤ) (e : AffineExpr keys) :
    (labels : List Paper.AffineNat.Label) →
    (∀ label ∈ labels, label.k ∈ keys) → AffineExpr keys
  | [], _ => e
  | label :: rest, hkeys =>
      terminalExpr (P * label.k)
        (stepExpr e P label (hkeys label (by simp))) rest
        (by intro q hq; exact hkeys q (by simp [hq]))

theorem terminalExpr_eval {keys : Finset Nat} (P : ℤ) (e : AffineExpr keys)
    (labels : List Paper.AffineNat.Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys) (a : Nat → Nat) :
    (terminalExpr P e labels hkeys).eval a =
      terminalWidth P (e.eval a)
        (labels.map (Paper.AffineNat.instantiate a)) := by
  induction labels generalizing P e with
  | nil => rfl
  | cons label rest ih =>
      let hk := hkeys label (by simp)
      let hrest : ∀ q ∈ rest, q.k ∈ keys := by
        intro q hq
        exact hkeys q (by simp [hq])
      change (terminalExpr (P * label.k) (stepExpr e P label hk)
        rest hrest).eval a =
        terminalWidth (P * label.k)
          (nextWidth P (e.eval a) (Paper.AffineNat.instantiate a label))
          (rest.map (Paper.AffineNat.instantiate a))
      rw [ih (P * label.k) (stepExpr e P label hk) hrest]
      rw [stepExpr_eval]

def contractionExpr {keys : Finset Nat} (e next : AffineExpr keys)
    (P : ℤ) (label : Paper.AffineNat.Label) : AffineExpr keys :=
  subExpr (scaleExpr label.k e)
    (subExpr next (startExpr keys (-(P * label.k))))

theorem contractionExpr_eval {keys : Finset Nat} (e next : AffineExpr keys)
    (P : ℤ) (label : Paper.AffineNat.Label) (a : Nat → Nat) :
    (contractionExpr e next P label).eval a =
      label.k * e.eval a - next.eval a - P * label.k := by
  simp [contractionExpr, eval_subExpr, eval_scaleExpr,
    startExpr_eval]
  ring

def contractionRows {keys : Finset Nat} (P : ℤ) (e : AffineExpr keys) :
    (labels : List Paper.AffineNat.Label) →
    (∀ label ∈ labels, label.k ∈ keys) → List (AffineExpr keys)
  | [], _ => []
  | label :: rest, hkeys =>
      let next := stepExpr e P label (hkeys label (by simp))
      contractionExpr e next P label ::
        contractionRows (P * label.k) next rest
          (by intro q hq; exact hkeys q (by simp [hq]))

theorem contractionRows_iff {keys : Finset Nat} (P : ℤ)
    (e : AffineExpr keys) (labels : List Paper.AffineNat.Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys) (a : Nat → Nat) :
    (contractionRows P e labels hkeys).Forall
      (fun row => 0 ≤ row.eval a) ↔
    ClearedContractions P (e.eval a)
      (labels.map (Paper.AffineNat.instantiate a)) := by
  induction labels generalizing P e with
  | nil => rfl
  | cons label rest ih =>
      let hk := hkeys label (by simp)
      let next := stepExpr e P label hk
      let hrest : ∀ q ∈ rest, q.k ∈ keys := by
        intro q hq
        exact hkeys q (by simp [hq])
      simp only [contractionRows, List.forall_cons, List.map_cons,
        ClearedContractions]
      rw [contractionExpr_eval, stepExpr_eval]
      have hfirst :
          (0 ≤ label.k * e.eval a -
            nextWidth P (e.eval a) (Paper.AffineNat.instantiate a label) -
            P * label.k) ↔
          P * (Paper.AffineNat.instantiate a label).k ≤
            (Paper.AffineNat.instantiate a label).k * e.eval a -
            nextWidth P (e.eval a) (Paper.AffineNat.instantiate a label) := by
        change (0 ≤ label.k * e.eval a -
          nextWidth P (e.eval a) (Paper.AffineNat.instantiate a label) -
          P * label.k) ↔
          P * label.k ≤ label.k * e.eval a -
            nextWidth P (e.eval a) (Paper.AffineNat.instantiate a label)
        omega
      have htail := ih (P * label.k) next hrest
      rw [stepExpr_eval] at htail
      exact and_congr hfirst htail

end Paper.F6ILPRows
/- END Constraints.lean -/

/- BEGIN Rows.lean transformed_from_sha256=aea586304c3e87b6439cb2129071f9b3b6d49e75aa9ac9b5013bf0b796e8a6f1 -/
namespace Paper.F6ILPCost

open Paper.F6ILP Paper.F6ILPRows Paper.AffineNat Paper.AffineILP
open Paper.F6Cleared Paper.F6Objective

def addExpr {keys : Finset Nat} (e f : AffineExpr keys) : AffineExpr keys where
  intercept := e.intercept + f.intercept
  coeff := fun k => e.coeff k + f.coeff k

theorem eval_addExpr {keys : Finset Nat} (e f : AffineExpr keys)
    (a : Nat → Nat) :
    (addExpr e f).eval a = e.eval a + f.eval a := by
  simp [AffineExpr.eval, addExpr, add_mul, Finset.sum_add_distrib]
  ring

def clearedExpr {keys : Finset Nat} (D : ℤ) (c : Nat → Nat)
    (N : Nat) (P : ℤ) (e : AffineExpr keys) :
    (labels : List Paper.AffineNat.Label) →
    (∀ label ∈ labels, label.k ∈ keys) → AffineExpr keys
  | [], _ => startExpr keys 0
  | label :: rest, hkeys =>
      let next := stepExpr e P label (hkeys label (by simp))
      let term := scaleExpr (8 * (N : ℤ) * (c label.k : ℤ))
        (subExpr (scaleExpr (D / (P * label.k)) next)
          (startExpr keys D))
      addExpr term
        (clearedExpr D c (N * (2 * (label.k - 1) + 1))
          (P * label.k) next rest
          (by intro q hq; exact hkeys q (by simp [hq])))

theorem clearedExpr_eval {keys : Finset Nat} (D : ℤ) (c : Nat → Nat)
    (N : Nat) (P : ℤ) (e : AffineExpr keys)
    (labels : List Paper.AffineNat.Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys) (a : Nat → Nat) :
    (clearedExpr D c N P e labels hkeys).eval a =
      clearedSum D a c N P (e.eval a) labels := by
  induction labels generalizing N P e with
  | nil => simp [clearedExpr, clearedSum, startExpr_eval]
  | cons label rest ih =>
      let hk := hkeys label (by simp)
      let next := stepExpr e P label hk
      let hrest : ∀ q ∈ rest, q.k ∈ keys := by
        intro q hq
        exact hkeys q (by simp [hq])
      change (addExpr
        (scaleExpr (8 * (N : ℤ) * (c label.k : ℤ))
          (subExpr (scaleExpr (D / (P * label.k)) next)
            (startExpr keys D)))
        (clearedExpr D c (N * (2 * (label.k - 1) + 1))
          (P * label.k) next rest hrest)).eval a =
        8 * (N : ℤ) * (c label.k : ℤ) *
          ((D / (P * label.k)) *
            nextWidth P (e.eval a) (Paper.AffineNat.instantiate a label) - D) +
        clearedSum D a c (N * (2 * (label.k - 1) + 1))
          (P * label.k)
          (nextWidth P (e.eval a) (Paper.AffineNat.instantiate a label)) rest
      rw [eval_addExpr, eval_scaleExpr, eval_subExpr,
        eval_scaleExpr, startExpr_eval]
      rw [ih (N * (2 * (label.k - 1) + 1)) (P * label.k) next hrest]
      rw [stepExpr_eval]

theorem mem_usedArities {labels : List Paper.AffineNat.Label}
    {label : Paper.AffineNat.Label} (h : label ∈ labels) :
    label.k ∈ usedArities labels := by
  simp only [usedArities, List.mem_toFinset]
  exact List.mem_map.mpr ⟨label, h, rfl⟩

def rootExpr (labels : List Paper.AffineNat.Label) (x : ℤ) :
    AffineExpr (usedArities labels) :=
  startExpr (usedArities labels) x

theorem terminalProduct_independent (P : ℤ)
    (labels : List Paper.AffineNat.Label) (a b : Nat → Nat) :
    terminalProduct P (labels.map (Paper.AffineNat.instantiate a)) =
      terminalProduct P (labels.map (Paper.AffineNat.instantiate b)) := by
  induction labels generalizing P with
  | nil => rfl
  | cons label rest ih =>
      change terminalProduct (P * label.k)
        (rest.map (Paper.AffineNat.instantiate a)) =
        terminalProduct (P * label.k)
          (rest.map (Paper.AffineNat.instantiate b))
      exact ih (P * label.k)

def terminalRow (labels : List Paper.AffineNat.Label)
    (x z : ℤ) : AffineExpr (usedArities labels) :=
  subExpr
    (terminalExpr 1 (rootExpr labels x) labels
      (by intro label h; exact mem_usedArities h))
    (startExpr (usedArities labels)
      (terminalProduct 1
        (labels.map (Paper.AffineNat.instantiate (fun _ => 0))) * z))

theorem terminalRow_eval (labels : List Paper.AffineNat.Label)
    (x z : ℤ) (a : Nat → Nat) :
    (terminalRow labels x z).eval a =
      terminalWidth 1 x
        (labels.map (Paper.AffineNat.instantiate a)) -
      terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) * z := by
  rw [terminalRow, eval_subExpr, terminalExpr_eval]
  simp only [startExpr_eval, rootExpr]
  congr 1
  exact congrArg (fun n : ℤ => n * z)
    (terminalProduct_independent 1 labels (fun _ => 0) a)

end Paper.F6ILPCost
/- END Rows.lean -/

/- BEGIN Finite.lean transformed_from_sha256=9dae01f4ae4b102346c0f8df281fe1eafef3b003b8ac67adfeef414b2f41f621 -/
namespace Paper.F6ILPSystem

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost
open Paper.AffineNat Paper.AffineILP Paper.AffineChain
open Paper.F6Cleared Paper.F6Objective Paper.PPEndToEnd

def keyProof (labels : List Paper.AffineNat.Label) :
    ∀ label ∈ labels, label.k ∈ usedArities labels := by
  intro label h
  exact mem_usedArities h

def contractionRoot (labels : List Paper.AffineNat.Label) (x : ℤ) :
    List (AffineExpr (usedArities labels)) :=
  contractionRows 1 (rootExpr labels x) labels (keyProof labels)

theorem contractionRoot_iff (labels : List Paper.AffineNat.Label)
    (x : ℤ) (a : Nat → Nat) :
    (contractionRoot labels x).Forall (fun row => 0 ≤ row.eval a) ↔
    ClearedContractions 1 x
      (labels.map (Paper.AffineNat.instantiate a)) := by
  simpa only [contractionRoot, rootExpr, startExpr_eval] using
    contractionRows_iff 1 (rootExpr labels x) labels (keyProof labels) a

def budgetRow (labels : List Paper.AffineNat.Label)
    (x z : ℤ) (c : Nat → Nat) (price : Nat → Nat) (N T : Nat) :
    AffineExpr (usedArities labels) :=
  let D := terminalProduct 1
    (labels.map (Paper.AffineNat.instantiate (fun _ => 0)))
  let leaf := leafPP price (finalN N labels) z.toNat
  subExpr
    (startExpr (usedArities labels) (D * ((T : ℤ) - leaf)))
    (clearedExpr D c N 1 (rootExpr labels x) labels (keyProof labels))

theorem budgetRow_iff (labels : List Paper.AffineNat.Label)
    (x z : ℤ) (c : Nat → Nat) (price : Nat → Nat) (N T : Nat)
    (a : Nat → Nat) :
    0 ≤ (budgetRow labels x z c price N T).eval a ↔
    clearedSum (terminalProduct 1
      (labels.map (Paper.AffineNat.instantiate a))) a c N 1 x labels ≤
      terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) *
        ((T : ℤ) - (leafPP price (finalN N labels) z.toNat : ℤ)) := by
  rw [budgetRow, eval_subExpr, startExpr_eval, clearedExpr_eval]
  simp only [rootExpr, startExpr_eval]
  rw [terminalProduct_independent 1 labels (fun _ => 0) a]
  omega

def evalInt {keys : Finset Nat} (e : AffineExpr keys)
    (values : { k : Nat // k ∈ keys } → ℤ) : ℤ :=
  e.intercept + ∑ key : { k : Nat // k ∈ keys }, e.coeff key * values key

theorem evalInt_ofNat {keys : Finset Nat} (e : AffineExpr keys)
    (a : Nat → Nat) :
    evalInt e (fun key => a key.val) = e.eval a := rfl

def liftNat (keys : Finset Nat) (values : { k : Nat // k ∈ keys } → ℤ)
    (k : Nat) : Nat :=
  if h : k ∈ keys then (values ⟨k, h⟩).toNat else 0

theorem liftNat_cast {keys : Finset Nat}
    (values : { k : Nat // k ∈ keys } → ℤ)
    (hpositive : ∀ key, 0 ≤ values key) (key : { k : Nat // k ∈ keys }) :
    (liftNat keys values key.val : ℤ) = values key := by
  simp [liftNat, key.property, Int.toNat_of_nonneg (hpositive key)]

theorem evalInt_eq_liftNat {keys : Finset Nat}
    (e : AffineExpr keys) (values : { k : Nat // k ∈ keys } → ℤ)
    (hpositive : ∀ key, 0 ≤ values key) :
    evalInt e values = e.eval (liftNat keys values) := by
  simp only [evalInt, AffineExpr.eval]
  congr 1
  apply Finset.sum_congr rfl
  intro key _
  rw [liftNat_cast values hpositive key]

end Paper.F6ILPSystem
/- END Finite.lean -/

/- BEGIN Concrete.lean transformed_from_sha256=84821ebb4c475d5feb753271f4e672f963248dd507596008ce4f0285d12fa255 -/
namespace Paper.F6ILPFeasible

open Paper.F6ILP Paper.F6ILPCost Paper.F6ILPSystem
open Paper.AffineNat Paper.AffineILP Paper.AffineChain
open Paper.F6Cleared Paper.F6Objective Paper.PPEndToEnd

def Feasible (labels : List Paper.AffineNat.Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat)
    (values : Variable labels → ℤ) : Prop :=
  evalInt (terminalRow labels x z) values = 0 ∧
  (contractionRoot labels x).Forall
    (fun row => 0 ≤ evalInt row values) ∧
  0 ≤ evalInt (budgetRow labels x z c price N T) values ∧
  ∀ key : Variable labels,
    (lo key.val : ℤ) ≤ values key ∧ values key ≤ (hi key.val : ℤ)

theorem feasible_nat_iff (labels : List Paper.AffineNat.Label)
    (x z : ℤ) (c lo hi : Nat → Nat) (price : Nat → Nat)
    (N T : Nat) (a : Nat → Nat) :
    Feasible labels x z c lo hi price N T (fun key => a key.val) ↔
    terminalWidth 1 x (labels.map (Paper.AffineNat.instantiate a)) =
      terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) * z ∧
    ClearedContractions 1 x
      (labels.map (Paper.AffineNat.instantiate a)) ∧
    clearedSum (terminalProduct 1
      (labels.map (Paper.AffineNat.instantiate a))) a c N 1 x labels ≤
      terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) *
        ((T : ℤ) - (leafPP price (finalN N labels) z.toNat : ℤ)) ∧
    (∀ key : Variable labels,
      (lo key.val : ℤ) ≤ (a key.val : ℤ) ∧
        (a key.val : ℤ) ≤ hi key.val) := by
  simp only [Feasible, evalInt_ofNat]
  rw [terminalRow_eval]
  have hterm :
      (terminalWidth 1 x (labels.map (Paper.AffineNat.instantiate a)) -
        terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) * z = 0) ↔
      terminalWidth 1 x (labels.map (Paper.AffineNat.instantiate a)) =
        terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) * z := by
    omega
  rw [hterm]
  rw [contractionRoot_iff, budgetRow_iff]

theorem feasible_sound_nat (labels : List Paper.AffineNat.Label)
    (x z : ℤ) (c lo hi : Nat → Nat) (price : Nat → Nat)
    (N T : Nat) (values : Variable labels → ℤ)
    (h : Feasible labels x z c lo hi price N T values) :
    let a := liftNat (usedArities labels) values
    terminalWidth 1 x (labels.map (Paper.AffineNat.instantiate a)) =
      terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) * z ∧
    ClearedContractions 1 x
      (labels.map (Paper.AffineNat.instantiate a)) ∧
    clearedSum (terminalProduct 1
      (labels.map (Paper.AffineNat.instantiate a))) a c N 1 x labels ≤
      terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) *
        ((T : ℤ) - (leafPP price (finalN N labels) z.toNat : ℤ)) ∧
    (∀ key : Variable labels,
      (lo key.val : ℤ) ≤ (a key.val : ℤ) ∧
        (a key.val : ℤ) ≤ hi key.val) := by
  have hpositive : ∀ key : Variable labels, 0 ≤ values key := by
    intro key
    have hlower := h.2.2.2 key
    exact le_trans (Int.natCast_nonneg _) hlower.1
  have hfn := (feasible_nat_iff labels x z c lo hi price N T
    (liftNat (usedArities labels) values)).1
  have heq : (fun key : Variable labels =>
      (liftNat (usedArities labels) values key.val : ℤ)) = values := by
    funext key
    exact liftNat_cast values hpositive key
  apply hfn
  simpa only [heq] using h

end Paper.F6ILPFeasible
/- END Concrete.lean -/

/- BEGIN Source.lean transformed_from_sha256=ef9ac1935aad590f0d4a872127adcfa5997b80ee66d0b9403d4aa34a1d08b1e2 -/
namespace Paper.F6ILPSound

open Paper.F6ILP Paper.F6ILPCost Paper.F6ILPSystem Paper.F6ILPFeasible
open Paper.AffineNat Paper.AffineILP Paper.AffineChain
open Paper.F6Cleared Paper.F6Objective Paper.F4ChargeIntervals

theorem feasible_shared_plateau {K : Nat}
    (labels : List Paper.AffineNat.Label) (x z : ℤ)
    (d c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat)
    (values : Variable labels → ℤ)
    (hfeasible : Feasible labels x z c lo hi price N T values)
    (hdecor : ∀ label ∈ labels,
      label.d = d label.k ∧ label.c = c label.k)
    (hlo : ∀ key : Variable labels,
      minCharge (K := K) key.val (d key.val) (lo key.val) =
        (c key.val : WithTop Nat))
    (hhi : ∀ key : Variable labels,
      minCharge (K := K) key.val (d key.val) (hi key.val) =
        (c key.val : WithTop Nat)) :
    let a := liftNat (usedArities labels) values
    ∀ label ∈ labels,
      label.d = d label.k ∧ label.c = c label.k ∧
      minCharge (K := K) label.k (d label.k) (a label.k) =
        (c label.k : WithTop Nat) := by
  let a := liftNat (usedArities labels) values
  have hnat := feasible_sound_nat labels x z c lo hi price N T values hfeasible
  dsimp
  intro label hmem
  let key : Variable labels := ⟨label.k, mem_usedArities hmem⟩
  have hbounds := hnat.2.2.2 key
  have hlow : lo label.k ≤ a label.k := by exact_mod_cast hbounds.1
  have hhigh : a label.k ≤ hi label.k := by exact_mod_cast hbounds.2
  obtain ⟨hd, hc⟩ := hdecor label hmem
  exact ⟨hd, hc, minCharge_level_interval hlow hhigh (hlo key) (hhi key)⟩

theorem feasible_to_actual_cost {K : Nat}
    (labels : List Paper.AffineNat.Label) (x z : ℤ)
    (d c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat)
    (values : Variable labels → ℤ) (hz : 1 ≤ z)
    (hfeasible : Feasible labels x z c lo hi price N T values)
    (hdecor : ∀ label ∈ labels,
      label.d = d label.k ∧ label.c = c label.k)
    (hlo : ∀ key : Variable labels,
      minCharge (K := K) key.val (d key.val) (lo key.val) =
        (c key.val : WithTop Nat))
    (hhi : ∀ key : Variable labels,
      minCharge (K := K) key.val (d key.val) (hi key.val) =
        (c key.val : WithTop Nat)) :
    ∃ (w : Nat) (ts : List (Paper.F2CatalogTransfer.F2Source K)) (v : Nat),
      x = w ∧ ts.length = labels.length ∧
      Coupled.Formal.CostL (Paper.F6CostBridge.rawProblem price) ts w N v ∧
      v ≤ T := by
  let a := liftNat (usedArities labels) values
  have hnat := feasible_sound_nat labels x z c lo hi price N T values hfeasible
  have hshared := feasible_shared_plateau (K := K)
    labels x z d c lo hi price N T values hfeasible hdecor hlo hhi
  obtain ⟨w, ts, v, hx, hlen, hcost, hiff⟩ :=
    fixed_constraints_budget a d c labels 1 x z (by decide) hz
      hshared hnat.1 hnat.2.1 price N T
  exact ⟨w, ts, v, by simpa using hx, hlen, hcost, hiff.mpr hnat.2.2.1⟩

theorem canonical_to_feasible (labels : List Paper.AffineNat.Label)
    (x z : ℤ) (a c lo hi : Nat → Nat) (price : Nat → Nat)
    (N T : Nat)
    (hterminal : terminalWidth 1 x
      (labels.map (Paper.AffineNat.instantiate a)) =
      terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) * z)
    (hcontract : ClearedContractions 1 x
      (labels.map (Paper.AffineNat.instantiate a)))
    (hbudget : clearedSum (terminalProduct 1
      (labels.map (Paper.AffineNat.instantiate a))) a c N 1 x labels ≤
      terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) *
        ((T : ℤ) -
          (Paper.PPEndToEnd.leafPP price (finalN N labels) z.toNat : ℤ)))
    (hinterval : ∀ key : Variable labels,
      lo key.val ≤ a key.val ∧ a key.val ≤ hi key.val) :
    Feasible labels x z c lo hi price N T (fun key => a key.val) := by
  apply (feasible_nat_iff labels x z c lo hi price N T a).2
  refine ⟨hterminal, hcontract, hbudget, ?_⟩
  intro key
  obtain ⟨hl, hu⟩ := hinterval key
  constructor <;> exact_mod_cast (by assumption)

end Paper.F6ILPSound
/- END Source.lean -/
