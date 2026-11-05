import Foundations.Counting.WeightedWords
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Typed budget words

Generalizes the weighted budget words to an arbitrary typed alphabet with branch counts `q`. Defines `typedBudgetWords` and `typedWeightSum`, and proves the enumeration sound (`typedBudgetWords_sound`) and complete (`typedBudgetWords_complete`) with respect to the product budget.
-/

namespace Paper.CountStage.TypedDecorationWords

open Paper.CountStage.DecorationWords

def qProduct {α : Type} (q : α → Nat) (xs : List α) : Nat := (xs.map q).prod

def typedBudgetWords {α : Type} (A : List α) (q : α → Nat)
    (hq : ∀ a, 3 ≤ q a) : Nat → List (List α)
  | 0 => []
  | U + 1 => [[]] ++ A.flatMap (fun a =>
      (typedBudgetWords A q hq ((U + 1) / q a)).map (a :: ·))
termination_by U => U
decreasing_by
  simp_wf
  exact Nat.div_lt_self (by omega) (by have := hq a; omega)

def typedWeightSum {α : Type} (A : List α) (q : α → Nat) : ℚ :=
  (A.map fun a => (1 : ℚ) / (q a : ℚ) ^ 10).sum

lemma typedProduct_ge_one {α : Type} (q : α → Nat) (hq : ∀ a, 3 ≤ q a) :
    ∀ xs : List α, 1 ≤ qProduct q xs := by
  intro xs
  induction xs with
  | nil => simp [qProduct]
  | cons a xs ih =>
      have hq1 : 1 ≤ q a := by have := hq a; omega
      change 1 ≤ q a * qProduct q xs
      simpa using Nat.mul_le_mul hq1 ih

theorem typedBudgetWords_sound {α : Type} (A : List α) (q : α → Nat)
    (hq : ∀ a, 3 ≤ q a) : ∀ U w,
      w ∈ typedBudgetWords A q hq U →
        qProduct q w ≤ U ∧ ∀ x ∈ w, x ∈ A := by
  intro U
  induction U using Nat.strong_induction_on with
  | h U ih =>
      intro w hw
      cases U with
      | zero => simp [typedBudgetWords] at hw
      | succ U =>
          simp only [typedBudgetWords, List.mem_append, List.mem_singleton,
            List.mem_flatMap, List.mem_map] at hw
          rcases hw with hempty | ⟨a, ha, tail, htail, rfl⟩
          · subst w
            simp [qProduct]
          · have hlt : (U + 1) / q a < U + 1 :=
              Nat.div_lt_self (by omega) (by have := hq a; omega)
            have htailSound := ih ((U + 1) / q a) hlt tail htail
            have hprod : qProduct q tail * q a ≤ U + 1 :=
              (Nat.le_div_iff_mul_le (by have := hq a; omega)).mp htailSound.1
            constructor
            · simpa [qProduct, Nat.mul_comm] using hprod
            · intro x hx
              rcases List.mem_cons.mp hx with hx | hx
              · subst x; exact ha
              · exact htailSound.2 x hx

theorem typedBudgetWords_complete {α : Type} (A : List α) (q : α → Nat)
    (hq : ∀ a, 3 ≤ q a) : ∀ U w,
      (∀ x ∈ w, x ∈ A) → qProduct q w ≤ U → w ∈ typedBudgetWords A q hq U := by
  intro U
  induction U using Nat.strong_induction_on with
  | h U ih =>
      intro w hmem hprod
      cases U with
      | zero =>
          have hpos := typedProduct_ge_one q hq w
          have hz : qProduct q w = 0 := Nat.eq_zero_of_le_zero hprod
          rw [hz] at hpos
          omega
      | succ U =>
          cases w with
          | nil => simp [typedBudgetWords]
          | cons a xs =>
              have hamem : a ∈ A := hmem a (by simp)
              have htailMem : ∀ y ∈ xs, y ∈ A := by
                intro y hy
                exact hmem y (by simp [hy])
              have hprod' : q a * qProduct q xs ≤ U + 1 := by
                simpa [qProduct] using hprod
              have htailprod : qProduct q xs ≤ (U + 1) / q a := by
                apply (Nat.le_div_iff_mul_le (by have := hq a; omega)).2
                simpa [Nat.mul_comm] using hprod'
              have hlt : (U + 1) / q a < U + 1 :=
                Nat.div_lt_self (by omega) (by have := hq a; omega)
              have htail : xs ∈ typedBudgetWords A q hq ((U + 1) / q a) :=
                ih ((U + 1) / q a) hlt xs htailMem htailprod
              have hbranch : a :: xs ∈ A.flatMap (fun b =>
                  (typedBudgetWords A q hq ((U + 1) / q b)).map (b :: ·)) := by
                rw [List.mem_flatMap]
                refine ⟨a, hamem, ?_⟩
                rw [List.mem_map]
                exact ⟨xs, htail, rfl⟩
              have hall : a :: xs ∈ [[]] ++ A.flatMap (fun b =>
                  (typedBudgetWords A q hq ((U + 1) / q b)).map (b :: ·)) :=
                List.mem_append.mpr (Or.inr hbranch)
              simpa [typedBudgetWords] using hall

theorem typedBudgetWords_length_eq {α : Type} (A : List α) (q : α → Nat)
    (hq : ∀ a, 3 ≤ q a) : ∀ U,
      (typedBudgetWords A q hq U).length =
        (budgetWords (A.map fun a => ⟨q a, hq a⟩) U).length := by
  intro U
  induction U using Nat.strong_induction_on with
  | h U ih =>
      cases U with
      | zero => simp [typedBudgetWords, budgetWords]
      | succ U =>
          have hbranches : ∀ a ∈ A,
              (typedBudgetWords A q hq ((U + 1) / q a)).length =
                (budgetWords (A.map fun a => ⟨q a, hq a⟩) ((U + 1) / q a)).length := by
            intro a ha
            apply ih
            exact Nat.div_lt_self (by omega) (by have := hq a; omega)
          simp only [typedBudgetWords, budgetWords, List.length_append,
            List.length_singleton, List.length_flatMap, List.length_map]
          simp only [List.map_map]
          congr 1
          apply congrArg List.sum
          apply List.map_congr_left
          intro a ha
          exact hbranches a ha

theorem typedWords_count_lt_three_U10 {α : Type} (A : List α) (q : α → Nat)
    (hq : ∀ a, 3 ≤ q a) (hweight : typedWeightSum A q ≤ 14 / 27)
    {U : Nat} (hU : 1 ≤ U) :
      ((typedBudgetWords A q hq U).length : ℚ) < 3 * (U : ℚ) ^ 10 := by
  have hsum : weightSum (A.map fun a => ⟨q a, hq a⟩) ≤ 14 / 27 := by
    calc
      weightSum (A.map fun a => ⟨q a, hq a⟩) = typedWeightSum A q := by
        unfold weightSum
        rw [List.map_map]
        change ((A.map fun a => Paper.CountStage.DecorationWords.weight
            (⟨q a, hq a⟩ : BranchLabel)).sum) =
          ((A.map fun a => (1 : ℚ) / (q a : ℚ) ^ 10).sum)
        simp [Paper.CountStage.DecorationWords.weight]
      _ ≤ 14 / 27 := hweight
  rw [typedBudgetWords_length_eq A q hq U]
  exact budgetWords_length_lt_three_pow hsum hU


abbrev ArityIndex := {k : Nat // 2 ≤ k}

structure DecoratedLabel where
  arity : ArityIndex
  row : Nat
  col : Nat
  charge : Nat
  deriving DecidableEq

def labelQ (x : DecoratedLabel) : Nat := 2 * x.arity.val - 1

def branchOfLabel (x : DecoratedLabel) : BranchLabel :=
  ⟨labelQ x, by have hk := x.arity.property; unfold labelQ; omega⟩

def labelsAt (k : ArityIndex) : List DecoratedLabel :=
  (List.range k.val).flatMap fun r =>
    (List.range k.val).flatMap fun d =>
      (List.range (27 * k.val ^ 3 + 1)).map fun c =>
        ⟨k, r, d, c⟩

def decorationLabels (K : Nat) : List DecoratedLabel :=
  (List.range (K - 1)).flatMap fun i =>
    labelsAt ⟨i + 2, by omega⟩

lemma flatMap_constant_replicate {α β : Type} (xs : List α) (f : α → List β)
    (m : Nat) (b : β) (hf : ∀ x, f x = List.replicate m b) :
    xs.flatMap f = List.replicate (xs.length * m) b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.length_cons, hf x, ih]
      rw [← List.replicate_add]
      congr 1
      ring
lemma map_constant_replicate {α β : Type} (xs : List α) (f : α → β) (b : β)
    (hf : ∀ x ∈ xs, f x = b) : xs.map f = List.replicate xs.length b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : ∀ y ∈ xs, f y = b := by
        intro y hy
        exact hf y (by simp [hy])
      simp only [List.map_cons, List.length_cons]
      rw [hf x (by simp), ih htail]
      simp [List.replicate_succ]

lemma map_flatMap_constant_replicate {α β γ : Type} (xs : List α)
    (f : α → List β) (g : β → γ) (m : Nat) (b : γ)
    (hf : ∀ x, (f x).map g = List.replicate m b) :
    (xs.flatMap f).map g = List.replicate (xs.length * m) b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.map_append, List.length_cons, hf x, ih]
      rw [← List.replicate_add]
      congr 1
      ring

lemma flatMap_congr {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have htail : ∀ y ∈ xs, f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.flatMap_cons, h x (by simp), ih htail]

theorem labelsAt_branch_map (k : ArityIndex) :
    (labelsAt k).map branchOfLabel =
      List.replicate (Paper.CountStage.Decoration.B k.val)
        ⟨Paper.CountStage.Decoration.q k.val,
          Paper.CountStage.Decoration.q_ge_three k.property⟩ := by
  let b : BranchLabel := ⟨Paper.CountStage.Decoration.q k.val,
    Paper.CountStage.Decoration.q_ge_three k.property⟩
  have hc : ∀ r d,
      ((List.range (27 * k.val ^ 3 + 1)).map
        (fun c => branchOfLabel ⟨k, r, d, c⟩)) =
          List.replicate (27 * k.val ^ 3 + 1) b := by
    intro r d
    have h := map_constant_replicate (List.range (27 * k.val ^ 3 + 1))
      (fun c => branchOfLabel ⟨k, r, d, c⟩) b (by
        intro c hc
        simp [branchOfLabel, labelQ, b, Paper.CountStage.Decoration.q])
    simpa [List.length_range] using h
  have hd : ∀ r,
      ((List.range k.val).flatMap (fun d =>
        (List.range (27 * k.val ^ 3 + 1)).map
          (fun c => branchOfLabel ⟨k, r, d, c⟩))) =
          List.replicate (k.val * (27 * k.val ^ 3 + 1)) b := by
    intro r
    have h := flatMap_constant_replicate (List.range k.val)
      (fun d => (List.range (27 * k.val ^ 3 + 1)).map
        (fun c => branchOfLabel ⟨k, r, d, c⟩))
      (27 * k.val ^ 3 + 1) b (by intro d; exact hc r d)
    simpa [List.length_range] using h
  have hall : (labelsAt k).map branchOfLabel =
      List.replicate (k.val * (k.val * (27 * k.val ^ 3 + 1))) b := by
    unfold labelsAt
    have h := map_flatMap_constant_replicate (List.range k.val)
      (fun r => (List.range k.val).flatMap (fun d =>
        (List.range (27 * k.val ^ 3 + 1)).map
          (fun c => ⟨k, r, d, c⟩)))
      branchOfLabel (k.val * (27 * k.val ^ 3 + 1)) b (by
        intro r
        simpa only [List.map_flatMap, List.map_map] using hd r)
    simpa [List.length_range] using h
  have hcount : k.val * (k.val * (27 * k.val ^ 3 + 1)) =
      Paper.CountStage.Decoration.B k.val := by
    dsimp [Paper.CountStage.Decoration.B]
    ring
  rw [hcount] at hall
  simpa [b] using hall

theorem labelsAt_length (k : ArityIndex) :
    (labelsAt k).length = Paper.CountStage.Decoration.B k.val := by
  have h := congrArg List.length (labelsAt_branch_map k)
  simpa [List.length_replicate] using h

theorem decorationLabels_branch_map (K : Nat) :
    (decorationLabels K).map branchOfLabel =
      Paper.CountStage.DecorationWords.decorationAlphabet K := by
  unfold decorationLabels Paper.CountStage.DecorationWords.decorationAlphabet
  rw [List.map_flatMap]
  apply flatMap_congr
  intro i hi
  exact labelsAt_branch_map ⟨i + 2, by omega⟩

theorem typedWeightSum_decorationLabels_le (K : Nat) :
    typedWeightSum (decorationLabels K) labelQ ≤ 14 / 27 := by
  have hweight : typedWeightSum (decorationLabels K) labelQ =
      weightSum ((decorationLabels K).map branchOfLabel) := by
    unfold typedWeightSum weightSum
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x hx
    simp [branchOfLabel, labelQ, weight]
  rw [hweight, decorationLabels_branch_map]
  exact Paper.CountStage.DecorationWords.decorationAlphabet_weight_le K

theorem actualDecorationWords_count_lt_three_U10 (K U : Nat) (hU : 1 ≤ U) :
    ((typedBudgetWords (decorationLabels K) labelQ
      (fun x => by have hk := x.arity.property; unfold labelQ; omega) U).length : ℚ)
      < 3 * (U : ℚ) ^ 10 := by
  exact typedWords_count_lt_three_U10 (decorationLabels K) labelQ
    (fun x => by have hk := x.arity.property; unfold labelQ; omega)
    (typedWeightSum_decorationLabels_le K) hU

theorem actualDecorationWords_complete (K U : Nat) (w : List DecoratedLabel)
    (hlabels : ∀ x ∈ w, x ∈ decorationLabels K)
    (hbudget : qProduct labelQ w ≤ U) :
      w ∈ typedBudgetWords (decorationLabels K) labelQ
        (fun x => by have hk := x.arity.property; unfold labelQ; omega) U := by
  exact typedBudgetWords_complete (decorationLabels K) labelQ
    (fun x => by have hk := x.arity.property; unfold labelQ; omega)
    U w hlabels hbudget

theorem labelsAt_member_bounds (k : ArityIndex) {x : DecoratedLabel}
    (hx : x ∈ labelsAt k) : x.arity = k ∧ x.row < k.val ∧
      x.col < k.val ∧ x.charge ≤ 27 * k.val ^ 3 := by
  unfold labelsAt at hx
  rcases List.mem_flatMap.mp hx with ⟨r, hr, hx⟩
  rcases List.mem_flatMap.mp hx with ⟨d, hd, hx⟩
  rcases List.mem_map.mp hx with ⟨c, hc, heq⟩
  cases heq
  simp only [List.mem_range] at hr hd hc
  have hc' : c ≤ 27 * k.val ^ 3 := by
    exact Nat.le_of_lt_succ (by simpa [Nat.add_comm] using hc)
  exact ⟨rfl, hr, hd, hc'⟩

theorem decorationLabels_member_bounds (K : Nat) {x : DecoratedLabel}
    (hx : x ∈ decorationLabels K) :
      2 ≤ x.arity.val ∧ x.arity.val ≤ K ∧ x.row < x.arity.val ∧
        x.col < x.arity.val ∧ x.charge ≤ 27 * x.arity.val ^ 3 := by
  unfold decorationLabels at hx
  rcases List.mem_flatMap.mp hx with ⟨i, hi, hx⟩
  have hi' : i < K - 1 := by simpa using hi
  have hk : i + 2 ≤ K := by omega
  have hlabel := labelsAt_member_bounds ⟨i + 2, by omega⟩ hx
  rcases hlabel with ⟨ha, hr, hc, hcharge⟩
  have haval : x.arity.val = i + 2 := congrArg Subtype.val ha
  rw [haval]
  exact ⟨by omega, hk, by simpa using hr, by simpa using hc, by simpa using hcharge⟩

def labelCompatible (x y : DecoratedLabel) : Prop :=
  x.arity ≠ y.arity ∨
    (x.row = y.row ∧ x.col = y.col ∧ x.charge = y.charge)

instance : DecidableRel labelCompatible := by
  intro x y
  unfold labelCompatible
  infer_instance

def repeatedArityConsistent (w : List DecoratedLabel) : Bool :=
  decide (List.Pairwise labelCompatible w)

def consistentBudgetWords (K U : Nat) : List (List DecoratedLabel) :=
  (typedBudgetWords (decorationLabels K) labelQ
    (fun x => by have hk := x.arity.property; unfold labelQ; omega) U).filter
      repeatedArityConsistent

theorem consistentWords_count_le_candidates (K U : Nat) :
    (consistentBudgetWords K U).length ≤
      (typedBudgetWords (decorationLabels K) labelQ
        (fun x => by have hk := x.arity.property; unfold labelQ; omega) U).length := by
  exact List.length_filter_le _ _

end Paper.CountStage.TypedDecorationWords
