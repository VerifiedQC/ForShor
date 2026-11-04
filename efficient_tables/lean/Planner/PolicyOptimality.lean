import Model.Defs

/-!
# Optimality for shared-table policies

Concerns selecting a shared-table trace from a finite catalog. Proves membership characterizations of the enumerated traces (`finiteTraces_mem_iff`, `scoredTraces_mem_iff`), that the selected trace is valid (`selected_valid`) and no more costly than any valid shared trace (`selected_le_all_shared`), and `selector_eq_any_optimal`.
-/

namespace Paper.PolicyOptimality

open Coupled.Formal

variable {ι : Type}

theorem traceCost?_iff (P : Prob ι) (l : List ι) (w N v : Nat) :
    traceCost? P l w N = some v ↔ CostL P l w N v := by
  induction l generalizing w N v with
  | nil =>
      simp only [traceCost?]
      constructor
      · intro h
        cases h
        exact CostL.base w N
      · intro h
        cases h
        rfl
  | cons c rest ih =>
      constructor
      · intro h
        simp only [traceCost?] at h
        split at h
        · rename_i hcontract
          obtain ⟨childCost, hchild, heq⟩ := Option.map_eq_some_iff.mp h
          cases heq
          exact CostL.step c rest w N childCost hcontract ((ih _ _ _).mp hchild)
        · contradiction
      · intro h
        cases h with
        | step _ _ _ _ childCost hcontract hchild =>
            simp only [traceCost?, hcontract, ↓reduceIte]
            exact congrArg (Option.map (fun v => N * P.own c w (P.child c w) + v))
              ((ih _ _ _).mpr hchild)

theorem costL_length_le_width (P : Prob ι) {l : List ι} {w N v : Nat}
    (h : CostL P l w N v) : l.length ≤ w := by
  induction h with
  | base w N => simp
  | step c l w N v hcontract hchild ih =>
      simp only [List.length_cons]
      omega

theorem listsOfLength_mem_iff (catalog : List ι) (n : Nat) (l : List ι) :
    l ∈ listsOfLength n catalog ↔ l.length = n ∧ ∀ c ∈ l, c ∈ catalog := by
  induction n generalizing l with
  | zero =>
      cases l <;> simp [listsOfLength]
  | succ n ih =>
      constructor
      · intro h
        simp only [listsOfLength, List.mem_flatMap, List.mem_map] at h
        obtain ⟨c, hc, tail, htail, rfl⟩ := h
        obtain ⟨hlen, hmem⟩ := (ih tail).mp htail
        refine ⟨by simp [hlen], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hc
        · exact hmem x hx
      · rintro ⟨hlen, hmem⟩
        cases l with
        | nil => simp at hlen
        | cons c tail =>
            simp only [List.length_cons, Nat.succ.injEq] at hlen
            apply List.mem_flatMap.mpr
            refine ⟨c, hmem c List.mem_cons_self, ?_⟩
            apply List.mem_map.mpr
            refine ⟨tail, ?_, rfl⟩
            apply (ih tail).mpr
            exact ⟨hlen, fun x hx => hmem x (List.mem_cons_of_mem _ hx)⟩

theorem cappedCatalog_mem_iff (catalog : List ι) (arity : ι → Nat)
    (K : Nat) (c : ι) :
    c ∈ cappedCatalog catalog arity K ↔
      c ∈ catalog ∧ 2 ≤ arity c ∧ arity c ≤ K := by
  simp [cappedCatalog]

theorem finiteTraces_mem_iff (catalog : List ι) (arity : ι → Nat)
    (K width : Nat) (l : List ι) :
    l ∈ finiteTraces catalog arity K width ↔
      l.length ≤ width ∧
        ∀ c ∈ l, c ∈ catalog ∧ 2 ≤ arity c ∧ arity c ≤ K := by
  simp only [finiteTraces, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨n, hn, hm⟩
    obtain ⟨hlen, hmem⟩ := (listsOfLength_mem_iff _ _ _).mp hm
    exact ⟨by omega, fun c hc => (cappedCatalog_mem_iff _ _ _ _).mp (hmem c hc)⟩
  · rintro ⟨hlen, hmem⟩
    refine ⟨l.length, by omega, ?_⟩
    apply (listsOfLength_mem_iff _ _ _).mpr
    exact ⟨rfl, fun c hc => (cappedCatalog_mem_iff _ _ _ _).mpr (hmem c hc)⟩

theorem sharedB_eq_true_iff [DecidableEq ι] (arity : ι → Nat) (l : List ι) :
    sharedB arity l = true ↔ ArityInj arity l := by
  simp only [sharedB, List.all_eq_true]
  constructor
  · intro h c hc d hd heq
    have hcd : arity c ≠ arity d ∨ c = d := by
      simpa using h c hc d hd
    rcases hcd with hneq | hsame
    · exact False.elim (hneq heq)
    · exact hsame
  · intro h c hc d hd
    apply decide_eq_true
    by_cases heq : arity c = arity d
    · exact Or.inr (h c hc d hd heq)
    · exact Or.inl heq

theorem scoredTraces_mem_iff [DecidableEq ι] (P : Prob ι)
    (catalog : List ι) (arity : ι → Nat) (K w N : Nat)
    (l : List ι) (v : Nat) :
    (l, v) ∈ scoredTraces P catalog arity K w N ↔
      l.length ≤ w ∧
      (∀ c ∈ l, c ∈ catalog ∧ 2 ≤ arity c ∧ arity c ≤ K) ∧
      ArityInj arity l ∧ CostL P l w N v := by
  simp only [scoredTraces, List.mem_filterMap]
  constructor
  · rintro ⟨l', hl', hscore⟩
    by_cases hs : sharedB arity l' = true
    · simp only [hs, ↓reduceIte] at hscore
      cases hc : traceCost? P l' w N with
      | none => simp [hc] at hscore
      | some v' =>
          simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hscore
          obtain ⟨rfl, rfl⟩ := hscore
          obtain ⟨hlen, hmem⟩ := (finiteTraces_mem_iff _ _ _ _ _).mp hl'
          exact ⟨hlen, hmem, (sharedB_eq_true_iff _ _).mp hs,
            (traceCost?_iff _ _ _ _ _).mp hc⟩
    · simp only [Bool.not_eq_true] at hs
      simp [hs] at hscore
  · rintro ⟨hlen, hmem, hshared, hcost⟩
    refine ⟨l, (finiteTraces_mem_iff _ _ _ _ _).mpr ⟨hlen, hmem⟩, ?_⟩
    rw [(sharedB_eq_true_iff _ _).mpr hshared,
        (traceCost?_iff _ _ _ _ _).mpr hcost]
    rfl

theorem lowerCost_eq_left_or_right (a b : List ι × Nat) :
    lowerCost a b = a ∨ lowerCost a b = b := by
  by_cases h : b.2 < a.2
  · exact Or.inr (by simp [lowerCost, h])
  · exact Or.inl (by simp [lowerCost, h])

theorem lowerCost_le_left (a b : List ι × Nat) :
    (lowerCost a b).2 ≤ a.2 := by
  by_cases h : b.2 < a.2
  · simp [lowerCost, h, Nat.le_of_lt h]
  · simp [lowerCost, h]

theorem lowerCost_le_right (a b : List ι × Nat) :
    (lowerCost a b).2 ≤ b.2 := by
  by_cases h : b.2 < a.2
  · simp [lowerCost, h]
  · simp [lowerCost, h, Nat.le_of_not_gt h]

theorem fold_lowerCost_mem_or_initial (xs : List (List ι × Nat))
    (initial : List ι × Nat) :
    xs.foldl lowerCost initial = initial ∨
      xs.foldl lowerCost initial ∈ xs := by
  induction xs generalizing initial with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases ih (lowerCost initial x) with h | h
      · rcases lowerCost_eq_left_or_right initial x with hl | hr
        · exact Or.inl (by rw [h, hl])
        · exact Or.inr (by rw [h, hr]; exact List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem fold_lowerCost_le_initial (xs : List (List ι × Nat))
    (initial : List ι × Nat) :
    (xs.foldl lowerCost initial).2 ≤ initial.2 := by
  induction xs generalizing initial with
  | nil => exact le_rfl
  | cons x xs ih =>
      simpa only [List.foldl_cons] using
        le_trans (ih (lowerCost initial x)) (lowerCost_le_left initial x)

theorem fold_lowerCost_le_mem (xs : List (List ι × Nat))
    (initial item : List ι × Nat) (hmem : item ∈ xs) :
    (xs.foldl lowerCost initial).2 ≤ item.2 := by
  induction xs generalizing initial with
  | nil => simp at hmem
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact le_trans (fold_lowerCost_le_initial xs (lowerCost initial item))
          (lowerCost_le_right initial item)
      · exact ih (lowerCost initial x) htail

theorem selected_valid [DecidableEq ι] (P : Prob ι) (catalog : List ι)
    (arity : ι → Nat) (K w N : Nat) :
    (chosenTrace P catalog arity K w N).length ≤ w ∧
      (∀ c ∈ chosenTrace P catalog arity K w N,
        c ∈ catalog ∧ 2 ≤ arity c ∧ arity c ≤ K) ∧
      ArityInj arity (chosenTrace P catalog arity K w N) ∧
      CostL P (chosenTrace P catalog arity K w N) w N
        (chosenCost P catalog arity K w N) := by
  unfold chosenTrace chosenCost select
  rcases fold_lowerCost_mem_or_initial
      (scoredTraces P catalog arity K w N) ([], P.leaf N w) with h | h
  · rw [h]
    exact ⟨by simp, by simp, by simp [ArityInj], CostL.base w N⟩
  · exact (scoredTraces_mem_iff P catalog arity K w N _ _).mp h

theorem selected_le_all_shared [DecidableEq ι] (P : Prob ι)
    (catalog : List ι) (arity : ι → Nat) (K w N : Nat)
    (l : List ι) (v : Nat)
    (hcatalog : ∀ c ∈ l, c ∈ catalog ∧ 2 ≤ arity c ∧ arity c ≤ K)
    (hshared : ArityInj arity l) (hcost : CostL P l w N v) :
    chosenCost P catalog arity K w N ≤ v := by
  have hmem : (l, v) ∈ scoredTraces P catalog arity K w N :=
    (scoredTraces_mem_iff P catalog arity K w N l v).mpr
      ⟨costL_length_le_width P hcost, hcatalog, hshared, hcost⟩
  unfold chosenCost select
  exact fold_lowerCost_le_mem _ _ _ hmem

theorem selector_eq_any_optimal [DecidableEq ι] (P : Prob ι)
    (catalog : List ι) (arity : ι → Nat) (K w N v : Nat)
    (hexists : ∃ l, (∀ c ∈ l, c ∈ catalog ∧ 2 ≤ arity c ∧ arity c ≤ K) ∧
      ArityInj arity l ∧ CostL P l w N v)
    (hlower : ∀ l v', (∀ c ∈ l, c ∈ catalog ∧ 2 ≤ arity c ∧ arity c ≤ K) →
      ArityInj arity l → CostL P l w N v' → v ≤ v') :
    chosenCost P catalog arity K w N = v := by
  obtain ⟨l, hcatalog, hshared, hcost⟩ := hexists
  apply Nat.le_antisymm
  · exact selected_le_all_shared P catalog arity K w N l v hcatalog hshared hcost
  · obtain ⟨_, hc, hs, hv⟩ := selected_valid P catalog arity K w N
    exact hlower _ _ hc hs hv

theorem findArity?_hit [DecidableEq ι] (arity : ι → Nat) (l : List ι)
    (c : ι) (hshared : ArityInj arity l) (hc : c ∈ l) :
    l.find? (fun d => arity d == arity c) = some c := by
  induction l with
  | nil => simp at hc
  | cons d rest ih =>
      by_cases heq : arity d = arity c
      · have hdc : d = c := hshared d List.mem_cons_self c hc heq
        subst d
        simp [List.find?]
      · have htail : c ∈ rest := by
          rcases List.mem_cons.mp hc with h | h
          · exact False.elim (heq (h ▸ rfl))
          · exact h
        have hrest : ArityInj arity rest := by
          intro a ha b hb hab
          exact hshared a (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb) hab
        have hb : (arity d == arity c) = false := by
          cases h : (arity d == arity c) with
          | false => rfl
          | true => exact False.elim (heq (beq_iff_eq.mp h))
        simp [List.find?, hb, ih hrest htail]

theorem chosenAtArity_hit [DecidableEq ι] (P : Prob ι)
    (catalog : List ι) (arity : ι → Nat) (K w N : Nat)
    (c : ι) (hc : c ∈ chosenTrace P catalog arity K w N) :
    chosenAtArity P catalog arity K w N (arity c) = some c := by
  unfold chosenAtArity
  exact findArity?_hit arity _ c (selected_valid P catalog arity K w N).2.2.1 hc

theorem chosenTable_contains [DecidableEq ι] (P : Prob ι)
    (catalog : List ι) (arity : ι → Nat) (K w N : Nat)
    (c : ι) (hc : c ∈ chosenTrace P catalog arity K w N) :
    (arity c, c) ∈ chosenTable P catalog arity K w N := by
  have hcap : arity c ≤ K :=
    ((selected_valid P catalog arity K w N).2.1 c hc).2.2
  unfold chosenTable
  apply List.mem_filterMap.mpr
  refine ⟨arity c, by simp [hcap], ?_⟩
  rw [chosenAtArity_hit P catalog arity K w N c hc]
  rfl

end Paper.PolicyOptimality
