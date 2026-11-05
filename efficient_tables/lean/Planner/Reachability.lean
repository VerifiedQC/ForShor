import Planner.RecursiveLocal
import Mathlib.Data.Finset.Card

/-!
# Reachable widths of the recursive planner

Analyzes the queue-based enumeration of widths reachable from a set of roots. Proves the worklist step keeps the list duplicate-free and bounded (`step_nodup`, `step_bounded`), that it covers the reachable widths (`step_coverage`), and the final facts `reachableWidths_nodup`, `reachableWidths_root_mem` and `reachableWidths_child_mem`.
-/

namespace Paper.PlannerReachability

open TableGeneration.RecursiveCost

theorem eraseDups_mem (xs : List Nat) (x : Nat) :
    x ∈ xs.eraseDups ↔ x ∈ xs := by
  suffices ∀ n (ys : List Nat), ys.length ≤ n → (x ∈ ys.eraseDups ↔ x ∈ ys) from
    this xs.length xs (by rfl)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ys hlen
    cases ys with
    | nil => simp
    | cons a as =>
      rw [List.eraseDups_cons]
      have hsmall : (as.filter fun b => !b == a).length < n := by
        have hf := List.length_filter_le (fun b => !b == a) as
        simp only [List.length_cons] at hlen
        omega
      simp only [List.mem_cons, ih _ hsmall _ (le_refl _), List.mem_filter]
      constructor
      · rintro (rfl | ⟨hx, _⟩)
        · exact Or.inl rfl
        · exact Or.inr hx
      · rintro (rfl | hx)
        · exact Or.inl rfl
        · by_cases h : x = a
          · exact Or.inl h
          · exact Or.inr ⟨hx, by simp [h]⟩

theorem eraseDups_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  suffices ∀ n (ys : List Nat), ys.length ≤ n → ys.eraseDups.Nodup from
    this xs.length xs (by rfl)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ys hlen
    cases ys with
    | nil => simp
    | cons a as =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      have hsmall : (as.filter fun b => !b == a).length < n := by
        have hf := List.length_filter_le (fun b => !b == a) as
        simp only [List.length_cons] at hlen
        omega
      constructor
      · intro h
        have h' := (eraseDups_mem (as.filter fun b => !b == a) a).mp h
        simp at h'
      · exact ih _ hsmall _ (le_refl _)

theorem enqueue_cons (c : Candidate) (cs : List Candidate) (width : Nat)
    (seen pending : List Nat) :
    enqueueContractingChildren (c :: cs) width seen pending =
      enqueueContractingChildren cs width seen
        (if (c.analyze width).childWidth < width &&
            !seen.contains (c.analyze width).childWidth &&
            !pending.contains (c.analyze width).childWidth then
          (c.analyze width).childWidth :: pending else pending) := rfl

theorem pending_mem_enqueue (cs : List Candidate) (width : Nat)
    (seen pending : List Nat) (x : Nat) (hx : x ∈ pending) :
    x ∈ enqueueContractingChildren cs width seen pending := by
  induction cs generalizing pending with
  | nil => simpa [enqueueContractingChildren] using hx
  | cons c cs ih =>
    rw [enqueue_cons]
    split_ifs
    · exact ih _ (List.mem_cons_of_mem _ hx)
    · exact ih _ hx

theorem enqueue_new_bounded (cs : List Candidate) (width M : Nat)
    (seen pending : List Nat) (hwidth : width ≤ M)
    (hpending : ∀ x ∈ pending, x ≤ M) :
    ∀ x ∈ enqueueContractingChildren cs width seen pending, x ≤ M := by
  induction cs generalizing pending with
  | nil => simpa [enqueueContractingChildren] using hpending
  | cons c cs ih =>
    rw [enqueue_cons]
    split_ifs with hg
    · apply ih
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have hchild : (c.analyze width).childWidth < width := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
          exact hg.1.1
        omega
      · exact hpending x hx
    · exact ih _ hpending

theorem enqueue_preserves_nodup (cs : List Candidate) (width : Nat)
    (seen pending : List Nat) (h : (seen ++ pending).Nodup) :
    (seen ++ enqueueContractingChildren cs width seen pending).Nodup := by
  induction cs generalizing pending with
  | nil => simpa [enqueueContractingChildren] using h
  | cons c cs ih =>
    rw [enqueue_cons]
    split_ifs with hg
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hg
      have hns : (c.analyze width).childWidth ∉ seen := by
        intro hm
        have ht := List.contains_iff_mem.mpr hm
        rw [hg.1.2] at ht
        cases ht
      have hnp : (c.analyze width).childWidth ∉ pending := by
        intro hm
        have ht := List.contains_iff_mem.mpr hm
        rw [hg.2] at ht
        cases ht
      have hs := (List.nodup_append.mp h).1
      have hp := (List.nodup_append.mp h).2.1
      have hd := (List.nodup_append.mp h).2.2
      apply ih
      apply List.nodup_append.mpr
      refine ⟨hs, List.nodup_cons.mpr ⟨hnp, hp⟩, ?_⟩
      intro a ha b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact fun heq => hns (heq ▸ ha)
      · exact hd a ha b hb
    · exact ih _ h

theorem enqueue_excludes_width (cs : List Candidate) (width : Nat)
    (seen pending : List Nat) (h : width ∉ pending) :
    width ∉ enqueueContractingChildren cs width seen pending := by
  induction cs generalizing pending with
  | nil => simpa [enqueueContractingChildren] using h
  | cons c cs ih =>
    rw [enqueue_cons]
    split_ifs with hg
    · apply ih
      simp only [List.mem_cons, not_or]
      constructor
      · have hlt : (c.analyze width).childWidth < width := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
          exact hg.1.1
        omega
      · exact h
    · exact ih _ h

theorem enqueue_child_or_seen (cs : List Candidate) (width : Nat)
    (seen pending : List Nat) (c : Candidate) (hc : c ∈ cs)
    (hcontract : (c.analyze width).childWidth < width) :
    (c.analyze width).childWidth ∈ seen ∨
      (c.analyze width).childWidth ∈
        enqueueContractingChildren cs width seen pending := by
  induction cs generalizing pending with
  | nil => simp at hc
  | cons head tail ih =>
    rw [enqueue_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · by_cases hs : (c.analyze width).childWidth ∈ seen
      · exact Or.inl hs
      · right
        by_cases hp : (c.analyze width).childWidth ∈ pending
        · have hm := pending_mem_enqueue tail width seen pending _ hp
          simpa [hcontract, hs, hp] using hm
        · have hm := pending_mem_enqueue tail width seen
            ((c.analyze width).childWidth :: pending)
            (c.analyze width).childWidth (by simp)
          simpa [hcontract, hs, hp] using hm
    · split_ifs
      · exact ih _ hc
      · exact ih _ hc

theorem nodup_length_bounded (xs : List Nat) (M : Nat)
    (hn : xs.Nodup) (hb : ∀ x ∈ xs, x ≤ M) : xs.length ≤ M + 1 := by
  have hsub : xs.toFinset ⊆ Finset.range (M + 1) := by
    intro x hx
    have hmem : x ∈ xs := by simpa using hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hb x hmem))
  have hc := Finset.card_le_card hsub
  simpa [List.toFinset_card_of_nodup hn] using hc

theorem step_nodup (cs : List Candidate) (width : Nat)
    (seen pending : List Nat)
    (h : (seen ++ width :: pending).Nodup) :
    ((width :: seen) ++ enqueueContractingChildren cs width seen pending).Nodup := by
  have hse : (seen ++ pending).Nodup := by
    have h0 := List.nodup_append.mp h
    apply List.nodup_append.mpr
    refine ⟨h0.1, (List.nodup_cons.mp h0.2.1).2, ?_⟩
    intro a ha b hb
    exact h0.2.2 a ha b (List.mem_cons_of_mem _ hb)
  have hwseen : width ∉ seen := by
    intro hw
    have h0 := (List.nodup_append.mp h).2.2 width hw width (by simp)
    exact h0 rfl
  have hwpending : width ∉ pending := (List.nodup_cons.mp (List.nodup_append.mp h).2.1).1
  have hwenqueue := enqueue_excludes_width cs width seen pending hwpending
  change (width :: (seen ++ enqueueContractingChildren cs width seen pending)).Nodup
  apply List.nodup_cons.mpr
  constructor
  · simp [hwseen, hwenqueue]
  · exact enqueue_preserves_nodup cs width seen pending hse

theorem step_bounded (cs : List Candidate) (width M : Nat)
    (seen pending : List Nat)
    (h : ∀ x ∈ seen ++ width :: pending, x ≤ M) :
    ∀ x ∈ (width :: seen) ++ enqueueContractingChildren cs width seen pending,
      x ≤ M := by
  have hw : width ≤ M := h width (by simp)
  have hs : ∀ x ∈ seen, x ≤ M := by
    intro x hx
    exact h x (by simp [hx])
  have hp : ∀ x ∈ pending, x ≤ M := by
    intro x hx
    exact h x (by simp [hx])
  have he := enqueue_new_bounded cs width M seen pending hw hp
  intro x hx
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | hx
  · exact hw
  · rcases hx with hx | hx
    · exact hs x hx
    · exact he x hx

theorem step_coverage (cs : List Candidate) (roots : List Nat)
    (width : Nat) (seen pending : List Nat)
    (h : ∀ r ∈ roots, r ∈ seen ∨ r ∈ width :: pending) :
    ∀ r ∈ roots, r ∈ width :: seen ∨
      r ∈ enqueueContractingChildren cs width seen pending := by
  intro r hr
  rcases h r hr with hs | hp
  · exact Or.inl (List.mem_cons_of_mem _ hs)
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl (by simp)
    · exact Or.inr (pending_mem_enqueue cs width seen pending r hp)

theorem step_closed (cs : List Candidate) (width : Nat)
    (seen pending : List Nat)
    (h : ∀ w ∈ seen, ∀ c ∈ cs,
      (c.analyze w).childWidth < w →
      (c.analyze w).childWidth ∈ seen ∨
        (c.analyze w).childWidth ∈ width :: pending) :
    ∀ w ∈ width :: seen, ∀ c ∈ cs,
      (c.analyze w).childWidth < w →
      (c.analyze w).childWidth ∈ width :: seen ∨
        (c.analyze w).childWidth ∈
          enqueueContractingChildren cs width seen pending := by
  intro w hw c hc hcontract
  rcases List.mem_cons.mp hw with rfl | hw
  · rcases enqueue_child_or_seen cs w seen pending c hc hcontract with hs | he
    · exact Or.inl (List.mem_cons_of_mem _ hs)
    · exact Or.inr he
  · rcases h w hw c hc hcontract with hs | hp
    · exact Or.inl (List.mem_cons_of_mem _ hs)
    · rcases List.mem_cons.mp hp with hcwidth | hp
      · exact Or.inl (by simp [hcwidth])
      · exact Or.inr (pending_mem_enqueue cs width seen pending _ hp)

theorem reachableWidthsAux_invariant (cs : List Candidate) (roots : List Nat)
    (M fuel : Nat) (pending seen : List Nat)
    (hn : (seen ++ pending).Nodup)
    (hb : ∀ x ∈ seen ++ pending, x ≤ M)
    (hr : ∀ r ∈ roots, r ∈ seen ∨ r ∈ pending)
    (hc : ∀ w ∈ seen, ∀ c ∈ cs,
      (c.analyze w).childWidth < w →
      (c.analyze w).childWidth ∈ seen ∨
        (c.analyze w).childWidth ∈ pending)
    (hf : fuel + seen.length = M + 1) :
    let out := reachableWidthsAux cs fuel pending seen
    out.Nodup ∧
      (∀ x ∈ out, x ≤ M) ∧
      (∀ r ∈ roots, r ∈ out) ∧
      (∀ w ∈ out, ∀ c ∈ cs,
        (c.analyze w).childWidth < w →
        (c.analyze w).childWidth ∈ out) := by
  induction fuel generalizing pending seen with
  | zero =>
    have hpempty : pending = [] := by
      cases pending with
      | nil => rfl
      | cons p ps =>
        have hlen := nodup_length_bounded (seen ++ p :: ps) M hn hb
        simp only [List.length_append, List.length_cons] at hlen
        omega
    subst pending
    simp only [reachableWidthsAux]
    refine ⟨by simpa using hn, ?_, ?_, ?_⟩
    · intro x hx
      exact hb x (by simpa using hx)
    · intro r hx
      rcases hr r hx with hs | hp
      · exact hs
      · simp at hp
    · intro w hw c hcm hcontract
      rcases hc w hw c hcm hcontract with hs | hp
      · exact hs
      · simp at hp
  | succ fuel ih =>
    cases pending with
    | nil =>
      simp only [reachableWidthsAux]
      refine ⟨by simpa using hn, ?_, ?_, ?_⟩
      · intro x hx
        exact hb x (by simpa using hx)
      · intro r hx
        rcases hr r hx with hs | hp
        · exact hs
        · simp at hp
      · intro w hw c hcm hcontract
        rcases hc w hw c hcm hcontract with hs | hp
        · exact hs
        · simp at hp
    | cons width pending =>
      have hn' := step_nodup cs width seen pending hn
      have hb' := step_bounded cs width M seen pending hb
      have hr' := step_coverage cs roots width seen pending hr
      have hc' := step_closed cs width seen pending hc
      have hf' : fuel + (width :: seen).length = M + 1 := by
        simp only [List.length_cons] at *
        omega
      simpa only [reachableWidthsAux] using
        ih (enqueueContractingChildren cs width seen pending)
          (width :: seen) hn' hb' hr' hc' hf'

theorem foldl_max_initial_le (xs : List Nat) (initial : Nat) :
    initial ≤ xs.foldl max initial := by
  induction xs generalizing initial with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left _ _) (ih _)

theorem mem_le_foldl_max (xs : List Nat) (initial x : Nat)
    (hx : x ∈ xs) : x ≤ xs.foldl max initial := by
  induction xs generalizing initial with
  | nil => simp at hx
  | cons a as ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · have hle : x ≤ max initial x := le_max_right _ _
      have hmono := foldl_max_initial_le as (max initial x)
      exact le_trans hle hmono
    · exact ih _ hx

theorem reachableWidths_properties (cs : List Candidate) (roots : List Nat) :
    let M := roots.foldl max 0
    let out := reachableWidths cs roots
    out.Nodup ∧
      (∀ x ∈ out, x ≤ M) ∧
      (∀ r ∈ roots, r ∈ out) ∧
      (∀ w ∈ out, ∀ c ∈ cs,
        (c.analyze w).childWidth < w →
        (c.analyze w).childWidth ∈ out) := by
  unfold reachableWidths
  apply reachableWidthsAux_invariant cs roots
  · simpa using eraseDups_nodup roots
  · intro x hx
    have hm : x ∈ roots := (eraseDups_mem roots x).mp (by simpa using hx)
    exact mem_le_foldl_max roots 0 x hm
  · intro r hr
    exact Or.inr ((eraseDups_mem roots r).mpr hr)
  · intro w hw
    simp at hw
  · simp

theorem reachableWidths_nodup (cs : List Candidate) (roots : List Nat) :
    (reachableWidths cs roots).Nodup :=
  (reachableWidths_properties cs roots).1

theorem reachableWidths_le_maxRoot (cs : List Candidate) (roots : List Nat)
    (x : Nat) (hx : x ∈ reachableWidths cs roots) :
    x ≤ roots.foldl max 0 :=
  (reachableWidths_properties cs roots).2.1 x hx

theorem reachableWidths_root_mem (cs : List Candidate) (roots : List Nat)
    (r : Nat) (hr : r ∈ roots) :
    r ∈ reachableWidths cs roots :=
  (reachableWidths_properties cs roots).2.2.1 r hr

theorem reachableWidths_child_mem (cs : List Candidate) (roots : List Nat)
    (w : Nat) (hw : w ∈ reachableWidths cs roots)
    (c : Candidate) (hc : c ∈ cs)
    (hcontract : (c.analyze w).childWidth < w) :
    (c.analyze w).childWidth ∈ reachableWidths cs roots :=
  (reachableWidths_properties cs roots).2.2.2 w hw c hc hcontract

end Paper.PlannerReachability
