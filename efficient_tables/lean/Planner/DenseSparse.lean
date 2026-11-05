import Planner.RecursiveLocal
import Planner.Reachability

/-!
# Dense versus sparse planner tables

Relates the dense plan table built over a width prefix to the sparse reachable-width fold. Proves properties of the dense prefix and table (`densePrefix_get_stable`, `buildPlanTable_get`, `buildPlanTable_fixed`) and that the sparse fold reconstructs the dense choice (`sparseFold_reconstruct`).
-/

namespace Paper.PlannerDenseSparse

open TableGeneration.RecursiveCost

theorem densePrefix_succ (candidates : List Candidate) (n : Nat) :
    (List.range (n + 1)).foldl
      (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[] =
    ((List.range n).foldl
      (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[]).push
      (chooseAtWidth candidates
        ((List.range n).foldl
          (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[]) n) := by
  rw [List.range_succ, List.foldl_append]
  rfl

theorem densePrefix_size (candidates : List Candidate) (n : Nat) :
    ((List.range n).foldl
      (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[]).size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [densePrefix_succ, Array.size_push, ih]

theorem densePrefix_get_stable (candidates : List Candidate)
    {n m i : Nat} (hnm : n ≤ m) (hi : i < n) :
    ((List.range n).foldl
      (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[])[i]? =
    ((List.range m).foldl
      (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[])[i]? := by
  induction m with
  | zero => have : n = 0 := Nat.eq_zero_of_le_zero hnm; omega
  | succ m ih =>
    by_cases hnm' : n ≤ m
    · rw [densePrefix_succ, Array.getElem?_push]
      have hne : i ≠ ((List.range m).foldl
          (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[]).size := by
        rw [densePrefix_size]
        omega
      simp only [hne, ↓reduceIte]
      exact ih hnm'
    · have : n = m + 1 := by omega
      subst n
      rfl

theorem densePrefix_get_self (candidates : List Candidate) (n : Nat) :
    ((List.range (n + 1)).foldl
      (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[])[n]? =
    some (chooseAtWidth candidates
      ((List.range n).foldl
        (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[]) n) := by
  rw [densePrefix_succ]
  simpa only [densePrefix_size candidates n] using
    (Array.getElem?_push_size
      (xs := (List.range n).foldl
        (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[])
      (x := chooseAtWidth candidates
        ((List.range n).foldl
          (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[]) n))

theorem buildPlanTable_size (candidates : List Candidate) (maxWidth : Nat) :
    (buildPlanTable candidates maxWidth).size = maxWidth + 1 := by
  exact densePrefix_size candidates (maxWidth + 1)

theorem buildPlanTable_get (candidates : List Candidate) (maxWidth width : Nat)
    (hwidth : width ≤ maxWidth) :
    (buildPlanTable candidates maxWidth)[width]? =
      some (chooseAtWidth candidates
        ((List.range width).foldl
          (fun plans w => plans.push (chooseAtWidth candidates plans w)) #[]) width) := by
  unfold buildPlanTable
  rw [← densePrefix_get_stable candidates (show width + 1 ≤ maxWidth + 1 by omega)
    (by omega : width < width + 1)]
  exact densePrefix_get_self candidates width

theorem chooseAtWidth_congr (candidates : List Candidate)
    (a b : Array PlanResult) (width : Nat)
    (hlookup : ∀ c ∈ candidates,
      (c.analyze width).childWidth < width →
      a[(c.analyze width).childWidth]? = b[(c.analyze width).childWidth]?) :
    chooseAtWidth candidates a width = chooseAtWidth candidates b width := by
  let stepA : PlanResult → Candidate → PlanResult := fun current c =>
    let analysis := c.analyze width
    if analysis.childWidth < width then
      match a[analysis.childWidth]? with
      | some child => lowerGateCount (PlanResult.step width c analysis child) current
      | none => current
    else current
  let stepB : PlanResult → Candidate → PlanResult := fun current c =>
    let analysis := c.analyze width
    if analysis.childWidth < width then
      match b[analysis.childWidth]? with
      | some child => lowerGateCount (PlanResult.step width c analysis child) current
      | none => current
    else current
  have hstep (current : PlanResult) (c : Candidate) (hc : c ∈ candidates) :
      stepA current c = stepB current c := by
    dsimp [stepA, stepB]
    by_cases h : (c.analyze width).childWidth < width
    · simp [h, hlookup c hc h]
    · simp [h]
  have hfold (cs : List Candidate) (hsub : ∀ c ∈ cs, c ∈ candidates) :
      ∀ current : PlanResult, cs.foldl stepA current = cs.foldl stepB current := by
    induction cs with
    | nil => intro current; rfl
    | cons c cs ih =>
      intro current
      have hc : c ∈ candidates := hsub c (by simp)
      have ht : ∀ x ∈ cs, x ∈ candidates := by
        intro x hx
        exact hsub x (by simp [hx])
      simp only [List.foldl_cons]
      rw [hstep current c hc]
      exact ih ht (stepB current c)
  change candidates.foldl stepA (PlanResult.base width) =
    candidates.foldl stepB (PlanResult.base width)
  exact hfold candidates (by intro c hc; exact hc) (PlanResult.base width)

theorem buildPlanTable_fixed (candidates : List Candidate) (maxWidth width : Nat)
    (hwidth : width ≤ maxWidth) :
    (buildPlanTable candidates maxWidth)[width]? =
      some (chooseAtWidth candidates (buildPlanTable candidates maxWidth) width) := by
  rw [buildPlanTable_get candidates maxWidth width hwidth]
  congr 1
  apply chooseAtWidth_congr
  intro c hc hchild
  exact densePrefix_get_stable candidates
    (show width ≤ maxWidth + 1 by omega) hchild

theorem buildPlanTable_plan_width (candidates : List Candidate) (maxWidth width : Nat)
    (hwidth : width ≤ maxWidth) :
    ((buildPlanTable candidates maxWidth)[width]?.getD (PlanResult.base width)).width = width := by
  rw [buildPlanTable_fixed candidates maxWidth width hwidth]
  exact RecursivePlannerLocal.chooseAtWidth_width candidates
    (buildPlanTable candidates maxWidth) width

theorem findPlan?_cons_self (p : PlanResult) (plans : List PlanResult) :
    findPlan? (p :: plans) p.width = some p := by
  simp [findPlan?]

theorem findPlan?_cons_ne (p : PlanResult) (plans : List PlanResult)
    (width : Nat) (hne : p.width ≠ width) :
    findPlan? (p :: plans) width = findPlan? plans width := by
  simp [findPlan?, hne]

theorem sparseFold_reconstruct (candidates : List Candidate) (maxWidth : Nat)
    (todo done : List Nat) (plans : List PlanResult)
    (hsorted : todo.Pairwise (· < ·))
    (horder : ∀ d ∈ done, ∀ t ∈ todo, d < t)
    (hbound : ∀ w ∈ done ++ todo, w ≤ maxWidth)
    (hclosed : ∀ w ∈ done ++ todo, ∀ c ∈ candidates,
      (c.analyze w).childWidth < w →
      (c.analyze w).childWidth ∈ done ++ todo)
    (hlookup : ∀ d ∈ done,
      findPlan? plans d = (buildPlanTable candidates maxWidth)[d]?) :
    ∀ d ∈ done ++ todo,
      findPlan? (todo.foldl
        (fun ps w => chooseAtWidthSparse candidates ps w :: ps) plans) d =
        (buildPlanTable candidates maxWidth)[d]? := by
  induction todo generalizing done plans with
  | nil =>
    simpa using hlookup
  | cons w rest ih =>
    have hsplit : (∀ t ∈ rest, w < t) ∧ rest.Pairwise (· < ·) := by
      simpa only [List.pairwise_cons] using hsorted
    obtain ⟨hwlt, hrest⟩ := hsplit
    have hchild (c : Candidate) (hc : c ∈ candidates)
        (hcwidth : (c.analyze w).childWidth < w) :
        (c.analyze w).childWidth ∈ done := by
      have hmem := hclosed w (by simp) c hc hcwidth
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hmem
      · rcases List.mem_cons.mp hmem with heq | htail
        · omega
        · have := hwlt _ htail
          omega
    let p := chooseAtWidthSparse candidates plans w
    have hp : p = chooseAtWidth candidates
        (buildPlanTable candidates maxWidth) w := by
      apply RecursivePlannerLocal.chooseAtWidthSparse_eq_chooseAtWidth_of_child_lookup
      intro c hc hcwidth
      exact hlookup _ (hchild c hc hcwidth)
    have hpwidth : p.width = w := by
      rw [hp]
      exact RecursivePlannerLocal.chooseAtWidth_width candidates
        (buildPlanTable candidates maxWidth) w
    have hmemSwap (d : Nat) :
        d ∈ done ++ w :: rest ↔ d ∈ (w :: done) ++ rest := by
      simp only [List.mem_append, List.mem_cons]
      rw [or_assoc]
      exact or_left_comm
    have horder' : ∀ d ∈ w :: done, ∀ t ∈ rest, d < t := by
      intro d hd t ht
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hwlt t ht
      · exact horder d hd t (by simp [ht])
    have hbound' : ∀ d ∈ (w :: done) ++ rest, d ≤ maxWidth := by
      intro d hd
      exact hbound d ((hmemSwap d).2 hd)
    have hclosed' : ∀ d ∈ (w :: done) ++ rest, ∀ c ∈ candidates,
        (c.analyze d).childWidth < d →
        (c.analyze d).childWidth ∈ (w :: done) ++ rest := by
      intro d hd c hc hlt
      exact (hmemSwap _).1 (hclosed d ((hmemSwap d).2 hd) c hc hlt)
    have hlookup' : ∀ d ∈ w :: done,
        findPlan? (p :: plans) d = (buildPlanTable candidates maxWidth)[d]? := by
      intro d hd
      rcases List.mem_cons.mp hd with heq | hd
      · subst d
        have hself : findPlan? (p :: plans) w = some p := by
          simpa only [hpwidth] using findPlan?_cons_self p plans
        rw [hself, buildPlanTable_fixed candidates maxWidth w
          (hbound w (by simp))]
        exact congrArg some hp
      · have hne : p.width ≠ d := by
          rw [hpwidth]
          have := horder d hd w (by simp)
          omega
        rw [findPlan?_cons_ne p plans d hne]
        exact hlookup d hd
    have hresult := ih (w :: done) (p :: plans) hrest horder' hbound' hclosed' hlookup'
    intro d hd
    have hd' := (hmemSwap d).1 hd
    simpa only [List.foldl_cons] using hresult d hd'

theorem sparseFold_eq_dense_of_closed (candidates : List Candidate)
    (maxWidth : Nat) (widths : List Nat)
    (hsorted : widths.Pairwise (· < ·))
    (hbound : ∀ width ∈ widths, width ≤ maxWidth)
    (hclosed : ∀ width ∈ widths, ∀ c ∈ candidates,
      (c.analyze width).childWidth < width →
      (c.analyze width).childWidth ∈ widths) :
    ∀ width ∈ widths,
      findPlan? (widths.foldl
        (fun plans w => chooseAtWidthSparse candidates plans w :: plans) []) width =
        (buildPlanTable candidates maxWidth)[width]? := by
  simpa using sparseFold_reconstruct candidates maxWidth widths [] [] hsorted
    (by simp) (by simpa using hbound) (by simpa using hclosed) (by simp)

theorem mergeSort_pairwise_lt_of_nodup (widths : List Nat)
    (hnodup : widths.Nodup) : (widths.mergeSort).Pairwise (· < ·) := by
  have hle : (widths.mergeSort).Pairwise (· ≤ ·) := by
    simpa only [decide_eq_true_eq] using
      (List.pairwise_mergeSort
        (le := fun a b : Nat => a ≤ b)
        (by intro a b c hab hbc
            simp only [decide_eq_true_eq] at *
            omega)
        (by intro a b
            simp only [Bool.or_eq_true, decide_eq_true_eq]
            omega) widths)
  have hn : (widths.mergeSort).Nodup :=
    hnodup.perm (List.mergeSort_perm widths (fun a b : Nat => a ≤ b)).symm
  have hne : (widths.mergeSort).Pairwise (· ≠ ·) :=
    List.nodup_iff_pairwise_ne.mp hn
  exact (hle.and hne).imp (by intro a b h; omega)

theorem buildSparsePlans_eq_dense_of_reachable_conditions
    (candidates : List Candidate) (roots : List Nat) (maxWidth : Nat)
    (hnodup : (reachableWidths candidates roots).Nodup)
    (hbound : ∀ width ∈ reachableWidths candidates roots, width ≤ maxWidth)
    (hclosed : ∀ width ∈ reachableWidths candidates roots,
      ∀ c ∈ candidates, (c.analyze width).childWidth < width →
        (c.analyze width).childWidth ∈ reachableWidths candidates roots) :
    ∀ width ∈ reachableWidths candidates roots,
      findPlan? (buildSparsePlans candidates roots) width =
        (buildPlanTable candidates maxWidth)[width]? := by
  let widths := reachableWidths candidates roots
  have hsort := mergeSort_pairwise_lt_of_nodup widths hnodup
  have hb : ∀ width ∈ widths.mergeSort, width ≤ maxWidth := by
    intro width hmem
    exact hbound width (List.mem_mergeSort.mp hmem)
  have hc : ∀ width ∈ widths.mergeSort, ∀ c ∈ candidates,
      (c.analyze width).childWidth < width →
        (c.analyze width).childWidth ∈ widths.mergeSort := by
    intro width hmem c hc hlt
    exact List.mem_mergeSort.mpr
      (hclosed width (List.mem_mergeSort.mp hmem) c hc hlt)
  have hfold := sparseFold_eq_dense_of_closed candidates maxWidth widths.mergeSort
    hsort hb hc
  intro width hmem
  exact hfold width (List.mem_mergeSort.mpr hmem)

theorem bestPlan_eq_dense_of_reachable_conditions
    (candidates : List Candidate) (width : Nat)
    (hnodup : (reachableWidths candidates [width]).Nodup)
    (hroot : width ∈ reachableWidths candidates [width])
    (hbound : ∀ w ∈ reachableWidths candidates [width], w ≤ width)
    (hclosed : ∀ w ∈ reachableWidths candidates [width],
      ∀ c ∈ candidates, (c.analyze w).childWidth < w →
        (c.analyze w).childWidth ∈ reachableWidths candidates [width]) :
    bestPlan candidates width =
      ((buildPlanTable candidates width)[width]?).getD (PlanResult.base width) := by
  unfold bestPlan
  rw [buildSparsePlans_eq_dense_of_reachable_conditions candidates [width] width
    hnodup hbound hclosed width hroot]

theorem sparse_root_some_of_reachable_conditions
    (candidates : List Candidate) (width : Nat)
    (hnodup : (reachableWidths candidates [width]).Nodup)
    (hroot : width ∈ reachableWidths candidates [width])
    (hbound : ∀ w ∈ reachableWidths candidates [width], w ≤ width)
    (hclosed : ∀ w ∈ reachableWidths candidates [width],
      ∀ c ∈ candidates, (c.analyze w).childWidth < w →
        (c.analyze w).childWidth ∈ reachableWidths candidates [width]) :
    findPlan? (buildSparsePlans candidates [width]) width =
      some (chooseAtWidth candidates (buildPlanTable candidates width) width) := by
  rw [buildSparsePlans_eq_dense_of_reachable_conditions candidates [width] width
    hnodup hbound hclosed width hroot]
  exact buildPlanTable_fixed candidates width width (by omega)

theorem bestPlan_eq_dense_choice_of_reachable_conditions
    (candidates : List Candidate) (width : Nat)
    (hnodup : (reachableWidths candidates [width]).Nodup)
    (hroot : width ∈ reachableWidths candidates [width])
    (hbound : ∀ w ∈ reachableWidths candidates [width], w ≤ width)
    (hclosed : ∀ w ∈ reachableWidths candidates [width],
      ∀ c ∈ candidates, (c.analyze w).childWidth < w →
        (c.analyze w).childWidth ∈ reachableWidths candidates [width]) :
    bestPlan candidates width =
      chooseAtWidth candidates (buildPlanTable candidates width) width := by
  unfold bestPlan
  rw [sparse_root_some_of_reachable_conditions candidates width
    hnodup hroot hbound hclosed]
  rfl

theorem buildSparsePlans_eq_dense (candidates : List Candidate)
    (roots : List Nat) :
    ∀ width ∈ reachableWidths candidates roots,
      findPlan? (buildSparsePlans candidates roots) width =
        (buildPlanTable candidates (roots.foldl max 0))[width]? := by
  apply buildSparsePlans_eq_dense_of_reachable_conditions
  · exact PlannerReachability.reachableWidths_nodup candidates roots
  · intro width hmem
    exact PlannerReachability.reachableWidths_le_maxRoot candidates roots width hmem
  · intro width hmem c hc hlt
    exact PlannerReachability.reachableWidths_child_mem candidates roots
      width hmem c hc hlt

theorem sparse_root_some (candidates : List Candidate) (width : Nat) :
    findPlan? (buildSparsePlans candidates [width]) width =
      some (chooseAtWidth candidates (buildPlanTable candidates width) width) := by
  have hroot : width ∈ reachableWidths candidates [width] :=
    PlannerReachability.reachableWidths_root_mem candidates [width] width (by simp)
  have h := buildSparsePlans_eq_dense candidates [width] width hroot
  simpa using
    (h.trans (buildPlanTable_fixed candidates width width (by omega)))

theorem bestPlan_eq_dense_choice (candidates : List Candidate) (width : Nat) :
    bestPlan candidates width =
      chooseAtWidth candidates (buildPlanTable candidates width) width := by
  unfold bestPlan
  rw [sparse_root_some]
  rfl

theorem bestKnownPlan_eq_dense_choice (width : Nat) :
    bestKnownPlan width =
      chooseAtWidth bestKnownCandidates
        (buildPlanTable bestKnownCandidates width) width := by
  exact bestPlan_eq_dense_choice bestKnownCandidates width

end Paper.PlannerDenseSparse
