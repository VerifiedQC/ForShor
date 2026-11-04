import Mathlib

/-!
# Machine-integer resource arithmetic

Natural-number arithmetic about depth, storage and index bounds against the machine limits `defaultMax` and `wideMax`. Includes `native_depth_bound` (a power `3^d` within the wide limit forces `d ≤ 39`) and the derived shape bounds such as `terminal_shape_bound`.
-/

set_option autoImplicit false
namespace MachineResource
def defaultMax : Nat := 2147483647
def wideMax : Nat := 9223372036854775807

theorem power_step {q d : Nat} (hq : q = 3^d) :
    3*q = 3^(d+1) := by simp [hq, pow_succ]; omega

theorem guarded_depth_step {q u : Nat} (h : q ≤ u/3) :
    3*q ≤ u := by omega

theorem native_depth_bound {d u : Nat}
    (hu : u ≤ wideMax) (hp : 3^d ≤ u) : d ≤ 39 := by
  by_contra h
  have hd : 40 ≤ d := by omega
  have ht : (3:Nat)^40 ≤ 3^d := pow_le_pow_right' (by norm_num) hd
  norm_num [wideMax] at hu
  norm_num at ht
  omega

theorem terminal_shape_bound {depth t : Nat} (hd : depth ≤ 39) (ht : t ≤ depth) :
    2*t + depth + 3 ≤ 120 ∧ t ≤ 39 ∧ 3*depth+3 ≤ 120 := by omega

theorem terminal_row_storage {depth t : Nat} (ht : t ≤ depth) :
    2*t + depth + 3 ≤ 3*depth+3 := by omega

theorem terminal_objective_shape {depth t : Nat} (hd : depth ≤ 39) (ht : t ≤ depth) :
    (t+1) ≤ 40 ∧ (depth+1)*(depth+1) ≤ 1600 := by
  constructor
  · omega
  · have h : depth+1 ≤ 40 := by omega
    nlinarith

theorem terminal_matrix_elements {depth t : Nat}
    (hd : depth ≤ 39) (ht : t ≤ depth) :
    (3*depth+3)*t ≤ 4680 := by
  have hm : 3*depth+3 ≤ 120 := by omega
  have hn : t ≤ 39 := by omega
  nlinarith

theorem product_window_indices {na nb i j : Nat}
    (ha : 1 ≤ na) (hb : 1 ≤ nb)
    (hi : 1 ≤ i ∧ i ≤ na) (hj : 1 ≤ j ∧ j ≤ nb)
    (hs : na+nb+1 ≤ defaultMax) :
    1 ≤ i+j-1 ∧ i+j-1 < na+nb+1 ∧
    i+j ≤ defaultMax ∧ i+nb < na+nb+1 ∧
    i+1 ≤ defaultMax ∧ j+1 ≤ defaultMax := by omega

theorem guarded_extent_sum {na nb : Nat} (hb : nb+1 ≤ defaultMax)
    (ha : na ≤ defaultMax-nb-1) :
    na+nb+1 ≤ defaultMax := by omega

theorem conservative_limb_sum {na nb : Nat}
    (ha : na ≤ 1073741822) (hb : nb ≤ 1073741822) :
    na+nb+1 < defaultMax := by norm_num [defaultMax]; omega

theorem forward_do_final {bound i : Nat}
    (hb : bound < defaultMax) (hi : i ≤ bound) :
    i+1 ≤ defaultMax := by omega

theorem extent_plus_one {n : Nat} (h : n < defaultMax-1) :
    n+1 < defaultMax := by omega

theorem allocation_counter_step {count : Nat} (h : count < defaultMax) :
    count+1 ≤ defaultMax := by omega

theorem arena_double {capacity : Nat} (h : capacity ≤ defaultMax/2) :
    2*capacity < defaultMax ∧ 2*capacity+1 ≤ defaultMax := by
  norm_num [defaultMax] at *
  omega

theorem arena_insert {used capacity : Nat} (hu : used < capacity)
    (hc : capacity < defaultMax) :
    used+1 ≤ capacity ∧ used+1 < defaultMax := by omega

theorem child_scalar_bounds {n k : Nat} (hn : n < 536870912)
    (hk : 1 ≤ k ∧ k ≤ n) :
    2*k-1 < defaultMax ∧ 4*k-4 < defaultMax ∧
    3*k-1 < defaultMax ∧ k+1 < defaultMax := by
  norm_num [defaultMax]; omega

def within (cap lo hi : Nat) : Prop := lo ≤ hi ∧ hi < cap

theorem shape_index {cap lo hi i : Nat}
    (hw : within cap lo hi) (hi' : lo ≤ i ∧ i ≤ hi) :
    i < cap := by unfold within at hw; omega

inductive Outcome (α : Type)
| answer (value : α)
| nonanswer
| fault
deriving DecidableEq

def checkedIncrement (cap count : Nat) : Outcome Nat :=
  if count < cap then .answer (count+1) else .nonanswer

theorem checked_increment_answer {cap count value : Nat} :
    checkedIncrement cap count = .answer value ↔
      count < cap ∧ value = count+1 := by
  unfold checkedIncrement
  split_ifs with h
  · simp only [Outcome.answer.injEq]; omega
  · simp [h]

theorem checked_increment_no_overflow {cap count value : Nat}
    (h : checkedIncrement cap count = .answer value) :
    value ≤ cap := by
  obtain ⟨hc, rfl⟩ := checked_increment_answer.mp h
  omega

def checkedExtent (cap na nb : Nat) : Outcome Nat :=
  if nb+1 ≤ cap ∧ na ≤ cap-nb-1 then .answer (na+nb+1) else .nonanswer

theorem checked_extent_answer {cap na nb value : Nat} :
    checkedExtent cap na nb = .answer value →
      value = na+nb+1 ∧ value ≤ cap := by
  unfold checkedExtent
  split_ifs with h
  · intro hv; simp only [Outcome.answer.injEq] at hv
    constructor
    · omega
    · omega
  · intro h; cases h

-- Allocation failure is an allowed outcome, never evidence of feasibility.
def reserve (enough : Bool) (extent : Nat) : Outcome Nat :=
  if enough then .answer extent else .nonanswer

theorem reserve_success {enough : Bool} {extent got : Nat}
    (h : reserve enough extent = .answer got) : got = extent := by
  unfold reserve at h
  split at h
  · cases h; rfl
  · cases h

-- Sequential composition preserves nonanswers and faults.
def bind {α β : Type} (out : Outcome α) (next : α → Outcome β) : Outcome β :=
  match out with
  | .answer a => next a
  | .nonanswer => .nonanswer
  | .fault => .fault

theorem bind_nonanswer {α β : Type} (next : α → Outcome β) :
    bind .nonanswer next = .nonanswer := rfl

theorem bind_fault {α β : Type} (next : α → Outcome β) :
    bind .fault next = .fault := rfl

theorem bind_answer_origin {α β : Type} {out : Outcome α}
    {next : α → Outcome β} {value : β}
    (h : bind out next = .answer value) :
    ∃ a, out = .answer a ∧ next a = .answer value := by
  cases out with
  | answer a => exact ⟨a,rfl,h⟩
  | nonanswer => cases h
  | fault => cases h

theorem guarded_extent_sum_strict {na nb : Nat}
    (hb : nb+2 ≤ defaultMax) (ha : na ≤ defaultMax-nb-2) :
    na+nb+1 < defaultMax := by omega

theorem rtoi_truncation (x : Int) (hx : x ≤ 0) :
    x.tdiv 1000000 = -((-x)/1000000) := by
  conv_lhs => rw [← Int.neg_neg x, Int.neg_tdiv]
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]

theorem rtoi_guard_exact {lim v digit : Int}
    (hl : lim ≤ -1000000) (hd : 0 ≤ digit ∧ digit < 1000000) :
    ¬ v < (lim+digit).tdiv 1000000 ↔
      lim ≤ v*1000000-digit := by
  rw [rtoi_truncation (lim+digit) (by omega)]
  omega

theorem rtoi_step_native_safe {lim v digit : Int}
    (hl : -(9223372036854775808:Int) ≤ lim ∧ lim ≤ -1000000)
    (hv : lim ≤ v ∧ v ≤ 0)
    (hd : 0 ≤ digit ∧ digit < 1000000)
    (hg : ¬ v < (lim+digit).tdiv 1000000) :
    -(9223372036854775808:Int) ≤ lim+digit ∧ lim+digit ≤ 0 ∧
    lim ≤ v*1000000 ∧ v*1000000 ≤ 0 ∧
    lim ≤ v*1000000-digit ∧ v*1000000-digit ≤ 0 := by
  have h := (rtoi_guard_exact hl.2 hd).mp hg
  omega

theorem rtoi_positive_final_negation {v : Int}
    (h : -(9223372036854775807:Int) ≤ v ∧ v ≤ 0) :
    0 ≤ -v ∧ -v ≤ 9223372036854775807 := by omega

def guardedHorner (lim : Int) (v : Int) : List Int → Outcome Int
  | [] => .answer v
  | digit::rest =>
    if v < (lim+digit).tdiv 1000000 then .nonanswer
    else guardedHorner lim (v*1000000-digit) rest

theorem guarded_horner_sound {lim v : Int} {digits : List Int} {value : Int}
    (hl : lim ≤ -1000000) (hv : lim ≤ v ∧ v ≤ 0)
    (hd : ∀ digit ∈ digits, 0 ≤ digit ∧ digit < 1000000)
    (h : guardedHorner lim v digits = .answer value) :
    value = digits.foldl (fun x digit => x*1000000-digit) v ∧
    lim ≤ value ∧ value ≤ 0 := by
  induction digits generalizing v with
  | nil =>
    simp only [guardedHorner, Outcome.answer.injEq] at h
    subst value
    simp [hv]
  | cons digit rest ih =>
    by_cases hg : v < (lim+digit).tdiv 1000000
    · rw [guardedHorner, if_pos hg] at h
      cases h
    · rw [guardedHorner, if_neg hg] at h
      have hdi := hd digit (by simp)
      have hn : lim ≤ v*1000000-digit ∧ v*1000000-digit ≤ 0 := by
        have := (rtoi_guard_exact hl hdi).mp hg
        omega
      have hr : ∀ d ∈ rest, 0 ≤ d ∧ d < 1000000 := by
        intro d hm; exact hd d (by simp [hm])
      simpa only [List.foldl_cons] using ih hn hr h


theorem negative_horner_le_start {v : Int} {digits : List Int}
    (hv : v ≤ 0) (hd : ∀ digit ∈ digits, 0 ≤ digit) :
    digits.foldl (fun x digit => x*1000000-digit) v ≤ v := by
  induction digits generalizing v with
  | nil => simp
  | cons digit rest ih =>
    have hdi : 0 ≤ digit := hd digit (by simp)
    have hn : v*1000000-digit ≤ 0 := by omega
    have hr : ∀ d ∈ rest, 0 ≤ d := by
      intro d hm; exact hd d (by simp [hm])
    have ht := ih hn hr
    simp only [List.foldl_cons]
    omega

theorem guarded_horner_complete {lim v : Int} {digits : List Int}
    (hl : lim ≤ -1000000) (hv : lim ≤ v ∧ v ≤ 0)
    (hd : ∀ digit ∈ digits, 0 ≤ digit ∧ digit < 1000000)
    (hfit : lim ≤ digits.foldl (fun x digit => x*1000000-digit) v) :
    guardedHorner lim v digits =
      .answer (digits.foldl (fun x digit => x*1000000-digit) v) := by
  induction digits generalizing v with
  | nil => rfl
  | cons digit rest ih =>
    have hdi := hd digit (by simp)
    have hr : ∀ d ∈ rest, 0 ≤ d ∧ d < 1000000 := by
      intro d hm; exact hd d (by simp [hm])
    have hnneg : v*1000000-digit ≤ 0 := by omega
    have ht := negative_horner_le_start hnneg (fun d hm => (hr d hm).1)
    simp only [List.foldl_cons] at hfit ⊢
    have hn : lim ≤ v*1000000-digit ∧ v*1000000-digit ≤ 0 := by omega
    have hg := (rtoi_guard_exact hl hdi).mpr hn.1
    rw [guardedHorner, if_neg hg]
    exact ih hn hr hfit

theorem guarded_horner_success_iff {lim v : Int} {digits : List Int}
    (hl : lim ≤ -1000000) (hv : lim ≤ v ∧ v ≤ 0)
    (hd : ∀ digit ∈ digits, 0 ≤ digit ∧ digit < 1000000) :
    (∃ value, guardedHorner lim v digits = .answer value) ↔
      lim ≤ digits.foldl (fun x digit => x*1000000-digit) v := by
  constructor
  · rintro ⟨value,h⟩
    obtain ⟨heq,hlo,_⟩ := guarded_horner_sound hl hv hd h
    omega
  · intro h
    exact ⟨_, guarded_horner_complete hl hv hd h⟩

end MachineResource
