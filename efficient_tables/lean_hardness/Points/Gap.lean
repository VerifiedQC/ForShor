import Points.Weight
import TableGeneration.Language

/-!
# The gap lemma for two registers

For `k = 2`:
* `detOK_apply`: every safe operation keeps the determinant of the state of the form `±2^t`;
* `Rep`: the current registers are rational combinations (`C`) of an anchor state's rows, and
  `rep_apply` updates `C` by the same row operation;
* `cls_step`: from the identity, after one operation every entry of `C` is `D1`, after two `D2`;
* `gap`: if the anchor has row `(1, a)` (a marker for point `a`) and, `g` operations later, some
  register is `(1, b)`, then `b − a = y · (±2^t)` with `y` an entry of `C`; hence `g ≤ 1` gives
  `W1 (b − a)` and `g = 2` gives `W2 (b − a)`.
-/

namespace Pts

open TableGeneration Operations

/-- The row of the integer point `z` for `k = 2`. -/
def row (z : ℤ) : Register 2 := expectedRow (k := 2) (.int z)

@[simp] lemma row_zero (z : ℤ) : row z 0 = 1 := by simp [row, expectedRow]
@[simp] lemma row_one (z : ℤ) : row z 1 = z := by simp [row, expectedRow]

def det2 (S : State 2) : ℤ := S 0 0 * S 1 1 - S 0 1 * S 1 0

/-- The determinant is a signed power of two. -/
def DetOK (S : State 2) : Prop := ∃ (s : ℤ) (t : ℕ), (s = 1 ∨ s = -1) ∧ det2 S = s * 2 ^ t

lemma detOK_start : DetOK State.start_state := ⟨1, 0, Or.inl rfl, by simp [det2, State.start_state]⟩

lemma fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

lemma fin2_other {i j : Fin 2} (h : i ≠ j) : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;> simp_all

lemma det2_setReg0 (S : State 2) (r : Register 2) :
    det2 (State.setReg S 0 r) = r 0 * S 1 1 - r 1 * S 1 0 := by simp [det2, State.setReg]

lemma det2_setReg1 (S : State 2) (r : Register 2) :
    det2 (State.setReg S 1 r) = S 0 0 * r 1 - S 0 1 * r 0 := by simp [det2, State.setReg]

/-- **Determinant invariant.** -/
theorem detOK_apply {S S' : State 2} {op : valid_ops 2} (hok : Prog.OpOK? op = true)
    (h : applyOp? S op = some S') (hS : DetOK S) : DetOK S' := by
  obtain ⟨s, t, hs, hdet⟩ := hS
  cases op with
  | phaseProduct i => simp [applyOp?] at h; subst h; exact ⟨s, t, hs, hdet⟩
  | negate i =>
    simp only [applyOp?, Option.some.injEq] at h; subst h
    refine ⟨-s, t, by rcases hs with rfl | rfl <;> simp, ?_⟩
    rcases fin2_cases i with rfl | rfl
    · simp only [State.negateReg, det2_setReg0, Register.negate]; unfold det2 at hdet
      linear_combination -hdet
    · simp only [State.negateReg, det2_setReg1, Register.negate]; unfold det2 at hdet
      linear_combination -hdet
  | shiftL i n =>
    simp only [applyOp?, Option.some.injEq] at h; subst h
    refine ⟨s, t + n, hs, ?_⟩
    rcases fin2_cases i with rfl | rfl
    · simp only [State.shiftLReg, det2_setReg0, Register.shiftL]; unfold det2 at hdet
      rw [pow_add]; linear_combination (2 : ℤ) ^ n * hdet
    · simp only [State.shiftLReg, det2_setReg1, Register.shiftL]; unfold det2 at hdet
      rw [pow_add]; linear_combination (2 : ℤ) ^ n * hdet
  | addScaled d src neg sh =>
    simp only [Prog.OpOK?, decide_eq_true_eq] at hok
    simp only [applyOp?, Option.some.injEq] at h; subst h
    refine ⟨s, t, hs, ?_⟩
    rcases fin2_other hok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [State.addScaledReg, det2_setReg0, Register.addScaled]; unfold det2 at hdet
      linear_combination hdet
    · simp only [State.addScaledReg, det2_setReg1, Register.addScaled]; unfold det2 at hdet
      linear_combination hdet
  | shiftR i n =>
    simp only [applyOp?, State.shiftRReg?, Register.shiftR?] at h
    split_ifs at h with hdiv
    swap
    · exact absurd h (by simp)
    change some (State.setReg S i fun j => S i j / 2 ^ n) = some S' at h
    simp only [Option.some.injEq] at h
    subst h
    have hd : ∀ j, (2 : ℤ) ^ n ∣ S i j := fun j => by
      have := List.all_eq_true.mp hdiv j (List.mem_finRange j)
      exact Int.dvd_of_emod_eq_zero (of_decide_eq_true this)
    -- `det S' * 2^n = det S`
    have hmul : det2 (State.setReg S i fun j => S i j / 2 ^ n) * 2 ^ n = s * 2 ^ t := by
      rw [← hdet]
      rcases fin2_cases i with rfl | rfl
      · rw [det2_setReg0, det2]
        have h0 := Int.ediv_mul_cancel (hd 0)
        have h1 := Int.ediv_mul_cancel (hd 1)
        linear_combination (S 1 1) * h0 - (S 1 0) * h1
      · rw [det2_setReg1, det2]
        have h0 := Int.ediv_mul_cancel (hd 0)
        have h1 := Int.ediv_mul_cancel (hd 1)
        linear_combination (S 0 0) * h1 - (S 0 1) * h0
    have hn : n ≤ t := le_of_pow_dvd (not_two_dvd_sign hs)
      ⟨det2 (State.setReg S i fun j => S i j / 2 ^ n), by linear_combination -hmul⟩
    refine ⟨s, t - n, hs, ?_⟩
    have : det2 (State.setReg S i fun j => S i j / 2 ^ n) * 2 ^ n = s * 2 ^ (t - n) * 2 ^ n := by
      rw [hmul, mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
    exact mul_right_cancel₀ (by positivity) this

/-! ### Transfer coefficients -/

/-- Coefficient matrices. -/
abbrev Coef := Fin 2 → Fin 2 → ℚ

def C0 : Coef := fun i l => if i = l then 1 else 0

/-- The current state is `C` times the anchor state. -/
def Rep (S Sa : State 2) (C : Coef) : Prop :=
  ∀ i j, (S i j : ℚ) = C i 0 * Sa 0 j + C i 1 * Sa 1 j

lemma rep_self (S : State 2) : Rep S S C0 := by
  intro i j; rcases fin2_cases i with rfl | rfl <;> simp [C0]

/-- The row operation of `op` on coefficients. -/
def updC (op : valid_ops 2) (C : Coef) : Coef :=
  match op with
  | .addScaled d s neg sh => fun i l =>
      if i = d then C d l + (if neg then -1 else 1) * 2 ^ sh * C s l else C i l
  | .shiftL i n => fun i' l => if i' = i then 2 ^ n * C i l else C i' l
  | .shiftR i n => fun i' l => if i' = i then C i l / 2 ^ n else C i' l
  | .negate i => fun i' l => if i' = i then -C i l else C i' l
  | .phaseProduct _ => C

lemma rep_apply {S S' Sa : State 2} {op : valid_ops 2} {C : Coef} (h : applyOp? S op = some S')
    (hR : Rep S Sa C) : Rep S' Sa (updC op C) := by
  cases op with
  | phaseProduct i => simp [applyOp?] at h; subst h; exact hR
  | negate i =>
    simp only [applyOp?, Option.some.injEq] at h; subst h
    intro i' j
    by_cases hi : i' = i
    · subst hi; simp [State.negateReg, State.setReg, Register.negate, updC, hR i' j]; ring
    · simp [State.negateReg, State.setReg, updC, hi, hR i' j]
  | shiftL i n =>
    simp only [applyOp?, Option.some.injEq] at h; subst h
    intro i' j
    by_cases hi : i' = i
    · subst hi; simp [State.shiftLReg, State.setReg, Register.shiftL, updC, hR i' j]; ring
    · simp [State.shiftLReg, State.setReg, updC, hi, hR i' j]
  | addScaled d src neg sh =>
    simp only [applyOp?, Option.some.injEq] at h; subst h
    intro i' j
    by_cases hi : i' = d
    · subst hi
      simp only [State.addScaledReg, State.setReg, if_pos, Register.addScaled, updC]
      push_cast; rw [hR i' j, hR src j]; split_ifs <;> push_cast <;> ring
    · simp [State.addScaledReg, State.setReg, updC, hi, hR i' j]
  | shiftR i n =>
    simp only [applyOp?, State.shiftRReg?, Register.shiftR?] at h
    split_ifs at h with hdiv
    swap
    · exact absurd h (by simp)
    change some (State.setReg S i fun j => S i j / 2 ^ n) = some S' at h
    simp only [Option.some.injEq] at h
    subst h
    intro i' j
    by_cases hi : i' = i
    · subst hi
      have hdj : (2 : ℤ) ^ n ∣ S i' j := by
        have := List.all_eq_true.mp hdiv j (List.mem_finRange j)
        exact Int.dvd_of_emod_eq_zero (of_decide_eq_true this)
      simp only [State.setReg, if_pos, updC]
      rw [Int.cast_div hdj (by positivity), hR i' j]
      push_cast; ring
    · simp [State.setReg, updC, hi, hR i' j]

/-- Coefficient classes after `g` operations from the identity. -/
def Cls : ℕ → Coef → Prop
  | 0, C => C = C0
  | 1, C => ∀ i l, D1 (C i l)
  | 2, C => ∀ i l, D2 (C i l)
  | _, _ => True

lemma sgnpow_D1 (neg : Bool) (sh : ℕ) : D1 ((if neg then -1 else 1) * 2 ^ sh : ℚ) := by
  refine Or.inr ⟨if neg then -1 else 1, sh, by cases neg <;> simp, ?_⟩
  cases neg <;> simp

lemma pow_D1 (n : ℕ) : D1 ((2 : ℚ) ^ n) := Or.inr ⟨1, n, Or.inl rfl, by simp⟩
lemma invpow_D1 (n : ℕ) : D1 ((2 : ℚ) ^ n)⁻¹ := Or.inr ⟨1, -n, Or.inl rfl, by simp⟩
lemma negone_D1 : D1 (-1 : ℚ) := Or.inr ⟨-1, 0, Or.inr rfl, by simp⟩

lemma C0_D1 (i l : Fin 2) : D1 (C0 i l) := by
  unfold C0; split_ifs; exacts [D1_one, D1_zero]

lemma C0_add {d s : Fin 2} (h : d ≠ s) {c : ℚ} (hc : D1 c) (l : Fin 2) :
    D1 (C0 d l + c * C0 s l) := by
  unfold C0
  by_cases hl : d = l
  · rw [if_pos hl, if_neg (fun h' => h (hl.trans h'.symm))]; simpa using D1_one
  · by_cases hs : s = l
    · rw [if_neg hl, if_pos hs]; simpa using hc
    · rw [if_neg hl, if_neg hs]; simpa using D1_zero

/-- **Class step.** -/
theorem cls_step {op : valid_ops 2} (hok : Prog.OpOK? op = true) {g : ℕ} {C : Coef}
    (h : Cls g C) : Cls (g + 1) (updC op C) := by
  match g, h with
  | 0, h =>
    subst h
    show ∀ i l, D1 (updC op C0 i l)
    intro i l
    cases op with
    | phaseProduct _ => exact C0_D1 i l
    | negate i0 =>
      dsimp only [updC]
      by_cases hi : i = i0
      · rw [if_pos hi]; simpa using negone_D1.mul (C0_D1 i0 l)
      · rw [if_neg hi]; exact C0_D1 i l
    | shiftL i0 n =>
      dsimp only [updC]
      by_cases hi : i = i0
      · rw [if_pos hi]; exact (pow_D1 n).mul (C0_D1 i0 l)
      · rw [if_neg hi]; exact C0_D1 i l
    | shiftR i0 n =>
      dsimp only [updC]
      by_cases hi : i = i0
      · rw [if_pos hi, div_eq_mul_inv]; exact (C0_D1 i0 l).mul (invpow_D1 n)
      · rw [if_neg hi]; exact C0_D1 i l
    | addScaled d s neg sh =>
      simp only [Prog.OpOK?, decide_eq_true_eq] at hok
      dsimp only [updC]
      by_cases hi : i = d
      · rw [if_pos hi]; exact C0_add hok (sgnpow_D1 neg sh) l
      · rw [if_neg hi]; exact C0_D1 i l
  | 1, h =>
    show ∀ i l, D2 (updC op C i l)
    intro i l
    cases op with
    | phaseProduct _ => exact (h i l).D2
    | negate i0 =>
      dsimp only [updC]
      by_cases hi : i = i0
      · rw [if_pos hi]; exact (by simpa using negone_D1.mul (h i0 l) : D1 _).D2
      · rw [if_neg hi]; exact (h i l).D2
    | shiftL i0 n =>
      dsimp only [updC]
      by_cases hi : i = i0
      · rw [if_pos hi]; exact ((pow_D1 n).mul (h i0 l)).D2
      · rw [if_neg hi]; exact (h i l).D2
    | shiftR i0 n =>
      dsimp only [updC]
      by_cases hi : i = i0
      · rw [if_pos hi, div_eq_mul_inv]; exact ((h i0 l).mul (invpow_D1 n)).D2
      · rw [if_neg hi]; exact (h i l).D2
    | addScaled d s neg sh =>
      dsimp only [updC]
      by_cases hi : i = d
      · rw [if_pos hi]
        exact ⟨C d l, (if neg then -1 else 1) * 2 ^ sh * C s l, h d l,
          (sgnpow_D1 neg sh).mul (h s l), rfl⟩
      · rw [if_neg hi]; exact (h i l).D2
  | n + 2, _ => trivial

/-! ### The gap lemma -/

/-- Reading off a marker: if the anchor has `(1, a)` in register `r` and the current state has
`(1, b)` in register `r'`, then `b − a` is the coefficient on the anchor's other row times
`±det`. -/
lemma diff_eq {S Sa : State 2} {C : Coef} (hR : Rep S Sa C) {r r' : Fin 2} {a b : ℤ}
    (ha : Sa r = row a) (hb : S r' = row b) :
    ∃ o, o ≠ r ∧ (((b - a : ℤ) : ℚ) = C r' o * det2 Sa ∨ ((b - a : ℤ) : ℚ) = -(C r' o * det2 Sa)) := by
  have h0 := hR r' 0
  have h1 := hR r' 1
  rw [hb] at h0 h1
  simp only [row_zero, row_one, Int.cast_one] at h0 h1
  rcases fin2_cases r with rfl | rfl
  · refine ⟨1, by decide, Or.inl ?_⟩
    have ha0 : Sa 0 0 = 1 := by rw [ha]; simp
    have ha1 : Sa 0 1 = a := by rw [ha]; simp
    rw [ha0] at h0; rw [ha1] at h1
    push_cast; unfold det2; push_cast; rw [ha0, ha1]; push_cast
    linear_combination h1 - (a : ℚ) * h0
  · refine ⟨0, by decide, Or.inr ?_⟩
    have ha0 : Sa 1 0 = 1 := by rw [ha]; simp
    have ha1 : Sa 1 1 = a := by rw [ha]; simp
    rw [ha0] at h0; rw [ha1] at h1
    push_cast; unfold det2; push_cast; rw [ha0, ha1]; push_cast
    linear_combination h1 - (a : ℚ) * h0

lemma D1_neg {q : ℚ} (h : D1 q) : D1 (-q) := by simpa using negone_D1.mul h
lemma D2_neg {q : ℚ} (h : D2 q) : D2 (-q) := by simpa using h.mul_D1 negone_D1

/-- **Gap lemma.** -/
theorem gap {S Sa : State 2} {C : Coef} {g : ℕ} (hR : Rep S Sa C) (hC : Cls g C)
    (hdet : DetOK Sa) {r r' : Fin 2} {a b : ℤ} (ha : Sa r = row a) (hb : S r' = row b) :
    (g ≤ 1 → W1 (b - a)) ∧ (g = 2 → W2 (b - a)) := by
  obtain ⟨o, -, ho⟩ := diff_eq hR ha hb
  obtain ⟨s, t, hs, hd⟩ := hdet
  have hdq : (det2 Sa : ℚ) = (s : ℚ) * 2 ^ t := by rw [hd]; push_cast; ring
  -- `b - a = y * (±2^t)` with `y = ±C r' o * s`
  have key : ∃ y : ℚ, (((b - a : ℤ)) : ℚ) = y * 2 ^ t ∧
      (D1 (C r' o) → D1 y) ∧ (D2 (C r' o) → D2 y) := by
    have hsD : D1 (s : ℚ) := Or.inr ⟨s, 0, hs, by simp⟩
    rcases ho with ho | ho
    · exact ⟨C r' o * s, by rw [ho, hdq]; ring, fun h => h.mul hsD, fun h => h.mul_D1 hsD⟩
    · exact ⟨-(C r' o * s), by rw [ho, hdq]; ring, fun h => D1_neg (h.mul hsD),
        fun h => D2_neg (h.mul_D1 hsD)⟩
  obtain ⟨y, hy, h1, h2⟩ := key
  have hpow : ∀ {q : ℚ}, D1 q → D1 (q * 2 ^ t) := fun h => h.mul (pow_D1 t)
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · have hc : D1 (C r' o) := by
      match g, hg, hC with
      | 0, _, hC => rw [hC]; exact C0_D1 _ _
      | 1, _, hC => exact hC _ _
    exact W1_of_D1_int (hpow (h1 hc)) hy
  · subst hg
    exact W2_of_D2_int ((h2 (hC r' o)).mul_D1 (pow_D1 t)) hy

end Pts
