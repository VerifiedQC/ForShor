import Mathlib.Tactic

/-!
# Bit strings as numbers (most significant bit first)

`val` reads a bit string as a binary number, MSB first; `bits n a` writes the low `n` bits of `a`.
`LexLe` is the lexicographic order (`false < true`); on strings of equal length it is the
numeric order (`val_le_iff_lexLe`), and it has a bounded-quantifier form (`lexLe_iff_bounded`)
that a polynomial-time test can check.
-/

namespace Mahaney

/-- MSB-first value of a bit string. -/
def val : List Bool → ℕ
  | [] => 0
  | b :: t => b.toNat * 2 ^ t.length + val t

/-- The low `n` bits of `a`, MSB first. -/
def bits : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, a => decide (a / 2 ^ n % 2 = 1) :: bits n a

@[simp] lemma val_nil : val [] = 0 := rfl

@[simp] lemma val_cons (b : Bool) (t : List Bool) : val (b :: t) = b.toNat * 2 ^ t.length + val t :=
  rfl

@[simp] lemma length_bits (n a : ℕ) : (bits n a).length = n := by
  induction n <;> simp [bits, *]

lemma val_lt (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [val_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

lemma val_append_bit (l : List Bool) (b : Bool) : val (l ++ [b]) = 2 * val l + b.toNat := by
  induction l with
  | nil => simp
  | cons c t ih => simp only [List.cons_append, val_cons, ih, List.length_append,
      List.length_singleton, pow_succ]; ring

lemma val_append_zeros (l : List Bool) (m : ℕ) :
    val (l ++ List.replicate m false) = val l * 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ', ← List.append_assoc, val_append_bit, ih]
    simp [pow_succ]; ring

lemma val_bits (n a : ℕ) : val (bits n a) = a % 2 ^ n := by
  induction n with
  | zero => simp [bits, Nat.mod_one]
  | succ n ih =>
    simp only [bits, val_cons, length_bits, ih]
    have h := Nat.mod_mul_right_div_self a (2 ^ n) 2
    have h2 : a % 2 ^ (n + 1) = a % 2 ^ n + 2 ^ n * (a / 2 ^ n % 2) := by
      rw [pow_succ, Nat.mod_mul]
    rw [h2]
    rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ n) with h0 | h1
    · simp [h0]
    · simp [h1]; ring

lemma val_bits_of_lt {n a : ℕ} (h : a < 2 ^ n) : val (bits n a) = a := by
  rw [val_bits, Nat.mod_eq_of_lt h]

lemma val_injective_of_length {l m : List Bool} (hl : l.length = m.length) (h : val l = val m) :
    l = m := by
  induction l generalizing m with
  | nil => cases m <;> simp_all
  | cons b t ih =>
    cases m with
    | nil => simp at hl
    | cons c s =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [val_cons] at h
      have ht := val_lt t
      have hs := val_lt s
      rw [hl] at h ht
      have hbc : b = c := by
        cases b <;> cases c <;> simp at h ⊢ <;> omega
      subst hbc
      have : val t = val s := by omega
      rw [ih hl this]

lemma bits_val (l : List Bool) : bits l.length (val l) = l :=
  val_injective_of_length (by simp) (val_bits_of_lt (val_lt l))

lemma bits_append_bit {i p : ℕ} (b : Bool) (hp : p < 2 ^ i) :
    bits (i + 1) (2 * p + b.toNat) = bits i p ++ [b] := by
  apply val_injective_of_length (by simp)
  rw [val_append_bit, val_bits_of_lt hp, val_bits_of_lt]
  rw [pow_succ]; cases b <;> simp <;> omega

/-- Lexicographic order on bit strings, `false < true`. -/
def LexLe : List Bool → List Bool → Prop
  | [], _ => True
  | _ :: _, [] => False
  | b :: t, c :: s => (b = false ∧ c = true) ∨ (b = c ∧ LexLe t s)

/-- On strings of equal length, the lexicographic order is the numeric order. -/
lemma val_le_iff_lexLe {y a : List Bool} (h : y.length = a.length) :
    val y ≤ val a ↔ LexLe y a := by
  induction y generalizing a with
  | nil => simp [LexLe]
  | cons b t ih =>
    cases a with
    | nil => simp at h
    | cons c s =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [val_cons, LexLe, ← ih h]
      have ht := val_lt t
      have hs := val_lt s
      rw [h] at ht ⊢
      cases b <;> cases c <;> simp <;> omega

/-- The bounded-quantifier form of `LexLe` for strings of equal length: at every position
where the two strings agree on everything before it, the bit of `y` is at most that of `a`. -/
def LexLeB (y a : List Bool) : Prop :=
  ∀ k < y.length, (∀ j < k, y[j]?.getD false = a[j]?.getD false) →
    (y[k]?.getD false = true → a[k]?.getD false = true)

lemma lexLe_iff_bounded {y a : List Bool} (h : y.length = a.length) : LexLe y a ↔ LexLeB y a := by
  induction y generalizing a with
  | nil => simp [LexLe, LexLeB]
  | cons b t ih =>
    cases a with
    | nil => simp at h
    | cons c s =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have key := ih h
      unfold LexLeB at key
      simp only [LexLe, LexLeB, List.length_cons]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, hts⟩)
        · intro k hk hagree hyk
          cases k with
          | zero => simp
          | succ k =>
            have := hagree 0 (by omega); simp at this
        · intro k hk hagree hyk
          cases k with
          | zero => simpa using hyk
          | succ k =>
            simp only [List.getElem?_cons_succ] at hyk ⊢
            exact key.mp hts k (by omega) (fun j hj => by
              simpa using hagree (j + 1) (by omega)) hyk
      · intro H
        have h0 := H 0 (by omega) (fun j hj => absurd hj (by omega))
        simp only [List.getElem?_cons_zero, Option.getD_some] at h0
        by_cases hbc : b = c
        · subst hbc
          right
          refine ⟨rfl, key.mpr fun k hk hagree => ?_⟩
          have := H (k + 1) (by omega) (fun j hj => by
            cases j with
            | zero => simp
            | succ j => simpa using hagree j (by omega))
          simpa using this
        · left
          cases b <;> cases c <;> simp_all

end Mahaney
