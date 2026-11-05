import Points.SatParse

/-!
# Bits of the translated labels

The table instance of a digraph has the points `lab e − lab e₀` with `e₀ = {0, 1}`, i.e.
`8^a + 8^b − 9` for the edge `{a, b}`, `a < b`. `dBits a b` writes this number in binary
(least significant bit first) explicitly, so that it can be produced in polynomial time.
-/

namespace Pts

open Complexity Mahaney TableGeneration Operations

/-- `8^a + 8^b − 9` in binary, LSB first, for `a < b`. -/
def dBits (a b : ℕ) : List Bool :=
  if a = 0 then (if b = 1 then [] else [false, false, false] ++ List.replicate (3 * b - 3) true)
  else if a = 1 then List.replicate (3 * b) true
  else [true, true, true, false] ++ List.replicate (3 * a - 4) true ++
    List.replicate (3 * b - 3 * a) false ++ [true]

lemma lsbVal_replicate_true (p : ℕ) : lsbVal (List.replicate p true) + 1 = 2 ^ p := by
  induction p with
  | zero => rfl
  | succ p ih => simp [List.replicate_succ, lsbVal, Nat.bit_val, pow_succ]; omega

lemma dBits_val {a b : ℕ} (hab : a < b) : lsbVal (dBits a b) + 9 = 8 ^ a + 8 ^ b := by
  have p8 : ∀ k, (8 : ℕ) ^ k = 2 ^ (3 * k) := fun k => by rw [pow_mul]; norm_num
  unfold dBits
  split_ifs with h0 h1 h1'
  · subst h0; subst h1; rfl
  · subst h0
    have hr := lsbVal_replicate_true (3 * b - 3)
    have e : (2 : ℕ) ^ (3 * b) = 8 * 2 ^ (3 * b - 3) := by
      rw [show 3 * b = 3 + (3 * b - 3) by omega, pow_add]; norm_num
    simp only [List.cons_append, lsbVal, List.nil_append, Nat.bit_val, Bool.toNat_false]
    rw [p8 b, e]; norm_num; omega
  · subst h1'
    have hr := lsbVal_replicate_true (3 * b)
    rw [p8 b]; norm_num; omega
  · have hr1 := lsbVal_replicate_true (3 * a - 4)
    have e1 : (2 : ℕ) ^ (3 * a) = 16 * 2 ^ (3 * a - 4) := by
      rw [show 3 * a = 4 + (3 * a - 4) by omega, pow_add]; norm_num
    have e2 : (2 : ℕ) ^ (3 * b) = 2 ^ (3 * a) * 2 ^ (3 * b - 3 * a) := by
      rw [← pow_add]; congr 1; omega
    rw [lsbVal_append, lsbVal_append, lsbVal_append, lsbVal_replicate_false]
    simp only [List.length_append, List.length_cons, List.length_replicate, List.length_nil]
    simp only [lsbVal, Nat.bit_val, Bool.toNat_true, Bool.toNat_false]
    have e3 : (2 : ℕ) ^ (3 * a + (3 * b - 3 * a)) = 16 * 2 ^ (3 * a - 4) * 2 ^ (3 * b - 3 * a) := by
      rw [pow_add, e1]
    rw [p8, p8, e2, e1, show 0 + 1 + 1 + 1 + 1 + (3 * a - 4) + (3 * b - 3 * a) = 3 * a + (3 * b - 3 * a)
      by omega, e3]
    generalize lsbVal (List.replicate (3 * a - 4) true) = R at hr1 ⊢
    generalize 2 ^ (3 * a - 4) = P at hr1 ⊢
    generalize 2 ^ (3 * b - 3 * a) = Q
    norm_num
    subst hr1; ring

lemma canon_snoc (L : List Bool) : Canon (L ++ [true]) := by right; simp

lemma dBits_canon {a b : ℕ} (hab : a < b) : Canon (dBits a b) := by
  unfold dBits
  split_ifs with h0 h1 h1'
  · left; rfl
  · rw [show 3 * b - 3 = (3 * b - 4) + 1 by omega, List.replicate_succ', ← List.append_assoc]
    exact canon_snoc _
  · rw [show 3 * b = (3 * b - 1) + 1 by omega, List.replicate_succ']
    exact canon_snoc _
  · exact canon_snoc _

lemma lab01 : lab ({0, 1} : Finset ℕ) = 9 := by rw [lab_pair (by norm_num)]; norm_num

/-- The encoded point of a translated label. -/
lemma encPt_dl {a b : ℕ} (hab : a < b) :
    encPt (.int (dl {0, 1} {a, b})) = pair [false, false] (dBits a b) := by
  have hv := dBits_val hab
  have hval : dl {0, 1} {a, b} = ((lsbVal (dBits a b) : ℕ) : ℤ) := by
    unfold dl; rw [lab01, lab_pair (Nat.ne_of_lt hab)]
    have : ((lsbVal (dBits a b) : ℕ) : ℤ) = ((8 ^ a + 8 ^ b : ℕ) : ℤ) - 9 := by
      rw [← hv]; push_cast; ring
    rw [this]; push_cast; ring
  rw [hval, encPt]
  simp only [Int.natAbs_natCast, bits_lsbVal_of_canon (dBits_canon hab)]
  congr 2
  try simp only [decide_eq_false_iff_not, not_lt]
  try positivity

end Pts
