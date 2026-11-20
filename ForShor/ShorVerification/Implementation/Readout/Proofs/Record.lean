import ForShor.ShorVerification.Implementation.Readout.Statement

/-!
# Readout: reading a record as an integer, and the feed-forward angle

Facts about `readoutOfRecord` (little-endian reading of a measurement record)
and its link to `ffAngle`:

* `readoutOfRecord_testBit`: slot `i` is bit `i`;
* `readoutOfRecord_append`: appending outcome `b` to a record of length `k`
  adds `b · 2^k`;
* `readoutOfRecord_lt`: a record of length `k` reads a number `< 2^k`;
* `readoutOfRecord_inj`, `exists_record_of_lt`: on records of length `m` the
  reading is a bijection onto `[0, 2^m)`;
* `ffAngle_eq_neg_readout_div`: on a record of length `j`,
  `ffAngle j rec = -(readoutOfRecord rec) / 2^j`.
-/

namespace Shor
namespace Readout

/-- The `0/1` value of an outcome. -/
def bitVal (b : Bool) : ℕ := if b then 1 else 0

theorem readoutOfRecord_cons (b : Bool) (rest : Record) :
    readoutOfRecord (b :: rest) = bitVal b + 2 * readoutOfRecord rest := rfl

/-- Slot `i` of the record is bit `i` of `readoutOfRecord` (missing slots are `0`). -/
theorem readoutOfRecord_testBit (rec : Record) (i : ℕ) :
    (readoutOfRecord rec).testBit i = rec.getD i false := by
  induction rec generalizing i with
  | nil => simp [readoutOfRecord]
  | cons b rest ih =>
    rw [readoutOfRecord_cons]
    cases i with
    | zero =>
      rw [Nat.testBit_zero]
      cases b <;> simp [bitVal]
    | succ i =>
      rw [Nat.testBit_succ, List.getD_cons_succ, ← ih i]
      congr 1
      cases b <;> simp [bitVal]; omega

/-- Appending outcome `b` to a record adds `b · 2^(length)`. -/
theorem readoutOfRecord_append (r : Record) (b : Bool) :
    readoutOfRecord (r ++ [b]) = readoutOfRecord r + bitVal b * 2 ^ r.length := by
  induction r with
  | nil => simp [readoutOfRecord, bitVal]
  | cons b' rest ih =>
    rw [List.cons_append, readoutOfRecord_cons, readoutOfRecord_cons, ih, List.length_cons,
      pow_succ]
    ring

/-- A record of length `k` reads a number below `2^k`. -/
theorem readoutOfRecord_lt (r : Record) : readoutOfRecord r < 2 ^ r.length := by
  induction r with
  | nil => simp [readoutOfRecord]
  | cons b rest ih =>
    rw [readoutOfRecord_cons, List.length_cons, pow_succ]
    have : bitVal b ≤ 1 := by cases b <;> simp [bitVal]
    omega

/-- Two records of the same length with the same reading are equal. -/
theorem readoutOfRecord_inj {r r' : Record} (hl : r.length = r'.length)
    (h : readoutOfRecord r = readoutOfRecord r') : r = r' := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := readoutOfRecord_testBit r i
  rw [h, readoutOfRecord_testBit, List.getD_eq_getElem _ _ h2,
    List.getD_eq_getElem _ _ h1] at this
  exact this.symm

/-- Every `o < 2^m` is the reading of a record of length `m`. -/
theorem exists_record_of_lt (m o : ℕ) (ho : o < 2 ^ m) :
    ∃ r : Record, r.length = m ∧ readoutOfRecord r = o := by
  refine ⟨List.ofFn (fun i : Fin m => o.testBit i), by simp, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro i
  rw [readoutOfRecord_testBit]
  by_cases hi : i < m
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using hi)]
    exact (Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

/-- `readoutOfRecord` as a sum of weighted slots (in `ℚ`). -/
theorem readoutOfRecord_eq_sum (r : Record) :
    (readoutOfRecord r : ℚ)
      = ∑ i ∈ Finset.range r.length, (if r.getD i false then (1 : ℚ) else 0) * 2 ^ i := by
  induction r with
  | nil => simp [readoutOfRecord]
  | cons b rest ih =>
    rw [readoutOfRecord_cons, List.length_cons, Finset.sum_range_succ']
    push_cast
    rw [ih, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_succ, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · cases b <;> simp [bitVal]

/-- **The feed-forward angle in closed form.** On a record of length `j`, round
`j`'s angle (units of `π`) is minus the record's little-endian reading over
`2^j`: `ffAngle j rec = -(readoutOfRecord rec / 2^j)`. -/
theorem ffAngle_eq_neg_readout_div (j : ℕ) (rec : Record) (h : rec.length = j) :
    ffAngle j rec = -((readoutOfRecord rec : ℚ) / 2 ^ j) := by
  rw [ffAngle, readoutOfRecord_eq_sum, h, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [pow_sub₀ _ two_ne_zero hi.le]
  split_ifs <;> field_simp

end Readout
end Shor
