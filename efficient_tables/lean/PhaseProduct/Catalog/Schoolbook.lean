import PhaseProduct.Catalog.ValuePhase

/-!
# Schoolbook leaf phase

Shows the schoolbook leaf computes the phase of a product: the signed digits of
a bitvector have the right length and sum (`signedDigits_length`,
`signedDigits_sum`), the cell count is as stated (`schoolbookCells_length`),
and the phase is correct (`schoolbookPhase_correct`, `schoolbookLeaf_correct`).
-/

open scoped BigOperators
namespace Paper.PPEndToEnd

theorem sum_map_double (l : List ℚ) : (l.map (fun q => 2*q)).sum = 2*l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, mul_add]

theorem signedDigits_length {W : Nat} (a : BitVec W) : (signedDigits W a).length = W := by
  induction W with
  | zero => simp [signedDigits]
  | succ w ih =>
      by_cases h : w = 0
      · subst w; simp [signedDigits]
      · simp [signedDigits, h, ih]

theorem signedDigits_sum {W : Nat} (a : BitVec W) : (signedDigits W a).sum = (a.toInt : ℚ) := by
  induction W with
  | zero => simp [signedDigits, BitVec.eq_nil a]
  | succ w ih =>
      have hh := congrArg (fun x : Int => (x : ℚ))
        (BitVec.toInt_concat (a.extractLsb' 1 w) (a.getLsb 0))
      rw [BitVec.concat_extractLsb'_getLsb] at hh
      by_cases h : w = 0
      · simp [signedDigits, h] at hh ⊢
        exact hh.symm
      · simp only [h, ↓reduceIte, Int.cast_add, Int.cast_mul, Int.cast_ofNat] at hh
        simp only [signedDigits, h, ↓reduceIte, List.sum_cons, sum_map_double, ih]
        rw [hh]
        ring

theorem sum_mul_cells (a c : List ℚ) :
    (a.flatMap (fun x => c.map (fun z => x*z))).sum = a.sum*c.sum := by
  have hm : ∀ x : ℚ, (c.map (fun z => x*z)).sum = x*c.sum := by
    intro x
    induction c with
    | nil => simp
    | cons z zs ih => simp [ih, mul_add]
  induction a with
  | nil => simp
  | cons x xs ih => simp [hm, ih, add_mul]

theorem phaseCharacter_list_sum (theta : ℝ) (l : List ℚ) :
    (l.map (Paper.ValuePhase.phaseCharacter theta)).prod =
      Paper.ValuePhase.phaseCharacter theta l.sum := by
  induction l with
  | nil => simp [Paper.ValuePhase.phaseCharacter_zero]
  | cons x xs ih => simp [ih, Paper.ValuePhase.phaseCharacter_add]

theorem schoolbookPhase_correct {W : Nat} (theta : ℝ) (a c : BitVec W) :
    schoolbookPhase theta a c = Paper.ValuePhase.phaseCharacter theta
      ((a.toInt : ℚ)*(c.toInt : ℚ)) := by
  rw [schoolbookPhase, phaseCharacter_list_sum, schoolbookCells, sum_mul_cells,
    signedDigits_sum, signedDigits_sum]

theorem schoolbookCells_length {W : Nat} (a c : BitVec W) :
    (schoolbookCells a c).length = W^2 := by
  unfold schoolbookCells
  have hh : ∀ l : List ℚ,
      (l.flatMap (fun x => (signedDigits W c).map (fun z => x*z))).length = l.length * W := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih => simp [ih, signedDigits_length, Nat.add_mul, Nat.add_comm]
  rw [hh, signedDigits_length, pow_two]

theorem schoolbookLeaf_correct (W : Nat) (theta : ℝ) (a c : Int)
    (ha : (BitVec.ofInt W a).toInt = a) (hc : (BitVec.ofInt W c).toInt = c) :
    schoolbookLeaf W theta a c = some
      (Paper.ValuePhase.phaseCharacter theta ((a:ℚ)*(c:ℚ))) := by
  simp [schoolbookLeaf, ha, hc, schoolbookPhase_correct]

end Paper.PPEndToEnd
