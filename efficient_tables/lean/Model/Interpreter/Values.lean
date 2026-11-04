import Model.Interpreter.Interpreter

/-!
# Value semantics of symbolic rows

Interprets symbolic integer rows as functions of concrete input values. Proves `evalRow` respects addition, scaling, negation and exact division (`evalRow_add`, `evalRow_mul`, `evalRow_neg`, `evalRow_div_exact`), and that a symbolic step refines the scalar step (`rowStep_refines_values`).
-/

namespace Paper.ValueSemantics

theorem evalRow_add {k : Nat} (a b : Fin k → Int) (x : Values k) :
    evalRow (fun j => a j + b j) x = evalRow a x + evalRow b x := by
  simp [evalRow, add_mul, Finset.sum_add_distrib]

theorem evalRow_mul {k : Nat} (a : Fin k → Int) (x : Values k) (c : Int) :
    evalRow (fun j => a j * c) x = evalRow a x * c := by
  simp only [evalRow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem evalRow_neg {k : Nat} (a : Fin k → Int) (x : Values k) :
    evalRow (fun j => -a j) x = -evalRow a x := by
  simp [evalRow]

theorem evalRow_div_exact {k : Nat} (a : Fin k → Int) (x : Values k)
    (c : Int) (hc : c ≠ 0) (h : ∀ j, a j % c = 0) :
    evalRow a x % c = 0 ∧
      evalRow (fun j => a j / c) x = evalRow a x / c := by
  have heq : evalRow a x = evalRow (fun j => a j / c) x * c := by
    rw [← evalRow_mul]
    congr 1
    funext j
    exact (Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero (h j))).symm
  rw [heq]
  constructor
  · simp
  · simp [hc]

theorem evalRows_update {k : Nat} (rows : FullDSL.Rows k) (x : Values k)
    (i : Fin k) (row : Fin k → Int) :
    evalRows (rows.updateRow i row) x = Function.update (evalRows rows x) i (evalRow row x) := by
  funext j
  change evalRow (Function.update rows i row j) x =
    Function.update (evalRows rows x) i (evalRow row x) j
  by_cases h : j = i
  · subst j
    simp
  · simp [h, evalRows]

theorem evalRows_identity {k : Nat} (x : Values k) :
    evalRows (FullDSL.identity k) x = x := by
  funext i
  simp [evalRows, evalRow, FullDSL.identity, Matrix.one_apply]

theorem rowStep_refines_values {k : Nat} (op : FullDSL.Instruction k)
    (rows next : FullDSL.Rows k) (x : Values k)
    (h : FullDSL.rowStep op rows = some next) :
    valueStep op (evalRows rows x) = some (evalRows next x) := by
  cases op with
  | shiftL i n =>
      simp only [FullDSL.rowStep, Option.some.injEq] at h
      subst next
      simp [valueStep, evalRows_update, evalRow_mul, evalRows]
  | shiftR i n =>
      by_cases hg : ∀ j : Fin k, rows i j % (2 : Int) ^ n = 0
      · simp only [FullDSL.rowStep, dif_pos hg, Option.some.injEq] at h
        subst next
        have hd := evalRow_div_exact (rows i) x ((2 : Int)^n) (by positivity) hg
        simp [valueStep, evalRows_update, evalRows, hd.1, hd.2]
      · simp [FullDSL.rowStep, hg] at h
  | negate i =>
      simp only [FullDSL.rowStep, Option.some.injEq] at h
      subst next
      simp [valueStep, evalRows_update, evalRow_neg, evalRows]
  | addScaled dst src negSrc shift =>
      by_cases he : dst = src
      · simp [FullDSL.rowStep, he] at h
      · simp only [FullDSL.rowStep, if_neg he, Option.some.injEq] at h
        subst next
        simp only [valueStep, if_neg he, evalRows_update, evalRow_add]
        have hm := evalRow_mul (rows src) x ((if negSrc then -1 else 1) * (2 : Int)^shift)
        have hm' : evalRow (fun j => ((if negSrc then -1 else 1) * (2 : Int)^shift) * rows src j) x =
            ((if negSrc then -1 else 1) * (2 : Int)^shift) * evalRow (rows src) x := by
          simpa only [mul_comm] using hm
        rw [hm']
        rfl
  | phaseProduct i =>
      simp only [FullDSL.rowStep, Option.some.injEq] at h
      subst next
      rfl

end Paper.ValueSemantics
