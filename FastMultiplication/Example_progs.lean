import FastMultiplication.Language
-- /******************************************************************************/
-- /*                 A SAMPLE PROGRAM & ITS COVERAGE PROOF                      */
-- /******************************************************************************/
open Operations

def example_prog_1:Prog 3:=
  [valid_ops.phaseProduct 0] ;;
  [valid_ops.phaseProduct 2] ;;
  (1 +:= 0 << 0) ;;
  1+:= 2 << 0 ;;
  [valid_ops.phaseProduct 1]


theorem example_prog_1_phase_converage:
  phaseProduct_coverage_check example_prog_1 State.start_state [Point.int 0,Point.inf,Point.int 1]:=by {
    unfold phaseProduct_coverage_check phaseCoverageFrom? phaseCoverageFrom?.loop example_prog_1 List.eraseFirstMatch? matchesAt_pointRow regEqExpected State.start_state expectedRow List.eraseFirstMatch?
    simp
    have :(∀ (x : Fin 3), x ∈ List.finRange 3 → ((if x = 0 then (1:ℤ) else 0) = 0 ^ x.val))=true:=by {
      simp
      intro x
      split_ifs with h
      simp[h]
      fin_cases x<;>simp_all
    }
    split_ifs with h
    simp [Fin.isValue]
    rfl
    · simp at h
      simp at this
      exfalso
      rcases h with ⟨x, hxne⟩
      simp_all
    · simp_all
  }


/-- Program for the k=3 (regs 0,1,2). -/
def example_prog_2 : Prog 3 :=
  (1 +:= 2 << 0) ;;
  (1 +:= 0 << 0) ;;
  -- Product on all registers
  [valid_ops.phaseProduct 0] ;;
  [valid_ops.phaseProduct 1] ;;
  [valid_ops.phaseProduct 2] ;;

  (neg 1) ;;
  (1 +:= 0 << 0) ;;
  (1 +:= 2 << 1) ;;
  (0 +:= 1 << 0) ;;
  (1 +:= 0 << 0) ;;
  (1 +:= 2 << 1) ;;
  -- Product on regs. 1 and 0
  [valid_ops.phaseProduct 1] ;;
  [valid_ops.phaseProduct 0] ;;

  (neg 1) ;;
  (1 +:= 2 << 1) ;;
  (0 <<s= 1) ;; (0 +:= 1 << 0) ;;
  (1 +:= 0 << 0) ;;
  (1 +:= 2 << 1) ;;
  (1 >>s= 1)

def example_prog_3 : Prog 4 :=
  (1 +:= 3 << 0) ;;
  (1 +:= 2 << 0) ;;
  (1 +:= 0 << 0) ;;
  -- Product on all registers
  [valid_ops.phaseProduct 0] ;;
  [valid_ops.phaseProduct 1] ;;
  [valid_ops.phaseProduct 3] ;;

  (1 -:= 0 << 0) ;;
  (1 -:= 2 << 0) ;;
  (1 -:= 3 << 0) ;;
  (0 -:= 1 << 0) ;;
  (0 +:= 2 << 0) ;;
  (0 -:= 3 << 0) ;;
  [valid_ops.phaseProduct 0] ;;
  (0 +:= 3 << 0) ;;
  (0 -:= 2 << 0) ;;
  (0 +:= 1 << 0)



lemma x_fin_checker(k:ℕ)(hk:k>0): (∀ (x : Fin k), x ∈ List.finRange k → ((if x = (Fin.mk 0 (by simp[hk])) then (1:ℤ) else 0) = 0 ^ x.val))=true:=by {
  simp
  intro x
  split_ifs with h
  simp[h]
  have hx0 : (x : ℕ) ≠ 0 := by
    intro hx
    apply h
    apply Fin.ext
    simpa using hx
  obtain ⟨n, h⟩ := Nat.exists_eq_succ_of_ne_zero hx0
  simp[h]
}

theorem example_prog_2_phase_converage:
  phaseProduct_coverage_check example_prog_2 State.start_state [Point.int 0,Point.inf,Point.int 1,Point.int (-1),Point.int (-2)]:=by {
    simp[phaseProduct_coverage_check,phaseCoverageFrom?,phaseCoverageFrom?.loop,example_prog_2,List.eraseFirstMatch?,matchesAt_pointRow,regEqExpected,State.start_state,expectedRow,List.eraseFirstMatch?,Prog.ADD,applyOp?,phaseCoverageFrom?.loop,State.addScaledReg,State.setReg, Register.addScaled]
    have := x_fin_checker 3 (by simp)
    split_ifs with h
    rfl
    all_goals simp_all
  }
