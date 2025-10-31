import FastMultiplication.Tactics
import FastMultiplication.Example_progs

-- /******************************************************************************/
-- /*                 RETURN TO ORIGINAL STATE PROOF.                            */
-- /******************************************************************************/

open Operations

/-- Start state entry (usable by `simp`). -/
@[simp] lemma start_state_entry {k} (i j : Fin k) :
  State.start_state i j = (if j = i then 1 else 0) := by
  simp [State.start_state]


theorem example_prog_2_returns:
  run? example_prog_2 State.start_state = some State.start_state:=by {
    unfold example_prog_2 State.start_state
    simp [ run?_append,
         applyOp?,
         State.addScaledReg, State.negateReg, State.shiftLReg, State.shiftRReg?,
         State.setReg,
         Register.addScaled, Register.negate, Register.shiftL, Register.shiftR?]
    split_ifs with h
    simp
    funext j k
    have h2:=h j
    fin_cases j<;>fin_cases k<;>simp
    simp
    apply h
    intro j
    fin_cases j<;>simp
  }


theorem example_prog_2_phase_converage_2:
  phaseProduct_coverage_check example_prog_2 State.start_state [Point.int 0,Point.inf,Point.int 1,Point.int (-1),Point.int (-2)]:=by {
    unfold example_prog_2
    prove_coverage 3
  }



theorem example_prog_4_phase_coverage :
  phaseProduct_coverage_check example_prog_3 State.start_state [Point.int 0,Point.inf,Point.int 1,Point.int (-1)] := by
    unfold example_prog_3
    prove_coverage 4

theorem example_prog_2_returns_2:
  run? example_prog_2 State.start_state = some State.start_state:=by {
    unfold example_prog_2
    returns_to_original?
  }
