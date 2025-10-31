import FastMultiplication.Example_progs
import FastMultiplication.Basic_lemmas
-- /******************************************************************************/
-- /*                 TACTIC FOR VERIFYING PHASEPRODUCT COVERGE                  */
-- /******************************************************************************/

open Lean Meta Elab Tactic
open Operations

-- Custom tactic
elab "prove_coverage" n:num : tactic => do
  let nVal := n.getNat

  -- We will build the sequence of tactics as syntax
  let tacstx ← `(tactic|
    {
      simp [phaseProduct_coverage_check, phaseCoverageFrom?, phaseCoverageFrom?.loop, List.eraseFirstMatch?, matchesAt_pointRow, regEqExpected,
            State.start_state, expectedRow, List.eraseFirstMatch?, Prog.ADD,
            applyOp?, phaseCoverageFrom?.loop, State.addScaledReg, State.setReg,
            Register.addScaled]

      -- Use the parsed integer `n` here
      have := x_fin_checker $(quote nVal) (by simp)

      split_ifs with h
      rfl
      all_goals simp_all
    }
  )

  -- Run the tactic sequence using evalTactic
  -- This evaluates the tactic block in the current context
  evalTactic tacstx


-- /******************************************************************************/
-- /*               TACTIC TO PROVE RETURN TO ORIGINAL STATE.                    */
-- /******************************************************************************/

elab "returns_to_original?": tactic => do


  -- We will build the sequence of tactics as syntax
  let tacstx ← `(tactic|
    {
      simp [ run?_append,
         State.start_state,
         applyOp?,
         State.addScaledReg, State.negateReg, State.shiftLReg, State.shiftRReg?,
         State.setReg,
         Register.addScaled, Register.negate, Register.shiftL, Register.shiftR?]
      try (unfold State.setReg)
      try (funext j k)
      split_ifs with h
      simp
      try (funext j k)
      have h2:=h j
      fin_cases j<;>fin_cases k<;>simp
      simp
      apply h
      intro j
      fin_cases j<;>simp
    }
  )

  -- Run the tactic sequence using evalTactic
  -- This evaluates the tactic block in the current context
  evalTactic tacstx
