import TableGeneration.Language

/-!
# The submission contract against the companion's obligations

`ProgConsumesPtsSafe` is stated here with Bool-valued fields
(`progConsumesPts? ... = true`) where the companion states the same obligations
with Prop-valued ones. That is deliberate: the Bool form is what lets a
submitter discharge the contract by `decide` -- kernel-checked, with no Mathlib
and no `native_decide` -- which is why `#print axioms` on the two submission
theorems reports `propext` alone.

It also bundles into one structure what the companion's `ShorLoweringSetup`
asks for as two obligations:

* `consumes` and `safe_add` correspond to the companion's
  `ProgConsumesPtsSafe`, i.e. its `ProgConsumesPts` and `SafeProg`;
* `returns_start` corresponds to its separate `returns` obligation,
  `run? ops State.start_state = some State.start_state`, discharged upstream by
  `genOpsWithProduct_returns_to_original`.

A restatement is only as good as the proof that it says the same thing. This
file discharges that for the round-trip obligation: `returnsToStartCheck_iff`
shows the Bool check holds exactly when the companion's equation does. The
submission contract instantiates it at `State.start_state`, so the two
obligations coincide there.

## What is not proved here

`progConsumesPts? = true → ProgConsumesPts` and `safeProg? = true → SafeProg`.
Those need the companion's Prop-valued definitions integrated and a proof that
follows the recursion through the program. Soundness is the direction that
matters -- completeness would only govern whether a valid policy could be
wrongly rejected -- and it remains the one formal gap between this contract and
the companion's.
-/

namespace TableGeneration

open Operations

/-- `statesEqual` decides equality of states: it compares every register at
every index, and `State k` is a function, so agreement everywhere is equality. -/
theorem statesEqual_iff {k : Nat} (a b : State k) :
    statesEqual a b = true ↔ a = b := by
  constructor
  · intro h
    have h' := List.all_eq_true.mp h
    funext i j
    have hi := h' i (List.mem_finRange i)
    have hj := List.all_eq_true.mp hi j (List.mem_finRange j)
    exact of_decide_eq_true hj
  · rintro rfl
    simp [statesEqual]

/-- The contract's round-trip field says exactly what the companion's `returns`
obligation says: running the program from `sigma` succeeds and lands back on
`sigma`.

At `sigma = State.start_state`, which is where `GeneratorPolicy.generate_safe`
instantiates it, the right-hand side is literally the companion's
`run? ops State.start_state = some State.start_state`. -/
theorem returnsToStartCheck_iff {k : Nat} (ops : Prog k) (sigma : State k) :
    returnsToStartCheck ops sigma = true ↔ run? ops sigma = some sigma := by
  unfold returnsToStartCheck
  cases hrun : run? ops sigma with
  | none => simp
  | some sigma' =>
      constructor
      · intro h
        rw [(statesEqual_iff sigma' sigma).mp h]
      · intro h
        have hEq : sigma' = sigma := by
          simp only [Option.some.injEq] at h
          exact h
        rw [hEq]
        exact (statesEqual_iff sigma sigma).mpr rfl

/-- The round-trip obligation a submission actually carries, in the companion's
own form. -/
theorem returns_to_start_of_contract {k : Nat} {hk : k > 0}
    {ops : Prog k} {pts : List Point}
    (h : ProgConsumesPtsSafe hk State.start_state ops pts) :
    run? ops State.start_state = some State.start_state :=
  (returnsToStartCheck_iff ops State.start_state).mp h.returns_start

end TableGeneration
