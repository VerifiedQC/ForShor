import FastMultiplication.QuantumCircuit.Abstract_circ

------------------------------------------------------------
-- WIRING-LEVEL PHASE-COVERAGE PREDICATE
------------------------------------------------------------

open Operations Compile

section

variable [QubitPrimitives]

@[simp] lemma applyProg_nil {k} (σ : Qubits.State k) :
  Qubits.applyProg ([] : Qubits.QProg k) σ = σ := rfl

@[simp] lemma applyProg_cons {k}
    (op : Qubits.valid_operation k) (p : Qubits.QProg k) (σ : Qubits.State k) :
  Qubits.applyProg (op :: p) σ = Qubits.applyProg p (Qubits.apply op σ) := rfl

/--
This is the qubit analogue of
  `abbrev MatchesAt (k : Nat) := Register k → Point → Bool`
on the classical side, but now the register type is `Qubits.Register_w`. -/
abbrev QMatchesAt (_k : Nat) := Qubits.Register_w → Point → Bool

/--
Qubit analogue of
 `abbrev MatchesAtState (k : Nat) := State k → Fin k → Point → Bool`. -/
abbrev QMatchesAtState (k : Nat) := Qubits.State k → Fin k → Point → Bool

/-- Adapter: lift a register-only wiring matcher to a state-level wiring matcher. -/
def QMatchesAtState.ofRegister {k : Nat} (m : QMatchesAt k) : QMatchesAtState k :=
  fun σ i pt => m (σ i) pt


variable {k : ℕ} [AddScaledNegBackend k] [DecodeBackend k]

inductive QPhaseProductCoverage_compiled (hk : 0 < k) :
    Prog k → Qubits.State k → List Point → Prop where
| nil {σQ} :
    QPhaseProductCoverage_compiled hk [] σQ []

| step_op
    {op : valid_ops k} {ps : Prog k}
    {σQ : Qubits.State k} {pts : List Point}
    (hrest      : QPhaseProductCoverage_compiled hk ps (compileOp σQ op).2 pts) :
    QPhaseProductCoverage_compiled hk (op :: ps) σQ pts

| step_phase
    {i : Fin k} {ps : Prog k}
    {σQ : Qubits.State k} {pts pts' : List Point}
    (hconsume :
      List.eraseFirstMatch?
        (fun pt => matchesAt_pointRow_state hk (decodeState σQ) i pt) pts
      = some pts')
    (hrest : QPhaseProductCoverage_compiled hk ps σQ pts') :
    QPhaseProductCoverage_compiled hk (valid_ops.phaseProduct i :: ps) σQ pts



def PhaseCovMotive
    (hk : 0 < k)
    (p : Prog k) (σC : State k) (pts : List Point) : Prop :=
  ∀ σQ : Qubits.State k,
    decodeState σQ = σC →
    QPhaseProductCoverage_compiled (k := k) hk p σQ pts


lemma phaseCoverage_preserved_by_compilation_stronger
    (hk : 0 < k)
    {p : Prog k} {σC : State k} {pts : List Point}
    (hClass : PhaseProductCoverage hk p σC pts) :
  PhaseCovMotive (k := k) hk p σC pts := by
  -- Induction on the classical coverage derivation
  induction hClass with
  | nil =>
      intro σQ hdec
      exact QPhaseProductCoverage_compiled.nil

  | step_op hstep hrest IH =>
      rename_i op ps σC₀ τ pts2
      intro σQ hdec
      cases hcomp : compileOp σQ op with
      | mk prog1 σQ' =>
        have hdecode' :
          some (decodeState σQ') = run? [op] σC₀ := by
            have := compileOp_respects_decode (k := k) σQ op
            simpa [hcomp, hdec] using this

        have hrun : run? [op] σC₀ = some τ := by
          simp [run?, hstep]

        have hDec1 : decodeState σQ' = τ := by
          have hEq : some (decodeState σQ') = some τ := by
            simpa [hrun] using hdecode'
          exact Option.some.inj hEq

        have hTailQ' :
          QPhaseProductCoverage_compiled (k := k) hk ps σQ' pts2 :=
          IH σQ' hDec1

        have hState : (compileOp σQ op).2 = σQ' := by
          simp [hcomp]

        have hTailQ :
          QPhaseProductCoverage_compiled (k := k) hk ps (compileOp σQ op).2 pts2 := by
          simpa [hState] using hTailQ'

        apply QPhaseProductCoverage_compiled.step_op (k := k) (hk := hk)
        apply hTailQ

  | step_phase hconsume hrest IH =>
      rename_i i ps σC pts pts'
      intro σQ hdec
      have hconsume' :
        List.eraseFirstMatch?
          (fun pt ↦ matchesAt_pointRow_state hk (decodeState σQ) i pt)
          pts
        = some pts' := by
        simpa [hdec] using hconsume

      have hrest_compiled :
        QPhaseProductCoverage_compiled (k := k) hk ps σQ pts' :=
        IH σQ hdec

      exact QPhaseProductCoverage_compiled.step_phase
        (k := k) (hk := hk) hconsume' hrest_compiled


theorem phaseCoverage_preserved_by_compilation
    (hk : 0 < k)
    (p : Prog k) (σQ₀ : Qubits.State k) (pts : List Point)
    (hp : PhaseProductCoverage hk p (decodeState σQ₀) pts) :
  QPhaseProductCoverage_compiled (k := k) hk p σQ₀ pts := by
  have h := phaseCoverage_preserved_by_compilation_stronger
              (k := k) hk hp
  unfold PhaseCovMotive at h
  exact h σQ₀ rfl

































































inductive QPhaseProductCoverageM {k : ℕ} (M : QMatchesAtState k) :
    Qubits.QProg k → Qubits.State k → List Operations.Point → Prop
| nil {σ : Qubits.State k} :
    QPhaseProductCoverageM M [] σ []
| step_op {op : Qubits.valid_operation k} {ps : Qubits.QProg k}
          {σ τ : Qubits.State k} {pts : List Operations.Point}
    (hstep : τ = Qubits.apply op σ)
    (hrest : QPhaseProductCoverageM M ps τ pts) :
    QPhaseProductCoverageM M (op :: ps) σ pts
| step_phase {i : Fin k} {ps : Qubits.QProg k}
             {σ : Qubits.State k} {pts pts' : List Operations.Point}
    (hconsume :
      List.eraseFirstMatch? (fun pt => M σ i pt) pts = some pts')
    (hrest : QPhaseProductCoverageM M ps σ pts') :
    QPhaseProductCoverageM M (Qubits.valid_operation.phaseProduct i :: ps) σ pts

















































































/--
Quibit-level phase coverage: now the inductive tracks both
the integer-level program `p` and its compiled qubit-level program `q`.
-/
inductive QPhaseProductCoverage_qubit (hk : 0 < k) :
    Prog k → Qubits.QProg k → Qubits.State k → List Point → Prop where
| nil {σQ} :
    QPhaseProductCoverage_qubit hk [] [] σQ []

| step_op
    {op : valid_ops k} {ps : Prog k}
    {prog1 prog2 : Qubits.QProg k}
    {σQ σQ' : Qubits.State k} {pts : List Point}
    (hcompile : compileOp σQ op = (prog1, σQ'))
    (hrest    : QPhaseProductCoverage_qubit hk ps prog2 σQ' pts) :
    QPhaseProductCoverage_qubit hk (op :: ps) (prog1 ++ prog2) σQ pts

| step_phase
    {i : Fin k} {ps : Prog k}
    {qprog : Qubits.QProg k}
    {σQ : Qubits.State k} {pts pts' : List Point}
    (hconsume :
      List.eraseFirstMatch?
        (fun pt => matchesAt_pointRow_state hk (decodeState σQ) i pt) pts
      = some pts')
    (hrest : QPhaseProductCoverage_qubit hk ps qprog σQ pts') :
    -- on the qubit side we *know* the next compiled gate is a phaseProduct
    QPhaseProductCoverage_qubit hk
      (valid_ops.phaseProduct i :: ps)
      (Qubits.valid_operation.phaseProduct i :: qprog)
      σQ pts



/-
Adapter motive: given classical coverage for `(p, σC, pts)`, we want to
prove that for every wiring-level state `σQ` decoding to `σC`, the
compiled qubit program `compile_Prog σQ p` satisfies qubit coverage.
-/
def PhaseCovMotive_qubit
    (hk : 0 < k)
    (p : Prog k) (σC : State k) (pts : List Point) : Prop :=
  ∀ σQ : Qubits.State k,
    decodeState σQ = σC →
    QPhaseProductCoverage_qubit (k := k) hk p (compile_Prog σQ p) σQ pts

/-
## Main stronger lemma: classical → qubit coverage, for all σQ decoding to σC
-/
lemma phaseCoverage_preserved_by_compilation_qubit_stronger
    (hk : 0 < k)
    {p : Prog k} {σC : State k} {pts : List Point}
    (hClass : PhaseProductCoverage hk p σC pts) :
  PhaseCovMotive_qubit (k := k) hk p σC pts := by
  -- Induction on the classical coverage derivation
  induction hClass with
  | nil =>
      intro σQ hdec
      have hprog : compile_Prog σQ ([] : Prog k) = ([] : Qubits.QProg k) :=
        compile_Prog_nil (k := k) σQ
      simpa [PhaseCovMotive_qubit, hprog] using
        (QPhaseProductCoverage_qubit.nil (k := k) (hk := hk) (σQ := σQ))

  | step_op hstep hrest IH =>
      rename_i op ps σC₀ τ pts
      intro σQ hdec
      cases hcomp : compileOp σQ op with
      | mk prog1 σQ' =>
        have hdecode' :
          some (decodeState σQ') = run? [op] σC₀ := by
            have := compileOp_respects_decode (k := k) σQ op
            simpa [hcomp, hdec] using this

        have hrun : run? [op] σC₀ = some τ := by
          simp [run?, hstep]

        -- So decodeState σQ' = τ
        have hDec1 : decodeState σQ' = τ := by
          have hEq : some (decodeState σQ') = some τ := by
            simpa [hrun] using hdecode'
          exact Option.some.inj hEq

        -- Apply IH at σQ'
        have hTailQ' :
          QPhaseProductCoverage_qubit (k := k) hk ps (compile_Prog σQ' ps) σQ' pts :=
          IH σQ' hDec1

        -- Relate `compile_Prog` on `op :: ps` to `prog1 ++ compile_Prog σQ' ps`
        have hprog_eq :=
          compile_Prog_cons (k := k) (σQ := σQ) (op := op) (ps := ps)
        have hprog_eq' :
          compile_Prog σQ (op :: ps)
            = prog1 ++ compile_Prog σQ' ps := by
          simpa [hcomp] using hprog_eq

        -- Rewrite the qubit-program index and apply step_op
        refine hprog_eq' ▸ ?_
        exact QPhaseProductCoverage_qubit.step_op (k := k) (hk := hk)
          (op := op) (ps := ps)
          (σQ := σQ) (σQ' := σQ') (pts := pts)
          (prog1 := prog1) (prog2 := compile_Prog σQ' ps)
          (hcompile := hcomp)
          (hrest := hTailQ')

  | step_phase hconsume hrest IH =>
      rename_i i ps σC pts pts'
      intro σQ hdec

      have hconsume' :
        List.eraseFirstMatch?
          (fun pt ↦ matchesAt_pointRow_state hk (decodeState σQ) i pt)
          pts
        = some pts' := by
        simpa [hdec] using hconsume

      have hrest_compiled :
        QPhaseProductCoverage_qubit (k := k) hk ps (compile_Prog σQ ps) σQ pts' :=
        IH σQ hdec

      have hprog_eq :=
        compile_Prog_cons (k := k) (σQ := σQ)
          (op := valid_ops.phaseProduct i) (ps := ps)

      have hprog_eq' :
        compile_Prog σQ (valid_ops.phaseProduct i :: ps)
          = Qubits.valid_operation.phaseProduct i :: compile_Prog σQ ps := by
        simp [compile_Prog_cons, Compile.compileOp, Qubits.apply] at hprog_eq
        aesop

      refine hprog_eq' ▸ ?_
      exact QPhaseProductCoverage_qubit.step_phase (k := k) (hk := hk)
        (i := i) (ps := ps)
        (qprog := compile_Prog σQ ps)
        (σQ := σQ) (pts := pts) (pts' := pts')
        hconsume'
        hrest_compiled


theorem phaseCoverage_preserved_to_qubit_prog
    {k : ℕ} [AddScaledNegBackend k] [DecodeBackend k]
    (hk : 0 < k)
    (p : Prog k) (σQ₀ : Qubits.State k) (pts : List Point)
    (hp : PhaseProductCoverage hk p (decodeState σQ₀) pts) :
  QPhaseProductCoverage_qubit hk p (compile_Prog σQ₀ p) σQ₀ pts :=
by
  have:=phaseCoverage_preserved_by_compilation_qubit_stronger hk hp
  apply this
  rfl
