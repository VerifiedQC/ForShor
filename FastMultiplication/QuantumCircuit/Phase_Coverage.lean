import FastMultiplication.QuantumCircuit.Abstract_circ

------------------------------------------------------------
-- WIRING-LEVEL PHASE-COVERAGE PREDICATE
------------------------------------------------------------

open Operations Compile

@[simp] lemma applyProg_nil {k} (σ : Qubits.State k) :
  Qubits.applyProg ([] : Qubits.QProg k) σ = σ := rfl

@[simp] lemma applyProg_cons {k} (op : Qubits.valid_operation k) (p : Qubits.QProg k) (σ : Qubits.State k) :
  Qubits.applyProg (op :: p) σ = Qubits.applyProg p (Qubits.apply op σ) := rfl
/-- Wiring-level "matches at point" for a *single register*.

This is the qubit analogue of

  abbrev MatchesAt (k : Nat) := Register k → Point → Bool

on the classical side, but now the register type is `Qubits.Register`. -/
abbrev QMatchesAt (k : Nat) := Qubits.Register_w → Point → Bool

/-- Wiring-level "matches at point" that can see the *whole state* and an index.

Quibit analogue of
 abbrev MatchesAtState (k : Nat) := State k → Fin k → Point → Bool. -/
abbrev QMatchesAtState (k : Nat) := Qubits.State k → Fin k → Point → Bool


/-- Adapter: lift a register-only wiring matcher to a state-level wiring matcher. -/
def QMatchesAtState.ofRegister {k : Nat} (m : QMatchesAt k) : QMatchesAtState k :=
  fun σ i pt => m (σ i) pt

/-- Inductive wiring-level phase-product coverage, mirroring `PhaseProductCoverageM`
    but over `Qubits.State` and `Qubits.valid_operation`.

    Intuition:
    * `nil`      : empty program covers an empty point list.
    * `step_op`  : non-`phaseProduct` op just steps the state via `Qubits.apply`.
    * `step_phase` : when we hit a `phaseProduct i`, we must consume exactly one
                     point from the "todo" list for which `M σ i pt` holds. -/
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

/-- Wiring-level phase-coverage predicate using a given wiring matcher `M`. -/
def QPhaseProductCoverage {k : ℕ} (M : QMatchesAtState k) :
    Qubits.QProg k → Qubits.State k → List Operations.Point → Prop :=
  QPhaseProductCoverageM (k := k) M


/-- Wiring-level matcher that first decodes a qubit state to a classical state
    and then uses the classical `matchesAt_pointRow_state` row-matcher.

    This is the natural bridge for correctness theorems: it says
    "the qubit register at index `i` matches the point-row *when decoded*". -/
noncomputable def Q_matchesAt_pointRow_state {k : Nat} (hk : 0 < k) : QMatchesAtState k :=
  fun σQ i pt =>
    matchesAt_pointRow_state (k := k) hk (decodeState σQ) i pt

/-- Wiring-level phase coverage using the decoded Vandermonde row matcher. -/
def QPhaseProductCoverage_decoded {k : ℕ} (hk : 0 < k) :
    Qubits.QProg k → Qubits.State k → List Operations.Point → Prop :=
  QPhaseProductCoverage (k := k) (Q_matchesAt_pointRow_state (k := k) hk)


open Compile
open PhaseProductCoverage

/-- **Phase coverage is preserved by compilation, under decoding.** -/

def PhaseCovMotive
    {k : ℕ} (hk : 0 < k)
    (p : Prog k) (σC : State k) (pts : List Point) : Prop :=
  ∀ σQ : Qubits.State k,
    decodeState σQ = σC →
    QPhaseProductCoverage_decoded hk (compileProgramAux σQ p).1 σQ pts

lemma QPhaseProductCoverage_prepend_prog
    {k : ℕ} {M : QMatchesAtState k}
    (p₁ p₂ : Qubits.QProg k) (σ₀ : Qubits.State k) (pts : List Point)
    (hTail : QPhaseProductCoverageM M p₂ (Qubits.applyProg p₁ σ₀) pts) :
    QPhaseProductCoverageM M (p₁ ++ p₂) σ₀ pts :=
by
  induction p₁ generalizing σ₀ with
  | nil =>
      -- p₁ = []
      -- then applyProg p₁ σ₀ = σ₀ and [] ++ p₂ = p₂
      simpa [Qubits.applyProg] using hTail

  | cons op p₁ ih =>
      -- p₁ = op :: p₁
      -- we know: hTail : QPhaseProductCoverageM M p₂ (applyProg (op :: p₁) σ₀) pts
      have hTail' :
          QPhaseProductCoverageM M p₂
            (Qubits.applyProg p₁ (Qubits.apply op σ₀)) pts := by
        -- unfold applyProg (op :: p₁) σ₀ = applyProg p₁ (apply op σ₀)
        simpa [Qubits.applyProg] using hTail

      -- Use IH to prepend p₁ in front of p₂, starting at (apply op σ₀)
      have hRest :
          QPhaseProductCoverageM M (p₁ ++ p₂)
            (Qubits.apply op σ₀) pts := by
        aesop

      -- Now build one more `step_op` for the head `op`
      apply QPhaseProductCoverageM.step_op
        (M := M)
        (op := op)
        (ps := p₁ ++ p₂)
        (σ := σ₀)
        (τ := Qubits.apply op σ₀)
        (pts := pts)
        (by rfl)    -- hstep : apply op σ₀ = apply op σ₀
        hRest



lemma phaseCov_stepOp_case
    {k : ℕ} (hk : 0 < k)
    (op : valid_ops k)(ps : Prog k)
    (σC τ : State k)(pts : List Point)
    (hstep : applyOp? σC op = some τ)
    (hrest : PhaseProductCoverage hk ps τ pts)
    (IH : PhaseCovMotive hk ps τ pts) :
    PhaseCovMotive hk (op :: ps) σC pts := by
  -- unfold the motive
  intro σQ₀ hdec
  classical

  ----------------------------------------------------------------
  -- 1. Compile op at the qubit level and name the pieces
  ----------------------------------------------------------------
  -- Create prog1 and σQ₁ *with an equality*:
  cases h1 : compileOp σQ₀ op with
  | mk prog1 σQ₁ =>
    have hDec1 : decodeState σQ₁ = τ := by
      -- sketch:
      --   some (decodeState σQ₁) = run? [op] (decodeState σQ₀)
      --   = applyOp? (decodeState σQ₀) op
      --   = some τ
      -- so decodeState σQ₁ = τ
      have hRun :=
        compileOp_respects_decode (σQ := σQ₀) (op := op)
      -- hRun : some (decodeState σQ₁) = run? [op] (decodeState σQ₀)
      have hRunSingle :
        run? [op] (decodeState σQ₀) =
          applyOp? (decodeState σQ₀) op := by
        simp [run?]
        aesop
      have : some (decodeState σQ₁) = some τ := by
        calc
          some (decodeState σQ₁)
              = run? [op] (decodeState σQ₀) := by simp_all
          _   = applyOp? (decodeState σQ₀) op := hRunSingle
          _   = some τ := by simpa [hdec] using hstep
      exact Option.some.inj this

    -- 3. Apply the IH to the tail `ps`, starting from σQ₁
    have hTail :
        QPhaseProductCoverage_decoded hk
          (compileProgramAux σQ₁ ps).1 σQ₁ pts :=
      IH σQ₁ hDec1

    -- 4. Qubit semantics of the compiled op (prog1, σQ₁)
    have hProgSound : Qubits.applyProg prog1 σQ₀ = σQ₁ := by
      have := compileOp_sound (σ := σQ₀) (op := op)
      simp at this
      aesop

    -- 5. Use the prepend lemma to stick `prog1` in front of the tail program
    have hTail' :
        QPhaseProductCoverageM (Q_matchesAt_pointRow_state hk)
          (compileProgramAux σQ₁ ps).1
          (Qubits.applyProg prog1 σQ₀) pts := by
      -- just rephrase hTail with σQ₁ = applyProg prog1 σQ₀
      simpa [QPhaseProductCoverage_decoded, hProgSound] using hTail

    have hFull :
        QPhaseProductCoverageM (Q_matchesAt_pointRow_state hk)
          (prog1 ++ (compileProgramAux σQ₁ ps).1) σQ₀ pts := by
      have:=QPhaseProductCoverage_prepend_prog
        (M := Q_matchesAt_pointRow_state hk)
        (p₁ := prog1)
        (p₂ := (compileProgramAux σQ₁ ps).1)
        (σ₀ := σQ₀) (pts := pts)
        hTail'
      aesop

    -- 6. Finally, rewrite `compileProgramAux σQ₀ (op :: ps)` to that concatenation
    have hComp :
      compileProgramAux σQ₀ (op :: ps)
        = (prog1 ++ (compileProgramAux σQ₁ ps).1,
          (compileProgramAux σQ₁ ps).2) := by
      simp [compileProgramAux, h1]

    -- wrap up
    show QPhaseProductCoverage_decoded hk
        (compileProgramAux σQ₀ (op :: ps)).1 σQ₀ pts
    -- unfold and rewrite using hComp
    simpa [QPhaseProductCoverage_decoded, hComp] using hFull


lemma phaseCov_phase_case
    {k : ℕ} (hk : 0 < k)
    (i : Fin k)
    {ps : Prog k} {σ : State k}
    {pts1 pts2 : List Point}
    (hconsume :
      List.eraseFirstMatch?
        (fun pt => matchesAt_pointRow_state hk σ i pt) pts1 = some pts2)
    (IH :
      ∀ σQ₀ : Qubits.State k,
        decodeState σQ₀ = σ →
          QPhaseProductCoverage_decoded hk
            (compileProgramAux σQ₀ ps).1 σQ₀ pts2) :
    ∀ σQ₀ : Qubits.State k,
      decodeState σQ₀ = σ →
        QPhaseProductCoverage_decoded hk
          (compileProgramAux σQ₀ (valid_ops.phaseProduct i :: ps)).1 σQ₀ pts1 := by
  intro σQ₀ hdec
  have hTail :
      QPhaseProductCoverage_decoded hk
        (compileProgramAux σQ₀ ps).1 σQ₀ pts2 :=
    IH σQ₀ hdec
  -- unfold the `_decoded` abbreviation
  have hTail' :
      QPhaseProductCoverageM (Q_matchesAt_pointRow_state hk)
        (compileProgramAux σQ₀ ps).1 σQ₀ pts2 := by
    simpa [QPhaseProductCoverage_decoded] using hTail

  have hconsumeQ :
      List.eraseFirstMatch?
        (fun pt => Q_matchesAt_pointRow_state hk σQ₀ i pt) pts1 = some pts2 := by
    simpa [Q_matchesAt_pointRow_state, hdec] using hconsume

  have hPhase :
      QPhaseProductCoverageM (Q_matchesAt_pointRow_state hk)
        (Qubits.valid_operation.phaseProduct i
           :: (compileProgramAux σQ₀ ps).1)
        σQ₀ pts1 :=
    QPhaseProductCoverageM.step_phase
      (M      := Q_matchesAt_pointRow_state hk)
      (i      := i)
      (ps     := (compileProgramAux σQ₀ ps).1)
      (σ      := σQ₀)
      (pts    := pts1)
      (pts'   := pts2)
      (hconsume := hconsumeQ)
      (hrest    := hTail')

  have hOp :
      compileOp σQ₀ (valid_ops.phaseProduct i)
        = ([Qubits.valid_operation.phaseProduct i], σQ₀) := by
    simp [compileOp]
    aesop

  have hComp :
      compileProgramAux σQ₀ (valid_ops.phaseProduct i :: ps)
        = ( [Qubits.valid_operation.phaseProduct i]
              ++ (compileProgramAux σQ₀ ps).1,
            (compileProgramAux σQ₀ ps).2 ) := by
    simp [compileProgramAux, hOp]

  have hPhase_decoded :
      QPhaseProductCoverage_decoded hk
        (compileProgramAux σQ₀ (valid_ops.phaseProduct i :: ps)).1
        σQ₀ pts1 := by
    have :
        (compileProgramAux σQ₀ (valid_ops.phaseProduct i :: ps)).1
          = (Qubits.valid_operation.phaseProduct i
              :: (compileProgramAux σQ₀ ps).1) := by
      simp[hComp]
    simpa [QPhaseProductCoverage_decoded, this] using hPhase

  exact hPhase_decoded

lemma phaseCoverage_preserved_by_compileAux
    {k} (hk : 0 < k) (p : Prog k) (σC₀ : State k) (pts : List Point)
    (hClass : PhaseProductCoverage hk p σC₀ pts) :
  ∀ σQ₀, decodeState σQ₀ = σC₀ →
    QPhaseProductCoverage_decoded hk (compileProgramAux σQ₀ p).1 σQ₀ pts :=
by
  -- induction with motive = PhaseCovMotive hk p σC pts
  induction hClass with
  | nil =>
    intro σQ₀ h
    unfold QPhaseProductCoverage_decoded QPhaseProductCoverage compileProgramAux
    simp
    apply QPhaseProductCoverageM.nil
  | step_op hstep hrest IH =>
      intro σQ₀ hdec
      rename_i op ps σC₀ τ pts
      apply (phaseCov_stepOp_case (hk := hk) op ps σC₀ τ pts hstep (by unfold PhaseProductCoverage;apply hrest) IH)
      apply hdec
  | step_phase hconsume hrest IH =>
      rename_i i ps σ pts1 pts2
      have stepCase :=
        phaseCov_phase_case (k := k) (hk := hk)
          (i := i)
          (ps := ps) (σ := σ)
          (pts1 := pts1) (pts2 := pts2)
          hconsume IH
      exact stepCase


theorem phaseCoverage_preserved_by_compile
    {k : ℕ} (hk : 0 < k)
    (p   : Prog k)
    (σQ₀ : Qubits.State k)
    (pts : List Point)
    (hClass : PhaseProductCoverage hk p (decodeState σQ₀) pts) :
  let res   := compileProgramAux σQ₀ p
  let progQ := res.1
  QPhaseProductCoverage_decoded hk progQ σQ₀ pts := by {
    have h := phaseCoverage_preserved_by_compileAux (k := k) hk p (decodeState σQ₀) pts hClass
    intro res progQ
    simp_all only [progQ, res]
  }
