import ForShor.ShorVerification.Implementation.Readout.Statement
import ForShor.ShorVerification.Implementation.Shor.Proofs.ApproxSetup

/-!
# Readout: the semiclassical order-finding circuit (statement side)

Everything needed to state the success theorems of `Readout/Shor.lean`.

* `semiclassicalMultipliers a N c m y work scratch flag hw hs4 j` is round `j`'s
  multiplier: the REAL five-step controlled modular multiplier
  `CmodMulInPlaceCore (a^(2^(m-1-j)) mod N) N c y work scratch flag hw hs4`,
  i.e. the same gate (same constant, same Step-5 inverse constant
  `step5Constant`, same workspaces) that `modExpApproxValid` applies for the
  exponent qubit of weight `2^(m-1-j)`, with the control `ctrl := c`.
* `orderFindingSemiclassical a N c m y work scratch flag hw hs4` is the full
  semiclassical order-finding circuit as an `MGate`:
  `initY1 y.active` (data register `0 ↦ 1`), then the `m` rounds of
  `readoutRounds` on the one control qubit `c`. It replaces
  `H_reg x ;; initY1 ;; modExpApproxValid ;; IQFT x` (`orderFindingApprox`):
  no exponent register.
* `recordOutcomeProb m ψ o`: the probability that a run ends with a record of
  `m` outcomes whose little-endian reading (`readoutOfRecord`) is `o`;
  `probability_of_success_M` is `∑_{o < Q} r_found verify o Q r · recordOutcomeProb m ψ o`,
  the semiclassical analogue of `probability_of_success` with the same
  continued-fraction post-processing `r_found`.
* `SemiclassicalShorSetup`: the hypotheses (layout, workspaces, precision, clean
  start, and a reference exponent register `x` that the circuit never touches).

These are high-level (`Gate`-level) statements, like `orderFindingApprox`; the
lowered form (`Policy.lowerGate` on the unitary parts) is a separate step.
-/

namespace Shor

/-- Round `j`'s multiplier of the semiclassical circuit with `m` rounds: the
five-step controlled in-place modular multiplier `CmodMulInPlaceCore` by
`a^(2^(m-1-j)) mod N` on the data register `y`, controlled by the qubit `c`.
This is the gate `modExpApproxStepsValid` uses for the exponent bit of weight
`2^(m-1-j)` (there with the control `x_(m-1-j)`), with `ctrl := c`. -/
def semiclassicalMultipliers (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) : ℕ → Gate :=
  fun j => CmodMulInPlaceCore ((a ^ (2 ^ (m - 1 - j))) % N) N c y work scratch flag hw hs4

/-- **The semiclassical order-finding circuit.** Prepare the data register
`y.active` in `1` (`initY1`, an `X` on its lowest qubit), then run `m`
semiclassical rounds on the single control qubit `c`: round `j`
(`j = 0, …, m-1`) is

  `H c ;; CmodMulInPlaceCore (a^(2^(m-1-j)) mod N) … (ctrl := c) ;; ffPhase c j ;; H c ;; measureReset c`.

The record of `m` outcomes, read little-endian (`readoutOfRecord`), plays the
role of the measured exponent register of `orderFindingApprox`. -/
def orderFindingSemiclassical (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) : MGate :=
  .seq (.unitary (initY1 y.active))
    (readoutRounds (semiclassicalMultipliers a N c m y work scratch flag hw hs4) c m)

section
variable {qs : QSemantics}

/-- The probability that the run `ψ` ends with a record of exactly `m` outcomes
whose little-endian reading is `o` (a finite sum: there is at most one such
record, none if `o ≥ 2^m`). -/
noncomputable def recordOutcomeProb (m : ℕ) (ψ : MState qs) (o : ℕ) : ℝ :=
  ∑' rec : Record, if rec.length = m ∧ readoutOfRecord rec = o then recordProb ψ rec else 0

/-- **Success probability of a semiclassical run.** The probability that the
record (`m` outcomes, read as the integer `o = readoutOfRecord rec`), post-
processed by continued fractions exactly as in `probability_of_success`
(`r_found T verify o Q r`), returns `r`:
`∑_{o < Q} r_found verify o Q r · P(record reads o)`. -/
noncomputable def probability_of_success_M (T : ℕ → ℕ) (verify : ℕ → Bool) (m r Q : ℕ)
    (ψ : MState qs) : ℝ :=
  ∑ o : Fin Q, r_found (T := T) verify o.1 Q r * recordOutcomeProb m ψ o.1

end

/-- Hypotheses of the semiclassical success theorems, on the registers
`y` (data), `work`, `scratch`, the flag qubit, the control qubit `c`, and a
reference exponent register `x`.

`x` is NOT used by the semiclassical circuit. It only fixes the number of
rounds `m = regSize x.active` and `Q = 2^m`, and lets the proof compare with the
textbook circuit `orderFindingIdeal` on the same start ket `b0` (the existing
ideal bound `Shor_correct` is stated for it). Any qubits outside `y` that are
`0` in `b0` will do; they may even contain `c` (e.g. `c` = the first exponent
qubit, `ShorApproxSetup.toSemiclassicalShorSetup`).

Fields: the control `c` lies outside `y`, `work`, `scratch` (reserves included)
and is not the flag; the modular-multiplier workspaces (exactly those of
`ShorApproxSetup`); the precision `η` of the work register; `x` and `y` own
disjoint qubits; the start ket `b0` is zero on `x`, `y`, `work`, `scratch`, their
spare qubits and the flag (`ShorCleanInput`), and on `c`. -/
structure SemiclassicalShorSetup (qs : QSemantics) [RegEncoding qs.Basis] (η : ℝ) (N c : ℕ)
    (x y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis) : Type where
  layout : SemiclassicalLayout c y work scratch flag
  circuit_workspace : ModMulCircuitWorkspaceOK y work
  step4_workspace : CmpLtNWWorkspace N (y.grow 1) work scratch flag
  work_precision : Algorithm1Precision η y.active work.active
  reference_data_disjoint : ExtReg.OwnedDisjoint x y
  clean_input : ShorCleanInput qs x y work scratch flag b0
  control_zero : RegEncoding.bit c b0 = false

end Shor
