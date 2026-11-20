import ForShor.ShorVerification.Implementation.Readout.Locality
import ForShor.ShorVerification.Implementation.Readout.Proofs.LocalityInfinite

/-!
# Readout: the semiclassical circuits do not depend on ANY qubit they do not name

The T3/T4 agreement theorems of `Locality.lean` need the two start kets to differ at finitely
many qubits (`hfin`). Here that hypothesis is gone: the start kets may differ at infinitely many
qubits (which the model basis `ℕ → Bool` allows). The general machinery is
`Proofs/LocalityInfinite.lean` (`MGate.recordProb_of_agree_inf`).

* **Real circuit** (`orderFindingSemiclassical`): NO hypothesis on the registers or the start
  kets beyond agreement on `semiclassicalQubits c y work scratch flag` (control, owned qubits of
  `y`/`work`/`scratch` with reserves, flag):
  `orderFindingSemiclassical_recordProb_of_agree_inf`, `orderFindingSemiclassical_success_of_agree_inf`.
* **Lowered circuit** (`orderFindingSemiclassicalLow`): the hypotheses of
  `semiclassical_lowerM_eval` for `b0` (admissible policy, workspace, layout, zero reserves of
  `y`/`work`/`scratch`, zero active scratch), and `b0'` agreeing with `b0` on
  `semiclassicalQubits`: `orderFindingSemiclassicalLow_recordProb_of_agree_inf`,
  `orderFindingSemiclassicalLow_success_of_agree_inf`.
* **Corollary** `orderFindingSemiclassicalLow_success_eq_of_named`: the success probability of the
  lowered circuit is the same for ANY two start kets whose named qubits (`semiclassicalQubits`)
  carry the same bits, as long as one of them has clean named registers. In particular the
  exponent register (and every other unnamed qubit) may start in an arbitrary computational
  basis state, including patterns with infinitely many `1`s.

What is not covered is exactly as in `Locality.lean`: reserve qubits are named (so not free),
programs with an `idealCtrlModMul` node are not covered by the general theorem, and nothing is
said about named qubits.
-/

namespace Shor
namespace Readout

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- **Real circuit, any number of differing qubits.** For any registers and any two start kets
`b0`, `b0'` that agree on every qubit of `semiclassicalQubits c y work scratch flag`, every
record `r` of the real circuit has the same probability. No finiteness hypothesis: `b0` and
`b0'` may differ at infinitely many qubits. -/
theorem orderFindingSemiclassical_recordProb_of_agree_inf (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 b0' : qs.Basis)
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0'))) r
      = recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0))) r :=
  MGate.recordProb_of_agree_inf _ (orderFindingSemiclassical_noIdeal a N c m hw hs4) b0 b0'
    (fun p hp => hagree p (orderFindingSemiclassical_support a N m hw hs4 hp)) r

/-- **Real circuit, success.** Same hypotheses: the success probability (any `T`, `verify`,
`r`, `Q`) is the same from `|b0'⟩` as from `|b0⟩`. -/
theorem orderFindingSemiclassical_success_of_agree_inf (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 b0' : qs.Basis)
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (T : ℕ → ℕ) (verify : ℕ → Bool) (r Q : ℕ) :
    probability_of_success_M T verify m r Q
        ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
          (MState.init (qs.ket b0')))
      = probability_of_success_M T verify m r Q
        ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
          (MState.init (qs.ket b0))) :=
  probability_of_success_M_congr T verify m r Q fun rec =>
    orderFindingSemiclassical_recordProb_of_agree_inf a N c m y work scratch flag hw hs4 b0 b0'
      hagree rec

/-- **Lowered circuit, any number of differing qubits.** Hypotheses of
`semiclassical_lowerM_eval` for `b0`: admissible policy `P`, lowering workspace `hws`,
`SemiclassicalLayout c y work scratch flag`, zero data / work / scratch reserves in `b0`, zero
scratch register in `b0`. For ANY `b0'` that agrees with `b0` on `semiclassicalQubits c y work
scratch flag` (and may differ from it at infinitely many other qubits), every record of the
lowered circuit has the same probability from `|b0'⟩` as from `|b0⟩`. -/
theorem orderFindingSemiclassicalLow_recordProb_of_agree_inf {P : ShorLoweringPolicy}
    (hP : P.Admissible) (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 b0' : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0)
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (qs.ket b0'))) r
      = recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (qs.ket b0))) r := by
  have hzero' := semiclassicalWorkspaceCleanInput_ofAgree hagree hzero
  have hscratch' : RegEncoding.toNat scratch.active b0' = 0 := by
    rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_scratch (active_sub p hp)) hagree,
      hscratch]
  rw [orderFindingSemiclassicalLow,
    semiclassical_lowerM_eval hP a N c m y work scratch flag hw hs4 hws hl b0' hzero' hscratch',
    semiclassical_lowerM_eval hP a N c m y work scratch flag hw hs4 hws hl b0 hzero hscratch]
  exact orderFindingSemiclassical_recordProb_of_agree_inf a N c m y work scratch flag hw hs4 b0
    b0' hagree r

/-- **Lowered circuit, success.** Same hypotheses as
`orderFindingSemiclassicalLow_recordProb_of_agree_inf`. -/
theorem orderFindingSemiclassicalLow_success_of_agree_inf {P : ShorLoweringPolicy}
    (hP : P.Admissible) (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 b0' : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0)
    (hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b0' = RegEncoding.bit p b0)
    (T : ℕ → ℕ) (verify : ℕ → Bool) (r Q : ℕ) :
    probability_of_success_M T verify m r Q
        ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
          (MState.init (qs.ket b0')))
      = probability_of_success_M T verify m r Q
        ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
          (MState.init (qs.ket b0))) :=
  probability_of_success_M_congr T verify m r Q fun rec =>
    orderFindingSemiclassicalLow_recordProb_of_agree_inf hP a N c m y work scratch flag hw hs4
      hws hl b0 b0' hzero hscratch hagree rec

/-- **Corollary: only the named qubits matter.** Under the hypotheses of the lowered theorem
(stated for one reference ket `b0` with clean named registers), the success probability of the
lowered circuit, as a function of the start ket, is constant on the set of ALL basis kets whose
bits on `semiclassicalQubits c y work scratch flag` are those of `b0`: for any two such kets
`b1`, `b2` (arbitrary, possibly infinitely different, outside `semiclassicalQubits`) the success
probabilities coincide. So the exponent register (and every other qubit outside
`semiclassicalQubits`) can start in an arbitrary computational-basis state. -/
theorem orderFindingSemiclassicalLow_success_eq_of_named {P : ShorLoweringPolicy}
    (hP : P.Admissible) (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0) (b1 b2 : qs.Basis)
    (h1 : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b1 = RegEncoding.bit p b0)
    (h2 : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p b2 = RegEncoding.bit p b0)
    (T : ℕ → ℕ) (verify : ℕ → Bool) (r Q : ℕ) :
    probability_of_success_M T verify m r Q
        ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
          (MState.init (qs.ket b1)))
      = probability_of_success_M T verify m r Q
        ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
          (MState.init (qs.ket b2))) :=
  (orderFindingSemiclassicalLow_success_of_agree_inf hP a N c m y work scratch flag hw hs4 hws hl
      b0 b1 hzero hscratch h1 T verify r Q).trans
    (orderFindingSemiclassicalLow_success_of_agree_inf hP a N c m y work scratch flag hw hs4 hws
      hl b0 b2 hzero hscratch h2 T verify r Q).symm

end Readout
end Shor
