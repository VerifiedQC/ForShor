import FastMultiplication.Emit.Reflect.Targets
import FastMultiplication.Emit.IR.Instantiate
import FastMultiplication.Emit.Json.LowGateJson

/-!
# R6: the correctness-theorem lemma library

`Emit/PLAN.md` §12. Lemmas about `IR.evalW`/`evalReg`/`evalA`/`Env.call`/
`evalNode` reused across every per-template R6 theorem
(`Proofs/PhaseProduct.lean`, `Proofs/Qft.lean`, `Proofs/Shor.lean`).
-/

namespace Shor.IR

/-- `evalNode`'s `foldLowGateSeq` and the real `LowGate.sequence` are the
same right fold. -/
theorem foldLowGateSeq_eq_sequence (l : List LowGate) : foldLowGateSeq l = LowGate.sequence l := by
  induction l with
  | nil => rfl
  | cons g gs ih => simp [foldLowGateSeq, LowGate.sequence, ih]

/-- The project's real notion of "two `LowGate` terms describe the same
circuit" is not raw AST equality but "the same flattened leaf sequence"
(`Json/README.md`: `lowGateJson` compares via `flattenSeq`; every R2
`native_decide` check in `Tests.lean` compares `lowGateJson` output, not
raw `LowGate`s). `evalNode`'s `.loop` unrolling naturally produces
*nested* `sequence`s (one per loop level) while a hand-written real term
like `naiveSignedPhaseGates` produces one *flat* `sequence` over a
`flatMap`-built list — different ASTs, same flattened form. This lemma is
the bridge every R6 theorem needs to reconcile the two shapes:
`flattenSeq` distributes over `sequence` exactly the way `flatMap`
distributes over itself. -/
theorem flattenSeq_sequence (l : List LowGate) :
    (LowGate.sequence l).flattenSeq = l.flatMap LowGate.flattenSeq := by
  induction l with
  | nil => rfl
  | cons g gs ih => simp [LowGate.sequence, LowGate.flattenSeq, ih]

/-- `List.mapM` over `Except` collapses to a plain `List.map` once every
call is known to succeed. -/
theorem List.mapM_except_ok {α β : Type*} (f : α → β) (l : List α) :
    l.mapM (fun a => (Except.ok (f a) : Except String β)) = Except.ok (l.map f) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.mapM_cons, ih, List.map_cons]; rfl

/-- The environment `naive_leaf`'s template is meant to be checked against:
`x`/`z` and `phi` bound directly. `opaqueW`/`coeff` are parameters (default
`fun _ _ => none`), not hardcoded: `naive_leaf`'s body has no `.opaque` or
`.coeff` subexpression at all, so `evalNode_naive_leaf`'s proof never
inspects them — but a *caller* reaching `naive_leaf` via `Env.call` (as
`phase_product`'s base case does, `Proofs/PhaseProduct.lean`) carries its
own real `opaqueW`/`coeff` through unchanged (`Env.call`'s own doc comment),
so the environment `evalNode` actually sees there is not literally this
`Env`'s default. Keeping them as parameters lets `evalNode_naive_leaf`
apply directly to *that* environment too, once its `w`/`a`/`r` fields are
shown equal to this one's (a trivial `Env.call`/`Env.mk` unfolding, nothing
about `opaqueW`/`coeff` needs to match). -/
def naiveLeafEnv (x z : ExtReg) (phi : Angle)
    (opaqueW : String → List ℕ → Option ℕ := fun _ _ => none)
    (coeff : ℕ → ℕ → Option ℚ := fun _ _ => none) : Env :=
  { w := fun n => if n == "xw" then some x.width else if n == "zw" then some z.width else none
    a := fun n => if n == "phi" then some phi else none
    r := fun n => if n == "x" then some x else if n == "z" then some z else none
    opaqueW := opaqueW
    coeff := coeff }

/-- `List.mapM` over `Except`, generalized to a pointwise-`Except.ok`
hypothesis rather than requiring the callback to be syntactically
`fun a => Except.ok (f a)`. -/
theorem List.mapM_except_ok_of_mem {α β : Type*} {F : α → Except String β} {f : α → β}
    (l : List α) (h : ∀ a ∈ l, F a = Except.ok (f a)) :
    l.mapM F = Except.ok (l.map f) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      have hF : F a = Except.ok (f a) := h a (List.mem_cons_self)
      have hrest : as.mapM F = Except.ok (as.map f) := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [List.mapM_cons, hF, hrest, List.map_cons]
      rfl

/-- `signedTermsAux` re-expressed as an indexed `List.range`-`map`, matching
the shape `evalNode`'s `.loop` unrolling produces. -/
theorem signedTermsAux_eq (width i : ℕ) (qs : List ℕ) :
    signedTermsAux width i qs =
      (List.range qs.length).map (fun j => (qs.getD j 0, signedBitWeight width (i + j))) := by
  induction qs generalizing i with
  | nil => rfl
  | cons q qs ih =>
      simp only [signedTermsAux, List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.map_map]
      congr 1
      rw [ih (i + 1)]
      apply List.map_congr_left
      intro j _
      simp [Function.comp, Nat.add_right_comm i 1 j, Nat.add_assoc]

/-- `signedTerms r` re-expressed the same way, in terms of `r.active.get`. -/
theorem signedTerms_eq (r : ExtReg) :
    signedTerms r =
      (List.range r.width).map (fun i => (r.active.qubits.getD i 0, signedBitWeight r.width i)) := by
  show signedTermsAux r.width 0 r.active.qubits = _
  simpa using signedTermsAux_eq r.width 0 r.active.qubits

/-- R6.2's first theorem (`Emit/PLAN.md` §12.4): `naive_leaf`'s extracted
body, instantiated against the real `x, z, phi`, succeeds and produces the
*same circuit* (same `flattenSeq`, `Json/README.md`'s notion of equality,
matching what `Tests.lean`'s R2.3 `native_decide` check already compares
via `lowGateJson`) as `Naive_SignedPhaseProd` — for *every* `x, z, phi`,
not just the widths R2.3 sampled. Stated via `flattenSeq` rather than raw
equality because `evalNode`'s `.loop`/`.loop` unrolling produces *nested*
`sequence`s while `Naive_SignedPhaseProd` is one *flat* `sequence`
(`flattenSeq_sequence` bridges the two). Unlike `phase_product`/`qft`,
this target has no table dependence and no recursion, so it needs none of
the register-slicing machinery R6.2 flags as the hard part — a natural
first R6 theorem. -/
theorem evalNode_naive_leaf (x z : ExtReg) (phi : Angle) (d : Doc) (fuel : ℕ)
    (opaqueW : String → List ℕ → Option ℕ := fun _ _ => none)
    (coeff : ℕ → ℕ → Option ℚ := fun _ _ => none) :
    ∃ g, evalNode d fuel (naiveLeafEnv x z phi opaqueW coeff) Reflect.naiveLeafTemplate.body = .ok g ∧
      g.flattenSeq = (LowGate.Naive_SignedPhaseProd phi x z).flattenSeq := by
  have hLHS : evalNode d fuel (naiveLeafEnv x z phi opaqueW coeff) Reflect.naiveLeafTemplate.body =
      .ok (LowGate.sequence (List.map (fun i => LowGate.sequence (List.map
        (fun j => LowGate.CPhase (x.active.qubits.getD i 0) (z.active.qubits.getD j 0)
          (signedPairAngle phi (x.active.qubits.getD i 0, signedBitWeight x.width i)
            (z.active.qubits.getD j 0, signedBitWeight z.width j)))
        (List.range z.width))) (List.range x.width))) := by
    simp [Reflect.naiveLeafTemplate, evalNode, evalW, Env.bindW, naiveLeafEnv,
      Except.instMonad, Monad.toBind, Except.bind, Except.pure, Except.map,
      foldLowGateSeq_eq_sequence]
    rw [List.mapM_except_ok_of_mem (l := List.range x.width) (f := fun i =>
      LowGate.sequence (List.map
        (fun j => LowGate.CPhase (x.active.qubits.getD i 0) (z.active.qubits.getD j 0)
          (signedPairAngle phi (x.active.qubits.getD i 0, signedBitWeight x.width i)
            (z.active.qubits.getD j 0, signedBitWeight z.width j)))
        (List.range z.width)))]
    all_goals first
      | rfl
      | (intro i hi
         have hix : i < x.width := List.mem_range.mp hi
         have hix' : i < x.active.width := hix
         have hix'' : i < x.active.qubits.length := hix'
         rw [List.mapM_except_ok_of_mem (l := List.range z.width) (f := fun j =>
           LowGate.CPhase (x.active.qubits.getD i 0) (z.active.qubits.getD j 0)
             (signedPairAngle phi (x.active.qubits.getD i 0, signedBitWeight x.width i)
               (z.active.qubits.getD j 0, signedBitWeight z.width j)))]
         all_goals first
           | rfl
           | (intro j hj
              have hjz : j < z.width := List.mem_range.mp hj
              have hjz' : j < z.active.width := hjz
              have hjz'' : j < z.active.qubits.length := hjz'
              simp [evalReg, evalA, evalW, Except.instMonad, Monad.toBind, Except.bind,
                Except.pure, Except.map, hix', hjz', buildLowGate, signedPairAngle,
                ExtReg.singleQubit?, ExtReg.ofReg, Reg.singleton, List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem hix'', List.getElem?_eq_getElem hjz'', Reg.get]))
  refine ⟨_, hLHS, ?_⟩
  simp only [LowGate.Naive_SignedPhaseProd, LowGate.naiveSignedPhaseGates, signedTerms_eq,
    List.map_map, flattenSeq_sequence, List.flatMap_map, List.flatMap_assoc, Function.comp]

end Shor.IR
