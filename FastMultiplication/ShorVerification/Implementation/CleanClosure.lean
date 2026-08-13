import FastMultiplication.ShorVerification.Framework.Quantum.QSemantics

/-!
# Generic basis-clean linear closure (implementation proof-support)

`CleanClosure P` is the linear subspace spanned by basis kets satisfying a
per-basis cleanliness predicate `P`.  It is used only inside the lowering /
correctness proofs, so it lives on the implementation side.
-/

namespace Shor


/-- The set of states reachable from `P`-clean basis kets by `+` and `•`:
    a `zero/ket/add/smul` linear closure parameterized by the per-basis
    predicate `P`. -/
inductive CleanClosure {qs : QSemantics} [RegEncoding qs.Basis]
    (P : qs.Basis → Prop) : qs.State → Prop
  | zero : CleanClosure P 0
  | ket (b : qs.Basis) (h : P b) : CleanClosure P (qs.ket b)
  | add {ψ φ : qs.State} (hψ : CleanClosure P ψ) (hφ : CleanClosure P φ) :
      CleanClosure P (ψ + φ)
  | smul (a : ℂ) {ψ : qs.State} (hψ : CleanClosure P ψ) :
      CleanClosure P (a • ψ)

end Shor
