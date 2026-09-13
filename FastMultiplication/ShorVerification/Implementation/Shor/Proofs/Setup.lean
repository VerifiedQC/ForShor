import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Cleanliness

/-!
# Bridge from the approximate setup to the ideal order-finding input

`ShorApproxSetup.toIdealOrderFindingInput` is the final bridge from the
approximate setup to the ideal order-finding input predicate.
-/
namespace Shor

/--
The approximate Shor setup contains extra implementation assumptions, but the
ideal specification only needs the exponent/data zero state and their
disjointness. This lemma forgets the implementation-only fields.
-/
lemma ShorApproxSetup.toIdealOrderFindingInput
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {η : ℝ}
    {N : ℕ}
    {x y work scratch : ExtReg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (hsetup : ShorApproxSetup qs η N x y work scratch flag b0) :
    IdealOrderFindingInput qs x y b0 := by
  rcases hsetup.clean_input with
    ⟨hx0, hy0, _hyFresh, _hwork0,
      _hworkFresh, _hscratch0, _hscratchFresh, _hflag0⟩

  exact
    ⟨hx0, hy0, hsetup.exponent_data_disjoint⟩

end Shor
