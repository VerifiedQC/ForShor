import ForShor.ShorVerification.Framework.Gatecount.ResourceModel
import ForShor.ShorVerification.Framework.Policy

/-!
# The resource model a policy is priced under

A policy carries a `NegationMethod`; this file turns it into the `LowGateResourceModel` its circuits are charged
by. The model differs from `shorGateResourceModel` only in what a `Negate` costs. For the default method
(`oneQubit`) it is `shorGateResourceModel` itself, so a policy that names no method is priced exactly as before.
-/

namespace Shor
namespace ShorLoweringPolicy

/-- The resource model a policy is priced under. -/
def resourceModel (P : ShorLoweringPolicy) : LowGateResourceModel :=
  shorGateResourceModelFor P.negation

theorem resourceModel_of_oneQubit {P : ShorLoweringPolicy} (h : P.negation = .oneQubit) :
    P.resourceModel = shorGateResourceModel := by
  simp [resourceModel, h]

@[simp] theorem resourceModel_negate (P : ShorLoweringPolicy) (r : ExtReg) :
    P.resourceModel.negate r = negateResourcesFor P.negation r := rfl

@[simp] theorem constPolicy_resourceModel (T : ToomCookTable) :
    (constPolicy T).resourceModel = shorGateResourceModel := rfl

@[simp] theorem withRule_resourceModel (P : ShorLoweringPolicy) (R : WidthRule) :
    (P.withRule R).resourceModel = P.resourceModel := rfl

@[simp] theorem withNegation_resourceModel (P : ShorLoweringPolicy) (m : NegationMethod) :
    (P.withNegation m).resourceModel = shorGateResourceModelFor m := rfl

end ShorLoweringPolicy

namespace ShorPolicySubmission

@[simp] theorem policy_resourceModel (s : ShorPolicySubmission) :
    s.policy.resourceModel = shorGateResourceModelFor s.negation := rfl

end ShorPolicySubmission
end Shor
