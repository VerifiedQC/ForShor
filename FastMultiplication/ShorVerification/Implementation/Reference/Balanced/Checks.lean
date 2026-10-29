import FastMultiplication.ShorVerification.Implementation.Reference.Balanced.Defs

/-!
# Balanced phase products: concrete plans at `n = 2048`

The default rule's plans at the four unequal Shor sites of the reference layout
at `n = 2048` (work = 2347, data = 2048, scratch = 4398; sites
`(data+1) × (work+1)`, `(work+1) × (data+2)`, `(data+2) × (work+1)`,
`(work+1) × (scratch+1)`), checked by the kernel (`decide`).
-/

namespace Shor
namespace Balanced

/-- Steps 1, 2, 5: pad the small operand to 2348 (no lower block). -/
theorem defaultPlan_2348_2049 : defaultPlan 2348 2049 = some ⟨[], 2348⟩ := by decide
theorem defaultPlan_2348_2050 : defaultPlan 2348 2050 = some ⟨[], 2348⟩ := by decide

/-- Step 4: 4399 = 2347 (zero-extended to 2348) + 2052 (padded to 2348): two 2348 × 2348 products. -/
theorem defaultPlan_4399_2348 : defaultPlan 4399 2348 = some ⟨[⟨2347, 2348⟩], 2348⟩ := by decide

/-- Equal widths are left alone. -/
theorem defaultPlan_eq (n : ℕ) : defaultPlan n n = none := by
  unfold defaultPlan; simp

end Balanced
end Shor
