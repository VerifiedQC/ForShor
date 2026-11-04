import Mathlib

/- Pure integer max-plus profile algebra. No scanner, row operation, target,
   legal schedule, realizability oracle, or polynomial algorithm is encoded. -/

namespace Paper

theorem profile_offset_formula (A B R : ℤ) :
    max B (A - R) = max A (R + B) - R := by
  omega

theorem profile_canonical_constraints (A B R : ℤ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    0 ≤ max A B ∧ 0 ≤ max B (A - R) ∧
    max B (A - R) ≤ max A B ∧
    max A B - R ≤ max B (A - R) := by
  omega

theorem profile_canonical_identity (A B R r : ℤ)
    (hr0 : 0 ≤ r) (hrR : r ≤ R) :
    max A (r + B) = max (max A B) (r + max B (A - R)) := by
  omega

theorem profile_k_remainder_identity (A B k r : ℤ)
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hrk : r < k) :
    max A (r + B) = max (max A B) (r + max B (A - (k - 1))) := by
  exact profile_canonical_identity A B (k - 1) r hr0 (by omega)

theorem profile_child_algebra_identity (A B k r L : ℤ)
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hrk : r < k) :
    L + 1 + max A (r + B) =
    L + 1 + max (max A B) (r + max B (A - (k - 1))) := by
  rw [profile_k_remainder_identity A B k r hk hr0 hrk]

theorem profile_canonical_endpoints (a b R : ℤ)
    (hba : b ≤ a) (hab : a - R ≤ b) :
    max a (0 + b) = a ∧ max a (R + b) = R + b := by
  omega

theorem profile_endpoint_uniqueness (a b a' b' R : ℤ)
    (hba : b ≤ a) (hab : a - R ≤ b)
    (hba' : b' ≤ a') (hab' : a' - R ≤ b')
    (hzero : max a (0 + b) = max a' (0 + b'))
    (hlast : max a (R + b) = max a' (R + b')) :
    a = a' ∧ b = b' := by
  omega

theorem profile_function_uniqueness (a b a' b' R : ℤ)
    (hR : 0 ≤ R) (hba : b ≤ a) (hab : a - R ≤ b)
    (hba' : b' ≤ a') (hab' : a' - R ≤ b')
    (heq : ∀ r : ℤ, 0 ≤ r → r ≤ R → max a (r + b) = max a' (r + b')) :
    a = a' ∧ b = b' := by
  exact profile_endpoint_uniqueness a b a' b' R hba hab hba' hab'
    (heq 0 (by omega) hR) (heq R hR (by omega))

theorem profile_componentwise_iff_pointwise (a b a' b' R : ℤ)
    (hR : 0 ≤ R) (hba : b ≤ a) (hab : a - R ≤ b)
    (hba' : b' ≤ a') (hab' : a' - R ≤ b') :
    (a ≤ a' ∧ b ≤ b') ↔
    (∀ r : ℤ, 0 ≤ r → r ≤ R → max a (r + b) ≤ max a' (r + b')) := by
  constructor
  · intro h r hr0 hrR
    omega
  · intro h
    have hz := h 0 (by omega) hR
    have hlast := h R hR (by omega)
    omega

theorem profile_endpoint_cap_iff_raw_bounds (A B a b R : ℤ)
    (hba : b ≤ a) (hab : a - R ≤ b) :
    (max A B ≤ a ∧ max A (R + B) ≤ R + b) ↔ (A ≤ a ∧ B ≤ b) := by
  omega

theorem profile_raw_cap_iff_all_remainders (A B a b R : ℤ)
    (hR : 0 ≤ R) (hba : b ≤ a) (hab : a - R ≤ b) :
    (A ≤ a ∧ B ≤ b) ↔
    (∀ r : ℤ, 0 ≤ r → r ≤ R → max A (r + B) ≤ max a (r + b)) := by
  constructor
  · intro h r hr0 hrR
    omega
  · intro h
    have hz := h 0 (by omega) hR
    have hlast := h R hR (by omega)
    omega

theorem profile_padding_raw_equality (A B a b r : ℤ)
    (hA : A ≤ a) (hB : B ≤ b) :
    max (max A a) (r + max B b) = max a (r + b) := by
  omega

theorem profile_padding_from_endpoints (A B a b R r : ℤ)
    (hba : b ≤ a) (hab : a - R ≤ b)
    (hzero : max A B ≤ a) (hlast : max A (R + B) ≤ R + b) :
    max (max A a) (r + max B b) = max a (r + b) := by
  omega

theorem profile_padding_from_canonical_domination (A B a b R r : ℤ)
    (ha : max A B ≤ a) (hb : max B (A - R) ≤ b) :
    max (max A a) (r + max B b) = max a (r + b) := by
  omega

theorem profile_charge_monotone_at_fixed_child (cQ cP child : ℤ)
    (hcharge : cQ ≤ cP) (hchild : 1 ≤ child) :
    8 * (child - 1) * cQ ≤ 8 * (child - 1) * cP := by
  exact mul_le_mul_of_nonneg_left hcharge (by omega)

end Paper
