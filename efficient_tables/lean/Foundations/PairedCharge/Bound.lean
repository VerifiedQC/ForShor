import Foundations.PairedCharge.ChargeFormula

namespace PairedCharge

theorem charge_le (k : ℕ) (hk : 2 ≤ k) :
    ((PairedCharge.cPair k : ℕ) : ℤ) ≤ 4 * (k : ℤ) ^ 2 - 6 * (k : ℤ) + 1 ∧
    4 * (k : ℤ) ^ 2 - 6 * (k : ℤ) + 1 ≤ 6 * (k : ℤ) ^ 2 := by
  obtain ⟨⟨h1, h2⟩, _, h3⟩ := charge_formula k hk
  have h4 : (PairedCharge.nu k : ℤ) ≤ (k : ℤ) - 1 := by
    have : PairedCharge.nu k + 1 ≤ k := by omega
    have : ((PairedCharge.nu k + 1 : ℕ) : ℤ) ≤ (k : ℤ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hk' : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  constructor
  · rw [h1, h2]; linarith
  · nlinarith

end PairedCharge
