import Provider.Ladders.CatalogTransfer
import PhaseProduct.Identity.CanonicalNodes
import PhaseProduct.Identity.GeneralConstruction

/-!
# F2 point ladder: injectivity and normalization

Properties of the fixed F2 point enumeration `f2Point` used by the raw ladder
sources. It proves that `f2Point` is injective (`f2Point_injective`) and that
its points are already in normalized form (`normalize_f2Point`), the node
facts needed by the certificate construction.
-/

namespace Paper.F2CatalogTransfer

open TableGeneration TableGeneration.Operations Paper.Normalization

private def rev4 (n : Nat) : Nat := 4 * (n / 4) + (3 - n % 4)

private theorem rev4_div (n : Nat) : rev4 n / 4 = n / 4 := by
  have h := Nat.mod_lt n (show 0 < 4 by decide)
  unfold rev4
  omega

private theorem rev4_mod (n : Nat) : rev4 n % 4 = 3 - n % 4 := by
  have h := Nat.mod_lt n (show 0 < 4 by decide)
  unfold rev4
  omega

private theorem rev4_rev4 (n : Nat) : rev4 (rev4 n) = n := by
  rw [rev4, rev4_div, rev4_mod]
  have h := Nat.mod_add_div n 4
  have hr := Nat.mod_lt n (show 0 < 4 by decide)
  omega

private def f2Index : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | n + 4 => rev4 n + 4

private theorem f2Index_involutive (n : Nat) : f2Index (f2Index n) = n := by
  by_cases hn : n < 4
  . interval_cases n <;> decide
  . have he : n = (n-4)+4 := by omega
    rw [he]
    simp only [f2Index]
    exact congrArg (fun x => x + 4) (rev4_rev4 (n-4))

private theorem f2Index_injective : Function.Injective f2Index := by
  intro a b h
  have h' := congrArg f2Index h
  simpa only [f2Index_involutive] using h'

private theorem f2Point_eq_canonical (n : Nat) :
    f2Point n = canonicalPoint (f2Index n) := by
  by_cases hn : n < 4
  . interval_cases n <;> decide
  . have he : n = (n-4)+4 := by omega
    rw [he]
    have hr : (n-4) % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases hm : (n-4) % 4 <;>
      simp [f2Point, f2Index, canonicalPoint, rev4_div, rev4_mod, hm]

theorem f2Point_injective : Function.Injective f2Point := by
  intro a b h
  apply f2Index_injective
  apply Paper.CanonicalNodes.canonicalPoint_injective
  simpa only [f2Point_eq_canonical] using h

theorem normalize_f2Point (n : Nat) :
    normalizePoint (f2Point n) = f2Point n := by
  rw [f2Point_eq_canonical]
  exact Paper.CanonicalNodes.normalize_canonicalPoint _

end Paper.F2CatalogTransfer
