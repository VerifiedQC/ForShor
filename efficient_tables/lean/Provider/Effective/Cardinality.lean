import Provider.Effective.Complete
import Provider.Effective.Size

/-! # Effective Provider Cardinality
Proves `keys_length`: the effective provider visits exactly one key position for each bounded arity and pair of bounded peak values. Also proves `catalog_length`, the exact size decomposition of the catalog before any source-check filtering. The program catalog may contain many entries at each key position.
-/

namespace Paper.EffectiveProvider

/-- The effective provider visits exactly one key position for each bounded
arity and pair of bounded peak values, including arities without valid F2
sources. Its program catalog may contain many entries at each position. -/
theorem keys_length (K root : Nat) :
    (keys K root).length = (K + 1) * (root + 1) ^ 2 := by
  simp [keys, List.length_flatMap, pow_two]

/-- Exact size decomposition before any source-check filtering. -/
theorem catalog_length (K root : Nat) :
    (catalog K root).length =
      ((keys K root).map (fun key =>
        (Paper.BoundedThreshold.searchEntries key.1.val key.2.1.val
          (Paper.BoundedThreshold.lengthCap key.1.val (budget K root))).length)).sum := by
  simp [catalog, List.length_flatMap]

end Paper.EffectiveProvider
