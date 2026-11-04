import Provider.Ceiling.LocalBlock

/-! # Point Blocks
Proves length bounds `nonzeroFins_length_le` and `nonlastFins_length_le` for index lists of `Fin k`. Uses them to prove `pointBlock_fixed_length`, a fixed-length statement for a point block.
-/

namespace Paper.F3ChargeCeiling

open TableGeneration TableGeneration.Operations

theorem nonzeroFins_length_le {k : Nat} (hk : 0 < k) :
    (nonzeroFins hk).length ≤ k := by
  simpa [nonzeroFins] using (List.length_filter_le (fun j => decide (j != finZero hk)) (List.finRange k))

theorem nonlastFins_length_le {k : Nat} (hk : 0 < k) :
    (nonlastFins hk).length ≤ k := by
  simpa [nonlastFins] using (List.length_filter_le (fun j => decide (j != finLast hk)) (List.finRange k))

theorem pointBlock_fixed_length {k E : Nat} (hk : 0 < k)
    (hE : k * (k - 1) ≤ E) (p : Point) (hp : PointDyadic k p) :
    (match p with
      | .int _ => SourceFixed (finZero hk) E (opsForPointWithProduct hk p)
      | .frac _ => SourceFixed (finLast hk) E (opsForPointWithProduct hk p)) ∧
      (opsForPointWithProduct hk p).length ≤ 2*k+1 := by
  cases p with
  | int z =>
    have hlocal := computeLocal_fixed_length hk z hp hE
    constructor
    · simp only [opsForPointWithProduct]
      apply sourceFixed_append
      · apply sourceFixed_append hlocal.1
        intro op hop
        simp only [List.mem_singleton] at hop
        subst op
        exact Or.inl ⟨finZero hk, rfl⟩
      · exact sourceFixed_inverse hlocal.1
    · simp only [opsForPointWithProduct, List.length_append,
        List.length_singleton, apply_Op_inverse, List.length_map, List.length_reverse]
      have hlen := nonzeroFins_length_le hk
      omega
  | frac c =>
    by_cases hc : c = 0
    · subst c
      constructor
      · intro op hop
        simp only [opsForPointWithProduct, ↓reduceIte, List.mem_singleton] at hop
        subst op
        exact Or.inl ⟨finLast hk, rfl⟩
      · simp [opsForPointWithProduct]
    · have hlocal := computeFracLocal_fixed_length hk c hp hE
      constructor
      · simp only [opsForPointWithProduct, if_neg hc]
        apply sourceFixed_append
        · apply sourceFixed_append hlocal.1
          intro op hop
          simp only [List.mem_singleton] at hop
          subst op
          exact Or.inl ⟨finLast hk, rfl⟩
        · exact sourceFixed_inverse hlocal.1
      · simp only [opsForPointWithProduct, if_neg hc, List.length_append,
          List.length_singleton, apply_Op_inverse, List.length_map, List.length_reverse]
        have hlen := nonlastFins_length_le hk
        omega

end Paper.F3ChargeCeiling
