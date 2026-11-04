import Provider.Ceiling.PointBlock

/-! # Grouped Words
Defines `integerPoints` and `fractionalPoints` and shows they are integer, fractional and dyadic points. Proves fixed-length statements `intGroup_fixed_length` and `fracGroup_fixed_length`, assembled into `grouped_words_fixed_length`.
-/

namespace Paper.F3ChargeCeiling



open TableGeneration TableGeneration.Operations Paper.F2CatalogTransfer



theorem intGroup_fixed_length {k E : Nat} (hk : 0 < k)

    (hE : k * (k - 1) ≤ E) (pts : List Point)

    (hint : ∀ p ∈ pts, ∃ z, p = .int z)

    (hdyad : ∀ p ∈ pts, PointDyadic k p) :

    SourceFixed (finZero hk) E (genOpsWithProduct hk pts) ∧

      (genOpsWithProduct hk pts).length ≤ pts.length * (2*k+1) := by

  induction pts with

  | nil => simp [genOpsWithProduct, SourceFixed]

  | cons p rest ih =>

    obtain ⟨z, rfl⟩ := hint p (by simp)

    have hp := pointBlock_fixed_length hk hE (.int z) (hdyad _ (by simp))

    have hrint : ∀ p ∈ rest, ∃ z, p = .int z := by

      intro p h

      exact hint p (by simp [h])

    have hrdyad : ∀ p ∈ rest, PointDyadic k p := by

      intro p h

      exact hdyad p (by simp [h])

    have hr := ih hrint hrdyad

    constructor

    · simpa only [genOpsWithProduct] using sourceFixed_append hp.1 hr.1

    · simp only [genOpsWithProduct, List.length_append, List.length_cons]

      nlinarith [hp.2, hr.2]



theorem fracGroup_fixed_length {k E : Nat} (hk : 0 < k)

    (hE : k * (k - 1) ≤ E) (pts : List Point)

    (hfrac : ∀ p ∈ pts, ∃ z, p = .frac z)

    (hdyad : ∀ p ∈ pts, PointDyadic k p) :

    SourceFixed (finLast hk) E (genOpsWithProduct hk pts) ∧

      (genOpsWithProduct hk pts).length ≤ pts.length * (2*k+1) := by

  induction pts with

  | nil => simp [genOpsWithProduct, SourceFixed]

  | cons p rest ih =>

    obtain ⟨z, rfl⟩ := hfrac p (by simp)

    have hp := pointBlock_fixed_length hk hE (.frac z) (hdyad _ (by simp))

    have hrfrac : ∀ p ∈ rest, ∃ z, p = .frac z := by

      intro p h

      exact hfrac p (by simp [h])

    have hrdyad : ∀ p ∈ rest, PointDyadic k p := by

      intro p h

      exact hdyad p (by simp [h])

    have hr := ih hrfrac hrdyad

    constructor

    · simpa only [genOpsWithProduct] using sourceFixed_append hp.1 hr.1

    · simp only [genOpsWithProduct, List.length_append, List.length_cons]

      nlinarith [hp.2, hr.2]



def integerPoints (k : Nat) : List Point :=

  (f2Points k).filter isIntegerPoint



def fractionalPoints (k : Nat) : List Point :=

  (f2Points k).filter (fun p => !isIntegerPoint p)



theorem integerPoints_are_int {k : Nat} {p : Point}

    (hp : p ∈ integerPoints k) : ∃ z, p = .int z := by

  simp only [integerPoints, List.mem_filter] at hp

  cases p with

  | int z => exact ⟨z, rfl⟩

  | frac z => simp [isIntegerPoint] at hp



theorem fractionalPoints_are_frac {k : Nat} {p : Point}

    (hp : p ∈ fractionalPoints k) : ∃ z, p = .frac z := by

  simp only [fractionalPoints, List.mem_filter] at hp

  cases p with

  | int z => simp [isIntegerPoint] at hp

  | frac z => exact ⟨z, rfl⟩



theorem integerPoints_dyadic {k : Nat} (hk : 2 ≤ k)

    {p : Point} (hp : p ∈ integerPoints k) : PointDyadic k p := by

  have h : p ∈ f2Points k := (List.mem_filter.mp hp).1

  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h

  exact f2Point_dyadic hk (List.mem_range.mp hn)



theorem fractionalPoints_dyadic {k : Nat} (hk : 2 ≤ k)

    {p : Point} (hp : p ∈ fractionalPoints k) : PointDyadic k p := by

  have h : p ∈ f2Points k := (List.mem_filter.mp hp).1

  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h

  exact f2Point_dyadic hk (List.mem_range.mp hn)



theorem genOpsWithProduct_append {k : Nat} (hk : 0 < k)

    (first second : List Point) :

    genOpsWithProduct hk (first ++ second) =

      genOpsWithProduct hk first ++ genOpsWithProduct hk second := by

  induction first with

  | nil => rfl

  | cons p ps ih => simp [genOpsWithProduct, ih, List.append_assoc]



theorem grouped_words_fixed_length {k E : Nat} (hk : 2 ≤ k)

    (hE : k * (k - 1) ≤ E) :

    SourceFixed (finZero (positive_of_ge_two hk)) E

      (genOpsWithProduct (positive_of_ge_two hk) (integerPoints k)) ∧

    SourceFixed (finLast (positive_of_ge_two hk)) E

      (genOpsWithProduct (positive_of_ge_two hk) (fractionalPoints k)) ∧

    (genOpsWithProduct (positive_of_ge_two hk) (groupedF2Points k)).length ≤

      (2*k-1)*(2*k+1) := by

  let hk' := positive_of_ge_two hk

  have hi := intGroup_fixed_length hk' hE (integerPoints k)

    (fun p hp => integerPoints_are_int hp)

    (fun p hp => integerPoints_dyadic hk hp)

  have hf := fracGroup_fixed_length hk' hE (fractionalPoints k)

    (fun p hp => fractionalPoints_are_frac hp)

    (fun p hp => fractionalPoints_dyadic hk hp)

  have hlen : (integerPoints k).length + (fractionalPoints k).length = 2*k-1 := by

    have h := groupedF2Points_length k hk

    simp only [groupedF2Points, List.length_append] at h
    change (integerPoints k).length + (fractionalPoints k).length =
      2 * (k - 1) + 1 at h
    omega

  constructor

  · exact hi.1

  constructor

  · exact hf.1

  · have hgen : genOpsWithProduct hk' (groupedF2Points k) =

        genOpsWithProduct hk' (integerPoints k) ++

          genOpsWithProduct hk' (fractionalPoints k) := by

      simpa only [groupedF2Points, integerPoints, fractionalPoints] using
        genOpsWithProduct_append hk' (integerPoints k) (fractionalPoints k)

    rw [hgen, List.length_append]

    nlinarith [hi.2, hf.2]



end Paper.F3ChargeCeiling

