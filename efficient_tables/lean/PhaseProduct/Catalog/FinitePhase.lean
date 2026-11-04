import PhaseProduct.Encoding.BitTrace
import PhaseProduct.Catalog.ValuePhase

/-!
# Finite phase-product identity

At the source scanner width a successful integer trace supplies native markers
(`native_markers_of_valueTrace`). It then gives one weight vector working for
every real phase scale and input, for pair and triple words
(`source_pair_finite_phase_product_exists`,
`source_triple_finite_phase_product_exists`), and for the original best-known
words (`bestKnown_pair_finite_phase_product`,
`bestKnown_triple_finite_phase_product`).
-/

open scoped BigOperators

namespace Paper.FinitePhase

/-- At the original source scanner width, a successful integer trace supplies
the same ordered markers in actual native BitVec execution. -/
theorem native_markers_of_valueTrace {k : Nat} (width : Nat)
    (ops : TableGeneration.Prog k)
    (x : Paper.ValueSemantics.Values k) (xs : List Int)
    (hfit : Paper.ValueBounds.Fits
      (Paper.ArrayBridge.literalSourceSplit width k) x)
    (htrace : Paper.ValueSemantics.valueTrace
      (Paper.SourceBridge.mapToFull ops) x = some (x, xs)) :
    let B := TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops
    ∃ ms : List (BitVec B),
      Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
        (Paper.BitStep.encode (B := B) x) =
          some (Paper.BitStep.encode (B := B) x, ms) ∧
      ms.map BitVec.toInt = xs := by
  dsimp
  have he := Paper.BitStep.source_bitTrace_eq_map_valueTrace width ops x hfit
  dsimp at he
  rw [htrace] at he
  simp only [Option.map_some] at he
  refine ⟨xs.map (BitVec.ofInt
    (TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops)), he, ?_⟩
  have hd := Paper.BitStep.source_bitTrace_decode_eq_valueTrace width ops x hfit
  dsimp at hd
  rw [he, htrace] at hd
  simp only [Option.map_some] at hd
  exact congrArg Prod.snd (Option.some.inj hd)

/-- One pair weight vector works for every real phase scale and every pair of
integer inputs that fit the source's initial limb bounds. The markers come
from actual native BitVec execution. -/
theorem source_pair_finite_phase_product_exists {k q : Nat} (hk : k > 0)
    (width : Nat) (ops : TableGeneration.Prog k)
    (pts : Fin q → TableGeneration.Operations.Point) (base : Fin k → ℚ)
    (hcontract : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops (List.ofFn pts))
    (hweights : ∃ weight : Fin q → ℚ,
      Paper.PhaseIdentity.PairCertificate weight
        (Paper.GenericPhase.indexedSourceRows pts) base) :
    let B := TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops
    ∃ weight : Fin q → ℚ, ∀ theta : ℝ,
      ∀ x z : Paper.ValueSemantics.Values k,
      Paper.ValueBounds.Fits (Paper.ArrayBridge.literalSourceSplit width k) x →
      Paper.ValueBounds.Fits (Paper.ArrayBridge.literalSourceSplit width k) z →
      ∃ mx mz : List (BitVec B),
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) x) =
            some (Paper.BitStep.encode (B := B) x, mx) ∧
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) z) =
            some (Paper.BitStep.encode (B := B) z, mz) ∧
        mx.length = q ∧ mz.length = q ∧
        (∏ l : Fin q, Paper.ValuePhase.phaseCharacter theta
          (weight l * ((mx.map BitVec.toInt).getD l.val 0 : ℚ) *
            ((mz.map BitVec.toInt).getD l.val 0 : ℚ))) =
          Paper.ValuePhase.phaseCharacter theta
            (Paper.PhaseIdentity.linearForm base (fun j => (x j : ℚ)) *
             Paper.PhaseIdentity.linearForm base (fun j => (z j : ℚ))) := by
  dsimp
  obtain ⟨weight, hall⟩ := Paper.ValuePhase.source_pair_phase_product_exists
    hk ops pts base hcontract hweights
  refine ⟨weight, ?_⟩
  intro theta x z hfx hfz
  obtain ⟨xs, zs, hx, hz, hxl, hzl, hphase⟩ := hall theta x z
  obtain ⟨mx, hmx, hdx⟩ :=
    native_markers_of_valueTrace width ops x xs hfx hx
  obtain ⟨mz, hmz, hdz⟩ :=
    native_markers_of_valueTrace width ops z zs hfz hz
  refine ⟨mx, mz, hmx, hmz, ?_, ?_, ?_⟩
  · have hlen := congrArg List.length hdx
    simp only [List.length_map] at hlen
    exact hlen.trans hxl
  · have hlen := congrArg List.length hdz
    simp only [List.length_map] at hlen
    exact hlen.trans hzl
  · rw [hdx, hdz]
    exact hphase

/-- The triple analogue retains one weight vector before all phase scales
and all bounded input triples. -/
theorem source_triple_finite_phase_product_exists {k q : Nat} (hk : k > 0)
    (width : Nat) (ops : TableGeneration.Prog k)
    (pts : Fin q → TableGeneration.Operations.Point) (base : Fin k → ℚ)
    (hcontract : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops (List.ofFn pts))
    (hweights : ∃ weight : Fin q → ℚ,
      Paper.PhaseIdentity.TripleCertificate weight
        (Paper.GenericPhase.indexedSourceRows pts) base) :
    let B := TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops
    ∃ weight : Fin q → ℚ, ∀ theta : ℝ,
      ∀ x y z : Paper.ValueSemantics.Values k,
      Paper.ValueBounds.Fits (Paper.ArrayBridge.literalSourceSplit width k) x →
      Paper.ValueBounds.Fits (Paper.ArrayBridge.literalSourceSplit width k) y →
      Paper.ValueBounds.Fits (Paper.ArrayBridge.literalSourceSplit width k) z →
      ∃ mx my mz : List (BitVec B),
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) x) =
            some (Paper.BitStep.encode (B := B) x, mx) ∧
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) y) =
            some (Paper.BitStep.encode (B := B) y, my) ∧
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) z) =
            some (Paper.BitStep.encode (B := B) z, mz) ∧
        mx.length = q ∧ my.length = q ∧ mz.length = q ∧
        (∏ l : Fin q, Paper.ValuePhase.phaseCharacter theta
          (weight l * ((mx.map BitVec.toInt).getD l.val 0 : ℚ) *
            ((my.map BitVec.toInt).getD l.val 0 : ℚ) *
            ((mz.map BitVec.toInt).getD l.val 0 : ℚ))) =
          Paper.ValuePhase.phaseCharacter theta
            (Paper.PhaseIdentity.linearForm base (fun j => (x j : ℚ)) *
             Paper.PhaseIdentity.linearForm base (fun j => (y j : ℚ)) *
             Paper.PhaseIdentity.linearForm base (fun j => (z j : ℚ))) := by
  dsimp
  obtain ⟨weight, hall⟩ := Paper.ValuePhase.source_triple_phase_product_exists
    hk ops pts base hcontract hweights
  refine ⟨weight, ?_⟩
  intro theta x y z hfx hfy hfz
  obtain ⟨xs, ys, zs, hx, hy, hz, hxl, hyl, hzl, hphase⟩ := hall theta x y z
  obtain ⟨mx, hmx, hdx⟩ :=
    native_markers_of_valueTrace width ops x xs hfx hx
  obtain ⟨my, hmy, hdy⟩ :=
    native_markers_of_valueTrace width ops y ys hfy hy
  obtain ⟨mz, hmz, hdz⟩ :=
    native_markers_of_valueTrace width ops z zs hfz hz
  refine ⟨mx, my, mz, hmx, hmy, hmz, ?_, ?_, ?_, ?_⟩
  · have hlen := congrArg List.length hdx
    simp only [List.length_map] at hlen
    exact hlen.trans hxl
  · have hlen := congrArg List.length hdy
    simp only [List.length_map] at hlen
    exact hlen.trans hyl
  · have hlen := congrArg List.length hdz
    simp only [List.length_map] at hlen
    exact hlen.trans hzl
  · rw [hdx, hdy, hdz]
    exact hphase

/-- The original BestKnown pair word, including its protected source
contract, has the finite native trace phase identity at its actual scanner
width for every bounded pair of integer inputs. -/
theorem bestKnown_pair_finite_phase_product (k : Nat) (hk : 2 ≤ k)
    (width : Nat) (b : ℚ) :
    let ops := TableGeneration.bestKnownGenerate .PhaseProduct k hk
    let B := TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops
    ∃ weight : Fin (2*(k-1)+1) → ℚ, ∀ theta : ℝ,
      ∀ x z : Paper.ValueSemantics.Values k,
      Paper.ValueBounds.Fits (Paper.ArrayBridge.literalSourceSplit width k) x →
      Paper.ValueBounds.Fits (Paper.ArrayBridge.literalSourceSplit width k) z →
      ∃ mx mz : List (BitVec B),
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) x) =
            some (Paper.BitStep.encode (B := B) x, mx) ∧
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) z) =
            some (Paper.BitStep.encode (B := B) z, mz) ∧
        mx.length = 2*k-1 ∧ mz.length = 2*k-1 ∧
        (∏ l, Paper.ValuePhase.phaseCharacter theta
          (weight l * ((mx.map BitVec.toInt).getD l.val 0 : ℚ) *
            ((mz.map BitVec.toInt).getD l.val 0 : ℚ))) =
          Paper.ValuePhase.phaseCharacter theta
            ((∑ j : Fin k, b^j.val * (x j : ℚ)) *
             (∑ j : Fin k, b^j.val * (z j : ℚ))) := by
  dsimp
  obtain ⟨weight, hall⟩ :=
    Paper.ValuePhase.bestKnown_pair_phase_product k hk b
  refine ⟨weight, ?_⟩
  intro theta x z hfx hfz
  obtain ⟨xs, zs, hx, hz, hxl, hzl, hphase⟩ := hall theta x z
  obtain ⟨mx, hmx, hdx⟩ := native_markers_of_valueTrace width
    (TableGeneration.bestKnownGenerate .PhaseProduct k hk) x xs hfx hx
  obtain ⟨mz, hmz, hdz⟩ := native_markers_of_valueTrace width
    (TableGeneration.bestKnownGenerate .PhaseProduct k hk) z zs hfz hz
  refine ⟨mx, mz, hmx, hmz, ?_, ?_, ?_⟩
  · have hlen := congrArg List.length hdx
    simp only [List.length_map] at hlen
    exact hlen.trans hxl
  · have hlen := congrArg List.length hdz
    simp only [List.length_map] at hlen
    exact hlen.trans hzl
  · rw [hdx, hdz]
    exact hphase

/-- The corresponding original BestKnown triple word has one fixed weight
vector for every real phase scale and bounded integer input triple. -/
theorem bestKnown_triple_finite_phase_product (k : Nat) (hk : 2 ≤ k)
    (width : Nat) (b : ℚ) :
    let ops := TableGeneration.bestKnownGenerate .PhaseTripleProduct k hk
    let B := TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops
    ∃ weight : Fin (3*(k-1)+1) → ℚ, ∀ theta : ℝ,
      ∀ x y z : Paper.ValueSemantics.Values k,
      Paper.ValueBounds.Fits (Paper.ArrayBridge.literalSourceSplit width k) x →
      Paper.ValueBounds.Fits (Paper.ArrayBridge.literalSourceSplit width k) y →
      Paper.ValueBounds.Fits (Paper.ArrayBridge.literalSourceSplit width k) z →
      ∃ mx my mz : List (BitVec B),
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) x) =
            some (Paper.BitStep.encode (B := B) x, mx) ∧
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) y) =
            some (Paper.BitStep.encode (B := B) y, my) ∧
        Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull ops)
          (Paper.BitStep.encode (B := B) z) =
            some (Paper.BitStep.encode (B := B) z, mz) ∧
        mx.length = 3*k-2 ∧ my.length = 3*k-2 ∧ mz.length = 3*k-2 ∧
        (∏ l, Paper.ValuePhase.phaseCharacter theta
          (weight l * ((mx.map BitVec.toInt).getD l.val 0 : ℚ) *
            ((my.map BitVec.toInt).getD l.val 0 : ℚ) *
            ((mz.map BitVec.toInt).getD l.val 0 : ℚ))) =
          Paper.ValuePhase.phaseCharacter theta
            ((∑ j : Fin k, b^j.val * (x j : ℚ)) *
             (∑ j : Fin k, b^j.val * (y j : ℚ)) *
             (∑ j : Fin k, b^j.val * (z j : ℚ))) := by
  dsimp
  obtain ⟨weight, hall⟩ :=
    Paper.ValuePhase.bestKnown_triple_phase_product k hk b
  refine ⟨weight, ?_⟩
  intro theta x y z hfx hfy hfz
  obtain ⟨xs, ys, zs, hx, hy, hz, hxl, hyl, hzl, hphase⟩ := hall theta x y z
  obtain ⟨mx, hmx, hdx⟩ := native_markers_of_valueTrace width
    (TableGeneration.bestKnownGenerate .PhaseTripleProduct k hk) x xs hfx hx
  obtain ⟨my, hmy, hdy⟩ := native_markers_of_valueTrace width
    (TableGeneration.bestKnownGenerate .PhaseTripleProduct k hk) y ys hfy hy
  obtain ⟨mz, hmz, hdz⟩ := native_markers_of_valueTrace width
    (TableGeneration.bestKnownGenerate .PhaseTripleProduct k hk) z zs hfz hz
  refine ⟨mx, my, mz, hmx, hmy, hmz, ?_, ?_, ?_, ?_⟩
  · have hlen := congrArg List.length hdx
    simp only [List.length_map] at hlen
    exact hlen.trans hxl
  · have hlen := congrArg List.length hdy
    simp only [List.length_map] at hlen
    exact hlen.trans hyl
  · have hlen := congrArg List.length hdz
    simp only [List.length_map] at hlen
    exact hlen.trans hzl
  · rw [hdx, hdy, hdz]
    exact hphase

end Paper.FinitePhase
