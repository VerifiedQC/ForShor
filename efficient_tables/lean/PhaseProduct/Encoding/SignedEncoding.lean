import Model.Interpreter.ValueBoundsPrefixes

/-!
# Signed two's-complement encoding

A strict magnitude bound gives a faithful signed encoding
(`toInt_ofInt_of_natAbs_lt`). Registers and recorded markers after a successful
prefix then have such an encoding (`successful_prefix_signed_encoding`), and the
original source width is itself the signed length
(`source_successful_prefix_signed_encoding`).
-/

namespace Paper.SignedEncoding

/-- A strict magnitude bound gives a faithful signed two's-complement encoding
with one additional sign bit. -/
theorem toInt_ofInt_of_natAbs_lt (p : Nat) (v : Int)
    (hv : v.natAbs < 2 ^ p) :
    (BitVec.ofInt (p + 1) v).toInt = v := by
  have hcast : (v.natAbs : Int) < (2 : Int) ^ p := by
    exact_mod_cast hv
  have hu : v < (2 : Int) ^ p := lt_of_le_of_lt Int.le_natAbs hcast
  have hneg : -v ≤ (v.natAbs : Int) := by
    simpa using (Int.le_natAbs (a := -v))
  have hl : -(2 : Int) ^ p ≤ v := by omega
  exact BitVec.toInt_ofInt_eq_self (by omega)
    (by simpa only [Nat.add_one_sub_one] using hl)
    (by simpa only [Nat.add_one_sub_one] using hu)

/-- Each register and recorded product marker after a successful prefix has an
exact signed BitVec encoding at the peak allocated for the whole program. -/
theorem successful_prefix_signed_encoding {k : Nat}
    (pre suffix : List (Paper.FullDSL.Instruction k))
    (w : Paper.Scanner.Widths k)
    (v mid : Paper.ValueSemantics.Values k) (marks : List Int)
    (hinit : Paper.ValueBounds.Fits w v)
    (hprefix : Paper.ValueSemantics.valueTrace pre v = some (mid, marks)) :
    (∀ i, (BitVec.ofInt
      ((Paper.Scanner.scan (Paper.FullDSL.widthWord (pre ++ suffix))
        (Paper.Scanner.fresh w)).peak + 1) (mid i)).toInt = mid i) ∧
    (∀ z ∈ marks, (BitVec.ofInt
      ((Paper.Scanner.scan (Paper.FullDSL.widthWord (pre ++ suffix))
        (Paper.Scanner.fresh w)).peak + 1) z).toInt = z) := by
  obtain ⟨hr, hm⟩ := Paper.ValueBounds.successful_prefix_below_full_peak
    pre suffix w v mid marks hinit hprefix
  constructor
  · intro i
    exact toInt_ofInt_of_natAbs_lt _ _ (hr i)
  · intro z hz
    exact toInt_ofInt_of_natAbs_lt _ _ (hm z hz)

/-- The original balanced source width itself is the signed BitVec length;
starting limb bounds and prefix execution remain explicit premises. -/
theorem source_successful_prefix_signed_encoding {k : Nat} (width : Nat)
    (pre suffix : TableGeneration.Prog k)
    (x mid : Paper.ValueSemantics.Values k) (marks : List Int)
    (hinit : Paper.ValueBounds.Fits
      (Paper.ArrayBridge.literalSourceSplit width k) x)
    (hprefix : Paper.ValueSemantics.valueTrace
      (Paper.SourceBridge.mapToFull pre) x = some (mid, marks)) :
    (∀ i, (BitVec.ofInt
      (TableGeneration.RecursiveCost.nextBalancedSignedWidth
        width (pre ++ suffix)) (mid i)).toInt = mid i) ∧
    (∀ z ∈ marks, (BitVec.ofInt
      (TableGeneration.RecursiveCost.nextBalancedSignedWidth
        width (pre ++ suffix)) z).toInt = z) := by
  obtain ⟨hr, hm⟩ := Paper.ValueBounds.source_successful_prefix_signed_bound
    width pre suffix x mid marks hinit hprefix
  have hpos : 0 < TableGeneration.RecursiveCost.nextBalancedSignedWidth
      width (pre ++ suffix) := by
    rw [Paper.ArrayBridge.nextBalancedSignedWidth_eq_full_widthWord]
    omega
  have hsize : TableGeneration.RecursiveCost.nextBalancedSignedWidth
      width (pre ++ suffix) - 1 + 1 =
      TableGeneration.RecursiveCost.nextBalancedSignedWidth
        width (pre ++ suffix) := by omega
  constructor
  · intro i
    have henc := toInt_ofInt_of_natAbs_lt
      (TableGeneration.RecursiveCost.nextBalancedSignedWidth
        width (pre ++ suffix) - 1) (mid i) (hr i)
    rw [hsize] at henc
    exact henc
  · intro z hz
    have henc := toInt_ofInt_of_natAbs_lt
      (TableGeneration.RecursiveCost.nextBalancedSignedWidth
        width (pre ++ suffix) - 1) z (hm z hz)
    rw [hsize] at henc
    exact henc

end Paper.SignedEncoding
