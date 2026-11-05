import ILPEncoding.Bounds.Products
import ILPEncoding.Bounds.StopBudget

/-! # Canonical Leaf Bound
Proves `leaf_tauExact_le`, which bounds the leaf price at `tauExact` by `2004 * (U + 1) ^ 6` when the arguments are at most `U`, and `canonical_leaf_bound` for a label list.
-/

namespace Paper.F7LeafCanon

open Paper.AffineNat Paper.F6Objective Paper.F7Products Paper.F7QControl
open Paper.PPEndToEnd Paper.CountStage.StopBudget

theorem leaf_tauExact_le (N z U : Nat)
    (hN : N ≤ U) (hz : z ≤ U) :
    leafPP tauExact N z ≤ 2004 * (U + 1) ^ 6 := by
  let R := N * z ^ 2
  have hR : R ≤ U ^ 3 := by
    dsimp [R]
    have hz2 : z ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hz 2
    have hm := Nat.mul_le_mul hN hz2
    simpa [pow_succ, pow_zero, mul_assoc] using hm
  have htau := tauExact_le_thousand_mul_succ R
  have hleaf : leafPP tauExact N z ≤ 4 * R + R * (1000 * (R + 1)) := by
    unfold leafPP R
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ htau) _
  have hcube : U ^ 3 ≤ (U + 1) ^ 3 :=
    Nat.pow_le_pow_left (Nat.le_succ U) 3
  have hcube1 : 1 ≤ (U + 1) ^ 3 := by
    have hpos : 0 < (U + 1) ^ 3 := by positivity
    omega
  have hpoly : 4 * R + R * (1000 * (R + 1)) ≤
      2004 * (U + 1) ^ 6 := by
    have hRbig : R ≤ (U + 1) ^ 3 := le_trans hR hcube
    have h1 : 4 * R ≤ 4 * (U + 1) ^ 3 :=
      Nat.mul_le_mul_left 4 hRbig
    have h2 : R * (1000 * (R + 1)) ≤
        (U + 1) ^ 3 * (1000 * ((U + 1) ^ 3 + 1)) := by
      gcongr
    have h3 : (U + 1) ^ 3 * (1000 * ((U + 1) ^ 3 + 1)) ≤
        2000 * (U + 1) ^ 6 := by
      have hCubeSq : (U + 1) ^ 6 = ((U + 1) ^ 3) ^ 2 := by ring
      nlinarith [hCubeSq]
    nlinarith [h1, h2, h3]
  exact hleaf.trans hpoly

theorem canonical_leaf_bound (labels : List Label) (U z : Nat)
    (hbudget : qWord labels ≤ U) (hz : z ≤ U) :
    leafPP tauExact (finalN 1 labels) z ≤ 2004 * (U + 1) ^ 6 := by
  apply leaf_tauExact_le _ _ U
  · exact finalN_le_budget labels U hbudget
  · exact hz

end Paper.F7LeafCanon

