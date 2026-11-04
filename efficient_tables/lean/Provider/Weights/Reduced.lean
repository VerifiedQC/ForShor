import Provider.Weights.Rational
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas

/-!
# Size bounds for the F2 weights

Instantiates the unreduced-fraction bounds for the actual F2 source tables.
It defines explicit bound functions (`inputBound`, `scaleBound`,
`projectiveWeightBound`, `phaseWeightBound`) and proves bounds on the actual
nodes and radix (`actualNodeAndRadixBound`), on the projective weights
(`projectiveWeightsExec_rawBound`) and on the phase weights
(`actualF2_phaseWeightsExec_rawBound`).
-/

/- BEGIN Actual.lean source_sha256=92ae55d8e464ccd13e21c012772d71b2d391af775cbba337e8f208f6a832f967 body_sha256=56e5921a556c9ae92149e69364c95d3a3ef6093fe71b262a9649417b4bfda688 -/

namespace Paper.A4F2Size

open TableGeneration TableGeneration.Operations
open Paper.Normalization Paper.F2CatalogTransfer Paper.A4Exec
open Paper.A4RationalBounds

def pointMagnitudeLocal : Point → Int
  | .int z => z
  | .frac z => z

def PointDyadicLocal (k : Nat) (p : Point) : Prop :=
  ∃ e, e ≤ k ∧ (pointMagnitudeLocal p = 0 ∨
    (pointMagnitudeLocal p).natAbs = 2 ^ e)

lemma f2Point_dyadicLocal {k n : Nat} (hk : 2 ≤ k) (hn : n < 2 * k - 1) :
    PointDyadicLocal k (f2Point n) := by
  by_cases hsmall : n < 4
  · interval_cases n <;> refine ⟨0, by omega, ?_⟩ <;>
      simp [PointDyadicLocal, pointMagnitudeLocal, f2Point]
  · let m := n - 4
    have hnm : n = m + 4 := by dsimp [m]; omega
    have he : 1 + m / 4 ≤ k := by dsimp [m]; omega
    rw [hnm]
    dsimp [f2Point]
    split <;> refine ⟨1 + m / 4, he, Or.inr ?_⟩ <;>
      simp [PointDyadicLocal, pointMagnitudeLocal, Int.natAbs_pow, Int.natAbs_neg]

def inputBound (W k : Nat) : Nat := 2 ^ (W + k + 3)
def scaleBound (k : Nat) : Nat := (2 ^ k) ^ (k - 1)
def outerDim (k : Nat) : Nat := 2 * (k - 1)

lemma rawBound_intCast {B : Nat} (z : Int) (hB : 1 ≤ B)
    (hz : z.natAbs ≤ B) :
    RawBound B (z : ℚ) := by
  refine ⟨z, 1, by norm_num, hz, by simpa using hB, ?_⟩
  simp

lemma rawBound_natCast {B n : Nat} (hB : 1 ≤ B) (hn : n ≤ B) :
    RawBound B (n : ℚ) := by
  refine ⟨n, 1, by norm_num, ?_, hB, ?_⟩
  · simpa using hn
  · simp

lemma pointMagnitude_abs_le {k : Nat} {p : Point} (hp : PointDyadicLocal k p) :
    (pointMagnitudeLocal p).natAbs ≤ 2 ^ k := by
  rcases hp with ⟨e, he, hmag⟩
  rcases hmag with hz | hpow
  · simp [hz]
  · rw [hpow]
    exact Nat.pow_le_pow_right (by norm_num) he

lemma sourcePoint_rawBound {k : Nat} {p : Point} {q : ℚ}
    (hp : PointDyadicLocal k p) (hs : sourcePoint p = some q) :
    RawBound (2 ^ k) q := by
  cases p with
  | int z =>
      have hq : q = (z : ℚ) := by simpa [sourcePoint] using hs.symm
      rw [hq]
      have hB : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
      exact rawBound_intCast (B := 2 ^ k) z hB (by
        simpa [pointMagnitudeLocal] using pointMagnitude_abs_le hp)
  | frac m =>
      by_cases hm : m = 0
      · simp [sourcePoint, hm] at hs
      · have hq : q = (m : ℚ)⁻¹ := by simpa [sourcePoint, hm] using hs.symm
        have hmag : m.natAbs ≤ 2 ^ k := by
          simpa [pointMagnitudeLocal] using pointMagnitude_abs_le hp
        refine ⟨1, m, ?_, ?_, ?_, ?_⟩
        · exact_mod_cast hm
        · exact Nat.one_le_pow _ _ (by positivity)
        · exact hmag
        · rw [hq]
          simp [one_div]

lemma actualPointDyadic {K : Nat} (t : F2Source K) (i : Fin (2 * (t.source.k - 1) + 1)) :
    PointDyadicLocal t.source.k (t.points i) := by
  have hm : t.points i ∈ f2Points t.source.k :=
    t.literalF2.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩)
  obtain ⟨n, hn, hpt⟩ := List.mem_map.mp hm
  rw [← hpt]
  exact f2Point_dyadicLocal t.source.hk (List.mem_range.mp hn)

lemma actualFiniteNodes_rawBound {K : Nat} (t : F2Source K) :
    ∀ i : Fin (outerDim t.source.k), RawBound (2 ^ t.source.k)
      (finiteNodes t.points i) := by
  obtain ⟨hni, hi⟩ := Paper.A4Certificate.f2Source_nodes t
  obtain ⟨_, hfinite, _⟩ :=
    Paper.A4Nodes.finiteNodes_properties t.points hni hi
  intro i
  exact sourcePoint_rawBound
    (actualPointDyadic t (order t.points i.castSucc))
    (hfinite i)

lemma radix_rawBound (W k : Nat) (hk : 2 ≤ k) :
    RawBound (inputBound W k) ((Paper.SignedLimbs.radix W k : Nat) : ℚ) := by
  have hB : 1 ≤ inputBound W k := by
    dsimp [inputBound]
    exact Nat.one_le_pow _ _ (by norm_num)
  have hdiv : W / k ≤ W := Nat.div_le_self _ _
  have he : W / k ≤ W + k + 3 := by omega
  have hradix : (Paper.SignedLimbs.radix W k : Nat) ≤ inputBound W k := by
    dsimp [Paper.SignedLimbs.radix, inputBound]
    exact Nat.pow_le_pow_right (by norm_num) he
  exact rawBound_natCast hB hradix

lemma actualNodeAndRadixBound {K W : Nat} (t : F2Source K) :
    RawBound (inputBound W t.source.k)
      (Paper.SignedLimbs.radix W t.source.k : ℚ) ∧
    ∀ i : Fin (outerDim t.source.k),
      RawBound (inputBound W t.source.k) (finiteNodes t.points i) := by
  have hk := t.source.hk
  refine ⟨radix_rawBound W t.source.k hk, ?_⟩
  intro i
  apply rawBound_mono (B := 2 ^ t.source.k)
  · dsimp [inputBound]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact actualFiniteNodes_rawBound t i

def finiteWeightBound (B d : Nat) : Nat := (4 * B ^ 4) ^ (d - 1)
def infinityWeightBound (B d : Nat) : Nat :=
  2 * (B ^ d * ((2 * (finiteWeightBound B d * B ^ d)) ^ d))
def projectiveWeightBound (B d : Nat) : Nat :=
  max (finiteWeightBound B d) (infinityWeightBound B d)

lemma projectiveWeightsExec_rawBound {d B : Nat} (v : Fin d → ℚ) (b : ℚ)
    (hb : RawBound B b) (hv : ∀ i, RawBound B (v i))
    (hinj : Function.Injective v) :
    ∀ i : Fin (d + 1), RawBound (projectiveWeightBound B d)
      (projectiveWeightsExec v b i) := by
  intro i
  have hgap : ∀ i j : Fin d, i ≠ j → v i ≠ v j := by
    intro i j hij heq
    exact hij (hinj heq)
  cases i using Fin.lastCases with
  | last =>
      apply rawBound_mono (Nat.le_max_right _ _)
      simpa [projectiveWeightsExec] using infinityWeightExec_rawBound v b hb hv hgap
  | cast i =>
      apply rawBound_mono (Nat.le_max_left _ _)
      simpa [projectiveWeightsExec] using finiteWeightExec_rawBound v b i hb hv (by
        intro j hj
        exact hgap i j (Ne.symm (Finset.mem_erase.mp hj).1))

lemma sourceScale_rawBound {k : Nat} {p : Point} (hp : PointDyadicLocal k p) :
    RawBound (scaleBound k) (sourceScale k p) := by
  cases p with
  | int z =>
      have hOne : RawBound 1 (1 : ℚ) := by
        exact ⟨1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      have hle : 1 ≤ scaleBound k := by
        dsimp [scaleBound]
        exact Nat.one_le_pow _ _ (by norm_num [Nat.pow_pos])
      simpa [sourceScale] using rawBound_mono hle hOne
  | frac m =>
      by_cases hm : m = 0
      · have hOne : RawBound 1 (1 : ℚ) := by
          exact ⟨1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
        have hle : 1 ≤ scaleBound k := by
          dsimp [scaleBound]
          exact Nat.one_le_pow _ _ (by norm_num [Nat.pow_pos])
        simpa [sourceScale, hm] using rawBound_mono hle hOne
      · have hmag : m.natAbs ≤ 2 ^ k := by
          simpa [pointMagnitudeLocal] using pointMagnitude_abs_le hp
        have hB : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
        have hmBound := rawBound_intCast (B := 2 ^ k) m hB hmag
        simpa [sourceScale, hm] using rawBound_pow hmBound (k - 1)

lemma sourceScale_ne_zero {k : Nat} (hk : 1 ≤ k) (p : Point) :
    sourceScale k p ≠ 0 := by
  cases p with
  | int z => simp [sourceScale]
  | frac m =>
      by_cases hm : m = 0
      · simp [sourceScale, hm]
      · simp [sourceScale, hm]

def phaseWeightBound (W k : Nat) : Nat :=
  projectiveWeightBound (inputBound W k) (outerDim k) * (scaleBound k) ^ 2

theorem actualF2_phaseWeightsExec_rawBound {K W : Nat} (t : F2Source K) :
    ∀ i : Fin (2 * (t.source.k - 1) + 1),
      RawBound (phaseWeightBound W t.source.k)
        (phaseWeightsExec t.source.k 2 t.points
          (Paper.SignedLimbs.radix W t.source.k : ℚ) i) := by
  let k := t.source.k
  let d := outerDim k
  let B := inputBound W k
  have hvB := actualNodeAndRadixBound (W := W) t
  have hnodes : ∀ j : Fin d, RawBound B (finiteNodes t.points j) := by
    simpa [B, k, d] using hvB.2
  have hb : RawBound B (Paper.SignedLimbs.radix W k : ℚ) := by
    simpa [B, k] using hvB.1
  obtain ⟨hni, hi⟩ := Paper.A4Certificate.f2Source_nodes t
  have hinj : Function.Injective (finiteNodes t.points) :=
    (Paper.A4Nodes.finiteNodes_properties t.points hni hi).1
  intro i
  have hp : PointDyadicLocal k (t.points i) := actualPointDyadic t i
  have hs : RawBound (scaleBound k) (sourceScale k (t.points i)) :=
    sourceScale_rawBound hp
  have hsPow := rawBound_pow hs 2
  have hsne : sourceScale k (t.points i) ^ 2 ≠ 0 :=
    pow_ne_zero _ (sourceScale_ne_zero (by have := t.source.hk; omega) _)
  have hproj : RawBound (projectiveWeightBound B d)
      (projectiveWeightsExec (finiteNodes t.points)
        (Paper.SignedLimbs.radix W k : ℚ) ((order t.points).symm i)) :=
    projectiveWeightsExec_rawBound (finiteNodes t.points)
      (Paper.SignedLimbs.radix W k : ℚ) hb hnodes hinj ((order t.points).symm i)
  have hnorm := rawBound_div hproj hsPow hsne
  simpa [phaseWeightsExec, Paper.Normalization.normalizedWeights,
    phaseWeightBound, B, k, d] using hnorm


end Paper.A4F2Size
/- END Actual.lean -/

/- BEGIN ExponentFix4.lean source_sha256=0092ad80e1392b59349db99d11e6f6f682a2f39d9ab73a0e64f416bd65666e99 body_sha256=f37f6fdc359767aecc56c8c98914cfd51184fd24a5e2f7f5f5fb806f29dabe0e -/

set_option maxHeartbeats 500000

namespace Paper.A4F2Size

open Paper.A4RationalBounds Paper.F2CatalogTransfer Paper.A4Exec Paper.F2CatalogTransfer Paper.A4Exec

def phaseExponent (W k : Nat) : Nat :=
  let s := W + k + 3
  let d := 2 * (k - 1)
  let ef := (2 + 4 * s) * (d - 1)
  let ei := 1 + s * d + d * (1 + ef + s * d)
  ef + ei + 2 * k * (k - 1)

lemma finiteWeightBound_pow (s d : Nat) :
    finiteWeightBound (2 ^ s) d = 2 ^ ((2 + 4 * s) * (d - 1)) := by
  have hb : 4 * (2 ^ s) ^ 4 = 2 ^ (2 + 4 * s) := by
    calc
      4 * (2 ^ s) ^ 4 = 2 ^ 2 * (2 ^ s) ^ 4 := by norm_num
      _ = 2 ^ 2 * 2 ^ (s * 4) := by rw [pow_mul]
      _ = 2 ^ (2 + s * 4) := by rw [← pow_add]
      _ = 2 ^ (2 + 4 * s) := by congr 1 <;> omega
  rw [finiteWeightBound, hb, pow_mul]

lemma infinityWeightBound_pow (s d : Nat) :
    infinityWeightBound (2 ^ s) d =
      2 ^ (1 + s * d + d * (1 + (2 + 4 * s) * (d - 1) + s * d)) := by
  have hF := finiteWeightBound_pow s d
  have hBd : (2 ^ s) ^ d = 2 ^ (s * d) := by rw [pow_mul]
  have hinner : 2 * (2 ^ ((2 + 4 * s) * (d - 1)) * 2 ^ (s * d)) =
      2 ^ (1 + (2 + 4 * s) * (d - 1) + s * d) := by
    calc
      _ = 2 ^ 1 * (2 ^ ((2 + 4 * s) * (d - 1)) * 2 ^ (s * d)) := by norm_num
      _ = (2 ^ 1 * 2 ^ ((2 + 4 * s) * (d - 1))) * 2 ^ (s * d) := by ac_rfl
      _ = 2 ^ (1 + (2 + 4 * s) * (d - 1)) * 2 ^ (s * d) := by rw [← pow_add]
      _ = 2 ^ (1 + (2 + 4 * s) * (d - 1) + s * d) := by rw [← pow_add]
  unfold infinityWeightBound
  rw [hBd, hF, hinner]
  calc
    2 * (2 ^ (s * d) * (2 ^ (1 + (2 + 4 * s) * (d - 1) + s * d)) ^ d)
      = 2 ^ 1 * (2 ^ (s * d) * (2 ^ (1 + (2 + 4 * s) * (d - 1) + s * d)) ^ d) := by norm_num
    _ = 2 ^ 1 * (2 ^ (s * d) * 2 ^ ((1 + (2 + 4 * s) * (d - 1) + s * d) * d)) := by
      congr 2
      rw [pow_mul]
    _ = (2 ^ 1 * 2 ^ (s * d)) * 2 ^ ((1 + (2 + 4 * s) * (d - 1) + s * d) * d) := by ac_rfl
    _ = 2 ^ (1 + s * d) * 2 ^ ((1 + (2 + 4 * s) * (d - 1) + s * d) * d) := by rw [← pow_add]
    _ = 2 ^ (1 + s * d + (1 + (2 + 4 * s) * (d - 1) + s * d) * d) := by rw [← pow_add]
    _ = 2 ^ (1 + s * d + d * (1 + (2 + 4 * s) * (d - 1) + s * d)) := by congr 1 <;> ring

lemma phaseWeightBound_pow_le (W k : Nat) :
    phaseWeightBound W k ≤ 2 ^ phaseExponent W k := by
  let s := W + k + 3
  let d := outerDim k
  let ef := (2 + 4 * s) * (d - 1)
  let ei := 1 + s * d + d * (1 + ef + s * d)
  have hF := finiteWeightBound_pow s d
  have hI := infinityWeightBound_pow s d
  have hmax : projectiveWeightBound (2 ^ s) d ≤ 2 ^ (ef + ei) := by
    unfold projectiveWeightBound
    rw [hF, hI]
    apply Nat.max_le.mpr
    constructor
    · apply Nat.pow_le_pow_right (by norm_num)
      exact Nat.le_add_right _ _
    · apply Nat.pow_le_pow_right (by norm_num)
      exact Nat.le_add_left _ _
  have hscale : scaleBound k ^ 2 = 2 ^ (2 * k * (k - 1)) := by
    change ((2 ^ k) ^ (k - 1)) ^ 2 = 2 ^ (2 * k * (k - 1))
    have hi : (2 ^ k) ^ (k - 1) = 2 ^ (k * (k - 1)) :=
      (Nat.pow_mul 2 k (k - 1)).symm
    calc
      ((2 ^ k) ^ (k - 1)) ^ 2 = (2 ^ (k * (k - 1))) ^ 2 := congrArg (fun x : Nat => x ^ 2) hi
      _ = 2 ^ (k * (k - 1) * 2) := (Nat.pow_mul 2 (k * (k - 1)) 2).symm
      _ = 2 ^ (2 * k * (k - 1)) := congrArg (fun e : Nat => 2 ^ e) (by ring)
  unfold phaseWeightBound
  dsimp [inputBound, outerDim] at hmax ⊢
  rw [hscale]
  calc
    projectiveWeightBound (2 ^ (W + k + 3)) (2 * (k - 1)) *
        2 ^ (2 * k * (k - 1))
      ≤ 2 ^ (ef + ei) * 2 ^ (2 * k * (k - 1)) := Nat.mul_le_mul_right _ hmax
    _ = 2 ^ (ef + ei + 2 * k * (k - 1)) := by rw [← pow_add]
    _ = 2 ^ phaseExponent W k := by
      simp [phaseExponent, s, d, ef, ei, outerDim]

theorem actualF2_phaseWeightsExec_powBound {K W : Nat} (t : F2Source K) :
    ∀ i : Fin (2 * (t.source.k - 1) + 1),
      RawBound (2 ^ phaseExponent W t.source.k)
        (phaseWeightsExec t.source.k 2 t.points
          (Paper.SignedLimbs.radix W t.source.k : ℚ) i) := by
  intro i
  exact rawBound_mono (phaseWeightBound_pow_le W t.source.k)
    (actualF2_phaseWeightsExec_rawBound t i)

end Paper.A4F2Size
/- END ExponentFix4.lean -/

/- BEGIN ReducedFinal.lean source_sha256=23f70fd57c96f8fa61c3c24f90a51e26e29173d40b94d18ffb074fc946860aca body_sha256=58004572c0cf4002473d7947c894327bd6f787ce098b5ba8ce10d80db54653e2 -/

namespace Paper.A4F2Size

open Paper.A4RationalBounds Paper.F2CatalogTransfer Paper.A4Exec

/-- Reducing an integer fraction cannot increase either encoded coordinate. -/
theorem reducedBound_of_rawBound {B : Nat} {q : ℚ} (h : RawBound B q) :
    q.num.natAbs ≤ B ∧ q.den ≤ B := by
  rcases h with ⟨a, b, hb, haB, hbB, hq⟩
  have hqdiv : q = Rat.divInt a b := by
    calc
      q = (a : ℚ) / (b : ℚ) := hq
      _ = Rat.divInt a b := Rat.intCast_div_eq_divInt a b
  constructor
  · by_cases ha : a = 0
    · have hq0 : q = 0 := by rw [hqdiv, ha]; simp
      simp [hq0]
    · have hdiv : q.num ∣ a := by
        rw [hqdiv]
        exact Rat.num_dvd a hb
      exact (Int.natAbs_le_of_dvd_ne_zero hdiv ha).trans haB
  · have hdiv : (q.den : Int) ∣ b := by
      rw [hqdiv]
      exact Rat.den_dvd a b
    have hnat := Int.natAbs_le_of_dvd_ne_zero hdiv hb
    have hle : q.den ≤ b.natAbs := by simpa using hnat
    exact hle.trans hbB

/-- The actual F2 interpolation weights have reduced numerator and denominator
bounded by the same explicit power-of-two bound as their raw representations. -/
theorem actualF2_phaseWeightsExec_reducedBound {K W : Nat} (t : F2Source K) :
    ∀ i : Fin (2 * (t.source.k - 1) + 1),
      (phaseWeightsExec t.source.k 2 t.points
        (Paper.SignedLimbs.radix W t.source.k : ℚ) i).num.natAbs ≤
          2 ^ phaseExponent W t.source.k ∧
      (phaseWeightsExec t.source.k 2 t.points
        (Paper.SignedLimbs.radix W t.source.k : ℚ) i).den ≤
          2 ^ phaseExponent W t.source.k := by
  intro i
  exact reducedBound_of_rawBound (actualF2_phaseWeightsExec_powBound (W := W) t i)
/-- The binary ceiling-log size of each reduced integer coordinate is at most
`phaseExponent`; thus the certificate coordinates have polynomial numeric-parameter
bit length whenever the displayed exponent is expanded as its fixed polynomial. -/
theorem actualF2_phaseWeightsExec_clogBound {K W : Nat} (t : F2Source K) :
    ∀ i : Fin (2 * (t.source.k - 1) + 1),
      Nat.clog 2 (phaseWeightsExec t.source.k 2 t.points
        (Paper.SignedLimbs.radix W t.source.k : ℚ) i).num.natAbs ≤
          phaseExponent W t.source.k ∧
      Nat.clog 2 (phaseWeightsExec t.source.k 2 t.points
        (Paper.SignedLimbs.radix W t.source.k : ℚ) i).den ≤
          phaseExponent W t.source.k := by
  intro i
  rcases actualF2_phaseWeightsExec_reducedBound (W := W) t i with ⟨hn, hd⟩
  exact ⟨Nat.clog_le_of_le_pow hn, Nat.clog_le_of_le_pow hd⟩


end Paper.A4F2Size
/- END ReducedFinal.lean -/

/- BEGIN CapFinal9.lean source_sha256=b07bf369bd8b8a067ce258a35a13725ef6ff3864392d13d0c51ed1c1b513b579 body_sha256=d529241fc4944811afe4f6809358a2ae265c8d0b596d787406410804f4fe7664 -/

namespace Paper.A4F2Size

open Paper.F2CatalogTransfer Paper.A4Exec

/-- A simple fixed-degree cap on the exponent controlling every reduced
interpolation-weight coordinate. This is a numeric-parameter bound. -/
theorem phaseExponent_le_numericPolynomial (W k : Nat) :
    phaseExponent W k ≤ 100 * (W + k + 4) ^ 3 := by
  let H := W + k + 4
  have hH : 4 ≤ H := by dsimp [H]; omega
  have hHpos : 1 ≤ H := by omega
  have hs : W + k + 3 ≤ H := by dsimp [H]; omega
  have hk : k ≤ H := by dsimp [H]; omega
  have hk1 : k - 1 ≤ H := (Nat.sub_le k 1).trans hk
  have hd : 2 * (k - 1) ≤ 2 * H :=
    Nat.mul_le_mul_left 2 hk1
  have hd1 : 2 * (k - 1) - 1 ≤ 2 * H := by omega
  have hcoef : 2 + 4 * (W + k + 3) ≤ 6 * H := by
    dsimp [H]
    omega
  have hef : (2 + 4 * (W + k + 3)) * (2 * (k - 1) - 1) ≤ 12 * H ^ 2 := by
    calc
      _ ≤ (6 * H) * (2 * H) := Nat.mul_le_mul hcoef hd1
      _ = 12 * H ^ 2 := by ring
  have hsd : (W + k + 3) * (2 * (k - 1)) ≤ 2 * H ^ 2 := by
    calc
      _ ≤ H * (2 * H) := Nat.mul_le_mul hs hd
      _ = 2 * H ^ 2 := by ring
  have hinner :
      1 + (2 + 4 * (W + k + 3)) * (2 * (k - 1) - 1) +
          (W + k + 3) * (2 * (k - 1)) ≤ 1 + 14 * H ^ 2 := by
    have h := Nat.add_le_add hef hsd
    omega
  have hdinner :
      2 * (k - 1) *
        (1 + (2 + 4 * (W + k + 3)) * (2 * (k - 1) - 1) +
          (W + k + 3) * (2 * (k - 1))) ≤ 2 * H * (1 + 14 * H ^ 2) :=
    Nat.mul_le_mul hd hinner
  have hei :
      1 + (W + k + 3) * (2 * (k - 1)) +
          2 * (k - 1) *
            (1 + (2 + 4 * (W + k + 3)) * (2 * (k - 1) - 1) +
              (W + k + 3) * (2 * (k - 1))) ≤
        1 + 2 * H ^ 2 + 2 * H * (1 + 14 * H ^ 2) := by
    exact Nat.add_le_add (Nat.add_le_add_left hsd 1) hdinner
  have hscale : 2 * k * (k - 1) ≤ 2 * H ^ 2 := by
    have h2k : 2 * k ≤ 2 * H := Nat.mul_le_mul_left 2 hk
    calc
      2 * k * (k - 1) ≤ (2 * H) * H := Nat.mul_le_mul h2k hk1
      _ = 2 * H ^ 2 := by ring
  have hE : phaseExponent W k ≤ 1 + 16 * H ^ 2 + 2 * H + 28 * H ^ 3 := by
    unfold phaseExponent
    dsimp
    calc
      (2 + 4 * (W + k + 3)) * (2 * (k - 1) - 1) +
          (1 + (W + k + 3) * (2 * (k - 1)) +
            2 * (k - 1) *
              (1 + (2 + 4 * (W + k + 3)) * (2 * (k - 1) - 1) +
                (W + k + 3) * (2 * (k - 1)))) +
          2 * k * (k - 1)
        ≤ (12 * H ^ 2 + (1 + 2 * H ^ 2 + 2 * H * (1 + 14 * H ^ 2))) + 2 * H ^ 2 :=
          Nat.add_le_add (Nat.add_le_add hef hei) hscale
      _ = 1 + 16 * H ^ 2 + 2 * H + 28 * H ^ 3 := by ring
  have hH3 : 1 ≤ H ^ 3 := Nat.one_le_pow 3 H (by omega)
  have hH2le3 : H ^ 2 ≤ H ^ 3 := by
    calc
      H ^ 2 = H ^ 2 * 1 := by simp
      _ ≤ H ^ 2 * H := Nat.mul_le_mul_left _ hHpos
      _ = H ^ 3 := by simp [pow_succ]
  have hHle2 : H ≤ H ^ 2 := by
    calc
      H = H * 1 := by simp
      _ ≤ H * H := Nat.mul_le_mul_left _ hHpos
      _ = H ^ 2 := by rw [pow_two]
  have hHle3 : H ≤ H ^ 3 := hHle2.trans hH2le3
  have hsmall : 1 + 16 * H ^ 2 + 2 * H ≤ 19 * H ^ 3 := by
    calc
      1 + 16 * H ^ 2 + 2 * H ≤ H ^ 3 + 16 * H ^ 3 + 2 * H ^ 3 :=
        Nat.add_le_add (Nat.add_le_add hH3 (Nat.mul_le_mul_left 16 hH2le3))
          (Nat.mul_le_mul_left 2 hHle3)
      _ = 19 * H ^ 3 := by ring
  have hfinal : 1 + 16 * H ^ 2 + 2 * H + 28 * H ^ 3 ≤ 100 * H ^ 3 := by
    calc
      _ ≤ 19 * H ^ 3 + 28 * H ^ 3 := Nat.add_le_add_right hsmall _
      _ = 47 * H ^ 3 := by ring
      _ ≤ 100 * H ^ 3 := Nat.mul_le_mul_right _ (by omega)
  exact hE.trans (by simpa [H] using hfinal)

/-- Binary coordinate sizes for the actual certificate are bounded by this
explicit cubic polynomial in numeric W and k. -/
theorem actualF2_phaseWeightsExec_clogPolynomial {K W : Nat} (t : F2Source K) :
    ∀ i : Fin (2 * (t.source.k - 1) + 1),
      Nat.clog 2 (phaseWeightsExec t.source.k 2 t.points
        (Paper.SignedLimbs.radix W t.source.k : ℚ) i).num.natAbs ≤
          100 * (W + t.source.k + 4) ^ 3 ∧
      Nat.clog 2 (phaseWeightsExec t.source.k 2 t.points
        (Paper.SignedLimbs.radix W t.source.k : ℚ) i).den ≤
          100 * (W + t.source.k + 4) ^ 3 := by
  intro i
  rcases actualF2_phaseWeightsExec_clogBound (W := W) t i with ⟨hn, hd⟩
  exact ⟨hn.trans (phaseExponent_le_numericPolynomial W t.source.k),
    hd.trans (phaseExponent_le_numericPolynomial W t.source.k)⟩

/-- `Nat.log2` is bounded by the exponent of any power-of-two upper bound. -/
theorem log2_le_of_le_pow2 {x E : Nat} (h : x ≤ 2 ^ E) : Nat.log2 x ≤ E := by
  by_cases hx : x = 0
  · simp [hx]
  · have hp : 2 ^ E < 2 ^ (E + 1) := by
      rw [Nat.pow_succ]
      nlinarith [Nat.one_le_pow E 2 (by omega : 1 ≤ 2)]
    have hxlt : x < 2 ^ (E + 1) := lt_of_le_of_lt h hp
    rw [Nat.log2_eq_log_two]
    have := (Nat.log_lt_iff_lt_pow (by omega : 1 < 2) hx).2 hxlt
    omega

/-- Explicit signed numerator plus denominator binary-coordinate encoding bound. -/
theorem actualF2_phaseWeightsExec_binaryBits {K W : Nat} (t : F2Source K) :
    ∀ i : Fin (2 * (t.source.k - 1) + 1),
      Nat.log2 (phaseWeightsExec t.source.k 2 t.points
        (Paper.SignedLimbs.radix W t.source.k : ℚ) i).num.natAbs + 2 +
      (Nat.log2 (phaseWeightsExec t.source.k 2 t.points
        (Paper.SignedLimbs.radix W t.source.k : ℚ) i).den + 1) ≤
        200 * (W + t.source.k + 4) ^ 3 + 3 := by
  intro i
  rcases actualF2_phaseWeightsExec_reducedBound (W := W) t i with ⟨hn, hd⟩
  have hln := log2_le_of_le_pow2 hn
  have hld := log2_le_of_le_pow2 hd
  have hcap := phaseExponent_le_numericPolynomial W t.source.k
  omega

end Paper.A4F2Size
/- END CapFinal9.lean -/
