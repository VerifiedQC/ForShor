import Mathlib
import ILPEncoding.Bounds.StopBudget
import ILPEncoding.Bundles.MatrixOptimizer

/-!
# Threshold encodings and census lemmas

Counting and encoding lemmas for threshold pairs `(k, B)`: framed codes whose
lengths are computed (`thresholdBits_length`, `thresholdCode_injective`), a
bounded census of yes-pairs (`boundedYesPairCensus_card_le`), and the count of
canonical binary-width values (`canonicalBinaryWidthValues_card`). It also
relates the actual benchmark optimum to the root-stop envelope
`thresholdEnvelope` (`actualBenchmarkOpt_le_envelope`). These are census and
encoding lemmas only; this file is not a sparseness theorem.
-/

set_option autoImplicit false

namespace ExecutionAlignment.SparseThreshold

open Paper.CountStage.StopBudget

/-- Accepted numeric polynomial envelope for the root-stop cost. -/
def thresholdEnvelope (k : Nat) : Nat := 2004 * k ^ 4

/-- Yes predicate for the actual numeric objective `opt`, not for its envelope. -/
def thresholdYes (opt : Nat → Nat) (k B : Nat) : Prop := opt k ≤ B

inductive ThresholdSymbol where
  | unary
  | separator
  | bit (value : Bool)
  deriving DecidableEq, Repr

/-- Exactly `log₂(B)+1` little-endian bits, indexed by position. -/
def binaryBits (B : Nat) : List Bool :=
  List.ofFn (fun i : Fin (Nat.log2 B + 1) => Nat.testBit B i)

/-- A canonical framed code: k unary marks, a separator, then a fixed-width bit field. -/
def thresholdCode (k B : Nat) : List ThresholdSymbol :=
  List.replicate k .unary ++ [.separator] ++ (binaryBits B).map .bit

def thresholdCodeLength (k B : Nat) : Nat := k + 1 + Nat.log2 B + 1

/-- Literal Boolean-list frame for the clipped-binary auxiliary language:
`0^k 1 binary(B)`. The separator makes the unary prefix uniquely parseable. -/
def thresholdBits (k B : Nat) : List Bool :=
  List.replicate k false ++ [true] ++ binaryBits B

/-- The original tally frame used in the hardness notes: `1^k 0 1^B`.
This remains a distinct encoding from the clipped-binary auxiliary. -/
def tallyThresholdBits (k B : Nat) : List Bool :=
  List.replicate k true ++ [false] ++ List.replicate B true

theorem binaryBits_length (B : Nat) : (binaryBits B).length = Nat.log2 B + 1 := by
  simp [binaryBits]

theorem thresholdBits_length (k B : Nat) :
    (thresholdBits k B).length = thresholdCodeLength k B := by
  simp [thresholdBits, thresholdCodeLength, binaryBits_length] <;> omega

theorem tallyThresholdBits_length (k B : Nat) :
    (tallyThresholdBits k B).length = k + B + 1 := by
  simp [tallyThresholdBits, Nat.add_assoc]

theorem tallyThresholdBits_injective :
    Function.Injective (fun p : Nat × Nat => tallyThresholdBits p.1 p.2) := by
  intro a b hab
  have hu := congrArg (List.takeWhile id) hab
  have hk : a.1 = b.1 := by
    have hlen := congrArg List.length hu
    simpa [tallyThresholdBits] using hlen
  have hd := congrArg (List.drop (a.1 + 1)) hab
  have hB : a.2 = b.2 := by
    have hlen := congrArg List.length hd
    simp only [tallyThresholdBits, hk, List.length_drop, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil] at hlen
    omega
  exact Prod.ext hk hB
theorem binaryBits_injective : Function.Injective binaryBits := by
  intro a b hab
  have hw : Nat.log2 a = Nat.log2 b := by
    have := congrArg List.length hab
    simpa [binaryBits] using this
  have hab' : binaryBits a = binaryBits b := by simpa [hw] using hab
  have hfun : (fun i : Fin (Nat.log2 a + 1) => Nat.testBit a i) =
      (fun i : Fin (Nat.log2 a + 1) => Nat.testBit b i) := by
    apply List.ofFn_injective
    simpa [binaryBits, hw] using hab'
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < Nat.log2 a + 1
  · exact congrFun hfun ⟨i, hi⟩
  · have hi' : Nat.log2 a + 1 ≤ i := by omega
    have ha : a < 2 ^ (Nat.log2 a + 1) := by
      by_cases hz : a = 0
      · simp [hz]
      · exact (Nat.log2_lt hz).mp (by omega)
    have hb : b < 2 ^ (Nat.log2 b + 1) := by
      by_cases hz : b = 0
      · simp [hz]
      · exact (Nat.log2_lt hz).mp (by omega)
    have hp : 2 ^ (Nat.log2 a + 1) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by decide) hi'
    have hpa : a < 2 ^ i := ha.trans_le hp
    have hpb : b < 2 ^ i := by simpa [hw] using hb.trans_le (by simpa [hw] using hp)
    rw [Nat.testBit_eq_false_of_lt hpa, Nat.testBit_eq_false_of_lt hpb]

theorem thresholdBits_injective :
    Function.Injective (fun p : Nat × Nat => thresholdBits p.1 p.2) := by
  intro a b hab
  have hu := congrArg (List.takeWhile (fun x => !x)) hab
  have hk : a.1 = b.1 := by
    have hlen := congrArg List.length hu
    simpa [thresholdBits] using hlen
  have hd := congrArg (List.drop (a.1 + 1)) hab
  have hb : binaryBits a.2 = binaryBits b.2 := by
    simpa [thresholdBits, hk, List.drop_append] using hd
  exact Prod.ext hk (binaryBits_injective hb)

theorem thresholdCode_injective : Function.Injective (fun p : Nat × Nat => thresholdCode p.1 p.2) := by
  intro a b h
  have hu := congrArg (List.takeWhile (fun s => decide (s = .unary))) h
  have hk : a.1 = b.1 := by
    have hlen := congrArg List.length hu
    simpa [thresholdCode] using hlen
  have hd := congrArg (List.drop (a.1 + 1)) h
  have hb : (binaryBits a.2).map ThresholdSymbol.bit =
      (binaryBits b.2).map ThresholdSymbol.bit := by
    simpa [thresholdCode, hk, List.drop_append] using hd
  have hmap : Function.Injective (ThresholdSymbol.bit : Bool → ThresholdSymbol) := by
    intro x y hxy
    cases hxy
    rfl
  have hbits : binaryBits a.2 = binaryBits b.2 :=
    (List.map_injective_iff.mpr hmap) hb
  have hv := binaryBits_injective hbits
  exact Prod.ext hk hv

theorem thresholdCode_length (k B : Nat) :
    (thresholdCode k B).length = thresholdCodeLength k B := by
  simp [thresholdCode, thresholdCodeLength, binaryBits_length, List.length_map] <;> omega

theorem unary_parameter_le_code_length (k B : Nat) :
    k ≤ thresholdCodeLength k B := by
  unfold thresholdCodeLength
  omega

theorem thresholdEnvelope_mono {a b : Nat} (hab : a ≤ b) :
    thresholdEnvelope a ≤ thresholdEnvelope b := by
  unfold thresholdEnvelope
  exact Nat.mul_le_mul_left 2004 ((Nat.pow_le_pow_left hab) 4)

theorem rootThreshold_fits_envelope {k : Nat} (hk : 1 ≤ k) :
    rootStopBudget k ≤ thresholdEnvelope k := rootStopBudget_le_2004_n4 hk

/-- Finite census of yes pairs for any optimization objective. -/
def boundedYesPairCensus (opt : Nat → Nat) (N : Nat) : Finset (Nat × Nat) :=
  ((Finset.range N).product (Finset.range (thresholdEnvelope N + 1))).filter
    (fun p => opt (p.1 + 1) ≤ p.2)

theorem boundedYesPairCensus_card_le (opt : Nat → Nat) (N : Nat) :
    (boundedYesPairCensus opt N).card ≤ N * (thresholdEnvelope N + 1) := by
  unfold boundedYesPairCensus
  calc
    _ ≤ ((Finset.range N).product
        (Finset.range (thresholdEnvelope N + 1))).card := by
      exact Finset.card_filter_le _ _
    _ = N * (thresholdEnvelope N + 1) := by simp

theorem bounded_code_in_census {opt : Nat → Nat} {N k B : Nat}
    (hk : 1 ≤ k)
    (hsize : thresholdCodeLength k B ≤ N)
    (hB : B ≤ thresholdEnvelope k)
    (hfit : opt k ≤ thresholdEnvelope k)
    (hyes : opt k ≤ B) :
    (k - 1, B) ∈ boundedYesPairCensus opt N := by
  have hlen : k ≤ N := (unary_parameter_le_code_length k B).trans hsize
  unfold boundedYesPairCensus
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · rw [Finset.mem_range]
      omega
    · rw [Finset.mem_range]
      have hp := thresholdEnvelope_mono hlen
      omega
  · simpa [Nat.sub_add_cancel hk] using hyes

def canonicalBinaryWidthValues (m : Nat) : Finset Nat :=
  (Finset.range (2 ^ (m - 1))).image (fun j => 2 ^ (m - 1) + j)

theorem canonicalBinaryWidthValues_card {m : Nat} :
    (canonicalBinaryWidthValues m).card = 2 ^ (m - 1) := by
  unfold canonicalBinaryWidthValues
  calc
    _ = (Finset.range (2 ^ (m - 1))).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      change 2 ^ (m - 1) + a = 2 ^ (m - 1) + b at hab
      exact Nat.add_left_cancel hab
    _ = 2 ^ (m - 1) := by simp

theorem canonicalBinaryWidthValues_upper {m B : Nat}
    (hm : 1 ≤ m) (hB : B ∈ canonicalBinaryWidthValues m) : B < 2 ^ m := by
  unfold canonicalBinaryWidthValues at hB
  rcases Finset.mem_image.mp hB with ⟨j, hj, rfl⟩
  have hj' : j < 2 ^ (m - 1) := Finset.mem_range.mp hj
  have hpow : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
    calc
      2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ (m - 1) * 2 := by ring
      _ = 2 ^ (m - 1 + 1) := by rw [Nat.pow_succ]
      _ = 2 ^ m := by rw [hm']
  omega

theorem canonicalBinaryWidthValues_lower {m B : Nat}
    (hB : B ∈ canonicalBinaryWidthValues m) : 2 ^ (m - 1) ≤ B := by
  unfold canonicalBinaryWidthValues at hB
  rcases Finset.mem_image.mp hB with ⟨j, hj, rfl⟩
  omega

theorem canonicalBinaryWidthValues_log2 {m B : Nat}
    (hm : 1 ≤ m) (hB : B ∈ canonicalBinaryWidthValues m) :
    Nat.log2 B = m - 1 := by
  have hlo := canonicalBinaryWidthValues_lower hB
  have hhi := canonicalBinaryWidthValues_upper hm hB
  have hne : B ≠ 0 := by
    have hp : 0 < 2 ^ (m - 1) := Nat.pow_pos (by decide)
    omega
  have hloLog : m - 1 ≤ Nat.log2 B := (Nat.le_log2 hne).2 hlo
  have hhiLog : Nat.log2 B < m := (Nat.log2_lt hne).mpr hhi
  omega

theorem canonicalBinaryWidthValues_code_length {k m B : Nat}
    (hm : 1 ≤ m) (hB : B ∈ canonicalBinaryWidthValues m) :
    (thresholdBits k B).length = k + m + 1 := by
  rw [thresholdBits_length]
  unfold thresholdCodeLength
  rw [canonicalBinaryWidthValues_log2 hm hB]
  omega

def canonicalBinaryWidthCodes (k m : Nat) : Finset (List Bool) :=
  (canonicalBinaryWidthValues m).image (fun B => thresholdBits k B)

theorem canonicalBinaryWidthCodes_card {k m : Nat} :
    (canonicalBinaryWidthCodes k m).card = 2 ^ (m - 1) := by
  unfold canonicalBinaryWidthCodes
  calc
    _ = (canonicalBinaryWidthValues m).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      have hp : (k, a) = (k, b) :=
        thresholdBits_injective (by simpa using hab)
      exact congrArg Prod.snd hp
    _ = 2 ^ (m - 1) := canonicalBinaryWidthValues_card

def canonicalBinaryWidthYesValues (opt : Nat → Nat) (k m : Nat) :
    Finset Nat :=
  (canonicalBinaryWidthValues m).filter (fun B => decide (opt k ≤ B))

noncomputable def canonicalBinaryWidthYesCodes (opt : Nat → Nat) (k m : Nat) :
    Finset (List Bool) :=
  (canonicalBinaryWidthYesValues opt k m).image (fun B => thresholdBits k B)

theorem unbounded_binary_tail_yes_count {opt : Nat → Nat} {k m : Nat}
    (hm : 1 ≤ m) (hopt : opt k ≤ 2 ^ (m - 1)) :
    (canonicalBinaryWidthYesValues opt k m).card = 2 ^ (m - 1) := by
  have hall : canonicalBinaryWidthYesValues opt k m = canonicalBinaryWidthValues m := by
    unfold canonicalBinaryWidthYesValues
    apply Finset.filter_eq_self.mpr
    intro B hB
    have _hwidth := canonicalBinaryWidthValues_upper hm hB
    simp only [decide_eq_true_eq]
    exact le_trans hopt (canonicalBinaryWidthValues_lower hB)
  rw [hall, canonicalBinaryWidthValues_card]

theorem canonicalBinaryWidthYesCodes_card {opt : Nat → Nat} {k m : Nat}
    (hm : 1 ≤ m) (hopt : opt k ≤ 2 ^ (m - 1)) :
    (canonicalBinaryWidthYesCodes opt k m).card = 2 ^ (m - 1) := by
  unfold canonicalBinaryWidthYesCodes
  calc
    _ = (canonicalBinaryWidthYesValues opt k m).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      have hp : (k, a) = (k, b) :=
        thresholdBits_injective (by simpa using hab)
      exact congrArg Prod.snd hp
    _ = 2 ^ (m - 1) := unbounded_binary_tail_yes_count hm hopt

theorem canonicalBinaryWidthYesCodes_length {opt : Nat → Nat} {k m : Nat}
    (hm : 1 ≤ m) (hopt : opt k ≤ 2 ^ (m - 1))
    {code : List Bool} (hcode : code ∈ canonicalBinaryWidthYesCodes opt k m) :
    code.length = k + m + 1 := by
  unfold canonicalBinaryWidthYesCodes at hcode
  rcases Finset.mem_image.mp hcode with ⟨B, hB, rfl⟩
  have hB' : B ∈ canonicalBinaryWidthValues m :=
    (Finset.mem_filter.mp hB).1
  exact canonicalBinaryWidthValues_code_length hm hB'

theorem normalize_threshold_iff {opt : Nat → Nat} {k B : Nat}
    (hfit : opt k ≤ thresholdEnvelope k) :
    thresholdYes opt k B ↔ thresholdYes opt k (min B (thresholdEnvelope k)) := by
  unfold thresholdYes
  omega

theorem normalize_root_stop_threshold_iff {k B : Nat} (hk : 1 ≤ k) :
    thresholdYes rootStopBudget k B ↔
      thresholdYes rootStopBudget k (min B (thresholdEnvelope k)) :=
  normalize_threshold_iff (rootThreshold_fits_envelope hk)

/-- The accepted finite optimizer objective at width W, with arity bound K fixed. -/
noncomputable def actualBenchmarkOpt (K W : Nat) : Nat :=
  (Paper.ComputableProfileProvider.optimize K W 1).benchmarkCost Paper.PPEndToEnd.tauRS 1

/-- The actual benchmark optimum is bounded by the accepted root-stop budget. -/
theorem actualBenchmarkOpt_le_rootStop {K W : Nat}
    (hK : 2 ≤ K) (hW : 1 ≤ W) :
    actualBenchmarkOpt K W ≤ rootStopBudget W := by
  obtain ⟨_, v', _, _, hv, hroot, _, _, _, _, _, _, _, _, _⟩ :=
    Paper.F7MatrixFinal.optimizer_canonical_matrix_bits hK hW
  change (Paper.ComputableProfileProvider.optimize K W 1).benchmarkCost Paper.PPEndToEnd.tauRS 1 ≤ rootStopBudget W
  rw [← hv]
  exact hroot

/-- For fixed K, the actual optimizer threshold fits the numeric envelope. -/
theorem actualBenchmarkOpt_le_envelope {K W : Nat}
    (hK : 2 ≤ K) (hW : 1 ≤ W) :
    actualBenchmarkOpt K W ≤ thresholdEnvelope W := by
  exact (actualBenchmarkOpt_le_rootStop hK hW).trans
    (rootThreshold_fits_envelope hW)


/-- Census specialization for the actual accepted benchmark objective, with K fixed.
The optimizer-to-root-stop bound is imported from the accepted F7 optimizer theorem. -/
theorem actual_optimizer_code_in_census {K W N B : Nat}
    (hK : 2 ≤ K) (hW : 1 ≤ W)
    (hsize : thresholdCodeLength W B ≤ N)
    (hB : B ≤ thresholdEnvelope W)
    (hyes : actualBenchmarkOpt K W ≤ B) :
    (W - 1, B) ∈ boundedYesPairCensus (actualBenchmarkOpt K) N := by
  apply bounded_code_in_census (opt := actualBenchmarkOpt K) (hk := hW)
    (hsize := hsize) (hB := hB)
    (hfit := actualBenchmarkOpt_le_envelope hK hW) (hyes := hyes)
end ExecutionAlignment.SparseThreshold




