import Provider.Effective.Enumeration
import Provider.Weights.Projective
import Provider.Effective.Keys

/-! # Complete Effective Provider
Defines the finite enumerated `keys` and `catalog` with `budget K root = 3*K*root`, the selector `pick` and the entries `rawEntry` and `entry`. Proves completeness facts such as `charge_le_budget`, `relevantCheck_iff`, `catalog_mem` and `pick_relevant`. This is a finite enumeration; no running-time claim is made.
-/

namespace Paper.EffectiveProvider

open Paper.F2CatalogTransfer Paper.BoundedThreshold
open Paper.F4ChargeIntervals Paper.CompressionComplete
open Paper.CompressionEncoding Paper.CompressionF2
open Paper.SourceBridge TableGeneration

def budget (K root : Nat) : Nat := 3*K*root

abbrev Index (K root : Nat) :=
  Σ key : ProfileKey K root,
    { pair : Prog key.1.val × List TableGeneration.Operations.Point //
      pair ∈ searchEntries key.1.val key.2.1.val
        (lengthCap key.1.val (budget K root)) }

def keys (K root : Nat) : List (ProfileKey K root) :=
  (List.finRange (K+1)).flatMap fun k =>
    (List.finRange (root+1)).flatMap fun a =>
      (List.finRange (root+1)).map fun b => (k, (a, b))

def catalog (K root : Nat) : List (Index K root) :=
  (keys K root).flatMap fun key =>
    ((searchEntries key.1.val key.2.1.val
      (lengthCap key.1.val (budget K root))).attach.map fun e => ⟨key, e⟩)

def defaultIndex (K root : Nat) : Index K root :=
  ⟨(⟨0, by omega⟩, ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩),
    ⟨([], f2Points 0), by
      apply mem_searchEntries
      · simp
      · intro op hop; simp at hop
      · rfl⟩⟩

def keyOf {K root : Nat} (t : F2Source K) : ProfileKey K root :=
  (⟨t.arity, Nat.lt_succ_of_le t.cap⟩,
    ⟨⟨min (sourcePeaks t).1 root, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
     ⟨min (sourcePeaks t).2 root, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩)

theorem keyOf_relevant {K root : Nat} (t : F2Source K)
    (hrel : Relevant root t) : keyOf t = relevantKey t hrel := by
  have h := relevant_peaks_bounded t hrel
  simp [keyOf, relevantKey, Nat.min_eq_left h.1, Nat.min_eq_left h.2]

theorem charge_le_budget {K root : Nat} (t : F2Source K)
    (hrel : Relevant root t) : t.charge ≤ budget K root := by
  have hA := (relevant_peaks_bounded t hrel).1
  have hcap : t.charge ≤ 3 * (t.arity * (sourcePeaks t).1) := by
    simpa only [sourcePeaks] using (Paper.F3ChargeCeiling.source_charge_cap_bound t).1
  calc
    t.charge ≤ 3 * (t.arity * (sourcePeaks t).1) := hcap
    _ ≤ 3 * (K * root) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul t.cap hA)
    _ = budget K root := by simp [budget, Nat.mul_assoc]

def compressedPair {K : Nat} (t : F2Source K) :
    Prog t.arity × List TableGeneration.Operations.Point :=
  ((complete t).source.program, List.ofFn (complete t).points)

theorem compressed_mem {K root : Nat} (t : F2Source K)
    (hrel : Relevant root t) :
    compressedPair t ∈ searchEntries t.arity (sourcePeaks t).1
      (lengthCap t.arity (budget K root)) := by
  have hb := charge_le_budget t hrel
  apply mem_searchEntries
  · exact compressed_length_le_cap t (budget K root) hb
  · intro op hop
    exact complete_exponents t op hop
  · exact (complete t).literalF2

theorem compressed_check {K root : Nat} (t : F2Source K)
    (hrel : Relevant root t) :
    sourceCheck t.source.hk (sourcePeaks t).1 (sourcePeaks t).2
      (budget K root) (complete t).source.program
      (List.ofFn (complete t).points) = true := by
  apply (sourceCheck_iff t.source.hk (sourcePeaks t).1
    (sourcePeaks t).2 (budget K root)
    (complete t).source.program (List.ofFn (complete t).points)).2
  have hp : rawProfile (complete t) = rawProfile t := by
    simpa [rawProfile, Paper.PrefixPaddingStage.sourceProfileRaw] using
      complete_exact_profile t
  refine ⟨(complete t).literalF2, (complete t).safe, ?_, ?_, ?_⟩
  · have hc : (complete t).charge ≤ budget K root := by
      simpa [complete_charge] using charge_le_budget t hrel
    simpa [F2Source.charge] using hc
  · change (rawProfile (complete t)).peakA ≤ (rawProfile t).peakA
    rw [hp]
  · change (rawProfile (complete t)).peakB ≤ (rawProfile t).peakB
    rw [hp]

def relevantCheck {K : Nat} (root : Nat) (t : F2Source K) : Bool :=
  (List.range (root+1)).any (fun w => decide (t.childWidth w < w))

theorem any_contract_iff {K : Nat} (t : F2Source K) (l : List Nat) :
    l.any (fun w => decide (t.childWidth w < w)) = true ↔
      ∃ w ∈ l, t.childWidth w < w := by
  induction l with
  | nil => simp
  | cons w rest ih => simp [List.any, ih]

theorem relevantCheck_iff {K : Nat} (root : Nat) (t : F2Source K) :
    relevantCheck root t = true ↔ Relevant root t := by
  rw [relevantCheck, any_contract_iff]
  simp only [List.mem_range, Relevant]
  constructor
  · rintro ⟨w, hw, hc⟩
    exact ⟨w, by omega, hc⟩
  · rintro ⟨w, hw, hc⟩
    exact ⟨w, by omega, hc⟩

def pick {K root : Nat} (t : F2Source K) : Index K root :=
  if h : relevantCheck root t = true then
    let hrel := (relevantCheck_iff root t).mp h
    ⟨relevantKey t hrel, ⟨compressedPair t, compressed_mem t hrel⟩⟩
  else defaultIndex K root

def rawEntry {K root : Nat} (hK : 2 ≤ K) (i : Index K root) : F2Source K :=
  let k := i.1.1.val
  if hk : 2 ≤ k then
    let cap : k ≤ K := Nat.le_of_lt_succ i.1.1.isLt
    if hc : sourceCheck hk i.1.2.1.val i.1.2.2.val (budget K root)
        i.2.val.1 i.2.val.2 = true then
      checkedSource hk cap i.1.2.1.val i.1.2.2.val (budget K root)
        i.2.val.1 i.2.val.2 hc
    else Paper.F3ChargeCeiling.groupedLiteralBaseline 2 (by omega) hK
  else Paper.F3ChargeCeiling.groupedLiteralBaseline 2 (by omega) hK

def entry {K root : Nat} (hK : 2 ≤ K) (i : Index K root) :
    Paper.PPEndToEnd.VerifiedPPCandidate K :=
  Paper.A4Certificate.verifiedSource (rawEntry hK i)

theorem entry_literal {K root : Nat} (hK : 2 ≤ K) (i : Index K root) :
    VerifiedLiteralF2 (entry hK i) :=
  (Paper.A4Certificate.verifiedSource_literal (rawEntry hK i)).2

theorem keys_mem {K root : Nat} (key : ProfileKey K root) :
    key ∈ keys K root := by
  rcases key with ⟨k, ⟨a, b⟩⟩
  simp [keys]

theorem catalog_mem {K root : Nat} (i : Index K root) :
    i ∈ catalog K root := by
  rcases i with ⟨key, pair⟩
  simp only [catalog, List.mem_flatMap]
  refine ⟨key, keys_mem key, ?_⟩
  exact List.mem_map.mpr ⟨pair, by simp, rfl⟩

theorem pick_relevant {K root : Nat} (t : F2Source K)
    (hrel : Relevant root t) :
    pick (root := root) t = ⟨relevantKey t hrel,
      ⟨compressedPair t, by
        simpa only [relevantKey] using compressed_mem t hrel⟩⟩ := by
  have hc := (relevantCheck_iff root t).mpr hrel
  simp only [pick, dif_pos hc]

theorem rawEntry_pick {K root : Nat} (hK : 2 ≤ K)
    (t : F2Source K) (hrel : Relevant root t) :
    rawEntry (root := root) hK (pick (root := root) t) =
      checkedSource t.source.hk t.cap (sourcePeaks t).1 (sourcePeaks t).2
        (budget K root) (complete t).source.program
        (List.ofFn (complete t).points) (compressed_check t hrel) := by
  rw [pick_relevant t hrel]
  simp only [rawEntry, relevantKey, compressedPair]
  split
  · simp only [dif_pos (compressed_check t hrel)]
  · rename_i hn
    exact False.elim (hn t.source.hk)

theorem rawEntry_pick_spec {K root : Nat} (hK : 2 ≤ K)
    (t : F2Source K) (hrel : Relevant root t) :
    let u := rawEntry (root := root) hK (pick (root := root) t)
    u.arity = t.arity ∧ sourcePeaks u = sourcePeaks t ∧
      u.charge = t.charge := by
  dsimp only
  rw [rawEntry_pick hK t hrel]
  have hp : rawProfile (complete t) = rawProfile t := by
    simpa [rawProfile, Paper.PrefixPaddingStage.sourceProfileRaw] using
      complete_exact_profile t
  refine ⟨rfl, ?_, ?_⟩
  · change ((rawProfile (complete t)).peakA,
        (rawProfile (complete t)).peakB) =
        ((rawProfile t).peakA, (rawProfile t).peakB)
    rw [hp]
  · change (complete t).charge = t.charge
    exact complete_charge t

def provider {K root : Nat} (hK : 2 ≤ K) :
    CompleteProvider root (entry (root := root) hK) (catalog K root) := by
  refine {
    pick := pick,
    catalog_literal := ?_, member := ?_, arity := ?_, width := ?_, charge := ?_
  }
  · intro c hc
    exact entry_literal hK c
  · intro t hrel
    exact catalog_mem (pick (root := root) t)
  · intro t hrel
    exact (rawEntry_pick_spec hK t hrel).1
  · intro t hrel w
    have hs := rawEntry_pick_spec hK t hrel
    exact sourcePeaks_width_eq _ t hs.1 hs.2.1 w
  · intro t hrel
    exact (rawEntry_pick_spec hK t hrel).2.2.le

instance indexDecidableEq (K root : Nat) : DecidableEq (Index K root) := inferInstance

instance indexFintype (K root : Nat) : Fintype (Index K root) :=
  Fintype.ofList (catalog K root) catalog_mem

theorem effective_optimal_raw_F2_policy (K W N : Nat) (hK : 2 ≤ K)
    (price : Nat → Nat) :
    let e := entry (root := W) hK
    let c := catalog K W
    let P := Paper.PPEndToEnd.ppProblem price e
    let arity := fun i => (e i).arity
    let trace := Paper.PolicyOptimality.chosenTrace P c arity K W N
    ∃ policy : Paper.PPEndToEnd.PPPolicy K W,
      Paper.PPEndToEnd.policyFromTrace e trace W = some policy ∧
      Coupled.Formal.ArityInj arity trace ∧
      (∀ i ∈ trace, VerifiedLiteralF2 (e i)) ∧
      policy.benchmarkCost price N =
        Paper.PolicyOptimality.chosenCost P c arity K W N ∧
      policy.benchmarkCost price N =
        4 * (policy.adderAnds N + policy.leafRotations N) +
          policy.leafRotations N * price (policy.leafRotations N) ∧
      (∀ (theta : ℝ) (a c : BitVec W),
        policy.eval Paper.PPEndToEnd.schoolbookLeaf theta a.toInt c.toInt =
          some (Paper.ValuePhase.phaseCharacter theta
            ((a.toInt : ℚ) * (c.toInt : ℚ)))) ∧
      (∀ (l : List (F2Source K)) (v : Nat),
        Coupled.Formal.ArityInj F2Source.arity l →
        Coupled.Formal.CostL (rawProblem price) l W N v →
        policy.benchmarkCost price N ≤ v) := by
  dsimp only
  exact optimized_pp_all_F2_conditional price (entry hK) (catalog K W)
    W N (provider hK)

end Paper.EffectiveProvider
