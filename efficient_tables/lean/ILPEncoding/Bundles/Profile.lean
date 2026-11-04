import Provider.Effective.Attain
import ILPEncoding.Labels.Typed
import ILPEncoding.Labels.ILPChecked
import ILPEncoding.Labels.SharedCost
import ILPEncoding.Bounds.StopBudget

/-! # Bundled Profile Optimizer Development
A single-file bundle of the profile-to-label development, concatenating the segments marked by its `BEGIN` comments. It includes `labelOf`, `optimize_exact_raw_result` (a finite-search theorem with no uniform polynomial-time claim) and `optimizer_actual_feasible_root`, relating the optimizer's ladders to actual label words and the feasibility predicate. Also defines the candidate levels `levelSet` and `candidateIntervals`.
-/

/- BEGIN Charge.lean source_sha256=d79541efe7ca7c08b4cbec442d4395e25ffad798afa8ed6149fc0fb67119ea91 body_sha256=c16d3951c8e870e298b9a39a38425df2f4db915658d658c15aa2dcf9cca27627 -/

namespace Paper.ComputableProfileProvider

open Paper.F2CatalogTransfer Paper.F4ChargeIntervals
open Paper.BoundedThreshold Paper.PrefixPaddingStage
open Paper.CompressionComplete

theorem rawEntry_pick_minCharge {K root : Nat} (hK : 2 ≤ K)
    (t : F2Source K) (hrel : Relevant root t) :
    ((rawEntry hK (pick (root := root) t)).charge : WithTop Nat) =
      minCharge (K := K) t.arity
        ((sourcePeaks t).1 - (sourcePeaks t).2) (sourcePeaks t).1 := by
  obtain ⟨C,u,hfound,huarity,hcharge,huA,huB,_⟩ :=
    firstBudget_for_source t hrel
  let a := (sourcePeaks t).1
  let b := (sourcePeaks t).2
  have hcanonical := original_profile_canonical t
  have hBA : b ≤ a := by
    simpa [a, b, sourcePeaks, originalA, originalB,
      sourceProfileRaw, rawProfile] using hcanonical.1
  have hCanon : a ≤ b + (t.arity - 1) := by
    simpa [a, b, sourcePeaks, originalA, originalB,
      sourceProfileRaw, rawProfile, F2Source.arity] using hcanonical.2
  have hCanonU : a ≤ b + (u.source.k - 1) := by
    change a ≤ b + (u.arity - 1)
    rw [huarity]
    exact hCanon
  let v := paddedF2Source u a b
  have hraw : rawEntry hK (pick (root := root) t) = v := by
    rw [pick_relevant t hrel]
    simp only [rawEntry, relevantKey]
    have hk : 2 ≤ t.arity := t.source.hk
    simp only [dif_pos hk, dif_pos hBA, dif_pos hCanon, hfound, v, a, b]
  have hvcharge : v.charge = C := by
    simpa [v, F2Source.charge, paddedF2Source, paddingPrefix,
      Paper.PPEndToEnd.chargedCount, Paper.PPEndToEnd.chargedOp] using hcharge
  have hsub : a - (a-b) = b := by omega
  have hfound' : firstBudget t.source.hk t.cap a (a-(a-b))
      (27*t.arity^3) = some (C,u) := by
    simpa [a, b, F2Source.arity, hsub] using hfound
  have hmin := firstBudget_attains_raw_minimum t.source.hk t.cap
    (by omega : a-b ≤ a) (27*t.arity^3) C u hfound'
  have hfeas : feasible (K := K) t.arity (a-b) a C := by
    refine ⟨by omega, u, huarity, huA, ?_, ?_⟩
    · simpa [hsub] using huB
    · exact hcharge.le
  have hex : ∃ D, feasible (K := K) t.arity (a-b) a D := ⟨C,hfeas⟩
  have hle : leastBudget hex ≤ C := leastBudget_min hex hfeas
  have hrev : C ≤ leastBudget hex := by
    obtain ⟨_,s,hsarity,hsA,hsB,hsC⟩ := leastBudget_spec hex
    exact (hmin.2.2.2.2 s hsarity hsA hsB).trans hsC
  have heq : leastBudget hex = C := Nat.le_antisymm hle hrev
  rw [hraw, hvcharge]
  simpa [a, b, minCharge_eq_leastBudget hex, heq]

end Paper.ComputableProfileProvider
/- END Charge.lean -/

/- BEGIN Label.lean source_sha256=71968104919ff75ba3d4807620a227e4460277f7addfb978ae4678cc43335cc1 body_sha256=a35931a504ba19f352a4215e75e455c5f372366b9bc7cb5e7d18e6082eb1daa7 -/

namespace Paper.ComputableProfileProvider

open Paper.F2CatalogTransfer Paper.F4ChargeIntervals
open Paper.CompressionComplete
open Paper.PrefixPaddingStage

theorem rawEntry_pick_charge_cap {K root : Nat} (hK : 2 ≤ K)
    (t : F2Source K) (hrel : Relevant root t) :
    (rawEntry hK (pick (root := root) t)).charge ≤ 27 * t.arity ^ 3 := by
  have hcanon := original_profile_canonical t
  have hBA : (sourcePeaks t).2 ≤ (sourcePeaks t).1 := by
    simpa [sourcePeaks, originalA, originalB, sourceProfileRaw, rawProfile]
      using hcanon.1
  have hsub : (sourcePeaks t).1 -
      ((sourcePeaks t).1 - (sourcePeaks t).2) = (sourcePeaks t).2 := by omega
  have hfeas : feasible (K := K) t.arity
      ((sourcePeaks t).1 - (sourcePeaks t).2)
      (sourcePeaks t).1 t.charge := by
    refine ⟨by omega, t, rfl, ?_, ?_, le_rfl⟩
    · rfl
    · simpa [hsub] using (show (rawProfile t).peakB ≤ (sourcePeaks t).2 from le_rfl)
  have hmin := Paper.F3ChargeCeiling.minCharge_le_27_cube
    t.source.hk hfeas
  change minCharge (K := K) t.arity
    ((sourcePeaks t).1 - (sourcePeaks t).2) (sourcePeaks t).1 ≤
      (27 * t.arity ^ 3 : WithTop Nat) at hmin
  rw [← rawEntry_pick_minCharge hK t hrel] at hmin
  exact_mod_cast hmin

def labelOf {K root : Nat} (hK : 2 ≤ K) (t : F2Source K)
    (w : Nat) : Paper.AffineNat.Label :=
  let v := rawEntry hK (pick (root := root) t)
  { k := v.arity
    r := w % v.arity
    d := (sourcePeaks v).1 - (sourcePeaks v).2
    c := v.charge
    hk := v.source.hk
    hr := Nat.mod_lt _ (by
      have hvk : 2 ≤ v.arity := v.source.hk
      omega)
    hd := by
      have hcanon := original_profile_canonical v
      have h : (sourcePeaks v).1 ≤
          (sourcePeaks v).2 + (v.arity - 1) := by
        simpa [sourcePeaks, originalA, originalB,
          sourceProfileRaw, rawProfile, F2Source.arity] using hcanon.2
      have hvk : 2 ≤ v.arity := v.source.hk
      have hlt : (sourcePeaks v).1 - (sourcePeaks v).2 < v.arity := by
        omega
      simpa [sourcePeaks, originalA, originalB,
        sourceProfileRaw, rawProfile, F2Source.arity] using hlt }

theorem labelOf_minCharge {K root : Nat} (hK : 2 ≤ K)
    (t : F2Source K) (hrel : Relevant root t) (w : Nat) :
    minCharge (K := K) (labelOf (root := root) hK t w).k
      (labelOf (root := root) hK t w).d (sourcePeaks t).1 =
      ((labelOf (root := root) hK t w).c : WithTop Nat) := by
  have hs := rawEntry_pick_spec hK t hrel
  have hm := rawEntry_pick_minCharge hK t hrel
  dsimp [labelOf]
  rw [hs.1, hs.2.1]
  exact hm.symm

theorem labelOf_in_alphabet {K root : Nat} (hK : 2 ≤ K)
    (t : F2Source K) (hrel : Relevant root t) (w : Nat) :
    Paper.F6TypedBridge.toTyped (labelOf (root := root) hK t w) ∈
      Paper.CountStage.TypedDecorationWords.decorationLabels K := by
  apply Paper.F6TypedBridge.toTyped_alphabet
  · dsimp [labelOf]
    exact (rawEntry hK (pick (root := root) t)).cap
  · dsimp [labelOf]
    simpa only [(rawEntry_pick_spec hK t hrel).1] using
      rawEntry_pick_charge_cap hK t hrel

end Paper.ComputableProfileProvider
/- END Label.lean -/

/- BEGIN Result.lean source_sha256=fed367cfffcfbb65c5a086ac5e16c50a84c4e133b74eb2dad3acbb36799137c0 body_sha256=0381975532fe065b2242957be33d5e2b2d3fcbade60fb3105df1b04efab05db1 -/

namespace Paper.ExactAlgorithm

open Coupled.Formal Paper.F2CatalogTransfer
open Paper.ComputableProfileProvider

/-- The returned exhaustive optimizer has the exact benchmark price and ideal
PP semantics. A shared legal raw F2 ladder attains its cost, and no shared
legal raw F2 ladder has lower cost. This is a finite-search theorem; it makes
no uniform polynomial-time claim. -/
theorem optimize_exact_raw_result (K W N : Nat) :
    (optimize K W N).benchmarkCost Paper.PPEndToEnd.tauRS N =
      (optimize K W N).benchmarkCost Paper.PPEndToEnd.tauExact N ∧
    (∀ (theta : ℝ) (a c : BitVec W),
      (optimize K W N).eval Paper.PPEndToEnd.schoolbookLeaf theta a.toInt c.toInt =
        some (Paper.ValuePhase.phaseCharacter theta
          ((a.toInt : ℚ) * (c.toInt : ℚ)))) ∧
    (∃ l : List (F2Source K),
      ArityInj F2Source.arity l ∧
      CostL (rawProblem Paper.PPEndToEnd.tauRS) l W N
        ((optimize K W N).benchmarkCost Paper.PPEndToEnd.tauRS N)) ∧
    (∀ (l : List (F2Source K)) (v : Nat),
      ArityInj F2Source.arity l →
      CostL (rawProblem Paper.PPEndToEnd.tauRS) l W N v →
      (optimize K W N).benchmarkCost Paper.PPEndToEnd.tauRS N ≤ v) := by
  obtain ⟨hprice,hsem,hmin⟩ := optimize_all_raw K W N
  obtain ⟨l,hshared,hcost⟩ := optimize_raw_attained K W N
  exact ⟨hprice,hsem,⟨l,hshared,hcost⟩,hmin⟩

end Paper.ExactAlgorithm
/- END Result.lean -/

/- BEGIN Forward.lean source_sha256=85aa35b71c91e3d5a0179b9d162f7d5e80605dd7316f1319a4150dce7f6fe370 body_sha256=b32ef668a98a8b4e2c58a02940c5e38e500cb006b0783111e4cda9f1ae115af1 -/

namespace Paper.A2ActualForward

open Coupled.Formal Paper.F2CatalogTransfer
open Paper.F4ChargeIntervals Paper.AffineNat Paper.AffineTable
open Paper.AffineActual Paper.AffineStep

/-- Forward realization of a positive-width shared raw ladder whose tables
already satisfy the chosen common profile functions. The profile-function
construction from an arbitrary arity-injective list is a separate step. -/
theorem actual_labels_of_costL {K : Nat} (a d c : Nat → Nat)
    (price : Nat → Nat) {ts : List (F2Source K)} {w N v : Nat}
    (hcost : CostL (rawProblem price) ts w N v)
    (P : ℤ) (hP : 0 < P) (hpos : 1 ≤ w)
    (hspec : ∀ t ∈ ts, TableSpec a d c t.arity t)
    (hplateau : ∀ t ∈ ts,
      minCharge (K := K) t.arity (d t.arity) (a t.arity) =
        (c t.arity : WithTop Nat))
    (hd : ∀ t ∈ ts, d t.arity < t.arity) :
    ∃ labels : List Label,
      labels.length = ts.length ∧
      labels.map Label.k = ts.map F2Source.arity ∧
      (∀ label ∈ labels,
        label.d = d label.k ∧ label.c = c label.k ∧
        minCharge (K := K) label.k (d label.k) (a label.k) =
          (c label.k : WithTop Nat)) ∧
      ActualWord (K := K) a d c P (P * w) labels := by
  induction hcost generalizing P with
  | base w N =>
      refine ⟨[], rfl, rfl, by simp, ?_⟩
      exact ⟨w, rfl, hpos⟩
  | step t rest w N v hstrict htail ih =>
      have htsp : TableSpec a d c t.arity t := hspec t (by simp)
      have htplateau := hplateau t (by simp)
      have htd : d t.arity < t.arity := hd t (by simp)
      let label : Label :=
        { k := t.arity, r := w % t.arity,
          d := d t.arity, c := c t.arity,
          hk := t.source.hk,
          hr := Nat.mod_lt _ (by
            have hk : 2 ≤ t.arity := t.source.hk
            omega), hd := htd }
      have hchild : 1 ≤ t.childWidth w := by
        rw [htsp.2.2.2.2 w]
        exact (Nat.le_add_left 1 (w / t.arity)).trans
          (Nat.le_add_right _ _)
      have hkpos : 0 < (t.arity : ℤ) := by
        have hk : 0 < t.arity := by omega
        exact_mod_cast hk
      have hPk : 0 < P * t.arity := mul_pos hP hkpos
      have hrestSpec : ∀ u ∈ rest, TableSpec a d c u.arity u := by
        intro u hu
        exact hspec u (by simp [hu])
      have hrestPlateau : ∀ u ∈ rest,
          minCharge (K := K) u.arity (d u.arity) (a u.arity) =
            (c u.arity : WithTop Nat) := by
        intro u hu
        exact hplateau u (by simp [hu])
      have hrestD : ∀ u ∈ rest, d u.arity < u.arity := by
        intro u hu
        exact hd u (by simp [hu])
      obtain ⟨labels,hlen,hkeys,hshared,hactual⟩ :=
        ih (P * t.arity) hPk hchild hrestSpec hrestPlateau hrestD
      obtain ⟨u,hu,huspec⟩ :=
        plateau_tableAt a d c t.arity t.source.hk htd htplateau
      have hwidth : u.childWidth w = t.childWidth w := by
        exact (huspec.2.2.2.2 w).trans (htsp.2.2.2.2 w).symm
      have hnext : Paper.AffineILP.nextWidth P (P * w)
          (instantiate a label) =
          P * label.k * (u.childWidth w : ℤ) := by
        exact actual_child_cleared a d c label u P w rfl rfl
          (by simpa [label] using htplateau) (by simpa [label] using huspec)
      refine ⟨label :: labels, by simp [hlen], by simp [label, hkeys], ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hmem
        · exact ⟨rfl, rfl, by simpa [label] using htplateau⟩
        · exact hshared q hmem
      · refine ⟨u, w, hu, by simpa [label] using huspec,
          rfl, rfl, hnext, ?_, ?_⟩
        · simpa [hwidth, rawProblem] using hstrict
        · simpa [label, hnext, hwidth, mul_assoc] using hactual

end Paper.A2ActualForward
/- END Forward.lean -/

/- BEGIN Common.lean source_sha256=d940ffee371081a4092cb8badb28abb79db0e619dfb1ff37643280e900cb5a61 body_sha256=4d78ceaac4ce7aef655e42e2cc5d262c60bdf836ebb981cf9677cd932fa8c0be -/

namespace Paper.A2ActualForward

open Coupled.Formal Paper.F2CatalogTransfer
open Paper.F4ChargeIntervals Paper.AffineTable
open Paper.CompressionComplete Paper.PrefixPaddingStage

def tableFor {K : Nat} (ts : List (F2Source K)) (k : Nat) :
    Option (F2Source K) := ts.find? (fun t => t.arity == k)

def profileA {K : Nat} (ts : List (F2Source K)) (k : Nat) : Nat :=
  ((tableFor ts k).map fun t => (sourcePeaks t).1).getD 0

def profileD {K : Nat} (ts : List (F2Source K)) (k : Nat) : Nat :=
  ((tableFor ts k).map fun t => (sourcePeaks t).1 - (sourcePeaks t).2).getD 0

def profileC {K : Nat} (ts : List (F2Source K)) (k : Nat) : Nat :=
  ((tableFor ts k).map fun t => t.charge).getD 0

theorem tableFor_mem {K : Nat} {ts : List (F2Source K)}
    (hinj : ArityInj F2Source.arity ts) {t : F2Source K}
    (ht : t ∈ ts) : tableFor ts t.arity = some t := by
  have hex : ∃ u, u ∈ ts ∧ (u.arity == t.arity) :=
    ⟨t,ht,by simp⟩
  have hsome : (tableFor ts t.arity).isSome := by
    simpa only [tableFor, List.find?_isSome] using hex
  cases hfind : tableFor ts t.arity with
  | none => simp [hfind] at hsome
  | some u =>
      have hu : u ∈ ts := List.mem_of_find?_eq_some (by simpa [tableFor] using hfind)
      have heq : u.arity = t.arity := by
        have hh := List.find?_some (by simpa [tableFor] using hfind)
        simpa using hh
      have hut : u = t := hinj u hu t ht heq
      simpa [hut] using hfind

theorem common_values {K : Nat} {ts : List (F2Source K)}
    (hinj : ArityInj F2Source.arity ts) {t : F2Source K}
    (ht : t ∈ ts) :
    profileA ts t.arity = (sourcePeaks t).1 ∧
    profileD ts t.arity = (sourcePeaks t).1 - (sourcePeaks t).2 ∧
    profileC ts t.arity = t.charge := by
  simp [profileA, profileD, profileC, tableFor_mem hinj ht]

theorem tableSpec_of_shared_min {K : Nat} {ts : List (F2Source K)}
    (hinj : ArityInj F2Source.arity ts) {t : F2Source K}
    (ht : t ∈ ts) :
    TableSpec (profileA ts) (profileD ts) (profileC ts) t.arity t := by
  obtain ⟨ha,hd,hc⟩ := common_values hinj ht
  have hcanon := original_profile_canonical t
  have hBA : (sourcePeaks t).2 ≤ (sourcePeaks t).1 := by
    simpa [sourcePeaks, originalA, originalB, sourceProfileRaw, rawProfile]
      using hcanon.1
  have hsub : (sourcePeaks t).1 -
      ((sourcePeaks t).1 - (sourcePeaks t).2) = (sourcePeaks t).2 := by omega
  refine ⟨rfl, hc.symm, ?_, ?_, ?_⟩
  · simpa [sourcePeaks, rawProfile, ha]
  · rw [ha, hd]
    change (sourcePeaks t).2 = (sourcePeaks t).1 -
      ((sourcePeaks t).1 - (sourcePeaks t).2)
    exact hsub.symm
  · intro w
    rw [source_childWidth_eq_profile]
    change w / t.arity + 1 +
        max (sourcePeaks t).1 ((sourcePeaks t).2 + w % t.arity) =
      w / t.arity + 1 +
        max (profileA ts t.arity)
          ((profileA ts t.arity - profileD ts t.arity) + w % t.arity)
    rw [ha, hd, hsub]

theorem common_plateau_of_minimal {K : Nat} {ts : List (F2Source K)}
    (hinj : ArityInj F2Source.arity ts)
    (hmin : ∀ t ∈ ts,
      minCharge (K := K) t.arity
        ((sourcePeaks t).1 - (sourcePeaks t).2) (sourcePeaks t).1 =
          (t.charge : WithTop Nat)) :
    ∀ t ∈ ts,
      minCharge (K := K) t.arity
        (profileD ts t.arity) (profileA ts t.arity) =
          (profileC ts t.arity : WithTop Nat) := by
  intro t ht
  obtain ⟨ha,hd,hc⟩ := common_values hinj ht
  simpa [ha, hd, hc] using hmin t ht

theorem common_d_lt {K : Nat} {ts : List (F2Source K)}
    (hinj : ArityInj F2Source.arity ts) :
    ∀ t ∈ ts, profileD ts t.arity < t.arity := by
  intro t ht
  have hcanon := original_profile_canonical t
  have h : (sourcePeaks t).1 ≤
      (sourcePeaks t).2 + (t.arity - 1) := by
    simpa [sourcePeaks, originalA, originalB,
      sourceProfileRaw, rawProfile, F2Source.arity] using hcanon.2
  have hk : 2 ≤ t.arity := t.source.hk
  rw [(common_values hinj ht).2.1]
  omega

/-- A positive-width, shared minimum-charge raw ladder has a concrete F6
actual label word under computable per-arity functions. -/
theorem shared_minimal_ladder_actual {K : Nat}
    (price : Nat → Nat) {ts : List (F2Source K)} {w N v : Nat}
    (hcost : CostL (rawProblem price) ts w N v)
    (hinj : ArityInj F2Source.arity ts) (hw : 1 ≤ w)
    (hmin : ∀ t ∈ ts,
      minCharge (K := K) t.arity
        ((sourcePeaks t).1 - (sourcePeaks t).2) (sourcePeaks t).1 =
          (t.charge : WithTop Nat)) :
    ∃ labels : List Paper.AffineNat.Label,
      labels.length = ts.length ∧
      labels.map Paper.AffineNat.Label.k = ts.map F2Source.arity ∧
      (∀ label ∈ labels,
        label.d = profileD ts label.k ∧
        label.c = profileC ts label.k ∧
        minCharge (K := K) label.k
          (profileD ts label.k) (profileA ts label.k) =
            (profileC ts label.k : WithTop Nat)) ∧
      Paper.AffineActual.ActualWord (K := K)
        (profileA ts) (profileD ts) (profileC ts) 1 (1 * w) labels := by
  exact actual_labels_of_costL (profileA ts) (profileD ts) (profileC ts)
    price hcost 1 (by decide) hw
    (fun t ht => tableSpec_of_shared_min hinj ht)
    (common_plateau_of_minimal hinj hmin)
    (common_d_lt hinj)

end Paper.A2ActualForward
/- END Common.lean -/

/- BEGIN Bounds.lean source_sha256=26a74b94c3f03a2f233a13ae20aa1f689619ed2cd45d45aca2525a6bf3369c1b body_sha256=b3a2ce83318db9044cb29fbc09b7e29de5fd226e88f5114f1c21a3d607dd8253 -/

namespace Paper.A2ActualForward

open Paper.F2CatalogTransfer Paper.F6TypedBridge
open Paper.AffineNat

/-- Alignment with a capped shared representative list transfers the finite
alphabet bounds to every produced F6 label. -/
theorem aligned_label_bounds {K : Nat}
    {ts : List (F2Source K)} {labels : List Label}
    (hinj : Coupled.Formal.ArityInj F2Source.arity ts)
    (hkeys : labels.map Label.k = ts.map F2Source.arity)
    (hshared : ∀ label ∈ labels, label.c = profileC ts label.k)
    (hcap : ∀ t ∈ ts, t.charge ≤ 27 * t.arity ^ 3) :
    ∀ label ∈ labels,
      2 ≤ label.k ∧ label.k ≤ K ∧ label.c ≤ 27 * label.k ^ 3 := by
  intro label hlabel
  have hmem : label.k ∈ ts.map F2Source.arity := by
    rw [← hkeys]
    exact List.mem_map.mpr ⟨label, hlabel, rfl⟩
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hmem
  have hc : label.c = t.charge := by
    calc
      label.c = profileC ts label.k := hshared label hlabel
      _ = profileC ts t.arity := by rw [heq]
      _ = t.charge := (common_values hinj ht).2.2
  have hk2 : 2 ≤ label.k := by
    rw [← heq]
    exact t.source.hk
  have hkK : label.k ≤ K := by
    rw [← heq]
    exact t.cap
  refine ⟨hk2, hkK, ?_⟩
  rw [hc, ← heq]
  exact hcap t ht

end Paper.A2ActualForward
/- END Bounds.lean -/

/- BEGIN Transfer.lean source_sha256=11241b4c8b9e61807179805bcd6f86e38d63580ad4eafb5b7a0e537fa62b99e8 body_sha256=9067a68aff6b55c565d606820b50b4bd3d09bfb654e23a5862e6ee0ecadedb0b -/

namespace Paper.A2ActualForward

open Coupled.Formal Paper.F2CatalogTransfer
open Paper.F4ChargeIntervals Paper.ComputableProfileProvider

/-- Every positive-width shared raw ladder has a no-more-expensive ladder of
minimum-charge profile representatives, and that ladder has actual F6 labels.
The finite optimizer/profile searches remain exhaustive. -/
theorem original_to_actual_minimal {K W N v : Nat} (hK : 2 ≤ K)
    (hW : 1 ≤ W) (price : Nat → Nat)
    (l : List (F2Source K))
    (hshared : ArityInj F2Source.arity l)
    (hcost : CostL (rawProblem price) l W N v) :
    ∃ (reps : List (F2Source K)) (v' : Nat)
      (labels : List Paper.AffineNat.Label),
      ArityInj F2Source.arity reps ∧
      CostL (rawProblem price) reps W N v' ∧ v' ≤ v ∧
      (∀ u ∈ reps,
        minCharge (K := K) u.arity
          ((sourcePeaks u).1 - (sourcePeaks u).2) (sourcePeaks u).1 =
            (u.charge : WithTop Nat)) ∧
      (∀ u ∈ reps, u.charge ≤ 27 * u.arity ^ 3) ∧
      labels.length = reps.length ∧
      labels.map Paper.AffineNat.Label.k = reps.map F2Source.arity ∧
      (∀ label ∈ labels,
        label.d = profileD reps label.k ∧
        label.c = profileC reps label.k ∧
        minCharge (K := K) label.k
          (profileD reps label.k) (profileA reps label.k) =
            (profileC reps label.k : WithTop Nat)) ∧
      Paper.AffineActual.ActualWord (K := K)
        (profileA reps) (profileD reps) (profileC reps)
        1 (1 * W) labels := by
  let prov := provider (root := W) hK
  have hrel := cost_relevant price hcost
  obtain ⟨v',hcat,hle⟩ :=
    replacement_cost (entry hK) (catalog K W) W prov price hcost hrel
  let keys := l.map prov.pick
  let reps := keys.map (rawEntry hK)
  have hkeyShared : ArityInj (fun i => (entry hK i).arity) keys := by
    exact replacement_shared (entry hK) (catalog K W) W prov l
      hrel hshared
  have hrepShared : ArityInj F2Source.arity reps :=
    mapped_trace_shared hK keys hkeyShared
  have hrepCost : CostL (rawProblem price) reps W N v' :=
    mapped_trace_cost hK price keys W N v' hcat
  have hrepMin : ∀ u ∈ reps,
      minCharge (K := K) u.arity
        ((sourcePeaks u).1 - (sourcePeaks u).2) (sourcePeaks u).1 =
          (u.charge : WithTop Nat) := by
    intro u hu
    obtain ⟨key,hkey,rfl⟩ := List.mem_map.mp hu
    obtain ⟨t,ht,hkeyeq⟩ := List.mem_map.mp hkey
    subst key
    have hr : Relevant W t := hrel t ht
    have hs := rawEntry_pick_spec hK t hr
    have hm := rawEntry_pick_minCharge hK t hr
    simpa [prov, provider, hs.1, hs.2.1] using hm.symm
  have hrepCap : ∀ u ∈ reps, u.charge ≤ 27 * u.arity ^ 3 := by
    intro u hu
    obtain ⟨key,hkey,rfl⟩ := List.mem_map.mp hu
    obtain ⟨t,ht,hkeyeq⟩ := List.mem_map.mp hkey
    subst key
    have hr : Relevant W t := hrel t ht
    have hs := rawEntry_pick_spec hK t hr
    have hc := rawEntry_pick_charge_cap hK t hr
    simpa [prov, provider, hs.1] using hc
  obtain ⟨labels,hlen,hkeys,hsharedLabel,hactual⟩ :=
    shared_minimal_ladder_actual price hrepCost hrepShared hW hrepMin
  exact ⟨reps,v',labels,hrepShared,hrepCost,hle,hrepMin,hrepCap,
    hlen,hkeys,hsharedLabel,hactual⟩

end Paper.A2ActualForward
/- END Transfer.lean -/

/- BEGIN Typed.lean source_sha256=e0694c392253a68ad4a8276dc3cbea0dd7c16d5eb4f90acae201d25e3aa661c5 body_sha256=0d665fdc48bddb8e73c19c3cc72fc124595f69e57470aa23f385b8007fe2d068 -/

namespace Paper.A2ActualForward

open Coupled.Formal Paper.F2CatalogTransfer
open Paper.F6TypedBridge Paper.CountStage.TypedDecorationWords

/-- A positive-width shared original raw ladder transfers to an actual
minimum-profile F6 word whose decorated labels belong to the corrected
finite typed-word grammar at their exact product budget. -/
theorem original_to_typed_actual {K W N v : Nat} (hK : 2 ≤ K)
    (hW : 1 ≤ W) (price : Nat → Nat)
    (l : List (F2Source K))
    (hshared : ArityInj F2Source.arity l)
    (hcost : CostL (rawProblem price) l W N v) :
    ∃ (reps : List (F2Source K)) (v' : Nat)
      (labels : List Paper.AffineNat.Label),
      ArityInj F2Source.arity reps ∧
      CostL (rawProblem price) reps W N v' ∧ v' ≤ v ∧
      Paper.AffineActual.ActualWord (K := K)
        (profileA reps) (profileD reps) (profileC reps)
        1 (1 * W) labels ∧
      labels.map toTyped ∈
        consistentBudgetWordsFixed K
          (qProduct labelQ (labels.map toTyped)) := by
  obtain ⟨reps,v',labels,hrepShared,hrepCost,hle,_,hrepCap,_,hkeys,
      hsharedLabel,hactual⟩ :=
    original_to_actual_minimal hK hW price l hshared hcost
  have hbounds := aligned_label_bounds hrepShared hkeys
    (fun label hmem => (hsharedLabel label hmem).2.1) hrepCap
  have hfixed : labels.map toTyped ∈
      consistentBudgetWordsFixed K
        (qProduct labelQ (labels.map toTyped)) := by
    apply actual_labels_in_fixed_words K
      (qProduct labelQ (labels.map toTyped)) labels
      (profileD reps) (profileC reps)
    · intro label hmem
      exact ⟨(hbounds label hmem).2.1, (hbounds label hmem).2.2⟩
    · intro label hmem
      exact ⟨(hsharedLabel label hmem).1,
        (hsharedLabel label hmem).2.1⟩
    · exact le_refl _
  exact ⟨reps,v',labels,hrepShared,hrepCost,hle,hactual,hfixed⟩

end Paper.A2ActualForward
/- END Typed.lean -/

/- BEGIN Calls.lean source_sha256=15aa06a99a04f152c6701202cbd867ed7a49e1e3d428153ac4132e841dd50f1e body_sha256=5f4a5e4543172ba9c00d69cffb2b4077860e8c6fdb31dda4c13bfe42546d8c3c -/

namespace Paper.A2Budget

open Coupled.Formal Paper.F2CatalogTransfer
open Paper.PPEndToEnd
open Paper.F6TypedBridge Paper.CountStage.TypedDecorationWords

theorem source_child_pos {K : Nat} (t : F2Source K) (w : Nat) :
    1 ≤ t.childWidth w := by
  rw [source_childWidth_eq_profile]
  change 1 ≤ w / t.arity + 1 +
    max (sourcePeaks t).1 ((sourcePeaks t).2 + w % t.arity)
  exact (Nat.le_add_left 1 (w / t.arity)).trans
    (Nat.le_add_right _ _)

/-- The repeated call factor of a positive-width raw F2 ladder is bounded by
its PP cost whenever the initial multiplicity is positive. -/
theorem calls_product_le_raw_cost {K : Nat} (price : Nat → Nat)
    {ts : List (F2Source K)} {w N v : Nat}
    (hcost : CostL (rawProblem price) ts w N v) :
    1 ≤ N → 1 ≤ w → N * (ts.map F2Source.calls).prod ≤ v := by
  induction hcost with
  | base w N =>
      intro hN hw
      have hw2 : 1 ≤ w ^ 2 := by nlinarith
      have hmul : N ≤ N * w ^ 2 := by
        simpa using Nat.mul_le_mul_left N hw2
      have hleaf : N * w ^ 2 ≤ leafPP price N w := by
        unfold leafPP
        omega
      simpa [rawProblem] using hmul.trans hleaf
  | step t rest w N v hstrict htail ih =>
      intro hN hw
      have hcall : 1 ≤ t.calls := by
        have hk := t.source.hk
        simp only [F2Source.calls, F2Source.arity]
        omega
      have hN' : 1 ≤ N * t.calls := by nlinarith
      have hchild := source_child_pos t w
      have htailBound := ih hN' hchild
      calc
        N * ((t :: rest).map F2Source.calls).prod =
            (N * t.calls) * (rest.map F2Source.calls).prod := by
              simp [Nat.mul_assoc]
        _ ≤ v := htailBound
        _ ≤ N * (rawProblem price).own t w (t.childWidth w) + v :=
          Nat.le_add_left v _

theorem typed_product_eq_calls {K : Nat}
    {ts : List (F2Source K)} {labels : List Paper.AffineNat.Label}
    (hkeys : labels.map Paper.AffineNat.Label.k =
      ts.map F2Source.arity) :
    qProduct labelQ (labels.map toTyped) =
      (ts.map F2Source.calls).prod := by
  have hfirst : (labels.map toTyped).map labelQ =
      labels.map (fun label => 2 * (label.k - 1) + 1) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro label hmem
    dsimp [Function.comp_apply, labelQ, toTyped]
    have hk := label.hk
    omega
  have hsecond : labels.map (fun label => 2 * (label.k - 1) + 1) =
      ts.map F2Source.calls := by
    calc
      labels.map (fun label => 2 * (label.k - 1) + 1) =
          (labels.map Paper.AffineNat.Label.k).map
            (fun k => 2 * (k - 1) + 1) := by simp [List.map_map]
      _ = (ts.map F2Source.arity).map
            (fun k => 2 * (k - 1) + 1) := by rw [hkeys]
      _ = ts.map F2Source.calls := by
            simp [List.map_map, F2Source.calls]
  unfold qProduct
  rw [hfirst, hsecond]

end Paper.A2Budget
/- END Calls.lean -/

/- BEGIN Root.lean source_sha256=d1652851796d748c38786b78a693363e171af95cc89a286486c3c648e29b27e8 body_sha256=dd07c5f57615cdd6c5545684b25ec2a5488deaf898ef62efd73716bd9c5b5038 -/

namespace Paper.A2Budget

open Coupled.Formal Paper.F2CatalogTransfer
open Paper.A2ActualForward Paper.F6TypedBridge
open Paper.CountStage.TypedDecorationWords
open Paper.CountStage.StopBudget Paper.ComputableProfileProvider
open Paper.PPEndToEnd

theorem fixed_words_budget_mono {K U V : Nat}
    {w : List DecoratedLabel} (hUV : U ≤ V)
    (hw : w ∈ consistentBudgetWordsFixed K U) :
    w ∈ consistentBudgetWordsFixed K V := by
  have hmem := List.mem_filter.mp hw
  have hq : ∀ x : DecoratedLabel, 3 ≤ labelQ x := by
    intro x
    have hk := x.arity.property
    unfold labelQ
    omega
  have hs := typedBudgetWords_sound
    (decorationLabels K) labelQ hq U w hmem.1
  apply consistentBudgetWordsFixed_complete K V w hs.2 (hs.1.trans hUV)
  simpa [repeatedArityConsistentFixed] using hmem.2

/-- The transferred actual word fits the cost of its own representative
ladder, not merely an ad hoc product budget. -/
theorem original_to_typed_cost_budget {K W N v : Nat}
    (hK : 2 ≤ K) (hW : 1 ≤ W) (hN : 1 ≤ N)
    (price : Nat → Nat) (l : List (F2Source K))
    (hshared : ArityInj F2Source.arity l)
    (hcost : CostL (rawProblem price) l W N v) :
    ∃ (reps : List (F2Source K)) (v' : Nat)
      (labels : List Paper.AffineNat.Label),
      ArityInj F2Source.arity reps ∧
      CostL (rawProblem price) reps W N v' ∧ v' ≤ v ∧
      Paper.AffineActual.ActualWord (K := K)
        (profileA reps) (profileD reps) (profileC reps)
        1 (1 * W) labels ∧
      qProduct labelQ (labels.map toTyped) ≤ v' ∧
      labels.map toTyped ∈ consistentBudgetWordsFixed K v' := by
  obtain ⟨reps,v',labels,hrepShared,hrepCost,hle,_,hrepCap,_,hkeys,
      hsharedLabel,hactual⟩ :=
    original_to_actual_minimal hK hW price l hshared hcost
  have hbounds := aligned_label_bounds hrepShared hkeys
    (fun label hmem => (hsharedLabel label hmem).2.1) hrepCap
  have hqCalls := calls_product_le_raw_cost price hrepCost hN hW
  have hfactor : (reps.map F2Source.calls).prod ≤
      N * (reps.map F2Source.calls).prod := by
    simpa using Nat.mul_le_mul_right
      (reps.map F2Source.calls).prod hN
  have hq : qProduct labelQ (labels.map toTyped) ≤ v' := by
    rw [typed_product_eq_calls hkeys]
    exact hfactor.trans hqCalls
  have hfixed : labels.map toTyped ∈ consistentBudgetWordsFixed K v' := by
    apply actual_labels_in_fixed_words K v' labels
      (profileD reps) (profileC reps)
    · intro label hmem
      exact ⟨(hbounds label hmem).2.1, (hbounds label hmem).2.2⟩
    · intro label hmem
      exact ⟨(hsharedLabel label hmem).1,
        (hsharedLabel label hmem).2.1⟩
    · exact hq
  exact ⟨reps,v',labels,hrepShared,hrepCost,hle,hactual,hq,hfixed⟩

/-- At unit initial multiplicity, the exact optimizer's transferred actual
typed word lies in the finite root stopping-budget grammar. This remains an
exhaustive construction, with no uniform polynomial synthesis claim. -/
theorem optimizer_typed_root {K W : Nat} (hK : 2 ≤ K) (hW : 1 ≤ W) :
    ∃ (reps : List (F2Source K)) (v' : Nat)
      (labels : List Paper.AffineNat.Label),
      ArityInj F2Source.arity reps ∧
      CostL (rawProblem tauRS) reps W 1 v' ∧
      v' = (optimize K W 1).benchmarkCost tauRS 1 ∧
      qProduct labelQ (labels.map toTyped) ≤ rootStopBudget W ∧
      Paper.AffineActual.ActualWord (K := K)
        (profileA reps) (profileD reps) (profileC reps)
        1 (1 * W) labels ∧
      labels.map toTyped ∈ consistentBudgetWordsFixed K
        (rootStopBudget W) := by
  obtain ⟨l,hshared,hcost⟩ := optimize_raw_attained K W 1
  obtain ⟨reps,v',labels,hrepShared,hrepCost,hv,hactual,hprod,hfixed⟩ :=
    original_to_typed_cost_budget hK hW (by decide) tauRS l hshared hcost
  have hoptLe := (optimize_all_raw K W 1).2.2
    reps v' hrepShared hrepCost
  have hoptEq : v' = (optimize K W 1).benchmarkCost tauRS 1 :=
    Nat.le_antisymm hv hoptLe
  have hbase : CostL (rawProblem tauRS)
      ([] : List (F2Source K)) W 1 (leafPP tauRS 1 W) :=
    CostL.base W 1
  have hempty : ArityInj F2Source.arity ([] : List (F2Source K)) := by
    simp [ArityInj]
  have hopt := (optimize_all_raw K W 1).2.2
    [] (leafPP tauRS 1 W) hempty hbase
  have hroot : (optimize K W 1).benchmarkCost tauRS 1 ≤
      rootStopBudget W := by
    change (optimize K W 1).benchmarkCost tauRS 1 ≤
      leafPP tauExact 1 W
    rw [← tauRS_eq_tauExact_fun]
    exact hopt
  have hvroot : v' ≤ rootStopBudget W := hv.trans hroot
  have hprodRoot : qProduct labelQ (labels.map toTyped) ≤
      rootStopBudget W := hprod.trans hvroot
  have hfixedRoot := fixed_words_budget_mono hvroot hfixed
  exact ⟨reps,v',labels,hrepShared,hrepCost,hoptEq,
    hprodRoot,hactual,hfixedRoot⟩

end Paper.A2Budget
/- END Root.lean -/

/- BEGIN Cost.lean source_sha256=7535a8ea10ce6eb1aa3ad58dcb4d0928ad37e7dcb156da5af264c0892c3859d5 body_sha256=f59b426d8404acb6d630321e5a9a1ee4a87c85c0f39fbe3f9d542f1a8969853e -/

namespace Paper.F6SharedExact

open Paper.AffineNat Paper.AffineILP Paper.AffineChain Paper.AffineActual
open Paper.F2CatalogTransfer Paper.PPEndToEnd Paper.F6CostBridge
open Paper.F6Objective Coupled.Formal

theorem shared_actual_cost_exact {K : Nat} (a d c : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x : ℤ) (hP : 0 < P)
    (hactual : ActualWord (K := K) a d c P x labels)
    (hpos : PositiveWidths P x
      (labels.map (Paper.AffineNat.instantiate a)))
    (price : Nat → Nat) (N : Nat) :
    ∃ (w : Nat) (ts : List (F2Source K)) (v : Nat),
      x = P * w ∧ ts.length = labels.length ∧
      CostL (F6CostBridge.rawProblem price) ts w N v ∧
      (∀ t ∈ ts, Paper.AffineTable.tableAt (K := K) a d c t.arity = some t) ∧
      ArityInj F2Source.arity ts ∧
      (v : ℤ) = affineSum a c N P x labels +
        (leafPP price (finalN N labels) (terminalNat P x a labels) : ℤ) := by
  induction labels generalizing P x N with
  | nil =>
      obtain ⟨w, hx, hw⟩ := hactual
      have hterminal : terminalNat P x a [] = w := by
        simp [terminalNat, terminalWidth, terminalProduct, hx,
          Int.mul_ediv_cancel_left _ (ne_of_gt hP)]
      exact ⟨w, [], leafPP price N w, hx, rfl, CostL.base w N,
        by simp, by intro t ht; simp at ht,
        by simp [affineSum, finalN, hterminal]⟩
  | cons label rest ih =>
      obtain ⟨t, w, ht, hspec, hx, hr, hnext, hstrict, hrest⟩ := hactual
      have hkpos : 0 < (label.k : ℤ) := by
        have hkn : 0 < label.k :=
          lt_of_lt_of_le (by decide : 0 < 2) label.hk
        exact_mod_cast hkn
      have hPk : 0 < P * label.k := mul_pos hP hkpos
      let next := nextWidth P x (Paper.AffineNat.instantiate a label)
      have hnext' : next = P * label.k * (t.childWidth w : ℤ) := hnext
      let N' := N * (2 * (label.k - 1) + 1)
      have hcall : t.calls = 2 * (label.k - 1) + 1 := by
        change 2 * (t.source.k - 1) + 1 = 2 * (label.k - 1) + 1
        exact congrArg (fun k => 2 * (k - 1) + 1) hspec.1
      have hpos' : PositiveWidths (P * label.k) next
          (rest.map (Paper.AffineNat.instantiate a)) := hpos.2
      obtain ⟨w', ts, v, hx', hlen, hcost, hselected, hinj, hval⟩ :=
        ih (P * label.k) next hPk hrest hpos' N'
      have hwidth : w' = t.childWidth w := by
        have heq : (P * label.k) * (w' : ℤ) =
            (P * label.k) * (t.childWidth w : ℤ) := by
          calc
            _ = next := hx'.symm
            _ = _ := hnext'
        have hwi : (w' : ℤ) = (t.childWidth w : ℤ) :=
          mul_left_cancel₀ (ne_of_gt hPk) heq
        exact_mod_cast hwi
      have hchild : 1 ≤ t.childWidth w := by
        have hq : 1 ≤ next / (P * label.k) := by
          cases rest with
          | nil => exact hpos'
          | cons q tail => exact hpos'.1
        rw [hnext', Int.mul_ediv_cancel_left _ (ne_of_gt hPk)] at hq
        exact_mod_cast hq
      subst w'
      have hstep : CostL (F6CostBridge.rawProblem price) (t :: ts) w N
          (N * ownPP t.charge (t.childWidth w) + v) := by
        apply CostL.step t ts w N v
        · simpa only [rawProblem_child] using hstrict
        · simpa only [rawProblem_child, rawProblem_calls, hcall] using hcost
      have hcharge : t.charge = c label.k := hspec.2.1
      have hlocal : (N * ownPP t.charge (t.childWidth w) : ℤ) =
          8 * (N : ℤ) * (c label.k : ℤ) *
            (next / (P * label.k) - 1) := by
        rw [ownPP_cast N t.charge (t.childWidth w) hchild, hcharge]
        rw [hnext', Int.mul_ediv_cancel_left _ (ne_of_gt hPk)]
      have hselected' : ∀ u ∈ t :: ts,
          Paper.AffineTable.tableAt (K := K) a d c u.arity = some u := by
        intro u hu
        rcases List.mem_cons.mp hu with heq | htail
        · subst u
          simpa only [hspec.1] using ht
        · exact hselected u htail
      have hinj' := Paper.F6SharedCost.arityInj_of_tableAt a d c
        (t :: ts) hselected'
      refine ⟨w, t :: ts, _, hx, ?_, hstep, hselected', hinj', ?_⟩
      · simp [hlen]
      · rw [Nat.cast_add, Nat.cast_mul]
        rw [hlocal, hval]
        change
          8 * (N : ℤ) * (c label.k : ℤ) * (next / (P * label.k) - 1) +
            (affineSum a c N' (P * label.k) next rest +
              (leafPP price (finalN N' rest)
                (terminalNat (P * label.k) next a rest) : ℤ)) =
          (8 * (N : ℤ) * (c label.k : ℤ) * (next / (P * label.k) - 1) +
            affineSum a c N' (P * label.k) next rest) +
              (leafPP price (finalN N' rest)
                (terminalNat (P * label.k) next a rest) : ℤ)
        ring


end Paper.F6SharedExact
/- END Cost.lean -/

/- BEGIN Forward.lean source_sha256=c19f41614ebcaa8db6ea48cdccc3231446b37abca342c4f9126ba0fda6192aee body_sha256=3252ba4af8f3da2773128d9bca14095bbf7679f548ade6a564df08d9293428ca -/

namespace Paper.A2Feasible

open Paper.AffineNat Paper.AffineILP Paper.AffineChain
open Paper.AffineActual Paper.AffineConverse
open Paper.F6Objective Paper.F6Cleared Paper.F6ILPSound
open Paper.F6ILPFeasible Paper.PPEndToEnd
open Paper.F6SharedExact Coupled.Formal Paper.F2CatalogTransfer

/-- The integer objective identified by the exact shared-cost theorem. -/
def exactSharedCost (a c : Nat → Nat) (labels : List Label)
    (x : ℤ) (price : Nat → Nat) (N : Nat) : ℤ :=
  affineSum a c N 1 x labels +
    (leafPP price (finalN N labels) (terminalNat 1 x a labels) : ℤ)

theorem exact_shared_cost_witness {K : Nat}
    (a d c : Nat → Nat) (labels : List Label)
    (x : ℤ) (price : Nat → Nat) (N : Nat)
    (hactual : ActualWord (K := K) a d c 1 x labels) :
    ∃ (w : Nat) (ts : List (F2Source K)) (v : Nat),
      x = 1 * w ∧ ts.length = labels.length ∧
      CostL (Paper.F6CostBridge.rawProblem price) ts w N v ∧
      ArityInj F2Source.arity ts ∧
      (v : ℤ) = exactSharedCost a c labels x price N := by
  obtain ⟨z,hz,hterminal,hcontract⟩ :=
    actual_to_constraints a d c labels 1 x (by decide) hactual
  have hzI : 1 ≤ (z : ℤ) := by exact_mod_cast hz
  have hboth := terminal_cleared_positive 1 x
    (labels.map (instantiate a)) (z : ℤ)
    (by decide) hzI hterminal hcontract
  obtain ⟨w,ts,v,hx,hlen,hcost,_,hinj,hvalue⟩ :=
    shared_actual_cost_exact a d c labels 1 x (by decide)
      hactual hboth.2 price N
  exact ⟨w,ts,v,hx,hlen,hcost,hinj,
    by simpa [exactSharedCost] using hvalue⟩

/-- An actual F6 word with a bounded exact shared cost gives a concrete
feasible integer point for any prescribed profile intervals containing a.
The interval premise is explicit and may come from the F4 plateau system. -/
theorem actual_to_feasible_of_exact_cost {K : Nat}
    (a d c lo hi : Nat → Nat) (labels : List Label)
    (x : ℤ) (price : Nat → Nat) (N T : Nat)
    (hactual : ActualWord (K := K) a d c 1 x labels)
    (hinterval : ∀ key : Paper.F6ILP.Variable labels,
      lo key.val ≤ a key.val ∧ a key.val ≤ hi key.val)
    (hcost : exactSharedCost a c labels x price N ≤ (T : ℤ)) :
    ∃ z : ℤ, 1 ≤ z ∧
      Feasible labels x z c lo hi price N T
        (fun key => (a key.val : ℤ)) := by
  obtain ⟨z,hz,hterminal,hcontract⟩ :=
    actual_to_constraints a d c labels 1 x (by decide) hactual
  let ds := labels.map (instantiate a)
  let D := terminalProduct 1 ds
  have hzI : 1 ≤ (z : ℤ) := by exact_mod_cast hz
  have hterminal' : terminalWidth 1 x ds = D * (z : ℤ) := hterminal
  have hboth := terminal_cleared_positive 1 x ds (z : ℤ)
    (by decide) hzI hterminal' hcontract
  have hclear : D * affineSum a c N 1 x labels =
      clearedSum D a c N 1 x labels :=
    clear_affineSum a c N labels 1 x (by decide) hboth.1
  have hD : 0 < D := terminalProduct_pos 1 ds (by decide)
  have hterminalNat : terminalNat 1 x a labels = z := by
    simpa using terminalNat_eq a labels 1 x (z : ℤ)
      (by decide) hterminal'
  have hbound : affineSum a c N 1 x labels +
      (leafPP price (finalN N labels) z : ℤ) ≤ T := by
    simpa [exactSharedCost, hterminalNat] using hcost
  have hscaled : D * affineSum a c N 1 x labels ≤
      D * ((T : ℤ) -
        (leafPP price (finalN N labels) z : ℤ)) := by
    have hsmall : affineSum a c N 1 x labels ≤
        (T : ℤ) - (leafPP price (finalN N labels) z : ℤ) := by
      omega
    exact mul_le_mul_of_nonneg_left hsmall hD.le
  have hbudget : clearedSum D a c N 1 x labels ≤
      D * ((T : ℤ) -
        (leafPP price (finalN N labels) (z : ℤ).toNat : ℤ)) := by
    rw [← hclear]
    simpa using hscaled
  refine ⟨z,hzI,?_⟩
  exact canonical_to_feasible labels x z a c lo hi price N T
    hterminal' hcontract hbudget hinterval

theorem actual_to_feasible_singleton {K : Nat}
    (a d c : Nat → Nat) (labels : List Label)
    (x : ℤ) (price : Nat → Nat) (N T : Nat)
    (hactual : ActualWord (K := K) a d c 1 x labels)
    (hcost : exactSharedCost a c labels x price N ≤ (T : ℤ)) :
    ∃ z : ℤ, 1 ≤ z ∧
      Feasible labels x z c a a price N T
        (fun key => (a key.val : ℤ)) := by
  exact actual_to_feasible_of_exact_cost a d c a a labels x price N T
    hactual (by intro key; exact ⟨le_refl _,le_refl _⟩) hcost

end Paper.A2Feasible
/- END Forward.lean -/

/- BEGIN CostLink.lean source_sha256=d227323301be2c53b4d7e45bd528881d18903ff1d814b198989c9b732200df46 body_sha256=bb1c0afaa6e4f049d600de9c6d490a9bdc8bb442adcb3cee5417e29d5ef845a9 -/

namespace Paper.A2Feasible

open Coupled.Formal Paper.F2CatalogTransfer Paper.PPEndToEnd
open Paper.AffineNat Paper.AffineILP Paper.AffineTable
open Paper.AffineActual Paper.F6Objective
open Paper.A2ActualForward

/-- An aligned actual word computes the cost of the given raw ladder itself.
The table selected by `tableAt` may differ from that ladder's representative,
but `TableSpec` fixes its child widths and charge at each arity. -/
theorem aligned_raw_cost_exact {K : Nat} (a d c : Nat → Nat)
    (price : Nat → Nat) {ts : List (F2Source K)} {w N v : Nat}
    (hcost : CostL (rawProblem price) ts w N v)
    (P : ℤ) (hP : 0 < P) (labels : List Label)
    (hkeys : labels.map Label.k = ts.map F2Source.arity)
    (hspec : ∀ t ∈ ts, TableSpec a d c t.arity t)
    (hactual : ActualWord (K := K) a d c P (P * w) labels) :
    (v : ℤ) = affineSum a c N P (P * w) labels +
      (leafPP price (finalN N labels)
        (terminalNat P (P * w) a labels) : ℤ) := by
  induction hcost generalizing P labels with
  | base w N =>
      cases labels with
      | nil =>
          obtain ⟨w',hx,_⟩ := hactual
          have hw : w' = w := by
            have heq : P * (w' : ℤ) = P * (w : ℤ) := hx.symm
            have hwi := mul_left_cancel₀ (ne_of_gt hP) heq
            exact_mod_cast hwi
          subst w'
          have hterminal : terminalNat P (P * w) a [] = w := by
            simp [terminalNat, terminalWidth, terminalProduct,
              Int.mul_ediv_cancel_left _ (ne_of_gt hP)]
          simp [affineSum, finalN, hterminal, rawProblem]
      | cons label rest => simp at hkeys
  | step t ts w N v hstrict htail ih =>
      cases labels with
      | nil => simp at hkeys
      | cons label rest =>
          dsimp only [rawProblem] at ih
          have hpair : label.k = t.arity ∧
              rest.map Label.k = ts.map F2Source.arity := by
            simpa only [List.map_cons, List.cons.injEq] using hkeys
          obtain ⟨u, wu, _, hspecU, hx, _, hnext, _, hrest⟩ := hactual
          have hwu : wu = w := by
            have heq : P * (wu : ℤ) = P * (w : ℤ) := hx.symm
            have hwi := mul_left_cancel₀ (ne_of_gt hP) heq
            exact_mod_cast hwi
          subst wu
          have hspecT : TableSpec a d c t.arity t :=
            hspec t (by simp)
          have hwidth : u.childWidth w = t.childWidth w := by
            have hu := hspecU.2.2.2.2 w
            have ht := hspecT.2.2.2.2 w
            rw [← hpair.1] at ht
            exact hu.trans ht.symm
          have hkpos : 0 < (label.k : ℤ) := by
            exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) label.hk
          have hPk : 0 < P * label.k := mul_pos hP hkpos
          let next := nextWidth P (P * w) (instantiate a label)
          have hnext' : next =
              (P * label.k) * (t.childWidth w : ℤ) := by
            simpa only [hwidth] using hnext
          have hspecRest : ∀ q ∈ ts, TableSpec a d c q.arity q := by
            intro q hq
            exact hspec q (List.mem_cons_of_mem t hq)
          have hcall : t.calls = 2 * (label.k - 1) + 1 := by
            change 2 * (t.source.k - 1) + 1 =
              2 * (label.k - 1) + 1
            exact congrArg (fun k => 2 * (k - 1) + 1) hpair.1.symm
          have hrest' : ActualWord (K := K) a d c
              (P * label.k) ((P * label.k) * (t.childWidth w : ℤ))
              rest := by
            change ActualWord (K := K) a d c (P * label.k) next rest at hrest
            rw [hnext'] at hrest
            exact hrest
          have hvalue := ih (P * label.k) hPk rest hpair.2
            hspecRest hrest'
          have hcharge : t.charge = c label.k := by
            rw [hpair.1]
            exact hspecT.2.1
          have hlocal : (N * ownPP t.charge (t.childWidth w) : ℤ) =
              8 * (N : ℤ) * (c label.k : ℤ) *
                (next / (P * label.k) - 1) := by
            rw [ownPP_cast N t.charge (t.childWidth w)
              (Paper.A2Budget.source_child_pos t w), hcharge]
            rw [hnext', Int.mul_ediv_cancel_left _ (ne_of_gt hPk)]
          dsimp only [rawProblem] at ⊢
          rw [Nat.cast_add, Nat.cast_mul, hlocal, hvalue]
          rw [← hnext']
          change
            8 * (N : ℤ) * (c label.k : ℤ) *
                (next / (P * label.k) - 1) +
              (affineSum a c (N * t.calls) (P * label.k) next rest +
                (leafPP price (finalN (N * t.calls) rest)
                  (terminalNat (P * label.k) next a rest) : ℤ)) =
            (8 * (N : ℤ) * (c label.k : ℤ) *
                (next / (P * label.k) - 1) +
              affineSum a c (N * (2 * (label.k - 1) + 1))
                (P * label.k) next rest) +
              (leafPP price
                (finalN (N * (2 * (label.k - 1) + 1)) rest)
                (terminalNat (P * label.k) next a rest) : ℤ)
          rw [hcall]
          ring

end Paper.A2Feasible
/- END CostLink.lean -/

/- BEGIN Optimal.lean source_sha256=fd8c4ea5ac5a86fdf47915b61d805aefb902f97bb7af952cb0bdb6d91c095e1e body_sha256=0e1bf7e44f30613bcba2d9d76b1420b6865a08e6cfa3e1f35bd89ef293f9acea -/

namespace Paper.A2Feasible

open Coupled.Formal Paper.F2CatalogTransfer Paper.PPEndToEnd
open Paper.A2ActualForward Paper.A2Budget Paper.AffineNat
open Paper.AffineActual Paper.F6ILPFeasible Paper.F6ILP Paper.CountStage.StopBudget
open Paper.ComputableProfileProvider
open Paper.F6TypedBridge Paper.CountStage.TypedDecorationWords

/-- The exhaustive PP optimizer has an attained, root-budget actual word whose
affine objective is its own representative raw cost. Any externally supplied
profile intervals containing that word's profile therefore admit a concrete
F6 integer feasible point. This does not synthesize those intervals uniformly. -/
theorem optimizer_actual_feasible_root {K W : Nat}
    (hK : 2 ≤ K) (hW : 1 ≤ W) :
    ∃ (reps : List (F2Source K)) (v' : Nat) (labels : List Label),
      ArityInj F2Source.arity reps ∧
      CostL (rawProblem tauRS) reps W 1 v' ∧
      v' = (optimize K W 1).benchmarkCost tauRS 1 ∧
      labels.map Label.k = reps.map F2Source.arity ∧
      (∀ label ∈ labels,
        Paper.F4ChargeIntervals.minCharge (K := K) label.k
          (profileD reps label.k) (profileA reps label.k) =
            (profileC reps label.k : WithTop Nat)) ∧
      (∀ label ∈ labels,
        label.d = profileD reps label.k ∧
        label.c = profileC reps label.k ∧
        2 ≤ label.k ∧ label.k ≤ K ∧
        label.c ≤ 27 * label.k ^ 3) ∧
      qProduct labelQ (labels.map toTyped) ≤ rootStopBudget W ∧
      labels.map toTyped ∈
        consistentBudgetWordsFixed K (rootStopBudget W) ∧
      ActualWord (K := K) (profileA reps) (profileD reps)
        (profileC reps) 1 (1 * W) labels ∧
      exactSharedCost (profileA reps) (profileC reps) labels
        (1 * W) tauRS 1 = (v' : ℤ) ∧
      v' ≤ rootStopBudget W ∧
      ∀ (lo hi : Nat → Nat),
        (∀ key : Variable labels,
          lo key.val ≤ profileA reps key.val ∧
          profileA reps key.val ≤ hi key.val) →
        ∃ z : ℤ, 1 ≤ z ∧
          Feasible labels (1 * W) z (profileC reps)
            lo hi tauRS 1 (rootStopBudget W)
            (fun key => (profileA reps key.val : ℤ)) := by
  obtain ⟨l,hshared,hcost⟩ := optimize_raw_attained K W 1
  obtain ⟨reps,v',labels,hrepShared,hrepCost,hv,hmin,hrepCap,_,hkeys,
      hsharedLabel,hactual⟩ :=
    original_to_actual_minimal hK hW tauRS l hshared hcost
  have hoptLe := (optimize_all_raw K W 1).2.2
    reps v' hrepShared hrepCost
  have hoptEq : v' = (optimize K W 1).benchmarkCost tauRS 1 :=
    Nat.le_antisymm hv hoptLe
  have hspec : ∀ t ∈ reps,
      Paper.AffineTable.TableSpec (profileA reps) (profileD reps)
        (profileC reps) t.arity t :=
    fun t ht => tableSpec_of_shared_min hrepShared ht
  have hcostCast := aligned_raw_cost_exact
    (profileA reps) (profileD reps) (profileC reps)
    tauRS hrepCost 1 (by decide) labels hkeys hspec hactual
  have hcostExact : exactSharedCost (profileA reps) (profileC reps)
      labels (1 * W) tauRS 1 = (v' : ℤ) := by
    exact hcostCast.symm
  have hbase : CostL (rawProblem tauRS)
      ([] : List (F2Source K)) W 1 (leafPP tauRS 1 W) :=
    CostL.base W 1
  have hempty : ArityInj F2Source.arity ([] : List (F2Source K)) := by
    simp [ArityInj]
  have hopt := (optimize_all_raw K W 1).2.2
    [] (leafPP tauRS 1 W) hempty hbase
  have hroot : (optimize K W 1).benchmarkCost tauRS 1 ≤
      rootStopBudget W := by
    change (optimize K W 1).benchmarkCost tauRS 1 ≤
      leafPP tauExact 1 W
    rw [← tauRS_eq_tauExact_fun]
    exact hopt
  have hvroot : v' ≤ rootStopBudget W := hoptEq.le.trans hroot
  have hbounds := aligned_label_bounds hrepShared hkeys
    (fun label hmem => (hsharedLabel label hmem).2.1) hrepCap
  have hqCalls : (reps.map F2Source.calls).prod ≤ v' := by
    simpa using calls_product_le_raw_cost tauRS hrepCost
      (by decide) hW
  have hq : qProduct labelQ (labels.map toTyped) ≤
      rootStopBudget W := by
    rw [typed_product_eq_calls hkeys]
    exact hqCalls.trans hvroot
  have hfixed : labels.map toTyped ∈
      consistentBudgetWordsFixed K (rootStopBudget W) := by
    apply actual_labels_in_fixed_words K (rootStopBudget W) labels
      (profileD reps) (profileC reps)
    · intro label hmem
      exact ⟨(hbounds label hmem).2.1,
        (hbounds label hmem).2.2⟩
    · intro label hmem
      exact ⟨(hsharedLabel label hmem).1,
        (hsharedLabel label hmem).2.1⟩
    · exact hq
  refine ⟨reps,v',labels,hrepShared,hrepCost,hoptEq,hkeys,
    (fun label hmem => (hsharedLabel label hmem).2.2),
    (fun label hmem => ⟨(hsharedLabel label hmem).1,
      (hsharedLabel label hmem).2.1,
      (hbounds label hmem).1,
      (hbounds label hmem).2.1,
      (hbounds label hmem).2.2⟩),
    hq,hfixed,hactual,hcostExact,hvroot,?_⟩
  intro lo hi hinterval
  apply actual_to_feasible_of_exact_cost
    (profileA reps) (profileD reps) (profileC reps)
    lo hi labels (1 * W) tauRS 1 (rootStopBudget W)
    hactual hinterval
  rw [hcostExact]
  exact_mod_cast hvroot

end Paper.A2Feasible
/- END Optimal.lean -/

/- BEGIN Intervals.lean source_sha256=fbf6463a661a53d59430c7b2d9e4cb2f2b4e63c99554c1c931907bb413b4bfbc body_sha256=4b4307e8b631dcaab10461347eec1025282ae47ce12e5a971132597c023b00ad -/

namespace Paper.A2Feasible

open Coupled.Formal Paper.F2CatalogTransfer
open Paper.A2ActualForward Paper.ComputableProfileProvider
open Paper.F4ChargeIntervals Paper.AffineNat Paper.F6ILP

/-- The exact minimum-charge level set at fixed arity, kink, charge and root.
It is independent of any selected ladder or profile witness. -/
noncomputable def levelSet (K W k d c : Nat) : Finset Nat := by
  classical
  exact (Finset.range (W + 1)).filter
    (fun a => minCharge (K := K) k d a = (c : WithTop Nat))

/-- Empty levels receive an impossible interval. -/
noncomputable def levelLo (K W k d c : Nat) : Nat := by
  classical
  exact if h : (levelSet K W k d c).Nonempty then
    (levelSet K W k d c).min' h else 1

noncomputable def levelHi (K W k d c : Nat) : Nat := by
  classical
  exact if h : (levelSet K W k d c).Nonempty then
    (levelSet K W k d c).max' h else 0

theorem level_mem {K W k d c a : Nat}
    (haW : a ≤ W)
    (ha : minCharge (K := K) k d a = (c : WithTop Nat)) :
    a ∈ levelSet K W k d c := by
  classical
  simp [levelSet, ha, haW]

theorem level_mem_iff {K W k d c a : Nat} :
    a ∈ levelSet K W k d c ↔
      a ≤ W ∧ minCharge (K := K) k d a = (c : WithTop Nat) := by
  classical
  simp [levelSet]

theorem level_contains {K W k d c a : Nat}
    (haW : a ≤ W)
    (ha : minCharge (K := K) k d a = (c : WithTop Nat)) :
    levelLo K W k d c ≤ a ∧ a ≤ levelHi K W k d c := by
  classical
  have hmem := level_mem haW ha
  have hn : (levelSet K W k d c).Nonempty := ⟨a,hmem⟩
  constructor
  · simpa [levelLo, hn] using Finset.min'_le _ a hmem
  · simpa [levelHi, hn] using Finset.le_max' _ a hmem

theorem level_interval_exact {K W k d c a : Nat}
    (hlo : levelLo K W k d c ≤ a)
    (hhi : a ≤ levelHi K W k d c) :
    minCharge (K := K) k d a = (c : WithTop Nat) := by
  classical
  by_cases hn : (levelSet K W k d c).Nonempty
  · have hminMem : (levelSet K W k d c).min' hn ∈
        levelSet K W k d c := Finset.min'_mem _ hn
    have hmaxMem : (levelSet K W k d c).max' hn ∈
        levelSet K W k d c := Finset.max'_mem _ hn
    have hmin : minCharge (K := K) k d
        (levelLo K W k d c) = (c : WithTop Nat) := by
      simpa [levelLo, hn] using (level_mem_iff.mp hminMem).2
    have hmax : minCharge (K := K) k d
        (levelHi K W k d c) = (c : WithTop Nat) := by
      simpa [levelHi, hn] using (level_mem_iff.mp hmaxMem).2
    exact minCharge_level_interval hlo hhi hmin hmax
  · simp [levelLo, levelHi, hn] at hlo hhi
    omega

theorem level_endpoints_le_root {K W k d c : Nat} (hW : 1 ≤ W) :
    levelLo K W k d c ≤ W ∧ levelHi K W k d c ≤ W := by
  classical
  by_cases hn : (levelSet K W k d c).Nonempty
  · have hminMem := Finset.min'_mem (levelSet K W k d c) hn
    have hmaxMem := Finset.max'_mem (levelSet K W k d c) hn
    have hminW : (levelSet K W k d c).min' hn ≤ W := by
      exact (level_mem_iff.mp hminMem).1
    have hmaxW : (levelSet K W k d c).max' hn ≤ W := by
      exact (level_mem_iff.mp hmaxMem).1
    simpa [levelLo, levelHi, hn] using And.intro hminW hmaxW
  · simp [levelLo, levelHi, hn]
    omega

theorem level_endpoints_exact_of_order {K W k d c : Nat}
    (horder : levelLo K W k d c ≤ levelHi K W k d c) :
    minCharge (K := K) k d (levelLo K W k d c) =
        (c : WithTop Nat) ∧
      minCharge (K := K) k d (levelHi K W k d c) =
        (c : WithTop Nat) := by
  classical
  by_cases hn : (levelSet K W k d c).Nonempty
  · have hminMem : (levelSet K W k d c).min' hn ∈
        levelSet K W k d c := Finset.min'_mem _ hn
    have hmaxMem : (levelSet K W k d c).max' hn ∈
        levelSet K W k d c := Finset.max'_mem _ hn
    constructor
    · simpa [levelLo, hn] using (level_mem_iff.mp hminMem).2
    · simpa [levelHi, hn] using (level_mem_iff.mp hmaxMem).2
  · simp [levelLo, levelHi, hn] at horder

theorem profileA_le_root {K W N v : Nat}
    (price : Nat → Nat) {ts : List (F2Source K)}
    (hcost : CostL (rawProblem price) ts W N v)
    (hinj : ArityInj F2Source.arity ts)
    {t : F2Source K} (ht : t ∈ ts) :
    profileA ts t.arity ≤ W := by
  rw [(common_values hinj ht).1]
  exact (relevant_peaks_bounded t ((cost_relevant price hcost) t ht)).1

/-- A finite, profile-independent alphabet of arity/kink/charge choices.
Each triple determines its own interval by `levelLo` and `levelHi`. -/
def candidateTriples (K : Nat) : Finset (Nat × Nat × Nat) := by
  classical
  exact (Finset.range (K + 1)).biUnion fun k =>
    (Finset.range k).biUnion fun d =>
      (Finset.range (27 * k ^ 3 + 1)).image fun c => (k,d,c)

theorem candidateTriple_mem {K : Nat} (k d c : Nat)
    (hk : k ≤ K) (hd : d < k) (hc : c ≤ 27 * k ^ 3) :
    (k,d,c) ∈ candidateTriples K := by
  classical
  unfold candidateTriples
  apply Finset.mem_biUnion.mpr
  refine ⟨k, by simpa using hk, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨d, by simpa using hd, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨c, by simpa using hc, rfl⟩

noncomputable def candidateIntervals (K W : Nat) :
    Finset (Nat × Nat × Nat × Nat × Nat) := by
  classical
  exact (candidateTriples K).image fun q =>
    (q.1,q.2.1,q.2.2,
      levelLo K W q.1 q.2.1 q.2.2,
      levelHi K W q.1 q.2.1 q.2.2)

theorem candidateInterval_mem {K W k d c : Nat}
    (hk : k ≤ K) (hd : d < k) (hc : c ≤ 27 * k ^ 3) :
    (k,d,c,levelLo K W k d c,levelHi K W k d c) ∈
      candidateIntervals K W := by
  classical
  unfold candidateIntervals
  apply Finset.mem_image.mpr
  exact ⟨(k,d,c), candidateTriple_mem k d c hk hd hc, rfl⟩

end Paper.A2Feasible
/- END Intervals.lean -/

/- BEGIN Terminal.lean source_sha256=b003497dfb70086c3e49cf4813e29127c23f36dd2d1a5e2e2fdb2e8f64a2fa62 body_sha256=86cfcebe6864d765fdf4d6c1add83a478326019ba9cf51690190a5e840b05243 -/

namespace Paper.A2Feasible

open Paper.AffineNat Paper.AffineILP Paper.AffineActual
open Paper.F6Objective Paper.PPEndToEnd Paper.F2CatalogTransfer
open Paper.A2Budget
open Paper.F6ILP Paper.F6ILPFeasible Paper.F6ILPSound Paper.F6Cleared

theorem actual_affineSum_nonneg {K : Nat} (a d c : Nat → Nat)
    (labels : List Label) (P x : ℤ) (hP : 0 < P)
    (hactual : ActualWord (K := K) a d c P x labels)
    (N : Nat) : 0 ≤ affineSum a c N P x labels := by
  induction labels generalizing P x N with
  | nil => simp [affineSum]
  | cons label rest ih =>
      obtain ⟨t,w,_,_,_,_,hnext,_,hrest⟩ := hactual
      have hk : 0 < (label.k : ℤ) := by
        exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) label.hk
      have hPk : 0 < P * label.k := mul_pos hP hk
      let next := nextWidth P x (instantiate a label)
      have hnext' : next =
          (P * label.k) * (t.childWidth w : ℤ) := hnext
      have hdiff : 0 ≤ next / (P * label.k) - 1 := by
        rw [hnext', Int.mul_ediv_cancel_left _ (ne_of_gt hPk)]
        have hchild : (1 : ℤ) ≤ t.childWidth w := by
          exact_mod_cast source_child_pos t w
        omega
      have hlocal : 0 ≤
          8 * (N : ℤ) * (c label.k : ℤ) *
            (next / (P * label.k) - 1) := by positivity
      have htail := ih (P * label.k) next hPk hrest
        (N * (2 * (label.k - 1) + 1))
      change 0 ≤
        8 * (N : ℤ) * (c label.k : ℤ) *
          (next / (P * label.k) - 1) +
        affineSum a c (N * (2 * (label.k - 1) + 1))
          (P * label.k) next rest
      exact add_nonneg hlocal htail

theorem finalN_positive (N : Nat) (labels : List Label)
    (hN : 1 ≤ N) : 1 ≤ finalN N labels := by
  induction labels generalizing N with
  | nil => simpa [finalN] using hN
  | cons label rest ih =>
      apply ih
      have hf : 1 ≤ 2 * (label.k - 1) + 1 := by omega
      nlinarith

theorem leafPP_ge_width (price : Nat → Nat) (N w : Nat)
    (hN : 1 ≤ N) : w ≤ leafPP price N w := by
  have hw2 : w ≤ w ^ 2 := by nlinarith
  have hmul : w ^ 2 ≤ N * w ^ 2 := by
    simpa using Nat.mul_le_mul_right (w ^ 2) hN
  unfold leafPP
  omega

/-- Every actual affine representation at positive multiplicity pays for its
terminal width. In particular, the exact optimizer's terminal width is at
most its benchmark cost, hence at most the root stopping budget. -/
theorem actual_terminal_le_exact_cost {K : Nat} (a d c : Nat → Nat)
    (labels : List Label) (x : ℤ) (price : Nat → Nat) (N v : Nat)
    (hN : 1 ≤ N)
    (hactual : ActualWord (K := K) a d c 1 x labels)
    (hvalue : exactSharedCost a c labels x price N = (v : ℤ)) :
    terminalNat 1 x a labels ≤ v := by
  have hsum := actual_affineSum_nonneg a d c labels 1 x
    (by decide) hactual N
  have hleaf := leafPP_ge_width price (finalN N labels)
    (terminalNat 1 x a labels) (finalN_positive N labels hN)
  unfold exactSharedCost at hvalue
  have hleI : (terminalNat 1 x a labels : ℤ) ≤ v := by
    have hle : (terminalNat 1 x a labels : ℤ) ≤
        (leafPP price (finalN N labels)
          (terminalNat 1 x a labels) : ℤ) := by exact_mod_cast hleaf
    omega
  exact_mod_cast hleI

/-- The same canonical feasible terminal has a numeric root-budget bound. -/
theorem bounded_actual_to_feasible {K : Nat}
    (a d c lo hi : Nat → Nat) (labels : List Label)
    (x : ℤ) (price : Nat → Nat) (N v T : Nat)
    (hN : 1 ≤ N)
    (hactual : ActualWord (K := K) a d c 1 x labels)
    (hinterval : ∀ key : Variable labels,
      lo key.val ≤ a key.val ∧ a key.val ≤ hi key.val)
    (hvalue : exactSharedCost a c labels x price N = (v : ℤ))
    (hvT : v ≤ T) :
    ∃ z : ℤ, 1 ≤ z ∧ z ≤ T ∧
      Feasible labels x z c lo hi price N T
        (fun key => (a key.val : ℤ)) := by
  have hbudget : exactSharedCost a c labels x price N ≤ (T : ℤ) := by
    rw [hvalue]
    exact_mod_cast hvT
  obtain ⟨z,hz,hfeasible⟩ := actual_to_feasible_of_exact_cost
    a d c lo hi labels x price N T hactual hinterval hbudget
  have hterminal := (feasible_nat_iff labels x z c lo hi price N T a).1
    hfeasible
  have hterminalNat : terminalNat 1 x a labels = z.toNat :=
    terminalNat_eq a labels 1 x z (by decide) hterminal.1
  have hle : z.toNat ≤ T := by
    rw [← hterminalNat]
    exact (actual_terminal_le_exact_cost a d c labels x price N v
      hN hactual hvalue).trans hvT
  have hzcast : (z.toNat : ℤ) = z :=
    Int.toNat_of_nonneg (by omega : 0 ≤ z)
  have hzT : z ≤ T := by
    have hleI : (z.toNat : ℤ) ≤ T := by exact_mod_cast hle
    simpa [hzcast] using hleI
  exact ⟨z,hz,hzT,hfeasible⟩

end Paper.A2Feasible
/- END Terminal.lean -/

/- BEGIN Candidate.lean source_sha256=cb113b66d9363cc05938fd6e34a6d6a9c918973d0207eff0149d5a0f4974c2da body_sha256=33e1115bba8ab79837a66a7aebc3aa23c0a5a548aad6f7fe66f5416d494a1480 -/

namespace Paper.A2Feasible

open Coupled.Formal Paper.F2CatalogTransfer Paper.PPEndToEnd
open Paper.A2ActualForward Paper.AffineNat Paper.AffineActual
open Paper.ComputableProfileProvider
open Paper.F6ILP Paper.F6ILPFeasible Paper.F6TypedBridge
open Paper.CountStage.TypedDecorationWords Paper.CountStage.StopBudget

/-- The finite, independently indexed charge-level intervals contain an
actual optimum and admit a canonical ILP point at its *exact* raw cost.
The terminal value of that same point is at most the exact optimum, which is
at most the root stopping budget. This is an exhaustive finite result. -/
theorem optimizer_candidate_feasible_root {K W : Nat}
    (hK : 2 ≤ K) (hW : 1 ≤ W) :
    ∃ (reps : List (F2Source K)) (v' : Nat)
      (labels : List Label) (z : ℤ),
      v' = (optimize K W 1).benchmarkCost tauRS 1 ∧
      v' ≤ rootStopBudget W ∧
      ArityInj F2Source.arity reps ∧
      CostL (rawProblem tauRS) reps W 1 v' ∧
      (∀ label ∈ labels,
        label.d = profileD reps label.k ∧
        label.c = profileC reps label.k ∧
        2 ≤ label.k ∧ label.k ≤ K ∧
        label.c ≤ 27 * label.k ^ 3) ∧
      qProduct labelQ (labels.map toTyped) ≤ rootStopBudget W ∧
      labels.map toTyped ∈
        consistentBudgetWordsFixed K (rootStopBudget W) ∧
      (∀ label ∈ labels,
        (label.k, profileD reps label.k, profileC reps label.k,
          levelLo K W label.k (profileD reps label.k)
            (profileC reps label.k),
          levelHi K W label.k (profileD reps label.k)
            (profileC reps label.k)) ∈ candidateIntervals K W) ∧
      Paper.AffineActual.ActualWord (K := K)
        (profileA reps) (profileD reps) (profileC reps)
        1 (1 * W) labels ∧
      exactSharedCost (profileA reps) (profileC reps)
        labels (1 * W) tauRS 1 = (v' : ℤ) ∧
      1 ≤ z ∧ z ≤ v' ∧
      Feasible labels (1 * W) z (profileC reps)
        (fun k => levelLo K W k (profileD reps k) (profileC reps k))
        (fun k => levelHi K W k (profileD reps k) (profileC reps k))
        tauRS 1 v' (fun key => (profileA reps key.val : ℤ)) := by
  obtain ⟨reps,v',labels,hrepShared,hrepCost,hoptEq,hkeys,hmin,
      hlabel,hq,hfixed,hactual,hcostEq,hvroot,_⟩ :=
    optimizer_actual_feasible_root hK hW
  let lo : Nat → Nat := fun k =>
    levelLo K W k (profileD reps k) (profileC reps k)
  let hi : Nat → Nat := fun k =>
    levelHi K W k (profileD reps k) (profileC reps k)
  have hinterval : ∀ key : Variable labels,
      lo key.val ≤ profileA reps key.val ∧
      profileA reps key.val ≤ hi key.val := by
    intro key
    have hmemLabels : key.val ∈ labels.map Label.k := by
      simpa only [usedArities, List.mem_toFinset] using key.property
    obtain ⟨label,hlabelMem,hlabelKey⟩ := List.mem_map.mp hmemLabels
    have hminKey : Paper.F4ChargeIntervals.minCharge (K := K)
        key.val (profileD reps key.val) (profileA reps key.val) =
        (profileC reps key.val : WithTop Nat) := by
      simpa [hlabelKey] using hmin label hlabelMem
    have hmemReps : key.val ∈ reps.map F2Source.arity := by
      rw [← hkeys]
      exact hmemLabels
    obtain ⟨t,ht,htkey⟩ := List.mem_map.mp hmemReps
    have hpeak : profileA reps key.val ≤ W := by
      simpa [htkey] using profileA_le_root tauRS hrepCost hrepShared ht
    exact level_contains hpeak hminKey
  have hcandidate : ∀ label ∈ labels,
      (label.k, profileD reps label.k, profileC reps label.k,
        lo label.k, hi label.k) ∈ candidateIntervals K W := by
    intro label hmem
    obtain ⟨hdEq,hcEq,_,hkK,hcCap⟩ := hlabel label hmem
    have hdlt : profileD reps label.k < label.k := by
      rw [← hdEq]
      exact label.hd
    have hcap : profileC reps label.k ≤ 27 * label.k ^ 3 := by
      rw [← hcEq]
      exact hcCap
    exact candidateInterval_mem hkK hdlt hcap
  obtain ⟨z,hz,hzv,hfeasible⟩ := bounded_actual_to_feasible
    (profileA reps) (profileD reps) (profileC reps)
    lo hi labels (1 * W) tauRS 1 v' v'
    (by decide) hactual hinterval hcostEq (le_refl _)
  exact ⟨reps,v',labels,z,hoptEq,hvroot,hrepShared,hrepCost,
    hlabel,hq,hfixed,by simpa [lo, hi] using hcandidate,
    hactual,hcostEq,hz,hzv,by simpa [lo, hi] using hfeasible⟩

end Paper.A2Feasible
/- END Candidate.lean -/

/- BEGIN Sound.lean source_sha256=6c6111407f8d3003c90fc38332f4bd139a5afd063f142cd7f04db420a9d93438 body_sha256=869098d91589be5e93ce5e9957cbcb51fd6446d5aa9f4aae1958f01cba26b26a -/

namespace Paper.F6SharedILP

open Paper.F6ILP Paper.F6ILPCost Paper.F6ILPSystem Paper.F6ILPFeasible
open Paper.AffineNat Paper.AffineILP Paper.AffineChain
open Paper.F6Cleared Paper.F6Objective Paper.F4ChargeIntervals
open Paper.F6SharedExact Paper.F6ILPSound Paper.PPEndToEnd

theorem feasible_to_actual_shared_cost {K : Nat}
    (labels : List Paper.AffineNat.Label) (x z : ℤ)
    (d c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat)
    (values : Variable labels → ℤ) (hz : 1 ≤ z)
    (hfeasible : Feasible labels x z c lo hi price N T values)
    (hdecor : ∀ label ∈ labels,
      label.d = d label.k ∧ label.c = c label.k)
    (hlo : ∀ key : Variable labels,
      minCharge (K := K) key.val (d key.val) (lo key.val) =
        (c key.val : WithTop Nat))
    (hhi : ∀ key : Variable labels,
      minCharge (K := K) key.val (d key.val) (hi key.val) =
        (c key.val : WithTop Nat)) :
    ∃ (w : Nat) (ts : List (Paper.F2CatalogTransfer.F2Source K)) (v : Nat),
      x = w ∧ ts.length = labels.length ∧
      Coupled.Formal.CostL (Paper.F6CostBridge.rawProblem price) ts w N v ∧
      Coupled.Formal.ArityInj Paper.F2CatalogTransfer.F2Source.arity ts ∧
      v ≤ T := by
  let a := liftNat (usedArities labels) values
  have hnat := feasible_sound_nat labels x z c lo hi price N T values hfeasible
  have hshared := feasible_shared_plateau (K := K)
    labels x z d c lo hi price N T values hfeasible hdecor hlo hhi
  have hactual := (Paper.AffineConverse.fixed_word_iff_constraints
    a d c labels 1 x (by decide) hshared).2
      ⟨z, hz, hnat.1, hnat.2.1⟩
  have hboth := terminal_cleared_positive 1 x
    (labels.map (Paper.AffineNat.instantiate a)) z (by decide)
      hz hnat.1 hnat.2.1
  obtain ⟨w, ts, v, hx, hlen, hcost, hselected, hinj, hval⟩ :=
    shared_actual_cost_exact a d c labels 1 x (by decide)
      hactual hboth.2 price N
  let D := terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a))
  have hD : 0 < D := terminalProduct_pos 1 _ (by decide)
  have hclear : D * affineSum a c N 1 x labels =
      clearedSum D a c N 1 x labels :=
    clear_affineSum a c N labels 1 x (by decide) hboth.1
  have hterminalNat : terminalNat 1 x a labels = z.toNat :=
    terminalNat_eq a labels 1 x z (by decide) hnat.1
  have hscaled : D * affineSum a c N 1 x labels ≤
      D * ((T : ℤ) - (leafPP price (finalN N labels) z.toNat : ℤ)) := by
    rw [hclear]
    exact hnat.2.2.1
  have haff := (Paper.AffineCost.cleared_budget_iff D _ _ hD).1 hscaled
  have hvi : (v : ℤ) ≤ T := by
    rw [hval, hterminalNat]
    omega
  exact ⟨w, ts, v, by simpa using hx, hlen, hcost, hinj,
    by exact_mod_cast hvi⟩

end Paper.F6SharedILP
/- END Sound.lean -/

/- BEGIN Reverse.lean source_sha256=ef03eb0ca5706932311668778188bf25cf97265406830c84bd902a349fecfa93 body_sha256=8e7fb738b46e9d4341079de1f188f6ee060dfbc0a69ec03ead5e95470c76c18b -/

namespace Paper.A2Feasible

open Coupled.Formal Paper.F2CatalogTransfer Paper.PPEndToEnd
open Paper.A2ActualForward Paper.AffineNat Paper.F6ILP
open Paper.F6ILPFeasible Paper.F6SharedILP
open Paper.ComputableProfileProvider

/-- Any feasible point in the independently defined exact-charge intervals
has budget at least the exhaustive raw optimum. An empty charge level has the
impossible interval [1,0], so feasibility itself certifies nonemptiness. -/
theorem candidate_feasible_lower_bound {K W T : Nat}
    (labels : List Label) (z : ℤ) (d c : Nat → Nat)
    (N : Nat)
    (values : Variable labels → ℤ)
    (hz : 1 ≤ z)
    (hdecor : ∀ label ∈ labels,
      label.d = d label.k ∧ label.c = c label.k)
    (hfeasible : Feasible labels (W : ℤ) z c
      (fun k => levelLo K W k (d k) (c k))
      (fun k => levelHi K W k (d k) (c k))
      tauRS N T values) :
    (optimize K W N).benchmarkCost tauRS N ≤ T := by
  have horder : ∀ key : Variable labels,
      levelLo K W key.val (d key.val) (c key.val) ≤
        levelHi K W key.val (d key.val) (c key.val) := by
    intro key
    have hb := hfeasible.2.2.2 key
    exact_mod_cast (hb.1.trans hb.2)
  have hlo : ∀ key : Variable labels,
      Paper.F4ChargeIntervals.minCharge (K := K) key.val
        (d key.val) (levelLo K W key.val (d key.val) (c key.val)) =
          (c key.val : WithTop Nat) := by
    intro key
    exact (level_endpoints_exact_of_order (horder key)).1
  have hhi : ∀ key : Variable labels,
      Paper.F4ChargeIntervals.minCharge (K := K) key.val
        (d key.val) (levelHi K W key.val (d key.val) (c key.val)) =
          (c key.val : WithTop Nat) := by
    intro key
    exact (level_endpoints_exact_of_order (horder key)).2
  obtain ⟨w,ts,v,hx,_,hcost,hinj,hv⟩ :=
    feasible_to_actual_shared_cost labels W z d c
      (fun k => levelLo K W k (d k) (c k))
      (fun k => levelHi K W k (d k) (c k))
      tauRS N T values hz hfeasible hdecor hlo hhi
  have hw : w = W := by exact_mod_cast hx.symm
  subst w
  have hraw : CostL (rawProblem tauRS) ts W N v := by
    change CostL (rawProblem tauRS) ts W N v at hcost
    exact hcost
  have hopt : (optimize K W N).benchmarkCost tauRS N ≤ v :=
    (optimize_all_raw K W N).2.2 ts v hinj hraw
  exact hopt.trans hv

end Paper.A2Feasible
/- END Reverse.lean -/
