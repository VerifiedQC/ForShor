import PhaseProduct.Catalog.IntegerInputPhase
import PhaseProduct.Catalog.CatalogSemantics

/-!
# Semantics of verified PP tables

Native-execution facts for a `VerifiedPPCandidate`: its native trace
(`VerifiedPPCandidate.native_trace`), marker bounds and decoding
(`marker_bounds`, `native_markers_decode`), and the pair phase on deterministic
signed inputs (`VerifiedPPCandidate.native_pair_phase`). It also shows the
best-known catalogue supplies a verified candidate at every positive arity
(`bestKnown_verified_candidate_exists`).
-/

open scoped BigOperators

namespace Paper.PPEndToEnd

theorem VerifiedPPCandidate.calls_eq {K : Nat} (table : VerifiedPPCandidate K) :
    table.calls = 2 * table.arity - 1 := by
  unfold VerifiedPPCandidate.calls VerifiedPPCandidate.arity
  have hk := table.source.hk
  omega

theorem VerifiedPPCandidate.childWidth_eq_source {K : Nat}
    (table : VerifiedPPCandidate K) (W : Nat) :
    table.childWidth W =
      TableGeneration.RecursiveCost.nextBalancedSignedWidth W table.source.program := rfl

/-- The advertised marker payload is obtained by the actual native BitVec
interpreter, and the source program restores its entire register state. -/
theorem VerifiedPPCandidate.native_trace {K : Nat}
    (table : VerifiedPPCandidate K) (W : Nat)
    (x : Paper.ValueSemantics.Values table.source.k)
    (hfit : Paper.ValueBounds.Fits
      (Paper.ArrayBridge.literalSourceSplit W table.source.k) x) :
    let B := table.childWidth W
    Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull table.source.program)
      (Paper.BitStep.encode (B := B) x) =
      some (Paper.BitStep.encode (B := B) x,
        (Paper.PhaseIdentity.observations (List.ofFn table.points) x).map
          (BitVec.ofInt B)) := by
  dsimp [VerifiedPPCandidate.childWidth]
  simpa only [Paper.PhaseIdentity.observations] using
    Paper.BitStep.source_contract_bitTrace_encoded
      (TableGeneration.positive_of_ge_two table.source.hk)
      W table.source.program (List.ofFn table.points) x table.safe hfit

/-- Decoding each actual native marker recovers its unbounded integer value.
The strict bound uses the source scanner peak; `B` additionally includes its
sign bit. -/
theorem VerifiedPPCandidate.marker_bounds {K : Nat}
    (table : VerifiedPPCandidate K) (W : Nat)
    (x : Paper.ValueSemantics.Values table.source.k)
    (hfit : Paper.ValueBounds.Fits
      (Paper.ArrayBridge.literalSourceSplit W table.source.k) x) :
    let B := table.childWidth W
    ∀ m ∈ Paper.PhaseIdentity.observations (List.ofFn table.points) x,
      m.natAbs < 2 ^ (B - 1) := by
  dsimp [VerifiedPPCandidate.childWidth]
  have htrace : Paper.ValueSemantics.valueTrace
      (Paper.SourceBridge.mapToFull table.source.program) x =
      some (x, Paper.PhaseIdentity.observations (List.ofFn table.points) x) := by
    simpa only [Paper.PhaseIdentity.observations] using
      Paper.ValueSemantics.source_contract_valueTrace
        (TableGeneration.positive_of_ge_two table.source.hk)
        table.source.program (List.ofFn table.points) x table.safe
  have hb := Paper.ValueBounds.source_successful_prefix_signed_bound
    W table.source.program [] x x
    (Paper.PhaseIdentity.observations (List.ofFn table.points) x) hfit htrace
  simpa only [List.append_nil] using hb.2

theorem VerifiedPPCandidate.native_markers_decode {K : Nat}
    (table : VerifiedPPCandidate K) (W : Nat)
    (x : Paper.ValueSemantics.Values table.source.k)
    (hfit : Paper.ValueBounds.Fits
      (Paper.ArrayBridge.literalSourceSplit W table.source.k) x) :
    let B := table.childWidth W
    ((Paper.PhaseIdentity.observations (List.ofFn table.points) x).map
      (BitVec.ofInt B)).map BitVec.toInt =
        Paper.PhaseIdentity.observations (List.ofFn table.points) x := by
  dsimp
  have hb := table.marker_bounds W x hfit
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (Paper.PhaseIdentity.observations (List.ofFn table.points) x)]
  apply List.map_congr_left
  intro m hm
  have hB : 0 < table.childWidth W := by
    simp [VerifiedPPCandidate.childWidth,
      TableGeneration.RecursiveCost.nextBalancedSignedWidth]
  have hsub : table.childWidth W - 1 + 1 = table.childWidth W := by omega
  simpa [Function.comp_def, hsub] using
    Paper.SignedEncoding.toInt_ofInt_of_natAbs_lt
      (table.childWidth W - 1) m (hb m hm)

/-- Executing a verified source PP table natively on deterministic signed
limbs restores both register files and emits the prescribed ordered markers.
The interpolation phase equality is about those actual decoded markers. -/
theorem VerifiedPPCandidate.native_pair_phase {K : Nat}
    (table : VerifiedPPCandidate K) (W : Nat) (theta : ℝ)
    (a c : Int) (ha : a.natAbs < 2 ^ W) (hc : c.natAbs < 2 ^ W) :
    let hpos : 0 < table.source.k :=
      TableGeneration.positive_of_ge_two table.source.hk
    let B := table.childWidth W
    let x := Paper.SignedLimbs.limbs W hpos a
    let z := Paper.SignedLimbs.limbs W hpos c
    let mx := (Paper.PhaseIdentity.observations (List.ofFn table.points) x).map
      (BitVec.ofInt B)
    let mz := (Paper.PhaseIdentity.observations (List.ofFn table.points) z).map
      (BitVec.ofInt B)
    Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull table.source.program)
      (Paper.BitStep.encode (B := B) x) =
        some (Paper.BitStep.encode (B := B) x, mx) ∧
    Paper.BitStep.bitTrace (Paper.SourceBridge.mapToFull table.source.program)
      (Paper.BitStep.encode (B := B) z) =
        some (Paper.BitStep.encode (B := B) z, mz) ∧
    mx.length = table.calls ∧ mz.length = table.calls ∧
    (∀ m ∈ mx.map BitVec.toInt, m.natAbs < 2 ^ (B - 1)) ∧
    (∀ m ∈ mz.map BitVec.toInt, m.natAbs < 2 ^ (B - 1)) ∧
    (∏ l : Fin table.calls, Paper.ValuePhase.phaseCharacter theta
      (table.weights W l *
        ((mx.map BitVec.toInt).getD l.val 0 : ℚ) *
        ((mz.map BitVec.toInt).getD l.val 0 : ℚ))) =
      Paper.ValuePhase.phaseCharacter theta ((a : ℚ) * (c : ℚ)) := by
  dsimp only
  let hpos : 0 < table.source.k :=
    TableGeneration.positive_of_ge_two table.source.hk
  let x := Paper.SignedLimbs.limbs W hpos a
  let z := Paper.SignedLimbs.limbs W hpos c
  have hfx : Paper.ValueBounds.Fits
      (Paper.ArrayBridge.literalSourceSplit W table.source.k) x :=
    Paper.SignedLimbs.limbs_fits W hpos a ha
  have hfz : Paper.ValueBounds.Fits
      (Paper.ArrayBridge.literalSourceSplit W table.source.k) z :=
    Paper.SignedLimbs.limbs_fits W hpos c hc
  have hx := table.native_trace W x hfx
  have hz := table.native_trace W z hfz
  have hdx := table.native_markers_decode W x hfx
  have hdz := table.native_markers_decode W z hfz
  have hbx := table.marker_bounds W x hfx
  have hbz := table.marker_bounds W z hfz
  dsimp only at hx hz hdx hdz hbx hbz
  obtain ⟨xs, zs, hvx, hvz, hxl, hzl, hphase⟩ :=
    Paper.ValuePhase.source_pair_phase_product hpos table.source.program
      table.points (table.weights W)
      (fun j : Fin table.source.k =>
        (Paper.SignedLimbs.radix W table.source.k : ℚ) ^ j.val)
      table.safe (table.certificate W) theta x z
  have hcanonicalx : Paper.ValueSemantics.valueTrace
      (Paper.SourceBridge.mapToFull table.source.program) x =
      some (x, Paper.PhaseIdentity.observations (List.ofFn table.points) x) := by
    simpa only [Paper.PhaseIdentity.observations] using
      Paper.ValueSemantics.source_contract_valueTrace hpos
        table.source.program (List.ofFn table.points) x table.safe
  have hcanonicalz : Paper.ValueSemantics.valueTrace
      (Paper.SourceBridge.mapToFull table.source.program) z =
      some (z, Paper.PhaseIdentity.observations (List.ofFn table.points) z) := by
    simpa only [Paper.PhaseIdentity.observations] using
      Paper.ValueSemantics.source_contract_valueTrace hpos
        table.source.program (List.ofFn table.points) z table.safe
  have heqx : xs = Paper.PhaseIdentity.observations (List.ofFn table.points) x :=
    congrArg Prod.snd (Option.some.inj (hvx.symm.trans hcanonicalx))
  have heqz : zs = Paper.PhaseIdentity.observations (List.ofFn table.points) z :=
    congrArg Prod.snd (Option.some.inj (hvz.symm.trans hcanonicalz))
  subst xs
  subst zs
  have hcountx : (Paper.PhaseIdentity.observations (List.ofFn table.points) x).length =
      table.calls := Paper.GenericPhase.indexed_observations_length table.points x
  have hcountz : (Paper.PhaseIdentity.observations (List.ofFn table.points) z).length =
      table.calls := Paper.GenericPhase.indexed_observations_length table.points z
  have hphase' :
      (∏ l : Fin table.calls, Paper.ValuePhase.phaseCharacter theta
        (table.weights W l *
          ((Paper.PhaseIdentity.observations (List.ofFn table.points) x).getD l.val 0 : ℚ) *
          ((Paper.PhaseIdentity.observations (List.ofFn table.points) z).getD l.val 0 : ℚ))) =
        Paper.ValuePhase.phaseCharacter theta ((a : ℚ) * (c : ℚ)) := by
    have hevalx :
        (∑ j : Fin table.source.k,
          (Paper.SignedLimbs.radix W table.source.k : ℚ) ^ j.val * (x j : ℚ)) =
            (a : ℚ) := by
      simpa only [x] using Paper.IntegerInputPhase.evaluate_limbs W hpos a
    have hevalz :
        (∑ j : Fin table.source.k,
          (Paper.SignedLimbs.radix W table.source.k : ℚ) ^ j.val * (z j : ℚ)) =
            (c : ℚ) := by
      simpa only [z] using Paper.IntegerInputPhase.evaluate_limbs W hpos c
    simpa only [Paper.PhaseIdentity.linearForm, hevalx, hevalz] using hphase
  refine ⟨hx, hz, by simpa using hcountx, by simpa using hcountz,
    ?_, ?_, ?_⟩
  · change ∀ m ∈ ((Paper.PhaseIdentity.observations
        (List.ofFn table.points) x).map
        (BitVec.ofInt (table.childWidth W))).map BitVec.toInt,
        m.natAbs < 2 ^ (table.childWidth W - 1)
    rw [hdx]
    exact hbx
  · change ∀ m ∈ ((Paper.PhaseIdentity.observations
        (List.ofFn table.points) z).map
        (BitVec.ofInt (table.childWidth W))).map BitVec.toInt,
        m.natAbs < 2 ^ (table.childWidth W - 1)
    rw [hdz]
    exact hbz
  · change (∏ l : Fin table.calls, Paper.ValuePhase.phaseCharacter theta
        (table.weights W l *
          ((((Paper.PhaseIdentity.observations (List.ofFn table.points) x).map
            (BitVec.ofInt (table.childWidth W))).map BitVec.toInt).getD l.val 0 : ℚ) *
          ((((Paper.PhaseIdentity.observations (List.ofFn table.points) z).map
            (BitVec.ofInt (table.childWidth W))).map BitVec.toInt).getD l.val 0 : ℚ))) =
          Paper.ValuePhase.phaseCharacter theta ((a : ℚ) * (c : ℚ))
    rw [hdx, hdz]
    exact hphase'

/-- BestKnown supplies a verified PP source table for every positive arity,
not just the currently promoted finite list through sixteen. Its weight
family is selected from proved interpolation certificates, and the same
source program is used at every width. -/
theorem bestKnown_verified_candidate_exists (K k : Nat)
    (hk : 2 ≤ k) (hcap : k ≤ K) :
    ∃ table : VerifiedPPCandidate K, table.arity = k := by
  let ordered := TableGeneration.bestKnownGeneratePointsInOrder
    .PhaseProduct k hk
  have hvalid := Paper.BestKnownContract.bestKnownOrderedPoints_valid
    .PhaseProduct k hk
  have hlen : ordered.length = 2 * (k - 1) + 1 := by
    have h := hvalid.1
    simp only [TableGeneration.ProductMode.pointCount] at h
    dsimp [ordered]
    omega
  let pts : Fin (2 * (k - 1) + 1) → TableGeneration.Operations.Point :=
    fun i => ordered.get (i.cast hlen.symm)
  have hpts : List.ofFn pts = ordered :=
    Paper.ListPhase.ofFn_cast_get ordered hlen
  have hv : TableGeneration.ValidPointList .PhaseProduct k (List.ofFn pts) := by
    rw [hpts]
    exact hvalid
  have hi : TableGeneration.Operations.Point.frac 0 ∈ List.ofFn pts := by
    rw [hpts]
    exact Paper.BestKnownPhase.bestKnownOrderedPoints_has_infinity
      .PhaseProduct k hk
  obtain ⟨v, order, hvnode, hf, hinode⟩ :=
    Paper.PointNodes.exists_enumeration_of_validPointList .PhaseProduct k pts hv hi
  let weights : (W : Nat) → Fin (2 * (k - 1) + 1) → ℚ :=
    fun W => Paper.GeneralConstruction.phaseWeights k 2 pts v
      (Paper.SignedLimbs.radix W k : ℚ) order
  have hcert (W : Nat) :
      Paper.PhaseIdentity.PairCertificate (weights W)
        (Paper.GenericPhase.indexedSourceRows (k := k) pts)
        (fun j : Fin k => (Paper.SignedLimbs.radix W k : ℚ) ^ j.val) := by
    exact Paper.GeneralConstruction.pair_normalized_certificate
      (by omega) pts v order hvnode hf hinode
      (Paper.SignedLimbs.radix W k : ℚ)
  have hsafe : TableGeneration.ProgConsumesPtsSafe
      (TableGeneration.positive_of_ge_two hk)
      TableGeneration.State.start_state
      (TableGeneration.bestKnownGenerate .PhaseProduct k hk)
      (List.ofFn pts) := by
    rw [hpts]
    exact (Paper.BestKnownContract.bestKnownGenerate_safe .PhaseProduct k hk).2
  refine ⟨{
    source := TableGeneration.RecursiveCost.bestKnownCandidate k hk
    cap := hcap
    points := pts
    safe := hsafe
    weights := weights
    certificate := hcert
  }, rfl⟩

end Paper.PPEndToEnd
