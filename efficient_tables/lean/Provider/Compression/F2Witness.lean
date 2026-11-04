import Provider.Compression.SourceBridge
import Provider.Compression.Padding

/-!
# Compressed F2 witnesses

Builds the compressed F2 source `compressedF2` and the padded version
`paddedCompressedF2 t A B` from a source table `t`. It proves the compressed
source is safe (`compressed_safe`), that its marker count, length and profile
charge are as computed (`f2_marker_count`, `compressedF2_length`,
`compressedF2_profileCharge`), and that the padded version has the exact
peaks `A`, `B` (`paddedCompressedF2_exactPeaks`).
-/

namespace Paper.CompressionF2

open Paper.FullDSL Paper.SourceBridge Paper.ShiftCompression
open Paper.WholeCompression Paper.CompressionSource
open Paper.F2CatalogTransfer Paper.PrefixPaddingStage

private theorem shift_opOK {k : Nat} (op : Instruction k)
    (hs : ShiftOnly op) : TableGeneration.Prog.OpOK (toOriginal op) := by
  cases op <;> simp_all [ShiftOnly, toOriginal, TableGeneration.Prog.OpOK]

private theorem compressAux_opOK {k : Nat}
    (block rest : List (Instruction k))
    (hall : ∀ op ∈ rest, TableGeneration.Prog.OpOK (toOriginal op)) :
    ∀ op ∈ compressAux block rest, TableGeneration.Prog.OpOK (toOriginal op) := by
  induction rest generalizing block with
  | nil =>
      intro op hop
      exact shift_opOK op (compressed_shift_only block op (by simpa [compressAux] using hop))
  | cons head tail ih =>
      have hhead : TableGeneration.Prog.OpOK (toOriginal head) :=
        hall head (by simp)
      have htail : ∀ op ∈ tail, TableGeneration.Prog.OpOK (toOriginal op) := by
        intro op hop
        exact hall op (by simp [hop])
      by_cases hs : isShift head = true
      · simpa [compressAux, hs] using ih (block ++ [head]) htail
      · intro op hop
        have hop' : op ∈ compressed block ++ head :: compressAux [] tail := by
          simpa [compressAux, hs] using hop
        rcases List.mem_append.mp hop' with hb | htail'
        · exact shift_opOK op (compressed_shift_only block op hb)
        · rcases List.mem_cons.mp htail' with rfl | ht
          · exact hhead
          · exact ih [] htail op ht

theorem compressed_safe {k : Nat} (ops : TableGeneration.Prog k)
    (hsafe : TableGeneration.safeProg? ops = true) :
    TableGeneration.safeProg? (mapToOriginal (sourceCompressed ops)) = true := by
  apply (safeProg_iff _).2
  intro op hop
  obtain ⟨full, hfull, rfl⟩ := List.mem_map.mp hop
  apply compressAux_opOK [] (mapToFull ops)
  · intro full h
    obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp h
    simpa [toOriginal_toFull] using (safeProg_iff ops).1 hsafe src hsrc
  · simpa [sourceCompressed, compressWhole] using hfull

def compressedF2 {K : Nat} (t : F2Source K) : F2Source K := by
  let ops := mapToOriginal (sourceCompressed t.source.program)
  have hsafe : TableGeneration.safeProg? ops = true :=
    compressed_safe t.source.program t.safe.safe_add
  have horig := (source_contract_iff_trace
    (TableGeneration.positive_of_ge_two t.source.hk)
    TableGeneration.State.start_state t.source.program (List.ofFn t.points)).1 t.safe
  have htrace : markerTrace (mapToFull ops) TableGeneration.State.start_state =
      some (TableGeneration.State.start_state,
        (List.ofFn t.points).map TableGeneration.expectedRow) := by
    rw [mapToFull_mapToOriginal]
    exact sourceCompressed_trace t.source.program _ _ _ horig.2
  have hcontract := (source_contract_iff_trace
    (TableGeneration.positive_of_ge_two t.source.hk)
    TableGeneration.State.start_state ops (List.ofFn t.points)).2 ⟨hsafe, htrace⟩
  exact ⟨{ t.source with program := ops }, t.cap, t.points, hcontract, t.literalF2⟩

private theorem original_success {K : Nat} (t : F2Source K) :
    TableGeneration.run? t.source.program TableGeneration.State.start_state =
      some TableGeneration.State.start_state := by
  have h := (source_contract_iff_trace
    (TableGeneration.positive_of_ge_two t.source.hk)
    TableGeneration.State.start_state t.source.program (List.ofFn t.points)).1 t.safe
  have hr : runRows (mapToFull t.source.program)
      TableGeneration.State.start_state = some TableGeneration.State.start_state := by
    rw [← markerTrace_fst]
    simp [h.2]
  simpa [runRows_eq_run_of_safe t.source.program _ h.1] using hr

private theorem marker_count_of_consumes {k : Nat} (hk : k > 0)
    (ops : TableGeneration.Prog k) (sigma : TableGeneration.State k)
    (pts : List TableGeneration.Operations.Point)
    (h : TableGeneration.progConsumesPts? hk sigma ops pts = true) :
    TableGeneration.phaseProductCount ops = pts.length := by
  induction ops generalizing sigma pts with
  | nil =>
      cases pts with
      | nil => rfl
      | cons p ps => simp [TableGeneration.progConsumesPts?] at h
  | cons op rest ih =>
      cases op with
      | phaseProduct i =>
          cases pts with
          | nil => simp [TableGeneration.progConsumesPts?] at h
          | cons p ps =>
              have htail : TableGeneration.progConsumesPts? hk sigma rest ps = true := by
                have hh : TableGeneration.matchesAt_pointRow_state hk sigma i p &&
                    TableGeneration.progConsumesPts? hk sigma rest ps = true := by
                  simpa [TableGeneration.progConsumesPts?] using h
                have hh' :
                    TableGeneration.matchesAt_pointRow_state hk sigma i p = true ∧
                    TableGeneration.progConsumesPts? hk sigma rest ps = true := by
                  simpa only [Bool.and_eq_true, decide_eq_true_eq] using hh
                exact hh'.2
              simpa [TableGeneration.phaseProductCount] using
                congrArg Nat.succ (ih sigma ps htail)
      | shiftL i n =>
          cases hs : TableGeneration.applyOp? sigma (.shiftL i n) with
          | none => simp [TableGeneration.progConsumesPts?, hs] at h
          | some next =>
              have htail : TableGeneration.progConsumesPts? hk next rest pts = true := by
                simpa [TableGeneration.progConsumesPts?, hs] using h
              simpa [TableGeneration.phaseProductCount] using ih next pts htail
      | shiftR i n =>
          cases hs : TableGeneration.applyOp? sigma (.shiftR i n) with
          | none => simp [TableGeneration.progConsumesPts?, hs] at h
          | some next =>
              have htail : TableGeneration.progConsumesPts? hk next rest pts = true := by
                simpa [TableGeneration.progConsumesPts?, hs] using h
              simpa [TableGeneration.phaseProductCount] using ih next pts htail
      | negate i =>
          cases hs : TableGeneration.applyOp? sigma (.negate i) with
          | none => simp [TableGeneration.progConsumesPts?, hs] at h
          | some next =>
              have htail : TableGeneration.progConsumesPts? hk next rest pts = true := by
                simpa [TableGeneration.progConsumesPts?, hs] using h
              simpa [TableGeneration.phaseProductCount] using ih next pts htail
      | addScaled d s b n =>
          cases hs : TableGeneration.applyOp? sigma (.addScaled d s b n) with
          | none => simp [TableGeneration.progConsumesPts?, hs] at h
          | some next =>
              have htail : TableGeneration.progConsumesPts? hk next rest pts = true := by
                simpa [TableGeneration.progConsumesPts?, hs] using h
              simpa [TableGeneration.phaseProductCount] using ih next pts htail

theorem f2_marker_count {K : Nat} (t : F2Source K) :
    TableGeneration.phaseProductCount t.source.program =
      2 * (t.source.k - 1) + 1 := by
  simpa using marker_count_of_consumes
    (TableGeneration.positive_of_ge_two t.source.hk)
    t.source.program TableGeneration.State.start_state
    (List.ofFn t.points) t.safe.consumes

theorem f2_marker_count_canonical {K : Nat} (t : F2Source K) :
    TableGeneration.phaseProductCount t.source.program = 2 * t.source.k - 1 := by
  have h := f2_marker_count t
  have hk := t.source.hk
  omega

private theorem source_charge_equiv {k : Nat} (ops : TableGeneration.Prog k) :
    wordCharge (mapToFull ops) = Paper.PPEndToEnd.chargedCount ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      have ih' : (rest.map (charge ∘ toFull)).sum =
          (rest.map Paper.PPEndToEnd.chargedOp).sum := by
        simpa [wordCharge, mapToFull, Paper.PPEndToEnd.chargedCount,
          List.map_map] using ih
      cases op <;> simp [wordCharge, mapToFull, toFull, charge,
        Paper.PPEndToEnd.chargedCount, Paper.PPEndToEnd.chargedOp,
        List.map_map, ih']

theorem f2_profile_charge {K : Nat} (t : F2Source K) :
    (sourceProfileRaw t).charge = t.charge := by
  simpa [sourceProfileRaw, sourceProfile, F2Source.charge] using
    source_charge_equiv t.source.program

theorem compressedF2_length {K : Nat} (t : F2Source K) :
    (compressedF2 t).source.program.length =
      (t.source.k + 1) *
        (Paper.ScannerPotential.totalPaid (mapToFull t.source.program) +
          TableGeneration.phaseProductCount t.source.program) + t.source.k := by
  simpa [compressedF2, mapToOriginal] using sourceCompressed_length t.source.program

theorem compressedF2_profileA {K : Nat} (t : F2Source K) :
    (sourceProfileRaw (compressedF2 t)).peakA ≤
      (sourceProfileRaw t).peakA := by
  have h := sourceCompressed_peakA
    (TableGeneration.finLast (TableGeneration.positive_of_ge_two t.source.hk))
    t.source.program _ t.safe.safe_add (original_success t)
  simpa [sourceProfileRaw, compressedF2, sourceProfile,
    mapToFull_mapToOriginal] using h

theorem compressedF2_profileB {K : Nat} (t : F2Source K) :
    (sourceProfileRaw (compressedF2 t)).peakB ≤
      (sourceProfileRaw t).peakB := by
  have h := sourceCompressed_peakB
    (TableGeneration.finLast (TableGeneration.positive_of_ge_two t.source.hk))
    t.source.program _ t.safe.safe_add (original_success t)
  simpa [sourceProfileRaw, compressedF2, sourceProfile,
    mapToFull_mapToOriginal] using h

theorem compressedF2_profileCharge {K : Nat} (t : F2Source K) :
    (sourceProfileRaw (compressedF2 t)).charge =
      (sourceProfileRaw t).charge := by
  simpa [sourceProfileRaw, compressedF2, sourceProfile,
    mapToFull_mapToOriginal] using sourceCompressed_charge t.source.program

def paddedCompressedF2 {K : Nat} (t : F2Source K) (A B : Nat) : F2Source K :=
  paddedF2Source (compressedF2 t) A B

theorem paddedCompressedF2_exactPeaks {K : Nat} (t : F2Source K) (A B : Nat)
    (hBA : B ≤ A) (hcanon : A ≤ B + (t.source.k - 1))
    (hA : (sourceProfileRaw t).peakA ≤ A)
    (hB : (sourceProfileRaw t).peakB ≤ B) :
    (sourceProfileRaw (paddedCompressedF2 t A B)).peakA = A ∧
    (sourceProfileRaw (paddedCompressedF2 t A B)).peakB = B := by
  exact paddedF2Source_exactPeaks (compressedF2 t) A B hBA
    (by simpa [compressedF2] using hcanon)
    (le_trans (compressedF2_profileA t) hA)
    (le_trans (compressedF2_profileB t) hB)

theorem paddedCompressedF2_length {K : Nat} (t : F2Source K) (A B : Nat) :
    (paddedCompressedF2 t A B).source.program.length =
      (t.source.k + 1) *
        (Paper.ScannerPotential.totalPaid (mapToFull t.source.program) +
          TableGeneration.phaseProductCount t.source.program) + t.source.k + 4 := by
  simp [paddedCompressedF2, paddedF2Source, paddingPrefix,
    compressedF2_length]

theorem paddedCompressedF2_lengthF2 {K : Nat} (t : F2Source K) (A B : Nat) :
    (paddedCompressedF2 t A B).source.program.length =
      (t.source.k + 1) *
        (Paper.ScannerPotential.totalPaid (mapToFull t.source.program) +
          (2 * t.source.k - 1)) + t.source.k + 4 := by
  simpa [f2_marker_count_canonical t] using paddedCompressedF2_length t A B

theorem paddedCompressedF2_profileCharge {K : Nat} (t : F2Source K) (A B : Nat) :
    (sourceProfileRaw (paddedCompressedF2 t A B)).charge =
      (sourceProfileRaw t).charge := by
  exact (paddedF2Source_charge (compressedF2 t) A B).trans
    (compressedF2_profileCharge t)

theorem paddedCompressedF2_charge {K : Nat} (t : F2Source K) (A B : Nat) :
    (paddedCompressedF2 t A B).charge = t.charge := by
  rw [← f2_profile_charge (paddedCompressedF2 t A B),
    paddedCompressedF2_profileCharge, f2_profile_charge]

end Paper.CompressionF2
