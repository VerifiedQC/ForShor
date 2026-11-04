import PhaseProduct.Encoding.BitStep
import Model.Interpreter.ValueBoundsPrefixes

/-!
# Bit-level traces

Extends the bit step to whole words: the bit trace is the encoded value trace
(`bitTrace_eq_map_valueTrace`, `bitTrace_eq_map_valueTrace_at_peak`). At the
source scanner width this gives `source_bitTrace_eq_map_valueTrace` and decoding
results (`source_bitTrace_decode_eq_valueTrace`), with consequences for an
accepted source contract (`source_contract_bitTrace_encoded`,
`source_contract_bitTrace_decoded`).
-/

namespace Paper.BitStep

open Paper.ValueSemantics

theorem valueTrace_cons {k : Nat} (op : Paper.FullDSL.Instruction k)
    (rest : List (Paper.FullDSL.Instruction k)) (v : Values k) :
    valueTrace (op :: rest) v =
      (valueStep op v).bind (fun v' =>
        (valueTrace rest v').map (fun r => (r.1, markerValues op v ++ r.2))) := by
  cases op <;> simp [valueTrace, valueStep, markerValues]

theorem bitTrace_eq_map_valueTrace {k B : Nat} (hB : 0 < B)
    (ops : List (Paper.FullDSL.Instruction k)) (v : Values k)
    (hprefix : ∀ pre suffix mid marks,
      ops = pre ++ suffix → valueTrace pre v = some (mid, marks) →
      ∀ i, (mid i).natAbs < 2 ^ (B - 1)) :
    bitTrace ops (encode (B := B) v) =
      (valueTrace ops v).map
        (fun r => (encode (B := B) r.1, r.2.map (BitVec.ofInt B))) := by
  induction ops generalizing v with
  | nil => simp [bitTrace, valueTrace]
  | cons op rest ih =>
      have hinit : ∀ i, (v i).natAbs < 2 ^ (B - 1) := by
        exact hprefix [] (op :: rest) v [] rfl (by simp [valueTrace])
      rw [bitTrace, bitStep_eq_map_valueStep hB op v hinit,
        valueTrace_cons]
      cases hs : valueStep op v with
      | none => simp [hs]
      | some v' =>
          have htail : ∀ pre suffix mid marks,
              rest = pre ++ suffix → valueTrace pre v' = some (mid, marks) →
              ∀ i, (mid i).natAbs < 2 ^ (B - 1) := by
            intro pre suffix mid marks he hp
            apply hprefix (op :: pre) suffix mid
              (markerValues op v ++ marks)
            · simp [he]
            · simp [valueTrace_cons, hs, hp]
          simp only [hs, Option.map_some, Option.bind_some]
          rw [ih v' htail]
          cases ht : valueTrace rest v' with
          | none => simp [ht]
          | some tail =>
              rcases tail with ⟨vf, marks⟩
              simp [ht, List.map_append]

/-- The whole-word scanner peak supplies the successful-prefix bounds needed
for exact fixed-width execution, including an eventual failing step. -/
theorem bitTrace_eq_map_valueTrace_at_peak {k : Nat}
    (ops : List (Paper.FullDSL.Instruction k))
    (w : Paper.Scanner.Widths k) (v : Values k)
    (hinit : Paper.ValueBounds.Fits w v) :
    let B := (Paper.Scanner.scan (Paper.FullDSL.widthWord ops)
      (Paper.Scanner.fresh w)).peak + 1
    bitTrace ops (encode (B := B) v) =
      (valueTrace ops v).map
        (fun r => (encode (B := B) r.1, r.2.map (BitVec.ofInt B))) := by
  dsimp
  apply bitTrace_eq_map_valueTrace (by omega)
  intro pre suffix mid marks he hp i
  have hb := (Paper.ValueBounds.successful_prefix_below_full_peak
    pre suffix w v mid marks hinit hp).1 i
  rw [← he] at hb
  simpa using hb

/-- At the original array scanner's signed width, native fixed-width
execution has exactly the integer interpreter's success or failure result. -/
theorem source_bitTrace_eq_map_valueTrace {k : Nat}
    (width : Nat) (ops : TableGeneration.Prog k) (v : Values k)
    (hinit : Paper.ValueBounds.Fits
      (Paper.ArrayBridge.literalSourceSplit width k) v) :
    let B := TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops
    bitTrace (Paper.SourceBridge.mapToFull ops) (encode (B := B) v) =
      (valueTrace (Paper.SourceBridge.mapToFull ops) v).map
        (fun r => (encode (B := B) r.1, r.2.map (BitVec.ofInt B))) := by
  dsimp
  rw [Paper.ArrayBridge.nextBalancedSignedWidth_eq_full_widthWord]
  rw [Nat.add_comm 1]
  exact bitTrace_eq_map_valueTrace_at_peak
    (Paper.SourceBridge.mapToFull ops)
    (Paper.ArrayBridge.literalSourceSplit width k) v hinit

/-- On success the scanner bound also makes every decoded native marker and
register exact; on failure both options remain none. -/
theorem bitTrace_decode_eq_valueTrace_at_peak {k : Nat}
    (ops : List (Paper.FullDSL.Instruction k))
    (w : Paper.Scanner.Widths k) (v : Values k)
    (hinit : Paper.ValueBounds.Fits w v) :
    let B := (Paper.Scanner.scan (Paper.FullDSL.widthWord ops)
      (Paper.Scanner.fresh w)).peak + 1
    (bitTrace ops (encode (B := B) v)).map
      (fun r => (decode r.1, r.2.map BitVec.toInt)) = valueTrace ops v := by
  dsimp
  rw [bitTrace_eq_map_valueTrace_at_peak ops w v hinit]
  cases ht : valueTrace ops v with
  | none => simp [ht]
  | some r =>
      rcases r with ⟨vf, marks⟩
      have hb := Paper.ValueBounds.successful_prefix_below_full_peak
        ops [] w v vf marks hinit ht
      have hreg : decode (encode (B :=
          (Paper.Scanner.scan (Paper.FullDSL.widthWord ops)
            (Paper.Scanner.fresh w)).peak + 1) vf) = vf := by
        apply decode_encode (by omega)
        simpa using hb.1
      have hmarks : (marks.map (BitVec.ofInt
          ((Paper.Scanner.scan (Paper.FullDSL.widthWord ops)
            (Paper.Scanner.fresh w)).peak + 1))).map BitVec.toInt = marks := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id marks]
        apply List.map_congr_left
        intro z hz
        exact Paper.SignedEncoding.toInt_ofInt_of_natAbs_lt _ z
          (by simpa using hb.2 z hz)
      simp [ht, hreg, hmarks]

theorem source_bitTrace_decode_eq_valueTrace {k : Nat}
    (width : Nat) (ops : TableGeneration.Prog k) (v : Values k)
    (hinit : Paper.ValueBounds.Fits
      (Paper.ArrayBridge.literalSourceSplit width k) v) :
    let B := TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops
    (bitTrace (Paper.SourceBridge.mapToFull ops) (encode (B := B) v)).map
      (fun r => (decode r.1, r.2.map BitVec.toInt)) =
        valueTrace (Paper.SourceBridge.mapToFull ops) v := by
  dsimp
  rw [Paper.ArrayBridge.nextBalancedSignedWidth_eq_full_widthWord]
  rw [Nat.add_comm 1]
  exact bitTrace_decode_eq_valueTrace_at_peak
    (Paper.SourceBridge.mapToFull ops)
    (Paper.ArrayBridge.literalSourceSplit width k) v hinit

/-- An accepted source point-consumption contract executes natively at the
original scanner width, restores the input, and emits encoded advertised
point values. The input limb bound remains explicit. -/
theorem source_contract_bitTrace_encoded {k : Nat} (hk : k > 0)
    (width : Nat) (ops : TableGeneration.Prog k)
    (pts : List TableGeneration.Operations.Point) (x : Values k)
    (hcontract : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops pts)
    (hinit : Paper.ValueBounds.Fits
      (Paper.ArrayBridge.literalSourceSplit width k) x) :
    let B := TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops
    bitTrace (Paper.SourceBridge.mapToFull ops) (encode (B := B) x) =
      some (encode (B := B) x,
        (pts.map (fun p => evalRow (TableGeneration.expectedRow p) x)).map
          (BitVec.ofInt B)) := by
  dsimp
  rw [source_bitTrace_eq_map_valueTrace width ops x hinit,
    Paper.ValueSemantics.source_contract_valueTrace hk ops pts x hcontract]
  rfl

/-- Decoding the actual native execution gives exactly the restored input
and the specified integer marker values for every accepted source contract. -/
theorem source_contract_bitTrace_decoded {k : Nat} (hk : k > 0)
    (width : Nat) (ops : TableGeneration.Prog k)
    (pts : List TableGeneration.Operations.Point) (x : Values k)
    (hcontract : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops pts)
    (hinit : Paper.ValueBounds.Fits
      (Paper.ArrayBridge.literalSourceSplit width k) x) :
    let B := TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops
    (bitTrace (Paper.SourceBridge.mapToFull ops) (encode (B := B) x)).map
      (fun r => (decode r.1, r.2.map BitVec.toInt)) =
        some (x, pts.map (fun p => evalRow (TableGeneration.expectedRow p) x)) := by
  dsimp
  rw [source_bitTrace_decode_eq_valueTrace width ops x hinit]
  exact Paper.ValueSemantics.source_contract_valueTrace hk ops pts x hcontract

end Paper.BitStep
