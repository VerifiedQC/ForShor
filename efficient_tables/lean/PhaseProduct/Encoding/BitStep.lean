import PhaseProduct.Encoding.SignedEncoding

/-!
# Bit-level step

Relates the finite-width bit step to the integer value step: encoding and
decoding round-trip (`decode_encode`), and `bitStep_refines_valueStep` and
`bitStep_eq_map_valueStep` show the two steps give the same success or failure
result. `bitStep_decode_commutes` states decoding commutes with the step.
-/

namespace Paper.BitStep

theorem decode_encode {k B : Nat} (hB : 0 < B)
    (v : Paper.ValueSemantics.Values k)
    (hv : ∀ i, (v i).natAbs < 2 ^ (B - 1)) :
    decode (encode (B := B) v) = v := by
  funext i
  have hsize : B - 1 + 1 = B := by omega
  have h := Paper.SignedEncoding.toInt_ofInt_of_natAbs_lt (B - 1) (v i) (hv i)
  simpa [decode, encode, hsize] using h

theorem shiftLeft_ofInt (B n : Nat) (a : Int) :
    BitVec.ofInt B a <<< n = BitVec.ofInt B (a * (2 : Int) ^ n) := by
  have hp : BitVec.twoPow B n = BitVec.ofInt B ((2 : Int) ^ n) := by
    calc
      BitVec.twoPow B n = BitVec.ofNat B (2 ^ n) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_twoPow]
      _ = BitVec.ofInt B ((2 : Int) ^ n) := by norm_cast
  rw [BitVec.shiftLeft_eq_mul_twoPow, hp, ← BitVec.ofInt_mul]

theorem shiftRight_ofInt_of_bound {B n : Nat} {a : Int}
    (hB : 0 < B) (ha : a.natAbs < 2 ^ (B - 1)) :
    (BitVec.ofInt B a).sshiftRight n =
      BitVec.ofInt B (a / (2 : Int) ^ n) := by
  have hdecode := decode_encode (k := 1) hB (fun _ => a) (fun _ => ha)
  have hvalue : (BitVec.ofInt B a).toInt = a := by
    have := congrArg (fun f : Fin 1 → Int => f 0) hdecode
    simpa [decode, encode] using this
  rw [BitVec.sshiftRight_eq, hvalue, Int.shiftRight_eq_div_pow]
  norm_cast

theorem encode_update {k B : Nat} (v : Paper.ValueSemantics.Values k)
    (i : Fin k) (a : Int) :
    Function.update (encode (B := B) v) i (BitVec.ofInt B a) =
      encode (B := B) (Function.update v i a) := by
  funext j
  by_cases h : j = i <;> simp [encode, Function.update, h]

theorem bitStep_refines_valueStep {k B : Nat} (hB : 0 < B)
    (op : Paper.FullDSL.Instruction k)
    (v v' : Paper.ValueSemantics.Values k)
    (hinit : ∀ i, (v i).natAbs < 2 ^ (B - 1))
    (hstep : Paper.ValueSemantics.valueStep op v = some v') :
    bitStep op (encode (B := B) v) =
      some (encode (B := B) v',
        (markerValues op v).map (BitVec.ofInt B)) := by
  cases op with
  | shiftL i n =>
      simp [Paper.ValueSemantics.valueStep] at hstep
      subst v'
      simp [bitStep, markerValues, encode_update, shiftLeft_ofInt, encode]
  | shiftR i n =>
      have hv : (BitVec.ofInt B (v i)).toInt = v i := by
        have h := decode_encode (B := B) hB v hinit
        have := congrArg (fun f : Fin k → Int => f i) h
        simpa [decode, encode] using this
      by_cases hdiv : v i % (2 : Int) ^ n = 0
      · simp [Paper.ValueSemantics.valueStep, hdiv] at hstep
        subst v'
        simp [bitStep, markerValues, hv, hdiv,
          shiftRight_ofInt_of_bound hB (hinit i), encode_update, encode]
      · simp [Paper.ValueSemantics.valueStep, hdiv] at hstep
  | negate i =>
      simp [Paper.ValueSemantics.valueStep] at hstep
      subst v'
      simp [bitStep, markerValues, encode]
      rw [← BitVec.ofInt_neg, encode_update]
  | addScaled dst src negSrc shift =>
      by_cases hneq : dst = src
      · simp [Paper.ValueSemantics.valueStep, hneq] at hstep
      · simp [Paper.ValueSemantics.valueStep, hneq] at hstep
        subst v'
        cases negSrc with
        | false =>
            simp [bitStep, markerValues, hneq, shiftLeft_ofInt, encode]
            rw [← BitVec.ofInt_add, encode_update]
            congr 1
            congr 1
            ring
        | true =>
            simp [bitStep, markerValues, hneq, encode]
            rw [← BitVec.ofInt_neg, shiftLeft_ofInt]
            have harith : (-v src) * (2 : Int) ^ shift =
                -(v src * (2 : Int) ^ shift) := by ring
            rw [harith, ← BitVec.ofInt_add, encode_update]
            congr 1
            congr 1
            ring
  | phaseProduct i =>
      simp [Paper.ValueSemantics.valueStep] at hstep
      subst v'
      simp [bitStep, encode, markerValues]

/-- The finite step and the integer step have the same success/failure result.
The successful register equality is modulo the fixed width; exact signed
decoding additionally needs a bound on the result. -/
theorem bitStep_eq_map_valueStep {k B : Nat} (hB : 0 < B)
    (op : Paper.FullDSL.Instruction k)
    (v : Paper.ValueSemantics.Values k)
    (hinit : ∀ i, (v i).natAbs < 2 ^ (B - 1)) :
    bitStep op (encode (B := B) v) =
      (Paper.ValueSemantics.valueStep op v).map
        (fun v' => (encode (B := B) v',
          (markerValues op v).map (BitVec.ofInt B))) := by
  cases hs : Paper.ValueSemantics.valueStep op v with
  | some v' =>
      simpa [hs] using bitStep_refines_valueStep hB op v v' hinit hs
  | none =>
      cases op with
      | shiftL i n => simp [Paper.ValueSemantics.valueStep] at hs
      | shiftR i n =>
          by_cases hdiv : v i % (2 : Int) ^ n = 0
          · simp [Paper.ValueSemantics.valueStep, hdiv] at hs
          · have hv : (BitVec.ofInt B (v i)).toInt = v i := by
              have h := decode_encode (B := B) hB v hinit
              have := congrArg (fun f : Fin k → Int => f i) h
              simpa [decode, encode] using this
            simp [bitStep, encode, hdiv, hv]
      | negate i => simp [Paper.ValueSemantics.valueStep] at hs
      | addScaled dst src negSrc shift =>
          by_cases hd : dst = src
          · simp [bitStep, hd]
          · simp [Paper.ValueSemantics.valueStep, hd] at hs
      | phaseProduct i => simp [Paper.ValueSemantics.valueStep] at hs

theorem bitStep_decode_commutes {k B : Nat} (hB : 0 < B)
    (op : Paper.FullDSL.Instruction k)
    (v v' : Paper.ValueSemantics.Values k)
    (hinit : ∀ i, (v i).natAbs < 2 ^ (B - 1))
    (hfinal : ∀ i, (v' i).natAbs < 2 ^ (B - 1))
    (hstep : Paper.ValueSemantics.valueStep op v = some v') :
    (bitStep op (encode (B := B) v)).map
      (fun r => (decode r.1, r.2.map BitVec.toInt)) =
      some (v', markerValues op v) := by
  rw [bitStep_refines_valueStep hB op v v' hinit hstep]
  have hm : (markerValues op v).map (fun a => (BitVec.ofInt B a).toInt) =
      markerValues op v := by
    cases op <;> simp [markerValues]
    case phaseProduct i =>
      have h := decode_encode (B := B) hB v hinit
      have := congrArg (fun f : Fin k → Int => f i) h
      simpa [decode, encode] using this
  simp only [Option.map_some, decode_encode hB v' hfinal,
    List.map_map, Function.comp_def]
  simpa using congrArg (fun xs : List Int => some (v', xs)) hm

end Paper.BitStep
