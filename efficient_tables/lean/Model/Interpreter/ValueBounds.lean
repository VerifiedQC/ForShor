import Model.Interpreter.ValueTrace
import Model.Scanner.ArrayScanner

/-!
# Value bounds along an execution

Bounds the magnitudes of integer values reached during execution by the scanner capacities. Proves per-instruction bounds (`shiftL_bound`, `addScaled_bound`, `shiftR_bound`), that successful scalar steps preserve magnitude capacity (`valueStep_fits`), and the whole-trace statement `valueTrace_fits`.
-/

namespace Paper.ValueBounds

theorem shiftL_bound (a : Int) (w n : Nat)
    (h : a.natAbs < 2 ^ w) :
    (a * (2 : Int) ^ n).natAbs < 2 ^ (w + n) := by
  simpa [Int.natAbs_mul, pow_add, mul_comm] using
    Nat.mul_lt_mul_of_pos_right h (pow_pos (by decide : 0 < (2 : Nat)) n)

theorem negate_bound (a : Int) (w : Nat)
    (h : a.natAbs < 2 ^ w) :
    (-a).natAbs < 2 ^ (w + 1) := by
  have hp : 2 ^ w ≤ 2 ^ (w + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  simpa using lt_of_lt_of_le (by simpa using h) hp

theorem addScaled_bound (a b : Int) (wd ws n : Nat) (negSrc : Bool)
    (ha : a.natAbs < 2 ^ wd) (hb : b.natAbs < 2 ^ ws) :
    (a + (if negSrc then -1 else 1) * (2 : Int) ^ n * b).natAbs <
      2 ^ (1 + max wd (ws + n)) := by
  let M := max wd (ws + n)
  have hA : a.natAbs < 2 ^ M :=
    lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have hB : ((if negSrc then -1 else 1) * (2 : Int) ^ n * b).natAbs <
      2 ^ M := by
    have hs := shiftL_bound b ws n hb
    have he : ((if negSrc then -1 else 1) * (2 : Int) ^ n * b).natAbs =
        (b * (2 : Int) ^ n).natAbs := by
      cases negSrc <;> simp [mul_comm]
    rw [he]
    exact lt_of_lt_of_le hs
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  have ht := Int.natAbs_add_le a ((if negSrc then -1 else 1) * (2 : Int) ^ n * b)
  have hpow : 2 ^ (1 + M) = 2 ^ M + 2 ^ M := by
    simp [pow_add, pow_succ]; omega
  rw [hpow]
  omega

theorem shiftR_bound (a : Int) (w n : Nat)
    (h : a.natAbs < 2 ^ w)
    (hexact : a % (2 : Int) ^ n = 0) :
    (a / (2 : Int) ^ n).natAbs < 2 ^ (w - n) := by
  have hdiv : (2 : Int) ^ n ∣ a := Int.dvd_of_emod_eq_zero hexact
  have hm : a / (2 : Int) ^ n * (2 : Int) ^ n = a := Int.ediv_mul_cancel hdiv
  have hn : a.natAbs = (a / (2 : Int) ^ n).natAbs * 2 ^ n := by
    conv_lhs => rw [← hm]
    simp [Int.natAbs_mul]
  have hp : 0 < 2 ^ n := pow_pos (by decide : 0 < (2 : Nat)) n
  by_cases hnle : n ≤ w
  · have he : 2 ^ w = 2 ^ (w - n) * 2 ^ n := by
      rw [← pow_add]
      congr 1
      omega
    rw [hn, he] at h
    nlinarith
  · have hle : 2 ^ w ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    have hzero : (a / (2 : Int) ^ n).natAbs = 0 := by
      rw [hn] at h
      by_contra hne
      have hq : 1 ≤ (a / (2 : Int) ^ n).natAbs := by omega
      have hmle := Nat.mul_le_mul_right (2 ^ n) hq
      omega
    have hw : w - n = 0 := by omega
    simp [hw, hzero]

/-- Every successful scalar instruction preserves strict magnitude capacity.
The exact right-shift guard is part of success, including when `n > w i`. -/
theorem valueStep_fits {k : Nat} (op : Paper.FullDSL.Instruction k)
    (w : Paper.Scanner.Widths k) (v next : Paper.ValueSemantics.Values k)
    (hfits : Fits w v)
    (hstep : Paper.ValueSemantics.valueStep op v = some next) :
    Fits (Paper.Scanner.step (Paper.FullDSL.widthOp op) w) next := by
  cases op with
  | shiftL i n =>
      simp only [Paper.ValueSemantics.valueStep, Option.some.injEq] at hstep
      subst next
      intro j
      by_cases hij : j = i
      · subst j
        simpa [Paper.Scanner.step, Paper.FullDSL.widthOp] using shiftL_bound (v i) (w i) n (hfits i)
      · simpa [Paper.Scanner.step, Paper.FullDSL.widthOp, hij] using hfits j
  | shiftR i n =>
      by_cases hexact : v i % (2 : Int) ^ n = 0
      · simp only [Paper.ValueSemantics.valueStep, if_pos hexact, Option.some.injEq] at hstep
        subst next
        intro j
        by_cases hij : j = i
        · subst j
          simpa [Paper.Scanner.step, Paper.FullDSL.widthOp] using shiftR_bound (v i) (w i) n (hfits i) hexact
        · simpa [Paper.Scanner.step, Paper.FullDSL.widthOp, hij] using hfits j
      · simp [Paper.ValueSemantics.valueStep, hexact] at hstep
  | negate i =>
      simp only [Paper.ValueSemantics.valueStep, Option.some.injEq] at hstep
      subst next
      intro j
      by_cases hij : j = i
      · subst j
        simpa [Paper.Scanner.step, Paper.FullDSL.widthOp] using negate_bound (v i) (w i) (hfits i)
      · simpa [Paper.Scanner.step, Paper.FullDSL.widthOp, hij] using hfits j
  | addScaled dst src negSrc n =>
      by_cases hds : dst = src
      · simp [Paper.ValueSemantics.valueStep, hds] at hstep
      · simp only [Paper.ValueSemantics.valueStep, if_neg hds, Option.some.injEq] at hstep
        subst next
        intro j
        by_cases hj : j = dst
        · subst j
          simpa [Paper.Scanner.step, Paper.FullDSL.widthOp] using
            addScaled_bound (v dst) (v src) (w dst) (w src) n negSrc
              (hfits dst) (hfits src)
        · simpa [Paper.Scanner.step, Paper.FullDSL.widthOp, hj] using hfits j
  | phaseProduct i =>
      simp only [Paper.ValueSemantics.valueStep, Option.some.injEq] at hstep
      subst next
      simpa [Paper.Scanner.step, Paper.FullDSL.widthOp] using hfits

theorem width_le_maximum {k : Nat} (w : Paper.Scanner.Widths k) (i : Fin k) :
    w i ≤ Paper.Scanner.maximum w := by
  exact Finset.le_sup (Finset.mem_univ i)

theorem advance_width_le_peak {k : Nat} (op : Paper.Scanner.Op k)
    (s : Paper.Scanner.State k) (i : Fin k) :
    (Paper.Scanner.advance op s).widths i ≤ (Paper.Scanner.advance op s).peak := by
  exact le_trans (width_le_maximum (Paper.Scanner.step op s.widths) i)
    (le_max_right _ _)

theorem valueTrace_fits_aux {k : Nat}
    (word : List (Paper.FullDSL.Instruction k))
    (s : Paper.Scanner.State k)
    (v final : Paper.ValueSemantics.Values k) (marks : List Int)
    (hfits : Fits s.widths v)
    (hpeak : ∀ i, s.widths i ≤ s.peak)
    (htrace : Paper.ValueSemantics.valueTrace word v = some (final, marks)) :
    Fits (Paper.Scanner.scan (Paper.FullDSL.widthWord word) s).widths final ∧
      ∀ z ∈ marks,
        z.natAbs < 2 ^ (Paper.Scanner.scan (Paper.FullDSL.widthWord word) s).peak := by
  induction word generalizing s v final marks with
  | nil =>
      simp only [Paper.ValueSemantics.valueTrace, Option.some.injEq, Prod.mk.injEq] at htrace
      rcases htrace with ⟨rfl, rfl⟩
      simpa [Paper.FullDSL.widthWord, Paper.Scanner.scan] using
        (show Fits s.widths v ∧ ∀ z ∈ ([] : List Int),
          z.natAbs < 2 ^ s.peak from ⟨hfits, by simp⟩)
  | cons op rest ih =>
      cases op with
      | phaseProduct i =>
          cases ht : Paper.ValueSemantics.valueTrace rest v with
          | none => simp [Paper.ValueSemantics.valueTrace, ht] at htrace
          | some pair =>
              rcases pair with ⟨endv, tail⟩
              simp [Paper.ValueSemantics.valueTrace, ht] at htrace
              rcases htrace with ⟨rfl, rfl⟩
              let s' := Paper.Scanner.advance (.marker) s
              have hfit' : Fits s'.widths v := by
                simpa [s', Paper.Scanner.advance, Paper.Scanner.step] using hfits
              have hp' : ∀ j, s'.widths j ≤ s'.peak :=
                advance_width_le_peak (.marker) s
              obtain ⟨hf, hm⟩ := ih s' v endv tail hfit' hp' ht
              constructor
              · simpa [Paper.FullDSL.widthWord, Paper.FullDSL.widthOp,
                  Paper.Scanner.scan, s'] using hf
              · intro z hz
                simp only [List.mem_cons] at hz
                rcases hz with rfl | hz
                · have hle : s.peak ≤
                      (Paper.Scanner.scan (Paper.FullDSL.widthWord rest) s').peak :=
                    le_trans (le_max_left _ _)
                      (Paper.Scanner.incoming_peak_le_scan _ s')
                  have hi : s.widths i ≤
                      (Paper.Scanner.scan (Paper.FullDSL.widthWord rest) s').peak :=
                    le_trans (hpeak i) hle
                  have hpow : 2 ^ (s.widths i) ≤
                      2 ^ (Paper.Scanner.scan (Paper.FullDSL.widthWord rest) s').peak :=
                    Nat.pow_le_pow_right (by decide) hi
                  simpa [Paper.FullDSL.widthWord, Paper.FullDSL.widthOp,
                    Paper.Scanner.scan, s'] using lt_of_lt_of_le (hfits i) hpow
                · simpa [Paper.FullDSL.widthWord, Paper.FullDSL.widthOp,
                    Paper.Scanner.scan, s'] using hm z hz
      | shiftL i n =>
          cases hs : Paper.ValueSemantics.valueStep (.shiftL i n) v with
          | none => simp [Paper.ValueSemantics.valueTrace, hs] at htrace
          | some next =>
              have ht : Paper.ValueSemantics.valueTrace rest next = some (final, marks) := by
                simpa [Paper.ValueSemantics.valueTrace, hs] using htrace
              have hf := valueStep_fits (.shiftL i n) s.widths v next hfits hs
              have hp := advance_width_le_peak (Paper.FullDSL.widthOp (.shiftL i n)) s
              have hi := ih (Paper.Scanner.advance (Paper.FullDSL.widthOp (.shiftL i n)) s)
                next final marks (by simpa [Paper.Scanner.advance] using hf) hp ht
              simpa [Paper.FullDSL.widthWord, Paper.Scanner.scan] using hi
      | shiftR i n =>
          cases hs : Paper.ValueSemantics.valueStep (.shiftR i n) v with
          | none => simp [Paper.ValueSemantics.valueTrace, hs] at htrace
          | some next =>
              have ht : Paper.ValueSemantics.valueTrace rest next = some (final, marks) := by
                simpa [Paper.ValueSemantics.valueTrace, hs] using htrace
              have hf := valueStep_fits (.shiftR i n) s.widths v next hfits hs
              have hp := advance_width_le_peak (Paper.FullDSL.widthOp (.shiftR i n)) s
              have hi := ih (Paper.Scanner.advance (Paper.FullDSL.widthOp (.shiftR i n)) s)
                next final marks (by simpa [Paper.Scanner.advance] using hf) hp ht
              simpa [Paper.FullDSL.widthWord, Paper.Scanner.scan] using hi
      | negate i =>
          cases hs : Paper.ValueSemantics.valueStep (.negate i) v with
          | none => simp [Paper.ValueSemantics.valueTrace, hs] at htrace
          | some next =>
              have ht : Paper.ValueSemantics.valueTrace rest next = some (final, marks) := by
                simpa [Paper.ValueSemantics.valueTrace, hs] using htrace
              have hf := valueStep_fits (.negate i) s.widths v next hfits hs
              have hp := advance_width_le_peak (Paper.FullDSL.widthOp (.negate i)) s
              have hi := ih (Paper.Scanner.advance (Paper.FullDSL.widthOp (.negate i)) s)
                next final marks (by simpa [Paper.Scanner.advance] using hf) hp ht
              simpa [Paper.FullDSL.widthWord, Paper.Scanner.scan] using hi
      | addScaled d src negSrc n =>
          cases hs : Paper.ValueSemantics.valueStep (.addScaled d src negSrc n) v with
          | none => simp [Paper.ValueSemantics.valueTrace, hs] at htrace
          | some next =>
              have ht : Paper.ValueSemantics.valueTrace rest next = some (final, marks) := by
                simpa [Paper.ValueSemantics.valueTrace, hs] using htrace
              have hf := valueStep_fits (.addScaled d src negSrc n) s.widths v next hfits hs
              have hp := advance_width_le_peak
                (Paper.FullDSL.widthOp (.addScaled d src negSrc n)) s
              have hi := ih (Paper.Scanner.advance
                (Paper.FullDSL.widthOp (.addScaled d src negSrc n)) s)
                next final marks (by simpa [Paper.Scanner.advance] using hf) hp ht
              simpa [Paper.FullDSL.widthWord, Paper.Scanner.scan] using hi

/-- A successful integer trace fits every current scanner capacity and all
recorded marker values fit below its historical peak. -/
theorem valueTrace_fits {k : Nat}
    (word : List (Paper.FullDSL.Instruction k))
    (w : Paper.Scanner.Widths k)
    (v final : Paper.ValueSemantics.Values k) (marks : List Int)
    (hfits : Fits w v)
    (htrace : Paper.ValueSemantics.valueTrace word v = some (final, marks)) :
    Fits (Paper.Scanner.scan (Paper.FullDSL.widthWord word)
      (Paper.Scanner.fresh w)).widths final ∧
    ∀ z ∈ marks,
      z.natAbs < 2 ^ (Paper.Scanner.scan (Paper.FullDSL.widthWord word)
        (Paper.Scanner.fresh w)).peak := by
  apply valueTrace_fits_aux word (Paper.Scanner.fresh w) v final marks hfits
  · intro i
    exact width_le_maximum w i
  · exact htrace

theorem scan_width_le_peak {k : Nat} (word : List (Paper.Scanner.Op k))
    (s : Paper.Scanner.State k)
    (hpeak : ∀ i, s.widths i ≤ s.peak) :
    ∀ i, (Paper.Scanner.scan word s).widths i ≤
      (Paper.Scanner.scan word s).peak := by
  induction word generalizing s with
  | nil => simpa [Paper.Scanner.scan] using hpeak
  | cons op rest ih =>
      simpa [Paper.Scanner.scan] using
        ih (Paper.Scanner.advance op s) (advance_width_le_peak op s)

/-- The source's final signed width bounds every final register and every
observed marker value, provided the initial integer limbs fit the literal split.
This is an integer capacity statement, not a finite-register implementation. -/
theorem source_valueTrace_peak_bound {k : Nat} (width : Nat)
    (ops : TableGeneration.Prog k)
    (x final : Paper.ValueSemantics.Values k) (marks : List Int)
    (hinit : Fits (Paper.ArrayBridge.literalSourceSplit width k) x)
    (htrace : Paper.ValueSemantics.valueTrace
      (Paper.SourceBridge.mapToFull ops) x = some (final, marks)) :
    (∀ i, (final i).natAbs <
      2 ^ (TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops - 1)) ∧
    (∀ z ∈ marks, z.natAbs <
      2 ^ (TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops - 1)) := by
  let w := Paper.ArrayBridge.literalSourceSplit width k
  let word := Paper.SourceBridge.mapToFull ops
  let s := Paper.Scanner.scan (Paper.FullDSL.widthWord word) (Paper.Scanner.fresh w)
  have hb := valueTrace_fits word w x final marks hinit htrace
  have hp : ∀ i, s.widths i ≤ s.peak :=
    scan_width_le_peak (Paper.FullDSL.widthWord word) (Paper.Scanner.fresh w)
      (fun i => width_le_maximum w i)
  have hw : TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops - 1 =
      s.peak := by
    rw [Paper.ArrayBridge.nextBalancedSignedWidth_eq_full_widthWord]
    dsimp [s, word, w]
    omega
  constructor
  · intro i
    have hpow : 2 ^ (s.widths i) ≤ 2 ^ s.peak :=
      Nat.pow_le_pow_right (by decide) (hp i)
    rw [hw]
    exact lt_of_lt_of_le (hb.1 i) hpow
  · intro z hz
    rw [hw]
    exact hb.2 z hz

/-- A protected original source contract supplies the successful integer trace;
the independent initial-limb bound then gives signed-capacity bounds for its
ordered target observations and restored inputs. -/
theorem source_contract_peak_bound {k : Nat} (hk : k > 0)
    (width : Nat) (ops : TableGeneration.Prog k)
    (pts : List TableGeneration.Operations.Point)
    (x : Paper.ValueSemantics.Values k)
    (hcontract : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops pts)
    (hinit : Fits (Paper.ArrayBridge.literalSourceSplit width k) x) :
    (∀ i, (x i).natAbs <
      2 ^ (TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops - 1)) ∧
    (∀ p ∈ pts,
      (Paper.ValueSemantics.evalRow (TableGeneration.expectedRow p) x).natAbs <
        2 ^ (TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops - 1)) := by
  have ht := Paper.ValueSemantics.source_contract_valueTrace hk ops pts x hcontract
  have hb := source_valueTrace_peak_bound width ops x x
    (pts.map (fun p => Paper.ValueSemantics.evalRow (TableGeneration.expectedRow p) x))
    hinit ht
  refine ⟨hb.1, ?_⟩
  intro p hp
  exact hb.2 _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

end Paper.ValueBounds
