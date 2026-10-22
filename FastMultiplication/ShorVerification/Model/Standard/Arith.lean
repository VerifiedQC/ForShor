import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics

/-!
# Word-level arithmetic for the model

Risk 4 of the original construction plan says to prove the word-level statements over plain `ℕ`
and `ℤ` *first*, before touching registers. This file is that layer: the
two's-complement round trips used by `Negate`, `AddScaled`, `ShiftL` and
`ShiftR`, and the two facts about the reversible shift completions
`signedShiftLWord` / `signedShiftRWord` that make them mutually inverse.

Nothing here mentions `RegEncoding` or any state: every statement is about `ℕ`
and `ℤ`. It imports `Framework/Semantics/GateSemantics` only for the definitions
`tcDecodeWidth`, `tcModWidth`, `FitsSignedWidth`, `signedShiftLWord` and
`signedShiftRWord` that it is about.
-/

namespace Shor
namespace Model

/-! ## Two's complement -/

theorem two_pow_pos (w : ℕ) : (0 : ℤ) < 2 ^ w := by positivity

@[simp] theorem tcModWidth_cast (w : ℕ) (z : ℤ) :
    ((tcModWidth w z : ℕ) : ℤ) = z % 2 ^ w := by
  have h : (0 : ℤ) < ((2 ^ w : ℕ) : ℤ) := by positivity
  rw [tcModWidth, Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt h))]
  push_cast
  rfl

theorem tcModWidth_lt (w : ℕ) (z : ℤ) : tcModWidth w z < 2 ^ w := by
  have h : (0 : ℤ) < 2 ^ w := two_pow_pos w
  have := Int.emod_lt_of_pos z h
  have hcast : ((tcModWidth w z : ℕ) : ℤ) = z % 2 ^ w := tcModWidth_cast w z
  have : ((tcModWidth w z : ℕ) : ℤ) < ((2 ^ w : ℕ) : ℤ) := by
    rw [hcast]; push_cast; exact Int.emod_lt_of_pos z h
  exact_mod_cast this

theorem tcModWidth_congr {w : ℕ} {z₁ z₂ : ℤ} (h : z₁ % 2 ^ w = z₂ % 2 ^ w) :
    tcModWidth w z₁ = tcModWidth w z₂ := by
  have := tcModWidth_cast w z₁
  have h2 := tcModWidth_cast w z₂
  omega

theorem tcModWidth_of_lt {w v : ℕ} (h : v < 2 ^ w) : tcModWidth w (v : ℤ) = v := by
  have hcast := tcModWidth_cast w (v : ℤ)
  have : ((v : ℤ)) % 2 ^ w = (v : ℤ) := by
    refine Int.emod_eq_of_lt (by positivity) ?_
    exact_mod_cast h
  omega

/-- The two's-complement decoding of a `w`-bit word is congruent to it mod `2^w`. -/
theorem tcDecodeWidth_emod (w u : ℕ) :
    (tcDecodeWidth w u) % 2 ^ w = (u : ℤ) % 2 ^ w := by
  cases w with
  | zero => simp [tcDecodeWidth]
  | succ w' =>
      rw [tcDecodeWidth]
      split
      · rfl
      · rw [Int.sub_emod]
        push_cast
        simp

theorem tcModWidth_tcDecodeWidth {w u : ℕ} (hu : u < 2 ^ w) :
    tcModWidth w (tcDecodeWidth w u) = u := by
  rw [tcModWidth_congr (tcDecodeWidth_emod w u)]
  exact tcModWidth_of_lt hu

/-- Two's-complement decoding, as an explicit case split. -/
theorem tcDecodeWidth_eq {w : ℕ} (hw : 0 < w) (u : ℕ) :
    tcDecodeWidth w u = if u < 2 ^ (w - 1) then (u : ℤ) else (u : ℤ) - 2 ^ w := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  rw [tcDecodeWidth]
  simp only [Nat.add_sub_cancel]
  split
  · rfl
  · push_cast; ring

theorem two_pow_split_nat {w : ℕ} (hw : 0 < w) : (2:ℕ) ^ w = 2 * 2 ^ (w - 1) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  simp [pow_succ, Nat.mul_comm]

theorem two_pow_split_int {w : ℕ} (hw : 0 < w) : (2:ℤ) ^ w = 2 * 2 ^ (w - 1) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  simp [pow_succ, mul_comm]

theorem natCast_two_pow (w : ℕ) : ((2 ^ w : ℕ) : ℤ) = (2:ℤ) ^ w := by push_cast; ring

/-- `(a : ℕ) ≤ b` transported to `ℤ` with `2 ^ _` kept as an `ℤ`-power. -/
theorem int_le_of_nat_le_pow {m u : ℕ} (h : 2 ^ m ≤ u) : ((2:ℤ)) ^ m ≤ (u : ℤ) := by
  have h' : ((2 ^ m : ℕ) : ℤ) ≤ (u : ℤ) := Int.ofNat_le.mpr h
  rwa [natCast_two_pow] at h'

theorem int_lt_of_nat_lt_pow {m u : ℕ} (h : u < 2 ^ m) : (u : ℤ) < ((2:ℤ)) ^ m := by
  have h' : (u : ℤ) < ((2 ^ m : ℕ) : ℤ) := Int.ofNat_lt.mpr h
  rwa [natCast_two_pow] at h'

theorem tcDecodeWidth_nonneg_iff {w u : ℕ} (hw : 0 < w) (hu : u < 2 ^ w) :
    0 ≤ tcDecodeWidth w u ↔ u < 2 ^ (w - 1) := by
  have hp : (0:ℤ) < 2 ^ (w - 1) := two_pow_pos _
  have hsplit : (2:ℤ) ^ w = 2 * 2 ^ (w - 1) := two_pow_split_int hw
  have hu' : (u : ℤ) < (2:ℤ) ^ w := int_lt_of_nat_lt_pow hu
  rw [tcDecodeWidth_eq hw]
  by_cases h : u < 2 ^ (w - 1)
  · have hnn : (0:ℤ) ≤ (u:ℤ) := Int.natCast_nonneg u
    simp [h, hnn]
  · push_neg at h
    have hge : ((2:ℤ)) ^ (w - 1) ≤ (u : ℤ) := int_le_of_nat_le_pow h
    simp only [if_neg (not_lt.mpr h)]
    constructor
    · intro hle; exfalso; linarith
    · intro hlt; exfalso; omega

/-- `tcDecodeWidth` lands in the signed range. -/
theorem tcDecodeWidth_bounds {w u : ℕ} (hw : 0 < w) (hu : u < 2 ^ w) :
    -(2:ℤ) ^ (w - 1) ≤ tcDecodeWidth w u ∧ tcDecodeWidth w u < 2 ^ (w - 1) := by
  have hsplit : (2:ℤ) ^ w = 2 * 2 ^ (w - 1) := two_pow_split_int hw
  have hp : (0:ℤ) < 2 ^ (w - 1) := two_pow_pos _
  have hnn : (0:ℤ) ≤ (u:ℤ) := Int.natCast_nonneg u
  have hu' : (u : ℤ) < (2:ℤ) ^ w := int_lt_of_nat_lt_pow hu
  rw [tcDecodeWidth_eq hw]
  by_cases h : u < 2 ^ (w - 1)
  · have hlt : (u : ℤ) < (2:ℤ) ^ (w - 1) := int_lt_of_nat_lt_pow h
    simp only [if_pos h]
    constructor <;> linarith
  · push_neg at h
    have hge : ((2:ℤ)) ^ (w - 1) ≤ (u : ℤ) := int_le_of_nat_le_pow h
    simp only [if_neg (not_lt.mpr h)]
    constructor <;> linarith

theorem fitsSignedWidth_tcDecodeWidth {w u : ℕ} (hw : 0 < w) (hu : u < 2 ^ w) :
    FitsSignedWidth w (tcDecodeWidth w u) := by
  obtain ⟨h1, h2⟩ := tcDecodeWidth_bounds hw hu
  refine ⟨hw, ?_, ?_⟩
  · rw [signedMin]; push_cast; linarith
  · rw [signedMax]; push_cast; linarith

/-! ## Bit surgery on `ℕ`

Three facts about reading a bit out of `a + 2 ^ n * c`, all proved from
`Nat.testBit_eq_decide_div_mod_eq`.
-/

theorem two_pow_pos' (n : ℕ) : 0 < (2:ℕ) ^ n := by positivity

theorem testBit_add_mul_high {a c n j : ℕ} (ha : a < 2 ^ n) :
    Nat.testBit (a + 2 ^ n * c) (n + j) = Nat.testBit c j := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, pow_add,
    ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (two_pow_pos' n),
    Nat.div_eq_of_lt ha, Nat.zero_add]

theorem testBit_add_mul_low {a c n j : ℕ} (_ha : a < 2 ^ n) (hj : j < n) :
    Nat.testBit (a + 2 ^ n * c) j = Nat.testBit a j := by
  have hpow : (2:ℕ) ^ n = 2 ^ j * 2 ^ (n - j) := by
    rw [← pow_add]; congr 1; omega
  have h2 : (2:ℕ) ^ (n - j) = 2 * 2 ^ (n - j - 1) := by
    conv_lhs => rw [show n - j = (n - j - 1) + 1 from by omega]
    ring
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hpow,
    mul_assoc, Nat.add_mul_div_left _ _ (two_pow_pos' j), h2, mul_assoc,
    Nat.add_mul_mod_self_left]

/-- Inside its own width, a bit is the test `2 ^ k ≤ a`. -/
theorem testBit_eq_decide_le {a k : ℕ} (ha : a < 2 ^ (k + 1)) :
    Nat.testBit a k = decide (2 ^ k ≤ a) := by
  have hp : 0 < (2:ℕ) ^ k := two_pow_pos' k
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hlt : a / 2 ^ k < 2 := by
    refine (Nat.div_lt_iff_lt_mul hp).mpr ?_
    rw [pow_succ] at ha; omega
  by_cases h : 2 ^ k ≤ a
  · have h1 : 1 ≤ a / 2 ^ k := (Nat.one_le_div_iff hp).mpr h
    have : a / 2 ^ k = 1 := by omega
    simp [this, h]
  · have : a / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
    simp [this, h]

theorem testBit_mod_pow_of_lt {a k j : ℕ} (hj : j < k) :
    Nat.testBit (a % 2 ^ k) j = Nat.testBit a j := by
  simp [Nat.testBit_mod_two_pow, hj]

theorem testBit_div_pow (a n j : ℕ) : Nat.testBit (a / 2 ^ n) j = Nat.testBit a (n + j) := by
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

/-! ## The reversible shift completions

`signedShiftLWord` and `signedShiftRWord` (`Framework/Semantics/GateSemantics.lean`)
are the total reversible completions of signed shifts. Here they are shown to be
mutually inverse on `[0, 2 ^ w)`.
-/

theorem signedShiftLWord_of_lt {w n : ℕ} (h : n < w) (u : ℕ) :
    signedShiftLWord w n u =
      ((u / 2 ^ (w - n)) ^^^ (if Nat.testBit u (w - n - 1) then 2 ^ n - 1 else 0))
        + 2 ^ n * (u % 2 ^ (w - n)) := by
  rw [signedShiftLWord, dif_pos h]
  rfl

theorem signedShiftLWord_of_ge {w n : ℕ} (h : ¬ n < w) (u : ℕ) :
    signedShiftLWord w n u = u % 2 ^ w := by
  rw [signedShiftLWord, dif_neg h]

theorem signedShiftRWord_of_lt {w n : ℕ} (h : n < w) (u : ℕ) :
    signedShiftRWord w n u =
      (u / 2 ^ n)
        + 2 ^ (w - n) * ((u % 2 ^ n) ^^^ (if Nat.testBit u (w - 1) then 2 ^ n - 1 else 0)) := by
  rw [signedShiftRWord, dif_pos h]
  rfl

theorem signedShiftRWord_of_ge {w n : ℕ} (h : ¬ n < w) (u : ℕ) :
    signedShiftRWord w n u = u % 2 ^ w := by
  rw [signedShiftRWord, dif_neg h]

theorem signedShiftLWord_lt {w n u : ℕ} (hu : u < 2 ^ w) : signedShiftLWord w n u < 2 ^ w := by
  by_cases h : n < w
  · rw [signedShiftLWord_of_lt h]
    have hpk : 0 < (2:ℕ) ^ (w - n) := two_pow_pos' _
    have hpn : 0 < (2:ℕ) ^ n := two_pow_pos' n
    have hsplit : (2:ℕ) ^ w = 2 ^ n * 2 ^ (w - n) := by rw [← pow_add]; congr 1; omega
    have hd : u / 2 ^ (w - n) < 2 ^ n := (Nat.div_lt_iff_lt_mul hpk).mpr (by omega)
    have hm : (if Nat.testBit u (w - n - 1) then 2 ^ n - 1 else 0) < 2 ^ n := by split <;> omega
    have hx := Nat.xor_lt_two_pow hd hm
    have hkept : u % 2 ^ (w - n) < 2 ^ (w - n) := Nat.mod_lt _ hpk
    nlinarith [hx, hkept, hsplit]
  · rw [signedShiftLWord_of_ge h]; exact Nat.mod_lt _ (two_pow_pos' w)

theorem signedShiftRWord_lt {w n u : ℕ} (hu : u < 2 ^ w) : signedShiftRWord w n u < 2 ^ w := by
  by_cases h : n < w
  · rw [signedShiftRWord_of_lt h]
    have hpk : 0 < (2:ℕ) ^ (w - n) := two_pow_pos' _
    have hpn : 0 < (2:ℕ) ^ n := two_pow_pos' n
    have hsplit : (2:ℕ) ^ w = 2 ^ (w - n) * 2 ^ n := by rw [← pow_add]; congr 1; omega
    have hkeptlt : u / 2 ^ n < 2 ^ (w - n) := (Nat.div_lt_iff_lt_mul hpn).mpr (by omega)
    have hsynlt : u % 2 ^ n < 2 ^ n := Nat.mod_lt _ hpn
    have hm : (if Nat.testBit u (w - 1) then 2 ^ n - 1 else 0) < 2 ^ n := by split <;> omega
    have hx := Nat.xor_lt_two_pow hsynlt hm
    nlinarith [hx, hkeptlt, hsplit]
  · rw [signedShiftRWord_of_ge h]; exact Nat.mod_lt _ (two_pow_pos' w)

theorem signedShiftRWord_signedShiftLWord {w n u : ℕ} (hu : u < 2 ^ w) :
    signedShiftRWord w n (signedShiftLWord w n u) = u := by
  by_cases hnw : n < w
  · have hpk : 0 < (2:ℕ) ^ (w - n) := two_pow_pos' _
    have hpn : 0 < (2:ℕ) ^ n := two_pow_pos' n
    have hsplit : (2:ℕ) ^ w = 2 ^ n * 2 ^ (w - n) := by rw [← pow_add]; congr 1; omega
    set k := w - n with hk
    set d := u / 2 ^ k with hd
    set kept := u % 2 ^ k with hkept
    set m : ℕ := if Nat.testBit u (k - 1) then 2 ^ n - 1 else 0 with hm
    have hdlt : d < 2 ^ n := (Nat.div_lt_iff_lt_mul hpk).mpr (by omega)
    have hmlt : m < 2 ^ n := by rw [hm]; split <;> omega
    have hxlt : d ^^^ m < 2 ^ n := Nat.xor_lt_two_pow hdlt hmlt
    have hkeptlt : kept < 2 ^ k := Nat.mod_lt _ hpk
    rw [signedShiftLWord_of_lt hnw, signedShiftRWord_of_lt hnw, ← hk, ← hd, ← hkept, ← hm]
    have hdiv : ((d ^^^ m) + 2 ^ n * kept) / 2 ^ n = kept := by
      rw [Nat.add_mul_div_left _ _ hpn, Nat.div_eq_of_lt hxlt, Nat.zero_add]
    have hmod : ((d ^^^ m) + 2 ^ n * kept) % 2 ^ n = d ^^^ m := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxlt]
    have hsign : Nat.testBit ((d ^^^ m) + 2 ^ n * kept) (w - 1) = Nat.testBit u (k - 1) := by
      have hw1 : w - 1 = n + (k - 1) := by omega
      rw [hw1, testBit_add_mul_high hxlt, hkept, testBit_mod_pow_of_lt (by omega)]
    rw [hdiv, hmod, hsign, ← hm, Nat.xor_xor_cancel_right, hd, hkept]
    exact Nat.mod_add_div u (2 ^ k)
  · rw [signedShiftLWord_of_ge hnw, Nat.mod_eq_of_lt hu, signedShiftRWord_of_ge hnw,
      Nat.mod_eq_of_lt hu]

theorem signedShiftLWord_signedShiftRWord {w n u : ℕ} (hu : u < 2 ^ w) :
    signedShiftLWord w n (signedShiftRWord w n u) = u := by
  by_cases hnw : n < w
  · have hpk : 0 < (2:ℕ) ^ (w - n) := two_pow_pos' _
    have hpn : 0 < (2:ℕ) ^ n := two_pow_pos' n
    have hsplit : (2:ℕ) ^ w = 2 ^ (w - n) * 2 ^ n := by rw [← pow_add]; congr 1; omega
    set k := w - n with hk
    set kept := u / 2 ^ n with hkept
    set syn := u % 2 ^ n with hsyn
    set m : ℕ := if Nat.testBit u (w - 1) then 2 ^ n - 1 else 0 with hm
    have hkeptlt : kept < 2 ^ k := (Nat.div_lt_iff_lt_mul hpn).mpr (by omega)
    have hsynlt : syn < 2 ^ n := Nat.mod_lt _ hpn
    have hmlt : m < 2 ^ n := by rw [hm]; split <;> omega
    have hxlt : syn ^^^ m < 2 ^ n := Nat.xor_lt_two_pow hsynlt hmlt
    rw [signedShiftRWord_of_lt hnw, signedShiftLWord_of_lt hnw, ← hk, ← hkept, ← hsyn, ← hm]
    have hdiv : (kept + 2 ^ k * (syn ^^^ m)) / 2 ^ k = syn ^^^ m := by
      rw [Nat.add_mul_div_left _ _ hpk, Nat.div_eq_of_lt hkeptlt, Nat.zero_add]
    have hmod : (kept + 2 ^ k * (syn ^^^ m)) % 2 ^ k = kept := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hkeptlt]
    have hsign : Nat.testBit (kept + 2 ^ k * (syn ^^^ m)) (k - 1) = Nat.testBit u (w - 1) := by
      rw [testBit_add_mul_low hkeptlt (by omega), hkept, testBit_div_pow]
      congr 1
      omega
    rw [hdiv, hmod, hsign, ← hm, Nat.xor_xor_cancel_right, hkept, hsyn]
    exact Nat.mod_add_div u (2 ^ n)
  · rw [signedShiftRWord_of_ge hnw, Nat.mod_eq_of_lt hu, signedShiftLWord_of_ge hnw,
      Nat.mod_eq_of_lt hu]

/-! ## The `FitsSignedWidth` branches of `shiftLBasis` and `shiftRBasis`

`shiftLBasis` and `shiftRBasis` each dispatch between an "exact" branch, stated
with `FitsSignedWidth`, and the reversible completion. These two lemmas say the
dispatch is vacuous: on the exact branch the two agree, so each basis map equals
its raw version and inherits the round trips above.
-/

theorem tcModWidth_natCast (w v : ℕ) : tcModWidth w (v : ℤ) = v % 2 ^ w := by
  have h1 := tcModWidth_cast w (v : ℤ)
  have h2 : ((v % 2 ^ w : ℕ) : ℤ) = (v : ℤ) % 2 ^ w := by
    rw [Int.natCast_mod, natCast_two_pow]
  omega

@[simp] theorem tcModWidth_zero (w : ℕ) : tcModWidth w 0 = 0 := by
  have := tcModWidth_natCast w 0
  simpa using this

/-- Multiplying the decoded value by `2 ^ n` and re-encoding is a shift of the
raw word modulo `2 ^ w`. -/
theorem tcModWidth_two_pow_mul_tcDecode {w n u : ℕ} (hn : n < w) :
    tcModWidth w ((2:ℤ) ^ n * tcDecodeWidth w u) = 2 ^ n * (u % 2 ^ (w - n)) := by
  have hcong : ((2:ℤ) ^ n * tcDecodeWidth w u) % 2 ^ w = ((2 ^ n * u : ℕ) : ℤ) % 2 ^ w := by
    rw [Int.mul_emod, tcDecodeWidth_emod w u, ← Int.mul_emod]
    push_cast
    ring_nf
  rw [tcModWidth_congr hcong, tcModWidth_natCast]
  have hsplit : (2:ℕ) ^ w = 2 ^ n * 2 ^ (w - n) := by rw [← pow_add]; congr 1; omega
  rw [hsplit, Nat.mul_mod_mul_left]

/-- The exact branch of `shiftLBasis` fires only where the reversible completion
has an all-zero syndrome, and then the two agree. -/
theorem shiftLWord_fits_eq {w n u : ℕ} (hu : u < 2 ^ w)
    (hfit : FitsSignedWidth w ((2:ℤ) ^ n * tcDecodeWidth w u)) :
    tcModWidth w ((2:ℤ) ^ n * tcDecodeWidth w u) = signedShiftLWord w n u := by
  obtain ⟨hw, hlo, hhi⟩ := hfit
  rw [signedMin] at hlo
  rw [signedMax] at hhi
  rw [natCast_two_pow] at hlo hhi
  by_cases hn : n < w
  · set k := w - n with hk
    have hk1 : 1 ≤ k := by omega
    have hw1 : w - 1 = n + (k - 1) := by omega
    have hpowsplit : (2:ℤ) ^ (w - 1) = 2 ^ n * 2 ^ (k - 1) := by rw [hw1, pow_add]
    have hpn : (0:ℤ) < 2 ^ n := two_pow_pos n
    -- divide the fit bounds by `2 ^ n`
    have hxlo : -(2:ℤ) ^ (k - 1) ≤ tcDecodeWidth w u := by
      rw [hpowsplit] at hlo; nlinarith [hlo, hpn]
    have hxhi : tcDecodeWidth w u < (2:ℤ) ^ (k - 1) := by
      rw [hpowsplit] at hhi; nlinarith [hhi, hpn]
    have hsyn : (u / 2 ^ k) ^^^ (if Nat.testBit u (k - 1) then 2 ^ n - 1 else 0) = 0 := by
      rw [Nat.xor_eq_zero_iff]
      have hpkn : (2:ℕ) ^ w = 2 ^ k * 2 ^ n := by rw [← pow_add]; congr 1; omega
      have hpk1 : (2:ℕ) ^ (k - 1) * 2 = 2 ^ k := by
        rw [← pow_succ]; congr 1; omega
      by_cases hsgn : u < 2 ^ (w - 1)
      · -- nonnegative: the whole word already fits below `2 ^ (k-1)`
        have hx : tcDecodeWidth w u = (u : ℤ) := by rw [tcDecodeWidth_eq hw, if_pos hsgn]
        have hult : u < 2 ^ (k - 1) := by
          have : (u : ℤ) < (2:ℤ) ^ (k - 1) := by rw [← hx]; exact hxhi
          rw [← natCast_two_pow] at this
          exact_mod_cast this
        rw [Nat.div_eq_of_lt (by omega), if_neg (by simp [Nat.testBit_eq_false_of_lt hult])]
      · -- negative: the top `n+1` bits are all ones
        push_neg at hsgn
        have hx : tcDecodeWidth w u = (u : ℤ) - 2 ^ w := by
          rw [tcDecodeWidth_eq hw, if_neg (by omega)]
        have hge : (2:ℕ) ^ w ≤ u + 2 ^ (k - 1) := by
          have h1 : -(2:ℤ) ^ (k - 1) ≤ (u : ℤ) - 2 ^ w := by rw [← hx]; exact hxlo
          have h2 : ((2 ^ w : ℕ) : ℤ) ≤ ((u + 2 ^ (k - 1) : ℕ) : ℤ) := by
            push_cast; linarith
          exact_mod_cast h2
        have hpn' : 0 < (2:ℕ) ^ n := two_pow_pos' n
        have hpk' : 0 < (2:ℕ) ^ (k - 1) := two_pow_pos' _
        have hA : (2:ℕ) ^ n * 2 ^ k = 2 ^ w := by rw [hpkn]; ring
        have hB : (2 ^ n - 1) * 2 ^ k = 2 ^ w - 2 ^ k := by
          rw [Nat.sub_mul, one_mul, hA]
        have hC : (2 ^ n - 1 + 1) * 2 ^ k = 2 ^ w := by
          rw [Nat.sub_add_cancel hpn', hA]
        have hdiv : u / 2 ^ k = 2 ^ n - 1 :=
          Nat.div_eq_of_lt_le (by omega) (by omega)
        have hkw : (2:ℕ) ^ k ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hmodk : 2 ^ (k - 1) ≤ u % 2 ^ k := by
          have hma := Nat.mod_add_div u (2 ^ k)
          rw [hdiv, show (2:ℕ) ^ k * (2 ^ n - 1) = 2 ^ w - 2 ^ k from by
            rw [mul_comm]; exact hB] at hma
          omega
        have hmodlt : u % 2 ^ k < 2 ^ k := Nat.mod_lt _ (two_pow_pos' k)
        have hbit : Nat.testBit u (k - 1) = true := by
          rw [← testBit_mod_pow_of_lt (a := u) (k := k) (j := k - 1) (by omega),
            testBit_eq_decide_le (by omega)]
          simp [hmodk]
        rw [hdiv, if_pos (by simp [hbit])]
    rw [tcModWidth_two_pow_mul_tcDecode hn, signedShiftLWord_of_lt hn, ← hk, hsyn, Nat.zero_add]
  · -- `n ≥ w`: only the zero word fits
    push_neg at hn
    have hple : (2:ℤ) ^ (w - 1) < 2 ^ n :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    have hx : tcDecodeWidth w u = 0 := by
      rcases lt_trichotomy (tcDecodeWidth w u) 0 with h | h | h
      · exfalso
        have : tcDecodeWidth w u ≤ -1 := by omega
        nlinarith [two_pow_pos n, hlo, hple]
      · exact h
      · exfalso
        have : 1 ≤ tcDecodeWidth w u := by omega
        nlinarith [two_pow_pos n, hhi, hple]
    have hu0 : u = 0 := by
      have := tcModWidth_tcDecodeWidth hu
      rw [hx] at this
      simpa using this.symm
    rw [hx, hu0, signedShiftLWord_of_ge (by omega)]
    simp

/-- The exact branch of `shiftRBasis` agrees with the reversible completion. -/
theorem shiftRWord_fits_eq {w n u : ℕ} {q : ℤ} (hu : u < 2 ^ w)
    (hq : tcDecodeWidth w u = (2:ℤ) ^ n * q) (hfit : FitsSignedWidth w q) :
    tcModWidth w q = signedShiftRWord w n u := by
  obtain ⟨hw, hlo, hhi⟩ := hfit
  rw [signedMin, natCast_two_pow] at hlo
  rw [signedMax, natCast_two_pow] at hhi
  have hpn : (0:ℤ) < 2 ^ n := two_pow_pos n
  have hpw : (0:ℤ) < 2 ^ w := two_pow_pos w
  have hwle : (2:ℤ) ^ (w - 1) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) (by omega)
  by_cases hn : n < w
  · set k := w - n with hk
    have hsplitZ : (2:ℤ) ^ w = 2 ^ n * 2 ^ k := by rw [← pow_add]; congr 1; omega
    have hsplitN : (2:ℕ) ^ w = 2 ^ k * 2 ^ n := by rw [← pow_add]; congr 1; omega
    have hpn' : 0 < (2:ℕ) ^ n := two_pow_pos' n
    -- the raw word is a multiple of `2 ^ n`
    have hdw : ((2:ℤ) ^ n) ∣ (2:ℤ) ^ w := ⟨2 ^ k, hsplitZ⟩
    have hsynN : u % 2 ^ n = 0 := by
      have hmod := tcDecodeWidth_emod w u
      rw [hq] at hmod
      have e1 : (u : ℤ) % 2 ^ n = ((u : ℤ) % 2 ^ w) % 2 ^ n := (Int.emod_emod_of_dvd _ hdw).symm
      rw [← hmod, Int.emod_emod_of_dvd _ hdw, Int.mul_emod_right] at e1
      have hdvdZ : ((2 ^ n : ℕ) : ℤ) ∣ (u : ℤ) := by
        rw [natCast_two_pow]; exact Int.dvd_of_emod_eq_zero e1
      obtain ⟨c, hc⟩ : (2 ^ n : ℕ) ∣ u := by exact_mod_cast hdvdZ
      rw [hc, Nat.mul_mod_right]
    have hcast : ((tcModWidth w q : ℕ) : ℤ) = q % 2 ^ w := tcModWidth_cast w q
    have hudiv : ((u / 2 ^ n : ℕ) : ℤ) = (u : ℤ) / 2 ^ n := by
      rw [Int.natCast_div, natCast_two_pow]
    have hwpow : w - 1 + 1 = w := by omega
    have hunn : (0:ℤ) ≤ (u : ℤ) := Int.natCast_nonneg u
    rw [signedShiftRWord_of_lt hn, ← hk, hsynN, Nat.zero_xor]
    by_cases hsgn : u < 2 ^ (w - 1)
    · have hx : tcDecodeWidth w u = (u : ℤ) := by rw [tcDecodeWidth_eq hw, if_pos hsgn]
      have hz : (u : ℤ) = 2 ^ n * q := by rw [← hx, hq]
      have hq0 : 0 ≤ q := by nlinarith [hunn, hpn]
      have hbit : Nat.testBit u (w - 1) = false := by
        rw [testBit_eq_decide_le (by rw [hwpow]; exact hu)]
        simp [Nat.not_le.mpr hsgn]
      rw [hbit, if_neg (by simp), mul_zero, Nat.add_zero]
      have hfin : ((tcModWidth w q : ℕ) : ℤ) = ((u / 2 ^ n : ℕ) : ℤ) := by
        rw [hcast, hudiv, hz, Int.mul_ediv_cancel_left _ (ne_of_gt hpn)]
        exact Int.emod_eq_of_lt hq0 (by linarith)
      exact_mod_cast hfin
    · push_neg at hsgn
      have hx : tcDecodeWidth w u = (u : ℤ) - 2 ^ w := by
        rw [tcDecodeWidth_eq hw, if_neg (by omega)]
      have hz0 : (u : ℤ) - 2 ^ w = 2 ^ n * q := by rw [← hx, hq]
      have hz : (u : ℤ) = 2 ^ n * (q + 2 ^ k) := by rw [mul_add, ← hsplitZ]; linarith
      have hultZ : (u : ℤ) < 2 ^ w := int_lt_of_nat_lt_pow hu
      have hqneg : q < 0 := by nlinarith [hpn, hultZ, hz0]
      have hbit : Nat.testBit u (w - 1) = true := by
        rw [testBit_eq_decide_le (by rw [hwpow]; exact hu)]
        simp [hsgn]
      rw [hbit, if_pos rfl]
      have hone : (1:ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
      have hfin : ((tcModWidth w q : ℕ) : ℤ)
          = ((u / 2 ^ n + 2 ^ k * (2 ^ n - 1) : ℕ) : ℤ) := by
        rw [hcast]
        push_cast [Nat.cast_sub hone]
        rw [hz, Int.mul_ediv_cancel_left _ (ne_of_gt hpn)]
        have hmodq : q % 2 ^ w = q + 2 ^ w := by
          have h1 : q % 2 ^ w = (q + 2 ^ w * 1) % 2 ^ w := by
            rw [Int.add_mul_emod_self_left]
          rw [h1, mul_one]
          exact Int.emod_eq_of_lt (by linarith) (by linarith)
        rw [hmodq, hsplitZ]
        ring
      exact_mod_cast hfin
  · -- `n ≥ w`: only `q = 0` fits
    push_neg at hn
    have hple : (2:ℤ) ^ (w - 1) < 2 ^ n := pow_lt_pow_right₀ (by norm_num) (by omega)
    obtain ⟨hb1, hb2⟩ := tcDecodeWidth_bounds hw hu
    rw [hq] at hb1 hb2
    have hq0 : q = 0 := by
      rcases lt_trichotomy q 0 with h | h | h
      · exfalso; have : q ≤ -1 := by omega
        nlinarith [hb1, hpn, hple]
      · exact h
      · exfalso; have : 1 ≤ q := by omega
        nlinarith [hb2, hpn, hple]
    have hx : tcDecodeWidth w u = 0 := by rw [hq, hq0, mul_zero]
    have hu0 : u = 0 := by
      have := tcModWidth_tcDecodeWidth hu
      rw [hx] at this
      simpa using this.symm
    rw [hq0, hu0, signedShiftRWord_of_ge (by omega)]
    simp

/-! ## `tcModWidth` as a `ZMOD 2 ^ w` quotient map

`Negate` and `AddScaled` write `tcModWidth w z` and then read the result back
through `tcDecodeWidth`. Both steps preserve the class mod `2 ^ w`, so the round
trips are `Int.ModEq` calculations.
-/

theorem tcModWidth_modEq {w : ℕ} {z₁ z₂ : ℤ} (h : Int.ModEq (2 ^ w) z₁ z₂) :
    tcModWidth w z₁ = tcModWidth w z₂ := tcModWidth_congr h

theorem tcDecodeWidth_modEq (w u : ℕ) : Int.ModEq (2 ^ w) (tcDecodeWidth w u) (u : ℤ) :=
  tcDecodeWidth_emod w u

theorem tcModWidth_self_modEq (w : ℕ) (z : ℤ) :
    Int.ModEq (2 ^ w) ((tcModWidth w z : ℕ) : ℤ) z := by
  rw [Int.ModEq, tcModWidth_cast, Int.emod_emod_of_dvd _ dvd_rfl]

/-- The value a register holds after `tcModWidth w z` is written to it, decoded
again, is still `z` mod `2 ^ w`. -/
theorem tcDecodeWidth_tcModWidth_modEq (w : ℕ) (z : ℤ) :
    Int.ModEq (2 ^ w) (tcDecodeWidth w (tcModWidth w z)) z :=
  (tcDecodeWidth_modEq w (tcModWidth w z)).trans (tcModWidth_self_modEq w z)

/-- The workhorse for the register round trips: a value that is congruent to an
in-range natural mod `2 ^ w` re-encodes to that natural. -/
theorem tcModWidth_eq_self {w u : ℕ} (hu : u < 2 ^ w) {z : ℤ}
    (h : Int.ModEq (2 ^ w) z (u : ℤ)) : tcModWidth w z = u := by
  rw [tcModWidth_modEq h, tcModWidth_natCast, Nat.mod_eq_of_lt hu]

end Model
end Shor
