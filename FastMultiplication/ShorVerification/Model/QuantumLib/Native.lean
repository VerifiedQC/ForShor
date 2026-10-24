import FastMultiplication.ShorVerification.Model.QuantumLib.Denote

/-!
# The native gates, padded with identities

The sanity lemmas that tie `denote` back to
QuantumLib's own `hadamard`, `cnot` and `phaseShift`.

`Denote.lean` defines every primitive by its entries rather than by `kron`-padding,
precisely so that the `Fin` casts of padding never leak into the transfer
proof. They are quarantined here instead. The left `kron` factor is
the high digit, so a gate on qubit `q` of `dim` pads as

```
(1 : CSquare (2 ^ (dim - q - 1))) ⊗ gate ⊗ (1 : CSquare (2 ^ q))
```

Nothing in `Transfer.lean` or `Headline.lean` depends on this file; it exists to
make the final theorems statements *about QuantumLib* rather than about matrices
that merely live in its types.
-/

namespace Shor
namespace Model
namespace QuantumLib

open Matrix
open scoped Kron

/-! ## Agreeing away from a qubit -/

theorem two_pow_split (dim q : ℕ) (hq : q < dim) : 2 ^ (dim - q - 1) * 2 * 2 ^ q = 2 ^ dim := by
  rw [← pow_succ, ← pow_add]
  congr 1
  omega

/-- Agreement of all bits but one, in decidable arithmetic form. -/
def AgreeOff (q y x : ℕ) : Prop := y % 2 ^ q = x % 2 ^ q ∧ y / 2 ^ (q + 1) = x / 2 ^ (q + 1)

instance (q y x : ℕ) : Decidable (AgreeOff q y x) := by unfold AgreeOff; infer_instance

/-- Agreement of all bits but one, arithmetically. -/
theorem agree_off_iff (q y x : ℕ) :
    (∀ i, i ≠ q → Nat.testBit y i = Nat.testBit x i)
      ↔ AgreeOff q y x := by
  rw [AgreeOff]
  constructor
  · intro h
    refine ⟨Nat.eq_of_testBit_eq fun i => ?_, Nat.eq_of_testBit_eq fun i => ?_⟩
    · by_cases hi : i < q
      · rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, h i (by omega)]
      · simp [Nat.testBit_mod_two_pow, hi]
    · rw [testBit_div_pow, testBit_div_pow, h _ (by omega)]
  · rintro ⟨h1, h2⟩ i hi
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have e1 := congrArg (fun n => Nat.testBit n i) h1
      simpa [Nat.testBit_mod_two_pow, hlt] using e1
    · have e2 := congrArg (fun n => Nat.testBit n (i - (q + 1))) h2
      simp only [testBit_div_pow] at e2
      rwa [show q + 1 + (i - (q + 1)) = i from by omega] at e2

theorem bitIdx_false_eq_iff {dim q : ℕ} (hq : q < dim) (y x : Fin (2 ^ dim)) :
    bitIdx dim q false y = bitIdx dim q false x
      ↔ ∀ i, i ≠ q → Nat.testBit y.1 i = Nat.testBit x.1 i := by
  constructor
  · intro h i hi
    have hb : Function.update (idxBasis dim y) q false
        = Function.update (idxBasis dim x) q false := by
      rw [← idxBasis_bitIdx hq false y, ← idxBasis_bitIdx hq false x, h]
    have := congrArg (fun f => f i) hb
    simpa [Function.update_of_ne hi, idxBasis] using this
  · intro h
    rw [bitIdx, bitIdx]
    congr 1
    funext i
    by_cases hi : i = q
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact h i hi

theorem eq_iff_agree_and_bit {dim q : ℕ} (y x : Fin (2 ^ dim)) :
    y = x ↔ (∀ i, i ≠ q → Nat.testBit y.1 i = Nat.testBit x.1 i)
      ∧ Nat.testBit y.1 q = Nat.testBit x.1 q := by
  constructor
  · rintro rfl; exact ⟨fun _ _ => rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    refine Fin.ext (Nat.eq_of_testBit_eq fun i => ?_)
    by_cases hi : i = q
    · subst hi; exact h2
    · exact h1 i hi

/-! ## One-qubit padding, once and for all -/

/-- The `Fin 2` index of a bit. -/
def bIdx (c : Bool) : Fin 2 := if c then 1 else 0

@[simp] theorem bIdx_val (c : Bool) : (bIdx c).1 = if c then 1 else 0 := by
  cases c <;> rfl

theorem fin_two_eq_bIdx (u : Fin 2) : u = bIdx (decide (u.1 = 1)) := by
  fin_cases u <;> rfl

/-- **The one-qubit padding lemma.** Any matrix whose entries depend only on
agreement away from qubit `q` and on the two bits at `q` is the identity-padded
`kron` of the corresponding `2 × 2` gate. -/
theorem single_qubit_kron {dim q : ℕ} (hq : q < dim) (G : CSquare 2) (M : CSquare (2 ^ dim))
    (hM : ∀ y x : Fin (2 ^ dim), M y x =
      if AgreeOff q y.1 x.1
      then G (bIdx (Nat.testBit y.1 q)) (bIdx (Nat.testBit x.1 q)) else 0) :
    M.submatrix (finCongr (two_pow_split dim q hq)) (finCongr (two_pow_split dim q hq))
      = (1 : CSquare (2 ^ (dim - q - 1))) ⊗ G ⊗ (1 : CSquare (2 ^ q)) := by
  ext i j
  rw [Matrix.submatrix_apply, hM, Matrix.kron_apply, Matrix.kron_apply]
  simp only [finCongr_apply, Fin.val_cast]
  have hpow : (2 : ℕ) ^ q * 2 = 2 ^ (q + 1) := by rw [pow_succ]
  have hdiv : ∀ k : Fin (2 ^ (dim - q - 1) * 2 * 2 ^ q),
      (k.divNat.divNat : Fin (2 ^ (dim - q - 1))).1 = k.1 / 2 ^ (q + 1) := by
    intro k
    show k.1 / 2 ^ q / 2 = _
    rw [Nat.div_div_eq_div_mul, hpow]
  have hmod2 : ∀ k : Fin (2 ^ (dim - q - 1) * 2 * 2 ^ q),
      (k.divNat.modNat : Fin 2) = bIdx (Nat.testBit k.1 q) := by
    intro k
    refine Fin.ext ?_
    show k.1 / 2 ^ q % 2 = _
    rw [bIdx_val, Nat.testBit_eq_decide_div_mod_eq]
    have : k.1 / 2 ^ q % 2 < 2 := Nat.mod_lt _ (by norm_num)
    by_cases h : k.1 / 2 ^ q % 2 = 1
    · simp [h]
    · simp [h]; omega
  have hmodq : ∀ k : Fin (2 ^ (dim - q - 1) * 2 * 2 ^ q),
      (k.modNat : Fin (2 ^ q)).1 = k.1 % 2 ^ q := fun _ => rfl
  rw [hmod2, hmod2, Matrix.one_apply, Matrix.one_apply]
  by_cases hagree : AgreeOff q i.1 j.1
  · rw [ite_eq_left hagree, ite_eq_left (Fin.ext (by rw [hdiv, hdiv, hagree.2])),
      ite_eq_left (Fin.ext (by rw [hmodq, hmodq, hagree.1]))]
    simp
  · rw [ite_eq_right hagree]
    rw [AgreeOff, not_and_or] at hagree
    rcases hagree with h | h
    · rw [ite_eq_right (show ¬ (i.modNat = j.modNat) from fun hc =>
        h (by rw [← hmodq i, ← hmodq j]; exact congrArg Fin.val hc)), mul_zero]
    · rw [ite_eq_right (show ¬ (i.divNat.divNat = j.divNat.divNat) from fun hc =>
        h (by rw [← hdiv i, ← hdiv j]; exact congrArg Fin.val hc)), zero_mul, zero_mul]

/-! ## Hadamard -/

theorem hs_eq_sqrt_inv : hs = ((Real.sqrt 2⁻¹ : ℝ) : ℂ) := by
  rw [hs, Real.sqrt_inv, Complex.ofReal_inv]
  exact (one_div _).trans rfl

theorem hadamard_apply (c d : Bool) :
    _root_.hadamard (bIdx c) (bIdx d) = hs * (if c && d then -1 else 1) := by
  rw [hs_eq_sqrt_inv, _root_.hadamard]
  cases c <;> cases d <;>
    simp [bIdx, Matrix.smul_apply, Complex.real_smul]

/-- **Hadamard on qubit `q` is QuantumLib's `hadamard`, padded.** -/
theorem hMatrix_kron {dim q : ℕ} (hq : q < dim) :
    (hMatrix dim q).submatrix (finCongr (two_pow_split dim q hq))
        (finCongr (two_pow_split dim q hq))
      = (1 : CSquare (2 ^ (dim - q - 1))) ⊗ _root_.hadamard ⊗ (1 : CSquare (2 ^ q)) := by
  refine single_qubit_kron hq _ _ fun y x => ?_
  rw [hMatrix_apply, hadamard_apply]
  by_cases h : AgreeOff q y.1 x.1
  · rw [ite_eq_left h,
      ite_eq_left ((bitIdx_false_eq_iff hq y x).mpr ((agree_off_iff q y.1 x.1).mpr h))]
    rfl
  · rw [ite_eq_right h,
      ite_eq_right (fun hc => h ((agree_off_iff q y.1 x.1).mp ((bitIdx_false_eq_iff hq y x).mp hc)))]

/-! ## Phase shift -/

theorem phaseShift_apply (φ : ℝ) (c d : Bool) :
    _root_.phaseShift φ (bIdx c) (bIdx d) =
      if c = d then (if c then Complex.exp ((φ : ℂ) * Complex.I) else 1) else 0 := by
  rw [_root_.phaseShift]
  cases c <;> cases d <;> simp [bIdx]

/-- **`LowGate.Phase` on qubit `q` is QuantumLib's `phaseShift`, padded.** -/
theorem phaseMatrix_kron {dim q : ℕ} (hq : q < dim) (θ : Angle) :
    (diagMatrix dim (lowPhaseDiag q θ)).submatrix (finCongr (two_pow_split dim q hq))
        (finCongr (two_pow_split dim q hq))
      = (1 : CSquare (2 ^ (dim - q - 1))) ⊗ _root_.phaseShift (Angle.toReal θ)
          ⊗ (1 : CSquare (2 ^ q)) := by
  refine single_qubit_kron hq _ _ fun y x => ?_
  rw [diagMatrix, phaseShift_apply]
  by_cases h : AgreeOff q y.1 x.1
  · rw [ite_eq_left h]
    by_cases hb : Nat.testBit y.1 q = Nat.testBit x.1 q
    · rw [ite_eq_left hb,
        ite_eq_left ((eq_iff_agree_and_bit (q := q) y x).mpr ⟨(agree_off_iff q y.1 x.1).mpr h, hb⟩)]
      rw [lowPhaseDiag, idxBasis_apply, hb]
    · rw [ite_eq_right hb, ite_eq_right (fun hc => hb (by rw [hc]))]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h ((agree_off_iff q y.1 x.1).mp (by rw [hc]; exact fun _ _ => rfl)))]

/-! ## Two-qubit padding, and `cnot` -/

theorem two_pow_split2 (dim q : ℕ) (hq : q + 1 < dim) :
    2 ^ (dim - q - 2) * 4 * 2 ^ q = 2 ^ dim := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add, ← pow_add]
  congr 1
  omega

/-- Agreement of all bits but two adjacent ones. -/
def AgreeOff2 (q y x : ℕ) : Prop := y % 2 ^ q = x % 2 ^ q ∧ y / 2 ^ (q + 2) = x / 2 ^ (q + 2)

instance (q y x : ℕ) : Decidable (AgreeOff2 q y x) := by unfold AgreeOff2; infer_instance

theorem agree_off2_iff (q y x : ℕ) :
    (∀ i, i ≠ q → i ≠ q + 1 → Nat.testBit y i = Nat.testBit x i) ↔ AgreeOff2 q y x := by
  rw [AgreeOff2]
  constructor
  · intro h
    refine ⟨Nat.eq_of_testBit_eq fun i => ?_, Nat.eq_of_testBit_eq fun i => ?_⟩
    · by_cases hi : i < q
      · rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, h i (by omega) (by omega)]
      · simp [Nat.testBit_mod_two_pow, hi]
    · rw [testBit_div_pow, testBit_div_pow, h _ (by omega) (by omega)]
  · rintro ⟨h1, h2⟩ i hi hi'
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have e1 := congrArg (fun n => Nat.testBit n i) h1
      simpa [Nat.testBit_mod_two_pow, hlt] using e1
    · have e2 := congrArg (fun n => Nat.testBit n (i - (q + 2))) h2
      simp only [testBit_div_pow] at e2
      rwa [show q + 2 + (i - (q + 2)) = i from by omega] at e2

theorem agree_off_split {q y x : ℕ} :
    (∀ i, i ≠ q → Nat.testBit y i = Nat.testBit x i)
      ↔ ((∀ i, i ≠ q → i ≠ q + 1 → Nat.testBit y i = Nat.testBit x i)
          ∧ Nat.testBit y (q + 1) = Nat.testBit x (q + 1)) := by
  constructor
  · intro h
    exact ⟨fun i hi _ => h i hi, h (q + 1) (by omega)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases hi' : i = q + 1
    · subst hi'; exact h2
    · exact h1 i hi hi'

/-- The `Fin 4` index of a pair of bits, high bit first (the `kron` order). -/
def pIdx (hi lo : Bool) : Fin 4 := ⟨(if hi then 2 else 0) + (if lo then 1 else 0), by
  cases hi <;> cases lo <;> norm_num⟩

@[simp] theorem pIdx_val (hi lo : Bool) :
    (pIdx hi lo).1 = (if hi then 2 else 0) + (if lo then 1 else 0) := rfl

/-- **The two-qubit padding lemma**, for adjacent qubits `q + 1` (high) and `q`. -/
theorem two_qubit_kron {dim q : ℕ} (hq : q + 1 < dim) (G : CSquare 4) (M : CSquare (2 ^ dim))
    (hM : ∀ y x : Fin (2 ^ dim), M y x =
      if AgreeOff2 q y.1 x.1
      then G (pIdx (Nat.testBit y.1 (q + 1)) (Nat.testBit y.1 q))
             (pIdx (Nat.testBit x.1 (q + 1)) (Nat.testBit x.1 q)) else 0) :
    M.submatrix (finCongr (two_pow_split2 dim q hq)) (finCongr (two_pow_split2 dim q hq))
      = (1 : CSquare (2 ^ (dim - q - 2))) ⊗ G ⊗ (1 : CSquare (2 ^ q)) := by
  ext i j
  rw [Matrix.submatrix_apply, hM, Matrix.kron_apply, Matrix.kron_apply]
  simp only [finCongr_apply, Fin.val_cast]
  have hpow : (2 : ℕ) ^ q * 4 = 2 ^ (q + 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
  have hdiv : ∀ k : Fin (2 ^ (dim - q - 2) * 4 * 2 ^ q),
      (k.divNat.divNat : Fin (2 ^ (dim - q - 2))).1 = k.1 / 2 ^ (q + 2) := by
    intro k
    show k.1 / 2 ^ q / 4 = _
    rw [Nat.div_div_eq_div_mul, hpow]
  have hmod4 : ∀ k : Fin (2 ^ (dim - q - 2) * 4 * 2 ^ q),
      (k.divNat.modNat : Fin 4) = pIdx (Nat.testBit k.1 (q + 1)) (Nat.testBit k.1 q) := by
    intro k
    refine Fin.ext ?_
    show k.1 / 2 ^ q % 4 = _
    rw [pIdx_val, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have e1 : k.1 / 2 ^ (q + 1) = k.1 / 2 ^ q / 2 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    rw [e1]
    have h2 : k.1 / 2 ^ q % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have h3 : k.1 / 2 ^ q / 2 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have h4 : k.1 / 2 ^ q % 4 = 2 * (k.1 / 2 ^ q / 2 % 2) + k.1 / 2 ^ q % 2 := by omega
    rw [h4]
    by_cases a : k.1 / 2 ^ q / 2 % 2 = 1 <;> by_cases b : k.1 / 2 ^ q % 2 = 1 <;>
      simp [a, b] <;> omega
  have hmodq : ∀ k : Fin (2 ^ (dim - q - 2) * 4 * 2 ^ q),
      (k.modNat : Fin (2 ^ q)).1 = k.1 % 2 ^ q := fun _ => rfl
  rw [hmod4, hmod4, Matrix.one_apply, Matrix.one_apply]
  by_cases hagree : AgreeOff2 q i.1 j.1
  · rw [ite_eq_left hagree, ite_eq_left (Fin.ext (by rw [hdiv, hdiv, hagree.2])),
      ite_eq_left (Fin.ext (by rw [hmodq, hmodq, hagree.1]))]
    simp
  · rw [ite_eq_right hagree]
    rw [AgreeOff2, not_and_or] at hagree
    rcases hagree with h | h
    · rw [ite_eq_right (show ¬ (i.modNat = j.modNat) from fun hc =>
        h (by rw [← hmodq i, ← hmodq j]; exact congrArg Fin.val hc)), mul_zero]
    · rw [ite_eq_right (show ¬ (i.divNat.divNat = j.divNat.divNat) from fun hc =>
        h (by rw [← hdiv i, ← hdiv j]; exact congrArg Fin.val hc)), zero_mul, zero_mul]

theorem cnot_apply (c t c' t' : Bool) :
    _root_.cnot (pIdx c t) (pIdx c' t') =
      if c = c' ∧ t = (if c' then !t' else t') then 1 else 0 := by
  cases c <;> cases t <;> cases c' <;> cases t' <;>
    simp [pIdx, _root_.cnot, Fin.mk_one, Matrix.cons_val', Matrix.cons_val_zero]

theorem cnotBasis_apply_of_ne {ctrl target : ℕ} (h : ctrl ≠ target) (b : ModelBasis) (i : ℕ) :
    cnotBasis (Basis := ModelBasis) ctrl target b i
      = if i = target then (if b ctrl then !b target else b target) else b i := by
  rw [cnotBasis_eq, ite_eq_right h]
  by_cases hc : b ctrl
  · rw [ite_eq_left hc]
    by_cases hi : i = target
    · subst hi; simp [hc]
    · rw [Function.update_of_ne hi, ite_eq_right hi]
  · rw [ite_eq_right hc]
    by_cases hi : i = target
    · subst hi; simp [hc]
    · rw [ite_eq_right hi]

theorem permIdx_cnot {dim q : ℕ} (hq : q + 1 < dim) (x : Fin (2 ^ dim)) (i : ℕ) :
    Nat.testBit (permIdx dim (cnotPerm (q + 1) q) x).1 i
      = if i = q then (if Nat.testBit x.1 (q + 1) then !Nat.testBit x.1 q else Nat.testBit x.1 q)
        else Nat.testBit x.1 i := by
  have hbelow : Below dim (cnotBasis (Basis := ModelBasis) (q + 1) q (idxBasis dim x)) :=
    below_cnotBasis (by omega) _ (idxBasis_below dim x)
  have he : idxBasis dim (permIdx dim (cnotPerm (q + 1) q) x)
      = cnotBasis (Basis := ModelBasis) (q + 1) q (idxBasis dim x) :=
    idxBasis_basisIdx hbelow
  have e := congrArg (fun f => f i) he
  simp only [idxBasis_apply, cnotBasis_apply_of_ne (show q + 1 ≠ q from by omega)] at e
  exact e

theorem cnot_permIdx_eq_iff {dim q : ℕ} (hq : q + 1 < dim) (y x : Fin (2 ^ dim)) :
    y = permIdx dim (cnotPerm (q + 1) q) x
      ↔ ((∀ i, i ≠ q → Nat.testBit y.1 i = Nat.testBit x.1 i)
          ∧ Nat.testBit y.1 q
              = (if Nat.testBit x.1 (q + 1) then !Nat.testBit x.1 q else Nat.testBit x.1 q)) := by
  constructor
  · rintro rfl
    exact ⟨fun i hi => by rw [permIdx_cnot hq x i, ite_eq_right hi],
      by rw [permIdx_cnot hq x q, ite_eq_left rfl]⟩
  · rintro ⟨h1, h2⟩
    refine Fin.ext (Nat.eq_of_testBit_eq fun i => ?_)
    rw [permIdx_cnot hq x i]
    by_cases hi : i = q
    · subst hi; rw [ite_eq_left rfl]; exact h2
    · rw [ite_eq_right hi]; exact h1 i hi

/-- **`CNOT` on adjacent qubits is QuantumLib's `cnot`, padded.** The control is
`q + 1`, the high (left-`kron`) qubit, matching `cnot`'s own convention. -/
theorem cnotMatrix_kron {dim q : ℕ} (hq : q + 1 < dim) :
    (permMatrix dim (cnotPerm (q + 1) q)).submatrix (finCongr (two_pow_split2 dim q hq))
        (finCongr (two_pow_split2 dim q hq))
      = (1 : CSquare (2 ^ (dim - q - 2))) ⊗ _root_.cnot ⊗ (1 : CSquare (2 ^ q)) := by
  refine two_qubit_kron hq _ _ fun y x => ?_
  rw [permMatrix, cnot_apply]
  by_cases hA : AgreeOff2 q y.1 x.1
  · rw [ite_eq_left hA]
    by_cases hB : Nat.testBit y.1 (q + 1) = Nat.testBit x.1 (q + 1) ∧
        Nat.testBit y.1 q
          = (if Nat.testBit x.1 (q + 1) then !Nat.testBit x.1 q else Nat.testBit x.1 q)
    · rw [ite_eq_left hB, ite_eq_left ((cnot_permIdx_eq_iff hq y x).mpr
        ⟨agree_off_split.mpr ⟨(agree_off2_iff q y.1 x.1).mpr hA, hB.1⟩, hB.2⟩)]
    · rw [ite_eq_right hB, ite_eq_right (fun hc => hB ?_)]
      obtain ⟨ha, hb⟩ := (cnot_permIdx_eq_iff hq y x).mp hc
      exact ⟨(agree_off_split.mp ha).2, hb⟩
  · rw [ite_eq_right hA, ite_eq_right (fun hc => hA ?_)]
    obtain ⟨ha, _⟩ := (cnot_permIdx_eq_iff hq y x).mp hc
    exact (agree_off2_iff q y.1 x.1).mp (agree_off_split.mp ha).1

end QuantumLib
end Model
end Shor
