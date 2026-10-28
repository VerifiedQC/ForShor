import ForShor.ShorVerification.Model.QuantumLib.Embed
import ForShor.ShorVerification.Model.Standard.LowGates

/-!
# `denote` — every `LowGate` as a `CSquare (2 ^ dim)`

No gate is defined by kron-padding with identities. Each
primitive's matrix is given **directly by its entries**, reusing the basis maps
`Standard/BasisMaps.lean` already proves bijective and the Hadamard formula
`Standard/Blocks.lean` already uses. Kron-padded forms are *proved* equal to
these in `Native.lean`, where all the `Fin` casts are quarantined.

The arithmetic gates — `ShiftL`, `ShiftR`, `Negate`, `AddScaled`,
`signExtend`, `signDealloc`, `RadixReverse` — enter as permutation matrices.
That is faithful to the development, which charges them through
`shorGateCostModel` rather than decomposing them into Toffolis.
-/

namespace Shor
namespace Model
namespace QuantumLib

open Matrix
open scoped ComplexConjugate

/-! ## The qubit ceiling of a gate -/

/-- One past the largest qubit name in a register (`0` for the empty register). -/
def regCeil (r : Reg) : ℕ := r.qubits.foldr (fun q m => max (q + 1) m) 0

theorem lt_foldr_ceil : ∀ (l : List ℕ) {q : ℕ}, q ∈ l → q < l.foldr (fun a m => max (a + 1) m) 0
  | [], _, h => by simp at h
  | a :: as, q, h => by
      rw [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · omega
      · have := lt_foldr_ceil as h'
        omega

theorem lt_regCeil {r : Reg} {q : ℕ} (h : q ∈ r.qubits) : q < regCeil r := lt_foldr_ceil r.qubits h

/-- One past the largest qubit name an extendable register owns, active or
reserved. Sign extension writes reserve bits, so the reserve must be counted.
-/
def extCeil (e : ExtReg) : ℕ := max (regCeil e.active) (regCeil e.reserve)

theorem lt_extCeil_active {e : ExtReg} {q : ℕ} (h : q ∈ e.active.qubits) : q < extCeil e :=
  lt_of_lt_of_le (lt_regCeil h) (le_max_left _ _)

theorem lt_extCeil_reserve {e : ExtReg} {q : ℕ} (h : q ∈ e.reserve.qubits) : q < extCeil e :=
  lt_of_lt_of_le (lt_regCeil h) (le_max_right _ _)

theorem lt_extCeil_newBits {e : ExtReg} {n q : ℕ} (h : q ∈ (e.newBits n).qubits) :
    q < extCeil e :=
  lt_extCeil_reserve (List.mem_of_mem_take h)

/-- One past the largest qubit a low gate touches. -/
def maxQubit : LowGate → ℕ
  | LowGate.id => 0
  | LowGate.seq U V => max (maxQubit U) (maxQubit V)
  | LowGate.adj U => maxQubit U
  | LowGate.H q => q + 1
  | LowGate.X q => q + 1
  | LowGate.Phase q _ => q + 1
  | LowGate.CNOT c t => max (c + 1) (t + 1)
  | LowGate.Toffoli c₁ c₂ t => max (max (c₁ + 1) (c₂ + 1)) (t + 1)
  | LowGate.ShiftL r _ => extCeil r
  | LowGate.ShiftR r _ => extCeil r
  | LowGate.Negate r => extCeil r
  | LowGate.AddScaled dst src _ _ => max (extCeil dst) (extCeil src)
  | LowGate.zeroExtend r _ => extCeil r
  | LowGate.signExtend r _ => extCeil r
  | LowGate.zeroDealloc r _ => extCeil r
  | LowGate.signDealloc r _ => extCeil r
  | LowGate.RadixReverse r _ => regCeil r

/-! ## Stability of `Below` -/

theorem below_mWriteNat {dim : ℕ} {r : Reg} (hr : ∀ q ∈ r.qubits, q < dim) (v : ℕ)
    {b : ModelBasis} (hb : Below dim b) : Below dim (mWriteNat r v b) := by
  intro i hi
  rw [mWriteNat_agree_off r v b i (fun hm => absurd (hr i hm) (by omega))]
  exact hb i hi

theorem below_update {dim q : ℕ} (hq : q < dim) (c : Bool) {b : ModelBasis} (hb : Below dim b) :
    Below dim (Function.update b q c) := by
  intro i hi
  rw [Function.update_of_ne (by omega)]
  exact hb i hi

/-- A permutation of the basis that preserves "uses only qubits `< dim`" in both
directions. This is exactly what makes it restrict to `Fin (2 ^ dim)`. -/
structure BelowStable (dim : ℕ) (σ : Equiv.Perm ModelBasis) : Prop where
  fwd : ∀ b, Below dim b → Below dim (σ b)
  bwd : ∀ b, Below dim b → Below dim (σ.symm b)

/-! ## Permutation matrices -/

/-- A basis permutation, restricted to indices. -/
def permIdx (dim : ℕ) (σ : Equiv.Perm ModelBasis) (k : Fin (2 ^ dim)) : Fin (2 ^ dim) :=
  basisIdx dim (σ (idxBasis dim k))

theorem permIdx_comp {dim : ℕ} {σ : Equiv.Perm ModelBasis} (h : BelowStable dim σ)
    (k : Fin (2 ^ dim)) : permIdx dim σ.symm (permIdx dim σ k) = k := by
  rw [permIdx, permIdx, idxBasis_basisIdx (h.fwd _ (idxBasis_below dim k)),
    Equiv.symm_apply_apply, basisIdx_idxBasis]

theorem permIdx_comp' {dim : ℕ} {σ : Equiv.Perm ModelBasis} (h : BelowStable dim σ)
    (k : Fin (2 ^ dim)) : permIdx dim σ (permIdx dim σ.symm k) = k := by
  rw [permIdx, permIdx, idxBasis_basisIdx (h.bwd _ (idxBasis_below dim k)),
    Equiv.apply_symm_apply, basisIdx_idxBasis]

/-- The induced permutation of `Fin (2 ^ dim)`. -/
def permFin {dim : ℕ} (σ : Equiv.Perm ModelBasis) (h : BelowStable dim σ) :
    Equiv.Perm (Fin (2 ^ dim)) where
  toFun := permIdx dim σ
  invFun := permIdx dim σ.symm
  left_inv := permIdx_comp h
  right_inv := permIdx_comp' h

theorem permIdx_injective {dim : ℕ} {σ : Equiv.Perm ModelBasis} (h : BelowStable dim σ) :
    Function.Injective (permIdx dim σ) := (permFin σ h).injective

/-- The permutation matrix of a basis permutation. -/
def permMatrix (dim : ℕ) (σ : Equiv.Perm ModelBasis) : CSquare (2 ^ dim) :=
  fun y x => if y = permIdx dim σ x then 1 else 0

theorem permMatrix_unitary {dim : ℕ} {σ : Equiv.Perm ModelBasis} (h : BelowStable dim σ) :
    permMatrix dim σ ∈ Matrix.unitaryGroup (Fin (2 ^ dim)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext x x'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ y : Fin (2 ^ dim),
      (star (permMatrix dim σ)) x y * permMatrix dim σ y x'
        = if y = permIdx dim σ x then (if x = x' then 1 else 0) else 0 := by
    intro y
    simp only [Matrix.star_apply, permMatrix]
    by_cases h1 : y = permIdx dim σ x
    · subst h1
      by_cases h2 : x = x'
      · subst h2; simp
      · have : ¬ (permIdx dim σ x = permIdx dim σ x') := fun hc => h2 (permIdx_injective h hc)
        simp [this, h2]
    · simp [h1]
  rw [Finset.sum_congr rfl (fun y _ => hterm y),
    Finset.sum_ite_eq' Finset.univ (permIdx dim σ x) (fun _ => if x = x' then (1:ℂ) else 0),
    ite_eq_left (Finset.mem_univ _)]

/-! ## Diagonal matrices -/

/-- The diagonal matrix of a unit-modulus function of the basis state. -/
noncomputable def diagMatrix (dim : ℕ) (φ : ModelBasis → ℂ) : CSquare (2 ^ dim) :=
  fun y x => if y = x then φ (idxBasis dim x) else 0

theorem diagMatrix_unitary {dim : ℕ} {φ : ModelBasis → ℂ} (hφ : ∀ b, ‖φ b‖ = 1) :
    diagMatrix dim φ ∈ Matrix.unitaryGroup (Fin (2 ^ dim)) ℂ := by
  have hmul : ∀ b, conj (φ b) * φ b = 1 := by
    intro b; rw [RCLike.conj_mul]; norm_cast; rw [hφ b]; norm_num
  rw [Matrix.mem_unitaryGroup_iff']
  ext x x'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ y : Fin (2 ^ dim),
      (star (diagMatrix dim φ)) x y * diagMatrix dim φ y x'
        = if y = x then (if x = x' then 1 else 0) else 0 := by
    intro y
    simp only [Matrix.star_apply, diagMatrix]
    by_cases h1 : y = x
    · subst h1
      by_cases h2 : y = x'
      · subst h2; simp [hmul]
      · simp [h2]
    · simp [h1]
  rw [Finset.sum_congr rfl (fun y _ => hterm y),
    Finset.sum_ite_eq' Finset.univ x (fun _ => if x = x' then (1:ℂ) else 0),
    ite_eq_left (Finset.mem_univ _)]

/-! ## The Hadamard block -/

/-- The index obtained by forcing qubit `q` to `c`. -/
def bitIdx (dim q : ℕ) (c : Bool) (k : Fin (2 ^ dim)) : Fin (2 ^ dim) :=
  basisIdx dim (Function.update (idxBasis dim k) q c)

theorem idxBasis_bitIdx {dim q : ℕ} (hq : q < dim) (c : Bool) (k : Fin (2 ^ dim)) :
    idxBasis dim (bitIdx dim q c k) = Function.update (idxBasis dim k) q c :=
  idxBasis_basisIdx (below_update hq c (idxBasis_below dim k))

theorem bitIdx_bit {dim q : ℕ} (hq : q < dim) (c : Bool) (k : Fin (2 ^ dim)) :
    idxBasis dim (bitIdx dim q c k) q = c := by
  rw [idxBasis_bitIdx hq]; simp

theorem bitIdx_ne {dim q : ℕ} (hq : q < dim) (k : Fin (2 ^ dim)) :
    bitIdx dim q false k ≠ bitIdx dim q true k := by
  intro hc
  have h0 : idxBasis dim (bitIdx dim q false k) q = false := bitIdx_bit hq false k
  have h1 : idxBasis dim (bitIdx dim q true k) q = true := bitIdx_bit hq true k
  rw [hc, h1] at h0
  exact Bool.noConfusion h0

theorem bitIdx_clear {dim q : ℕ} (hq : q < dim) (c : Bool) (k : Fin (2 ^ dim)) :
    bitIdx dim q false (bitIdx dim q c k) = bitIdx dim q false k := by
  rw [bitIdx, idxBasis_bitIdx hq, Function.update_idem, bitIdx]

@[simp] theorem bitIdx_self {dim q : ℕ} (k : Fin (2 ^ dim)) :
    bitIdx dim q (idxBasis dim k q) k = k := by
  rw [bitIdx, Function.update_eq_self, basisIdx_idxBasis]

/-- Agreeing off qubit `q` means being one of the two indices over the cleared
one. This is what makes the Hadamard column have exactly two entries. -/
theorem eq_bitIdx_of_clear_eq {dim q : ℕ} (hq : q < dim) {y k : Fin (2 ^ dim)}
    (h : bitIdx dim q false y = bitIdx dim q false k) :
    y = bitIdx dim q (idxBasis dim y q) k := by
  have hb : Function.update (idxBasis dim y) q false
      = Function.update (idxBasis dim k) q false := by
    rw [← idxBasis_bitIdx hq false y, ← idxBasis_bitIdx hq false k, h]
  rw [bitIdx, ← basisIdx_idxBasis dim y]
  congr 1
  funext i
  by_cases hi : i = q
  · subst hi; simp
  · rw [Function.update_of_ne hi]
    have := congrArg (fun f => f i) hb
    simpa [Function.update_of_ne hi] using this

/-- The Hadamard matrix on qubit `q`, as `(-1)^(y_q x_q)/√2` on indices agreeing
off `q`. These are the same entries `Standard/Blocks.lean` gives `blockLift`. -/
noncomputable def hMatrix (dim q : ℕ) : CSquare (2 ^ dim) := fun y x =>
  if bitIdx dim q false y = bitIdx dim q false x then
    (1 / (Real.sqrt 2 : ℝ) : ℂ) * (if idxBasis dim y q && idxBasis dim x q then -1 else 1)
  else 0

/-! ## The denotation -/

/-- **Every low gate as a finite matrix.** -/
noncomputable def denote (dim : ℕ) : LowGate → CSquare (2 ^ dim)
  | LowGate.id => 1
  | LowGate.seq U V => denote dim V * denote dim U
  | LowGate.adj U => (denote dim U)ᴴ
  | LowGate.H q => hMatrix dim q
  | LowGate.X q => permMatrix dim (xPerm q)
  | LowGate.Phase q θ => diagMatrix dim (lowPhaseDiag q θ)
  | LowGate.CNOT c t => permMatrix dim (cnotPerm c t)
  | LowGate.Toffoli c₁ c₂ t => permMatrix dim (toffoliPerm c₁ c₂ t)
  | LowGate.ShiftL r n => permMatrix dim (shiftLPerm r n)
  | LowGate.ShiftR r n => permMatrix dim (shiftRPerm r n)
  | LowGate.Negate r => permMatrix dim (negatePerm r)
  | LowGate.AddScaled dst src neg sh => permMatrix dim (addScaledPerm dst src neg sh)
  | LowGate.zeroExtend _ _ => 1
  | LowGate.signExtend r n => permMatrix dim (signExtendPerm r n)
  | LowGate.zeroDealloc _ _ => 1
  | LowGate.signDealloc r n => permMatrix dim (signExtendPerm r n)
  | LowGate.RadixReverse r m => permMatrix dim (radixReversePerm r m)

/-! ## Each primitive's basis map keeps `Below`

A low gate writes one register. If every qubit of that register is `< dim`,
`mWriteNat_agree_off` says the state is untouched from `dim` up — which is
exactly `Below`-stability, and hence restrictability to `Fin (2 ^ dim)`.
-/

theorem reg_below {r : Reg} {dim : ℕ} (h : regCeil r ≤ dim) : ∀ q ∈ r.qubits, q < dim :=
  fun _ hq => lt_of_lt_of_le (lt_regCeil hq) h

theorem active_below {e : ExtReg} {dim : ℕ} (h : extCeil e ≤ dim) :
    ∀ q ∈ e.active.qubits, q < dim :=
  fun _ hq => lt_of_lt_of_le (lt_extCeil_active hq) h

theorem newBits_below {e : ExtReg} {dim n : ℕ} (h : extCeil e ≤ dim) :
    ∀ q ∈ (e.newBits n).qubits, q < dim :=
  fun _ hq => lt_of_lt_of_le (lt_extCeil_newBits hq) h

theorem below_xBasis {dim q : ℕ} (hq : q < dim) (b : ModelBasis) (hb : Below dim b) :
    Below dim (xBasis q b) :=
  below_mWriteNat (fun q' hq' => by simp at hq'; omega) _ hb

theorem below_cnotBasis {dim ctrl target : ℕ} (ht : target < dim) (b : ModelBasis)
    (hb : Below dim b) : Below dim (cnotBasis (Basis := ModelBasis) ctrl target b) := by
  rw [cnotBasis_eq]
  split
  · exact hb
  · split
    · exact below_update ht _ hb
    · exact hb

theorem below_toffoliBasis {dim c₁ c₂ target : ℕ} (ht : target < dim) (b : ModelBasis)
    (hb : Below dim b) : Below dim (toffoliBasis (Basis := ModelBasis) c₁ c₂ target b) := by
  rw [toffoliBasis_eq]
  split
  · exact hb
  · split
    · exact below_update ht _ hb
    · exact hb

theorem below_negateBasis {dim : ℕ} {r : ExtReg} (hr : ∀ q ∈ r.active.qubits, q < dim)
    (b : ModelBasis) (hb : Below dim b) :
    Below dim (negateBasis (Basis := ModelBasis) r b) :=
  below_mWriteNat hr _ hb

theorem below_signExtendBasis {dim : ℕ} {r : ExtReg} {n : ℕ}
    (hr : ∀ q ∈ (r.newBits n).qubits, q < dim) (b : ModelBasis) (hb : Below dim b) :
    Below dim (signExtendBasis (Basis := ModelBasis) r n b) :=
  below_mWriteNat hr _ hb

theorem below_shiftLBasis {dim : ℕ} {r : ExtReg} (hr : ∀ q ∈ r.active.qubits, q < dim) (n : ℕ)
    (b : ModelBasis) (hb : Below dim b) :
    Below dim (shiftLBasis (Basis := ModelBasis) r n b) := by
  rw [shiftLBasis_eq_raw]
  exact below_mWriteNat hr _ hb

theorem below_shiftRBasis {dim : ℕ} {r : ExtReg} (hr : ∀ q ∈ r.active.qubits, q < dim) (n : ℕ)
    (b : ModelBasis) (hb : Below dim b) :
    Below dim (shiftRBasis (Basis := ModelBasis) r n b) := by
  rw [shiftRBasis_eq_raw]
  exact below_mWriteNat hr _ hb

theorem below_addScaledBasis {dim : ℕ} {dst src : ExtReg}
    (hr : ∀ q ∈ dst.active.qubits, q < dim) (neg : Bool) (sh : ℕ)
    (b : ModelBasis) (hb : Below dim b) :
    Below dim (addScaledBasis (Basis := ModelBasis) dst src neg sh b) := by
  classical
  by_cases hd : ExtReg.ActiveDisjoint dst src
  · rw [addScaledBasis_of_disjoint hd]
    exact below_mWriteNat hr _ hb
  · rw [addScaledBasis_of_not_disjoint hd]
    exact hb

theorem below_radixReverseBasis {dim : ℕ} {r : Reg} (hr : ∀ q ∈ r.qubits, q < dim) (m : ℕ)
    (b : ModelBasis) (hb : Below dim b) :
    Below dim (radixReverseBasis (Basis := ModelBasis) r m b) := by
  by_cases hm : m ≤ regSize r
  · rw [radixReverseBasis_of_le hm]
    exact below_mWriteNat hr _ hb
  · rw [radixReverseBasis_of_gt hm]
    exact hb

/-! ### The inverses of the two non-involutive permutations -/

theorem addScaledPerm_symm_apply (dst src : ExtReg) (negSrc : Bool) (sh : ℕ) (b : ModelBasis) :
    (addScaledPerm dst src negSrc sh).symm b
      = addScaledBasis (Basis := ModelBasis) dst src (!negSrc) sh b := by
  classical
  rw [addScaledPerm]
  by_cases hdisj : ExtReg.ActiveDisjoint dst src
  · rw [dite_eq_left hdisj]; rfl
  · rw [dite_eq_right hdisj, addScaledBasis_of_not_disjoint hdisj]; rfl

theorem radixReversePerm_symm_apply (r : Reg) (m : ℕ) (b : ModelBasis) :
    (radixReversePerm r m).symm b
      = radixReverseBasis (Basis := ModelBasis) r (regSize r - m) b := by
  classical
  rw [radixReversePerm]
  by_cases hm : m ≤ regSize r
  · rw [dite_eq_left hm]; rfl
  · rw [dite_eq_right hm, show regSize r - m = 0 from by omega, radixReverseBasis_zero]; rfl

/-! ### `BelowStable` for every permutation a low gate uses -/

theorem belowStable_xPerm {dim q : ℕ} (hq : q < dim) : BelowStable dim (xPerm q) :=
  ⟨fun b hb => below_xBasis hq b hb, fun b hb => below_xBasis hq b hb⟩

theorem belowStable_cnotPerm {dim ctrl target : ℕ} (ht : target < dim) :
    BelowStable dim (cnotPerm ctrl target) :=
  ⟨fun b hb => below_cnotBasis ht b hb, fun b hb => below_cnotBasis ht b hb⟩

theorem belowStable_toffoliPerm {dim c₁ c₂ target : ℕ} (ht : target < dim) :
    BelowStable dim (toffoliPerm c₁ c₂ target) :=
  ⟨fun b hb => below_toffoliBasis ht b hb, fun b hb => below_toffoliBasis ht b hb⟩

theorem belowStable_negatePerm {dim : ℕ} {r : ExtReg} (hr : ∀ q ∈ r.active.qubits, q < dim) :
    BelowStable dim (negatePerm r) :=
  ⟨fun b hb => below_negateBasis hr b hb, fun b hb => below_negateBasis hr b hb⟩

theorem belowStable_signExtendPerm {dim : ℕ} {r : ExtReg} {n : ℕ}
    (hr : ∀ q ∈ (r.newBits n).qubits, q < dim) : BelowStable dim (signExtendPerm r n) :=
  ⟨fun b hb => below_signExtendBasis hr b hb, fun b hb => below_signExtendBasis hr b hb⟩

theorem belowStable_shiftLPerm {dim : ℕ} {r : ExtReg} (hr : ∀ q ∈ r.active.qubits, q < dim)
    (n : ℕ) : BelowStable dim (shiftLPerm r n) :=
  ⟨fun b hb => below_shiftLBasis hr n b hb, fun b hb => below_shiftRBasis hr n b hb⟩

theorem belowStable_shiftRPerm {dim : ℕ} {r : ExtReg} (hr : ∀ q ∈ r.active.qubits, q < dim)
    (n : ℕ) : BelowStable dim (shiftRPerm r n) :=
  ⟨fun b hb => below_shiftRBasis hr n b hb, fun b hb => below_shiftLBasis hr n b hb⟩

theorem belowStable_addScaledPerm {dim : ℕ} {dst src : ExtReg}
    (hr : ∀ q ∈ dst.active.qubits, q < dim) (neg : Bool) (sh : ℕ) :
    BelowStable dim (addScaledPerm dst src neg sh) :=
  ⟨fun b hb => by rw [addScaledPerm_apply]; exact below_addScaledBasis hr neg sh b hb,
   fun b hb => by rw [addScaledPerm_symm_apply]; exact below_addScaledBasis hr _ sh b hb⟩

theorem belowStable_radixReversePerm {dim : ℕ} {r : Reg} (hr : ∀ q ∈ r.qubits, q < dim) (m : ℕ) :
    BelowStable dim (radixReversePerm r m) :=
  ⟨fun b hb => by rw [radixReversePerm_apply]; exact below_radixReverseBasis hr m b hb,
   fun b hb => by rw [radixReversePerm_symm_apply]; exact below_radixReverseBasis hr _ b hb⟩

/-! ## `denote` is unitary -/

/-- The scalar in front of the Hadamard. -/
noncomputable def hs : ℂ := (1 / (Real.sqrt 2 : ℝ) : ℂ)

theorem hs_mul_hs : hs * hs = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    have : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = 2 := Real.mul_self_sqrt (by norm_num)
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro hz; rw [hz, mul_zero] at h; norm_num at h
  rw [hs, div_mul_div_comm, one_mul, h]

theorem hMatrix_apply (dim q : ℕ) (y x : Fin (2 ^ dim)) :
    hMatrix dim q y x =
      if bitIdx dim q false y = bitIdx dim q false x then
        hs * (if idxBasis dim y q && idxBasis dim x q then -1 else 1)
      else 0 := rfl

theorem hMatrix_eq_zero {dim q : ℕ} (hq : q < dim) {y x : Fin (2 ^ dim)}
    (h0 : y ≠ bitIdx dim q false x) (h1 : y ≠ bitIdx dim q true x) : hMatrix dim q y x = 0 := by
  rw [hMatrix_apply, ite_eq_right]
  intro hc
  have := eq_bitIdx_of_clear_eq hq hc
  cases hy : idxBasis dim y q
  · exact h0 (by rw [this, hy])
  · exact h1 (by rw [this, hy])

theorem hMatrix_false {dim q : ℕ} (hq : q < dim) {x x' : Fin (2 ^ dim)}
    (hcl : bitIdx dim q false x = bitIdx dim q false x') :
    hMatrix dim q (bitIdx dim q false x) x' = hs := by
  rw [hMatrix_apply, ite_eq_left (by rw [bitIdx_clear hq, hcl]), bitIdx_bit hq]
  simp

theorem hMatrix_true {dim q : ℕ} (hq : q < dim) {x x' : Fin (2 ^ dim)}
    (hcl : bitIdx dim q false x = bitIdx dim q false x') :
    hMatrix dim q (bitIdx dim q true x) x'
      = hs * (if idxBasis dim x' q then -1 else 1) := by
  rw [hMatrix_apply, ite_eq_left (by rw [bitIdx_clear hq, hcl]), bitIdx_bit hq]
  cases h : idxBasis dim x' q <;> simp

theorem star_hs : star hs = hs := by
  rw [hs]
  simp [Complex.conj_ofReal]

theorem hMatrix_star (dim q : ℕ) (y x : Fin (2 ^ dim)) :
    star (hMatrix dim q y x) = hMatrix dim q y x := by
  rw [hMatrix_apply]
  split
  · rw [star_mul', star_hs]
    congr 1
    split <;> simp
  · simp

theorem hMatrix_unitary {dim q : ℕ} (hq : q < dim) :
    hMatrix dim q ∈ Matrix.unitaryGroup (Fin (2 ^ dim)) ℂ := by
  classical
  have key1 : ∀ c c' : ℂ, c * c' = 1 → hs * hs + hs * c * (hs * c') = 1 := by
    intro c c' h
    rw [show hs * c * (hs * c') = hs * hs * (c * c') from by ring, h, mul_one, hs_mul_hs]
    norm_num
  have key0 : ∀ c c' : ℂ, c * c' = -1 → hs * hs + hs * c * (hs * c') = 0 := by
    intro c c' h
    rw [show hs * c * (hs * c') = hs * hs * (c * c') from by ring, h]
    ring
  rw [Matrix.mem_unitaryGroup_iff']
  ext x x'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstar : ∀ y, (star (hMatrix dim q)) x y = hMatrix dim q y x := fun y => by
    rw [Matrix.star_apply, hMatrix_star]
  by_cases hcl : bitIdx dim q false x = bitIdx dim q false x'
  · rw [Finset.sum_eq_add_of_mem (bitIdx dim q false x) (bitIdx dim q true x)
      (Finset.mem_univ _) (Finset.mem_univ _) (bitIdx_ne hq x) ?_]
    · rw [hstar, hstar, hMatrix_false hq rfl, hMatrix_false hq hcl,
        hMatrix_true hq rfl, hMatrix_true hq hcl]
      by_cases hxx : x = x'
      · subst hxx
        rw [ite_eq_left rfl]
        refine key1 _ _ ?_
        cases hx : idxBasis dim x q <;> simp
      · rw [ite_eq_right hxx]
        have hbit : idxBasis dim x q ≠ idxBasis dim x' q := fun hb =>
          hxx (by rw [eq_bitIdx_of_clear_eq hq hcl, hb, bitIdx_self])
        refine key0 _ _ ?_
        cases hx : idxBasis dim x q <;> cases hx' : idxBasis dim x' q <;>
          simp_all
    · intro y _ hy
      rw [hstar, hMatrix_eq_zero hq hy.1 hy.2, zero_mul]
  · have hxx : x ≠ x' := fun hc => hcl (by rw [hc])
    rw [ite_eq_right hxx]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [hstar]
    by_cases h0 : bitIdx dim q false y = bitIdx dim q false x
    · rw [hMatrix_apply (y := y) (x := x'), ite_eq_right (fun hc => hcl (h0.symm.trans hc)), mul_zero]
    · rw [hMatrix_apply (y := y) (x := x), ite_eq_right h0, zero_mul]

theorem denote_unitary {dim : ℕ} : ∀ (C : LowGate), maxQubit C ≤ dim →
    denote dim C ∈ Matrix.unitaryGroup (Fin (2 ^ dim)) ℂ
  | LowGate.id, _ => one_mem _
  | LowGate.seq U V, h => by
      refine mul_mem (denote_unitary V ?_) (denote_unitary U ?_)
      · exact le_trans (le_max_right _ _) h
      · exact le_trans (le_max_left _ _) h
  | LowGate.adj U, h => by
      have hU := denote_unitary U h
      show (denote dim U)ᴴ ∈ _
      exact Unitary.star_mem hU
  | LowGate.H q, h => hMatrix_unitary (by simpa [maxQubit] using h)
  | LowGate.X q, h => permMatrix_unitary (belowStable_xPerm (by simpa [maxQubit] using h))
  | LowGate.Phase q θ, _ => diagMatrix_unitary (lowPhaseDiag_norm q θ)
  | LowGate.CNOT c t, h =>
      permMatrix_unitary (belowStable_cnotPerm (by
        simp only [maxQubit] at h; omega))
  | LowGate.Toffoli c₁ c₂ t, h =>
      permMatrix_unitary (belowStable_toffoliPerm (by
        simp only [maxQubit] at h; omega))
  | LowGate.ShiftL r n, h => permMatrix_unitary (belowStable_shiftLPerm (active_below h) n)
  | LowGate.ShiftR r n, h => permMatrix_unitary (belowStable_shiftRPerm (active_below h) n)
  | LowGate.Negate r, h => permMatrix_unitary (belowStable_negatePerm (active_below h))
  | LowGate.AddScaled dst src neg sh, h =>
      permMatrix_unitary (belowStable_addScaledPerm
        (active_below (le_trans (le_max_left _ _) h)) neg sh)
  | LowGate.zeroExtend _ _, _ => one_mem _
  | LowGate.signExtend r n, h => permMatrix_unitary (belowStable_signExtendPerm (newBits_below h))
  | LowGate.zeroDealloc _ _, _ => one_mem _
  | LowGate.signDealloc r n, h => permMatrix_unitary (belowStable_signExtendPerm (newBits_below h))
  | LowGate.RadixReverse r m, h => permMatrix_unitary (belowStable_radixReversePerm (reg_below h) m)

end QuantumLib
end Model
end Shor
