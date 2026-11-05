import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Values.Semantics
/-!
# Exact PTP widths (`ptpTightWidth`)

The PTP board's width: the least `W` at which every register value of every
state the program reaches (hence every child operand), for every operand
fitting signed `n` bits, fits signed `W` bits. Computed by exact interval
arithmetic over the coefficient rows the program holds: register row `r`
holds `∑ⱼ r j · Lⱼ`, and under the PTP limb split (lower width `W = n / k`,
lower limbs unsigned in `[0, 2^W - 1]`, top limb signed in
`[-2^(t-1), 2^(t-1) - 1]`, `t = n - (k-1) W`) the limbs range independently
over a box, so the row's range is `[rowLo, rowHi]` (coordinatewise min/max)
and both ends are attained (`box_surj`). The three PTP operands of a node all
have width `n` (every PTP board node is balanced: the children of a node are
all at its child width), so their three boxes are the same box and the
three-operand maximum is the one-box maximum.

Provenance: the box, row-range, attainment (`box_surj`) and `leastExp` lemmas
are adapted, with proofs, from the PhaseProduct agent's
`ShorTableOptimization-policy-mirror/.../BandedPolicy/Tight.lean` (2026-10-28;
arity-free; not edited there). Everything that touches the PTP register
machine, the PTP scan, the policy and the semantics is new here.

Results:
* `tight_fits` (soundness), `tight_minimal` (minimality, attained witness),
  `tight_le_iff` (both): `ptpTightWidth T n ≤ W ↔` every reachable value of
  every operand fitting `n` fits `W`;
* `tight_le_childWidth`: `ptpTightWidth T n ≤ childWidth n T.ops` (the PTP scan);
* `evalPhaseD_correct`: the wrapping semantics with any node width
  `wd T n ≥ ptpTightWidth T n` applies `φ · x₀ · x₁ · x₂` at every level;
  `evalPhaseTight_correct` is `wd = ptpTightWidth` (the exact board).
-/

namespace Shor
namespace PTP

open Operations Finset

/-! ## Reachable rows and the trace of the value machine -/

section Reach

variable {k : ℕ}


/-- Every register value of every state of the exact value machine. -/
def traceVals (V : Vals k) : Prog k → List ℤ
  | [] => List.ofFn V
  | op :: ops => List.ofFn V ++ traceVals (vStepF id V op) ops

theorem allFits_iff (C : ℕ) : ∀ (ops : Prog k) (V : Vals k),
    AllFits C V ops ↔ ∀ v ∈ traceVals V ops, Shor.FitsSignedWidth C v
  | [], V => by simp [AllFits, traceVals, List.mem_ofFn]
  | op :: ops, V => by
      simp only [AllFits, traceVals, List.mem_append, List.mem_ofFn, allFits_iff C ops]
      constructor
      · rintro ⟨h1, h2⟩ v (⟨i, rfl⟩ | hv)
        · exact h1 i
        · exact h2 v hv
      · intro h
        exact ⟨fun i => h _ (Or.inl ⟨i, rfl⟩), fun v hv => h v (Or.inr hv)⟩

/-- On a successful run, the trace of the value machine is the row values. -/
theorem trace_reach (L : Fin k → ℤ) : ∀ (ops : Prog k) (σ σ' : State k),
    run? ops σ = some σ' → traceVals (valOf σ L) ops = (reachRows σ ops).map (fun r => regVal r L)
  | [], σ, _, _ => by
      simp only [traceVals, reachRows, List.map_ofFn]; rfl
  | op :: ops, σ, σ', h => by
      simp only [run?] at h
      rcases hs : applyOp? σ op with _ | σ₁
      · rw [hs] at h; cases h
      · rw [hs] at h
        have hv := (applyOp_val σ σ₁ op L hs).1
        simp only [traceVals, reachRows, hs, List.map_append, List.map_ofFn]
        rw [← hv, trace_reach L ops σ₁ σ' h]
        rfl

/-- Checkpoint values are trace values. -/
theorem cp_mem_trace : ∀ (ops : Prog k) (V : Vals k),
    ∀ v ∈ (runF id V ops).1, v ∈ traceVals V ops
  | [], V, v, hv => by simp [runF] at hv
  | op :: ops, V, v, hv => by
      simp only [traceVals, List.mem_append, List.mem_ofFn]
      cases op with
      | phaseProduct i =>
          simp only [runF, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact Or.inl ⟨i, rfl⟩
          · exact Or.inr (cp_mem_trace ops _ v hv)
      | shiftL i n => exact Or.inr (cp_mem_trace ops _ v (by simpa [runF] using hv))
      | shiftR i n => exact Or.inr (cp_mem_trace ops _ v (by simpa [runF] using hv))
      | negate i => exact Or.inr (cp_mem_trace ops _ v (by simpa [runF] using hv))
      | addScaled d s neg sh => exact Or.inr (cp_mem_trace ops _ v (by simpa [runF] using hv))

/-- Wrapping at `C` equals exact when every trace value fits `C`. -/
theorem runF_wrap_eq_of_fits {C : ℕ} : ∀ (ops : Prog k) (V : Vals k),
    AllFits C V ops → runF (Shor.tcWrapInt C) V ops = runF id V ops
  | [], _, _ => rfl
  | op :: ops, V, h => by
      have hnext := h.2
      have hhead : ∀ j, Shor.FitsSignedWidth C (vStepF id V op j) := by
        cases ops with
        | nil => exact hnext
        | cons _ _ => exact hnext.1
      have hstep : vStepF (Shor.tcWrapInt C) V op = vStepF id V op := by
        have key : ∀ (i : Fin k) (v : ℤ), Shor.FitsSignedWidth C (upd V i v i) →
            upd V i (Shor.tcWrapInt C v) = upd V i v := by
          intro i v hv
          have : upd V i v i = v := by simp [upd]
          rw [this] at hv
          rw [Shor.tcWrapInt_eq_of_fits hv.1 hv]
        cases op with
        | shiftL i n => exact key i _ (hhead i)
        | shiftR i n => exact key i _ (hhead i)
        | negate i => exact key i _ (hhead i)
        | addScaled d s neg sh => exact key d _ (hhead d)
        | phaseProduct i => rfl
      have ih := runF_wrap_eq_of_fits ops (vStepF id V op) hnext
      cases op with
      | phaseProduct i =>
          simp only [runF]
          have : vStepF id V (.phaseProduct i) = V := rfl
          rw [this] at ih; rw [ih]
      | shiftL i n => simp only [runF]; rw [hstep, ih]
      | shiftR i n => simp only [runF]; rw [hstep, ih]
      | negate i => simp only [runF]; rw [hstep, ih]
      | addScaled d s neg sh => simp only [runF]; rw [hstep, ih]

end Reach

/-! ## The limb box and row ranges (adapted from the PP agent's Tight.lean) -/

section Box

variable {k : ℕ}








theorem rowLo_eq (n : ℕ) (r : Register k) :
    rowLo k n r = ∑ j, min (r j * limbLo k n j) (r j * limbHi k n j) :=
  (Fin.sum_univ_def _).symm

theorem rowHi_eq (n : ℕ) (r : Register k) :
    rowHi k n r = ∑ j, max (r j * limbLo k n j) (r j * limbHi k n j) :=
  (Fin.sum_univ_def _).symm

theorem le_maxDemand (n : ℕ) : ∀ {rs : List (Register k)} {r : Register k}, r ∈ rs →
    rowDemand k n r ≤ maxDemand k n rs
  | [], _, h => by cases h
  | r' :: rs, r, h => by
      simp only [maxDemand]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (le_maxDemand n h) (le_max_right _ _)

theorem exists_maxDemand (n : ℕ) : ∀ {rs : List (Register k)}, 0 < maxDemand k n rs →
    ∃ r ∈ rs, rowDemand k n r = maxDemand k n rs
  | [], h => by simp [maxDemand] at h
  | r :: rs, h => by
      simp only [maxDemand] at h ⊢
      rcases le_total (rowDemand k n r) (maxDemand k n rs) with hle | hle
      · rw [max_eq_right hle]
        obtain ⟨r', hr', he⟩ := exists_maxDemand n (rs := rs) (by rw [max_eq_right hle] at h; exact h)
        exact ⟨r', List.mem_cons_of_mem _ hr', he⟩
      · exact ⟨r, List.mem_cons_self, (max_eq_left hle).symm⟩

theorem maxDemand_le (n D : ℕ) : ∀ {rs : List (Register k)},
    (∀ r ∈ rs, rowDemand k n r ≤ D) → maxDemand k n rs ≤ D
  | [], _ => Nat.zero_le _
  | r :: rs, h => max_le (h r List.mem_cons_self) (maxDemand_le n D fun r' h' => h r' (by simp [h']))

theorem limbLo_le_limbHi (n : ℕ) (j : Fin k) : limbLo k n j ≤ limbHi k n j := by
  unfold limbLo limbHi
  split
  · have : (1 : ℤ) ≤ 2 ^ (topWidth k n - 1) := one_le_pow₀ (by norm_num)
    linarith
  · have : (1 : ℤ) ≤ 2 ^ (n / k) := one_le_pow₀ (by norm_num)
    linarith

theorem top_offset_lt {k n : ℕ} (hk : 0 < k) (hn : 0 < n) : (k - 1) * (n / k) < n := by
  have := lowerBound_le n (n / k) k hk hn le_rfl
  omega

/-- The limbs of an operand fitting `n` bits lie in the box. -/
theorem limbs_box (hk : 0 < k) {n : ℕ} {x : ℤ} (hx : Shor.FitsSignedWidth n x) (j : Fin k) :
    limbLo k n j ≤ limbsAt k (n / k) x j ∧ limbsAt k (n / k) x j ≤ limbHi k n j := by
  have hn : 0 < n := hx.1
  obtain ⟨-, hlo, hhi⟩ := hx
  unfold Shor.signedMin at hlo
  unfold Shor.signedMax at hhi
  push_cast at hlo hhi
  unfold limbLo limbHi limbsAt limbs
  by_cases hj : (j : ℕ) + 1 = k
  · simp only [hj, ↓reduceIte]
    have hjk : (j : ℕ) = k - 1 := by omega
    rw [hjk, ← pow_mul, Nat.mul_comm (n / k)]
    set m := (k - 1) * (n / k)
    have hm : m < n := top_offset_lt hk hn
    have hp : (0 : ℤ) < 2 ^ m := by positivity
    have hsplit : (2 : ℤ) ^ (n - 1) = 2 ^ (topWidth k n - 1) * 2 ^ m := by
      rw [← pow_add]; congr 1; unfold topWidth; omega
    constructor
    · rw [Int.le_ediv_iff_mul_le hp]; nlinarith
    · have : x / 2 ^ m < 2 ^ (topWidth k n - 1) := by
        rw [Int.ediv_lt_iff_lt_mul hp]; nlinarith
      omega
  · simp only [hj, ↓reduceIte]
    have hB : (0 : ℤ) < 2 ^ (n / k) := by positivity
    have h0 := Int.emod_nonneg (x / (2 ^ (n / k)) ^ (j : ℕ)) (ne_of_gt hB)
    have h1 := Int.emod_lt_of_pos (x / (2 ^ (n / k)) ^ (j : ℕ)) hB
    constructor <;> omega

theorem term_bounds {c l lo hi : ℤ} (h1 : lo ≤ l) (h2 : l ≤ hi) :
    min (c * lo) (c * hi) ≤ c * l ∧ c * l ≤ max (c * lo) (c * hi) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h1 hc),
      le_trans (mul_le_mul_of_nonneg_left h2 hc) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left h2 hc),
      le_trans (mul_le_mul_of_nonpos_left h1 hc) (le_max_left _ _)⟩

/-- **Interval soundness.** -/
theorem row_bounds (n : ℕ) (r : Register k) {L : Fin k → ℤ}
    (hL : ∀ j, limbLo k n j ≤ L j ∧ L j ≤ limbHi k n j) :
    rowLo k n r ≤ regVal r L ∧ regVal r L ≤ rowHi k n r := by
  rw [rowLo_eq, rowHi_eq]
  unfold regVal
  exact ⟨Finset.sum_le_sum fun j _ => (term_bounds (c := r j) (hL j).1 (hL j).2).1,
    Finset.sum_le_sum fun j _ => (term_bounds (c := r j) (hL j).1 (hL j).2).2⟩

theorem fits_of_demand {W : ℕ} {z lo hi : ℤ} (hW : 0 < W) (hlo : lo ≤ z) (hhi : z ≤ hi)
    (hd : max (-lo).toNat (hi + 1).toNat ≤ 2 ^ (W - 1)) : Shor.FitsSignedWidth W z := by
  have h1 : (-lo).toNat ≤ 2 ^ (W - 1) := le_trans (le_max_left _ _) hd
  have h2 : (hi + 1).toNat ≤ 2 ^ (W - 1) := le_trans (le_max_right _ _) hd
  have e1 := Int.self_le_toNat (-lo)
  have e2 := Int.self_le_toNat (hi + 1)
  have c1 : ((-lo).toNat : ℤ) ≤ ((2 ^ (W - 1) : ℕ) : ℤ) := by exact_mod_cast h1
  have c2 : ((hi + 1).toNat : ℤ) ≤ ((2 ^ (W - 1) : ℕ) : ℤ) := by exact_mod_cast h2
  refine ⟨hW, ?_, ?_⟩
  · unfold Shor.signedMin; omega
  · unfold Shor.signedMax; omega

/-- The corner of the box at which row `r` is largest. -/
def cornerHi (k n : ℕ) (r : Register k) : Fin k → ℤ :=
  fun j => if 0 ≤ r j then limbHi k n j else limbLo k n j

/-- The corner of the box at which row `r` is least. -/
def cornerLo (k n : ℕ) (r : Register k) : Fin k → ℤ :=
  fun j => if 0 ≤ r j then limbLo k n j else limbHi k n j

theorem cornerHi_box (n : ℕ) (r : Register k) (j : Fin k) :
    limbLo k n j ≤ cornerHi k n r j ∧ cornerHi k n r j ≤ limbHi k n j := by
  have := limbLo_le_limbHi (k := k) n j
  unfold cornerHi; split <;> constructor <;> omega

theorem cornerLo_box (n : ℕ) (r : Register k) (j : Fin k) :
    limbLo k n j ≤ cornerLo k n r j ∧ cornerLo k n r j ≤ limbHi k n j := by
  have := limbLo_le_limbHi (k := k) n j
  unfold cornerLo; split <;> constructor <;> omega

theorem regVal_cornerHi (n : ℕ) (r : Register k) : regVal r (cornerHi k n r) = rowHi k n r := by
  rw [rowHi_eq]
  unfold regVal
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle := limbLo_le_limbHi (k := k) n j
  unfold cornerHi
  split
  · rename_i h; exact (max_eq_right (mul_le_mul_of_nonneg_left hle h)).symm
  · rename_i h; exact (max_eq_left (mul_le_mul_of_nonpos_left hle (by omega))).symm

theorem regVal_cornerLo (n : ℕ) (r : Register k) : regVal r (cornerLo k n r) = rowLo k n r := by
  rw [rowLo_eq]
  unfold regVal
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle := limbLo_le_limbHi (k := k) n j
  unfold cornerLo
  split
  · rename_i h; exact (min_eq_left (mul_le_mul_of_nonneg_left hle h)).symm
  · rename_i h; exact (min_eq_right (mul_le_mul_of_nonpos_left hle (by omega))).symm

end Box

/-! ## Attainment (adapted from the PP agent's Tight.lean) -/

section Attain

theorem digits_lt {B : ℤ} (hB : 0 < B) (w : ℕ → ℤ) :
    ∀ m, (∀ i < m, 0 ≤ w i ∧ w i < B) →
      0 ≤ ∑ i ∈ range m, w i * B ^ i ∧ ∑ i ∈ range m, w i * B ^ i < B ^ m
  | 0, _ => by simp
  | m + 1, h => by
      obtain ⟨ih0, ih1⟩ := digits_lt hB w m fun i hi => h i (by omega)
      obtain ⟨h0, h1⟩ := h m (by omega)
      have hp : 0 < B ^ m := pow_pos hB m
      rw [sum_range_succ, pow_succ]
      constructor
      · nlinarith
      · nlinarith

theorem sum_split (B : ℤ) (w : ℕ → ℤ) (j m : ℕ) :
    ∑ i ∈ range (j + m), w i * B ^ i
      = ∑ i ∈ range j, w i * B ^ i + B ^ j * ∑ i ∈ range m, w (j + i) * B ^ i := by
  rw [sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]; ring

theorem ediv_digits {B : ℤ} (hB : 0 < B) (w : ℕ → ℤ) (j m : ℕ)
    (hlow : ∀ i < j, 0 ≤ w i ∧ w i < B) :
    (∑ i ∈ range (j + m), w i * B ^ i) / B ^ j = ∑ i ∈ range m, w (j + i) * B ^ i := by
  rw [sum_split, Int.add_mul_ediv_left _ _ (pow_pos hB j).ne']
  obtain ⟨h0, h1⟩ := digits_lt hB w j hlow
  rw [Int.ediv_eq_zero_of_lt h0 h1, zero_add]

theorem emod_head {B : ℤ} (_hB : 0 < B) (u : ℕ → ℤ) (m : ℕ) (h0 : 0 ≤ u 0) (h1 : u 0 < B) :
    (∑ i ∈ range (m + 1), u i * B ^ i) % B = u 0 := by
  rw [sum_range_succ']
  have : ∑ i ∈ range m, u (i + 1) * B ^ (i + 1) = B * ∑ i ∈ range m, u (i + 1) * B ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ]; ring
  rw [this, pow_zero, mul_one, add_comm, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt h0 h1

/-- **Attainment.** Every point of the limb box is the limb vector of some
operand fitting `n` signed bits. -/
theorem box_surj {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (v : Fin k → ℤ)
    (hv : ∀ j, limbLo k n j ≤ v j ∧ v j ≤ limbHi k n j) :
    ∃ x, Shor.FitsSignedWidth n x ∧ ∀ j, limbsAt k (n / k) x j = v j := by
  set B : ℤ := 2 ^ (n / k) with hBdef
  have hB : 0 < B := by positivity
  let w : ℕ → ℤ := fun i => if h : i < k then v ⟨i, h⟩ else 0
  have hw : ∀ j : Fin k, w j = v j := fun j => by simp [w, j.2]
  have hlow : ∀ i, i + 1 < k → 0 ≤ w i ∧ w i < B := by
    intro i hi
    have h := hv ⟨i, by omega⟩
    have hne : (⟨i, by omega⟩ : Fin k).val + 1 ≠ k := by simp; omega
    simp only [limbLo, limbHi, hne, ↓reduceIte] at h
    have hik : i < k := by omega
    simp only [w, hik, ↓reduceDIte]
    constructor <;> omega
  refine ⟨∑ i ∈ range k, w i * B ^ i, ?_, fun j => ?_⟩
  · have hsplit := sum_split B w (k - 1) 1
    rw [show k - 1 + 1 = k by omega] at hsplit
    simp only [sum_range_one, pow_zero, mul_one, add_zero] at hsplit
    rw [hsplit]
    obtain ⟨hs0, hs1⟩ := digits_lt hB w (k - 1) fun i hi => hlow i (by omega)
    have ht := hv ⟨k - 1, by omega⟩
    have htop : (⟨k - 1, by omega⟩ : Fin k).val + 1 = k := by simp; omega
    simp only [limbLo, limbHi, htop, ↓reduceIte] at ht
    have hwt : w (k - 1) = v ⟨k - 1, by omega⟩ := by simp [w, show k - 1 < k by omega]
    rw [hwt]
    have hoff := top_offset_lt hk hn
    have hexp : (2 : ℤ) ^ (n - 1) = B ^ (k - 1) * 2 ^ (topWidth k n - 1) := by
      rw [hBdef, ← pow_mul, ← pow_add]
      congr 1
      unfold topWidth
      rw [Nat.mul_comm (n / k) (k - 1)]
      omega
    have hP : 0 < B ^ (k - 1) := pow_pos hB _
    refine ⟨hn, ?_, ?_⟩
    · unfold Shor.signedMin; push_cast; rw [hexp]; nlinarith
    · unfold Shor.signedMax; push_cast; rw [hexp]; nlinarith
  · have hjk : (j : ℕ) + (k - j) = k := by omega
    have hx : ∑ i ∈ range k, w i * B ^ i = ∑ i ∈ range (j + (k - j)), w i * B ^ i := by rw [hjk]
    unfold limbsAt limbs
    rw [hx, ediv_digits hB w j (k - j) fun i hi => hlow i (by omega)]
    split
    · rw [show k - j = 0 + 1 by omega, sum_range_one, pow_zero, mul_one, add_zero, hw]
    · rw [show k - j = (k - j - 1) + 1 by omega,
        emod_head hB (fun i => w (j + i)) _ (hlow j (by omega)).1 (hlow j (by omega)).2]
      simp only [add_zero, hw]

end Attain

/-! ## The exact PTP width -/


theorem leastExp_spec (D : ℕ) : ∀ (f e : ℕ), D ≤ 2 ^ (e + f) → (∀ e' < e, ¬ D ≤ 2 ^ e') →
    D ≤ 2 ^ leastExp D f e ∧ ∀ e' < leastExp D f e, ¬ D ≤ 2 ^ e'
  | 0, e, h, hm => ⟨by simpa [leastExp] using h, hm⟩
  | f + 1, e, h, hm => by
      simp only [leastExp]
      split
      · exact ⟨‹_›, hm⟩
      · rename_i hne
        refine leastExp_spec D f (e + 1) (by rwa [show e + 1 + f = e + (f + 1) by omega]) ?_
        intro e' he'
        rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h' | rfl
        · exact hm e' h'
        · exact hne



theorem ptpTightWidth_spec (T : PTPTable) (n : ℕ) :
    ptpDemand T n ≤ 2 ^ (ptpTightWidth T n - 1) ∧
      ∀ e < ptpTightWidth T n - 1, ¬ ptpDemand T n ≤ 2 ^ e := by
  have h := leastExp_spec (ptpDemand T n) (ptpDemand T n) 0 (by simpa using Nat.lt_two_pow_self.le)
    (fun _ h => absurd h (Nat.not_lt_zero _))
  simpa [ptpTightWidth] using h

theorem ptpTightWidth_pos (T : PTPTable) (n : ℕ) : 0 < ptpTightWidth T n := by
  unfold ptpTightWidth; omega

/-- The trace of one PTP operand at width `n`. -/
def opTrace (T : PTPTable) (n : ℕ) (x : ℤ) : List ℤ :=
  traceVals (limbsAt T.k (limbWidth n T.k) x) T.ops

theorem opTrace_eq (T : PTPTable) (hT : T.contract = true) (n : ℕ) (x : ℤ) :
    opTrace T n x = (reachRows State.start_state T.ops).map
      (fun r => regVal r (limbsAt T.k (n / T.k) x)) := by
  obtain ⟨_, _, hsafe⟩ := (PTPTable.contract_iff T).mp hT
  have hrun := (returnsToStartCheck_iff T.ops State.start_state).mp hsafe.returns_start
  have h := trace_reach (limbsAt T.k (limbWidth n T.k) x) T.ops _ _ hrun
  rw [valOf_start] at h
  unfold opTrace
  rw [h, limbWidth_eq]

/-- **Soundness of the exact width.** For any `W ≥ ptpTightWidth T n` and any
operand fitting `n`, every reachable register value fits `W`. -/
theorem tight_fits (T : PTPTable) (hT : T.contract = true) {n W : ℕ}
    (hW : ptpTightWidth T n ≤ W) (x : ℤ) (hx : Shor.FitsSignedWidth n x) :
    ∀ v ∈ opTrace T n x, Shor.FitsSignedWidth W v := by
  obtain ⟨hk, _, _⟩ := (PTPTable.contract_iff T).mp hT
  intro v hv
  rw [opTrace_eq T hT] at hv
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
  have hd : rowDemand T.k n r ≤ 2 ^ (W - 1) :=
    le_trans (le_maxDemand n hr) (le_trans (ptpTightWidth_spec T n).1
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  obtain ⟨hlo, hhi⟩ := row_bounds n r (limbs_box (by omega) hx)
  exact fits_of_demand (by have := ptpTightWidth_pos T n; omega) hlo hhi hd

/-- **Minimality of the exact width.** At `ptpTightWidth T n - 1` some operand
fitting `n` bits has a reachable register value that does not fit. -/
theorem tight_minimal (T : PTPTable) (hT : T.contract = true) {n : ℕ} (hn : 0 < n) :
    ∃ x, Shor.FitsSignedWidth n x ∧ ∃ v ∈ opTrace T n x,
      ¬ Shor.FitsSignedWidth (ptpTightWidth T n - 1) v := by
  obtain ⟨hk2, _, _⟩ := (PTPTable.contract_iff T).mp hT
  have hk : 0 < T.k := by omega
  obtain ⟨_, hmin⟩ := ptpTightWidth_spec T n
  by_cases he : ptpTightWidth T n - 1 = 0
  · refine ⟨0, ⟨hn, ?_, ?_⟩, ?_⟩
    · simp [Shor.signedMin]
    · simp [Shor.signedMax]
    · rw [opTrace_eq T hT]
      have hne : reachRows State.start_state T.ops ≠ [] := by
        cases T.ops <;> simp [reachRows, List.ofFn_eq_nil_iff] <;> omega
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
      exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, fun h => by rw [he] at h; exact absurd h.1 (Nat.lt_irrefl 0)⟩
  · set e := ptpTightWidth T n - 1 with he'
    have hnot : ¬ ptpDemand T n ≤ 2 ^ (e - 1) := hmin (e - 1) (by omega)
    have hpos : 0 < ptpDemand T n := by
      rcases Nat.eq_zero_or_pos (ptpDemand T n) with h | h
      · rw [h] at hnot; exact absurd (Nat.zero_le _) hnot
      · exact h
    obtain ⟨r, hr, hrd⟩ := exists_maxDemand n hpos
    have hgt : 2 ^ (e - 1) < rowDemand T.k n r := by
      unfold ptpDemand at hnot; rw [← hrd] at hnot; omega
    unfold rowDemand at hgt
    rcases lt_max_iff.mp hgt with hlo | hhi
    · obtain ⟨x, hx, hl⟩ := box_surj hk hn (cornerLo T.k n r) (cornerLo_box n r)
      refine ⟨x, hx, regVal r (limbsAt T.k (n / T.k) x), ?_, fun hf => ?_⟩
      · rw [opTrace_eq T hT]; exact List.mem_map.mpr ⟨r, hr, rfl⟩
      · obtain ⟨-, hf1, -⟩ := hf
        rw [show limbsAt T.k (n / T.k) x = cornerLo T.k n r from funext hl, regVal_cornerLo] at hf1
        unfold Shor.signedMin at hf1
        have := Int.lt_toNat.mp hlo
        push_cast at hf1 this
        omega
    · obtain ⟨x, hx, hl⟩ := box_surj hk hn (cornerHi T.k n r) (cornerHi_box n r)
      refine ⟨x, hx, regVal r (limbsAt T.k (n / T.k) x), ?_, fun hf => ?_⟩
      · rw [opTrace_eq T hT]; exact List.mem_map.mpr ⟨r, hr, rfl⟩
      · obtain ⟨-, -, hf2⟩ := hf
        rw [show limbsAt T.k (n / T.k) x = cornerHi T.k n r from funext hl, regVal_cornerHi] at hf2
        unfold Shor.signedMax at hf2
        have := Int.lt_toNat.mp hhi
        push_cast at hf2 this
        omega

/-- **The exact width is the least width holding every reachable value.** -/
theorem tight_le_iff (T : PTPTable) (hT : T.contract = true) {n : ℕ} (hn : 0 < n) (W : ℕ) :
    ptpTightWidth T n ≤ W ↔
      ∀ x, Shor.FitsSignedWidth n x → ∀ v ∈ opTrace T n x, Shor.FitsSignedWidth W v := by
  refine ⟨fun h x hx => tight_fits T hT h x hx, fun h => ?_⟩
  by_contra hlt
  obtain ⟨x, hx, v, hv, hnf⟩ := tight_minimal T hT hn
  exact hnf (Shor.FitsSignedWidth_mono (by omega) (h x hx v hv))

/-- Rows reached carry the scan bound on any limb vector within the scan's
initial bounds. -/
theorem reach_bounded (T : PTPTable) (hT : T.contract = true) (n : ℕ) (L : Fin T.k → ℤ)
    (hL : ∀ i, |L i| < 2 ^ (wget (initW n (limbWidth n T.k) T.k) i)) :
    ∀ r ∈ reachRows State.start_state T.ops,
      |regVal r L| < 2 ^ scanMax (initW n (limbWidth n T.k) T.k) T.ops := by
  obtain ⟨_, _, hsafe⟩ := (PTPTable.contract_iff T).mp hT
  have hrun := (returnsToStartCheck_iff T.ops State.start_state).mp hsafe.returns_start
  obtain ⟨hex, _⟩ := run_val L T.ops State.start_state State.start_state hrun
  rw [valOf_start] at hex
  have hb := scan_sound T.ops _ L (initW_length _ _ _) hL hex
  have htr := trace_reach L T.ops _ _ hrun
  rw [valOf_start] at htr
  have hall : ∀ (ops : Prog T.k) (V : Vals T.k) (B : ℕ), AllBounded B V ops →
      ∀ v ∈ traceVals V ops, |v| < 2 ^ B := by
    intro ops
    induction ops with
    | nil => intro V B h v hv; simp only [traceVals, List.mem_ofFn] at hv; obtain ⟨i, rfl⟩ := hv; exact h i
    | cons op ops ih =>
        intro V B h v hv
        simp only [traceVals, List.mem_append, List.mem_ofFn] at hv
        rcases hv with ⟨i, rfl⟩ | hv
        · exact h.1 i
        · exact ih _ B h.2 v hv
  intro r hr
  exact hall T.ops L _ hb _ (by rw [htr]; exact List.mem_map.mpr ⟨r, hr, rfl⟩)

/-- Box points meet the PTP scan's initial bounds. -/
theorem box_init (k n : ℕ) (hk : 0 < k) (hn : 0 < n) (L : Fin k → ℤ)
    (hL : ∀ j, limbLo k n j ≤ L j ∧ L j ≤ limbHi k n j) :
    ∀ i, |L i| < 2 ^ (wget (initW n (limbWidth n k) k) i) := by
  intro i
  rw [init_get, limbWidth_eq]
  have h := hL i
  unfold limbLo limbHi at h
  by_cases ht : i.1 + 1 = k
  · simp only [ht, ↓reduceIte]
    simp only [ht, ↓reduceIte] at h
    have hm := top_offset_lt hk hn
    have he : n - (k - 1) * (n / k) = (topWidth k n - 1) + 1 := by unfold topWidth; omega
    rw [he, abs_lt, pow_succ]
    have : (0 : ℤ) < 2 ^ (topWidth k n - 1) := by positivity
    constructor <;> linarith [h.1, h.2]
  · simp only [ht, ↓reduceIte]
    simp only [ht, ↓reduceIte] at h
    rw [abs_lt]; constructor <;> linarith [h.1, h.2]

/-- **The exact width never exceeds the PTP scan.** -/
theorem tight_le_childWidth (T : PTPTable) (hT : T.contract = true) {n : ℕ} (hn : 0 < n) :
    ptpTightWidth T n ≤ childWidth n T.ops := by
  obtain ⟨hk2, _, _⟩ := (PTPTable.contract_iff T).mp hT
  have hk : 0 < T.k := by omega
  set S := scanMax (initW n (limbWidth n T.k) T.k) T.ops
  have hC : S + 1 ≤ childWidth n T.ops := by
    simp only [S, childWidth, childWidth3]
    have : limbWidth3 (fun _ => n) T.k = limbWidth n T.k := rfl
    rw [this]; omega
  have hD : ptpDemand T n ≤ 2 ^ S := by
    apply maxDemand_le
    intro r hr
    have h1 := reach_bounded T hT n _ (box_init T.k n hk hn _ (cornerHi_box n r)) r hr
    have h2 := reach_bounded T hT n _ (box_init T.k n hk hn _ (cornerLo_box n r)) r hr
    rw [regVal_cornerHi] at h1
    rw [regVal_cornerLo] at h2
    have hhi : rowHi T.k n r < 2 ^ S := (abs_lt.mp h1).2
    have hlo : -(2 ^ S : ℤ) < rowLo T.k n r := (abs_lt.mp h2).1
    unfold rowDemand
    apply max_le
    · exact Int.toNat_le.mpr (by push_cast; linarith)
    · exact Int.toNat_le.mpr (by push_cast; linarith)
  have := (ptpTightWidth_spec T n).2
  by_contra hlt
  exact this S (by omega) hD

/-! ## Policy semantics at a declared node width -/

namespace PTPPolicy

/-- Wrapping PTP semantics where the node at width `n` with table `T` runs at
working width `wd T n` and its children are at that width. -/
noncomputable def evalPhaseD (P : PTPPolicy) (wd : PTPTable → ℕ → ℕ) (n : ℕ) (φ : ℚ)
    (x : Fin 3 → ℤ) : ℚ :=
  match P.choose n with
  | none => φ * x 0 * x 1 * x 2
  | some T =>
      if _h : wd T n < n then
        ∑ t : Fin T.pts.length,
          P.evalPhaseD wd (wd T n) (φ * T.coeff n t)
            (fun s => (T.children (Shor.tcWrapInt (wd T n)) n (x s)).getD t 0)
      else φ * x 0 * x 1 * x 2
termination_by n

/-- The exact board: every node at its exact width. -/
noncomputable def evalPhaseTight (P : PTPPolicy) : ℕ → ℚ → (Fin 3 → ℤ) → ℚ :=
  P.evalPhaseD fun T n => ptpTightWidth T n

def chainFuelX (P : PTPPolicy) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, n =>
      match P.choose n with
      | none => true
      | some T => decide (ptpTightWidth T n < n) && chainFuelX P f (ptpTightWidth T n)

/-- Every band selected on the exact-width recursion from `n` contracts. -/
def chainContractsX (P : PTPPolicy) (n : ℕ) : Bool := chainFuelX P (n + 1) n



end PTPPolicy

/-- **Soundness at every level, any width at least exact.** For a checked
policy and any node-width function `wd` with `ptpTightWidth T n ≤ wd T n` for
every band table, the wrapping semantics applies `φ · x₀ · x₁ · x₂` on operands
fitting signed `n` bits, at every `n`. -/
theorem evalPhaseD_correct (P : PTPPolicy) (hP : P.check = true) (wd : PTPTable → ℕ → ℕ)
    (hwd : ∀ b ∈ P.bands, ∀ n, ptpTightWidth b.table n ≤ wd b.table n) :
    ∀ (n : ℕ) (φ : ℚ) (x : Fin 3 → ℤ), (∀ s, Shor.FitsSignedWidth n (x s)) →
      P.evalPhaseD wd n φ x = φ * x 0 * x 1 * x 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ x hx
    rw [PTPPolicy.evalPhaseD]
    split
    · rfl
    · rename_i T hc
      obtain ⟨b, hb, rfl⟩ := PTPPolicy.choose_mem hc
      have hT := PTPPolicy.check_tables hP b hb
      split
      · rename_i hlt
        have hfits : ∀ s, AllFits (wd b.table n) (limbsAt b.table.k (limbWidth n b.table.k) (x s))
            b.table.ops := fun s =>
          (allFits_iff _ _ _).mpr (tight_fits b.table hT (hwd b hb n) (x s) (hx s))
        have hW : ∀ s, b.table.children (Shor.tcWrapInt (wd b.table n)) n (x s)
            = b.table.children id n (x s) := fun s => congrArg Prod.fst
          (runF_wrap_eq_of_fits _ _ (hfits s))
        have hfit : ∀ (t : Fin b.table.pts.length) s,
            Shor.FitsSignedWidth (wd b.table n) ((b.table.children id n (x s)).getD t 0) := by
          intro t s
          have hlenC : t.1 < (b.table.children id n (x s)).length := by
            rw [children_eq b.table hT]; simp
          rw [List.getD_eq_getElem _ _ hlenC]
          exact (allFits_iff _ _ _).mp (hfits s) _ (cp_mem_trace _ _ _ (List.getElem_mem hlenC))
        simp_rw [hW]
        rw [← node_identity b.table hT n φ x]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [ih _ hlt _ _ (fun s => hfit t s), Fin.prod_univ_three]
        simp only [children_getD b.table hT]
        ring
      · rfl

/-- **The exact PTP board is correct at every level.** -/
theorem evalPhaseTight_correct (P : PTPPolicy) (hP : P.check = true) :
    ∀ (n : ℕ) (φ : ℚ) (x : Fin 3 → ℤ), (∀ s, Shor.FitsSignedWidth n (x s)) →
      P.evalPhaseTight n φ x = φ * x 0 * x 1 * x 2 :=
  evalPhaseD_correct P hP _ fun _ _ _ => le_rfl

end PTP
end Shor
