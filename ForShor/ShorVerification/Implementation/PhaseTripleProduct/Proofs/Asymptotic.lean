import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.ExactBoard.ExactBuild
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Math.MasterTheorem
import Mathlib.Analysis.SpecialFunctions.Log.Base
/-!
# PTP asymptotic gate count (analogue of ForShor `GateCount/PhaseProduct`)

For a constant policy (one table `T`, `k` limbs, `3k - 2` points) the exact-board gate count
`ptpGateTotalD` is `O(n ^ α)` with `α = log_k (3k - 2)` (`ptp_gateTotal_bound_core`), and the
constructed circuit of `ptp_gate_full_exact` has that many gates (`ptp_circuit_gateCount_bound_core`).

Structure (as ForShor's `Math/MasterTheorem` + `GateCount/PhaseProduct`):
1. `scanMax_le`, `childWidth_le`, `ptpTightWidth_le`: the width contraction
   `n ↦ n/k + k + D(ops)` (`D` = total shift and add growth of the program);
2. the census recursion `gateTotal_node`: per-level cost `≤ Λ·C + B` plus `3k - 2` children;
3. ForShor's `shifted_master_theorem_exact_family` applied to that recurrence.
-/

namespace Shor
namespace PTP

open Operations

/-! ## 1. Width growth of the scan -/



theorem foldl_max_le_iff (m : ℕ) : ∀ (l : List ℕ) (a : ℕ), l.foldl max a ≤ m ↔ a ≤ m ∧ ∀ x ∈ l, x ≤ m
  | [], a => by simp
  | x :: l, a => by
      simp only [List.foldl_cons, foldl_max_le_iff m l, max_le_iff, List.mem_cons, forall_eq_or_imp]
      tauto

theorem wMax_le_iff (m : ℕ) (w : Widths) : wMax w ≤ m ↔ ∀ x ∈ w, x ≤ m := by
  unfold wMax; rw [foldl_max_le_iff]; simp

theorem le_wMax {w : Widths} {x : ℕ} (h : x ∈ w) : x ≤ wMax w :=
  ((wMax_le_iff _ w).mp le_rfl) x h

theorem wget_le_wMax {k : ℕ} (w : Widths) (i : Fin k) : wget w i ≤ wMax w := by
  unfold wget
  by_cases h : i.1 < w.length
  · rw [List.getD_eq_getElem _ _ h]; exact le_wMax (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _

theorem wMax_set_le (w : Widths) (i v m : ℕ) (hw : wMax w ≤ m) (hv : v ≤ m) :
    wMax (w.set i v) ≤ m := by
  rw [wMax_le_iff] at hw ⊢
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with h | h
  · exact hw x h
  · exact h ▸ hv

theorem wMax_wStep_le {k : ℕ} (w : Widths) (op : valid_ops k) :
    wMax (wStep w op) ≤ wMax w + opGrowth op := by
  cases op with
  | shiftL i n =>
      exact wMax_set_le w _ _ _ (by omega) (by have := wget_le_wMax w i; simp [opGrowth]; omega)
  | shiftR i n =>
      exact wMax_set_le w _ _ _ (by simp [opGrowth]) (by have := wget_le_wMax w i; simp [opGrowth]; omega)
  | negate i => simp [wStep, opGrowth]
  | addScaled d s neg sh =>
      refine wMax_set_le w _ _ _ (by simp [opGrowth]) ?_
      have h1 := wget_le_wMax w d
      have h2 := wget_le_wMax w s
      simp only [opGrowth]; omega
  | phaseProduct i => simp [wStep, opGrowth]

/-- **The scan grows by at most the program's total growth.** -/
theorem scanMax_le {k : ℕ} : ∀ (ops : Prog k) (w : Widths), scanMax w ops ≤ wMax w + growth ops
  | [], w => by simp [scanMax, growth]
  | op :: ops, w => by
      have h1 := wMax_wStep_le w op
      have h2 := scanMax_le ops (wStep w op)
      simp only [scanMax, growth]
      omega


theorem initW_le (nW W k m : ℕ) (hW : W ≤ m) (htop : nW - (k - 1) * W ≤ m) :
    wMax (initW nW W k) ≤ m := by
  rw [wMax_le_iff]
  intro x hx
  unfold initW at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  by_cases h : i.1 + 1 = k <;> simp [h, hW, htop]

theorem top_limb_le (n k : ℕ) (hk : 0 < k) : n - (k - 1) * (n / k) ≤ n / k + (k - 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 : (k' + 1) * (n / (k' + 1)) + n % (k' + 1) = n := Nat.div_add_mod n (k' + 1)
  have h2 : n % (k' + 1) < k' + 1 := Nat.mod_lt n (by omega)
  generalize n / (k' + 1) = q at *
  generalize n % (k' + 1) = r at *
  have h3 : n = k' * q + q + r := by rw [← h1]; ring
  simp only [Nat.add_sub_cancel]
  omega

/-- **Width contraction of the PTP scan**: `childWidth n ops ≤ n / k + k + growth ops`. -/
theorem childWidth_le {k : ℕ} (hk : 0 < k) (n : ℕ) (ops : Prog k) :
    childWidth n ops ≤ n / k + k + growth ops := by
  have hI : wMax (initW n (limbWidth n k) k) ≤ n / k + (k - 1) := by
    apply initW_le
    · rw [limbWidth_eq]; omega
    · rw [limbWidth_eq]; exact top_limb_le n k hk
  have hS := scanMax_le ops (initW n (limbWidth n k) k)
  simp only [childWidth, childWidth3]
  have : limbWidth3 (fun _ => n) k = limbWidth n k := rfl
  rw [this]
  omega

/-- The exact width obeys the same contraction (`ptpTightWidth ≤ childWidth`). -/
theorem ptpTightWidth_le (T : PTPTable) (hT : T.contract = true) {n : ℕ} (hn : 0 < n) :
    ptpTightWidth T n ≤ n / T.k + T.k + growth T.ops := by
  obtain ⟨hk2, _, _⟩ := (PTPTable.contract_iff T).mp hT
  exact (tight_le_childWidth T hT hn).trans (childWidth_le (by omega) n T.ops)

/-- A contract table has `3k - 2` checkpoints. -/
theorem cpCount_eq_pointCount (T : PTPTable) (hT : T.contract = true) :
    cpCount T.ops = 3 * T.k - 2 := by
  obtain ⟨hk2, ⟨hlen, _, _⟩, _⟩ := (PTPTable.contract_iff T).mp hT
  have h1 : cpCount T.ops = T.pts.length := by
    have h := congrArg List.length (children_eq T hT 1 0)
    simp only [List.length_map] at h
    unfold PTPTable.children at h
    rw [cpCount_eq_length] at h
    exact h
  rw [h1, hlen]; rfl


/-! ## 2. The census recursion -/


theorem gateTotal_leaf (P : PTPPolicy) (wd : WidthRule) (n : ℕ)
    (h : P.choose n = none ∨ ∀ T, P.choose n = some T → ¬ wd T n < n) :
    ptpGateTotalD P wd n = 2 * (n * n + n * n * n) + n * n * n := by
  unfold ptpGateTotalD
  rcases h with hc | hc
  · rw [ptpResourcesD, ptpCnotFullD, hc]; simp [leafCensus]
  · rcases hc' : P.choose n with _ | T
    · rw [ptpResourcesD, ptpCnotFullD, hc']; simp [leafCensus]
    · have := hc T hc'
      rw [ptpResourcesD, ptpCnotFullD, hc']; simp [leafCensus, this]

/-- **One level of the census recursion**: linear cost at the child width plus `3k - 2` children. -/
theorem gateTotal_node (P : PTPPolicy) (wd : WidthRule) (n : ℕ) (T : PTPTable)
    (hc : P.choose n = some T) (hlt : wd T n < n) :
    ptpGateTotalD P wd n ≤
      (27 * addCount T.ops + 99 * negCount T.ops + 6) * wd T n + 6 * negCount T.ops +
        cpCount T.ops * ptpGateTotalD P wd (wd T n) := by
  unfold ptpGateTotalD
  rw [ptpResourcesD, ptpCnotFullD, hc]
  simp only [hlt, ↓reduceDIte, nodeCensus]
  set C := wd T n
  set A := addCount T.ops
  set N := negCount T.ops
  set p := cpCount T.ops
  have e1 : A * (2 * C - 6) ≤ A * (2 * C) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have e2 : N * C ≤ N * (3 * C + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have e3 : A * (2 * C - 3) ≤ A * (2 * C) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have e4 : A * (5 * C - 7) ≤ A * (5 * C) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have e5 : C - topLimbWidth n T.k ≤ C := Nat.sub_le _ _
  nlinarith [e1, e2, e3, e4, e5]


/-! ## 3. The exponent and the bound -/


theorem cast_three_k_sub_two {k : ℕ} (hk : 2 ≤ k) : (((3 * k - 2 : ℕ)) : ℝ) = 3 * (k : ℝ) - 2 := by
  have : 2 ≤ 3 * k := by omega
  push_cast [Nat.cast_sub this]; ring

theorem ptpExponent_rpow {k : ℕ} (hk : 2 ≤ k) :
    Real.rpow (k : ℝ) (ptpExponent k) = (((3 * k - 2 : ℕ)) : ℝ) := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  have hq : (0 : ℝ) < (((3 * k - 2 : ℕ)) : ℝ) := by
    rw [cast_three_k_sub_two hk]; linarith
  exact Real.rpow_logb (by linarith) (ne_of_gt hk') hq

theorem one_lt_ptpExponent {k : ℕ} (hk : 2 ≤ k) : 1 < ptpExponent k := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  have hq : (0 : ℝ) < (((3 * k - 2 : ℕ)) : ℝ) := by
    rw [cast_three_k_sub_two hk]; linarith
  unfold ptpExponent
  rw [Real.lt_logb_iff_rpow_lt hk' hq, Real.rpow_one, cast_three_k_sub_two hk]
  linarith


theorem choose_const (t : ℕ) (T : PTPTable) (n : ℕ) :
    (constPTPPolicy t T).choose n = if t ≤ n then some T else none := by
  unfold constPTPPolicy PTPPolicy.choose
  by_cases h : t ≤ n <;> simp [h, List.find?]

/-- **Asymptotic gate count of a constant PTP policy** (any width rule contracting like the PTP
scan): `O(n ^ log_k (3k - 2))`. -/
theorem ptp_gateTotal_bound_core (t : ℕ) (T : PTPTable) (hT : T.contract = true) (wd : WidthRule)
    (hwd : ∀ n, 0 < n → wd T n ≤ n / T.k + T.k + growth T.ops) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (ptpGateTotalD (constPTPPolicy t T) wd n : ℝ) ≤ C * Real.rpow (n : ℝ) (ptpExponent T.k) := by
  obtain ⟨hk2, _, _⟩ := (PTPTable.contract_iff T).mp hT
  set P := constPTPPolicy t T with hP
  set g := growth T.ops with hg
  set k := T.k with hk
  have hcp := cpCount_eq_pointCount T hT
  have hrpow := ptpExponent_rpow hk2
  have hα := one_lt_ptpExponent hk2
  -- the leaf case is a small width
  have hleaf : ∀ n, ¬ (t ≤ n ∧ wd T n < n) → n ≤ t + 2 * k + 2 * g := by
    intro n hn
    by_cases ht : t ≤ n
    · have hge : n ≤ wd T n := by
        by_contra h; exact hn ⟨ht, by omega⟩
      by_cases h0 : n = 0
      · omega
      · have h1 := hwd n (by omega)
        have h2 : n / k ≤ n / 2 := Nat.div_le_div_left hk2 (by norm_num)
        omega
    · omega
  have hnext : ∀ n : ℕ, (if t ≤ n ∧ wd T n < n then wd T n else n) ≤
      (n + k - 1) / k + (t + 3 * k + 3 * g) := by
    intro n
    by_cases hcase : t ≤ n ∧ wd T n < n
    · simp only [hcase, and_self, ↓reduceIte]
      have h1 := hwd n (by omega)
      have h2 : n / k ≤ (n + k - 1) / k := Nat.div_le_div_right (by omega)
      omega
    · simp only [hcase, ↓reduceIte]
      have := hleaf n hcase
      have h3 := Nat.zero_le ((n + k - 1) / k)
      omega
  have hbounded : ∀ N : ℕ, ∃ D : ℕ, ∀ i : ℕ, i ≤ N → ptpGateTotalD P wd i ≤ D := by
    intro N
    exact ⟨∑ i ∈ Finset.range (N + 1), ptpGateTotalD P wd i, fun i hi =>
      Finset.single_le_sum (f := fun i => ptpGateTotalD P wd i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))⟩
  have hstep : ∀ n : ℕ, (if t ≤ n ∧ wd T n < n then wd T n else n) < n → ∀ D : ℕ,
      (∀ j : ℕ, j = (if t ≤ n ∧ wd T n < n then wd T n else n) → ptpGateTotalD P wd j ≤ D) →
      ptpGateTotalD P wd n ≤
        (27 * addCount T.ops + 99 * negCount T.ops + 6) *
            (if t ≤ n ∧ wd T n < n then wd T n else n) + 6 * negCount T.ops + (3 * k - 2) * D := by
    intro n hlt D hD
    by_cases hcase : t ≤ n ∧ wd T n < n
    · simp only [hcase, and_self, ↓reduceIte] at hlt ⊢
      have hc : P.choose n = some T := by rw [hP, choose_const]; simp only [hcase.1, ↓reduceIte]
      have h := gateTotal_node P wd n T hc hcase.2
      rw [hcp] at h
      have hD' := hD (wd T n) (by simp only [hcase.1, hcase.2, and_self, ↓reduceIte])
      have h4 : (3 * k - 2) * ptpGateTotalD P wd (wd T n) ≤ (3 * k - 2) * D :=
        Nat.mul_le_mul_left _ hD'
      exact h.trans (Nat.add_le_add_left h4 _)
    · simp only [hcase, ↓reduceIte] at hlt
      exact absurd hlt (lt_irrefl _)
  obtain ⟨C, hC, hbound⟩ := shifted_master_theorem_exact_family
    (k := k) (q := 3 * k - 2) (c := t + 3 * k + 3 * g)
    (A := 27 * addCount T.ops + 99 * negCount T.ops + 6) (B := 6 * negCount T.ops)
    (α := ptpExponent k) (by omega) hα hrpow
    (fun n => n) (fun n => if t ≤ n ∧ wd T n < n then wd T n else n)
    (fun n => ptpGateTotalD P wd n) hnext hbounded hstep
  refine ⟨C, hC, fun n hn => ?_⟩
  have := hbound n
  simpa [Nat.max_eq_right hn] using this


/-- **The constructed circuit has `O(n ^ log_k (3k - 2))` gates** (exact board, constant policy):
the circuit of `ptp_gate_full_exact` has `totalGates = ptpGateTotalD` and hence the bound. -/
theorem ptp_circuit_gateCount_bound_core {qs : Shor.QSemantics} [Shor.RegEncoding qs.Basis]
    [Shor.LowerGateClass qs] (t : ℕ) (T : PTPTable) (hT : T.contract = true)
    (hP : (constPTPPolicy t T).check = true) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (X : Fin 3 → Shor.ExtReg) (base : ℕ), Good X n base →
      ∃ (W : List ℕ) (G : Shor.Angle → Shor.LowGate),
        PolicyImplX (constPTPPolicy t T) X n W G ∧
        ∀ φ : Shor.Angle,
          ((Shor.LowGate.resources Shor.shorGateResourceModel (G φ)).totalGates : ℝ) ≤
            C * Real.rpow (n : ℝ) (ptpExponent T.k) := by
  obtain ⟨C, hC, hb⟩ := ptp_gateTotal_bound_core t T hT exactRule
    (fun n hn => ptpTightWidth_le T hT hn)
  refine ⟨C, hC, fun n hn X base hG => ?_⟩
  obtain ⟨W, G, hI, _, _, hR⟩ := ptp_gate_full_exact (qs := qs) (constPTPPolicy t T) hP n X base hG
  refine ⟨W, G, hI, fun φ => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := hR φ
  refine le_trans (le_of_eq ?_) (hb n hn)
  unfold Shor.GateResources.totalGates ptpGateTotalD
  dsimp only
  simp only [ptpResourcesX, ptpCnotFullX] at h1 h2 h3 h4 h5
  norm_cast
  omega

end PTP
end Shor
