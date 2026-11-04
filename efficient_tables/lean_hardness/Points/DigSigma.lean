import Points.SplitBack

/-!
# Directed Hamiltonian cycles as successor maps

* `sigma_of_dhc`: a directed Hamiltonian cycle gives a successor map along arcs, injective on the
  vertices, under which every vertex reaches every other.
* `dhc_of_cycle`: conversely, a successor map along arcs that returns to a base vertex and reaches
  every vertex from it gives a directed Hamiltonian cycle.
-/

namespace Pts

lemma iterate_period {σ : ℕ → ℕ} {b p : ℕ} (hp : σ^[p] b = b) (j k : ℕ) :
    σ^[j + p * k] b = σ^[j] b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, Function.iterate_add_apply, hp, ih]

theorem dhc_of_cycle (D : Dig) (hn : 2 ≤ D.n) (σ : ℕ → ℕ)
    (hσ : ∀ v < D.n, σ v < D.n ∧ (v, σ v) ∈ D.arcs) {b p : ℕ} (hb : b < D.n) (hp1 : 1 ≤ p)
    (hp : σ^[p] b = b) (hall : ∀ v < D.n, ∃ k, σ^[k] b = v) : DHC D := by
  have hlt : ∀ k, σ^[k] b < D.n := by
    intro k; induction k with
    | zero => simpa
    | succ k ih => rw [Function.iterate_succ_apply']; exact (hσ _ ih).1
  have hred : ∀ k, σ^[k] b = σ^[k % p] b := fun k => by
    conv_lhs => rw [← Nat.mod_add_div k p]
    exact iterate_period hp _ _
  refine dhc_of_sigma D hn σ hσ ?_ ?_
  · intro u hu w hw h
    obtain ⟨i, rfl⟩ := hall u hu
    obtain ⟨j, rfl⟩ := hall w hw
    have h' : σ^[i + 1] b = σ^[j + 1] b := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h]
    calc σ^[i] b = σ^[i + p * 1] b := (iterate_period hp i 1).symm
      _ = σ^[p - 1] (σ^[i + 1] b) := by
          rw [← Function.iterate_add_apply]; congr 1; omega
      _ = σ^[p - 1] (σ^[j + 1] b) := by rw [h']
      _ = σ^[j + p * 1] b := by rw [← Function.iterate_add_apply]; congr 1; omega
      _ = σ^[j] b := iterate_period hp j 1
  · intro v hv
    obtain ⟨k0, hk0⟩ := hall 0 (by omega)
    obtain ⟨j, rfl⟩ := hall v hv
    refine ⟨j + p * k0 - k0, ?_⟩
    have hk : k0 ≤ p * k0 := Nat.le_mul_of_pos_left k0 hp1
    rw [← hk0, ← Function.iterate_add_apply, show j + p * k0 - k0 + k0 = j + p * k0 by omega]
    exact iterate_period hp j k0

/-- The successor map of a directed Hamiltonian cycle. -/
theorem sigma_of_dhc {D : Dig} (h : DHC D) :
    ∃ σ : ℕ → ℕ, (∀ v < D.n, σ v < D.n ∧ (v, σ v) ∈ D.arcs) ∧
      (∀ u < D.n, ∀ w < D.n, σ u = σ w → u = w) ∧
      (∀ u < D.n, ∀ v < D.n, ∃ k, σ^[k] u = v) := by
  obtain ⟨hn, L, hperm, hchn⟩ := h
  have hlen : L.length = D.n := by rw [hperm.length_eq, List.length_range]
  have hnd : L.Nodup := hperm.nodup_iff.mpr List.nodup_range
  have hmem : ∀ v, v ∈ L ↔ v < D.n := fun v => by rw [hperm.mem_iff, List.mem_range]
  have hne : L ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
  have harc := (cyc_iff_index 0 hne).mp hchn
  rw [hlen] at harc
  have hget : ∀ i (hi : i < D.n), L.getD i 0 = L[i]'(hlen ▸ hi) := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  have hgetlt : ∀ i < D.n, L.getD i 0 < D.n := fun i hi => by
    rw [hget i hi, ← hmem]; exact List.getElem_mem _
  have hidx : ∀ v < D.n, L.idxOf v < D.n ∧ L.getD (L.idxOf v) 0 = v := fun v hv => by
    have hv' : v ∈ L := (hmem v).mpr hv
    have hlt : L.idxOf v < L.length := List.idxOf_lt_length_iff.mpr hv'
    refine ⟨by omega, ?_⟩
    rw [hget _ (by omega)]; exact List.getElem_idxOf hlt
  have hidx_get : ∀ i < D.n, L.idxOf (L.getD i 0) = i := fun i hi => by
    rw [hget i hi]; exact hnd.idxOf_getElem i (by omega)
  let σ : ℕ → ℕ := fun v => L.getD ((L.idxOf v + 1) % D.n) 0
  have hpos : 0 < D.n := by omega
  have hstep : ∀ i < D.n, σ (L.getD i 0) = L.getD ((i + 1) % D.n) 0 := fun i hi => by
    simp only [σ, hidx_get i hi]
  have hiter : ∀ i < D.n, ∀ k, σ^[k] (L.getD i 0) = L.getD ((i + k) % D.n) 0 := by
    intro i hi k
    induction k with
    | zero => simp [Nat.mod_eq_of_lt hi]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, hstep _ (Nat.mod_lt _ hpos), succ_mod_eq,
        Nat.add_assoc]
  refine ⟨σ, fun v hv => ?_, fun u hu w hw h => ?_, fun u hu v hv => ?_⟩
  · obtain ⟨hi, hv'⟩ := hidx v hv
    have := harc _ hi
    rw [hv'] at this
    exact ⟨hgetlt _ (Nat.mod_lt _ hpos), this⟩
  · obtain ⟨hiu, hu'⟩ := hidx u hu
    obtain ⟨hiw, hw'⟩ := hidx w hw
    have h1 : (L.idxOf u + 1) % D.n = (L.idxOf w + 1) % D.n := by
      have := congrArg L.idxOf h
      simp only [σ] at this
      rwa [hidx_get _ (Nat.mod_lt _ hpos), hidx_get _ (Nat.mod_lt _ hpos)] at this
    have := succ_mod_inj hiu hiw h1
    rw [← hu', ← hw', this]
  · obtain ⟨hiu, hu'⟩ := hidx u hu
    obtain ⟨hiv, hv'⟩ := hidx v hv
    refine ⟨L.idxOf v + D.n - L.idxOf u, ?_⟩
    have := hiter _ hiu (L.idxOf v + D.n - L.idxOf u)
    rw [hu', show L.idxOf u + (L.idxOf v + D.n - L.idxOf u) = L.idxOf v + D.n * 1
      by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hiv, hv'] at this
    exact this

end Pts
