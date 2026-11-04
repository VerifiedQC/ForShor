import Points.Cyclic

/-!
# Hamiltonian cycle of `L(H D)` ⇒ directed Hamiltonian cycle (out-degree ≤ 2)

Part 1: the edges of `H D` and which of them contain a given vertex.
-/

namespace Pts

section Edges

variable (D : Dig)

lemma mem_HE {f : Finset ℕ} :
    f ∈ HE D ↔ (∃ v < D.n, f = {vin v, vmid v} ∨ f = {vmid v, vleaf v} ∨ f = {vmid v, vout v}) ∨
      ∃ a ∈ D.arcs, f = arcE a := by
  simp only [HE, List.mem_append, List.mem_flatMap, List.mem_range, gadE, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map]
  constructor
  · rintro (⟨v, hv, h⟩ | ⟨a, ha, rfl⟩)
    · exact Or.inl ⟨v, hv, h⟩
    · exact Or.inr ⟨a, ha, rfl⟩
  · rintro (⟨v, hv, h⟩ | ⟨a, ha, rfl⟩)
    · exact Or.inl ⟨v, hv, h⟩
    · exact Or.inr ⟨a, ha, rfl⟩

lemma card_HE {f : Finset ℕ} (hf : f ∈ HE D) : f.card = 2 := by
  rcases (mem_HE D).mp hf with ⟨v, -, rfl | rfl | rfl⟩ | ⟨a, -, rfl⟩ <;>
    (try unfold arcE) <;> (rw [Finset.card_pair]; simp [vin, vmid, vout, vleaf]) <;> omega

lemma pair_eq_iff {a b c d : ℕ} (hab : a ≠ b) :
    ({a, b} : Finset ℕ) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a ∈ ({c, d} : Finset ℕ) := h ▸ by simp
    have hb : b ∈ ({c, d} : Finset ℕ) := h ▸ by simp
    have hc : c ∈ ({a, b} : Finset ℕ) := h.symm ▸ by simp
    have hd : d ∈ ({a, b} : Finset ℕ) := h.symm ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
    omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

lemma arcE_inj {a b : ℕ × ℕ} (h : arcE a = arcE b) : a = b := by
  unfold arcE at h
  rw [pair_eq_iff (by simp [vout, vin]; omega)] at h
  simp only [vout, vin] at h
  ext <;> omega

/-- The edges containing a leaf. -/
lemma leaf_mem {v : ℕ} {f : Finset ℕ} (hf : f ∈ HE D) (h : vleaf v ∈ f) : f = {vmid v, vleaf v} := by
  rcases (mem_HE D).mp hf with ⟨w, -, rfl | rfl | rfl⟩ | ⟨a, -, rfl⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, vin, vmid, vout, vleaf, arcE] at h ⊢ <;>
    first | omega | (have : w = v := by omega); subst this; rfl

lemma mid_mem {v : ℕ} {f : Finset ℕ} (hf : f ∈ HE D) (h : vmid v ∈ f) :
    f = {vin v, vmid v} ∨ f = {vmid v, vleaf v} ∨ f = {vmid v, vout v} := by
  rcases (mem_HE D).mp hf with ⟨w, -, rfl | rfl | rfl⟩ | ⟨a, -, rfl⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, vin, vmid, vout, vleaf, arcE] at h <;>
    first | omega | (have : w = v := by omega); subst this; simp

lemma out_mem {v : ℕ} {f : Finset ℕ} (hf : f ∈ HE D) (h : vout v ∈ f) :
    f = {vmid v, vout v} ∨ ∃ a ∈ D.arcs, a.1 = v ∧ f = arcE a := by
  rcases (mem_HE D).mp hf with ⟨w, -, rfl | rfl | rfl⟩ | ⟨a, ha, rfl⟩
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton, vin, vmid, vout, vleaf, arcE] at h
  · omega
  · omega
  · left; have : w = v := by omega
    subst this; rfl
  · right; exact ⟨a, ha, by omega, rfl⟩

lemma in_mem {v : ℕ} {f : Finset ℕ} (hf : f ∈ HE D) (h : vin v ∈ f) :
    f = {vin v, vmid v} ∨ ∃ a ∈ D.arcs, a.2 = v ∧ f = arcE a := by
  rcases (mem_HE D).mp hf with ⟨w, -, rfl | rfl | rfl⟩ | ⟨a, ha, rfl⟩
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton, vin, vmid, vout, vleaf, arcE] at h
  · left; have : w = v := by omega
    subst this; rfl
  · omega
  · omega
  · right; exact ⟨a, ha, by omega, rfl⟩

lemma length_HE : (HE D).length = 3 * D.n + D.arcs.length := by
  simp [HE, gadE, List.length_flatMap]; ring

end Edges

section Nodup

lemma div4_gad {v : ℕ} {f : Finset ℕ} (hf : f ∈ gadE v) : ∀ x ∈ f, x / 4 = v := by
  simp only [gadE, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> intro x hx <;> simp [vin, vmid, vout, vleaf] at hx <;>
    rcases hx with rfl | rfl <;> omega

lemma HE_nodup (D : Dig) (hD : D.ok) : (HE D).Nodup := by
  unfold HE
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun v _ => ?_, ?_⟩
    · have e1 : ({vin v, vmid v} : Finset ℕ) ≠ {vmid v, vleaf v} := fun h => by
        have := congrArg (vleaf v ∈ ·) h; simp [vin, vmid, vleaf] at this
      have e2 : ({vin v, vmid v} : Finset ℕ) ≠ {vmid v, vout v} := fun h => by
        have := congrArg (vout v ∈ ·) h; simp [vin, vmid, vout] at this
      have e3 : ({vmid v, vleaf v} : Finset ℕ) ≠ {vmid v, vout v} := fun h => by
        have := congrArg (vleaf v ∈ ·) h; simp [vmid, vout, vleaf] at this
      simp [gadE, e1, e2, e3]
    · refine List.Pairwise.imp (fun {v w} hvw => ?_) (List.nodup_iff_pairwise_ne.mp List.nodup_range)
      intro f hfv hfw
      obtain ⟨x, hx⟩ : f.Nonempty := by
        simp only [gadE, List.mem_cons, List.not_mem_nil, or_false] at hfv
        rcases hfv with rfl | rfl | rfl <;> simp
      exact hvw ((div4_gad hfv x hx).symm.trans (div4_gad hfw x hx))
  · exact hD.1.map_on fun a _ b _ h => arcE_inj h
  · intro f hf g hg hfg
    subst hfg
    obtain ⟨v, -, hfv⟩ := List.mem_flatMap.mp hf
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hg
    simp only [gadE, List.mem_cons, List.not_mem_nil, or_false] at hfv
    rcases hfv with h | h | h <;>
      (have h3 := congrArg (vmid v ∈ ·) h) <;>
      simp [arcE, vin, vmid, vout, vleaf] at h3 <;> omega

end Nodup

section Sigma

/-- A successor map that is a single cycle gives a directed Hamiltonian cycle. -/
theorem dhc_of_sigma (D : Dig) (hn : 2 ≤ D.n) (σ : ℕ → ℕ)
    (hσ : ∀ v < D.n, σ v < D.n ∧ (v, σ v) ∈ D.arcs)
    (hinj : ∀ u < D.n, ∀ w < D.n, σ u = σ w → u = w)
    (hall : ∀ v < D.n, ∃ k, σ^[k] 0 = v) : DHC D := by
  have hlt : ∀ k, σ^[k] 0 < D.n := by
    intro k; induction k with
    | zero => simp; omega
    | succ k ih => rw [Function.iterate_succ_apply']; exact (hσ _ ih).1
  -- cancellation
  have hcancel : ∀ a b j, σ^[a + j] 0 = σ^[b + j] 0 → σ^[a] 0 = σ^[b] 0 := by
    intro a b j
    induction j with
    | zero => simp
    | succ j ih =>
      intro h
      rw [← Nat.add_assoc, ← Nat.add_assoc, Function.iterate_succ_apply',
        Function.iterate_succ_apply'] at h
      exact ih (hinj _ (hlt _) _ (hlt _) h)
  -- the first n iterates are distinct
  have hdist : ∀ a < D.n, ∀ b < D.n, σ^[a] 0 = σ^[b] 0 → a = b := by
    intro a ha b hb h
    by_contra hne
    wlog hab : a < b generalizing a b
    · exact this b hb a ha h.symm (Ne.symm hne) (by omega)
    set q := b - a
    have hq : σ^[q] 0 = 0 := by
      have := hcancel q 0 a (by rw [show q + a = b by omega, zero_add]; exact h.symm)
      simpa using this
    have hper : ∀ k, σ^[k] 0 = σ^[k % q] 0 := by
      intro k
      conv_lhs => rw [← Nat.mod_add_div k q]
      induction k / q with
      | zero => simp
      | succ t ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc, Function.iterate_add_apply, hq, ih]
    -- all n vertices are among the first q iterates
    have hsub : Finset.range D.n ⊆ (Finset.range q).image fun k => σ^[k] 0 := by
      intro v hv
      obtain ⟨k, hk⟩ := hall v (Finset.mem_range.mp hv)
      exact Finset.mem_image.mpr ⟨k % q, Finset.mem_range.mpr (Nat.mod_lt _ (by omega)),
        by rw [← hper, hk]⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    have := this.trans Finset.card_image_le
    rw [Finset.card_range] at this
    omega
  -- the first n iterates fill `range n`
  have himg : (Finset.range D.n).image (fun k => σ^[k] 0) = Finset.range D.n := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx; exact Finset.mem_range.mpr (hlt t)
    · rw [Finset.card_image_of_injOn (fun a ha b hb h => hdist a (by simpa using ha) b
        (by simpa using hb) h)]
  have hcover : ∀ v < D.n, ∃ j < D.n, σ^[j] 0 = v := by
    intro v hv
    have : v ∈ (Finset.range D.n).image (fun k => σ^[k] 0) := by rw [himg]; simpa using hv
    obtain ⟨j, hj, h⟩ := Finset.mem_image.mp this
    exact ⟨j, Finset.mem_range.mp hj, h⟩
  have hret : σ^[D.n] 0 = 0 := by
    obtain ⟨j, hj, h⟩ := hcover _ (hlt D.n)
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using h.symm
    · exfalso
      have h' : σ^[(D.n - j) + j] 0 = σ^[0 + j] 0 := by
        rw [show D.n - j + j = D.n by omega, zero_add]; exact h.symm
      have := hdist (D.n - j) (by omega) 0 (by omega) (by simpa using hcancel _ _ _ h')
      omega
  set L := (List.range D.n).map fun k => σ^[k] 0 with hL
  have hLlen : L.length = D.n := by simp [hL]
  have hget : ∀ i < D.n, L.getD i 0 = σ^[i] 0 := by
    intro i hi; simp [hL, List.getD_eq_getElem?_getD, hi]
  have hLnd : L.Nodup := List.Nodup.map_on (fun a ha b hb h =>
    hdist a (List.mem_range.mp ha) b (List.mem_range.mp hb) h) List.nodup_range
  have hLperm : L.Perm (List.range D.n) := by
    apply (List.perm_ext_iff_of_nodup hLnd List.nodup_range).mpr
    intro v
    simp only [hL, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨k, -, rfl⟩; exact hlt k
    · intro hv; obtain ⟨j, hj, h⟩ := hcover v hv; exact ⟨j, hj, h⟩
  refine ⟨hn, L, hLperm, ?_⟩
  have hLne : L ≠ [] := by intro h; rw [h] at hLlen; simp at hLlen; omega
  rw [cyc_iff_index 0 hLne]
  intro i hi
  rw [hLlen] at hi ⊢
  rw [hget i hi, hget _ (Nat.mod_lt _ (by omega))]
  have hnext : σ^[(i + 1) % D.n] 0 = σ (σ^[i] 0) := by
    rcases Nat.lt_or_ge (i + 1) D.n with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, Function.iterate_succ_apply']
    · have h1' : i + 1 = D.n := by omega
      have hs : σ (σ^[i] 0) = σ^[D.n] 0 := by
        rw [← h1']; exact (Function.iterate_succ_apply' σ i 0).symm
      rw [h1', Nat.mod_self, hs, hret]; rfl
  rw [hnext]
  exact (hσ _ (hlt i)).2

end Sigma

section Back

/-- The hypotheses of the converse. -/
structure Ctx (D : Dig) (L : List (Finset ℕ)) : Prop where
  ok : D.ok
  out2 : D.out2
  n2 : 2 ≤ D.n
  perm : L.Perm (HE D)
  cyc : CycAdj L

variable {D : Dig} {L : List (Finset ℕ)} (c : Ctx D L)
include c

lemma Ctx.nd : L.Nodup := c.perm.nodup_iff.mpr (HE_nodup D c.ok)
lemma Ctx.card2 : ∀ f ∈ L, f.card = 2 := fun f hf => card_HE D (c.perm.subset hf)
lemma Ctx.len : L.length = 3 * D.n + D.arcs.length := by rw [c.perm.length_eq, length_HE]
lemma Ctx.m2 : 2 ≤ L.length := by have := c.len; have := c.n2; omega
lemma Ctx.mem (i : ℕ) : eS L i ∈ HE D := c.perm.subset (eS_mem c.m2 i)

lemma Ctx.not_leaf (i v : ℕ) : piv L i ≠ vleaf v := by
  intro hpv
  obtain ⟨h1, h1'⟩ := piv_mem c.cyc c.m2 i
  rw [hpv] at h1 h1'
  exact eS_ne c.nd c.m2 i ((leaf_mem D (c.mem i) h1).trans (leaf_mem D (c.mem (i + 1)) h1').symm)

/-- A transition edge. -/
def IsT (L : List (Finset ℕ)) (f : Finset ℕ) : Prop :=
  ∃ i < L.length, piv L i ≠ piv L (i + 1) ∧ eS L (i + 1) = f

lemma Ctx.trans_no_leaf {f : Finset ℕ} (hf : IsT L f) (v : ℕ) : vleaf v ∉ f := by
  obtain ⟨i, -, hne, rfl⟩ := hf
  rw [eS_trans c.card2 c.cyc c.m2 hne]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨fun h => c.not_leaf i v h.symm, fun h => c.not_leaf (i + 1) v h.symm⟩

open Classical in
/-- Transition edges containing `x`. -/
noncomputable def Im (L : List (Finset ℕ)) (x : ℕ) : Finset (Finset ℕ) :=
  (transAt L x).image fun i => eS L (i + 1)

lemma Ctx.im_card (x : ℕ) : (Im L x).card = 2 * (exits L x).card := by
  classical
  unfold Im
  rw [Finset.card_image_of_injOn, card_trans_at c.nd c.card2 c.cyc c.m2]
  intro i hi j hj h
  simp only [transAt, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
  have h' : eS L ((i + 1) % L.length) = eS L ((j + 1) % L.length) := by rw [eS_mod, eS_mod]; exact h
  exact succ_mod_inj hi.1 hj.1 (eS_inj c.nd c.m2 (Nat.mod_lt _ (by have := c.m2; omega))
    (Nat.mod_lt _ (by have := c.m2; omega)) h')

omit c in
lemma mem_im {L : List (Finset ℕ)} (x : ℕ) (f : Finset ℕ) : f ∈ Im L x ↔ x ∈ f ∧ IsT L f := by
  classical
  simp only [Im, transAt, Finset.mem_image, Finset.mem_filter, Finset.mem_range, IsT]
  constructor
  · rintro ⟨i, ⟨hi, hne, hx⟩, rfl⟩; exact ⟨hx, i, hi, hne, rfl⟩
  · rintro ⟨hx, i, hi, hne, rfl⟩; exact ⟨i, ⟨hi, hne, hx⟩, rfl⟩

lemma Ctx.mid_piv {v : ℕ} (hv : v < D.n) : ∃ j, piv L j = vmid v := by
  have hmem : ({vmid v, vleaf v} : Finset ℕ) ∈ L :=
    c.perm.symm.subset ((mem_HE D).mpr (Or.inl ⟨v, hv, Or.inr (Or.inl rfl)⟩))
  obtain ⟨j, -, hj⟩ := eS_index c.m2 hmem
  refine ⟨j, ?_⟩
  have := (piv_mem c.cyc c.m2 j).1
  rw [hj] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact h
  · exact absurd h (c.not_leaf j v)

lemma Ctx.exit_mid {v : ℕ} (hv : v < D.n) : 0 < (exits L (vmid v)).card := by
  classical
  by_contra h0
  have hempty : exits L (vmid v) = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨j, hj⟩ := c.mid_piv hv
  have hstay : ∀ i, piv L i = vmid v → piv L (i + 1) = vmid v := by
    intro i hpi
    by_contra hne
    have hmem : i % L.length ∈ exits L (vmid v) := by
      simp only [exits, Finset.mem_filter, Finset.mem_range]
      have hlt := Nat.mod_lt i (show 0 < L.length by have := c.m2; omega)
      refine ⟨hlt, by rw [piv_mod]; exact hpi, ?_⟩
      have : piv L (i % L.length + 1) = piv L (i + 1) := by
        rw [← piv_mod (i % L.length + 1), ← piv_mod (i + 1)]
        congr 1; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [this]; exact hne
    rw [hempty] at hmem; simp at hmem
  have hall := piv_propagate c.m2 (· = vmid v) hstay j hj
  -- every edge contains `vmid v`, so there are at most three edges
  have hsub : L.toFinset ⊆ (gadE v).toFinset := by
    intro f hf
    rw [List.mem_toFinset] at hf
    obtain ⟨i, -, rfl⟩ := eS_index c.m2 hf
    have hx : vmid v ∈ eS L i := by
      rw [eS_pred c.m2 i, ← hall (i + L.length - 1)]; exact (piv_mem c.cyc c.m2 _).2
    have := mid_mem D (c.mem i) hx
    simp only [gadE, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have h1 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup c.nd] at h1
  have h3 : (gadE v).toFinset.card ≤ 3 := (List.toFinset_card_le _).trans (by simp [gadE])
  have := c.len; have := c.n2
  omega

lemma Ctx.isT_mem {f : Finset ℕ} (hT : IsT L f) : f ∈ HE D := by
  obtain ⟨i, -, -, rfl⟩ := hT; exact c.mem (i + 1)

omit c in
lemma gad_ne_arc {v : ℕ} {a : ℕ × ℕ} :
    ({vin v, vmid v} : Finset ℕ) ≠ arcE a ∧ ({vmid v, vout v} : Finset ℕ) ≠ arcE a := by
  constructor <;> intro h <;> have := congrArg (vmid v ∈ ·) h <;>
    simp [arcE, vin, vmid, vout] at this <;> omega

/-- Both path edges at `mid v` are transitions. -/
lemma Ctx.mid_trans {v : ℕ} (hv : v < D.n) :
    IsT L {vin v, vmid v} ∧ IsT L {vmid v, vout v} := by
  classical
  have hcard := c.im_card (vmid v)
  have hpos := c.exit_mid hv
  have hne : ({vin v, vmid v} : Finset ℕ) ≠ {vmid v, vout v} := fun h => by
    have := congrArg (vin v ∈ ·) h; simp [vin, vmid, vout] at this
  have hsub : Im L (vmid v) ⊆ {{vin v, vmid v}, {vmid v, vout v}} := by
    intro f hf
    rw [mem_im] at hf
    obtain ⟨hx, hT⟩ := hf
    rcases mid_mem D (c.isT_mem hT) hx with h | h | h
    · simp [h]
    · exact absurd (h ▸ (by simp : vleaf v ∈ ({vmid v, vleaf v} : Finset ℕ))) (c.trans_no_leaf hT v)
    · simp [h]
  have heq : Im L (vmid v) = {{vin v, vmid v}, {vmid v, vout v}} :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hne]; omega)
  have h1 : ({vin v, vmid v} : Finset ℕ) ∈ Im L (vmid v) := by rw [heq]; simp
  have h3 : ({vmid v, vout v} : Finset ℕ) ∈ Im L (vmid v) := by rw [heq]; simp
  exact ⟨((mem_im _ _).mp h1).2, ((mem_im _ _).mp h3).2⟩

open Classical in
/-- Transition out-arcs of `v`. -/
noncomputable def OT (D : Dig) (L : List (Finset ℕ)) (v : ℕ) : Finset (ℕ × ℕ) :=
  D.arcs.toFinset.filter fun a => a.1 = v ∧ IsT L (arcE a)

open Classical in
/-- Transition in-arcs of `v`. -/
noncomputable def IT (D : Dig) (L : List (Finset ℕ)) (v : ℕ) : Finset (ℕ × ℕ) :=
  D.arcs.toFinset.filter fun a => a.2 = v ∧ IsT L (arcE a)

lemma Ctx.out_one {v : ℕ} (hv : v < D.n) : (OT D L v).card = 1 := by
  classical
  have hcard := c.im_card (vout v)
  have hmo : ({vmid v, vout v} : Finset ℕ) ∈ Im L (vout v) :=
    (mem_im _ _).mpr ⟨by simp, (c.mid_trans hv).2⟩
  set outE : Finset (Finset ℕ) := ((D.arcs.filter fun a => a.1 = v).map arcE).toFinset
  have hsub : Im L (vout v) ⊆ insert {vmid v, vout v} outE := by
    intro f hf
    rw [mem_im] at hf
    rcases out_mem D (c.isT_mem hf.2) hf.1 with h | ⟨a, ha, ha1, rfl⟩
    · simp [h]
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simpa using ha1⟩, rfl⟩))
  have hoE : outE.card ≤ 2 := (List.toFinset_card_le _).trans (by simpa using c.out2 v)
  have hle := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hge : 1 ≤ (Im L (vout v)).card := Finset.card_pos.mpr ⟨_, hmo⟩
  have h2 : (Im L (vout v)).card = 2 := by omega
  -- the transition out-arcs are the other element
  have himg : (OT D L v).image arcE = (Im L (vout v)).erase {vmid v, vout v} := by
    ext f
    simp only [OT, Finset.mem_image, Finset.mem_filter, List.mem_toFinset, Finset.mem_erase]
    constructor
    · rintro ⟨a, ⟨ha, ha1, hT⟩, rfl⟩
      exact ⟨(gad_ne_arc (v := v)).2.symm, (mem_im _ _).mpr ⟨by simp [arcE, ha1], hT⟩⟩
    · rintro ⟨hne, hf⟩
      rw [mem_im] at hf
      rcases out_mem D (c.isT_mem hf.2) hf.1 with h | ⟨a, ha, ha1, rfl⟩
      · exact absurd h hne
      · exact ⟨a, ⟨ha, ha1, hf.2⟩, rfl⟩
  rw [← Finset.card_image_of_injective _ (fun a b h => arcE_inj h), himg,
    Finset.card_erase_of_mem hmo, h2]

lemma Ctx.in_pos {v : ℕ} (hv : v < D.n) : 0 < (IT D L v).card := by
  classical
  have hcard := c.im_card (vin v)
  have hmi : ({vin v, vmid v} : Finset ℕ) ∈ Im L (vin v) :=
    (mem_im _ _).mpr ⟨by simp, (c.mid_trans hv).1⟩
  have hge : 2 ≤ (Im L (vin v)).card := by
    have := Finset.card_pos.mpr ⟨_, hmi⟩; omega
  obtain ⟨f, hf, hne⟩ : ∃ f ∈ Im L (vin v), f ≠ {vin v, vmid v} := by
    by_contra h; push Not at h
    have : Im L (vin v) ⊆ {{vin v, vmid v}} := fun f hf => by simp [h f hf]
    have := Finset.card_le_card this; simp at this; omega
  rw [mem_im] at hf
  rcases in_mem D (c.isT_mem hf.2) hf.1 with h | ⟨a, ha, ha2, rfl⟩
  · exact absurd h hne
  · exact Finset.card_pos.mpr ⟨a, by simp [IT, ha, ha2, hf.2]⟩

open Classical in
noncomputable def AT (D : Dig) (L : List (Finset ℕ)) : Finset (ℕ × ℕ) :=
  D.arcs.toFinset.filter fun a => IsT L (arcE a)

lemma Ctx.in_one {v : ℕ} (hv : v < D.n) : (IT D L v).card = 1 := by
  classical
  have hmaps1 : ∀ a ∈ AT D L, a.1 ∈ Finset.range D.n := fun a ha => by
    simp only [AT, Finset.mem_filter, List.mem_toFinset] at ha; simpa using (c.ok.2 a ha.1).1
  have hmaps2 : ∀ a ∈ AT D L, a.2 ∈ Finset.range D.n := fun a ha => by
    simp only [AT, Finset.mem_filter, List.mem_toFinset] at ha; simpa using (c.ok.2 a ha.1).2.1
  have hs1 := Finset.card_eq_sum_card_fiberwise hmaps1
  have hs2 := Finset.card_eq_sum_card_fiberwise hmaps2
  have hf1 : ∀ w, (AT D L).filter (fun a => a.1 = w) = OT D L w := fun w => by
    ext a; simp [AT, OT]; tauto
  have hf2 : ∀ w, (AT D L).filter (fun a => a.2 = w) = IT D L w := fun w => by
    ext a; simp [AT, IT]; tauto
  simp only [hf1, hf2] at hs1 hs2
  rw [Finset.sum_congr rfl (fun w hw => c.out_one (Finset.mem_range.mp hw))] at hs1
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hs1
  by_contra hne
  have hge : 2 ≤ (IT D L v).card := by have := c.in_pos hv; omega
  have : ∑ w ∈ Finset.range D.n, 1 < ∑ w ∈ Finset.range D.n, (IT D L w).card :=
    Finset.sum_lt_sum (fun w hw => c.in_pos (Finset.mem_range.mp hw))
      ⟨v, Finset.mem_range.mpr hv, by omega⟩
  simp at this
  omega

end Back

/-- Iterates of a map of `range n` into itself that is injective there. -/
lemma iter_period {n : ℕ} (hn : 0 < n) (σ : ℕ → ℕ) (hlt : ∀ v < n, σ v < n)
    (hinj : ∀ u < n, ∀ w < n, σ u = σ w → u = w) :
    (∀ k, σ^[k] 0 < n) ∧ (∀ a b j, σ^[a + j] 0 = σ^[b + j] 0 → σ^[a] 0 = σ^[b] 0) ∧
      ∃ p, 0 < p ∧ σ^[p] 0 = 0 := by
  have hit : ∀ k, σ^[k] 0 < n := by
    intro k; induction k with
    | zero => simpa
    | succ k ih => rw [Function.iterate_succ_apply']; exact hlt _ ih
  have hcancel : ∀ a b j, σ^[a + j] 0 = σ^[b + j] 0 → σ^[a] 0 = σ^[b] 0 := by
    intro a b j
    induction j with
    | zero => simp
    | succ j ih =>
      intro h
      rw [← Nat.add_assoc, ← Nat.add_assoc, Function.iterate_succ_apply',
        Function.iterate_succ_apply'] at h
      exact ih (hinj _ (hit _) _ (hit _) h)
  refine ⟨hit, hcancel, ?_⟩
  obtain ⟨a, ha, b, hb, hab, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (n + 1)) (t := Finset.range n) (f := fun k => σ^[k] 0)
    (by simp) (fun k _ => Finset.mem_range.mpr (hit k))
  rcases lt_or_gt_of_ne hab with hlt' | hlt'
  · refine ⟨b - a, by omega, ?_⟩
    have := hcancel (b - a) 0 a (by rw [show b - a + a = b by omega, zero_add]; exact h.symm)
    simpa using this
  · refine ⟨a - b, by omega, ?_⟩
    have := hcancel (a - b) 0 b (by rw [show a - b + b = a by omega, zero_add]; exact h)
    simpa using this

/-- **The converse.** -/
theorem dhc_of_ehc {D : Dig} (hD : D.ok) (ho : D.out2) (hn : 2 ≤ D.n) (h : EHC (HE D)) : DHC D := by
  classical
  obtain ⟨L, hLp, hcyc⟩ := h
  have c : Ctx D L := ⟨hD, ho, hn, hLp, hcyc⟩
  -- the successor map
  have hσex : ∀ v, ∃ w, v < D.n → (OT D L v = {(v, w)}) := by
    intro v
    by_cases hv : v < D.n
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (c.out_one hv)
      have : a.1 = v := by
        have : a ∈ OT D L v := by rw [ha]; simp
        simp [OT] at this; exact this.2.1
      exact ⟨a.2, fun _ => by rw [ha, ← this]⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose σ hσ using hσex
  have hσmem : ∀ v < D.n, (v, σ v) ∈ OT D L v := fun v hv => by rw [hσ v hv]; simp
  have hσarc : ∀ v < D.n, (v, σ v) ∈ D.arcs := fun v hv => by
    have := hσmem v hv; simp [OT] at this; exact this.1
  have hσlt : ∀ v < D.n, σ v < D.n := fun v hv => (hD.2 _ (hσarc v hv)).2.1
  have hAT : ∀ a ∈ D.arcs, IsT L (arcE a) → a.2 = σ a.1 := by
    intro a ha hT
    have hlt := (hD.2 a ha).1
    have : a ∈ OT D L a.1 := by simp [OT, ha, hT]
    rw [hσ _ hlt] at this
    simp at this
    rw [this]
  have hinj : ∀ u < D.n, ∀ w < D.n, σ u = σ w → u = w := by
    intro u hu w hw h
    have h1 : (u, σ u) ∈ IT D L (σ u) := by
      have := hσmem u hu; simp [OT] at this; simp [IT, this.1, this.2]
    have h3 : (w, σ u) ∈ IT D L (σ u) := by
      have := hσmem w hw; simp [OT] at this; rw [h]; simp [IT, this.1, this.2]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (c.in_one (hσlt u hu))
    rw [ha] at h1 h3
    simp at h1 h3
    have := h1.trans h3.symm
    simpa using congrArg Prod.fst this
  obtain ⟨hit, -, p, hp, hper⟩ := iter_period (by omega) σ hσlt hinj
  have hperk : ∀ k, σ^[k + p] 0 = σ^[k] 0 := fun k => by
    rw [Function.iterate_add_apply, hper]
  have hpred : ∀ u < D.n, ∀ k, σ u = σ^[k] 0 → ∃ k', σ^[k'] 0 = u := by
    intro u hu k h
    refine ⟨k + p - 1, hinj _ (hit _) u hu ?_⟩
    rw [← Function.iterate_succ_apply' σ (k + p - 1), show (k + p - 1).succ = k + p by omega,
      hperk, h]
  -- reachability propagates along the pivot sequence
  let Q : ℕ → Prop := fun x => ∃ k, σ^[k] 0 = x / 4
  have hstep : ∀ i, Q (piv L i) → Q (piv L (i + 1)) := by
    intro i hQ
    by_cases heq : piv L (i + 1) = piv L i
    · rw [heq]; exact hQ
    have hne : piv L i ≠ piv L (i + 1) := Ne.symm heq
    have he := eS_trans c.card2 c.cyc c.m2 hne
    have hT : IsT L (eS L (i + 1)) := ⟨i % L.length, Nat.mod_lt _ (by have := c.m2; omega),
      by rw [piv_mod, piv_succ_mod]; exact hne, eS_succ_mod i⟩
    rcases (mem_HE D).mp (c.mem (i + 1)) with ⟨w, -, hw⟩ | ⟨a, ha, hae⟩
    · -- a gadget edge: both pivots in the same gadget
      have hdiv : ∀ x ∈ eS L (i + 1), x / 4 = w := by
        intro x hx
        rcases hw with hw | hw | hw <;> rw [hw] at hx <;>
          simp [vin, vmid, vout, vleaf] at hx <;> rcases hx with rfl | rfl <;> omega
      have h1 : piv L i ∈ eS L (i + 1) := by rw [he]; simp
      have h3 : piv L (i + 1) ∈ eS L (i + 1) := by rw [he]; simp
      obtain ⟨k, hk⟩ := hQ
      exact ⟨k, by rw [hk, hdiv _ h1, hdiv _ h3]⟩
    · have hσa := hAT a ha (hae ▸ hT)
      have hpair : ({piv L i, piv L (i + 1)} : Finset ℕ) = {vout a.1, vin a.2} := by
        rw [← he, hae]; rfl
      rw [pair_eq_iff hne] at hpair
      have hlt1 := (hD.2 a ha).1
      have e1 : vout a.1 / 4 = a.1 := by simp only [vout]; omega
      have e2 : vin a.2 / 4 = a.2 := by simp only [vin]; omega
      obtain ⟨k, hk⟩ := hQ
      rcases hpair with ⟨h1, h3⟩ | ⟨h1, h3⟩
      · refine ⟨k + 1, ?_⟩
        rw [h3, Function.iterate_succ_apply', hk, h1, e1, e2, hσa]
      · rw [h1, e2] at hk
        obtain ⟨k', hk''⟩ := hpred a.1 hlt1 k (by rw [← hσa, hk])
        exact ⟨k', by rw [hk'', h3, e1]⟩
  obtain ⟨j0, hj0⟩ := c.mid_piv (show 0 < D.n by omega)
  have hQ0 : Q (piv L j0) := ⟨0, by rw [hj0]; simp [vmid]⟩
  have hall := piv_propagate c.m2 Q hstep j0 hQ0
  refine dhc_of_sigma D hn σ (fun v hv => ⟨hσlt v hv, hσarc v hv⟩) hinj (fun v hv => ?_)
  obtain ⟨jv, hjv⟩ := c.mid_piv hv
  obtain ⟨k, hk⟩ := hall jv
  exact ⟨k, by rw [hk, hjv]; simp [vmid]; omega⟩

/-- **The split-and-pendant lemma.** -/
theorem dhc_iff_ehc {D : Dig} (hD : D.ok) (ho : D.out2) (hn : 2 ≤ D.n) : DHC D ↔ EHC (HE D) :=
  ⟨ehc_of_dhc hD, dhc_of_ehc hD ho hn⟩





end Pts
