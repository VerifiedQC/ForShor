import Provider.Ceiling.FinalCeiling

namespace Paper.F3ChargeCeiling
open Paper.F2CatalogTransfer Paper.PPEndToEnd TableGeneration TableGeneration.Operations

/-- charge of a program together with its inverse -/
def pairCost {k : Nat} (p : Prog k) : Nat :=
  chargedCount p + chargedCount (apply_Op_inverse p)

theorem pairCost_append {k : Nat} (p q : Prog k) :
    pairCost (p ++ q) = pairCost p + pairCost q := by
  simp only [pairCost, chargedCount, apply_Op_inverse, List.reverse_append, List.map_append,
    List.sum_append]
  omega

theorem pairCost_nil {k : Nat} : pairCost ([] : Prog k) = 0 := by
  simp [pairCost, chargedCount, apply_Op_inverse]

theorem pairCost_single {k : Nat} (d s : Fin k) (b : Bool) (sh : Nat) :
    pairCost [valid_ops.addScaled d s b sh] = 4 := by
  cases b <;> simp [pairCost, chargedCount, apply_Op_inverse, chargedOp, Operations.inv]

theorem addConstAux_pow {k : Nat} (dst src : Fin k) (neg : Bool) (m : Nat) :
    ∀ fuel shift, m + 1 ≤ fuel →
      addConstAuxFuel dst src neg fuel (2 ^ m) shift =
        [valid_ops.addScaled dst src neg (shift + m)] := by
  induction m with
  | zero =>
    intro fuel shift h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    cases f <;> simp [addConstAuxFuel]
  | succ m ih =>
    intro fuel shift h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have h2 : 2 ^ (m + 1) = (2 ^ (m + 1) - 1) + 1 := by
      have := Nat.one_le_two_pow (n := m + 1); omega
    have h3 := ih f (shift + 1) (by omega)
    rw [h2]
    simp only [addConstAuxFuel]
    rw [← h2]
    have h4 : 2 ^ (m + 1) / 2 = 2 ^ m := by
      rw [pow_succ]; omega
    have h5 : ¬ (2 ^ (m + 1) % 2 = 1) := by
      rw [pow_succ]; omega
    rw [if_neg h5, h4]
    rw [h3]
    congr 2
    omega

theorem pairCost_addConstFrom {k : Nat} (dst src : Fin k) (c : Int)
    (h : c = 0 ∨ ∃ m, c.natAbs = 2 ^ m) :
    pairCost (addConstFrom dst src c) = if c = 0 then 0 else 4 := by
  by_cases hc : c = 0
  · simp [addConstFrom, hc, pairCost_nil]
  · obtain ⟨m, hm⟩ := h.resolve_left hc
    have : addConstFrom dst src c = [valid_ops.addScaled dst src (decide (c < 0)) m] := by
      unfold addConstFrom
      rw [if_neg hc]
      simp only
      rw [hm, addConstAux_pow _ _ _ m _ _ (by
        have := Nat.lt_two_pow_self (n := m); omega)]
      simp
    rw [this, pairCost_single, if_neg hc]

theorem natAbs_pow_two {z : Int} {e : Nat} (h : z.natAbs = 2 ^ e) (j : Nat) :
    (z ^ j).natAbs = 2 ^ (e * j) := by
  rw [Int.natAbs_pow, h, ← pow_mul]

theorem pairCost_computeLocalAux {k : Nat} (hk : 0 < k) (z : Int)
    (hz : z = 0 ∨ ∃ e, z.natAbs = 2 ^ e) (js : List (Fin k)) (hjs : ∀ j ∈ js, j.val ≠ 0) :
    pairCost (computeLocalAux hk z js) = if z = 0 then 0 else 4 * js.length := by
  induction js with
  | nil => simp [computeLocalAux, pairCost_nil]
  | cons j js ih =>
    have hj := hjs j (by simp)
    have ih := ih (fun j hj => hjs j (by simp [hj]))
    simp only [computeLocalAux, pairCost_append]
    by_cases hz0 : z = 0
    · subst hz0
      rw [pairCost_addConstFrom _ _ _ (Or.inl (by simp [hj]))]
      simp [hj] at ih ⊢
      exact ih
    · obtain ⟨e, he⟩ := hz.resolve_left hz0
      rw [pairCost_addConstFrom _ _ _ (Or.inr ⟨_, natAbs_pow_two he _⟩), ih]
      have : z ^ j.val ≠ 0 := pow_ne_zero _ hz0
      simp [this, hz0]
      omega

theorem pairCost_computeFracLocalAux {k : Nat} (hk : 0 < k) (c : Int)
    (hz : c ≠ 0) (he : ∃ e, c.natAbs = 2 ^ e) (js : List (Fin k)) :
    pairCost (computeFracLocalAux hk c js) = 4 * js.length := by
  obtain ⟨e, he⟩ := he
  induction js with
  | nil => simp [computeFracLocalAux, pairCost_nil]
  | cons j js ih =>
    simp only [computeFracLocalAux, pairCost_append]
    have e : fracCoeff (k := k) c j = c ^ (k - 1 - j.val) := rfl
    have : fracCoeff (k := k) c j ≠ 0 := pow_ne_zero _ hz
    rw [e, pairCost_addConstFrom _ _ _ (Or.inr ⟨_, natAbs_pow_two he _⟩), ih]
    rw [e] at this
    simp [this]
    omega

theorem length_filter_ne {k : Nat} (a : Fin k) :
    ((List.finRange k).filter (fun j => decide (j != a))).length = k - 1 := by
  have := (List.nodup_finRange k).erase_eq_filter a
  have e : (fun j : Fin k => decide (j != a)) = (fun x => x != a) := by funext j; by_cases h : j = a <;> simp [h]
  rw [e, ← this, List.length_erase_of_mem (List.mem_finRange a), List.length_finRange]

theorem pairCost_opsForPoint {k : Nat} (hk : 0 < k) (pt : Point)
    (hpt : (∃ z, pt = .int z ∧ (z = 0 ∨ ∃ e, z.natAbs = 2 ^ e)) ∨
           (∃ c, pt = .frac c ∧ (c = 0 ∨ ∃ e, c.natAbs = 2 ^ e))) :
    chargedCount (opsForPointWithProduct hk pt) =
      match pt with
      | .int z => if z = 0 then 0 else 4 * (k - 1)
      | .frac c => if c = 0 then 0 else 4 * (k - 1) := by
  have key : ∀ b : Prog k, chargedCount (b ++ [valid_ops.phaseProduct (finZero hk)] ++
      apply_Op_inverse b) = pairCost b := by
    intro b; simp [pairCost, chargedCount, chargedOp]
  have key2 : ∀ b : Prog k, chargedCount (b ++ [valid_ops.phaseProduct (finLast hk)] ++
      apply_Op_inverse b) = pairCost b := by
    intro b; simp [pairCost, chargedCount, chargedOp]
  rcases hpt with ⟨z, rfl, hz⟩ | ⟨c, rfl, hc⟩
  · simp only [opsForPointWithProduct]
    rw [key, computeLocal, pairCost_computeLocalAux hk z hz]
    · unfold nonzeroFins
      rw [length_filter_ne]
    · intro j hj
      simp [nonzeroFins, finZero, Fin.ext_iff] at hj
      exact hj
  · simp only [opsForPointWithProduct]
    by_cases h0 : c = 0
    · simp [h0, chargedCount, chargedOp]
    · rw [if_neg h0, if_neg h0, key2, computeFracLocal,
        pairCost_computeFracLocalAux hk c h0 (hc.resolve_left h0)]
      unfold nonlastFins
      rw [length_filter_ne]


def ptCost (k : Nat) : Point → Nat
  | .int z => if z = 0 then 0 else 4 * (k - 1)
  | .frac c => if c = 0 then 0 else 4 * (k - 1)

def GoodPt : Point → Prop
  | .int z => z = 0 ∨ ∃ e, z.natAbs = 2 ^ e
  | .frac c => c = 0 ∨ ∃ e, c.natAbs = 2 ^ e

theorem charge_gen {k : Nat} (hk : 0 < k) (pts : List Point) (h : ∀ p ∈ pts, GoodPt p) :
    chargedCount (genOpsWithProduct hk pts) = (pts.map (ptCost k)).sum := by
  induction pts with
  | nil => simp [genOpsWithProduct, chargedCount]
  | cons p ps ih =>
    have h1 := ih (fun q hq => h q (by simp [hq]))
    have hp := h p (by simp)
    have h2 := pairCost_opsForPoint hk p (by
      cases p with
      | int z => exact Or.inl ⟨z, rfl, hp⟩
      | frac c => exact Or.inr ⟨c, rfl, hp⟩)
    have h3 : chargedCount (opsForPointWithProduct hk p ++ genOpsWithProduct hk ps) =
        chargedCount (opsForPointWithProduct hk p) + chargedCount (genOpsWithProduct hk ps) := by
      simp [chargedCount]
    simp only [genOpsWithProduct, h3, h1, h2, List.map_cons, List.sum_cons]
    cases p <;> rfl

theorem f2Point_good (n : Nat) : GoodPt (f2Point n) := by
  match n with
  | 0 => simp [f2Point, GoodPt]
  | 1 => simp [f2Point, GoodPt]
  | 2 => simp only [f2Point, GoodPt]; right; exact ⟨0, rfl⟩
  | 3 => simp only [f2Point, GoodPt]; right; exact ⟨0, rfl⟩
  | n + 4 =>
    simp only [f2Point]
    split <;> simp [GoodPt, Int.natAbs_pow]

theorem ptCost_f2Point (k n : Nat) :
    ptCost k (f2Point n) = if n < 2 then 0 else 4 * (k - 1) := by
  match n with
  | 0 => simp [f2Point, ptCost]
  | 1 => simp [f2Point, ptCost]
  | 2 => simp [f2Point, ptCost]
  | 3 => simp [f2Point, ptCost]
  | n + 4 =>
    simp only [f2Point]
    split <;> simp [ptCost]

theorem sum_range_cost (c : Nat) : ∀ m : Nat,
    ((List.range (m + 2)).map (fun n => if n < 2 then 0 else c)).sum = c * m := by
  intro m
  induction m with
  | zero => simp [List.range_succ]
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 from rfl, List.range_succ, List.map_append, List.sum_append, ih]
    simp [Nat.mul_succ]

theorem groupedLiteralBaseline_charge {K : Nat} (k : Nat) (hk : 2 ≤ k) (hK : k ≤ K) :
    (groupedLiteralBaseline k hk hK).charge = 4 * (k - 1) * (2 * k - 3) := by
  show chargedCount (genOpsWithProduct (positive_of_ge_two hk) (groupedF2Points k)) = _
  have hperm := groupedF2Points_perm k
  have hgood : ∀ p ∈ groupedF2Points k, GoodPt p := by
    intro p hp
    have := hperm.mem_iff.mp hp
    simp only [f2Points, List.mem_map] at this
    obtain ⟨n, _, rfl⟩ := this
    exact f2Point_good n
  rw [charge_gen _ _ hgood, (hperm.map (ptCost k)).sum_eq]
  simp only [f2Points, List.map_map]
  have : (ptCost k ∘ f2Point) = fun n => if n < 2 then 0 else 4 * (k - 1) := by
    funext n; exact ptCost_f2Point k n
  rw [this]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have e1 : 2 * (m + 2) - 1 = (2 * m + 1) + 2 := by omega
  have e2 : 2 * (m + 2) - 3 = 2 * m + 1 := by omega
  rw [e1, e2, sum_range_cost]

theorem groupedLiteralBaseline_charge_le {K : Nat} (k : Nat) (hk : 2 ≤ k) (hK : k ≤ K) :
    (groupedLiteralBaseline k hk hK).charge ≤ 8 * k * k := by
  rw [groupedLiteralBaseline_charge k hk hK]
  have h1 : 4 * (k - 1) ≤ 4 * k := by omega
  have h2 : 2 * k - 3 ≤ 2 * k := by omega
  calc 4 * (k - 1) * (2 * k - 3) ≤ 4 * k * (2 * k) := Nat.mul_le_mul h1 h2
    _ = 8 * k * k := by ring

#print axioms groupedLiteralBaseline_charge
#print axioms groupedLiteralBaseline_charge_le

end Paper.F3ChargeCeiling
