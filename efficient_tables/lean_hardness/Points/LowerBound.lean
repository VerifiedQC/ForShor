import Points.Gap
import TableGeneration.Metrics

/-!
# The cost lower bound for two registers, and what a cheap schedule looks like

Let `Q` be a set of integers containing `0`, no two of which differ by a `W1` number.
* `run_bound`: any contract-valid schedule (k = 2) that consumes the integer points `O ⊆ Q`
  costs at least `chain 0 O = 5 |O| + Σ cst` over the cyclic sequence `0, O, 0`, where
  `cst x y` is `0` if `x = y`, `2` if `W2 (y − x)`, and `3` otherwise.
* `extract`: if `chain 0 O ≤ 7 |O|`, then `0` is at one end of `O` and the rest of `O` steps
  only by `W2` differences.
-/

namespace Pts

open TableGeneration Operations

/-- The paper's score. -/
def score {k : ℕ} (ops : Prog k) : ℕ :=
  arithmeticOperationCount ops + 5 * parallelPhaseProductLayerCount ops

/-- **Points as input.** The instance supplies `k`, the points and the budget; the contract and
the score are those of ShorTableOptimization. -/
def GenTableOpt (k : ℕ) (pts : List Point) (K : ℕ) : Prop :=
  ∃ hk : 0 < k, pts.Nodup ∧ ∃ (order : List Point) (ops : Prog k), order.Perm pts ∧
    ProgConsumesPtsSafe hk State.start_state ops order ∧ score ops ≤ K

open Classical in
/-- The step cost. -/
noncomputable def cst (x y : ℤ) : ℕ := if x = y then 0 else if W2 (y - x) then 2 else 3

lemma cst_self (x : ℤ) : cst x x = 0 := by simp [cst]
lemma two_le_cst {x y : ℤ} (h : x ≠ y) : 2 ≤ cst x y := by
  unfold cst; rw [if_neg h]; split_ifs <;> omega
lemma W2_of_cst {x y : ℤ} (h : cst x y = 2) : W2 (y - x) := by
  unfold cst at h; split_ifs at h with h1 h2 <;> first | exact h2 | omega
lemma cst_le_three (x y : ℤ) : cst x y ≤ 3 := by unfold cst; split_ifs <;> omega

/-- `5` per point plus the step costs along `a, pts, 0`. -/
noncomputable def chain (a : ℤ) : List ℤ → ℕ
  | [] => cst a 0
  | p :: rest => cst a p + 5 + chain p rest

/-! ### Contract plumbing -/

lemma consumes_nonmarker {k : ℕ} {hk : k > 0} {S : State k} {op : valid_ops k} {ops : Prog k}
    {pts : List Point} (hnm : ∀ i, op ≠ .phaseProduct i)
    (h : progConsumesPts? hk S (op :: ops) pts = true) :
    ∃ S', applyOp? S op = some S' ∧ progConsumesPts? hk S' ops pts = true := by
  have key : progConsumesPts? hk S (op :: ops) pts =
      (match applyOp? S op with
       | none => false
       | some S' => progConsumesPts? hk S' ops pts) := by
    cases op with
    | phaseProduct i => exact absurd rfl (hnm i)
    | _ => rfl
  rw [key] at h
  cases h' : applyOp? S op with
  | none => rw [h'] at h; exact absurd h (by simp)
  | some S' => rw [h'] at h; exact ⟨S', rfl, h⟩

lemma consumes_marker {k : ℕ} {hk : k > 0} {S : State k} {i : Fin k} {ops : Prog k}
    {pts : List Point} (h : progConsumesPts? hk S (.phaseProduct i :: ops) pts = true) :
    ∃ pt rest, pts = pt :: rest ∧ S i = expectedRow pt ∧ progConsumesPts? hk S ops rest = true := by
  cases pts with
  | nil => simp [progConsumesPts?] at h
  | cons pt rest =>
    simp only [progConsumesPts?, Bool.and_eq_true, matchesAt_pointRow_state, regEqExpected,
      List.all_eq_true, List.mem_finRange, decide_eq_true_eq, forall_const] at h
    exact ⟨pt, rest, rfl, funext h.1, h.2⟩

lemma run_cons_of {k : ℕ} {S S' T : State k} {op : valid_ops k} {ops : Prog k}
    (h1 : applyOp? S op = some S') (h2 : run? (op :: ops) S = some T) : run? ops S' = some T := by
  simpa only [run?, h1] using h2

lemma aux_nonmarker {k : ℕ} (b : Bool) {op : valid_ops k} (ops : Prog k)
    (hnm : ∀ i, op ≠ .phaseProduct i) :
    parallelPhaseProductLayerCountAux b (op :: ops) = parallelPhaseProductLayerCountAux false ops := by
  cases op with
  | phaseProduct i => exact absurd rfl (hnm i)
  | _ => rfl

lemma arith_nonmarker {k : ℕ} {op : valid_ops k} (ops : Prog k) (hnm : ∀ i, op ≠ .phaseProduct i) :
    arithmeticOperationCount (op :: ops) = arithmeticOperationCount ops + 1 := by
  cases op with
  | phaseProduct i => exact absurd rfl (hnm i)
  | _ => rfl

lemma start_row0 : (State.start_state : State 2) 0 = row 0 := by
  funext j; rcases fin2_cases j with rfl | rfl <;> simp [State.start_state, row, expectedRow]

/-! ### The run bound -/

section Bound

variable (Q : Set ℤ) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ¬ W1 (y - x)) (h0 : (0 : ℤ) ∈ Q)
include hQ

lemma gap_cost {S Sa : State 2} {C : Coef} {g : ℕ} (hR : Rep S Sa C) (hC : Cls g C)
    (hdet : DetOK Sa) {r r' : Fin 2} {a b : ℤ} (ha : Sa r = row a) (hb : S r' = row b)
    (haQ : a ∈ Q) (hbQ : b ∈ Q) : cst a b ≤ g := by
  by_cases hab : a = b
  · subst hab; rw [cst_self]; omega
  have hn := hQ a haQ b hbQ hab
  obtain ⟨g1, g2⟩ := gap hR hC hdet ha hb
  rcases Nat.lt_or_ge g 2 with hlt | hge
  · exact absurd (g1 (by omega)) hn
  rcases Nat.eq_or_lt_of_le hge with h2 | h3
  · subst h2
    have := g2 rfl
    unfold cst; rw [if_neg hab, if_pos this]
  · exact (cst_le_three a b).trans (by omega)

include h0 in
theorem run_bound : ∀ (ops : Prog 2) (S Sa : State 2) (C : Coef) (g : ℕ) (b : Bool) (r : Fin 2)
    (a : ℤ) (pts : List ℤ),
    Sa r = row a → DetOK Sa → DetOK S → Rep S Sa C → Cls g C → a ∈ Q → (∀ p ∈ pts, p ∈ Q) →
    pts.Nodup → (b = true → g = 0 ∧ a ∉ pts) → Prog.wellFormed? ops = true →
    progConsumesPts? (by decide : 2 > 0) S ops (pts.map Point.int) = true →
    run? ops S = some State.start_state →
    chain a pts ≤ arithmeticOperationCount ops + 5 * parallelPhaseProductLayerCountAux b ops + g
  | [], S, Sa, C, g, b, r, a, pts, ha, hdet, _, hR, hC, haQ, _, _, _, _, hcons, hrun => by
    cases pts with
    | cons p pts => simp [progConsumesPts?] at hcons
    | nil =>
      simp only [run?, Option.some.injEq] at hrun
      subst hrun
      have := gap_cost Q hQ hR hC hdet ha start_row0 haQ h0
      simpa [chain, arithmeticOperationCount, parallelPhaseProductLayerCountAux] using this
  | op :: rest, S, Sa, C, g, b, r, a, pts, ha, hdet, hdetS, hR, hC, haQ, hpQ, hnd, hb, hwf,
      hcons, hrun => by
    simp only [Prog.wellFormed?, Bool.and_eq_true] at hwf
    by_cases hm : ∃ i, op = .phaseProduct i
    · obtain ⟨i, rfl⟩ := hm
      obtain ⟨pt, rest', hpts, hrow, hcons'⟩ := consumes_marker hcons
      cases pts with
      | nil => simp at hpts
      | cons p pts' =>
      simp only [List.map_cons, List.cons.injEq] at hpts
      obtain ⟨hpt, hrest⟩ := hpts
      subst hpt; subst hrest
      have hrow' : S i = row p := hrow
      have hrun' : run? rest S = some State.start_state := by
        simpa only [run?, applyOp?] using hrun
      have hpQ' : p ∈ Q := hpQ p (by simp)
      have hgap := gap_cost Q hQ hR hC hdet ha hrow' haQ hpQ'
      have hnd' := List.nodup_cons.mp hnd
      have ih := run_bound rest S S C0 0 true i p pts' hrow' hdetS hdetS (rep_self S) rfl hpQ'
        (fun q hq => hpQ q (by simp [hq])) hnd'.2 (fun _ => ⟨rfl, hnd'.1⟩) hwf.2 hcons' hrun'
      cases b with
      | false =>
        simp only [chain, arithmeticOperationCount, parallelPhaseProductLayerCountAux]
        simp only [ite_false, Bool.false_eq_true] at ih ⊢
        omega
      | true =>
        obtain ⟨hg0, hanot⟩ := hb rfl
        have hne : a ≠ p := fun h => hanot (by simp [h])
        have := two_le_cst hne
        omega
    · push Not at hm
      have hnm : ∀ i, op ≠ .phaseProduct i := hm
      obtain ⟨S', happ, hcons'⟩ := consumes_nonmarker hnm hcons
      have hrun' := run_cons_of happ hrun
      have ih := run_bound rest S' Sa (updC op C) (g + 1) false r a pts ha hdet
        (detOK_apply hwf.1 happ hdetS) (rep_apply happ hR) (cls_step hwf.1 hC) haQ hpQ hnd
        (by simp) hwf.2 hcons' hrun'
      rw [arith_nonmarker rest hnm, aux_nonmarker b rest hnm]
      omega

end Bound

/-! ### Cheap schedules step by `W2` -/

/-- Consecutive entries differ by `W2` numbers. -/
def StepsW2 : List ℤ → Prop
  | x :: y :: rest => W2 (y - x) ∧ StepsW2 (y :: rest)
  | _ => True

lemma StepsW2.tail {x : ℤ} {L : List ℤ} (h : StepsW2 (x :: L)) : StepsW2 L := by
  match L, h with
  | [], _ => trivial
  | _ :: _, h => exact h.2

lemma StepsW2.dropLast {L : List ℤ} {e : ℤ} (h : StepsW2 (L ++ [e])) : StepsW2 L := by
  induction L with
  | nil => trivial
  | cons x L ih =>
    match L, h, ih with
    | [], _, _ => trivial
    | y :: L', h, ih => exact ⟨h.1, ih h.2⟩

/-- Step costs along `a, R, e`. -/
noncomputable def pathCost (a : ℤ) : List ℤ → ℤ → ℕ
  | [], e => cst a e
  | p :: rest, e => cst a p + pathCost p rest e

lemma chain_eq (a : ℤ) (L : List ℤ) : chain a L = 5 * L.length + pathCost a L 0 := by
  induction L generalizing a with
  | nil => simp [chain, pathCost]
  | cons p L ih => simp [chain, pathCost, ih]; ring

lemma pathCost_append (a m e : ℤ) (R1 R2 : List ℤ) :
    pathCost a (R1 ++ m :: R2) e = pathCost a R1 m + pathCost m R2 e := by
  induction R1 generalizing a with
  | nil => simp [pathCost]
  | cons p R1 ih => simp [pathCost, ih]; ring

lemma pathCost_ge : ∀ (R : List ℤ) (a e : ℤ), R.Nodup → a ∉ R → e ∉ R → (R ≠ [] ∨ a ≠ e) →
    2 * (R.length + 1) ≤ pathCost a R e ∧
      (pathCost a R e = 2 * (R.length + 1) → StepsW2 (a :: R ++ [e]))
  | [], a, e, _, _, _, h => by
    have hae : a ≠ e := by simpa using h
    refine ⟨by simpa [pathCost] using two_le_cst hae, fun heq => ?_⟩
    simp only [pathCost, List.length_nil] at heq
    exact ⟨W2_of_cst heq, trivial⟩
  | p :: R, a, e, hnd, ha, he, _ => by
    have hap : a ≠ p := fun h => ha (by simp [h])
    have hpe : p ≠ e := fun h => he (by simp [h])
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨ih1, ih2⟩ := pathCost_ge R p e hnd'.2 hnd'.1 (fun h => he (by simp [h])) (Or.inr hpe)
    have h2 := two_le_cst hap
    simp only [pathCost, List.length_cons]
    refine ⟨by omega, fun heq => ?_⟩
    have hc : cst a p = 2 := by omega
    exact ⟨W2_of_cst hc, ih2 (by omega)⟩

/-- **Extraction.** -/
theorem extract {O : List ℤ} (hnd : O.Nodup) (h0 : (0 : ℤ) ∈ O) (hcost : chain 0 O ≤ 7 * O.length) :
    ∃ R, (O = 0 :: R ∨ O = R ++ [0]) ∧ StepsW2 R := by
  obtain ⟨R1, R2, rfl⟩ := List.append_of_mem h0
  have hnd' := List.nodup_append.mp hnd
  have h1nd := hnd'.1
  have h2nd := (List.nodup_cons.mp hnd'.2.1).2
  have h01 : (0 : ℤ) ∉ R1 := fun h => by
    have := hnd'.2.2 0 h 0 (by simp); exact this rfl
  have h02 : (0 : ℤ) ∉ R2 := (List.nodup_cons.mp hnd'.2.1).1
  rw [chain_eq, pathCost_append] at hcost
  simp only [List.length_append, List.length_cons] at hcost
  by_cases hR1 : R1 = [] <;> by_cases hR2 : R2 = []
  · subst hR1; subst hR2; exact ⟨[], Or.inl rfl, trivial⟩
  · subst hR1
    obtain ⟨g1, g2⟩ := pathCost_ge R2 0 0 h2nd h02 h02 (Or.inl hR2)
    simp only [pathCost, cst_self, List.length_nil] at hcost
    refine ⟨R2, Or.inl rfl, ?_⟩
    have := g2 (by omega)
    exact (StepsW2.tail this).dropLast
  · subst hR2
    obtain ⟨g1, g2⟩ := pathCost_ge R1 0 0 h1nd h01 h01 (Or.inl hR1)
    simp only [pathCost, cst_self, List.length_nil] at hcost
    refine ⟨R1, Or.inr rfl, ?_⟩
    have := g2 (by omega)
    exact (StepsW2.tail this).dropLast
  · obtain ⟨g1, _⟩ := pathCost_ge R1 0 0 h1nd h01 h01 (Or.inl hR1)
    obtain ⟨g3, _⟩ := pathCost_ge R2 0 0 h2nd h02 h02 (Or.inl hR2)
    omega

end Pts
