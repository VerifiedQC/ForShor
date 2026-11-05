import ILPEncoding.Labels.Labels
import Provider.Weights.Projective

/-! # Cost Bridge for Actual Words
Defines `rawProblem` for a price function and `evalCost`, and proves `costL_eq_evalCost` and `actual_to_costL`, which turn an actual label word into a `CostL` statement. Also defines `finalN` and relates the affine sums to the objective through the later segments of the file.
-/

/- BEGIN Actual.lean sha256=116dd1c8dab368c3f4ad0b607afa69a0b71a1af253de95723e44a62d996d7c05 -/
namespace Paper.F6CostBridge

open Paper.AffineActual Paper.AffineNat Paper.AffineILP Paper.F2CatalogTransfer
open Paper.PPEndToEnd Coupled.Formal

def rawProblem {K : Nat} (price : Nat → Nat) : Prob (F2Source K) :=
  ppProblem price Paper.A4Certificate.verifiedSource

theorem rawProblem_child {K : Nat} (price : Nat → Nat) (t : F2Source K) (w : Nat) :
    (rawProblem price).child t w = t.childWidth w := rfl

theorem rawProblem_own {K : Nat} (price : Nat → Nat) (t : F2Source K)
    (w w' : Nat) :
    (rawProblem price).own t w w' = ownPP t.charge w' := rfl

theorem rawProblem_calls {K : Nat} (price : Nat → Nat) (t : F2Source K) :
    (rawProblem price).calls t = t.calls := rfl

theorem rawProblem_leaf {K : Nat} (price : Nat → Nat) (N w : Nat) :
    (rawProblem (K := K) price).leaf N w = leafPP price N w := rfl

def evalCost {K : Nat} (price : Nat → Nat) :
    List (F2Source K) → Nat → Nat → Nat
  | [], w, N => leafPP price N w
  | t :: rest, w, N =>
      N * ownPP t.charge (t.childWidth w) +
        evalCost price rest (t.childWidth w) (N * t.calls)

theorem costL_eq_evalCost {K : Nat} (price : Nat → Nat)
    (ts : List (F2Source K)) (w N v : Nat)
    (h : CostL (rawProblem price) ts w N v) :
    v = evalCost price ts w N := by
  induction h with
  | base w N => rfl
  | step t rest w N v hstrict htail ih =>
      simpa [evalCost, rawProblem_child, rawProblem_own, rawProblem_calls]
        using congrArg (fun v => N * ownPP t.charge (t.childWidth w) + v) ih

theorem actual_to_costL {K : Nat} (a d c : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x : ℤ) (hP : 0 < P)
    (hactual : ActualWord (K := K) a d c P x labels)
    (price : Nat → Nat) (N : Nat) :
    ∃ (w : Nat) (ts : List (F2Source K)) (v : Nat),
      x = P * w ∧ ts.length = labels.length ∧
      CostL (rawProblem price) ts w N v ∧
      v = evalCost price ts w N := by
  induction labels generalizing P x N with
  | nil =>
      obtain ⟨w, hx, hw⟩ := hactual
      exact ⟨w, [], leafPP price N w, hx, rfl, CostL.base w N, rfl⟩
  | cons label rest ih =>
      obtain ⟨t, w, ht, hspec, hx, hr, hnext, hstrict, hrest⟩ := hactual
      have hkpos : 0 < (label.k : ℤ) := by
        have hkn : 0 < label.k :=
          lt_of_lt_of_le (by decide : 0 < 2) label.hk
        exact_mod_cast hkn
      have hPk : 0 < P * label.k := mul_pos hP hkpos
      obtain ⟨w', ts, v, hx', hlen, hcost, hval⟩ :=
        ih (P * label.k) (nextWidth P x (Paper.AffineNat.instantiate a label))
          hPk hrest (N * t.calls)
      have hwidth : w' = t.childWidth w := by
        have heq : (P * label.k) * (w' : ℤ) =
            (P * label.k) * (t.childWidth w : ℤ) := by
          rw [← hx', hnext]
        have hwi : (w' : ℤ) = (t.childWidth w : ℤ) :=
          mul_left_cancel₀ (ne_of_gt hPk) heq
        exact_mod_cast hwi
      subst w'
      have hstep : CostL (rawProblem price) (t :: ts) w N
          (N * ownPP t.charge (t.childWidth w) + v) := by
        apply CostL.step t ts w N v
        · simpa only [rawProblem_child] using hstrict
        · simpa only [rawProblem_child, rawProblem_calls] using hcost
      refine ⟨w, t :: ts, _, hx, ?_, hstep, ?_⟩
      · simp [hlen]
      · exact costL_eq_evalCost price _ _ _ _ hstep

end Paper.F6CostBridge
/- END Actual.lean -/

/- BEGIN Exact.lean sha256=9311c0cea9e0e9e95b4ce9f90fcd386c4d652e2f4abea41d20fa788088b83345 -/
namespace Paper.F6Objective

open Paper.AffineNat Paper.AffineILP Paper.AffineChain Paper.AffineActual
open Paper.F2CatalogTransfer Paper.PPEndToEnd Paper.F6CostBridge
open Coupled.Formal

theorem ownPP_cast (N c child : Nat) (hchild : 1 ≤ child) :
    (N * ownPP c child : ℤ) =
      8 * (N : ℤ) * c * ((child : ℤ) - 1) := by
  unfold ownPP
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hchild]
  ring

def finalN (N : Nat) : List Paper.AffineNat.Label → Nat
  | [] => N
  | label :: rest => finalN (N * (2 * (label.k - 1) + 1)) rest

def terminalNat (P x : ℤ) (a : Nat → Nat)
    (labels : List Paper.AffineNat.Label) : Nat :=
  (terminalWidth P x (labels.map (Paper.AffineNat.instantiate a)) /
    terminalProduct P (labels.map (Paper.AffineNat.instantiate a))).toNat

def affineSum (a c : Nat → Nat) (N : Nat) (P x : ℤ) :
    List Paper.AffineNat.Label → ℤ
  | [] => 0
  | label :: rest =>
      let next := nextWidth P x (Paper.AffineNat.instantiate a label)
      8 * (N : ℤ) * (c label.k : ℤ) * (next / (P * label.k) - 1) +
        affineSum a c (N * (2 * (label.k - 1) + 1)) (P * label.k) next rest

theorem actual_cost_exact {K : Nat} (a d c : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x : ℤ) (hP : 0 < P)
    (hactual : ActualWord (K := K) a d c P x labels)
    (hpos : PositiveWidths P x
      (labels.map (Paper.AffineNat.instantiate a)))
    (price : Nat → Nat) (N : Nat) :
    ∃ (w : Nat) (ts : List (F2Source K)) (v : Nat),
      x = P * w ∧ ts.length = labels.length ∧
      CostL (F6CostBridge.rawProblem price) ts w N v ∧
      (v : ℤ) = affineSum a c N P x labels +
        (leafPP price (finalN N labels) (terminalNat P x a labels) : ℤ) := by
  induction labels generalizing P x N with
  | nil =>
      obtain ⟨w, hx, hw⟩ := hactual
      have hterminal : terminalNat P x a [] = w := by
        simp [terminalNat, terminalWidth, terminalProduct, hx,
          Int.mul_ediv_cancel_left _ (ne_of_gt hP)]
      exact ⟨w, [], leafPP price N w, hx, rfl, CostL.base w N,
        by simp [affineSum, finalN, hterminal]⟩
  | cons label rest ih =>
      obtain ⟨t, w, ht, hspec, hx, hr, hnext, hstrict, hrest⟩ := hactual
      have hkpos : 0 < (label.k : ℤ) := by
        have hkn : 0 < label.k :=
          lt_of_lt_of_le (by decide : 0 < 2) label.hk
        exact_mod_cast hkn
      have hPk : 0 < P * label.k := mul_pos hP hkpos
      let next := nextWidth P x (Paper.AffineNat.instantiate a label)
      have hnext' : next = P * label.k * (t.childWidth w : ℤ) := hnext
      let N' := N * (2 * (label.k - 1) + 1)
      have hcall : t.calls = 2 * (label.k - 1) + 1 := by
        change 2 * (t.source.k - 1) + 1 = 2 * (label.k - 1) + 1
        exact congrArg (fun k => 2 * (k - 1) + 1) hspec.1
      have hpos' : PositiveWidths (P * label.k) next
          (rest.map (Paper.AffineNat.instantiate a)) := hpos.2
      obtain ⟨w', ts, v, hx', hlen, hcost, hval⟩ :=
        ih (P * label.k) next hPk hrest hpos' N'
      have hwidth : w' = t.childWidth w := by
        have heq : (P * label.k) * (w' : ℤ) =
            (P * label.k) * (t.childWidth w : ℤ) := by
          calc
            _ = next := hx'.symm
            _ = _ := hnext'
        have hwi : (w' : ℤ) = (t.childWidth w : ℤ) :=
          mul_left_cancel₀ (ne_of_gt hPk) heq
        exact_mod_cast hwi
      have hchild : 1 ≤ t.childWidth w := by
        have hq : 1 ≤ next / (P * label.k) := by
          cases rest with
          | nil => exact hpos'
          | cons q tail => exact hpos'.1
        rw [hnext', Int.mul_ediv_cancel_left _ (ne_of_gt hPk)] at hq
        exact_mod_cast hq
      subst w'
      have hstep : CostL (F6CostBridge.rawProblem price) (t :: ts) w N
          (N * ownPP t.charge (t.childWidth w) + v) := by
        apply CostL.step t ts w N v
        · simpa only [rawProblem_child] using hstrict
        · simpa only [rawProblem_child, rawProblem_calls, hcall] using hcost
      have hcharge : t.charge = c label.k := hspec.2.1
      have hlocal : (N * ownPP t.charge (t.childWidth w) : ℤ) =
          8 * (N : ℤ) * (c label.k : ℤ) *
            (next / (P * label.k) - 1) := by
        rw [ownPP_cast N t.charge (t.childWidth w) hchild, hcharge]
        rw [hnext', Int.mul_ediv_cancel_left _ (ne_of_gt hPk)]
      refine ⟨w, t :: ts, _, hx, ?_, hstep, ?_⟩
      · simp [hlen]
      · rw [Nat.cast_add, Nat.cast_mul]
        rw [hlocal, hval]
        change
          8 * (N : ℤ) * (c label.k : ℤ) * (next / (P * label.k) - 1) +
            (affineSum a c N' (P * label.k) next rest +
              (leafPP price (finalN N' rest)
                (terminalNat (P * label.k) next a rest) : ℤ)) =
          (8 * (N : ℤ) * (c label.k : ℤ) * (next / (P * label.k) - 1) +
            affineSum a c N' (P * label.k) next rest) +
              (leafPP price (finalN N' rest)
                (terminalNat (P * label.k) next a rest) : ℤ)
        ring

end Paper.F6Objective
/- END Exact.lean -/

/- BEGIN Budget.lean sha256=5289328768cf12c8546def47c209c8bbda812cab9d588b618d8cd09d99c407a9 -/
namespace Paper.F6Cleared

open Paper.AffineNat Paper.AffineILP Paper.AffineChain
open Paper.AffineCost Paper.F6Objective

def clearedSum (D : ℤ) (a c : Nat → Nat) (N : Nat) (P x : ℤ) :
    List Paper.AffineNat.Label → ℤ
  | [] => 0
  | label :: rest =>
      let next := nextWidth P x (Paper.AffineNat.instantiate a label)
      8 * (N : ℤ) * (c label.k : ℤ) *
        ((D / (P * label.k)) * next - D) +
      clearedSum D a c (N * (2 * (label.k - 1) + 1))
        (P * label.k) next rest

theorem prefix_dvd_terminal (P : ℤ) (ds : List Decoration) :
    P ∣ terminalProduct P ds := by
  induction ds generalizing P with
  | nil => exact dvd_refl P
  | cons label rest ih =>
      obtain ⟨m, hm⟩ := ih (P * label.k)
      refine ⟨label.k * m, ?_⟩
      change terminalProduct (P * label.k) rest = P * (label.k * m)
      rw [hm]
      ring

theorem terminalProduct_pos (P : ℤ) (ds : List Decoration) (hP : 0 < P) :
    0 < terminalProduct P ds := by
  induction ds generalizing P with
  | nil => exact hP
  | cons label rest ih =>
      have hk : 0 < label.k :=
        lt_of_lt_of_le (by decide : (0 : ℤ) < 2) label.hk
      exact ih (P * label.k) (mul_pos hP hk)

theorem clear_affineSum (a c : Nat → Nat) (N : Nat)
    (labels : List Paper.AffineNat.Label) (P x : ℤ)
    (hP : 0 < P)
    (hres : AllResidues P x (labels.map (Paper.AffineNat.instantiate a))) :
    terminalProduct P (labels.map (Paper.AffineNat.instantiate a)) *
      affineSum a c N P x labels =
    clearedSum (terminalProduct P
      (labels.map (Paper.AffineNat.instantiate a))) a c N P x labels := by
  induction labels generalizing P x N with
  | nil => simp [affineSum, clearedSum]
  | cons label rest ih =>
      let next := nextWidth P x (Paper.AffineNat.instantiate a label)
      let D := terminalProduct P
        ((label :: rest).map (Paper.AffineNat.instantiate a))
      have hk : 0 < (label.k : ℤ) := by
        have hkn : 0 < label.k :=
          lt_of_lt_of_le (by decide : 0 < 2) label.hk
        exact_mod_cast hkn
      have hPk : 0 < P * label.k := mul_pos hP hk
      have hnextres : AllResidues (P * label.k) next
          (rest.map (Paper.AffineNat.instantiate a)) := hres.2.2
      have hnextdiv : P * label.k ∣ next :=
        allResidues_divisor _ _ _ hnextres
      have hDdiv : P * label.k ∣ D := by
        change P * label.k ∣ terminalProduct (P * label.k)
          (rest.map (Paper.AffineNat.instantiate a))
        exact prefix_dvd_terminal _ _
      let term : Term D :=
        { P := P * label.k, N := N, c := c label.k,
          x := next, hPx := hnextdiv, hPD := hDdiv, hP := hPk }
      have hfirst : D *
          (8 * (N : ℤ) * (c label.k : ℤ) *
            (next / (P * label.k) - 1)) =
          8 * (N : ℤ) * (c label.k : ℤ) *
            ((D / (P * label.k)) * next - D) := by
        exact clear_one term
      have htail := ih (N * (2 * (label.k - 1) + 1))
        (P * label.k) next hPk hnextres
      change D * (8 * (N : ℤ) * (c label.k : ℤ) *
          (next / (P * label.k) - 1) +
          affineSum a c (N * (2 * (label.k - 1) + 1))
            (P * label.k) next rest) =
        8 * (N : ℤ) * (c label.k : ℤ) *
          ((D / (P * label.k)) * next - D) +
          clearedSum D a c (N * (2 * (label.k - 1) + 1))
            (P * label.k) next rest
      rw [mul_add, hfirst]
      exact congrArg (fun z => 8 * (N : ℤ) * (c label.k : ℤ) *
        ((D / (P * label.k)) * next - D) + z) htail

theorem actual_budget_iff {K : Nat} (a d c : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x : ℤ) (hP : 0 < P)
    (hactual : Paper.AffineActual.ActualWord (K := K) a d c P x labels)
    (hpos : PositiveWidths P x
      (labels.map (Paper.AffineNat.instantiate a)))
    (hres : AllResidues P x
      (labels.map (Paper.AffineNat.instantiate a)))
    (price : Nat → Nat) (N T : Nat) :
    ∃ (w : Nat) (ts : List (Paper.F2CatalogTransfer.F2Source K)) (v : Nat),
      x = P * w ∧ ts.length = labels.length ∧
      Coupled.Formal.CostL (Paper.F6CostBridge.rawProblem price) ts w N v ∧
      (v ≤ T ↔
        clearedSum (terminalProduct P
          (labels.map (Paper.AffineNat.instantiate a))) a c N P x labels ≤
        terminalProduct P (labels.map (Paper.AffineNat.instantiate a)) *
          ((T : ℤ) -
            (Paper.PPEndToEnd.leafPP price (finalN N labels)
              (terminalNat P x a labels) : ℤ))) := by
  obtain ⟨w, ts, v, hx, hlen, hcost, hval⟩ :=
    actual_cost_exact a d c labels P x hP hactual hpos price N
  let D := terminalProduct P (labels.map (Paper.AffineNat.instantiate a))
  have hD : 0 < D := terminalProduct_pos P _ hP
  have hclear : D * affineSum a c N P x labels =
      clearedSum D a c N P x labels :=
    clear_affineSum a c N labels P x hP hres
  refine ⟨w, ts, v, hx, hlen, hcost, ?_⟩
  constructor
  · intro hv
    have hvi : (v : ℤ) ≤ T := by exact_mod_cast hv
    have haff : affineSum a c N P x labels ≤
        (T : ℤ) - (Paper.PPEndToEnd.leafPP price
          (finalN N labels) (terminalNat P x a labels) : ℤ) := by
      rw [hval] at hvi
      omega
    have hscaled := (cleared_budget_iff D _ _ hD).2 haff
    rw [← hclear]
    exact hscaled
  · intro hscaled
    have hscaled' : D * affineSum a c N P x labels ≤
        D * ((T : ℤ) - (Paper.PPEndToEnd.leafPP price
          (finalN N labels) (terminalNat P x a labels) : ℤ)) := by
      simpa only [hclear] using hscaled
    have haff := (cleared_budget_iff D _ _ hD).1 hscaled'
    have hvi : (v : ℤ) ≤ T := by rw [hval]; omega
    exact_mod_cast hvi

theorem terminalNat_eq (a : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x z : ℤ) (hP : 0 < P)
    (hterminal : terminalWidth P x
      (labels.map (Paper.AffineNat.instantiate a)) =
      terminalProduct P (labels.map (Paper.AffineNat.instantiate a)) * z) :
    terminalNat P x a labels = z.toNat := by
  have hD : 0 < terminalProduct P
      (labels.map (Paper.AffineNat.instantiate a)) :=
    terminalProduct_pos P _ hP
  simp [terminalNat, hterminal,
    Int.mul_ediv_cancel_left _ (ne_of_gt hD)]

theorem fixed_constraints_budget {K : Nat} (a d c : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x z : ℤ)
    (hP : 0 < P) (hz : 1 ≤ z)
    (hshared : ∀ label ∈ labels,
      label.d = d label.k ∧ label.c = c label.k ∧
      Paper.F4ChargeIntervals.minCharge (K := K) label.k
        (d label.k) (a label.k) = (c label.k : WithTop Nat))
    (hterminal : terminalWidth P x
      (labels.map (Paper.AffineNat.instantiate a)) =
      terminalProduct P (labels.map (Paper.AffineNat.instantiate a)) * z)
    (hcleared : ClearedContractions P x
      (labels.map (Paper.AffineNat.instantiate a)))
    (price : Nat → Nat) (N T : Nat) :
    ∃ (w : Nat) (ts : List (Paper.F2CatalogTransfer.F2Source K)) (v : Nat),
      x = P * w ∧ ts.length = labels.length ∧
      Coupled.Formal.CostL (Paper.F6CostBridge.rawProblem price) ts w N v ∧
      (v ≤ T ↔
        clearedSum (terminalProduct P
          (labels.map (Paper.AffineNat.instantiate a))) a c N P x labels ≤
        terminalProduct P (labels.map (Paper.AffineNat.instantiate a)) *
          ((T : ℤ) -
            (Paper.PPEndToEnd.leafPP price (finalN N labels)
              z.toNat : ℤ))) := by
  have hactual := (Paper.AffineConverse.fixed_word_iff_constraints
    a d c labels P x hP hshared).2 ⟨z, hz, hterminal, hcleared⟩
  have hboth := terminal_cleared_positive P x
    (labels.map (Paper.AffineNat.instantiate a)) z hP hz
    hterminal hcleared
  have hbudget := actual_budget_iff a d c labels P x hP hactual
    hboth.2 hboth.1 price N T
  simpa only [terminalNat_eq a labels P x z hP hterminal] using hbudget

end Paper.F6Cleared
/- END Budget.lean -/
