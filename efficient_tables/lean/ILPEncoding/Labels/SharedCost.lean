import ILPEncoding.Labels.ILPChecked

/-! # Shared Cost of Actual Words
Proves `arityInj_of_tableAt`, arity injectivity from table lookup, and `actual_to_shared_costL`, which gives the shared `CostL` statement for an actual word.
-/

namespace Paper.F6SharedCost

open Paper.AffineActual Paper.AffineNat Paper.AffineILP
open Paper.F2CatalogTransfer Paper.AffineTable Paper.F6CostBridge
open Paper.PPEndToEnd Coupled.Formal

theorem arityInj_of_tableAt {K : Nat} (a d c : Nat → Nat)
    (ts : List (F2Source K))
    (hselected : ∀ t ∈ ts, tableAt (K := K) a d c t.arity = some t) :
    ArityInj F2Source.arity ts := by
  intro t ht u hu heq
  have hfirst := hselected t ht
  have hsecond := hselected u hu
  rw [heq] at hfirst
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem actual_to_shared_costL {K : Nat} (a d c : Nat → Nat)
    (labels : List Label) (P x : ℤ) (hP : 0 < P)
    (hactual : ActualWord (K := K) a d c P x labels)
    (price : Nat → Nat) (N : Nat) :
    ∃ (w : Nat) (ts : List (F2Source K)) (v : Nat),
      x = P * w ∧ ts.length = labels.length ∧
      CostL (Paper.F6CostBridge.rawProblem price) ts w N v ∧
      (∀ t ∈ ts, tableAt (K := K) a d c t.arity = some t) ∧
      ArityInj F2Source.arity ts := by
  induction labels generalizing P x N with
  | nil =>
      obtain ⟨w, hx, hw⟩ := hactual
      exact ⟨w, [], leafPP price N w, hx, rfl, CostL.base w N,
        by simp, by intro t ht; simp at ht⟩
  | cons label rest ih =>
      obtain ⟨t, w, ht, hspec, hx, hr, hnext, hstrict, hrest⟩ := hactual
      have hkpos : 0 < (label.k : ℤ) := by
        have hkn : 0 < label.k :=
          lt_of_lt_of_le (by decide : 0 < 2) label.hk
        exact_mod_cast hkn
      have hPk : 0 < P * label.k := mul_pos hP hkpos
      obtain ⟨w', ts, v, hx', hlen, hcost, hselected, hinj⟩ :=
        ih (P * label.k)
          (nextWidth P x (Paper.AffineNat.instantiate a label))
          hPk hrest (N * t.calls)
      have hwidth : w' = t.childWidth w := by
        have heq : (P * label.k) * (w' : ℤ) =
            (P * label.k) * (t.childWidth w : ℤ) := by
          rw [← hx', hnext]
        have hwi : (w' : ℤ) = (t.childWidth w : ℤ) :=
          mul_left_cancel₀ (ne_of_gt hPk) heq
        exact_mod_cast hwi
      subst w'
      have hstep : CostL (Paper.F6CostBridge.rawProblem price) (t :: ts) w N
          (N * ownPP t.charge (t.childWidth w) + v) := by
        apply CostL.step t ts w N v
        · simpa only [rawProblem_child] using hstrict
        · simpa only [rawProblem_child, rawProblem_calls] using hcost
      have hselected' : ∀ u ∈ t :: ts,
          tableAt (K := K) a d c u.arity = some u := by
        intro u hu
        rcases List.mem_cons.mp hu with heq | htail
        · subst u
          simpa only [hspec.1] using ht
        · exact hselected u htail
      refine ⟨w, t :: ts, _, hx, ?_, hstep, hselected', ?_⟩
      · simp [hlen]
      · exact arityInj_of_tableAt a d c (t :: ts) hselected'

end Paper.F6SharedCost
