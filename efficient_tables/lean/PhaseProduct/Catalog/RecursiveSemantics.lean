import PhaseProduct.Catalog.TableSemantics

/-!
# Recursive semantics of PP policies

Signed round-trip facts for peak-bounded encodings (`signed_roundtrip_natAbs_lt`,
`signed_roundtrip_of_peak_bound`) and phase-character scaling lemmas
(`phaseCharacter_scaled`). It composes these into the correctness of the
policy evaluator, `PPPolicy.eval_correct`, with a genuine leaf action.
-/

open scoped BigOperators

namespace Paper.PPEndToEnd

theorem signed_roundtrip_natAbs_lt (W : Nat) (a : Int)
    (h : (BitVec.ofInt W a).toInt = a) : a.natAbs < 2 ^ W := by
  cases W with
  | zero =>
      simp at h
      simp [← h]
  | succ n =>
      have hlo := BitVec.le_toInt (BitVec.ofInt (n + 1) a)
      have hhi := BitVec.toInt_lt (x := BitVec.ofInt (n + 1) a)
      rw [h] at hlo hhi
      have hp : (2 : Int) ^ (n + 1 - 1) < (2 : Int) ^ (n + 1) := by
        simp only [Nat.add_sub_cancel_right, pow_succ]
        have hpow : (0 : Int) < 2 ^ n := pow_pos (by norm_num) _
        omega
      have habs : (a.natAbs : Int) < (2 : Int) ^ (n + 1) := by
        rcases Int.natAbs_eq a with he | he
        · omega
        · omega
      exact_mod_cast habs

theorem signed_roundtrip_of_peak_bound (B : Nat) (hB : 0 < B)
    (m : Int) (hm : m.natAbs < 2 ^ (B - 1)) :
    (BitVec.ofInt B m).toInt = m := by
  have he : B - 1 + 1 = B := by omega
  rw [← he]
  exact Paper.SignedEncoding.toInt_ofInt_of_natAbs_lt (B - 1) m hm

theorem getD_bound {q p : Nat} (xs : List Int) (hlen : xs.length = q)
    (hbound : ∀ m ∈ xs, m.natAbs < 2 ^ p) (l : Fin q) :
    (xs.getD l.val 0).natAbs < 2 ^ p := by
  have hlt : l.val < xs.length := by omega
  rw [List.getD_eq_getElem _ _ hlt]
  exact hbound _ (List.getElem_mem hlt)

theorem optionProduct_map_some (xs : List ℂ) :
    optionProduct (xs.map some) = some xs.prod := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [optionProduct, ih]

theorem optionProduct_finRange {q : Nat} (f : Fin q → Option ℂ)
    (g : Fin q → ℂ) (h : ∀ l, f l = some (g l)) :
    optionProduct ((List.finRange q).map f) = some (∏ l, g l) := by
  have hmap : (List.finRange q).map f =
      ((List.finRange q).map g).map some := by
    rw [List.map_map]
    apply List.map_congr_left
    intro l _
    exact h l
  rw [hmap, optionProduct_map_some]
  simp only [← List.ofFn_eq_map, List.prod_ofFn]

theorem phaseCharacter_scaled (theta : ℝ) (weight q : ℚ) :
    Paper.ValuePhase.phaseCharacter (theta * (weight : ℝ)) q =
      Paper.ValuePhase.phaseCharacter theta (weight * q) := by
  unfold Paper.ValuePhase.phaseCharacter Paper.ValuePhase.phaseAngle
  congr 1
  push_cast
  ring

/-- The evaluator uses a genuine leaf action; this theorem composes that
action through each source table's actual native traces and decoded marker
pairs. The leaf premise is discharged by the separate schoolbook theorem. -/
theorem PPPolicy.eval_correct {K W : Nat} (leafAction : LeafAction)
    (hleaf : ∀ W theta a c,
      (BitVec.ofInt W a).toInt = a →
      (BitVec.ofInt W c).toInt = c →
      leafAction W theta a c =
        some (Paper.ValuePhase.phaseCharacter theta ((a : ℚ) * (c : ℚ))))
    (policy : PPPolicy K W) : ∀ (theta : ℝ) (a c : Int),
    (BitVec.ofInt W a).toInt = a →
    (BitVec.ofInt W c).toInt = c →
    policy.eval leafAction theta a c =
      some (Paper.ValuePhase.phaseCharacter theta ((a : ℚ) * (c : ℚ))) := by
  induction policy with
  | leaf W =>
      intro theta a c ha hc
      exact hleaf W theta a c ha hc
  | @node W table hcontracting child ih =>
      intro theta a c ha hc
      have haMag := signed_roundtrip_natAbs_lt W a ha
      have hcMag := signed_roundtrip_natAbs_lt W c hc
      obtain ⟨hxa, hza, hlenx, hlenz, hboundx, hboundz, hphase⟩ :=
        table.native_pair_phase W theta a c haMag hcMag
      let hpos : 0 < table.source.k :=
        TableGeneration.positive_of_ge_two table.source.hk
      let x := Paper.SignedLimbs.limbs W hpos a
      let z := Paper.SignedLimbs.limbs W hpos c
      let B := table.childWidth W
      let mx := (Paper.PhaseIdentity.observations (List.ofFn table.points) x).map
        (BitVec.ofInt B)
      let mz := (Paper.PhaseIdentity.observations (List.ofFn table.points) z).map
        (BitVec.ofInt B)
      have hB : 0 < B := by
        simp [B, VerifiedPPCandidate.childWidth,
          TableGeneration.RecursiveCost.nextBalancedSignedWidth]
      have hchild (l : Fin table.calls) :
          child.eval leafAction (theta * (table.weights W l : ℝ))
            ((mx.map BitVec.toInt).getD l.val 0)
            ((mz.map BitVec.toInt).getD l.val 0) =
            some (Paper.ValuePhase.phaseCharacter
              (theta * (table.weights W l : ℝ))
              (((mx.map BitVec.toInt).getD l.val 0 : ℚ) *
               ((mz.map BitVec.toInt).getD l.val 0 : ℚ))) := by
        apply ih
        · apply signed_roundtrip_of_peak_bound B hB
          exact getD_bound (mx.map BitVec.toInt)
            (by simpa only [mx, List.length_map] using hlenx)
            hboundx l
        · apply signed_roundtrip_of_peak_bound B hB
          exact getD_bound (mz.map BitVec.toInt)
            (by simpa only [mz, List.length_map] using hlenz)
            hboundz l
      have hprod :
          (∏ l : Fin table.calls,
            Paper.ValuePhase.phaseCharacter
              (theta * (table.weights W l : ℝ))
              (((mx.map BitVec.toInt).getD l.val 0 : ℚ) *
               ((mz.map BitVec.toInt).getD l.val 0 : ℚ))) =
            Paper.ValuePhase.phaseCharacter theta ((a : ℚ) * (c : ℚ)) := by
        calc
          _ = ∏ l : Fin table.calls, Paper.ValuePhase.phaseCharacter theta
                (table.weights W l *
                  ((mx.map BitVec.toInt).getD l.val 0 : ℚ) *
                  ((mz.map BitVec.toInt).getD l.val 0 : ℚ)) := by
                apply Finset.prod_congr rfl
                intro l _
                rw [phaseCharacter_scaled]
                congr 1
                ring
          _ = _ := hphase
      change nodeEval W table (child.eval leafAction) theta a c = _
      simp only [nodeEval, hxa, hza, and_self]
      split_ifs with hh
      · change optionProduct ((List.finRange table.calls).map (fun l =>
          child.eval leafAction (theta * (table.weights W l : ℝ))
            ((mx.map BitVec.toInt).getD l.val 0)
            ((mz.map BitVec.toInt).getD l.val 0))) = _
        exact (optionProduct_finRange _ _ hchild).trans (congrArg some hprod)
      · exact False.elim (hh trivial)

end Paper.PPEndToEnd
