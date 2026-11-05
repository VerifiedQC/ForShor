import Source.Policy

/-!
# P6 parity construction

Supplies the machinery for the P6 policy. Gives precomputed small-`k` programs (`orderedPoints` and `program` in the `Precomputed` namespaces) and a general parity construction using `PointPairType`, `pairKindOfIndex` and `parityDegree`.
-/

namespace TableGeneration.Policies.Accepted.P6f7d25984ff8.GeneralParity

open Operations

namespace Precomputed

namespace K2Product

def orderedPoints : List Point :=
  [.int 0, .frac 0, .int 1]

def program : Prog 2 :=
  [.phaseProduct 0,
   .phaseProduct 1,
   .addScaled 0 1 false 0,
   .phaseProduct 0,
   .addScaled 0 1 true 0]

end K2Product

namespace K3Product

def orderedPoints : List Point :=
  [.int 1, .int 2, .frac 0, .int (-1), .int 0]

def program : Prog 3 :=
  [.addScaled 0 1 false 0,
   .addScaled 1 0 false 0,
   .addScaled 0 2 false 0,
   .addScaled 1 2 false 2,
   .phaseProduct 0,
   .phaseProduct 1,
   .phaseProduct 2,
   .addScaled 0 1 true 0,
   .addScaled 0 2 false 1,
   .addScaled 1 0 false 1,
   .addScaled 0 1 false 0,
   .addScaled 1 2 true 1,
   .phaseProduct 0,
   .phaseProduct 1,
   .addScaled 0 2 true 0,
   .addScaled 1 0 true 0,
   .addScaled 0 1 false 0]

end K3Product

namespace K2TripleProduct

def orderedPoints : List Point :=
  [.int 0, .frac 0, .int 1, .int (-1)]

def program : Prog 2 :=
  [.phaseProduct 0,
   .phaseProduct 1,
   .addScaled 0 1 false 0,
   .shiftL 1 1,
   .addScaled 1 0 true 0,
   .negate 1,
   .phaseProduct 0,
   .phaseProduct 1,
   .negate 1,
   .addScaled 1 0 false 0,
   .shiftR 1 1,
   .addScaled 0 1 true 0]

end K2TripleProduct

namespace K3TripleProduct

def orderedPoints : List Point :=
  [.int (-2), .int (-1), .frac 0, .int 2, .int 1, .int 0, .frac 2]

def program : Prog 3 :=
  [.addScaled 0 1 true 1,
   .addScaled 1 0 false 0,
   .addScaled 0 2 false 2,
   .addScaled 1 2 false 0,
   .phaseProduct 0,
   .phaseProduct 1,
   .phaseProduct 2,
   .addScaled 0 1 true 1,
   .addScaled 1 2 true 2,
   .addScaled 2 0 true 0,
   .addScaled 1 2 true 0,
   .addScaled 2 1 true 0,
   .addScaled 0 2 false 1,
   .phaseProduct 0,
   .phaseProduct 2,
   .addScaled 0 1 false 1,
   .addScaled 1 2 false 1,
   .addScaled 2 1 false 0,
   .addScaled 2 0 false 0,
   .phaseProduct 0,
   .phaseProduct 2,
   .addScaled 2 1 true 1,
   .addScaled 1 0 true 1]

end K3TripleProduct

end Precomputed

inductive PointPairType where
  | integer
  | fraction
deriving DecidableEq, Repr

def twoPowInt (e : Nat) : Int := 2 ^ e

def pairKindOfIndex (i : Nat) : PointPairType :=
  if i % 2 = 0 then .integer else .fraction

def pairExponentOfIndex (i : Nat) : Nat :=
  1 + i / 2

def parityDegree (kind : PointPairType) (k : Nat) (j : Fin k) : Nat :=
  match kind with
  | .integer => j.val
  | .fraction => k - 1 - j.val

theorem positive_of_ge_four {k : Nat} (hk : k >= 4) : 0 < k :=
  Nat.lt_of_lt_of_le (by decide) hk

theorem one_lt_of_ge_four {k : Nat} (hk : k >= 4) : 1 < k :=
  Nat.lt_of_lt_of_le (by decide) hk

theorem two_lt_of_ge_four {k : Nat} (hk : k >= 4) : 2 < k :=
  Nat.lt_of_lt_of_le (by decide) hk

theorem ge_four_of_ge_two_ne_two_ne_three {k : Nat}
    (hk : k >= 2) (h2 : k ≠ 2) (h3 : k ≠ 3) : k >= 4 := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · exact False.elim (h2 h.symm)
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · exact False.elim (h3 h'.symm)
    · exact h'

def evenCarrier (k : Nat) (hk : k >= 4) : PointPairType -> Fin k
  | .integer => ⟨0, positive_of_ge_four hk⟩
  | .fraction => ⟨k - 1, last_lt (positive_of_ge_four hk)⟩

def oddCarrier (k : Nat) (hk : k >= 4) : PointPairType -> Fin k
  | .integer => ⟨1, one_lt_of_ge_four hk⟩
  | .fraction => ⟨k - 2, Nat.sub_lt (positive_of_ge_four hk) (by decide)⟩

def carrierAdds
    (k : Nat) (kind : PointPairType) (e : Nat) (dst : Fin k) (parity : Nat) : Prog k :=
  (List.finRange k).foldl (fun acc j =>
    let d := parityDegree kind k j
    if d % 2 = parity then
      if j = dst then acc else acc ++ addConstFrom dst j (twoPowInt (e * d))
    else
      acc) []

def combineParityCarriers {k : Nat} (even odd : Fin k) : Prog k :=
  [.addScaled odd even false 0,
   .shiftL even 1,
   .addScaled even odd true 0]

def generateParityInitialBlock (k : Nat) (hk : k >= 4) : Prog k :=
  let r0 : Fin k := ⟨0, positive_of_ge_four hk⟩
  let r1 : Fin k := ⟨1, one_lt_of_ge_four hk⟩
  let r2 : Fin k := ⟨2, two_lt_of_ge_four hk⟩
  let rlast : Fin k := ⟨k - 1, last_lt (positive_of_ge_four hk)⟩
  let buildEven := carrierAdds k .integer 0 r2 0
  let buildOdd := carrierAdds k .integer 0 r1 1
  let build := buildEven ++ buildOdd ++ combineParityCarriers r2 r1
  build ++ [.phaseProduct r0, .phaseProduct rlast, .phaseProduct r1, .phaseProduct r2] ++
    apply_Op_inverse build

def generateParityPairBlock
    (k : Nat) (hk : k >= 4) (kind : PointPairType) (e : Nat) : Prog k :=
  let reven := evenCarrier k hk kind
  let rodd := oddCarrier k hk kind
  let buildEven := carrierAdds k kind e reven 0
  let buildOdd := [.shiftL rodd e] ++ carrierAdds k kind e rodd 1
  let build := buildEven ++ buildOdd ++ combineParityCarriers reven rodd
  build ++ [.phaseProduct rodd, .phaseProduct reven] ++ apply_Op_inverse build

def generateParitySingletonBlock (k : Nat) (hk : k >= 4) (x : Point) : Prog k :=
  opsForPointWithProduct (positive_of_ge_four hk) x

def generatedPoints (mode : ProductMode) (k : Nat) : List Point :=
  canonicalPoints mode k

def candidateGeneratePointsInOrder
    (mode : ProductMode) (k : Nat) (_hk : k >= 2) : List Point :=
  match mode with
  | .PhaseProduct =>
      if _h2 : k = 2 then Precomputed.K2Product.orderedPoints
      else if _h3 : k = 3 then Precomputed.K3Product.orderedPoints
      else generatedPoints mode k
  | .PhaseTripleProduct =>
      if _h2 : k = 2 then Precomputed.K2TripleProduct.orderedPoints
      else if _h3 : k = 3 then Precomputed.K3TripleProduct.orderedPoints
      else generatedPoints mode k

abbrev ResetBlock (k : Nat) := Prog k × List Point

def parityBlocks (mode : ProductMode) (k : Nat) (hk : k >= 4) : List (ResetBlock k) :=
  let remaining := mode.pointCount k - 4
  let pairCount := remaining / 2
  let initial : ResetBlock k :=
    (generateParityInitialBlock k hk,
      [canonicalPoint 0, canonicalPoint 1, canonicalPoint 2, canonicalPoint 3])
  let pairs := (List.range pairCount).map fun i =>
    (generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i),
      [canonicalPoint (4 + 2 * i), canonicalPoint (5 + 2 * i)])
  let singleton :=
    if remaining % 2 = 1 then
      let index := 4 + 2 * pairCount
      [(generateParitySingletonBlock k hk (canonicalPoint index), [canonicalPoint index])]
    else
      []
  initial :: pairs ++ singleton

def candidateBlocks (mode : ProductMode) (k : Nat) (hk : k >= 2) : List (ResetBlock k) :=
  match mode with
  | .PhaseProduct =>
      if h2 : k = 2 then
        [(h2.symm ▸ Precomputed.K2Product.program, Precomputed.K2Product.orderedPoints)]
      else if h3 : k = 3 then
        [(h3.symm ▸ Precomputed.K3Product.program, Precomputed.K3Product.orderedPoints)]
      else parityBlocks mode k (ge_four_of_ge_two_ne_two_ne_three hk h2 h3)
  | .PhaseTripleProduct =>
      if h2 : k = 2 then
        [(h2.symm ▸ Precomputed.K2TripleProduct.program,
          Precomputed.K2TripleProduct.orderedPoints)]
      else if h3 : k = 3 then
        [(h3.symm ▸ Precomputed.K3TripleProduct.program,
          Precomputed.K3TripleProduct.orderedPoints)]
      else parityBlocks mode k (ge_four_of_ge_two_ne_two_ne_three hk h2 h3)

def blockPrograms {k : Nat} (blocks : List (ResetBlock k)) : Prog k :=
  blocks.flatMap Prod.fst

def candidateGenerate (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k :=
  blockPrograms (candidateBlocks mode k hk)

def runConsume? {k : Nat} (hk : k > 0) :
    State k -> Prog k -> List Point -> Option (State k × List Point)
  | sigma, [], pts => some (sigma, pts)
  | sigma, op :: ops, pts =>
      match op with
      | .phaseProduct i =>
          match pts with
          | [] => none
          | pt :: rest =>
              if matchesAt_pointRow_state hk sigma i pt then
                runConsume? hk sigma ops rest
              else
                none
      | _ =>
          match applyOp? sigma op with
          | none => none
          | some sigma' => runConsume? hk sigma' ops pts

theorem runConsume_run {k : Nat} (hk : k > 0) (sigma sigma' : State k)
    (ops : Prog k) (pts rest : List Point)
    (h : runConsume? hk sigma ops pts = some (sigma', rest)) :
    run? ops sigma = some sigma' := by
  induction ops generalizing sigma pts with
  | nil =>
      simp [runConsume?] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | cons op ops ih =>
      cases op with
      | shiftL i n =>
          simp only [runConsume?, applyOp?] at h
          simp only [run?, applyOp?]
          exact ih _ _ h
      | shiftR i n =>
          simp only [runConsume?] at h
          simp only [run?]
          cases hop : applyOp? sigma (.shiftR i n) with
          | none => simp [hop] at h
          | some next =>
              simpa using ih next pts (by simpa [hop] using h)
      | negate i =>
          simp only [runConsume?, applyOp?] at h
          simp only [run?, applyOp?]
          exact ih _ _ h
      | addScaled dst src negSrc shift =>
          simp only [runConsume?, applyOp?] at h
          simp only [run?, applyOp?]
          exact ih _ _ h
      | phaseProduct i =>
          cases pts with
          | nil => simp [runConsume?] at h
          | cons pt pts =>
              by_cases hm : matchesAt_pointRow_state hk sigma i pt = true
              · simp [runConsume?, hm] at h
                simp only [run?, applyOp?]
                exact ih _ _ h
              · simp [runConsume?, hm] at h

theorem runConsume_consumes {k : Nat} (hk : k > 0) (sigma sigma' : State k)
    (ops : Prog k) (pts : List Point)
    (h : runConsume? hk sigma ops pts = some (sigma', [])) :
    progConsumesPts? hk sigma ops pts = true := by
  induction ops generalizing sigma pts with
  | nil =>
      simp [runConsume?] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | cons op ops ih =>
      cases op with
      | shiftL i n =>
          simp only [runConsume?, applyOp?] at h
          simp only [progConsumesPts?, applyOp?]
          exact ih _ _ h
      | shiftR i n =>
          simp only [runConsume?] at h
          simp only [progConsumesPts?]
          cases hop : applyOp? sigma (.shiftR i n) with
          | none => simp [hop] at h
          | some next =>
              simpa using ih next pts (by simpa [hop] using h)
      | negate i =>
          simp only [runConsume?, applyOp?] at h
          simp only [progConsumesPts?, applyOp?]
          exact ih _ _ h
      | addScaled dst src negSrc shift =>
          simp only [runConsume?, applyOp?] at h
          simp only [progConsumesPts?, applyOp?]
          exact ih _ _ h
      | phaseProduct i =>
          cases pts with
          | nil => simp [runConsume?] at h
          | cons pt pts =>
              by_cases hm : matchesAt_pointRow_state hk sigma i pt = true
              · simp [runConsume?, hm] at h
                simp only [progConsumesPts?]
                rw [hm]
                exact ih _ _ h
              · simp [runConsume?, hm] at h

def executionCheck (mode : ProductMode) (k : Nat) (hk : k >= 2) : Bool :=
  match runConsume? (positive_of_ge_two hk) State.start_state
      (candidateGenerate mode k hk) (candidateGeneratePointsInOrder mode k hk) with
  | some (sigma, []) => statesEqual sigma State.start_state
  | _ => false

def generalChecks (mode : ProductMode) (k : Nat) : Bool :=
  if hk : k >= 2 then
    decide ((generatedPoints mode k).length = mode.pointCount k) &&
      (decide ((generatedPoints mode k).map normalizePoint).Nodup &&
        ((generatedPoints mode k).all validPoint? &&
          (executionCheck mode k hk && safeProg? (candidateGenerate mode k hk))))
  else
    false

def scoredK (k : Nat) : Bool :=
  decide (k = 2) || (decide (k = 3) || (decide (k = 4) || (decide (k = 5) ||
    (decide (k = 6) || (decide (k = 7) || (decide (k = 8) || (decide (k = 9) ||
    (decide (k = 10) || (decide (k = 11) || (decide (k = 12) ||
    (decide (k = 13) || (decide (k = 14) ||
    (decide (k = 15) || decide (k = 16))))))))))))))

def handles (mode : ProductMode) (k : Nat) : Bool :=
  scoredK k || generalChecks mode k

theorem checks_of_generalChecks
    (mode : ProductMode) (k : Nat) (hk : k >= 2)
    (hchecks : generalChecks mode k = true) :
    ValidPointList mode k (generatedPoints mode k) ∧
      (progConsumesPts? (positive_of_ge_two hk) State.start_state
          (candidateGenerate mode k hk) (candidateGeneratePointsInOrder mode k hk) = true ∧
        (safeProg? (candidateGenerate mode k hk) = true ∧
          returnsToStartCheck (candidateGenerate mode k hk) State.start_state = true)) := by
  unfold generalChecks at hchecks
  rw [dif_pos hk] at hchecks
  rcases Bool.and_eq_true_iff.mp hchecks with ⟨hlength, hrest⟩
  rcases Bool.and_eq_true_iff.mp hrest with ⟨hnodup, hrest⟩
  rcases Bool.and_eq_true_iff.mp hrest with ⟨hpoints, hrest⟩
  rcases Bool.and_eq_true_iff.mp hrest with ⟨hexecution, hsafe⟩
  unfold executionCheck at hexecution
  generalize hrun : runConsume? (positive_of_ge_two hk) State.start_state
    (candidateGenerate mode k hk) (candidateGeneratePointsInOrder mode k hk) = result at hexecution
  cases result with
  | none => contradiction
  | some result =>
      rcases result with ⟨sigma, rest⟩
      cases rest with
      | cons _ _ => contradiction
      | nil =>
        have hconsumes := runConsume_consumes (positive_of_ge_two hk)
          State.start_state sigma (candidateGenerate mode k hk)
          (candidateGeneratePointsInOrder mode k hk) hrun
        have hrun' := runConsume_run (positive_of_ge_two hk)
          State.start_state sigma (candidateGenerate mode k hk)
          (candidateGeneratePointsInOrder mode k hk) [] hrun
        have hreturns :
            returnsToStartCheck (candidateGenerate mode k hk) State.start_state = true := by
          simp [returnsToStartCheck, hrun', hexecution]
        exact ⟨⟨of_decide_eq_true hlength, of_decide_eq_true hnodup, hpoints⟩,
          hconsumes, hsafe, hreturns⟩

theorem perm_move_to_front (x : Point) :
    ∀ (pre suffix : List Point),
      (pre ++ x :: suffix).Perm (x :: pre ++ suffix)
  | [], _ => List.Perm.refl _
  | y :: pre, suffix =>
      (List.Perm.cons y (perm_move_to_front x pre suffix)).trans
        (List.Perm.swap x y (pre ++ suffix))

theorem k3Product_order_perm :
    Precomputed.K3Product.orderedPoints.Perm
      (generatedPoints .PhaseProduct 3) := by
  change
    ([.int 1, .int 2, .frac 0, .int (-1), .int 0] : List Point).Perm
      [.int 0, .frac 0, .int 1, .int (-1), .int 2]
  have p1 :
      ([.int 1, .int 2, .frac 0, .int (-1), .int 0] : List Point).Perm
        [.int 0, .int 1, .int 2, .frac 0, .int (-1)] :=
    perm_move_to_front (.int 0) [.int 1, .int 2, .frac 0, .int (-1)] []
  have p2 :
      ([.int 0, .int 1, .int 2, .frac 0, .int (-1)] : List Point).Perm
        [.int 0, .frac 0, .int 1, .int 2, .int (-1)] :=
    List.Perm.cons (.int 0)
      (perm_move_to_front (.frac 0) [.int 1, .int 2] [.int (-1)])
  have p3 :
      ([.int 0, .frac 0, .int 1, .int 2, .int (-1)] : List Point).Perm
        [.int 0, .frac 0, .int 1, .int (-1), .int 2] :=
    List.Perm.cons (Point.int 0) <| List.Perm.cons (Point.frac 0) <|
      List.Perm.cons (Point.int 1) <| List.Perm.swap (Point.int (-1)) (Point.int 2) []
  exact p1.trans (p2.trans p3)

theorem k3TripleProduct_order_perm :
    Precomputed.K3TripleProduct.orderedPoints.Perm
      (generatedPoints .PhaseTripleProduct 3) := by
  change
    ([.int (-2), .int (-1), .frac 0, .int 2, .int 1, .int 0, .frac 2] : List Point).Perm
      [.int 0, .frac 0, .int 1, .int (-1), .int 2, .int (-2), .frac 2]
  have p1 :
      ([.int (-2), .int (-1), .frac 0, .int 2, .int 1, .int 0, .frac 2] : List Point).Perm
        [.int 0, .int (-2), .int (-1), .frac 0, .int 2, .int 1, .frac 2] :=
    perm_move_to_front (.int 0)
      [.int (-2), .int (-1), .frac 0, .int 2, .int 1] [.frac 2]
  have p2 :
      ([.int 0, .int (-2), .int (-1), .frac 0, .int 2, .int 1, .frac 2] : List Point).Perm
        [.int 0, .frac 0, .int (-2), .int (-1), .int 2, .int 1, .frac 2] :=
    List.Perm.cons (Point.int 0) <|
      perm_move_to_front (.frac 0) [.int (-2), .int (-1)] [.int 2, .int 1, .frac 2]
  have p3 :
      ([.int 0, .frac 0, .int (-2), .int (-1), .int 2, .int 1, .frac 2] : List Point).Perm
        [.int 0, .frac 0, .int 1, .int (-2), .int (-1), .int 2, .frac 2] :=
    List.Perm.cons (Point.int 0) <| List.Perm.cons (Point.frac 0) <|
      perm_move_to_front (.int 1) [.int (-2), .int (-1), .int 2] [.frac 2]
  have p4 :
      ([.int 0, .frac 0, .int 1, .int (-2), .int (-1), .int 2, .frac 2] : List Point).Perm
        [.int 0, .frac 0, .int 1, .int (-1), .int (-2), .int 2, .frac 2] :=
    List.Perm.cons (Point.int 0) <| List.Perm.cons (Point.frac 0) <|
      List.Perm.cons (Point.int 1) <|
      perm_move_to_front (.int (-1)) [.int (-2)] [.int 2, .frac 2]
  have p5 :
      ([.int 0, .frac 0, .int 1, .int (-1), .int (-2), .int 2, .frac 2] : List Point).Perm
        [.int 0, .frac 0, .int 1, .int (-1), .int 2, .int (-2), .frac 2] :=
    List.Perm.cons (Point.int 0) <| List.Perm.cons (Point.frac 0) <|
      List.Perm.cons (Point.int 1) <| List.Perm.cons (Point.int (-1)) <|
        perm_move_to_front (.int 2) [.int (-2)] [.frac 2]
  exact p1.trans (p2.trans (p3.trans (p4.trans p5)))

theorem candidate_order_valid
    (mode : ProductMode) (k : Nat) (hk : k >= 2) :
    ValidPointOrder (generatedPoints mode k) (candidateGeneratePointsInOrder mode k hk) := by
  unfold ValidPointOrder
  cases mode with
  | PhaseProduct =>
      if h2 : k = 2 then
        subst k
        have hhk : hk = (by decide : 2 >= 2) := Subsingleton.elim _ _
        subst hk
        exact List.Perm.refl _
      else if h3 : k = 3 then
        subst k
        have hhk : hk = (by decide : 3 >= 2) := Subsingleton.elim _ _
        subst hk
        simpa [candidateGeneratePointsInOrder] using k3Product_order_perm
      else
        simp [candidateGeneratePointsInOrder, h2, h3]
  | PhaseTripleProduct =>
      if h2 : k = 2 then
        subst k
        have hhk : hk = (by decide : 2 >= 2) := Subsingleton.elim _ _
        subst hk
        exact List.Perm.refl _
      else if h3 : k = 3 then
        subst k
        have hhk : hk = (by decide : 3 >= 2) := Subsingleton.elim _ _
        subst hk
        simpa [candidateGeneratePointsInOrder] using k3TripleProduct_order_perm
      else
        simp [candidateGeneratePointsInOrder, h2, h3]

theorem scoredK_cases {k : Nat} (h : scoredK k = true) :
    k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨
      k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨
      k = 15 ∨ k = 16 := by
  simpa [scoredK, Bool.or_eq_true, decide_eq_true_eq] using h

theorem generatedPoints_valid_scored
    (mode : ProductMode) (k : Nat) (h : scoredK k = true) :
    ValidPointList mode k (generatedPoints mode k) := by
  rcases scoredK_cases h with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst k
  all_goals cases mode <;> unfold ValidPointList generatedPoints canonicalPoints <;> decide

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem generate_safe_scored
    (mode : ProductMode) (k : Nat) (hk : k >= 2) (h : scoredK k = true) :
    ValidPointOrder (generatedPoints mode k) (candidateGeneratePointsInOrder mode k hk) ∧
      ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
        (candidateGenerate mode k hk) (candidateGeneratePointsInOrder mode k hk) := by
  rcases scoredK_cases h with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst k
  all_goals
    have hhk : hk = by decide := Subsingleton.elim _ _
    subst hk
    constructor
    · exact candidate_order_valid mode _ _
    · cases mode <;> apply progConsumesPtsSafe_of_checks <;> decide

theorem generatedPoints_valid
    (mode : ProductMode) (k : Nat) (hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointList mode k (generatedPoints mode k) := by
  cases hscored : scoredK k with
  | false =>
      unfold handles at hhandles
      rw [hscored] at hhandles
      exact (checks_of_generalChecks mode k hk hhandles).1
  | true => exact generatedPoints_valid_scored mode k hscored

theorem generate_safe
    (mode : ProductMode) (k : Nat) (hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointOrder (generatedPoints mode k) (candidateGeneratePointsInOrder mode k hk) ∧
      ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
        (candidateGenerate mode k hk) (candidateGeneratePointsInOrder mode k hk) := by
  cases hscored : scoredK k with
  | false =>
      unfold handles at hhandles
      rw [hscored] at hhandles
      rcases checks_of_generalChecks mode k hk hhandles with
        ⟨_, hconsumes, hsafe, hreturns⟩
      exact ⟨candidate_order_valid mode k hk,
        progConsumesPtsSafe_of_checks hconsumes hsafe hreturns⟩
  | true => exact generate_safe_scored mode k hk hscored

def implementation : GeneratorPolicy where
  generatedPoints := generatedPoints
  handles := handles
  generatePointsInOrder := candidateGeneratePointsInOrder
  generate := candidateGenerate
  generatedPoints_valid := generatedPoints_valid
  generate_safe := generate_safe

end TableGeneration.Policies.Accepted.P6f7d25984ff8.GeneralParity
