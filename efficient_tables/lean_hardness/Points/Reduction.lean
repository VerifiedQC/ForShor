import Points.LowerBound
import TableGeneration.ContractSoundness

/-!
# Edge-Hamiltonian path reduces to the points-as-input table problem

`EHP E`: the edges `E` (2-element sets of vertices) can be ordered so that consecutive edges share a
vertex, i.e. the line graph has a Hamiltonian path (Bertossi, IPL 13 (1981) 157–159: NP-complete).

The instance: `k = 2`, points `0` and `lab e = 8^a + 8^b` for `e = {a, b}`, budget `7 (|E| + 1)`.

`reduction_correct : EHP E ↔ GenTableOpt 2 (pointsOf E) (7 * (E.length + 1))`.
-/

namespace Pts

open TableGeneration Operations

/-- The label of an edge. -/
def lab (e : Finset ℕ) : ℤ := oct e ∅

/-- Consecutive edges share a vertex. -/
def AdjChain : List (Finset ℕ) → Prop
  | e :: f :: rest => (e ∩ f).Nonempty ∧ AdjChain (f :: rest)
  | _ => True

/-- **Edge-Hamiltonian path.** -/
def EHP (E : List (Finset ℕ)) : Prop := ∃ L, L.Perm E ∧ AdjChain L

/-- The integer points of the instance. -/
def ptsZ (E : List (Finset ℕ)) : List ℤ := 0 :: E.map lab

def pointsOf (E : List (Finset ℕ)) : List Point := (ptsZ E).map Point.int

/-! ### Label arithmetic -/

lemma oct_empty (A : Finset ℕ) : oct A ∅ = ∑ i ∈ A, (8 : ℤ) ^ i := by simp [oct]

lemma lab_sub (A B : Finset ℕ) : lab A - lab B = oct (A \ B) (B \ A) := by
  simp only [lab, oct_empty, oct]
  rw [← Finset.sum_sdiff (Finset.inter_subset_left : A ∩ B ⊆ A),
    ← Finset.sum_sdiff (Finset.inter_subset_right : A ∩ B ⊆ B)]
  rw [Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right]
  ring

lemma disj_sdiff (A B : Finset ℕ) : Disjoint (A \ B) (B \ A) := disjoint_sdiff_sdiff

lemma card_symm (A B : Finset ℕ) (hA : A.card = 2) (hB : B.card = 2) :
    ((A \ B) ∪ (B \ A)).card = 4 - 2 * (A ∩ B).card := by
  rw [Finset.card_union_of_disjoint (disj_sdiff A B), Finset.card_sdiff, Finset.card_sdiff,
    Finset.inter_comm B A]
  have := Finset.card_le_card (Finset.inter_subset_left : A ∩ B ⊆ A)
  omega

lemma card_inter_lt {A B : Finset ℕ} (hA : A.card = 2) (hB : B.card = 2) (h : A ≠ B) :
    (A ∩ B).card ≤ 1 := by
  by_contra hc
  push Not at hc
  have h1 : A ∩ B = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have h2 : A ∩ B = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact h (h1.symm.trans h2)

lemma notW1_lab_sub {A B : Finset ℕ} (hA : A.card = 2) (hB : B.card = 2) (h : A ≠ B) :
    ¬ W1 (lab A - lab B) := by
  intro hw
  rw [lab_sub] at hw
  have := oct_W1 (disj_sdiff A B) hw
  rw [card_symm A B hA hB] at this
  have := card_inter_lt hA hB h
  omega

lemma notW1_lab {A : Finset ℕ} (hA : A.card = 2) : ¬ W1 (lab A) := by
  intro hw
  have := oct_W1 (Finset.disjoint_empty_right A) hw
  simp [hA] at this

lemma notW1_neg {x : ℤ} (h : ¬ W1 x) : ¬ W1 (-x) := by
  intro hw; apply h
  rcases hw with hw | ⟨s, p, hs, hw⟩
  · left; omega
  · right; exact ⟨-s, p, by rcases hs with rfl | rfl <;> simp, by linarith⟩

lemma W2_lab_sub_iff {A B : Finset ℕ} (hA : A.card = 2) (hB : B.card = 2) :
    W2 (lab A - lab B) → (A ∩ B).Nonempty := by
  intro hw
  rw [lab_sub] at hw
  have := oct_W2 (disj_sdiff A B) hw
  rw [card_symm A B hA hB] at this
  rw [← Finset.card_pos]; omega

lemma lab_ne_zero {A : Finset ℕ} (hA : A.card = 2) : lab A ≠ 0 := fun h =>
  notW1_lab hA (by rw [h]; exact Or.inl rfl)

lemma lab_injOn {A B : Finset ℕ} (hA : A.card = 2) (hB : B.card = 2) (h : lab A = lab B) :
    A = B := by
  by_contra hne
  exact notW1_lab_sub hA hB hne (by rw [h, sub_self]; exact Or.inl rfl)

/-! ### The instance is well formed -/

section Inst

variable {E : List (Finset ℕ)} (hE : E.Nodup) (h2 : ∀ e ∈ E, e.card = 2)
include h2

lemma ptsZ_nodup (hE : E.Nodup) : (ptsZ E).Nodup := by
  refine List.nodup_cons.mpr ⟨fun h => ?_, ?_⟩
  · obtain ⟨e, he, h0⟩ := List.mem_map.mp h
    exact lab_ne_zero (h2 e he) h0
  · exact List.Nodup.map_on (fun a ha b hb h => lab_injOn (h2 a ha) (h2 b hb) h) hE

lemma ptsZ_sep : ∀ x ∈ ptsZ E, ∀ y ∈ ptsZ E, x ≠ y → ¬ W1 (y - x) := by
  intro x hx y hy hxy
  simp only [ptsZ, List.mem_cons, List.mem_map] at hx hy
  rcases hx with rfl | ⟨a, ha, rfl⟩ <;> rcases hy with rfl | ⟨b, hb, rfl⟩
  · exact absurd rfl hxy
  · simpa using notW1_lab (h2 b hb)
  · simpa using notW1_neg (notW1_lab (h2 a ha))
  · exact notW1_lab_sub (h2 b hb) (h2 a ha) (fun h => hxy (by rw [h]))

end Inst

/-! ### The YES direction: an explicit schedule -/

def sv (n : Bool) (p : ℕ) : ℤ := (if n then -1 else 1) * 2 ^ p

/-- A difference realisable by two additions from register 1. -/
def Rep2 (d : ℤ) : Prop := ∃ n1 p1 n2 p2, d = sv n1 p1 + sv n2 p2

def StepsRep2 : List ℤ → Prop
  | x :: y :: rest => Rep2 (y - x) ∧ StepsRep2 (y :: rest)
  | _ => True

/-- Register 0 holds `(1, z)`, register 1 holds `(0, 1)`. -/
def St (z : ℤ) : State 2 := State.setReg State.start_state 0 (row z)

lemma St_zero : St 0 = State.start_state := by
  funext i j; rcases fin2_cases i with rfl | rfl
  · simp [St, State.setReg, start_row0]
  · simp [St, State.setReg]

def mv (n1 : Bool) (p1 : ℕ) (n2 : Bool) (p2 : ℕ) : Prog 2 :=
  [.addScaled 0 1 n1 p1, .addScaled 0 1 n2 p2]

lemma addStep (z : ℤ) (n : Bool) (p : ℕ) :
    applyOp? (St z) (.addScaled 0 1 n p) = some (St (z + sv n p)) := by
  simp only [applyOp?, Option.some.injEq]
  funext i j
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
    simp [St, State.addScaledReg, State.setReg, Register.addScaled, row, expectedRow,
      State.start_state, sv] <;> split_ifs <;> ring

lemma run_mv (z : ℤ) (n1 : Bool) (p1 : ℕ) (n2 : Bool) (p2 : ℕ) (rest : Prog 2) :
    run? (mv n1 p1 n2 p2 ++ rest) (St z) = run? rest (St (z + sv n1 p1 + sv n2 p2)) := by
  simp [mv, run?, addStep]

lemma consumes_mv {hk : 2 > 0} (z : ℤ) (n1 : Bool) (p1 : ℕ) (n2 : Bool) (p2 : ℕ) (rest : Prog 2)
    (pts : List Point) :
    progConsumesPts? hk (St z) (mv n1 p1 n2 p2 ++ rest) pts =
      progConsumesPts? hk (St (z + sv n1 p1 + sv n2 p2)) rest pts := by
  simp [mv, progConsumesPts?, addStep]

lemma St_row (z : ℤ) : St z 0 = row z := by simp [St, State.setReg]

/-- The tour from `(1, z)` through `zs` and back to `0`. -/
theorem tour : ∀ (z : ℤ) (zs : List ℤ), StepsRep2 (z :: zs ++ [0]) →
    ∃ T : Prog 2, progConsumesPts? (by decide : 2 > 0) (St z) T (zs.map Point.int) = true ∧
      run? T (St z) = some State.start_state ∧ Prog.wellFormed? T = true ∧
      arithmeticOperationCount T = 2 * (zs.length + 1) ∧
      ∀ b, parallelPhaseProductLayerCountAux b T = zs.length
  | z, [], h => by
    obtain ⟨⟨n1, p1, n2, p2, hd⟩, -⟩ := h
    refine ⟨mv n1 p1 n2 p2, ?_, ?_, rfl, rfl, fun b => rfl⟩
    · have := consumes_mv (hk := by decide) z n1 p1 n2 p2 [] []
      simp only [List.append_nil] at this
      simp only [List.map_nil]
      rw [this]; rfl
    · have := run_mv z n1 p1 n2 p2 []
      simp only [List.append_nil] at this
      rw [this, show z + sv n1 p1 + sv n2 p2 = 0 by linarith, St_zero]; rfl
  | z, z' :: zs, h => by
    obtain ⟨⟨n1, p1, n2, p2, hd⟩, h'⟩ := h
    obtain ⟨T, hc, hr, hw, ha, hl⟩ := tour z' zs h'
    have hz : z + sv n1 p1 + sv n2 p2 = z' := by linarith
    refine ⟨mv n1 p1 n2 p2 ++ .phaseProduct 0 :: T, ?_, ?_, ?_, ?_, fun b => ?_⟩
    · rw [consumes_mv, hz, List.map_cons]
      simp only [progConsumesPts?, Bool.and_eq_true, matchesAt_pointRow_state, regEqExpected,
        List.all_eq_true, decide_eq_true_eq]
      exact ⟨fun j _ => by rw [St_row]; rfl, hc⟩
    · rw [run_mv, hz]; simpa only [run?, applyOp?] using hr
    · simp [mv, Prog.wellFormed?, Prog.OpOK?, hw]
    · simp [mv, arithmeticOperationCount, ha]; ring
    · simp [mv, parallelPhaseProductLayerCountAux, hl]; ring

theorem schedule (zs : List ℤ) (h : StepsRep2 (0 :: zs ++ [0])) :
    ∃ ops : Prog 2, ProgConsumesPtsSafe (by decide) State.start_state ops ((0 :: zs).map Point.int) ∧
      score ops = 7 * (zs.length + 1) := by
  obtain ⟨T, hc, hr, hw, ha, hl⟩ := tour 0 zs h
  rw [St_zero] at hc hr
  refine ⟨.phaseProduct 0 :: T, progConsumesPtsSafe_of_checks ?_ ?_ ?_, ?_⟩
  · simp only [List.map_cons, progConsumesPts?, Bool.and_eq_true, matchesAt_pointRow_state,
      regEqExpected, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun j _ => by rw [start_row0]; rfl, hc⟩
  · simpa [safeProg?, Prog.wellFormed?, Prog.OpOK?] using hw
  · unfold returnsToStartCheck
    rw [show run? (.phaseProduct 0 :: T) State.start_state = run? T State.start_state by
      simp [run?, applyOp?], hr]
    simp [statesEqual]
  · simp [score, arithmeticOperationCount, parallelPhaseProductLayerCount,
      parallelPhaseProductLayerCountAux, ha, hl]
    ring

/-! ### Edges sharing a vertex step by `Rep2` -/

lemma pow8 (a : ℕ) : (8 : ℤ) ^ a = 2 ^ (3 * a) := by rw [pow_mul]; norm_num

lemma lab_pair {a b : ℕ} (hab : a ≠ b) : lab {a, b} = 8 ^ a + 8 ^ b := by
  simp [lab, oct_empty, Finset.sum_pair hab]

lemma rep2_lab {e : Finset ℕ} (he : e.card = 2) : Rep2 (lab e - 0) ∧ Rep2 (0 - lab e) := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he
  rw [lab_pair hab]
  exact ⟨⟨false, 3 * a, false, 3 * b, by simp [sv, pow8]⟩,
    ⟨true, 3 * a, true, 3 * b, by simp [sv, pow8]; ring⟩⟩

lemma rep2_share {e f : Finset ℕ} (he : e.card = 2) (hf : f.card = 2) (hne : e ≠ f)
    (h : (e ∩ f).Nonempty) : Rep2 (lab f - lab e) := by
  obtain ⟨v, hv⟩ := h
  rw [Finset.mem_inter] at hv
  obtain ⟨x, hvx, hex⟩ : ∃ x, v ≠ x ∧ e = {v, x} := by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv.1 with rfl | rfl
    · exact ⟨b, hab, rfl⟩
    · exact ⟨a, Ne.symm hab, Finset.pair_comm _ _⟩
  obtain ⟨y, hvy, hfy⟩ : ∃ y, v ≠ y ∧ f = {v, y} := by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv.2 with rfl | rfl
    · exact ⟨b, hab, rfl⟩
    · exact ⟨a, Ne.symm hab, Finset.pair_comm _ _⟩
  subst hex hfy
  rw [lab_pair hvx, lab_pair hvy]
  exact ⟨false, 3 * y, true, 3 * x, by simp [sv, pow8]; ring⟩

/-! ### Lists -/

lemma exists_perm_map {f : Finset ℕ → ℤ} :
    ∀ {R : List ℤ} {E : List (Finset ℕ)}, R.Perm (E.map f) →
      ∃ L : List (Finset ℕ), L.Perm E ∧ L.map f = R
  | [], E, h => by
    have : E = [] := by simpa using h.symm.eq_nil
    exact ⟨[], by simp [this], rfl⟩
  | x :: R, E, h => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (h.subset (List.mem_cons_self ..))
    have hp : (E.map f).Perm ((e :: E.erase e).map f) := (List.perm_cons_erase he).map f
    have h' : R.Perm ((E.erase e).map f) := (h.trans hp).cons_inv
    obtain ⟨L, hL, hLf⟩ := exists_perm_map h'
    exact ⟨e :: L, (hL.cons e).trans (List.perm_cons_erase he).symm, by simp [hLf]⟩

lemma adj_of_steps {L : List (Finset ℕ)} (hnd : L.Nodup) (h2 : ∀ e ∈ L, e.card = 2)
    (h : StepsW2 (L.map lab)) : AdjChain L := by
  induction L with
  | nil => trivial
  | cons e L ih =>
    match L, hnd, h2, h, ih with
    | [], _, _, _, _ => trivial
    | f :: L', hnd, h2, h, ih =>
      refine ⟨?_, ih hnd.of_cons (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) h.2⟩
      have := W2_lab_sub_iff (h2 f (by simp)) (h2 e (by simp)) h.1
      rwa [Finset.inter_comm]

lemma steps_of_adj : ∀ {L : List (Finset ℕ)}, L.Nodup → (∀ e ∈ L, e.card = 2) → AdjChain L →
    ∀ z, (∀ e ∈ L.head?, Rep2 (lab e - z)) → (L = [] → Rep2 (0 - z)) →
      StepsRep2 (z :: L.map lab ++ [0])
  | [], _, _, _, z, _, h0 => ⟨h0 rfl, trivial⟩
  | [e], _, h2, _, z, hz, _ => ⟨hz e rfl, (rep2_lab (h2 e (by simp))).2, trivial⟩
  | e :: f :: L, hnd, h2, ⟨hef, hadj⟩, z, hz, _ => by
    refine ⟨hz e rfl, ?_⟩
    have := steps_of_adj (L := f :: L) hnd.of_cons (fun x hx => h2 x (List.mem_cons_of_mem _ hx))
      hadj (lab e) (fun g hg => by
        simp at hg; subst hg
        exact rep2_share (h2 e (by simp)) (h2 f (by simp))
          (fun h => (List.nodup_cons.mp hnd).1 (by simp [h])) hef) (by simp)
    simpa using this

/-! ### The reduction -/

theorem reduction_correct {E : List (Finset ℕ)} (hE : E.Nodup) (h2 : ∀ e ∈ E, e.card = 2) :
    EHP E ↔ GenTableOpt 2 (pointsOf E) (7 * (E.length + 1)) := by
  constructor
  · rintro ⟨L, hL, hadj⟩
    have hLnd : L.Nodup := hL.nodup_iff.mpr hE
    have hL2 : ∀ e ∈ L, e.card = 2 := fun e he => h2 e (hL.subset he)
    have hst := steps_of_adj hLnd hL2 hadj 0 (fun e he => by
      have := (rep2_lab (hL2 e (List.mem_of_mem_head? he))).1; simpa using this)
      (fun _ => ⟨false, 0, true, 0, by simp [sv]⟩)
    obtain ⟨ops, hsafe, hscore⟩ := schedule (L.map lab) (by simpa using hst)
    refine ⟨by decide, (List.nodup_map_iff fun a b h => Operations.Point.int.inj h).mpr (ptsZ_nodup h2 hE),
      _, ops, ?_, hsafe, ?_⟩
    · exact (((hL.map lab).cons 0).map Point.int)
    · simp [hscore, hL.length_eq]
  · rintro ⟨_, _, order, ops, hperm, hsafe, hscore⟩
    -- decode the order
    let getI : Point → ℤ := fun | .int z => z | .frac _ => 0
    set O := order.map getI with hO
    have hOperm : O.Perm (ptsZ E) := by
      have := hperm.map getI
      simpa [pointsOf, getI, List.map_map, Function.comp_def] using this
    have horder : order = O.map Point.int := by
      rw [hO, List.map_map]
      conv_lhs => rw [← List.map_id order]
      apply List.map_congr_left
      intro x hx
      obtain ⟨z, -, rfl⟩ := List.mem_map.mp (hperm.subset hx)
      rfl
    have hOnd : O.Nodup := hOperm.nodup_iff.mpr (ptsZ_nodup h2 hE)
    -- the lower bound
    have hb := run_bound {x | x ∈ ptsZ E} (fun x hx y hy => ptsZ_sep h2 x hx y hy) (by simp [ptsZ])
      ops State.start_state State.start_state C0 0 false 0 0 O start_row0 detOK_start detOK_start
      (rep_self _) rfl (by simp [ptsZ]) (fun p hp => hOperm.subset hp) hOnd (by simp)
      hsafe.safe_add (by rw [← horder]; exact hsafe.consumes)
      ((returnsToStartCheck_iff _ _).mp hsafe.returns_start)
    have hcost : chain 0 O ≤ 7 * O.length := by
      rw [hOperm.length_eq]
      simp only [ptsZ, List.length_cons, List.length_map]
      unfold score parallelPhaseProductLayerCount at hscore
      omega
    obtain ⟨R, hR, hsteps⟩ := extract hOnd (hOperm.symm.subset (by simp [ptsZ])) hcost
    -- the rest of the order is a permutation of the labels
    have hRperm : R.Perm (E.map lab) := by
      rcases hR with hR | hR
      · rw [hR] at hOperm; exact hOperm.cons_inv
      · rw [hR] at hOperm
        exact (List.perm_append_singleton _ _).symm.trans hOperm |>.cons_inv
    obtain ⟨L, hL, rfl⟩ := exists_perm_map hRperm
    have hLnd : L.Nodup := hL.nodup_iff.mpr hE
    exact ⟨L, hL, adj_of_steps hLnd (fun e he => h2 e (hL.subset he)) hsteps⟩

end Pts
