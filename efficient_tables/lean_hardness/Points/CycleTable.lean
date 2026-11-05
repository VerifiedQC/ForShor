import Points.Reduction

/-!
# The cycle version: Hamiltonian cycles of a line graph and the table problem

`EHC E`: the edges `E` can be arranged in a cycle with consecutive edges sharing a vertex
(a Hamiltonian cycle of the line graph). Translating all labels by the first edge's label makes
that edge the start state's point `0`, and the table instance then asks exactly for such a cycle:

`cycle_reduction : EHC E ↔ GenTableOpt 2 (pointsC E) (7 * E.length)`.
-/

namespace Pts

open TableGeneration Operations

/-! ### Chains -/

/-- Consecutive entries are related. -/
def Chn {α : Type*} (R : α → α → Prop) : List α → Prop
  | x :: y :: rest => R x y ∧ Chn R (y :: rest)
  | _ => True

section ChnLemmas
variable {α β : Type*} {R S : α → α → Prop}

@[simp] lemma chn_nil : Chn R [] := trivial
@[simp] lemma chn_single (a : α) : Chn R [a] := trivial
@[simp] lemma chn_cons_cons (a b : α) (l : List α) : Chn R (a :: b :: l) ↔ R a b ∧ Chn R (b :: l) :=
  Iff.rfl

lemma chn_cons {a : α} {l : List α} :
    Chn R (a :: l) ↔ (∀ b ∈ l.head?, R a b) ∧ Chn R l := by
  cases l <;> simp

lemma chn_append {X Y : List α} :
    Chn R (X ++ Y) ↔ Chn R X ∧ Chn R Y ∧ ∀ x ∈ X.getLast?, ∀ y ∈ Y.head?, R x y := by
  induction X with
  | nil => simp
  | cons a X ih =>
    cases X with
    | nil =>
      simp only [List.cons_append, List.nil_append, chn_cons, chn_single, true_and,
        List.getLast?_singleton, Option.mem_def, Option.some.injEq, forall_eq']
      tauto
    | cons b X =>
      simp only [List.cons_append, chn_cons_cons] at ih ⊢
      rw [ih]
      simp only [List.getLast?_cons_cons]
      tauto

lemma chn_map (f : β → α) {l : List β} : Chn R (l.map f) ↔ Chn (fun a b => R (f a) (f b)) l := by
  induction l with
  | nil => simp
  | cons a l ih => cases l with
    | nil => simp
    | cons b l => simp only [List.map_cons, chn_cons_cons] at ih ⊢; rw [ih]

lemma chn_mono_on {P : α → Prop} {l : List α} (hl : Chn R l) (hP : ∀ x ∈ l, P x)
    (h : ∀ a b, P a → P b → R a b → S a b) : Chn S l := by
  induction l with
  | nil => trivial
  | cons a l ih => cases l with
    | nil => trivial
    | cons b l =>
      exact ⟨h a b (hP a (by simp)) (hP b (by simp)) hl.1,
        ih hl.2 (fun x hx => hP x (List.mem_cons_of_mem _ hx))⟩

end ChnLemmas

lemma stepsW2_iff {L : List ℤ} : StepsW2 L ↔ Chn (fun x y => W2 (y - x)) L := by
  induction L with
  | nil => exact Iff.rfl
  | cons a L ih => cases L with
    | nil => exact Iff.rfl
    | cons b L => exact and_congr Iff.rfl ih

lemma stepsRep2_iff {L : List ℤ} : StepsRep2 L ↔ Chn (fun x y => Rep2 (y - x)) L := by
  induction L with
  | nil => exact Iff.rfl
  | cons a L ih => cases L with
    | nil => exact Iff.rfl
    | cons b L => exact and_congr Iff.rfl ih

/-! ### Cyclic adjacency -/

def Adj (e f : Finset ℕ) : Prop := (e ∩ f).Nonempty

/-- The list, read cyclically, has consecutive edges sharing a vertex. -/
def CycAdj (L : List (Finset ℕ)) : Prop := Chn Adj (L ++ L.take 1)

/-- **Edge-Hamiltonian cycle**: a Hamiltonian cycle of the line graph. -/
def EHC (E : List (Finset ℕ)) : Prop := ∃ L, L.Perm E ∧ CycAdj L

lemma cycAdj_rot {A B : List (Finset ℕ)} {e : Finset ℕ} (h : CycAdj (A ++ e :: B)) :
    CycAdj (e :: (B ++ A)) := by
  cases A with
  | nil => simpa [CycAdj] using h
  | cons a A =>
    unfold CycAdj at h ⊢
    simp only [List.cons_append, List.take_succ_cons, List.take_zero] at h ⊢
    -- h : Chn Adj (a :: (A ++ e :: B ++ [a]))
    have h' : Chn Adj ((a :: A) ++ ((e :: B) ++ [a])) := by simpa using h
    rw [chn_append, chn_append] at h'
    obtain ⟨h1, ⟨h2, -, h23⟩, h12⟩ := h'
    have goal : Chn Adj ((e :: B) ++ ((a :: A) ++ [e])) := by
      rw [chn_append, chn_append]
      refine ⟨h2, ⟨h1, by simp, ?_⟩, ?_⟩
      · intro x hx y hy
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        have := h12 x hx e (by simp)
        exact this
      · intro x hx y hy
        obtain rfl : a = y := by simpa using hy
        exact h23 x hx a (by simp)
    simpa using goal

/-! ### The instance -/

/-- Labels translated by the first edge's label. -/
def dl (e0 e : Finset ℕ) : ℤ := lab e - lab e0

def ptsC (E : List (Finset ℕ)) : List ℤ := E.map (dl (E.headD ∅))

def pointsC (E : List (Finset ℕ)) : List Point := (ptsC E).map Point.int

lemma W2_adj {e f : Finset ℕ} (he : e.card = 2) (hf : f.card = 2) (h : W2 (lab f - lab e)) :
    Adj e f := by
  have := W2_lab_sub_iff hf he h
  unfold Adj; rwa [Finset.inter_comm]

lemma rep2_adj {e f : Finset ℕ} (he : e.card = 2) (hf : f.card = 2) (h : Adj e f) :
    Rep2 (lab f - lab e) := by
  by_cases hef : e = f
  · subst hef; exact ⟨false, 0, true, 0, by simp [sv]⟩
  · exact rep2_share he hf hef h

/-- The extraction lemma keeping the closing steps through `0`. -/
theorem extract_cycle {O : List ℤ} (hnd : O.Nodup) (h0 : (0 : ℤ) ∈ O)
    (hcost : chain 0 O ≤ 7 * O.length) :
    ∃ R, (O = 0 :: R ∨ O = R ++ [0]) ∧ StepsW2 (0 :: R ++ [0]) := by
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
  · subst hR1; subst hR2
    refine ⟨[], Or.inl rfl, ?_⟩
    exact ⟨W1.W2 (Or.inl (by simp)), trivial⟩
  · subst hR1
    obtain ⟨g1, g2⟩ := pathCost_ge R2 0 0 h2nd h02 h02 (Or.inl hR2)
    simp only [pathCost, cst_self, List.length_nil] at hcost
    exact ⟨R2, Or.inl rfl, g2 (by omega)⟩
  · subst hR2
    obtain ⟨g1, g2⟩ := pathCost_ge R1 0 0 h1nd h01 h01 (Or.inl hR1)
    simp only [pathCost, cst_self, List.length_nil] at hcost
    exact ⟨R1, Or.inr rfl, g2 (by omega)⟩
  · obtain ⟨g1, _⟩ := pathCost_ge R1 0 0 h1nd h01 h01 (Or.inl hR1)
    obtain ⟨g3, _⟩ := pathCost_ge R2 0 0 h2nd h02 h02 (Or.inl hR2)
    omega

/-! ### The reduction -/

theorem cycle_reduction {E : List (Finset ℕ)} (hE : E.Nodup) (h2 : ∀ e ∈ E, e.card = 2) :
    EHC E ↔ GenTableOpt 2 (pointsC E) (7 * E.length) := by
  cases E with
  | nil =>
    simp only [List.length_nil, mul_zero]
    refine ⟨fun _ => ⟨by decide, by simp [pointsC, ptsC], [], [], by simp [pointsC, ptsC],
      progConsumesPtsSafe_of_checks rfl rfl ?_, le_refl _⟩, fun _ => ⟨[], List.Perm.refl _, trivial⟩⟩
    simp [returnsToStartCheck, run?, statesEqual]
  | cons e0 E' =>
    have hdl0 : dl e0 e0 = 0 := sub_self _
    have hpts : ptsC (e0 :: E') = 0 :: E'.map (dl e0) := by simp [ptsC, hdl0]
    have hnd : (ptsC (e0 :: E')).Nodup := by
      simp only [ptsC, List.headD_cons]
      exact List.Nodup.map_on (fun a ha b hb h => lab_injOn (h2 a ha) (h2 b hb)
        (by simpa [dl] using h)) hE
    have hsep : ∀ x ∈ ptsC (e0 :: E'), ∀ y ∈ ptsC (e0 :: E'), x ≠ y → ¬ W1 (y - x) := by
      intro x hx y hy hxy
      simp only [ptsC, List.headD_cons, List.mem_map] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have hab : b ≠ a := fun h => hxy (by rw [h])
      simpa [dl] using notW1_lab_sub (h2 b hb) (h2 a ha) hab
    constructor
    · rintro ⟨L, hL, hcyc⟩
      obtain ⟨A, B, rfl⟩ := List.append_of_mem (hL.symm.subset (List.mem_cons_self ..))
      have hrot := cycAdj_rot hcyc
      set M := B ++ A
      have hMperm : (e0 :: M).Perm (e0 :: E') :=
        ((List.perm_append_comm.cons e0).trans List.perm_middle.symm).trans hL
      have hM2 : ∀ x ∈ e0 :: M ++ [e0], x.card = 2 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact h2 x (hMperm.subset hx)
        · simp at hx; subst hx; exact h2 _ (by simp)
      have hchain : Chn Adj (e0 :: M ++ [e0]) := by simpa [CycAdj] using hrot
      have hsteps : StepsRep2 (0 :: (M.map (dl e0)) ++ [0]) := by
        rw [stepsRep2_iff]
        have : (0 :: (M.map (dl e0)) ++ [0]) = (e0 :: M ++ [e0]).map (dl e0) := by simp [hdl0]
        rw [this, chn_map]
        refine chn_mono_on hchain hM2 (fun a b ha hb hab => ?_)
        simpa [dl] using rep2_adj ha hb hab
      obtain ⟨ops, hsafe, hscore⟩ := schedule (M.map (dl e0)) hsteps
      refine ⟨by decide, (List.nodup_map_iff fun a b h => Point.int.inj h).mpr hnd, _, ops, ?_, hsafe, ?_⟩
      · rw [pointsC, hpts]
        simpa [hdl0] using (hMperm.map (dl e0)).map Point.int
      · rw [hscore]
        have := hMperm.length_eq
        simp only [List.length_cons] at this
        simp; omega
    · rintro ⟨_, _, order, ops, hperm, hsafe, hscore⟩
      let getI : Point → ℤ := fun | .int z => z | .frac _ => 0
      set O := order.map getI with hO
      have hOperm : O.Perm (ptsC (e0 :: E')) := by
        have := hperm.map getI
        simpa [pointsC, getI, List.map_map, Function.comp_def] using this
      have horder : order = O.map Point.int := by
        rw [hO, List.map_map]
        conv_lhs => rw [← List.map_id order]
        apply List.map_congr_left
        intro x hx
        obtain ⟨z, -, rfl⟩ := List.mem_map.mp (hperm.subset hx)
        rfl
      have hOnd : O.Nodup := hOperm.nodup_iff.mpr hnd
      have h0O : (0 : ℤ) ∈ O := hOperm.symm.subset (by rw [hpts]; simp)
      have hb := run_bound {x | x ∈ ptsC (e0 :: E')} (fun x hx y hy => hsep x hx y hy)
        (by rw [Set.mem_setOf_eq, hpts]; simp)
        ops State.start_state State.start_state C0 0 false 0 0 O start_row0 detOK_start
        detOK_start (rep_self _) rfl (by rw [Set.mem_setOf_eq, hpts]; simp)
        (fun p hp => hOperm.subset hp) hOnd (by simp)
        hsafe.safe_add (by rw [← horder]; exact hsafe.consumes)
        ((returnsToStartCheck_iff _ _).mp hsafe.returns_start)
      have hcost : chain 0 O ≤ 7 * O.length := by
        rw [hOperm.length_eq]
        simp only [ptsC, List.length_map]
        unfold score parallelPhaseProductLayerCount at hscore
        omega
      obtain ⟨R, hR, hsteps⟩ := extract_cycle hOnd h0O hcost
      have hRperm : R.Perm (E'.map (dl e0)) := by
        rw [hpts] at hOperm
        rcases hR with hR | hR
        · rw [hR] at hOperm; exact hOperm.cons_inv
        · rw [hR] at hOperm
          exact ((List.perm_append_singleton _ _).symm.trans hOperm).cons_inv
      obtain ⟨L', hL', rfl⟩ := exists_perm_map hRperm
      refine ⟨e0 :: L', hL'.cons e0, ?_⟩
      have hL2 : ∀ x ∈ e0 :: L' ++ [e0], x.card = 2 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact h2 _ (by simp)
          · exact h2 x (List.mem_cons_of_mem _ (hL'.subset hx))
        · simp at hx; subst hx; exact h2 _ (by simp)
      rw [stepsW2_iff] at hsteps
      have : (0 :: (L'.map (dl e0)) ++ [0]) = (e0 :: L' ++ [e0]).map (dl e0) := by simp [hdl0]
      rw [this, chn_map] at hsteps
      have hc : Chn Adj (e0 :: L' ++ [e0]) :=
        chn_mono_on hsteps hL2 (fun a b ha hb hab => W2_adj ha hb (by simpa [dl] using hab))
      simpa [CycAdj] using hc

end Pts
