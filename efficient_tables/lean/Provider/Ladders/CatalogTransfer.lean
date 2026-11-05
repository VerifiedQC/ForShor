import PhaseProduct.Catalog.EndToEnd

/-!
# Transfer of the catalogue to raw F2 sources

Defines the raw ladder source tables `F2Source` over the fixed point order
`f2Point`, the extra evidence `F2Certificate` needed to run one as a verified
candidate (`F2Source.toVerified`), and the raw benchmark problem `rawProblem`.
It also states conditional finite-catalogue coverage through the structure
`CompleteProvider` and the cost lemma `cost_relevant` for relevant tables.
-/

namespace Paper.F2CatalogTransfer

open Coupled.Formal
open Paper.PPEndToEnd

/-- The fixed F2 order is only a way to enumerate the required set. Marker
execution may use any permutation. `frac z` denotes the repository row for
1/z; in particular `frac 0` is infinity. -/
def f2Point : Nat → TableGeneration.Operations.Point
  | 0 => .int 0
  | 1 => .frac 0
  | 2 => .int (-1)
  | 3 => .int 1
  | n + 4 =>
      let e := 1 + n / 4
      match n % 4 with
      | 0 => .frac (-((2 : Int) ^ e))
      | 1 => .frac ((2 : Int) ^ e)
      | 2 => .int (-((2 : Int) ^ e))
      | _ => .int ((2 : Int) ^ e)

def f2Points (k : Nat) : List TableGeneration.Operations.Point :=
  (List.range (2 * k - 1)).map f2Point

/-- Legal original source table. The full source program and ordered markers
are retained; only its marker *set* is fixed. `safe` checks legal integer
operations, ordered consumption, and restoration in the source semantics.
There is no interpolation certificate in this raw optimization domain. -/
structure F2Source (K : Nat) where
  source : TableGeneration.RecursiveCost.Candidate
  cap : source.k ≤ K
  points : Fin (2 * (source.k - 1) + 1) → TableGeneration.Operations.Point
  safe : TableGeneration.ProgConsumesPtsSafe
    (TableGeneration.positive_of_ge_two source.hk)
    TableGeneration.State.start_state source.program (List.ofFn points)
  literalF2 : (List.ofFn points).Perm (f2Points source.k)

def F2Source.arity {K : Nat} (t : F2Source K) : Nat := t.source.k

def F2Source.childWidth {K : Nat} (t : F2Source K) (w : Nat) : Nat :=
  TableGeneration.RecursiveCost.nextBalancedSignedWidth w t.source.program

def F2Source.charge {K : Nat} (t : F2Source K) : Nat :=
  chargedCount t.source.program

def F2Source.calls {K : Nat} (t : F2Source K) : Nat :=
  2 * (t.arity - 1) + 1

/-- Additional algebraic evidence needed to run a raw F2 source table as a
semantic `VerifiedPPCandidate`. Existence is not asserted for every raw table. -/
structure F2Certificate {K : Nat} (t : F2Source K) where
  weights : (W : Nat) → Fin (2 * (t.source.k - 1) + 1) → ℚ
  certificate : ∀ W, Paper.PhaseIdentity.PairCertificate (weights W)
    (Paper.GenericPhase.indexedSourceRows (k := t.source.k) t.points)
    (fun j : Fin t.source.k => (Paper.SignedLimbs.radix W t.source.k : ℚ) ^ j.val)

def F2Source.toVerified {K : Nat} (t : F2Source K)
    (cert : F2Certificate t) : VerifiedPPCandidate K where
  source := t.source
  cap := t.cap
  points := t.points
  safe := t.safe
  weights := cert.weights
  certificate := cert.certificate

def VerifiedLiteralF2 {K : Nat} (t : VerifiedPPCandidate K) : Prop :=
  (List.ofFn t.points).Perm (f2Points t.source.k)

theorem toVerified_literal {K : Nat} (t : F2Source K)
    (cert : F2Certificate t) : VerifiedLiteralF2 (t.toVerified cert) :=
  t.literalF2

/-- The original benchmark domain uses the source scanner and exact charged
instruction count. Its leaf price is arbitrary. -/
def rawProblem {K : Nat} (price : Nat → Nat) : Prob (F2Source K) where
  child := F2Source.childWidth
  own := fun t _ w => ownPP t.charge w
  calls := F2Source.calls
  leaf := leafPP price

/-- Only tables that contract at some width below the root can be used. -/
def Relevant {K : Nat} (root : Nat) (t : F2Source K) : Prop :=
  ∃ w, w ≤ root ∧ t.childWidth w < w

/-- Conditional finite catalog coverage at a fixed root width. Each relevant
table has one representative with the same entire width function and no greater
charge. Every catalog entry itself belongs to the literal F2 domain. -/
structure CompleteProvider {K : Nat} {ι : Type} (root : Nat)
    (entry : ι → VerifiedPPCandidate K) (catalog : List ι) where
  pick : F2Source K → ι
  catalog_literal : ∀ c ∈ catalog, VerifiedLiteralF2 (entry c)
  member : ∀ t, Relevant root t → pick t ∈ catalog
  arity : ∀ t, Relevant root t → (entry (pick t)).arity = t.arity
  width : ∀ t, Relevant root t → ∀ w, (entry (pick t)).childWidth w = t.childWidth w
  charge : ∀ t, Relevant root t →
    chargedCount (entry (pick t)).source.program ≤ t.charge

theorem cost_relevant {K : Nat} {l : List (F2Source K)}
    {w N v : Nat} (price : Nat → Nat)
    (h : CostL (rawProblem price) l w N v) :
    ∀ t ∈ l, Relevant w t := by
  induction h with
  | base w N =>
      intro t ht
      simp at ht
  | step c rest w N v hc hchild ih =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | htail
      · exact ⟨w, le_rfl, hc⟩
      · obtain ⟨x, hx, hcon⟩ := ih t htail
        exact ⟨x, hx.trans (Nat.le_of_lt hc), hcon⟩

def rawWidths {K : Nat} : List (F2Source K) → Nat → List Nat
  | [], w => [w]
  | t :: rest, w => w :: rawWidths rest (t.childWidth w)

def catalogWidths {K : Nat} {ι : Type} (entry : ι → VerifiedPPCandidate K) :
    List ι → Nat → List Nat
  | [], w => [w]
  | c :: rest, w => w :: catalogWidths entry rest ((entry c).childWidth w)

def rawStates {K : Nat} : List (F2Source K) → Nat → Nat → List (Nat × Nat)
  | [], w, N => [(w, N)]
  | t :: rest, w, N => (w, N) :: rawStates rest (t.childWidth w) (N * t.calls)

def catalogStates {K : Nat} {ι : Type} (entry : ι → VerifiedPPCandidate K) :
    List ι → Nat → Nat → List (Nat × Nat)
  | [], w, N => [(w, N)]
  | c :: rest, w, N =>
      (w, N) :: catalogStates entry rest ((entry c).childWidth w) (N * (entry c).calls)

def rawResidues {K : Nat} : List (F2Source K) → Nat → List Nat
  | [], _ => []
  | t :: rest, w => w % t.arity :: rawResidues rest (t.childWidth w)

def catalogResidues {K : Nat} {ι : Type} (entry : ι → VerifiedPPCandidate K) :
    List ι → Nat → List Nat
  | [], _ => []
  | c :: rest, w => w % (entry c).arity ::
      catalogResidues entry rest ((entry c).childWidth w)

theorem replacement_widths {K : Nat} {ι : Type}
    (entry : ι → VerifiedPPCandidate K) (catalog : List ι)
    (root : Nat) (provider : CompleteProvider root entry catalog)
    (l : List (F2Source K)) (w : Nat)
    (hrel : ∀ t ∈ l, Relevant root t) :
    catalogWidths entry (l.map provider.pick) w = rawWidths l w := by
  induction l generalizing w with
  | nil => rfl
  | cons t rest ih =>
      have ht := hrel t List.mem_cons_self
      have hr : ∀ u ∈ rest, Relevant root u := by
        intro u hu
        exact hrel u (List.mem_cons_of_mem _ hu)
      simp only [List.map_cons, catalogWidths, rawWidths]
      rw [provider.width t ht w]
      exact congrArg (w :: ·) (ih (t.childWidth w) hr)

theorem replacement_states {K : Nat} {ι : Type}
    (entry : ι → VerifiedPPCandidate K) (catalog : List ι)
    (root : Nat) (provider : CompleteProvider root entry catalog)
    (l : List (F2Source K)) (w N : Nat)
    (hrel : ∀ t ∈ l, Relevant root t) :
    catalogStates entry (l.map provider.pick) w N = rawStates l w N := by
  induction l generalizing w N with
  | nil => rfl
  | cons t rest ih =>
      have ht := hrel t List.mem_cons_self
      have hr : ∀ u ∈ rest, Relevant root u := by
        intro u hu
        exact hrel u (List.mem_cons_of_mem _ hu)
      have hw := provider.width t ht w
      have hn : (entry (provider.pick t)).calls = t.calls := by
        simpa only [VerifiedPPCandidate.calls, F2Source.calls, F2Source.arity]
          using congrArg (fun k => 2 * (k - 1) + 1) (provider.arity t ht)
      simp only [List.map_cons, catalogStates, rawStates]
      rw [hw, hn]
      exact congrArg ((w, N) :: ·) (ih (t.childWidth w) (N * t.calls) hr)

theorem replacement_residues {K : Nat} {ι : Type}
    (entry : ι → VerifiedPPCandidate K) (catalog : List ι)
    (root : Nat) (provider : CompleteProvider root entry catalog)
    (l : List (F2Source K)) (w : Nat)
    (hrel : ∀ t ∈ l, Relevant root t) :
    catalogResidues entry (l.map provider.pick) w = rawResidues l w := by
  induction l generalizing w with
  | nil => rfl
  | cons t rest ih =>
      have ht := hrel t List.mem_cons_self
      have hr : ∀ u ∈ rest, Relevant root u := by
        intro u hu
        exact hrel u (List.mem_cons_of_mem _ hu)
      simp only [List.map_cons, catalogResidues, rawResidues]
      rw [provider.arity t ht, provider.width t ht w]
      exact congrArg (w % t.arity :: ·) (ih (t.childWidth w) hr)

theorem replacement_shared {K : Nat} {ι : Type}
    (entry : ι → VerifiedPPCandidate K) (catalog : List ι)
    (root : Nat) (provider : CompleteProvider root entry catalog)
    (l : List (F2Source K))
    (hrel : ∀ t ∈ l, Relevant root t)
    (hshared : ArityInj F2Source.arity l) :
    ArityInj (fun c => (entry c).arity) (l.map provider.pick) := by
  intro c hc d hd heq
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hd
  have htu : t.arity = u.arity := by
    simpa only [provider.arity t (hrel t ht), provider.arity u (hrel u hu)]
      using heq
  rw [hshared t ht u hu htu]

theorem replacement_cost {K : Nat} {ι : Type}
    (entry : ι → VerifiedPPCandidate K) (catalog : List ι)
    (root : Nat) (provider : CompleteProvider root entry catalog)
    (price : Nat → Nat) {l : List (F2Source K)} {w N v : Nat}
    (h : CostL (rawProblem price) l w N v)
    (hrel : ∀ t ∈ l, Relevant root t) :
    ∃ v', CostL (ppProblem price entry) (l.map provider.pick) w N v' ∧ v' ≤ v := by
  induction h with
  | base w N =>
      exact ⟨leafPP price N w, CostL.base w N, le_rfl⟩
  | step t rest w N v hcontract hchild ih =>
      have ht := hrel t List.mem_cons_self
      have hr : ∀ u ∈ rest, Relevant root u := by
        intro u hu
        exact hrel u (List.mem_cons_of_mem _ hu)
      obtain ⟨v', hrec, hle⟩ := ih hr
      have hw : (entry (provider.pick t)).childWidth w = t.childWidth w :=
        provider.width t ht w
      have hn : (entry (provider.pick t)).calls = t.calls := by
        simpa only [VerifiedPPCandidate.calls, F2Source.calls, F2Source.arity]
          using congrArg (fun k => 2 * (k - 1) + 1) (provider.arity t ht)
      have hown : ownPP (chargedCount (entry (provider.pick t)).source.program)
          (t.childWidth w) ≤ ownPP t.charge (t.childWidth w) := by
        unfold ownPP
        exact Nat.mul_le_mul_left 4
          (Nat.mul_le_mul_left (2 * (t.childWidth w - 1)) (provider.charge t ht))
      refine ⟨N * ownPP (chargedCount (entry (provider.pick t)).source.program)
          (t.childWidth w) + v', ?_, ?_⟩
      · have hc : (entry (provider.pick t)).childWidth w < w := by
          rw [hw]
          exact hcontract
        have hrec' : CostL (ppProblem price entry) (rest.map provider.pick)
            ((entry (provider.pick t)).childWidth w)
            (N * (entry (provider.pick t)).calls) v' := by
          rw [hw, hn]
          exact hrec
        simpa only [List.map_cons, ppProblem, hw] using
          CostL.step (provider.pick t) (rest.map provider.pick) w N v' hc hrec'
      · exact Nat.add_le_add (Nat.mul_le_mul_left N hown) hle

theorem selected_le_all_raw {K : Nat} {ι : Type} [DecidableEq ι]
    (price : Nat → Nat) (entry : ι → VerifiedPPCandidate K)
    (catalog : List ι) (W N : Nat)
    (provider : CompleteProvider W entry catalog)
    (l : List (F2Source K)) (v : Nat)
    (hshared : ArityInj F2Source.arity l)
    (hcost : CostL (rawProblem price) l W N v) :
    Paper.PolicyOptimality.chosenCost (ppProblem price entry) catalog
      (fun c => (entry c).arity) K W N ≤ v := by
  have hrel := cost_relevant price hcost
  obtain ⟨v', hcat, hle⟩ :=
    replacement_cost entry catalog W provider price hcost hrel
  have hm : ∀ c ∈ l.map provider.pick,
      c ∈ catalog ∧ 2 ≤ (entry c).arity ∧ (entry c).arity ≤ K := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    exact ⟨provider.member t (hrel t ht),
      by rw [provider.arity t (hrel t ht)]; exact t.source.hk,
      by rw [provider.arity t (hrel t ht)]; exact t.cap⟩
  exact (Paper.PolicyOptimality.selected_le_all_shared
    (ppProblem price entry) catalog (fun c => (entry c).arity) K W N
    (l.map provider.pick) v' hm
    (replacement_shared entry catalog W provider l hrel hshared) hcat).trans hle

/-- Conditional complete-domain transfer without a provider-construction
or runtime claim. -/
theorem optimized_pp_all_F2_conditional {K : Nat} {ι : Type} [DecidableEq ι]
    (price : Nat → Nat) (entry : ι → VerifiedPPCandidate K)
    (catalog : List ι) (W N : Nat)
    (provider : CompleteProvider W entry catalog) :
    let P := ppProblem price entry
    let arity := fun c => (entry c).arity
    let trace := Paper.PolicyOptimality.chosenTrace P catalog arity K W N
    ∃ policy : PPPolicy K W,
      policyFromTrace entry trace W = some policy ∧
      ArityInj arity trace ∧
      (∀ c ∈ trace, VerifiedLiteralF2 (entry c)) ∧
      policy.benchmarkCost price N =
        Paper.PolicyOptimality.chosenCost P catalog arity K W N ∧
      policy.benchmarkCost price N =
        4 * (policy.adderAnds N + policy.leafRotations N) +
          policy.leafRotations N * price (policy.leafRotations N) ∧
      (∀ (theta : ℝ) (a c : BitVec W),
        policy.eval schoolbookLeaf theta a.toInt c.toInt =
          some (Paper.ValuePhase.phaseCharacter theta
            ((a.toInt : ℚ) * (c.toInt : ℚ)))) ∧
      (∀ (l : List (F2Source K)) (v : Nat),
        ArityInj F2Source.arity l →
        CostL (rawProblem price) l W N v →
        policy.benchmarkCost price N ≤ v) := by
  dsimp only
  obtain ⟨policy, hp, hm, hs, _, hv, hc, hsem, _⟩ :=
    optimized_pp_end_to_end price entry catalog W N
  refine ⟨policy, hp, hs, ?_, hv, hc, hsem, ?_⟩
  · intro c hc
    exact provider.catalog_literal c (hm c hc)
  · intro l v hs hc
    rw [hv]
    exact selected_le_all_raw price entry catalog W N provider l v hs hc

end Paper.F2CatalogTransfer