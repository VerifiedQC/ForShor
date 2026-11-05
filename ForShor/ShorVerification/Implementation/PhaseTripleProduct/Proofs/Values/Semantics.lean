import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Table.Width
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Support.Mirror
/-!
# What a PTP policy computes: exact and wrapping-register semantics

`PTPPolicy.evalPhase P n φ x` is the total phase the recursive PTP construction
applies to three operands `x 0, x 1, x 2` at width `n` with angle `φ`:

* leaf (no band, or the chosen table does not shrink the width): the 3-way
  grid phase `φ · x₀ · x₁ · x₂` (`Statement.lean`'s `ptpLeafSandwich` is its gate circuit);
* node with table `T`: each operand is split top-heavy at `limbWidth n T.k`
  (`= n / k`), the program is **run** on each operand's limbs
  (`runF id`, `Table/Width.lean`), and the `t`-th checkpoint value of each operand
  is the `t`-th child operand; child `t` gets angle `φ · cₜ` (interpolation
  weight of declared point `t` at radix `2 ^ (n / k)`), at the PTP child width
  `childWidth n T.ops`.

`evalPhaseW` is the same recursion with every register write wrapped to
`childWidth n T.ops` bits (`runF (tcWrapInt C)`): the register semantics a
width-`C` circuit has.

Theorems:
* `evalPhase_correct` (a): every checked policy gives `φ·x₀·x₁·x₂` at every
  width, for all integer operands;
* `evalPhaseW_correct` (a)+(b): for operands that fit signed `n` bits, the
  wrapping semantics also gives `φ·x₀·x₁·x₂` at every width; at every node the
  child operands fit signed `childWidth` bits, which is the hypothesis one
  level down.
-/

noncomputable section

namespace Shor
namespace PTP

open Operations Finset

namespace PTPTable

/-- The weight the `Statement` defines (the radix row times the inverse interpolation matrix) is
ForShor's generic `ToomCookMath.interpCoeff` at `3k - 2` points, the form `toomCook_exact` is
stated for. -/
theorem coeff_eq_interpCoeff (T : PTPTable) (n : ℕ) (t : Fin T.pts.length) :
    T.coeff n t = ToomCookMath.interpCoeff (pointRowQ T.pts.length)
      (fun i : Fin T.pts.length => T.pts.get i) ((2 : ℚ) ^ limbWidth n T.k) t := rfl

/-- Child operands of operand `x` at width `n` under write map `f`: the
checkpoint values of the run on `x`'s limbs. -/
def children (T : PTPTable) (f : ℤ → ℤ) (n : Nat) (x : ℤ) : List ℤ :=
  (runF f (limbsAt T.k (limbWidth n T.k) x) T.ops).1

end PTPTable

namespace PTPPolicy

/-- Exact PTP semantics. -/
def evalPhase (P : PTPPolicy) (n : Nat) (φ : ℚ) (x : Fin 3 → ℤ) : ℚ :=
  match P.choose n with
  | none => φ * x 0 * x 1 * x 2
  | some T =>
      if _h : childWidth n T.ops < n then
        ∑ t : Fin T.pts.length,
          P.evalPhase (childWidth n T.ops) (φ * T.coeff n t)
            (fun s => (T.children id n (x s)).getD t 0)
      else φ * x 0 * x 1 * x 2
termination_by n

/-- Wrapping-register PTP semantics: every write at a node of width `n` is
reduced to `childWidth n T.ops` bits. -/
def evalPhaseW (P : PTPPolicy) (n : Nat) (φ : ℚ) (x : Fin 3 → ℤ) : ℚ :=
  match P.choose n with
  | none => φ * x 0 * x 1 * x 2
  | some T =>
      if _h : childWidth n T.ops < n then
        ∑ t : Fin T.pts.length,
          P.evalPhaseW (childWidth n T.ops) (φ * T.coeff n t)
            (fun s => (T.children (Shor.tcWrapInt (childWidth n T.ops)) n (x s)).getD t 0)
      else φ * x 0 * x 1 * x 2
termination_by n

end PTPPolicy

/-! ## The node identity -/

theorem children_eq (T : PTPTable) (hT : T.contract = true) (n : Nat) (x : ℤ) :
    T.children id n x =
      T.pts.map (fun p => regVal (expectedRow p) (limbsAt T.k (limbWidth n T.k) x)) := by
  obtain ⟨hk, _, hsafe⟩ := (PTPTable.contract_iff T).mp hT
  have hrows := checkpointRows_of_consumes (positive_of_ge_two hk) T.ops
    State.start_state T.pts hsafe.consumes
  have hcp := checkpoint_val (limbsAt T.k (limbWidth n T.k) x) T.ops State.start_state _ hrows
  rw [valOf_start, List.map_map] at hcp
  exact hcp

theorem children_getD (T : PTPTable) (hT : T.contract = true) (n : Nat) (x : ℤ)
    (t : Fin T.pts.length) :
    (T.children id n x).getD t 0 =
      regVal (expectedRow (T.pts.get t)) (limbsAt T.k (limbWidth n T.k) x) := by
  rw [children_eq T hT, List.getD_eq_getElem _ _ (by simp)]
  simp

/-- **PTP node identity**: the weighted sum over the `3k - 2` declared points
of the products of the three operands' point values is `φ · x₀ · x₁ · x₂`. -/
theorem node_identity (T : PTPTable) (hT : T.contract = true) (n : Nat) (φ : ℚ)
    (x : Fin 3 → ℤ) :
    ∑ t : Fin T.pts.length, φ * T.coeff n t *
        ∏ s, ((regVal (expectedRow (T.pts.get t)) (limbsAt T.k (limbWidth n T.k) (x s)) : ℤ) : ℚ)
      = φ * x 0 * x 1 * x 2 := by
  obtain ⟨hk, ⟨hlen, hnodup, _⟩, _⟩ := (PTPTable.contract_iff T).mp hT
  have hk0 : 0 < T.k := by omega
  have hlen' : T.pts.length = 3 * (T.k - 1) + 1 := by
    rw [hlen]; simp only [pointCount]; omega
  have hd := pairwise_distinct_of_nodup hnodup
  set B : ℤ := (2 : ℤ) ^ limbWidth n T.k with hB
  have key := toomCook_exact 3 T.k hk0 T.pts hlen' hd ((2 : ℚ) ^ limbWidth n T.k)
    (fun s => limbsAt T.k (limbWidth n T.k) (x s))
  have hrad : ∀ s, ∑ j : Fin T.k, ((limbsAt T.k (limbWidth n T.k) (x s) j : ℤ) : ℚ) *
      ((2 : ℚ) ^ limbWidth n T.k) ^ (j : ℕ) = (x s : ℚ) := by
    intro s
    have h := sum_limbs T.k hk0 B (by positivity) (x s)
    have h' : ((∑ j : Fin T.k, limbs T.k B (x s) j * B ^ (j : ℕ) : ℤ) : ℚ)
        = (x s : ℚ) := by rw [h]
    push_cast [hB] at h'
    exact h'
  simp_rw [hrad] at key
  rw [Fin.prod_univ_three] at key
  rw [show (φ * x 0 * x 1 * x 2 : ℚ) = φ * ((x 0 : ℚ) * x 1 * x 2) by ring, ← key,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [regVal, Int.cast_sum, Int.cast_mul, expectedRow_cast]
  refine Finset.sum_congr rfl fun j _ => by ring

/-! ## (a) Functional correctness -/

/-- **(a) PTP functional correctness.** Every policy whose bands pass the PTP
contract applies phase `φ · x₀ · x₁ · x₂` at every width, for every angle and
all integer operands. -/
theorem evalPhase_correct (P : PTPPolicy) (hP : P.check = true) :
    ∀ (n : Nat) (φ : ℚ) (x : Fin 3 → ℤ), P.evalPhase n φ x = φ * x 0 * x 1 * x 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ x
    rw [PTPPolicy.evalPhase]
    split
    · rfl
    · rename_i T hc
      obtain ⟨b, hb, rfl⟩ := PTPPolicy.choose_mem hc
      have hT := PTPPolicy.check_tables hP b hb
      split
      · rename_i hlt
        simp_rw [ih _ hlt]
        rw [← node_identity b.table hT n φ x]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Fin.prod_univ_three]
        simp only [children_getD b.table hT]
        ring
      · rfl

/-! ## (a)+(b) Correctness of the wrapping-register semantics -/

/-- **(b) at every level: PTP wrapping-register correctness.** For a checked
policy and operands that fit signed `n` bits, the semantics in which every node
wraps every register write to its PTP child width also applies
`φ · x₀ · x₁ · x₂`. -/
theorem evalPhaseW_correct (P : PTPPolicy) (hP : P.check = true) :
    ∀ (n : Nat) (φ : ℚ) (x : Fin 3 → ℤ), (∀ s, Shor.FitsSignedWidth n (x s)) →
      P.evalPhaseW n φ x = φ * x 0 * x 1 * x 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ x hx
    rw [PTPPolicy.evalPhaseW]
    split
    · rfl
    · rename_i T hc
      obtain ⟨b, hb, rfl⟩ := PTPPolicy.choose_mem hc
      have hT := PTPPolicy.check_tables hP b hb
      split
      · rename_i hlt
        have hn : ∀ s : Fin 3, 0 < (fun _ => n) s := fun s => (hx s).1
        have hws := fun s => node_width_sound b.table hT (fun _ => n) hn x hx s
        -- the wrapped children are the exact children, and they fit the child width
        have hW : ∀ s, b.table.children (Shor.tcWrapInt (childWidth n b.table.ops)) n (x s)
            = b.table.children id n (x s) := by
          intro s
          simp only [PTPTable.children]
          exact congrArg Prod.fst (hws s).2.2.2.1
        have hfit : ∀ (t : Fin b.table.pts.length) s,
            Shor.FitsSignedWidth (childWidth n b.table.ops)
              ((b.table.children id n (x s)).getD t 0) := by
          intro t s
          have hlenC : t.1 < (b.table.children id n (x s)).length := by
            rw [children_eq b.table hT]; simp
          rw [List.getD_eq_getElem _ _ hlenC]
          exact (hws s).2.2.1 _ (List.getElem_mem hlenC)
        simp_rw [hW]
        rw [← node_identity b.table hT n φ x]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [ih _ hlt _ _ (fun s => hfit t s), Fin.prod_univ_three]
        simp only [children_getD b.table hT]
        ring
      · rfl

end PTP
end Shor
