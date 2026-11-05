import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.NaiveLeaf

/-!
# The PTP CCPhase leaf: a 3-way grid of doubly-controlled phases (gate level)

**Status: documented alternative.** The default PTP leaf is the compute–rotate–uncompute
sandwich `ptpLeafSandwich` (`LeafSandwich.lean`; its definition is in `Statement.lean`, together
with `Cell`, `cellAngle` and `LeafActiveDisjoint`), 1 Rz per cell instead of 5. This module keeps
the original CCPhase leaf, which the claims do not mention, and all its theorems,
renamed `ptpLeafCCPhase`, `evalL_ptpLeafCCPhase_ket`, `leafCCPhase_census`,
`gateCount_ptpLeafCCPhase`; it also holds the shared grid algebra (`leafCells`,
`cellExp`, `cellExp_sum`, `triples`) and the gate counters.

The PTP base case, in ForShor's low-level gate language `Shor.LowGate` and its
semantics `Shor.LowerGateClass`, modelled on ForShor's PhaseProduct naive leaf
(`Naive_SignedPhaseProd`, a 2-way grid of `CPhase` cells).

**Cell.** For one bit `a` of `x`, `c` of `y` and `d` of `z`, with two's-complement
weights `wₐ, w_c, w_d ∈ {±2^i}` (`Shor.signedTerms`; the top bit has weight
`-2^(w-1)`), the cell is ForShor's `LowGate.CCPhase a c d θ` with
`θ = φ · wₐ · w_c · w_d`. Its gates (ForShor `Gates/NaiveLeaf.lean`), for
distinct qubits:

    CPhase a c (θ/2)  = Phase a (θ/4); Phase c (θ/4); CNOT a c; Phase c (-θ/4); CNOT a c
    Phase d (θ/2); Toffoli a c d; Phase d (-θ/2); Toffoli a c d

i.e. 5 single-qubit phase rotations, 2 CNOT, 2 Toffoli (9 gates). On a basis
state it multiplies by `exp(i·π·θ·bₐ·b_c·b_d)` (ForShor `evalL_CCPhase_ket`).

**Leaf.** `ptpLeafCCPhase φ x y z` is the sequence of all `|x|·|y|·|z|` cells. Since
`extToInt r = Σ wᵢ bᵢ`, the phases add up to `π·φ·⟦x⟧·⟦y⟧·⟦z⟧`
(`evalL_ptpLeafCCPhase_ket`), on every basis state, with no disjointness or workspace
hypothesis. Gate counts (`gateCount_ptpLeafCCPhase`, `leafCCPhase_census`) need the three
registers to own disjoint qubits.
-/

namespace Shor
namespace PTP

/-- All triples from three lists, `x`-major. -/
def triples {α β γ : Type} (as : List α) (bs : List β) (cs : List γ) : List (α × β × γ) :=
  as.flatMap fun a => bs.flatMap fun c => cs.map fun d => (a, c, d)

/-- The cells of the 3-way grid. -/
def leafCells (x y z : ExtReg) : List Cell := triples (signedTerms x) (signedTerms y) (signedTerms z)

/-- The gate of one cell: ForShor's doubly-controlled phase. -/
def cellGate (φ : Angle) (t : Cell) : LowGate :=
  LowGate.CCPhase t.1.1 t.2.1.1 t.2.2.1 (cellAngle φ t)

/-- **The PTP leaf circuit.** -/
def ptpLeafCCPhase (φ : Angle) (x y z : ExtReg) : LowGate :=
  LowGate.sequence ((leafCells x y z).map (cellGate φ))

/-! ## Counting -/

theorem triples_length {α β γ : Type} (as : List α) (bs : List β) (cs : List γ) :
    (triples as bs cs).length = as.length * bs.length * cs.length := by
  unfold triples
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.flatMap_cons, List.length_append, ih,
        LowerGateClass.flatMap_map_length bs cs (fun c d => (a, c, d))]
      simp only [List.length_cons]
      ring

theorem mem_triples {α β γ : Type} {as : List α} {bs : List β} {cs : List γ}
    {t : α × β × γ} (h : t ∈ triples as bs cs) : t.1 ∈ as ∧ t.2.1 ∈ bs ∧ t.2.2 ∈ cs := by
  unfold triples at h
  simp only [List.mem_flatMap, List.mem_map] at h
  obtain ⟨a, ha, c, hc, d, hd, rfl⟩ := h
  exact ⟨ha, hc, hd⟩

theorem leafCells_length (x y z : ExtReg) :
    (leafCells x y z).length = x.width * y.width * z.width := by
  simp [leafCells, triples_length, LowerGateClass.signedTerms_length]

/-! ## Semantics -/

/-- Exponent of one cell on basis state `b`. -/
noncomputable def cellExp {Basis : Type*} [RegEncoding Basis] (φ : Angle) (b : Basis) (t : Cell) : ℂ :=
  ((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
    (((LowerGateClass.signedTermValue b t.1 : ℤ) : ℂ) *
      ((LowerGateClass.signedTermValue b t.2.1 : ℤ) : ℂ) *
      ((LowerGateClass.signedTermValue b t.2.2 : ℤ) : ℂ))

theorem evalL_cellGate_ket {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (φ : Angle) (t : Cell) (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs) (cellGate φ t) (qs.ket b) =
      Complex.exp (cellExp φ b t) • qs.ket b := by
  unfold cellGate
  rw [LowerGateClass.evalL_CCPhase_ket]
  congr 2
  simp only [cellExp, cellAngle, LowerGateClass.signedTermValue, Angle.toReal]
  push_cast
  ring

theorem sum_triples_one {α β γ : Type} (a : α) (c : β) (cs : List γ)
    (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) (K : ℂ) :
    ((cs.map fun d => (a, c, d)).map (fun t => K * (u t.1 * v t.2.1 * w t.2.2))).sum =
      K * (u a * v c * (cs.map w).sum) := by
  induction cs with
  | nil => simp
  | cons d cs ihc =>
      simp only [List.map_cons, List.sum_cons] at ihc ⊢
      rw [ihc]; ring

theorem sum_triples_two {α β γ : Type} (a : α) (bs : List β) (cs : List γ)
    (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) (K : ℂ) :
    ((bs.flatMap fun c => cs.map fun d => (a, c, d)).map
        (fun t => K * (u t.1 * v t.2.1 * w t.2.2))).sum =
      K * (u a * (bs.map v).sum * (cs.map w).sum) := by
  induction bs with
  | nil => simp
  | cons c bs ihb =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ihb, sum_triples_one]
      simp only [List.map_cons, List.sum_cons]; ring

theorem sum_triples {α β γ : Type} (as : List α) (bs : List β) (cs : List γ)
    (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) (K : ℂ) :
    ((triples as bs cs).map (fun t => K * (u t.1 * v t.2.1 * w t.2.2))).sum =
      K * ((as.map u).sum * (bs.map v).sum * (cs.map w).sum) := by
  unfold triples
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, sum_triples_two]
      simp only [List.map_cons, List.sum_cons]; ring

/-- The cell exponents of the 3-way grid add up to `i π φ ⟦x⟧⟦y⟧⟦z⟧`. Shared by both
leaves (`evalL_ptpLeafCCPhase_ket` here, `evalL_ptpLeafSandwich_ket` in `LeafSandwich.lean`). -/
theorem cellExp_sum {Basis : Type*} [RegEncoding Basis] (φ : Angle) (x y z : ExtReg) (b : Basis) :
    ((leafCells x y z).map (cellExp φ b)).sum =
      ((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((extToInt x b : ℤ) : ℂ) * ((extToInt y b : ℤ) : ℂ) * ((extToInt z b : ℤ) : ℂ)) := by
  have hs := sum_triples (signedTerms x) (signedTerms y) (signedTerms z)
    (fun a => ((LowerGateClass.signedTermValue b a : ℤ) : ℂ))
    (fun a => ((LowerGateClass.signedTermValue b a : ℤ) : ℂ))
    (fun a => ((LowerGateClass.signedTermValue b a : ℤ) : ℂ))
    (((Angle.toReal φ : ℝ) : ℂ) * Complex.I)
  have hx := LowerGateClass.extToInt_eq_signedTerms_sum x b
  have hy := LowerGateClass.extToInt_eq_signedTerms_sum y b
  have hz := LowerGateClass.extToInt_eq_signedTerms_sum z b
  unfold cellExp
  rw [show ((leafCells x y z).map fun t => ((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
      (((LowerGateClass.signedTermValue b t.1 : ℤ) : ℂ) *
        ((LowerGateClass.signedTermValue b t.2.1 : ℤ) : ℂ) *
        ((LowerGateClass.signedTermValue b t.2.2 : ℤ) : ℂ))) =
      (triples (signedTerms x) (signedTerms y) (signedTerms z)).map
        (fun t => (((Angle.toReal φ : ℝ) : ℂ) * Complex.I) *
          ((fun a => ((LowerGateClass.signedTermValue b a : ℤ) : ℂ)) t.1 *
           (fun a => ((LowerGateClass.signedTermValue b a : ℤ) : ℂ)) t.2.1 *
           (fun a => ((LowerGateClass.signedTermValue b a : ℤ) : ℂ)) t.2.2)) from rfl, hs,
    hx, hy, hz]
  push_cast
  simp only [List.map_map]
  rfl

/-- **PTP CCPhase-leaf correctness (gate level).** On every computational basis state
the CCPhase leaf multiplies by `exp(i · π φ · ⟦x⟧ · ⟦y⟧ · ⟦z⟧)`, with `⟦·⟧ = extToInt`
the two's-complement value. -/
theorem evalL_ptpLeafCCPhase_ket {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (φ : Angle) (x y z : ExtReg) (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs) (ptpLeafCCPhase φ x y z) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((extToInt x b : ℤ) : ℂ) * ((extToInt y b : ℤ) : ℂ) * ((extToInt z b : ℤ) : ℂ))) •
        qs.ket b := by
  unfold ptpLeafCCPhase
  have hdiag : List.Forall₂
      (fun g e => LowerGateClass.evalL (qs := qs) g (qs.ket b) = Complex.exp e • qs.ket b)
      ((leafCells x y z).map (cellGate φ)) ((leafCells x y z).map (cellExp φ b)) := by
    induction leafCells x y z with
    | nil => simp
    | cons t ts ih => exact List.Forall₂.cons (evalL_cellGate_ket φ t b) ih
  rw [LowerGateClass.evalL_sequence_of_diagonal b _ _ hdiag, cellExp_sum]

/-! ## Gate census -/

/-- Number of single-qubit phase rotations. -/
def rotCount : LowGate → ℕ
  | .seq U V => rotCount U + rotCount V
  | .adj U => rotCount U
  | .Phase _ _ => 1
  | _ => 0

/-- Number of CNOT gates. -/
def cnotCount : LowGate → ℕ
  | .seq U V => cnotCount U + cnotCount V
  | .adj U => cnotCount U
  | .CNOT _ _ => 1
  | _ => 0

/-- Number of Toffoli gates. -/
def toffCount : LowGate → ℕ
  | .seq U V => toffCount U + toffCount V
  | .adj U => toffCount U
  | .Toffoli _ _ _ => 1
  | _ => 0

theorem count_sequence (f : LowGate → ℕ) (hid : f .id = 0)
    (hseq : ∀ U V, f (.seq U V) = f U + f V) (gs : List LowGate) :
    f (LowGate.sequence gs) = (gs.map f).sum := by
  induction gs with
  | nil => simp [LowGate.sequence, hid]
  | cons g gs ih => simp [LowGate.sequence, hseq, ih]

/-- Owned-qubit disjointness of the three leaf operands. -/
def LeafDisjoint (x y z : ExtReg) : Prop :=
  ExtReg.OwnedDisjoint x y ∧ ExtReg.OwnedDisjoint x z ∧ ExtReg.OwnedDisjoint y z

theorem cell_distinct {x y z : ExtReg} (h : LeafDisjoint x y z) {t : Cell}
    (ht : t ∈ leafCells x y z) :
    t.1.1 ≠ t.2.1.1 ∧ t.1.1 ≠ t.2.2.1 ∧ t.2.1.1 ≠ t.2.2.1 := by
  obtain ⟨h1, h2, h3⟩ := mem_triples ht
  obtain ⟨hxy, hxz, hyz⟩ := h
  exact ⟨LowerGateClass.signedTerms_ne_of_ownedDisjoint x y hxy h1 h2,
    LowerGateClass.signedTerms_ne_of_ownedDisjoint x z hxz h1 h3,
    LowerGateClass.signedTerms_ne_of_ownedDisjoint y z hyz h2 h3⟩

theorem ne_of_activeDisjoint {x y : ExtReg} (h : ExtReg.ActiveDisjoint x y) {a c : ℕ × ℤ}
    (ha : a ∈ signedTerms x) (hc : c ∈ signedTerms y) : a.1 ≠ c.1 := by
  have hx := LowerGateClass.signedTerms_fst_mem ha
  have hy := LowerGateClass.signedTerms_fst_mem hc
  intro e
  rw [e] at hx
  exact (List.disjoint_left.mp h) hx hy

theorem cell_distinct' {x y z : ExtReg} (h : LeafActiveDisjoint x y z) {t : Cell}
    (ht : t ∈ leafCells x y z) :
    t.1.1 ≠ t.2.1.1 ∧ t.1.1 ≠ t.2.2.1 ∧ t.2.1.1 ≠ t.2.2.1 := by
  obtain ⟨h1, h2, h3⟩ := mem_triples ht
  exact ⟨ne_of_activeDisjoint h.1 h1 h2, ne_of_activeDisjoint h.2.1 h1 h3,
    ne_of_activeDisjoint h.2.2 h2 h3⟩

theorem cellGate_census (φ : Angle) (t : Cell) (h : t.1.1 ≠ t.2.1.1 ∧ t.1.1 ≠ t.2.2.1 ∧ t.2.1.1 ≠ t.2.2.1) :
    rotCount (cellGate φ t) = 5 ∧ cnotCount (cellGate φ t) = 2 ∧ toffCount (cellGate φ t) = 2 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [cellGate, LowGate.CCPhase, LowGate.CPhase, h1, h2, h3, rotCount, cnotCount, toffCount]

theorem sum_const_of_mem {α : Type} (f : α → ℕ) (c : ℕ) (l : List α) (h : ∀ a ∈ l, f a = c) :
    (l.map f).sum = c * l.length :=
  LowerGateClass.list_sum_map_eq_mul_length_of_constant f c l h

/-- **Leaf gate census.** With `w³ = |x|·|y|·|z|`: `5 w³` phase rotations,
`2 w³` CNOT, `2 w³` Toffoli. -/
theorem leafCCPhase_census (φ : Angle) (x y z : ExtReg) (h : LeafDisjoint x y z) :
    rotCount (ptpLeafCCPhase φ x y z) = 5 * (x.width * y.width * z.width) ∧
    cnotCount (ptpLeafCCPhase φ x y z) = 2 * (x.width * y.width * z.width) ∧
    toffCount (ptpLeafCCPhase φ x y z) = 2 * (x.width * y.width * z.width) := by
  unfold ptpLeafCCPhase
  rw [count_sequence rotCount rfl (fun _ _ => rfl), count_sequence cnotCount rfl (fun _ _ => rfl),
    count_sequence toffCount rfl (fun _ _ => rfl), List.map_map, List.map_map, List.map_map,
    ← leafCells_length x y z]
  refine ⟨sum_const_of_mem _ 5 _ ?_, sum_const_of_mem _ 2 _ ?_, sum_const_of_mem _ 2 _ ?_⟩ <;>
    intro t ht <;> simp only [Function.comp] <;>
    [exact (cellGate_census φ t (cell_distinct h ht)).1;
     exact (cellGate_census φ t (cell_distinct h ht)).2.1;
     exact (cellGate_census φ t (cell_distinct h ht)).2.2]

/-- **Leaf gate count** under any ForShor cost model: `9 · |x| · |y| · |z|`. -/
theorem gateCount_ptpLeafCCPhase (M : LowGateCostModel) (φ : Angle) (x y z : ExtReg)
    (h : LeafDisjoint x y z) :
    LowGate.gateCount M (ptpLeafCCPhase φ x y z) = 9 * (x.width * y.width * z.width) := by
  unfold ptpLeafCCPhase
  rw [LowerGateClass.LowGate.gateCount_sequence, List.map_map, ← leafCells_length x y z]
  refine sum_const_of_mem _ 9 _ fun t ht => ?_
  obtain ⟨h1, h2, h3⟩ := cell_distinct h ht
  exact LowGate.gateCount_CCPhase_of_distinct M _ _ _ _ h1 h2 h3

end PTP
end Shor
