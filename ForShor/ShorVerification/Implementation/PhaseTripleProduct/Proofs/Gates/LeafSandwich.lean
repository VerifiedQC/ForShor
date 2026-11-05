import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Gates.Leaf
import ForShor.ShorVerification.Framework.Gatecount.ResourceModel

/-!
# The PTP sandwich leaf: compute–rotate–uncompute (gate level)

The default PTP base case (2026-10-28), in ForShor's `Shor.LowGate` language. It
replaces the CCPhase grid (`Leaf.lean`, kept as `ptpLeafCCPhase`): every cell is
**one** rotation on an ancilla holding the AND of its three control bits, and the
AND of the `x`/`y` bits is shared along the `z` row.

**Gates.** Two clean ancilla qubits `t`, `u`. For every signed bit term `a` of `x`
and `c` of `y` (a *row*):

    Toffoli a c t                       -- compute t = x_a ∧ y_c
    for every signed bit term d of z:   -- one cell
      Toffoli t d u                     --   compute u = t ∧ z_d
      Phase u (φ · wₐ · w_c · w_d)      --   the one Rz of the cell
      † Toffoli t d u                   --   uncompute u
    † Toffoli a c t                     -- uncompute t

Uncomputations are written `LowGate.adj (Toffoli …)` (ForShor's `†`), so the census
can tell And from And† (the Qualtran `And` / `And(uncompute=True)` of the site's
`TripleLeaf`); semantically a Toffoli is its own inverse.

**Ancilla model.** ForShor's `LowGate` has no allocation node for scratch qubits:
the PP lowering keeps workspace in `ExtReg` reserves and states cleanliness as
`FreshZero r b` (`toNat r b = 0`), with `zeroExtend`/`zeroDealloc` semantically
the identity. The sandwich leaf follows the same convention: the ancillas are two
qubit indices, and the hypotheses (`SandwichAnc`) are exactly

* `t ≠ u`, and neither is an active qubit of `x`, `y` or `z`;
* both are `|0⟩` in the input basis state (`bit t b = false`, `bit u b = false`;
  `ancClean_of_freshZero` derives this from ForShor's `FreshZero` of any register
  containing them);

plus active-qubit disjointness of `x`, `y`, `z` (`LeafActiveDisjoint`). Under them
`evalL_ptpLeafSandwich_ket`: the leaf multiplies `ket b` by
`exp(i·π·φ·⟦x⟧·⟦y⟧·⟦z⟧)` and returns `ket b` itself, so the ancillas are back in
`|0⟩`. (Unlike the CCPhase leaf, the hypotheses are needed: a dirty `t` or a
qubit shared between operands breaks the AND.)

**Census** (`ptpLeafSandwich_resources`, any `LowGateResourceModel`), with
`W² = |x|·|y|`, `W³ = |x|·|y|·|z|`: `Rz = W³` (one per cell), `Toffoli = 2(W² + W³)`
of which `W² + W³` are uncomputations (`adjToffCount`), `CNOT = X = H = 0`, model
`cleanAnc = 0`; the qubits touched are inside `x ∪ y ∪ z ∪ {t, u}`
(`ptpLeafSandwich_usedQubits_subset`), i.e. 2 ancillas.
-/

namespace Shor
namespace PTP

/-! ## Hypotheses -/

/-- Both ancillas are `|0⟩` in `b`. -/
def AncClean {Basis : Type*} [RegEncoding Basis] (t u : ℕ) (b : Basis) : Prop :=
  RegEncoding.bit t b = false ∧ RegEncoding.bit u b = false

/-- Every qubit of a ForShor-clean register (`FreshZero r b`) reads `false`. -/
theorem bit_false_of_freshZero {Basis : Type*} [RegEncoding Basis] {r : Reg} {b : Basis}
    (h : FreshZero r b) {q : ℕ} (hq : q ∈ r.qubits) : RegEncoding.bit q b = false := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
  have key := RegEncoding.bit_eq_testBit_toNat r b ⟨j, hj⟩
  unfold FreshZero at h
  rw [h, Nat.zero_testBit] at key
  exact key

/-- ForShor's cleanliness predicate gives `AncClean`. -/
theorem ancClean_of_freshZero {Basis : Type*} [RegEncoding Basis] {r : Reg} {b : Basis}
    (h : FreshZero r b) {t u : ℕ} (ht : t ∈ r.qubits) (hu : u ∈ r.qubits) : AncClean t u b :=
  ⟨bit_false_of_freshZero h ht, bit_false_of_freshZero h hu⟩

/-! ## Basis-level gate facts -/

section Gates

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

/-- An uncomputing Toffoli acts on basis states as the Toffoli itself. -/
theorem evalL_adjToffoli_ket (c₁ c₂ tg : ℕ) (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs) (LowGate.adj (LowGate.Toffoli c₁ c₂ tg)) (qs.ket b) =
      qs.ket (toffoliBasis c₁ c₂ tg b) := by
  have h : qs.ket b = LowerGateClass.evalL (qs := qs) (LowGate.Toffoli c₁ c₂ tg)
      (qs.ket (toffoliBasis c₁ c₂ tg b)) := by
    rw [LowerGateClass.evalL_Toffoli_ket, LowerGateClass.toffoliBasis_involutive]
  calc LowerGateClass.evalL (qs := qs) (LowGate.adj (LowGate.Toffoli c₁ c₂ tg)) (qs.ket b)
      = LowerGateClass.evalL (qs := qs) (LowGate.adj (LowGate.Toffoli c₁ c₂ tg))
          (LowerGateClass.evalL (qs := qs) (LowGate.Toffoli c₁ c₂ tg)
            (qs.ket (toffoliBasis c₁ c₂ tg b))) := by rw [← h]
    _ = qs.ket (toffoliBasis c₁ c₂ tg b) := LowerGateClass.evalL_adj_apply _ _

end Gates

/-- A Toffoli into a clean target writes the AND of its controls. -/
theorem bit_toffoliBasis_clean {Basis : Type*} [RegEncoding Basis] (c₁ c₂ tg : ℕ) (b : Basis)
    (h12 : c₁ ≠ c₂) (h1t : c₁ ≠ tg) (h2t : c₂ ≠ tg) (hclean : RegEncoding.bit tg b = false) :
    RegEncoding.bit tg (toffoliBasis c₁ c₂ tg b) =
      (RegEncoding.bit c₁ b && RegEncoding.bit c₂ b) := by
  rw [LowerGateClass.bit_toffoliBasis_target_of_distinct c₁ c₂ tg b h12 h1t h2t, hclean]
  cases RegEncoding.bit c₁ b <;> cases RegEncoding.bit c₂ b <;> rfl

/-! ## Semantics -/

/-- Exponent of one cell given the bit already held by `t`: `i π θ` if `t ∧ z_d`. -/
noncomputable def sandCellExp {Basis : Type*} [RegEncoding Basis] (φ : Angle) (t : ℕ)
    (a c d : ℕ × ℤ) (b : Basis) : ℂ :=
  if (RegEncoding.bit t b && RegEncoding.bit d.1 b) = true then
    ((Angle.toReal (cellAngle φ (a, c, d)) : ℝ) : ℂ) * Complex.I
  else 0

theorem evalL_sandCell_ket {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (φ : Angle) (t u : ℕ) (a c d : ℕ × ℤ) (b : qs.Basis)
    (htd : t ≠ d.1) (htu : t ≠ u) (hdu : d.1 ≠ u) (hu : RegEncoding.bit u b = false) :
    LowerGateClass.evalL (qs := qs) (sandCell φ t u a c d) (qs.ket b) =
      Complex.exp (sandCellExp φ t a c d b) • qs.ket b := by
  unfold sandCell
  rw [LowerGateClass.evalL_seq, LowerGateClass.evalL_seq, LowerGateClass.evalL_Toffoli_ket,
    LowerGateClass.evalL_Phase_ket, bit_toffoliBasis_clean t d.1 u b htd htu hdu hu]
  unfold sandCellExp
  split_ifs with h
  · rw [LowerGateClass.evalL_smul, evalL_adjToffoli_ket, LowerGateClass.toffoliBasis_involutive]
  · rw [evalL_adjToffoli_ket, LowerGateClass.toffoliBasis_involutive, Complex.exp_zero, one_smul]

/-- On the state after the row's compute Toffoli, the cell exponent is the grid's. -/
theorem sandCellExp_eq {Basis : Type*} [RegEncoding Basis] (φ : Angle) (t : ℕ) (a c d : ℕ × ℤ)
    (b : Basis) (hac : a.1 ≠ c.1) (hat : a.1 ≠ t) (hct : c.1 ≠ t) (hdt : d.1 ≠ t)
    (ht : RegEncoding.bit t b = false) :
    sandCellExp φ t a c d (toffoliBasis a.1 c.1 t b) = cellExp φ b (a, c, d) := by
  unfold sandCellExp cellExp
  rw [bit_toffoliBasis_clean a.1 c.1 t b hac hat hct ht,
    LowerGateClass.bit_toffoliBasis_of_ne_target a.1 c.1 t d.1 b hdt]
  simp only [LowerGateClass.signedTermValue, LowerGateClass.basisBitInt, cellAngle,
    Angle.toReal]
  cases RegEncoding.bit a.1 b <;> cases RegEncoding.bit c.1 b <;>
    cases RegEncoding.bit d.1 b <;> simp
  ring

/-- One row: diagonal, exponent `Σ_d cellExp (a, c, d)`, every qubit restored. -/
theorem evalL_sandRow_ket {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (φ : Angle) (t u : ℕ) (zs : List (ℕ × ℤ)) (a c : ℕ × ℤ) (b : qs.Basis)
    (hac : a.1 ≠ c.1) (hat : a.1 ≠ t) (hct : c.1 ≠ t) (htu : t ≠ u) (hz : ∀ d ∈ zs, d.1 ≠ t ∧ d.1 ≠ u) (hclean : AncClean t u b) :
    LowerGateClass.evalL (qs := qs) (sandRow φ t u zs a c) (qs.ket b) =
      Complex.exp ((zs.map fun d => cellExp φ b (a, c, d)).sum) • qs.ket b := by
  set b1 := toffoliBasis a.1 c.1 t b with hb1
  have hu1 : RegEncoding.bit u b1 = false := by
    rw [hb1, LowerGateClass.bit_toffoliBasis_of_ne_target a.1 c.1 t u b (Ne.symm htu)]
    exact hclean.2
  have hdiag : List.Forall₂
      (fun g e => LowerGateClass.evalL (qs := qs) g (qs.ket b1) = Complex.exp e • qs.ket b1)
      (zs.map (sandCell φ t u a c)) (zs.map fun d => cellExp φ b (a, c, d)) := by
    induction zs with
    | nil => simp
    | cons d ds ih =>
        simp only [List.map_cons]
        refine List.Forall₂.cons ?_ (ih fun d' hd' => hz d' (by simp [hd']))
        have hd := hz d (by simp)
        rw [evalL_sandCell_ket φ t u a c d b1 (Ne.symm hd.1) htu hd.2 hu1,
          sandCellExp_eq φ t a c d b hac hat hct hd.1 hclean.1]
  unfold sandRow
  rw [LowerGateClass.evalL_seq, LowerGateClass.evalL_seq, LowerGateClass.evalL_Toffoli_ket, ← hb1,
    LowerGateClass.evalL_sequence_of_diagonal b1 _ _ hdiag, LowerGateClass.evalL_smul,
    evalL_adjToffoli_ket, hb1, LowerGateClass.toffoliBasis_involutive]

theorem mem_pairsOf {α β : Type} {as : List α} {bs : List β} {p : α × β}
    (h : p ∈ pairsOf as bs) : p.1 ∈ as ∧ p.2 ∈ bs := by
  unfold pairsOf at h
  simp only [List.mem_flatMap, List.mem_map] at h
  obtain ⟨a, ha, c, hc, rfl⟩ := h
  exact ⟨ha, hc⟩

theorem pairsOf_length {α β : Type} (as : List α) (bs : List β) :
    (pairsOf as bs).length = as.length * bs.length := by
  unfold pairsOf
  induction as with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, ih]; ring

/-- Summing the row exponents over all rows is summing over the grid. -/
theorem sum_rows_eq_sum_triples {α β γ : Type} (as : List α) (bs : List β) (cs : List γ)
    (f : α × β × γ → ℂ) :
    ((pairsOf as bs).map fun p => (cs.map fun d => f (p.1, p.2, d)).sum).sum =
      ((triples as bs cs).map f).sum := by
  unfold pairsOf triples
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.sum_append, List.map_append,
        List.sum_append, ih]
      congr 1
      clear ih
      induction bs with
      | nil => simp
      | cons c bs ihb =>
          rw [List.map_cons, List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
            List.sum_append, ihb, List.map_map]
          rfl

/-- A list of gates, each diagonal on `ket b`. -/
theorem forall₂_map_of_forall {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    {α : Type} (b : qs.Basis) (l : List α) (g : α → LowGate) (e : α → ℂ)
    (h : ∀ p ∈ l, LowerGateClass.evalL (qs := qs) (g p) (qs.ket b) = Complex.exp (e p) • qs.ket b) :
    List.Forall₂
      (fun g e => LowerGateClass.evalL (qs := qs) g (qs.ket b) = Complex.exp e • qs.ket b)
      (l.map g) (l.map e) := by
  induction l with
  | nil => simp
  | cons p ps ih =>
      exact List.Forall₂.cons (h p (by simp)) (ih fun p' hp' => h p' (by simp [hp']))

/-- **PTP sandwich-leaf correctness (gate level).** If `x`, `y`, `z` are pairwise
active-disjoint, the ancillas `t ≠ u` are off all three operands, and both are
`|0⟩` in `b`, the sandwich leaf multiplies `ket b` by `exp(i · π φ · ⟦x⟧ · ⟦y⟧ · ⟦z⟧)`
and returns `ket b` (ancillas back in `|0⟩`). -/
theorem evalL_ptpLeafSandwich_ket {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (φ : Angle) (x y z : ExtReg) (t u : ℕ) (b : qs.Basis)
    (hD : LeafActiveDisjoint x y z) (hA : SandwichAnc x y z t u) (hclean : AncClean t u b) :
    LowerGateClass.evalL (qs := qs) (ptpLeafSandwich φ x y z t u) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((extToInt x b : ℤ) : ℂ) * ((extToInt y b : ℤ) : ℂ) * ((extToInt z b : ℤ) : ℂ))) •
        qs.ket b := by
  obtain ⟨htu, htx, hty, htz, hux, huy, huz⟩ := hA
  have hoff : ∀ {r : ExtReg} {q : ℕ}, q ∉ r.active.qubits → ∀ d ∈ signedTerms r, d.1 ≠ q :=
    fun hq d hd e => hq (e ▸ LowerGateClass.signedTerms_fst_mem hd)
  have hdiag := forall₂_map_of_forall (qs := qs) b (leafPairs x y)
    (fun p => sandRow φ t u (signedTerms z) p.1 p.2)
    (fun p => ((signedTerms z).map fun d => cellExp φ b (p.1, p.2, d)).sum) (by
      intro p hp
      obtain ⟨ha, hc⟩ := mem_pairsOf hp
      exact evalL_sandRow_ket φ t u (signedTerms z) p.1 p.2 b
        (ne_of_activeDisjoint hD.1 ha hc) (hoff htx _ ha) (hoff hty _ hc) htu (fun d hd => ⟨hoff htz d hd, hoff huz d hd⟩) hclean)
  unfold ptpLeafSandwich sandRows
  rw [LowerGateClass.evalL_sequence_of_diagonal b _ _ hdiag, leafPairs,
    sum_rows_eq_sum_triples (signedTerms x) (signedTerms y) (signedTerms z) (cellExp φ b)]
  exact congrArg (fun e => Complex.exp e • qs.ket b) (cellExp_sum φ x y z b)


/-! ## Gate census -/

/-- A field of `GateResources` that adds under sequential composition. -/
structure AddField where
  f : GateResources → ℕ
  seq : ∀ a b, f (GateResources.seq a b) = f a + f b
  zero : f {} = 0

def fRz : AddField := ⟨GateResources.rz, fun _ _ => rfl, rfl⟩
def fCnot : AddField := ⟨GateResources.cnot, fun _ _ => rfl, rfl⟩
def fToff : AddField := ⟨GateResources.toffoli, fun _ _ => rfl, rfl⟩
def fX : AddField := ⟨GateResources.x, fun _ _ => rfl, rfl⟩
def fH : AddField := ⟨GateResources.h, fun _ _ => rfl, rfl⟩

theorem field_sequence (F : AddField) (M : LowGateResourceModel) (gs : List LowGate) :
    F.f (LowGate.resources M (LowGate.sequence gs)) = (gs.map fun g => F.f (LowGate.resources M g)).sum := by
  induction gs with
  | nil => simp [LowGate.sequence, LowGate.resources, F.zero]
  | cons g gs ih => simp [LowGate.sequence, LowGate.resources, F.seq, ih]

theorem sandCell_resources (M : LowGateResourceModel) (φ : Angle) (t u : ℕ) (a c d : ℕ × ℤ) :
    LowGate.resources M (sandCell φ t u a c d) = { toffoli := 2, rz := 1 } := by
  simp [sandCell, LowGate.resources, GateResources.seq]

/-- An additive field of one row. -/
theorem sandRow_field (F : AddField) (M : LowGateResourceModel) (φ : Angle) (t u : ℕ)
    (zs : List (ℕ × ℤ)) (a c : ℕ × ℤ) :
    F.f (LowGate.resources M (sandRow φ t u zs a c)) =
      2 * F.f { toffoli := 1 } + zs.length * F.f { toffoli := 2, rz := 1 } := by
  simp only [sandRow, LowGate.resources, F.seq, field_sequence, List.map_map]
  rw [sum_const_of_mem _ (F.f { toffoli := 2, rz := 1 }) zs fun d _ => by
    simp only [Function.comp, sandCell_resources]]
  ring

/-- An additive field of the sandwich leaf: `|x||y|` rows of `|z|` cells. -/
theorem leafSandwich_field (F : AddField) (M : LowGateResourceModel) (φ : Angle)
    (x y z : ExtReg) (t u : ℕ) :
    F.f (LowGate.resources M (ptpLeafSandwich φ x y z t u)) =
      x.width * y.width * (2 * F.f { toffoli := 1 } + z.width * F.f { toffoli := 2, rz := 1 }) := by
  unfold ptpLeafSandwich sandRows
  rw [field_sequence, List.map_map]
  rw [sum_const_of_mem _ (2 * F.f { toffoli := 1 } +
      (signedTerms z).length * F.f { toffoli := 2, rz := 1 }) _ fun p _ => by
    simp only [Function.comp, sandRow_field]]
  rw [leafPairs, pairsOf_length, LowerGateClass.signedTerms_length,
    LowerGateClass.signedTerms_length, LowerGateClass.signedTerms_length]
  ring

theorem leafSandwich_cleanAnc (M : LowGateResourceModel) (φ : Angle) (x y z : ExtReg) (t u : ℕ) :
    (LowGate.resources M (ptpLeafSandwich φ x y z t u)).cleanAnc = 0 := by
  unfold ptpLeafSandwich sandRows
  induction leafPairs x y with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, LowGate.sequence, LowGate.resources, GateResources.seq, ih]
      have hrow : ∀ zs : List (ℕ × ℤ),
          (LowGate.resources M (LowGate.sequence (zs.map (sandCell φ t u p.1 p.2)))).cleanAnc = 0 := by
        intro zs
        induction zs with
        | nil => rfl
        | cons d ds ihd =>
            simp only [List.map_cons, LowGate.sequence, LowGate.resources, GateResources.seq, ihd,
              sandCell_resources]
            rfl
      simp only [sandRow, LowGate.resources, GateResources.seq, hrow]
      rfl

/-- **Sandwich-leaf census** (any ForShor resource model; no disjointness needed).
With `W² = |x|·|y|` and `W³ = |x|·|y|·|z|`: exactly one Rz per cell (`W³`),
`2 (W² + W³)` Toffoli, no CNOT, X or H, and no model scratch ancilla (the two
ancillas `t`, `u` are explicit qubits, `ptpLeafSandwich_usedQubits_subset`). -/
theorem ptpLeafSandwich_resources (M : LowGateResourceModel) (φ : Angle) (x y z : ExtReg)
    (t u : ℕ) :
    let R := LowGate.resources M (ptpLeafSandwich φ x y z t u)
    let W2 := x.width * y.width
    let W3 := x.width * y.width * z.width
    R.rz = W3 ∧ R.toffoli = 2 * (W2 + W3) ∧ R.cnot = 0 ∧ R.x = 0 ∧ R.h = 0 ∧ R.cleanAnc = 0 := by
  intro R W2 W3
  refine ⟨?_, ?_, ?_, ?_, ?_, leafSandwich_cleanAnc M φ x y z t u⟩
  · have h := leafSandwich_field fRz M φ x y z t u; simp only [fRz] at h
    rw [show R.rz = _ from h]; ring
  · have h := leafSandwich_field fToff M φ x y z t u; simp only [fToff] at h
    rw [show R.toffoli = _ from h]; ring
  · have h := leafSandwich_field fCnot M φ x y z t u; simpa [fCnot] using h
  · have h := leafSandwich_field fX M φ x y z t u; simpa [fX] using h
  · have h := leafSandwich_field fH M φ x y z t u; simpa [fH] using h

/-- Structural counts (`Leaf.lean` counters): `W³` rotations, `2(W² + W³)` Toffoli of
which `W² + W³` are uncomputations (`† Toffoli`, the Qualtran And†), no CNOT. -/
theorem ptpLeafSandwich_counts (φ : Angle) (x y z : ExtReg) (t u : ℕ) :
    let L := ptpLeafSandwich φ x y z t u
    let W2 := x.width * y.width
    let W3 := x.width * y.width * z.width
    rotCount L = W3 ∧ toffCount L = 2 * (W2 + W3) ∧ adjToffCount L = W2 + W3 ∧ cnotCount L = 0 := by
  intro L W2 W3
  have gen : ∀ (f : LowGate → ℕ) (hid : f .id = 0) (hseq : ∀ U V, f (.seq U V) = f U + f V)
      (rT rA c : ℕ) (hT : ∀ a b q, f (LowGate.Toffoli a b q) = rT)
      (hA : ∀ a b q, f (LowGate.adj (LowGate.Toffoli a b q)) = rA)
      (hcell : ∀ a c' d, f (sandCell φ t u a c' d) = c),
      f L = W2 * (rT + rA + z.width * c) := by
    intro f hid hseq rT rA c hT hA hcell
    simp only [L, ptpLeafSandwich, sandRows]
    rw [count_sequence f hid hseq, List.map_map]
    rw [sum_const_of_mem _ (rT + rA + (signedTerms z).length * c) _ fun p _ => by
      simp only [Function.comp, sandRow, hseq, hT, hA, count_sequence f hid hseq, List.map_map]
      rw [sum_const_of_mem _ c _ fun d _ => by simp only [Function.comp, hcell]]
      ring]
    rw [leafPairs, pairsOf_length, LowerGateClass.signedTerms_length,
      LowerGateClass.signedTerms_length, LowerGateClass.signedTerms_length]
    simp only [W2]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gen rotCount rfl (fun _ _ => rfl) 0 0 1 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)]; ring
  · rw [gen toffCount rfl (fun _ _ => rfl) 1 1 2 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)]; ring
  · rw [gen adjToffCount rfl (fun _ _ => rfl) 0 1 1 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)]; ring
  · rw [gen cnotCount rfl (fun _ _ => rfl) 0 0 0 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)]; ring

/-- The qubits the sandwich leaf touches: the three operands and the two ancillas. -/
theorem ptpLeafSandwich_usedQubits_subset (φ : Angle) (x y z : ExtReg) (t u : ℕ) :
    LowGate.usedQubits (ptpLeafSandwich φ x y z t u) ⊆
      extRegActiveQubits x ∪ extRegActiveQubits y ∪ extRegActiveQubits z ∪ {t, u} := by
  set S := extRegActiveQubits x ∪ extRegActiveQubits y ∪ extRegActiveQubits z ∪ {t, u}
  have hseqL : ∀ gs : List LowGate, (∀ g ∈ gs, LowGate.usedQubits g ⊆ S) →
      LowGate.usedQubits (LowGate.sequence gs) ⊆ S := by
    intro gs
    induction gs with
    | nil => intro _; simp [LowGate.sequence, LowGate.usedQubits]
    | cons g gs ih =>
        intro h
        simp only [LowGate.sequence, LowGate.usedQubits]
        exact Finset.union_subset (h g (by simp)) (ih fun g' h' => h g' (by simp [h']))
  have mem_of : ∀ {r : ExtReg} {d : ℕ × ℤ}, d ∈ signedTerms r → d.1 ∈ extRegActiveQubits r :=
    fun hd => by simpa [extRegActiveQubits] using LowerGateClass.signedTerms_fst_mem hd
  have ht : t ∈ S := by simp [S]
  have hu : u ∈ S := by simp [S]
  apply hseqL
  intro g hg
  simp only [sandRows, List.mem_map] at hg
  obtain ⟨p, hp, rfl⟩ := hg
  obtain ⟨ha, hc⟩ := mem_pairsOf hp
  have ha' : p.1.1 ∈ S := by simp only [S, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (mem_of ha)))
  have hc' : p.2.1 ∈ S := by simp only [S, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (mem_of hc)))
  have hT : LowGate.usedQubits (LowGate.Toffoli p.1.1 p.2.1 t) ⊆ S := by
    intro q hq; simp only [LowGate.usedQubits, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  simp only [sandRow, LowGate.usedQubits]
  refine Finset.union_subset hT (Finset.union_subset (hseqL _ ?_) hT)
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨d, hd, rfl⟩ := hg
  have hd' : d.1 ∈ S := by simp only [S, Finset.mem_union]; exact Or.inl (Or.inr (mem_of hd))
  have hT2 : LowGate.usedQubits (LowGate.Toffoli t d.1 u) ⊆ S := by
    intro q hq; simp only [LowGate.usedQubits, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  simp only [sandCell, LowGate.usedQubits]
  refine Finset.union_subset hT2 (Finset.union_subset ?_ hT2)
  intro q hq; simp only [Finset.mem_singleton] at hq; rw [hq]; exact hu

end PTP
end Shor
