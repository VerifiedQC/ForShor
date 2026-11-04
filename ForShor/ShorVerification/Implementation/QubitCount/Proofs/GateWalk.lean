import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Registers
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Walk
import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Plan

/-!
# Qubit count: the walk on high-level gates

A phase-lowering plan is a `Gate` whose signed phase products are lowered
recursively and whose other gates are lowered one for one. This file walks
such gates with the phase products left opaque: a phase product returns the
live set it started from and costs `ex x z` extra qubits at its peak. The
plan induction in `PhaseProduct.lean` shows that this walk agrees with the
walk of the lowered circuit, with `ex` the phase-product budget.

It also computes the walk of the three parts of one compiled recursion
level: the allocations, the arithmetic body, and the deallocations.
-/

namespace Shor
namespace QubitCount

open Gate

/-! ## The walk -/

/-- A high-level gate that `lowerGateRec` sends to one low-level gate. -/
def gPrim : Gate → Option LowGate
  | .H q => some (.H q)
  | .X q => some (.X q)
  | .ShiftL r n => some (.ShiftL r n)
  | .ShiftR r n => some (.ShiftR r n)
  | .Negate r => some (.Negate r)
  | .AddScaled d s b n => some (.AddScaled d s b n)
  | .zeroExtend r n => some (.zeroExtend r n)
  | .signExtend r n => some (.signExtend r n)
  | .zeroDealloc r n => some (.zeroDealloc r n)
  | .signDealloc r n => some (.signDealloc r n)
  | .RadixReverse r m => some (.RadixReverse r m)
  | _ => none

/-- Live set after a high-level gate, phase products left opaque. -/
def gAfter : Gate → Finset ℕ → Finset ℕ
  | .id, L => L
  | .seq U V, L => gAfter V (gAfter U L)
  | .SignedPhaseProd _ _ _, L => L
  | .CSignedPhaseProd _ _ _ _, L => L
  | g, L => match gPrim g with
    | some u => after u true L
    | none => L

/-- Peak of a high-level gate, a phase product on `x` and `z` costing `ex x z`. -/
def gPeak (ex : ExtReg → ExtReg → ℕ) : Gate → Finset ℕ → ℕ
  | .id, L => L.card
  | .seq U V, L => max (gPeak ex U L) (gPeak ex V (gAfter U L))
  | .SignedPhaseProd _ x z, L => L.card + ex x z
  | .CSignedPhaseProd _ _ x z, L => L.card + ex x z
  | g, L => match gPrim g with
    | some u => peak scratch u true L
    | none => L.card

/-- A phase product at plan index `n` is ready to be counted from `L`: its
input size is `n`, its operands are live and their reserves are not. -/
def PPGood (n : ℕ) (x z : ExtReg) (L : Finset ℕ) : Prop :=
  phaseInputSize x z = n ∧ regQubitSet x.active ⊆ L ∧ regQubitSet z.active ⊆ L ∧
    _root_.Disjoint L (regQubitSet x.reserve ∪ regQubitSet z.reserve)

/-- Every part of a high-level gate is ready to be counted. -/
def gGood (n : ℕ) : Gate → Finset ℕ → Prop
  | .id, _ => True
  | .seq U V, L => gGood n U L ∧ gGood n V (gAfter U L)
  | .SignedPhaseProd _ x z, L => PPGood n x z L
  | .CSignedPhaseProd c _ x z, L => c ∈ L ∧ PPGood n x z L
  | g, L => match gPrim g with
    | some u => WellFormed u true L
    | none => False

/-! ## Touch-only circuits -/

/-- Every primitive of `g` acts on qubits of `L`, and `g` moves no qubits. -/
def TouchIn (L : Finset ℕ) : LowGate → Prop
  | .id => True
  | .seq U V => TouchIn L U ∧ TouchIn L V
  | .adj U => TouchIn L U
  | .zeroExtend _ _ | .signExtend _ _ | .zeroDealloc _ _ | .signDealloc _ _ => False
  | g => LowGate.usedQubits g ⊆ L

/-- The largest charge `anc` puts on a primitive of `g`. -/
def tmax (anc : LowGate → ℕ) : LowGate → ℕ
  | .id => 0
  | .seq U V => max (tmax anc U) (tmax anc V)
  | .adj U => tmax anc U
  | .zeroExtend _ _ | .signExtend _ _ | .zeroDealloc _ _ | .signDealloc _ _ => 0
  | g => anc g

/-- A circuit that only acts on live qubits leaves the live set alone, peaks
at its largest charge above it, and is well formed, in either direction. -/
theorem touch_walk_anc (anc : LowGate → ℕ) (L : Finset ℕ) :
    ∀ (g : LowGate), TouchIn L g → ∀ d : Bool,
      after g d L = L ∧ peak anc g d L = L.card + tmax anc g ∧ WellFormed g d L := by
  intro g
  induction g with
  | id => intro _ d; cases d <;> simp [after, peak, WellFormed, tmax]
  | seq U V ihU ihV =>
      intro h d
      obtain ⟨hU, hV⟩ := h
      obtain ⟨a1, p1, w1⟩ := ihU hU d
      obtain ⟨a2, p2, w2⟩ := ihV hV d
      cases d
      · refine ⟨?_, ?_, ?_⟩
        · simp only [after, a2, a1]
        · simp only [peak, a2, p1, p2, tmax]; omega
        · simp only [WellFormed, a2]; exact ⟨w2, w1⟩
      · refine ⟨?_, ?_, ?_⟩
        · simp only [after, a1, a2]
        · simp only [peak, a1, p1, p2, tmax]; omega
        · simp only [WellFormed, a1]; exact ⟨w1, w2⟩
  | adj U ih => intro h d; exact ih h (!d)
  | H _ | X _ | Phase _ _ | CNOT _ _ | Toffoli _ _ _ | ShiftL _ _ | ShiftR _ _ | Negate _
  | AddScaled _ _ _ _ | RadixReverse _ _ =>
      intro h d
      simp only [TouchIn] at h
      simp [after, peak, WellFormed, tmax, Finset.union_eq_left.mpr h, h]
  | zeroExtend _ _ | signExtend _ _ | zeroDealloc _ _ | signDealloc _ _ =>
      intro h; exact h.elim

section
variable (anc : LowGate → ℕ)
@[simp] lemma tmax_id : tmax anc .id = 0 := rfl
@[simp] lemma tmax_seq (U V : LowGate) : tmax anc (U ;; V) = max (tmax anc U) (tmax anc V) := rfl
@[simp] lemma tmax_adj (U : LowGate) : tmax anc (†U) = tmax anc U := rfl
@[simp] lemma tmax_H (q : ℕ) : tmax anc (.H q) = anc (.H q) := rfl
@[simp] lemma tmax_X (q : ℕ) : tmax anc (.X q) = anc (.X q) := rfl
@[simp] lemma tmax_Phase (q : ℕ) (a : Angle) : tmax anc (.Phase q a) = anc (.Phase q a) := rfl
@[simp] lemma tmax_CNOT (c t : ℕ) : tmax anc (.CNOT c t) = anc (.CNOT c t) := rfl
@[simp] lemma tmax_Toffoli (a b t : ℕ) : tmax anc (.Toffoli a b t) = anc (.Toffoli a b t) := rfl
@[simp] lemma tmax_ShiftL (r : ExtReg) (n : ℕ) : tmax anc (.ShiftL r n) = anc (.ShiftL r n) := rfl
@[simp] lemma tmax_ShiftR (r : ExtReg) (n : ℕ) : tmax anc (.ShiftR r n) = anc (.ShiftR r n) := rfl
@[simp] lemma tmax_Negate (r : ExtReg) : tmax anc (.Negate r) = anc (.Negate r) := rfl
@[simp] lemma tmax_AddScaled (d s : ExtReg) (b : Bool) (n : ℕ) :
    tmax anc (.AddScaled d s b n) = anc (.AddScaled d s b n) := rfl
@[simp] lemma tmax_RadixReverse (r : Reg) (m : ℕ) :
    tmax anc (.RadixReverse r m) = anc (.RadixReverse r m) := rfl
end

lemma tmax_zero : ∀ g : LowGate, tmax (fun _ => 0) g = 0 := by
  intro g
  induction g <;> simp [tmax, *]

/-- A circuit that only acts on live qubits leaves the live set alone, never
exceeds it without scratch, and is well formed, in either direction. -/
theorem touch_walk (L : Finset ℕ) :
    ∀ (g : LowGate), TouchIn L g → ∀ d : Bool,
      after g d L = L ∧ peak (fun _ => 0) g d L = L.card ∧ WellFormed g d L := by
  intro g h d
  obtain ⟨a, p, w⟩ := touch_walk_anc (fun _ => 0) L g h d
  exact ⟨a, by rw [p, tmax_zero, Nat.add_zero], w⟩

/-- A circuit that only acts on live qubits and charges no scratch. -/
theorem touch_walk_quiet (L : Finset ℕ) (g : LowGate) (h : TouchIn L g)
    (hq : tmax scratch g = 0) (d : Bool) :
    after g d L = L ∧ peak scratch g d L = L.card ∧ WellFormed g d L := by
  obtain ⟨a, p, w⟩ := touch_walk_anc scratch L g h d
  exact ⟨a, by rw [p, hq, Nat.add_zero], w⟩

lemma touchIn_sequence (L : Finset ℕ) :
    ∀ gs : List LowGate, (∀ g ∈ gs, TouchIn L g) → TouchIn L (LowGate.sequence gs) := by
  intro gs
  induction gs with
  | nil => intro _; simp [LowGate.sequence, TouchIn]
  | cons g gs ih =>
      intro h
      exact ⟨h g (by simp), ih (fun u hu => h u (by simp [hu]))⟩

lemma tmax_sequence (anc : LowGate → ℕ) :
    ∀ gs : List LowGate, (∀ g ∈ gs, tmax anc g = 0) → tmax anc (LowGate.sequence gs) = 0 := by
  intro gs
  induction gs with
  | nil => intro _; simp [LowGate.sequence]
  | cons g gs ih =>
      intro h
      simp only [LowGate.sequence, tmax, h g (by simp), ih (fun u hu => h u (by simp [hu]))]
      rfl

lemma tmax_CPhase (c t : ℕ) (θ : Angle) : tmax scratch (LowGate.CPhase c t θ) = 0 := by
  unfold LowGate.CPhase
  split <;> simp [tmax]

lemma tmax_CCPhase (a b c : ℕ) (θ : Angle) : tmax scratch (LowGate.CCPhase a b c θ) = 0 := by
  unfold LowGate.CCPhase
  split
  · exact tmax_CPhase _ _ _
  · split
    · exact tmax_CPhase _ _ _
    · split
      · exact tmax_CPhase _ _ _
      · simp [tmax, tmax_CPhase]

lemma touchIn_CPhase {L : Finset ℕ} {c t : ℕ} (θ : Angle) (hc : c ∈ L) (ht : t ∈ L) :
    TouchIn L (LowGate.CPhase c t θ) := by
  unfold LowGate.CPhase
  split
  · simp [TouchIn, LowGate.usedQubits, hc]
  · simp [TouchIn, LowGate.usedQubits, Finset.insert_subset_iff, hc, ht]

lemma touchIn_CCPhase {L : Finset ℕ} {a b c : ℕ} (θ : Angle) (ha : a ∈ L) (hb : b ∈ L)
    (hc : c ∈ L) : TouchIn L (LowGate.CCPhase a b c θ) := by
  unfold LowGate.CCPhase
  split
  · exact touchIn_CPhase θ ha hc
  · split
    · exact touchIn_CPhase θ ha hb
    · split
      · exact touchIn_CPhase θ ha hb
      · refine ⟨touchIn_CPhase _ ha hb, ?_⟩
        simp [TouchIn, LowGate.usedQubits, Finset.insert_subset_iff, ha, hb, hc]

lemma signedTermsAux_mem (w i : ℕ) :
    ∀ (qs : List ℕ) (t : ℕ × ℤ), t ∈ signedTermsAux w i qs → t.1 ∈ qs := by
  intro qs
  induction qs generalizing i with
  | nil => simp [signedTermsAux]
  | cons q qs ih =>
      intro t ht
      simp only [signedTermsAux, List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp
      · exact List.mem_cons_of_mem _ (ih (i + 1) t ht)

lemma signedTerms_mem {r : ExtReg} {t : ℕ × ℤ} (ht : t ∈ signedTerms r) :
    t.1 ∈ regQubitSet r.active := by
  rw [mem_regQubitSet]
  exact signedTermsAux_mem _ _ _ t ht

/-- The base-case phase product acts on its operands only. -/
lemma touchIn_naive {L : Finset ℕ} (phi : Angle) {x z : ExtReg}
    (hx : regQubitSet x.active ⊆ L) (hz : regQubitSet z.active ⊆ L) :
    TouchIn L (LowGate.Naive_SignedPhaseProd phi x z) := by
  apply touchIn_sequence
  intro g hg
  simp only [LowGate.naiveSignedPhaseGates, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨xt, hxt, zt, hzt, rfl⟩ := hg
  exact touchIn_CPhase _ (hx (signedTerms_mem hxt)) (hz (signedTerms_mem hzt))

/-- The base-case phase product charges no scratch. -/
lemma tmax_naive (phi : Angle) (x z : ExtReg) :
    tmax scratch (LowGate.Naive_SignedPhaseProd phi x z) = 0 := by
  apply tmax_sequence
  intro g hg
  simp only [LowGate.naiveSignedPhaseGates, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨xt, _, zt, _, rfl⟩ := hg
  exact tmax_CPhase _ _ _

/-- The controlled base case charges no scratch. -/
lemma tmax_cnaive (ctrl : ℕ) (phi : Angle) (x z : ExtReg) :
    tmax scratch (LowGate.Naive_CSignedPhaseProd ctrl phi x z) = 0 := by
  apply tmax_sequence
  intro g hg
  simp only [LowGate.naiveCSignedPhaseGates, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨xt, _, zt, _, rfl⟩ := hg
  exact tmax_CCPhase _ _ _ _

/-- The controlled base case acts on its operands and its control only. -/
lemma touchIn_cnaive {L : Finset ℕ} {ctrl : ℕ} (phi : Angle) {x z : ExtReg} (hc : ctrl ∈ L)
    (hx : regQubitSet x.active ⊆ L) (hz : regQubitSet z.active ⊆ L) :
    TouchIn L (LowGate.Naive_CSignedPhaseProd ctrl phi x z) := by
  apply touchIn_sequence
  intro g hg
  simp only [LowGate.naiveCSignedPhaseGates, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨xt, hxt, zt, hzt, rfl⟩ := hg
  exact touchIn_CCPhase _ hc (hx (signedTerms_mem hxt)) (hz (signedTerms_mem hzt))

end QubitCount
end Shor
