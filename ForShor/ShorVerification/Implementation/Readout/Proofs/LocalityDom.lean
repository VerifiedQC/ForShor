import ForShor.ShorVerification.Implementation.Readout.Proofs.LocalityProj

/-!
# Readout: spectator laws on a domain (shared machinery)

`Proofs/Locality.lean` and `Proofs/LocalityProj.lean` prove, for a program `P` and a qubit `q`,
the two halves of "`q` is a spectator of `P`" on EVERY state: `P` commutes with `X q` and with
the Z projectors `measProj (qubitReg q) o`; then they derive the record-level corollaries. Those
corollaries use nothing else. Here they are derived once, from the two halves stated on a
DOMAIN `D` (a `ℂ`-submodule of states, `D = ⊤` for "every state"):

* `MGate.SpectatorOn P q D`: for every branching state whose branches all lie in `D`,
  running `P` on the branchwise `X q` (resp. projection) is the branchwise `X q` (resp.
  projection) of the run.
* corollaries, for start states in `D`:
  - `MGate.SpectatorOn.recordProb_init_X`: `X q ψ₀` and `ψ₀` give every record the same
    probability (`ψ₀ ∈ D`);
  - `.recordProb_flipBit` (`|b⟩ ∈ D`), `MGate.recordProb_flipBits_on` (a list of flips; every
    flipped qubit a spectator on `D`, and `D` closed under those flips on kets),
    `MGate.recordProb_of_agree_on` (two kets differing at finitely many spectator qubits);
  - `.recordProb_decomp` (`ψ₀ ∈ D`): the record probabilities of `ψ₀` are the sums of those
    of its two Z-projections on `q`;
  - `.recordProb_superpose` (`|b⟩, |flipBit q b⟩ ∈ D`): starting in
    `α|b⟩ + β|flipBit q b⟩` multiplies every record probability by `‖α‖² + ‖β‖²`.

`MGate.spectatorOn_top` recovers the existing all-state results (`P.NoIdeal`,
`q ∉ P.qubitSupport`) as the case `D = ⊤`. No new axiom, no class field.
-/

namespace Shor
namespace Readout

open MeasureClass

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- **`q` is a spectator of `P` on the domain `D`.** For every branching state `ψ` all of whose
branches lie in `D`: running `P` on the branchwise `X q ψ` gives the branchwise `X q` of the run
on `ψ` (`commX`), and running `P` on the branchwise Z projection `measProj (qubitReg q) o ψ`
gives the branchwise projection of the run (`commP`, every `o`). With `D = ⊤` this is the
all-state law of `MGate.eval_commX` / `MGate.eval_commProj`. -/
structure _root_.Shor.MGate.SpectatorOn (P : MGate) (q : ℕ) (D : Submodule ℂ qs.State) : Prop where
  commX : ∀ ψ : MState qs, (∀ r, ψ r ∈ D) →
    P.eval (fun r => qs.eval (Gate.X q) (ψ r)) = fun r => qs.eval (Gate.X q) (P.eval ψ r)
  commP : ∀ (o : ℕ) (ψ : MState qs), (∀ r, ψ r ∈ D) →
    P.eval (fun r => measProj (qubitReg q) o (ψ r)) = fun r => measProj (qubitReg q) o (P.eval ψ r)

omit [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
/-- The initial branching state of a start state in `D` has every branch in `D`. -/
theorem MState.init_mem {D : Submodule ℂ qs.State} {ψ₀ : qs.State} (h : ψ₀ ∈ D) (r : Record) :
    MState.init ψ₀ r ∈ D := by
  unfold MState.init; split
  · exact h
  · exact D.zero_mem

/-- The existing all-state laws are the case `D = ⊤`. -/
theorem MGate.spectatorOn_top (P : MGate) (hP : P.NoIdeal) {q : ℕ} (hq : q ∉ P.qubitSupport) :
    P.SpectatorOn q (⊤ : Submodule ℂ qs.State) :=
  ⟨fun ψ _ => MGate.eval_commX P hP hq ψ, fun o ψ _ => MGate.eval_commProj P hP hq o ψ⟩

end Readout

namespace MGate.SpectatorOn

open Readout MeasureClass

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]
variable {P : MGate} {q : ℕ} {D : Submodule ℂ qs.State}

/-- Every branch of the run from `X q ψ₀` is `X q` of the corresponding branch from `ψ₀`
(`ψ₀ ∈ D`). -/
theorem eval_init_X (h : P.SpectatorOn q D) {ψ₀ : qs.State} (hψ : ψ₀ ∈ D) (r : Record) :
    P.eval (MState.init (qs.eval (Gate.X q) ψ₀)) r
      = qs.eval (Gate.X q) (P.eval (MState.init ψ₀) r) := by
  rw [MState.init_X, h.commX _ (MState.init_mem hψ)]

/-- Flipping `q` in a start state `ψ₀ ∈ D` changes no record probability. -/
theorem recordProb_init_X (h : P.SpectatorOn q D) {ψ₀ : qs.State} (hψ : ψ₀ ∈ D) (r : Record) :
    recordProb (P.eval (MState.init (qs.eval (Gate.X q) ψ₀))) r
      = recordProb (P.eval (MState.init ψ₀)) r := by
  rw [recordProb, recordProb, h.eval_init_X hψ, norm_eval_gate]

/-- Ket form: `|flipBit q b⟩` and `|b⟩` give the same record distribution (`|b⟩ ∈ D`). -/
theorem recordProb_flipBit (h : P.SpectatorOn q D) {b : qs.Basis} (hb : qs.ket b ∈ D)
    (r : Record) :
    recordProb (P.eval (MState.init (qs.ket (flipBit q b)))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  rw [← eval_X_ket_flipBit]
  exact h.recordProb_init_X hb r

/-- Projecting the start state on `q` projects every branch (`ψ₀ ∈ D`). -/
theorem eval_init_proj (h : P.SpectatorOn q D) (o : ℕ) {ψ₀ : qs.State} (hψ : ψ₀ ∈ D)
    (r : Record) :
    P.eval (MState.init (measProj (qubitReg q) o ψ₀)) r
      = measProj (qubitReg q) o (P.eval (MState.init ψ₀) r) := by
  rw [MState.init_proj, h.commP o _ (MState.init_mem hψ)]

/-- **Decomposition** (`ψ₀ ∈ D`): the record probabilities of `ψ₀` are the sums of those of its
two Z-projections on `q`. -/
theorem recordProb_decomp (h : P.SpectatorOn q D) {ψ₀ : qs.State} (hψ : ψ₀ ∈ D) (r : Record) :
    recordProb (P.eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2,
          recordProb (P.eval (MState.init (measProj (qubitReg q) o ψ₀))) r := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, recordProb,
    h.eval_init_proj _ hψ]
  exact (probMeas_qubitReg_zero_add_one q _).symm

private theorem recordProb_superpose_of_false (h : P.SpectatorOn q D) {b : qs.Basis}
    (hb0 : qs.ket b ∈ D) (hb1 : qs.ket (flipBit q b) ∈ D) (hb : RegEncoding.bit q b = false)
    (α β : ℂ) (r : Record) :
    recordProb (P.eval (MState.init (α • qs.ket b + β • qs.ket (flipBit q b)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb (P.eval (MState.init (qs.ket b))) r := by
  have h0 : measProj (qubitReg q) 0 (α • qs.ket b + β • qs.ket (flipBit q b)) = α • qs.ket b := by
    simp [map_add, map_smul, measProj_qubitReg_ket, bit_flipBit_self, hb]
  have h1 : measProj (qubitReg q) 1 (α • qs.ket b + β • qs.ket (flipBit q b))
      = β • qs.ket (flipBit q b) := by
    simp [map_add, map_smul, measProj_qubitReg_ket, bit_flipBit_self, hb]
  rw [h.recordProb_decomp (D.add_mem (D.smul_mem _ hb0) (D.smul_mem _ hb1))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [show ((0 : ℕ) : ℕ) = 0 from rfl, h0, h1, MGate.recordProb_init_smul,
    MGate.recordProb_init_smul, h.recordProb_flipBit hb0]
  ring

/-- **Spectator in superposition** (`|b⟩, |flipBit q b⟩ ∈ D`): for ANY `α β : ℂ`, starting in
`α|b⟩ + β|flipBit q b⟩` gives every record `(‖α‖² + ‖β‖²)` times its probability from `|b⟩`. -/
theorem recordProb_superpose (h : P.SpectatorOn q D) {b : qs.Basis} (hb0 : qs.ket b ∈ D)
    (hb1 : qs.ket (flipBit q b) ∈ D) (α β : ℂ) (r : Record) :
    recordProb (P.eval (MState.init (α • qs.ket b + β • qs.ket (flipBit q b)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb (P.eval (MState.init (qs.ket b))) r := by
  cases hb : RegEncoding.bit q b
  · exact recordProb_superpose_of_false h hb0 hb1 hb α β r
  · set b' := flipBit q b with hb'
    have hb'0 : RegEncoding.bit q b' = false := by rw [hb', bit_flipBit_self, hb]; rfl
    have hbb : b = flipBit q b' := by rw [hb', flipBit_flipBit]
    have e : α • qs.ket b + β • qs.ket b' = β • qs.ket b' + α • qs.ket (flipBit q b') := by
      rw [← hbb, add_comm]
    have hb1' : qs.ket (flipBit q b') ∈ D := by rw [← hbb]; exact hb0
    rw [e, recordProb_superpose_of_false h hb1 hb1' hb'0 β α r, hbb,
      h.recordProb_flipBit hb1 r]
    ring

end MGate.SpectatorOn

namespace Readout

open MeasureClass

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- **Finitely many flips on a domain.** Every qubit of `l` is a spectator of `P` on `D`, `D`
is closed (on kets) under flipping each qubit of `l`, and `|b⟩ ∈ D`: then `|flipBits l b⟩` and
`|b⟩` give every record the same probability. -/
theorem MGate.recordProb_flipBits_on (P : MGate) {D : Submodule ℂ qs.State} (l : List ℕ)
    (hl : ∀ q ∈ l, P.SpectatorOn q D)
    (hD : ∀ q ∈ l, ∀ b : qs.Basis, qs.ket b ∈ D → qs.ket (flipBit q b) ∈ D)
    (b : qs.Basis) (hb : qs.ket b ∈ D) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket (flipBits l b)))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  have hmem : ∀ l' : List ℕ, (∀ q ∈ l', q ∈ l) → qs.ket (flipBits l' b) ∈ D := by
    intro l' hl'
    induction l' with
    | nil => exact hb
    | cons q l' ih =>
      exact hD q (hl' q (List.mem_cons_self ..)) _ (ih fun q' h => hl' q' (List.mem_cons_of_mem _ h))
  have key : ∀ l' : List ℕ, (∀ q ∈ l', q ∈ l) →
      recordProb (P.eval (MState.init (qs.ket (flipBits l' b)))) r
        = recordProb (P.eval (MState.init (qs.ket b))) r := by
    intro l' hl'
    induction l' with
    | nil => rfl
    | cons q l' ih =>
      have hl'' : ∀ q' ∈ l', q' ∈ l := fun q' h => hl' q' (List.mem_cons_of_mem _ h)
      rw [flipBits_cons, (hl q (hl' q (List.mem_cons_self ..))).recordProb_flipBit
        (hmem l' hl''), ih hl'']
  exact key l fun _ h => h

/-- **Agreement form on a domain.** `|b⟩ ∈ D`; `b'` differs from `b` at finitely many qubits,
each a spectator of `P` on `D` under whose flips `D` is closed on kets. Then `|b'⟩` and `|b⟩`
give every record the same probability. -/
theorem MGate.recordProb_of_agree_on (P : MGate) {D : Submodule ℂ qs.State} (b b' : qs.Basis)
    (hb : qs.ket b ∈ D)
    (hspec : ∀ q, RegEncoding.bit q b' ≠ RegEncoding.bit q b → P.SpectatorOn q D)
    (hD : ∀ q, RegEncoding.bit q b' ≠ RegEncoding.bit q b →
      ∀ x : qs.Basis, qs.ket x ∈ D → qs.ket (flipBit q x) ∈ D)
    (hfin : {p | RegEncoding.bit p b' ≠ RegEncoding.bit p b}.Finite) (r : Record) :
    recordProb (P.eval (MState.init (qs.ket b'))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  conv_lhs => rw [eq_flipBits_of_finite b b' hfin]
  have hmem : ∀ q ∈ hfin.toFinset.toList, RegEncoding.bit q b' ≠ RegEncoding.bit q b := by
    intro q hq
    simpa only [Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hq
  exact MGate.recordProb_flipBits_on P _ (fun q hq => hspec q (hmem q hq))
    (fun q hq => hD q (hmem q hq)) b hb r

end Readout
end Shor
