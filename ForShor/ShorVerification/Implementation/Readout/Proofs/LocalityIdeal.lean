import ForShor.ShorVerification.Implementation.Readout.Proofs.LocalityExact
import ForShor.ShorVerification.Implementation.Readout.Proofs.Approx

/-!
# Readout: locality for programs WITH ideal multipliers, on their domain

`IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact` fixes the ideal controlled
multiplier `idealCtrlModMul c N data ctrl` only on kets with `toNat data < N`, and only under
the side conditions `1 < N ≤ 2^|data|`, `Nat.Coprime c N`, `ctrl ∉ data`. Off that domain the
classes say NOTHING about it, so no all-state locality theorem can hold for it. Here locality is
proved ON A DOMAIN.

* `IdealDom qs N data`: the `ℂ`-span of the kets `|x⟩` with `toNat data x < N` (control and
  every other qubit arbitrary; it is the ALGEBRAIC span, i.e. finite linear combinations). The
  auxiliary lemma `validSpan_true_eq` (universe `0` only, as `ValidSpan` itself) identifies it
  with `ValidSpan data N (fun _ => True)` of `Proofs/Approx.lean`; nothing depends on it. And every `InRange c data N` state lies in it
  (`inRange_mem_idealDom`). It is closed under `X p` for `p ∉ data` (`idealDom_X`).
* `Gate.IdealSafe qs D q U` (an inductive predicate, built bottom-up): `U` is
  - `local_`: any gate with no ideal node and `q ∉ U.exactSupport` (all-state locality, A1), or
  - `ideal`: an `idealCtrlModMul c N data ctrl` with its side conditions, `q ∉ data`,
    `q ≠ ctrl`, and `D ≤ IdealDom qs N data` (every state of `D` is in the gate's domain), or
  - `seq`: `U ;; V` with both safe and `U` mapping `D` into `D` (`GatePreserves`).
  `MGate.IdealSafe qs D q P` is the same for programs (`local_` / `unitary` / `seq` with
  `MPreserves`).
* `gate_commX_on`, `gate_commP_on`: an `IdealSafe` gate commutes with `X q` and with the
  Z projectors of `q` on every state of `D`. `MGate.spectatorOn_of_idealSafe`: an `IdealSafe`
  program has `q` as a spectator on `D` (`MGate.SpectatorOn`), so every corollary of
  `Proofs/LocalityDom.lean` applies to start states in `D`.
* The domain obligations are discharged STRUCTURALLY for `D = IdealDom qs N data`:
  `Gate.KeepsDom N data U` / `MGate.KeepsDom N data P` (inductive: identity, `H p` / `X p` with
  `p ∉ data`, the phase products, `idealCtrlModMul _ N data ctrl` with `1 < N ≤ 2^|data|`,
  `ctrl ∉ data`; `measureReset p` with `p ∉ data`; any `ffPhase`; sequences) imply
  `GatePreserves` / `MPreserves` (`Gate.KeepsDom.preserves`, `MGate.KeepsDom.preserves`).

NOT covered: states outside the domain (for them the classes do not determine the ideal gate);
qubits of `data` and the controls of ideal nodes (excluded by `ideal`); a program whose
intermediate states leave `D` (excluded by the preservation obligations). No new axiom or class
field.
-/

namespace Shor
namespace Readout

open MeasureClass

/-! ## The domain -/

/-- The span of the basis kets whose `data` value is `< N`: where the classes specify every
`idealCtrlModMul _ N data _`. -/
def IdealDom (qs : QSemantics) [RegEncoding qs.Basis] (N : ℕ) (data : Reg) :
    Submodule ℂ qs.State :=
  Submodule.span ℂ (qs.ket '' {x | RegEncoding.toNat data x < N})

section Dom
variable {qs : QSemantics} [RegEncoding qs.Basis] {N : ℕ} {data : Reg}

theorem ket_mem_idealDom {x : qs.Basis} (h : RegEncoding.toNat data x < N) :
    qs.ket x ∈ IdealDom qs N data :=
  Submodule.subset_span ⟨x, h, rfl⟩

/-- Every `InRange` state (control `0`, data `< N`) lies in the domain. -/
theorem inRange_mem_idealDom [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]
    {c : ℕ} {φ : qs.State} (h : InRange c data N φ) : φ ∈ IdealDom qs N data := by
  refine Submodule.span_mono ?_ h
  rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
  exact ⟨x, hx, rfl⟩

/-- A linear map that sends every in-range ket into the domain maps the domain into itself. -/
theorem idealDom_map {f : qs.State →ₗ[ℂ] qs.State}
    (hf : ∀ x : qs.Basis, RegEncoding.toNat data x < N → f (qs.ket x) ∈ IdealDom qs N data)
    {φ : qs.State} (hφ : φ ∈ IdealDom qs N data) : f φ ∈ IdealDom qs N data := by
  induction hφ using Submodule.span_induction with
  | mem x hx => obtain ⟨y, hy, rfl⟩ := hx; exact hf y hy
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- Writing a qubit outside `data` does not change the data value. -/
theorem toNat_writeNat_qubitReg_out {p : ℕ} (hp : p ∉ data.qubits) (v : ℕ) (x : qs.Basis) :
    RegEncoding.toNat data (RegEncoding.writeNat (qubitReg p) v x) = RegEncoding.toNat data x :=
  toNat_congr_bits' data fun _ hs => RegEncoding.bit_writeNat_out _ _ _ _
    (not_mem_qubitReg.mpr fun e => hp (e ▸ hs))

end Dom

/-- Auxiliary (universe `0` only, as `ValidSpan`): `ValidSpan data N` with no side condition is
the domain. Nothing else depends on it. -/
theorem validSpan_true_eq {qs : QSemantics.{0}} [RegEncoding qs.Basis] (data : Reg) (N : ℕ) :
    ValidSpan (qs := qs) data N (fun _ => True) = IdealDom qs N data := by
  unfold ValidSpan IdealDom
  congr 2
  ext x
  simp

/-! ## Safe programs and their domain obligations -/

section Safe
variable {qs : QSemantics} [RegEncoding qs.Basis]

/-- A spectator on `D` is a spectator on every smaller domain. -/
theorem _root_.Shor.MGate.SpectatorOn.mono [GateSemanticsFacts qs] [LowerGateClass qs]
    [MeasureClass qs] {P : MGate} {q : ℕ} {D D' : Submodule ℂ qs.State}
    (h : P.SpectatorOn q D) (hle : D' ≤ D) : P.SpectatorOn q D' :=
  ⟨fun ψ hψ => h.commX ψ fun r => hle (hψ r), fun o ψ hψ => h.commP o ψ fun r => hle (hψ r)⟩

/-- `eval U` maps `D` into `D`. -/
def GatePreserves (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs]
    (D : Submodule ℂ qs.State) (U : Gate) : Prop :=
  ∀ ψ ∈ D, qs.eval U ψ ∈ D

/-- Running `P` keeps every branch in `D`. -/
def MPreserves (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs] [LowerGateClass qs]
    [MeasureClass qs] (D : Submodule ℂ qs.State) (P : MGate) : Prop :=
  ∀ ψ : MState qs, (∀ r, ψ r ∈ D) → ∀ r, P.eval ψ r ∈ D

/-- **A gate whose locality at `q` holds on the domain `D`** (see the module docstring). -/
inductive _root_.Shor.Gate.IdealSafe (qs : QSemantics) [RegEncoding qs.Basis]
    [GateSemanticsCore qs] (D : Submodule ℂ qs.State) (q : ℕ) : Gate → Prop
  /-- A gate with no ideal node, `q` outside its exact support (all-state locality). -/
  | local_ (U : Gate) : U.NoIdeal → q ∉ U.exactSupport → Gate.IdealSafe qs D q U
  /-- An ideal multiplier with its side conditions, whose domain contains `D`; `q` is not one of
  its qubits. -/
  | ideal (c N : ℕ) (data : Reg) (ctrl : ℕ) : 1 < N → N ≤ ASize data → Nat.Coprime c N →
      ctrl ∉ data.qubits → q ∉ data.qubits → q ≠ ctrl → D ≤ IdealDom qs N data →
      Gate.IdealSafe qs D q (Gate.idealCtrlModMul c N data ctrl)
  /-- A sequence of safe gates whose first part keeps `D`. -/
  | seq (U V : Gate) : Gate.IdealSafe qs D q U → Gate.IdealSafe qs D q V → GatePreserves qs D U →
      Gate.IdealSafe qs D q (U ;; V)

/-- **A program whose locality at `q` holds on the domain `D`.** -/
inductive _root_.Shor.MGate.IdealSafe (qs : QSemantics) [RegEncoding qs.Basis]
    [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] (D : Submodule ℂ qs.State)
    (q : ℕ) : MGate → Prop
  /-- No ideal node, `q` outside the exact support. -/
  | local_ (P : MGate) : P.NoIdeal → q ∉ P.exactSupport → MGate.IdealSafe qs D q P
  /-- A safe gate. -/
  | unitary (g : Gate) : g.IdealSafe qs D q → MGate.IdealSafe qs D q (.unitary g)
  /-- A sequence of safe programs whose first part keeps every branch in `D`. -/
  | seq (a b : MGate) : MGate.IdealSafe qs D q a → MGate.IdealSafe qs D q b → MPreserves qs D a →
      MGate.IdealSafe qs D q (.seq a b)

variable [GateSemanticsFacts qs]

/-- **The ideal multiplier commutes with `X q` on its domain** (all states of the span). -/
theorem idealCtrlModMul_commX_dom {c N ctrl q : ℕ} {data : Reg} (hN : 1 < N)
    (hNd : N ≤ ASize data) (hc : Nat.Coprime c N) (hctrl : ctrl ∉ data.qubits)
    (hqd : q ∉ data.qubits) (hqc : q ≠ ctrl) {ψ : qs.State} (hψ : ψ ∈ IdealDom qs N data) :
    qs.eval (Gate.idealCtrlModMul c N data ctrl) (qs.eval (Gate.X q) ψ)
      = qs.eval (Gate.X q) (qs.eval (Gate.idealCtrlModMul c N data ctrl) ψ) := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [eval_X_ket_flipBit]
    exact idealCtrlModMul_ket_flipBit hN hNd hc hctrl hqd hqc y hy
  | zero => simp only [MGate.gate_eval_zero_state]
  | add x y _ _ hx hy => rw [gate_eval_add, gate_eval_add, hx, hy, gate_eval_add, gate_eval_add]
  | smul a x _ hx => rw [gate_eval_smul, gate_eval_smul, hx, gate_eval_smul, gate_eval_smul]

variable [MeasureClass qs]

/-- **The ideal multiplier commutes with the Z projectors of `q` on its domain.** -/
theorem idealCtrlModMul_commP_dom {c N ctrl q : ℕ} {data : Reg} (hN : 1 < N)
    (hNd : N ≤ ASize data) (hc : Nat.Coprime c N) (hctrl : ctrl ∉ data.qubits)
    (hqd : q ∉ data.qubits) (o : ℕ) {ψ : qs.State} (hψ : ψ ∈ IdealDom qs N data) :
    qs.eval (Gate.idealCtrlModMul c N data ctrl) (measProj (qubitReg q) o ψ)
      = measProj (qubitReg q) o (qs.eval (Gate.idealCtrlModMul c N data ctrl) ψ) := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    have hk := IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact (qs := qs) c N data
      ctrl y hN hNd hc hctrl hy
    rw [measProj_qubitReg_ket, hk, measProj_ket_keep (RegEncoding.bit_writeNat_out _ _ _ _ hqd)]
    by_cases ho : (if RegEncoding.bit q y then 1 else 0) = o
    · simp only [ho, ↓reduceIte, hk]
    · simp only [ho, ↓reduceIte, MGate.gate_eval_zero_state]
  | zero => simp only [map_zero, MGate.gate_eval_zero_state]
  | add x y _ _ hx hy => rw [map_add, gate_eval_add, hx, hy, gate_eval_add, map_add]
  | smul a x _ hx => rw [map_smul, gate_eval_smul, hx, gate_eval_smul, map_smul]

omit [MeasureClass qs] in
/-- **Gate locality on the domain, `X` half.** -/
theorem gate_commX_on {D : Submodule ℂ qs.State} {q : ℕ} {U : Gate} (h : U.IdealSafe qs D q)
    {ψ : qs.State} (hψ : ψ ∈ D) :
    qs.eval U (qs.eval (Gate.X q) ψ) = qs.eval (Gate.X q) (qs.eval U ψ) := by
  induction h generalizing ψ with
  | local_ U hU hq => exact gate_commX_exact U hU hq ψ
  | ideal c N data ctrl hN hNd hc hctrl hqd hqc hD =>
    exact idealCtrlModMul_commX_dom hN hNd hc hctrl hqd hqc (hD hψ)
  | seq U V _ _ hP ihU ihV =>
    simp only [QSemantics.eval, GateSemanticsCore.eval_seq] at ihU ihV ⊢
    rw [ihU hψ, ihV (hP ψ hψ)]

/-- **Gate locality on the domain, projector half.** -/
theorem gate_commP_on {D : Submodule ℂ qs.State} {q : ℕ} {U : Gate} (h : U.IdealSafe qs D q)
    (o : ℕ) {ψ : qs.State} (hψ : ψ ∈ D) :
    qs.eval U (measProj (qubitReg q) o ψ) = measProj (qubitReg q) o (qs.eval U ψ) := by
  induction h generalizing ψ with
  | local_ U hU hq => exact gate_commP_exact U hU hq o ψ
  | ideal c N data ctrl hN hNd hc hctrl hqd hqc hD =>
    exact idealCtrlModMul_commP_dom hN hNd hc hctrl hqd o (hD hψ)
  | seq U V _ _ hP ihU ihV =>
    simp only [QSemantics.eval, GateSemanticsCore.eval_seq] at ihU ihV ⊢
    rw [ihU hψ, ihV (hP ψ hψ)]

variable [LowerGateClass qs]

/-- **Program locality on the domain.** An `IdealSafe` program has `q` as a spectator on `D`:
it commutes, branch by branch, with `X q` and with the Z projectors of `q`, on every branching
state whose branches lie in `D`. -/
theorem MGate.spectatorOn_of_idealSafe {D : Submodule ℂ qs.State} {q : ℕ} {P : MGate}
    (h : P.IdealSafe qs D q) : P.SpectatorOn q D := by
  induction h with
  | local_ P hP hq => exact MGate.spectatorOn_exact P hP hq |>.mono le_top
  | unitary g hg =>
    refine ⟨fun ψ hψ => ?_, fun o ψ hψ => ?_⟩
    · funext r; exact gate_commX_on hg (hψ r)
    · funext r; exact gate_commP_on hg o (hψ r)
  | seq a b _ _ hP iha ihb =>
    refine ⟨fun ψ hψ => ?_, fun o ψ hψ => ?_⟩
    · simp only [MGate.eval_seq]
      rw [iha.commX ψ hψ, ihb.commX _ (hP ψ hψ)]
    · simp only [MGate.eval_seq]
      rw [iha.commP o ψ hψ, ihb.commP o _ (hP ψ hψ)]

end Safe

/-! ## Structural domain preservation for `IdealDom` -/

section Keeps
variable {qs : QSemantics} [RegEncoding qs.Basis]

/-- Gates that keep `IdealDom N data`, structurally. -/
inductive _root_.Shor.Gate.KeepsDom (N : ℕ) (data : Reg) : Gate → Prop
  | id : Gate.KeepsDom N data Gate.id
  | H (p : ℕ) : p ∉ data.qubits → Gate.KeepsDom N data (Gate.H p)
  | X (p : ℕ) : p ∉ data.qubits → Gate.KeepsDom N data (Gate.X p)
  | SignedPhaseProd (phi : Angle) (x z : ExtReg) :
      Gate.KeepsDom N data (Gate.SignedPhaseProd phi x z)
  | CSignedPhaseProd (ctrl : ℕ) (phi : Angle) (x z : ExtReg) :
      Gate.KeepsDom N data (Gate.CSignedPhaseProd ctrl phi x z)
  | ideal (c ctrl : ℕ) : 1 < N → N ≤ ASize data → Nat.Coprime c N → ctrl ∉ data.qubits →
      Gate.KeepsDom N data (Gate.idealCtrlModMul c N data ctrl)
  | seq (U V : Gate) : Gate.KeepsDom N data U → Gate.KeepsDom N data V →
      Gate.KeepsDom N data (U ;; V)

/-- Programs that keep `IdealDom N data` on every branch, structurally. -/
inductive _root_.Shor.MGate.KeepsDom (N : ℕ) (data : Reg) : MGate → Prop
  | unitary (g : Gate) : g.KeepsDom N data → MGate.KeepsDom N data (.unitary g)
  | measureReset (p : ℕ) : p ∉ data.qubits → MGate.KeepsDom N data (.measureReset p)
  | ffPhase (p j : ℕ) : MGate.KeepsDom N data (.ffPhase p j)
  | seq (a b : MGate) : MGate.KeepsDom N data a → MGate.KeepsDom N data b →
      MGate.KeepsDom N data (.seq a b)

variable [GateSemanticsFacts qs]

/-- `X p`, `p ∉ data`, keeps the domain. -/
theorem idealDom_X {N : ℕ} {data : Reg} {p : ℕ} (hp : p ∉ data.qubits) {φ : qs.State}
    (hφ : φ ∈ IdealDom qs N data) : qs.eval (Gate.X p) φ ∈ IdealDom qs N data :=
  idealDom_map (f := gateL (Gate.X p)) (fun x hx => by
    rw [gateL_apply, eval_X_ket_flipBit]
    exact ket_mem_idealDom (by rwa [toNat_flipBit hp])) hφ

/-- **Structural preservation, gates.** -/
theorem _root_.Shor.Gate.KeepsDom.preserves {N : ℕ} {data : Reg} {U : Gate} (h : U.KeepsDom N data) :
    GatePreserves qs (IdealDom qs N data) U := by
  induction h with
  | id => intro ψ hψ; rwa [QSemantics.eval, GateSemanticsCore.eval_id]
  | H p hp =>
    intro ψ hψ
    refine idealDom_map (f := gateL (Gate.H p)) (fun x hx => ?_) hψ
    rw [gateL_apply, HadamardSemantics.eval_H_ket]
    refine Submodule.smul_mem _ _ (Submodule.add_mem _ (ket_mem_idealDom ?_)
      (Submodule.smul_mem _ _ (ket_mem_idealDom ?_)))
    · rwa [toNat_writeNat_qubitReg_out hp]
    · rwa [toNat_writeNat_qubitReg_out hp]
  | X p hp => intro ψ hψ; exact idealDom_X hp hψ
  | SignedPhaseProd phi x z =>
    intro ψ hψ
    refine idealDom_map (f := gateL (Gate.SignedPhaseProd phi x z)) (fun y hy => ?_) hψ
    rw [gateL_apply, PhaseSemantics.eval_SignedPhaseProd_ket]
    exact Submodule.smul_mem _ _ (ket_mem_idealDom hy)
  | CSignedPhaseProd ctrl phi x z =>
    intro ψ hψ
    refine idealDom_map (f := gateL (Gate.CSignedPhaseProd ctrl phi x z)) (fun y hy => ?_) hψ
    rw [gateL_apply, PhaseSemantics.eval_CSignedPhaseProd_ket]
    split_ifs
    · exact Submodule.smul_mem _ _ (ket_mem_idealDom hy)
    · exact ket_mem_idealDom hy
  | ideal c ctrl hN hNd hcN hctrl =>
    intro ψ hψ
    refine idealDom_map (f := gateL (Gate.idealCtrlModMul c N data ctrl)) (fun y hy => ?_) hψ
    rw [gateL_apply, IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact c N data ctrl
      _ hN hNd hcN hctrl hy]
    have hv : (if RegEncoding.bit ctrl y then c * RegEncoding.toNat data y % N
        else RegEncoding.toNat data y) < N := by
      split_ifs
      · exact Nat.mod_lt _ (by omega)
      · exact hy
    exact ket_mem_idealDom (by
      rw [RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le hv hNd)]; exact hv)
  | seq U V _ _ ihU ihV =>
    intro ψ hψ
    rw [QSemantics.eval, GateSemanticsCore.eval_seq]
    exact ihV _ (ihU ψ hψ)

variable [LowerGateClass qs] [MeasureClass qs]

omit [GateSemanticsFacts qs] [LowerGateClass qs] in
/-- The Born projectors of a qubit keep the domain. -/
theorem idealDom_measProj {N : ℕ} {data : Reg} (p o : ℕ) {φ : qs.State}
    (hφ : φ ∈ IdealDom qs N data) : measProj (qubitReg p) o φ ∈ IdealDom qs N data :=
  idealDom_map (f := (measProj (qubitReg p) o).toLinearMap) (fun x hx => by
    simp only [ContinuousLinearMap.coe_coe]
    rw [measProj_qubitReg_ket]
    split_ifs <;> first | exact ket_mem_idealDom hx | exact Submodule.zero_mem _) hφ

/-- **Structural preservation, programs.** -/
theorem _root_.Shor.MGate.KeepsDom.preserves {N : ℕ} {data : Reg} {P : MGate} (h : P.KeepsDom N data) :
    MPreserves qs (IdealDom qs N data) P := by
  induction h with
  | unitary g hg => intro ψ hψ r; exact hg.preserves _ (hψ r)
  | measureReset p hp =>
    intro ψ hψ r
    simp only [MGate.eval]
    split
    · exact Submodule.zero_mem _
    · unfold measureResetBranch
      split
      · exact idealDom_X hp (idealDom_measProj p 1 (hψ _))
      · exact idealDom_measProj p 0 (hψ _)
  | ffPhase p j =>
    intro ψ hψ r
    refine idealDom_map (f := lowL (LowGate.Phase p (ffAngle j r))) (fun y hy => ?_) (hψ r)
    rw [lowL_apply, evalL_Phase_ket_diag]
    exact Submodule.smul_mem _ _ (ket_mem_idealDom hy)
  | seq a b _ _ iha ihb =>
    intro ψ hψ r
    exact ihb _ (iha ψ hψ) r

end Keeps

end Readout
end Shor
