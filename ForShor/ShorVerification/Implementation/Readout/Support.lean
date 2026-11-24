import ForShor.ShorVerification.Implementation.Readout.ShorStatement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Registers

/-!
# Readout: which qubits the semiclassical circuit names

The point of the semiclassical readout is that the exponent register is gone.
`orderFindingSemiclassical_support` states it: every qubit the circuit names is
the control `c`, a qubit of the data, work or scratch register (spare qubits
included) or the flag.

`Gate.qubitSupport g` is SYNTACTIC: the set of qubits named by the operands of
the constructors of `g`. A register operand of type `ExtReg` counts with all
its owned qubits (active and reserve), since the lowering may allocate workspace
in the reserve. `MGate.qubitSupport` adds the measured / phased qubit of
`measureReset` and `ffPhase`. This is not a semantic locality theorem (that
`eval` acts as the identity on other qubits); it is the statement about the
circuit's text that the qubit count is read from. The register `x` of the
success theorems (`Readout/Shor.lean`) is a ghost register: it occurs only in
their hypotheses (to fix `m` and `Q`), and no qubit of it is needed by the
machine except possibly `c` itself.
-/

namespace Shor

/-- The qubits named by the operands of a high-level gate (`ExtReg` operands
with their reserves). Syntactic; see the module docstring. -/
def Gate.qubitSupport : Gate → Set ℕ
  | .id => ∅
  | .seq U V => U.qubitSupport ∪ V.qubitSupport
  | .adj U => U.qubitSupport
  | .H q => {q}
  | .X q => {q}
  | .CNOT a b => {a, b}
  | .Toffoli a b t => {a, b, t}
  | .QFT r => {q | q ∈ r.ownedQubits}
  | .RadixReverse r _ => {q | q ∈ r.qubits}
  | .SignedPhaseProd _ x z => {q | q ∈ x.ownedQubits ∨ q ∈ z.ownedQubits}
  | .CSignedPhaseProd ctrl _ x z => {q | q = ctrl ∨ q ∈ x.ownedQubits ∨ q ∈ z.ownedQubits}
  | .CmpGeConst _ d s f => {q | q ∈ d.ownedQubits ∨ q ∈ s.ownedQubits ∨ q = f}
  | .CSubConst _ d s f => {q | q ∈ d.ownedQubits ∨ q ∈ s.ownedQubits ∨ q = f}
  | .ShiftL r _ => {q | q ∈ r.ownedQubits}
  | .ShiftR r _ => {q | q ∈ r.ownedQubits}
  | .Negate r => {q | q ∈ r.ownedQubits}
  | .AddScaled d s _ _ => {q | q ∈ d.ownedQubits ∨ q ∈ s.ownedQubits}
  | .zeroExtend r _ => {q | q ∈ r.ownedQubits}
  | .signExtend r _ => {q | q ∈ r.ownedQubits}
  | .zeroDealloc r _ => {q | q ∈ r.ownedQubits}
  | .signDealloc r _ => {q | q ∈ r.ownedQubits}
  | .idealCtrlModMul _ _ data ctrl => {q | q ∈ data.qubits ∨ q = ctrl}

/-- The qubits named by a measurement-language program: those of its gates,
and the qubit of every `measureReset` and `ffPhase`. -/
def MGate.qubitSupport : MGate → Set ℕ
  | .unitary g => g.qubitSupport
  | .seq a b => a.qubitSupport ∪ b.qubitSupport
  | .measureReset q => {q}
  | .ffPhase q _ => {q}

/-- The qubits of the semiclassical circuit's registers: the control `c`, the
owned qubits of `y`, `work`, `scratch`, and the flag. -/
def semiclassicalQubits (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) : Set ℕ :=
  {q | q = c ∨ q ∈ y.ownedQubits ∨ q ∈ work.ownedQubits ∨ q ∈ scratch.ownedQubits ∨ q = flag}

namespace Readout

section
variable {c flag : ℕ} {y work scratch : ExtReg}

private theorem mem_S_y {q : ℕ} (h : q ∈ y.ownedQubits) :
    q ∈ semiclassicalQubits c y work scratch flag := Or.inr (Or.inl h)
private theorem mem_S_w {q : ℕ} (h : q ∈ work.ownedQubits) :
    q ∈ semiclassicalQubits c y work scratch flag := Or.inr (Or.inr (Or.inl h))
private theorem mem_S_s {q : ℕ} (h : q ∈ scratch.ownedQubits) :
    q ∈ semiclassicalQubits c y work scratch flag := Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- `H_reg r` names only the qubits of `r`. -/
theorem H_reg_qubitSupport (r : Reg) : (H_reg r).qubitSupport ⊆ {q | q ∈ r.qubits} := by
  have key : ∀ (l : List ℕ) (acc : Gate),
      (l.foldl (fun acc q => Gate.H q ;; acc) acc).qubitSupport ⊆ acc.qubitSupport ∪ {q | q ∈ l} := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc q hq
      rcases ih _ hq with h | h
      · simp only [Gate.qubitSupport, Set.mem_union, Set.mem_singleton_iff] at h
        rcases h with rfl | h
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
  intro q hq
  rcases key _ _ hq with h | h
  · simp [Gate.qubitSupport] at h
  · exact h

@[simp] theorem ownedQubits_withReserve (a r : Reg) (h : Disjoint a r) :
    (ExtReg.withReserve a r h).ownedQubits = a.qubits ++ r.qubits := rfl

/-- Owned qubits of a register with its reserve shortened by `drop`. -/
theorem mem_owned_dropReserve (e : ExtReg) (n q : ℕ)
    (h : q ∈ (ExtReg.withReserve e.active (e.reserve.drop n)
      (e.active_disjoint_reserve_drop n)).ownedQubits) : q ∈ e.ownedQubits := by
  simp only [ExtReg.ownedQubits, ExtReg.withReserve_active, ExtReg.withReserve_reserve,
    List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_of_mem_drop h)

/-- **The real multiplier names only the multiplier's registers.** Every qubit
named by `CmodMulInPlaceCore cm N c y work scratch flag hw hs4` is `c`, an owned
qubit of `y`, `work` or `scratch`, or `flag`. -/
theorem cmodMul_qubitSupport (cm N : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    (CmodMulInPlaceCore cm N c y work scratch flag hw hs4).qubitSupport
      ⊆ semiclassicalQubits c y work scratch flag := by
  have hW : ∀ q, q ∈ work.active.qubits → q ∈ semiclassicalQubits c y work scratch flag :=
    fun q h => mem_S_w (List.mem_append_left _ h)
  have hHw : (H_reg work.active).qubitSupport ⊆ semiclassicalQubits c y work scratch flag :=
    fun q h => hW q (H_reg_qubitSupport _ h)
  have hzR : hs4.mulWorkspace.zReserve = scratch.reserve := hs4.mul_zReserve_eq
  have hxR : hs4.mulWorkspace.xReserve = work.reserve := hs4.mul_xReserve_eq
  have hSign : ∀ h, cmpLtNWSignQubit scratch h ∈ scratch.ownedQubits := fun h =>
    List.mem_append_left _ (List.get_mem _ _)
  intro q hq
  simp only [CmodMulInPlaceCore, step1, step2, step3, step4, step5, cmpLtNW, fastConstMulInto,
    cmpLtNWDifference, IQFT, Gate.PhaseProdUsing, Gate.CPhaseProdUsing, Gate.qubitSupport,
    Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_insert_iff] at hq
  simp only [ModMulCircuitWorkspaceOK.step1Workspace, ModMulCircuitWorkspaceOK.step2Workspace,
    ModMulCircuitWorkspaceOK.step5Workspace, Gate.PhaseProdWorkspace.xExt,
    Gate.PhaseProdWorkspace.zExt, Gate.PhaseProdWorkspace.ofExtRegs,
    Gate.ExtReg.ownedQubits_grow, ownedQubits_withReserve, hzR, hxR, List.mem_append] at hq
  by_contra hS
  have nY : q ∉ y.ownedQubits := fun h => hS (mem_S_y h)
  have nW : q ∉ work.ownedQubits := fun h => hS (mem_S_w h)
  have nS : q ∉ scratch.ownedQubits := fun h => hS (mem_S_s h)
  have nYa : q ∉ y.active.qubits := fun h => nY (List.mem_append_left _ h)
  have nYr : q ∉ y.reserve.qubits := fun h => nY (List.mem_append_right _ h)
  have nYd : q ∉ (y.reserve.drop 1).qubits := fun h => nYr (List.mem_of_mem_drop h)
  have nWa : q ∉ work.active.qubits := fun h => nW (List.mem_append_left _ h)
  have nWr : q ∉ work.reserve.qubits := fun h => nW (List.mem_append_right _ h)
  have nSa : q ∉ scratch.active.qubits := fun h => nS (List.mem_append_left _ h)
  have nSr : q ∉ scratch.reserve.qubits := fun h => nS (List.mem_append_right _ h)
  have nc : q ≠ c := fun h => hS (Or.inl h)
  have nf : q ≠ flag := fun h => hS (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have nH : q ∉ (H_reg work.active).qubitSupport := fun h => hS (hHw h)
  have nSg : ∀ h, q ≠ cmpLtNWSignQubit scratch h := fun h e => nS (e ▸ hSign h)
  have nG : ∀ e : ExtReg, e.ownedQubits = y.ownedQubits →
      q ∉ e.active.qubits ∧ q ∉ e.reserve.qubits := fun e he =>
    ⟨fun h => nY (he ▸ List.mem_append_left _ h), fun h => nY (he ▸ List.mem_append_right _ h)⟩
  have g1 := nG (y.grow 1) (Gate.ExtReg.ownedQubits_grow y 1)
  simp [nY, nS, nYa, nYd, nWa, nWr, nSa, nSr, nc, nf, nH, nSg, g1.1, g1.2] at hq

/-- `initY1 r` names at most one qubit of `r`. -/
theorem initY1_qubitSupport (r : Reg) : (initY1 r).qubitSupport ⊆ {q | q ∈ r.qubits} := by
  intro q hq
  unfold initY1 at hq
  split at hq
  · simp [Gate.qubitSupport] at hq
  · rename_i q0 rest h
    simp only [Gate.qubitSupport, Set.mem_singleton_iff] at hq
    show q ∈ r.qubits
    rw [h, hq]
    exact List.mem_cons_self ..

/-- **Qubit support of the semiclassical order-finding circuit.** Every qubit
named by `orderFindingSemiclassical a N c m y work scratch flag hw hs4` (for any
number of rounds `m`) is the control `c`, an owned qubit (active or spare) of
the data register `y`, the work register or the scratch register, or the flag.
There is no exponent register: the reference register `x` of the success
theorems is a ghost register that appears only in their hypotheses to fix `m`
and `Q`, and the machine needs none of its qubits
(`orderFindingSemiclassical_avoids`). -/
theorem orderFindingSemiclassical_support (a N m : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    (orderFindingSemiclassical a N c m y work scratch flag hw hs4).qubitSupport
      ⊆ semiclassicalQubits c y work scratch flag := by
  have hc : c ∈ semiclassicalQubits c y work scratch flag := Or.inl rfl
  have hrounds : ∀ k, (readoutRounds (semiclassicalMultipliers a N c m y work scratch flag hw hs4)
      c k).qubitSupport ⊆ semiclassicalQubits c y work scratch flag := by
    intro k
    induction k with
    | zero => simp [readoutRounds, MGate.qubitSupport, Gate.qubitSupport]
    | succ k ih =>
      simp only [readoutRounds, MGate.qubitSupport, Gate.qubitSupport, Set.union_subset_iff,
        Set.singleton_subset_iff]
      exact ⟨ih, hc, cmodMul_qubitSupport _ N hw hs4, hc, hc, hc⟩
  simp only [orderFindingSemiclassical, MGate.qubitSupport, Set.union_subset_iff]
  exact ⟨fun q h => mem_S_y (List.mem_append_left _ (initY1_qubitSupport _ h)), hrounds m⟩

/-- **The circuit needs no qubit of a register outside its own.** If no owned
qubit of `x` is the control, the flag, or an owned qubit of `y`, `work` or
`scratch`, then the semiclassical circuit names no qubit of `x`. -/
theorem orderFindingSemiclassical_avoids (a N m : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (x : ExtReg)
    (hx : ∀ q ∈ x.ownedQubits, q ∉ semiclassicalQubits c y work scratch flag) :
    ∀ q ∈ x.ownedQubits,
      q ∉ (orderFindingSemiclassical a N c m y work scratch flag hw hs4).qubitSupport :=
  fun q hq h => hx q hq (orderFindingSemiclassical_support a N m hw hs4 h)

end

/-- **On the coherent layout, the exponent register is unused.** Under a
`ShorApproxSetup`, every exponent qubit other than `c` is outside the
semiclassical circuit's registers; with `orderFindingSemiclassical_support` the
semiclassical circuit on that layout names no exponent qubit except (possibly)
the control `c` itself. -/
theorem exponent_outside_semiclassicalQubits {qs : QSemantics} [RegEncoding qs.Basis] {η : ℝ}
    {N c : ℕ} {x y work scratch : ExtReg} {flag : ℕ} {b0 : qs.Basis}
    (h : ShorApproxSetup qs η N x y work scratch flag b0) :
    ∀ q ∈ x.active.qubits, q ≠ c → q ∉ semiclassicalQubits c y work scratch flag := by
  intro q hq hqc hS
  obtain ⟨j, hj⟩ := List.get_of_mem hq
  let i : Fin (regSize x.active) := ⟨j.1, by simp [regSize, Reg.width]⟩
  have hget : x.active.get i = q := by
    dsimp [i, Reg.get]
    simpa [Reg.width] using hj
  have hl : ModMulCoreLayout y work flag q := hget ▸ h.register_layout i
  obtain ⟨-, -, -, hqy, hqw, hqf⟩ := hl
  rcases hS with h1 | h1 | h1 | h1 | h1
  · exact hqc h1
  · exact hqy h1
  · exact hqw h1
  · exact h.exponent_scratch_disjoint (List.mem_append_left _ hq) h1
  · exact hqf h1

end Readout
end Shor
