import FastMultiplication.ShorVerification.Implementation.AlgorithmCorrectness.ModMulBounds.Core
import FastMultiplication.ShorVerification.Implementation.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.Workspace.PhaseProductLowering

open Shor

universe v

/-! =========================================================
    Algorithm 1 Expansion Lemmas

This file expands the staged Algorithm 1 gates on valid basis states and builds
the finite reference trace used by the quantitative modular-multiplication
bounds. The main endpoint is `alg1_trace_of_valid`, which packages a valid input
state as an `Alg1Trace` with Step-1 coefficients and the Step-3/4 support
condition needed later.
========================================================= -/

/-! ---------------------------------------------------------
    Staged-gate equivalence

The public approximate modular-multiplication gate is definitionally the same
as the staged `U1 ; U2 ; U34 ; U5` presentation used by the error proof.
--------------------------------------------------------- -/

section StagedGateEquivalence

namespace ModMulConfig

lemma eval_approxGate_eq_staged
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State) :
    qs.eval (ModMulConfig.approxGate (Basis := qs.Basis) cfg) ψ
      =
    qs.eval (ModMulConfig.stagedGate (Basis := qs.Basis) cfg) ψ := by
  simp [ModMulConfig.approxGate,CmodMulInPlaceCore,
    ModMulConfig.stagedGate, ModMulConfig.U1,ModMulConfig.U2,
    ModMulConfig.U34,ModMulConfig.U5,qs.eval_seq,step2]

end ModMulConfig

end StagedGateEquivalence

/-! ---------------------------------------------------------
    Linear expansion helpers

These lemmas push gate evaluation through finite sums and expose the two basic
Step-1 pieces: inverse QFT on the work register and the controlled PhaseProduct
as a diagonal operation on each work label.
--------------------------------------------------------- -/

section LinearExpansionHelpers

/-- Gate evaluation distributes over finite sums by linearity. -/
lemma eval_finset_sum
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    {ι : Type*}
    (s : Finset ι)
    (f : ι → qs.State) :
    qs.eval U (∑ i ∈ s, f i)
      =
    ∑ i ∈ s, qs.eval U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using qs.eval_zero U
  | insert a s ha ih =>
      simp [Finset.sum_insert, ha, qs.eval_add, ih]


/-- Expands inverse QFT on an extended work register as a finite basis sum over its active labels. -/
lemma eval_iqft_work_expansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [QFTSemantics qs]
    (work : ExtReg)
    (b : qs.Basis) :
    ∃ α : Fin (ASize work.active) → ℂ,
      qs.eval (IQFT work) (qs.ket b)
        =
      ∑ t : Fin (ASize work.active),
        α t •
          qs.ket
            (RegEncoding.writeNat work.active t.1 b) := by
  refine ⟨
    fun t =>
      (1 / Real.sqrt ((ASize work.active : ℕ) : ℝ) : ℂ) *
        star
          (qftPhase
            (ASize work.active)
            (RegEncoding.toNat work.active b)
            t.1),
    ?_
  ⟩
  unfold IQFT
  rw [QFTSemantics.eval_adj_QFT_ket]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [smul_smul]
  simp [ExtReg.toNat]

/-- On a clean unsigned PhaseProduct workspace, the controlled phase product is diagonal in the work label. -/
lemma eval_cphaseprodusing_work_diagonal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (ctrl : ℕ)
    (φ : ℝ)
    (data work : Reg)
    (ws : Gate.PhaseProdWorkspace data work)
    (b : qs.Basis)
    (z : Fin (ASize work))
    (hclean : ws.Clean (RegEncoding.writeNat work z.1 b)) :
    ∃ L : ℂ,
      qs.eval (Gate.CPhaseProdUsing ctrl φ data work ws)
          (qs.ket (RegEncoding.writeNat work z.1 b))
        =
      L • qs.ket (RegEncoding.writeNat work z.1 b) := by
  let b' := RegEncoding.writeNat work z.1 b

  refine ⟨
    if RegEncoding.bit ctrl b' then
      Complex.exp
        (φ * Complex.I *
          ((RegEncoding.toNat data b' : ℂ) *
           (RegEncoding.toNat work b' : ℂ)))
    else
      1,
    ?_
  ⟩

  simpa [b'] using
    GateSemanticsFacts.eval_CPhaseProdUsing_ket qs ctrl φ data work ws b' hclean


end LinearExpansionHelpers

/-! ---------------------------------------------------------
    Work-register support spans

The Step-1 expansion needs to show that applying Hadamards to the work register
keeps the state supported on basis states obtained by writing only that register.
The private `HRegWorkSpan` predicate and helper lemmas provide this local
closure argument.
--------------------------------------------------------- -/

section WorkRegisterSupportSpans

open QSemantics

/-- States supported entirely on `work`, relative to an unchanged base state. -/
private def HRegWorkSpan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (ψ : qs.State) : Prop :=
  ∃ α : Fin (ASize work) → ℂ,
    ψ =
      ∑ t : Fin (ASize work),
        α t •
          qs.ket (RegEncoding.writeNat work t.1 base)


/-- The zero state is trivially supported on the work-register span. -/
private lemma hregWorkSpan_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis) :
    HRegWorkSpan qs work base (0 : qs.State) := by
  refine ⟨fun _ => 0, ?_⟩
  simp


/-- Work-register support is closed under addition. -/
private lemma hregWorkSpan_add
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (ψ φ : qs.State) :
    HRegWorkSpan qs work base ψ →
    HRegWorkSpan qs work base φ →
    HRegWorkSpan qs work base (ψ + φ) := by
  rintro ⟨α, hα⟩ ⟨β, hβ⟩
  refine ⟨fun t => α t + β t, ?_⟩

  rw [hα, hβ, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  simp [add_smul]


/-- Work-register support is closed under scalar multiplication. -/
private lemma hregWorkSpan_smul
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (a : ℂ)
    (ψ : qs.State) :
    HRegWorkSpan qs work base ψ →
    HRegWorkSpan qs work base (a • ψ) := by
  rintro ⟨α, hα⟩
  refine ⟨fun t => a * α t, ?_⟩

  rw [hα, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [smul_smul]


/-- A finite sum of work-supported states is work-supported. -/
private lemma hregWorkSpan_sum
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    {ι : Type*}
    (s : Finset ι)
    (f : ι → qs.State)
    (hf : ∀ i ∈ s, HRegWorkSpan qs work base (f i)) :
    HRegWorkSpan qs work base (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hregWorkSpan_zero qs work base

  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply hregWorkSpan_add qs work base
      · exact hf a (by simp)
      · apply ih
        intro i hi
        exact hf i (by simp [hi])


/-- A single basis state obtained by writing `work` is in the work-register span. -/
private lemma hregWorkSpan_ket_write
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (z : Fin (ASize work)) :
    HRegWorkSpan qs work base
      (qs.ket (RegEncoding.writeNat work z.1 base)) := by
  classical
  refine ⟨fun t => if t = z then 1 else 0, ?_⟩
  simp


/--
Writing qubit `q` inside `work` can be represented as one whole-register
write to `work`, relative to the original `base`.
-/
private lemma qubit_write_eq_work_write
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (q : ℕ)
    (hq : q ∈ work.qubits)
    (z : Fin (ASize work))
    (v : ℕ) :
    ∃ t : Fin (ASize work),
      RegEncoding.writeNat
          (qubitReg q)
          v
          (RegEncoding.writeNat work z.1 base)
        =
      RegEncoding.writeNat work t.1 base := by
  classical

  let bout : qs.Basis :=
    RegEncoding.writeNat
      (qubitReg q)
      v
      (RegEncoding.writeNat work z.1 base)

  let t : Fin (ASize work) :=
    ⟨RegEncoding.toNat work bout,
      RegEncoding.toNat_lt_ASize work bout⟩

  refine ⟨t, ?_⟩
  change bout = RegEncoding.writeNat work t.1 base

  apply RegEncoding.basis_ext
  intro p

  by_cases hp : p ∈ work.qubits

  ·
    have hrewrite :
        RegEncoding.writeNat work t.1 bout = bout := by
      simpa [t] using
        (RegEncoding.writeNat_toNat work bout)

    have hin :
        RegEncoding.bit p
            (RegEncoding.writeNat work t.1 base)
          =
        RegEncoding.bit p
            (RegEncoding.writeNat work t.1 bout) :=
      RegEncoding.bit_writeNat_in work t.1 base bout p hp

    calc
      RegEncoding.bit p bout
          =
        RegEncoding.bit p
          (RegEncoding.writeNat work t.1 bout) := by
            rw [hrewrite]
      _ =
        RegEncoding.bit p
          (RegEncoding.writeNat work t.1 base) := by
            symm
            exact hin

  ·
    have hne : p ≠ q := by
      intro hpq
      subst hpq
      exact hp hq

    have hqout : p ∉ (qubitReg q).qubits := by
      simp [qubitReg, Reg.singleton, hne]

    have hout_qubit :
        RegEncoding.bit p bout
          =
        RegEncoding.bit p
          (RegEncoding.writeNat work z.1 base) := by
      simpa [bout] using
        (RegEncoding.bit_writeNat_out
          (r := qubitReg q)
          (v := v)
          (b := RegEncoding.writeNat work z.1 base)
          (q := p)
          hqout)

    have hout_work_z :
        RegEncoding.bit p
            (RegEncoding.writeNat work z.1 base)
          =
        RegEncoding.bit p base :=
      RegEncoding.bit_writeNat_out
        (r := work)
        (v := z.1)
        (b := base)
        (q := p)
        hp

    have hout_work_t :
        RegEncoding.bit p
            (RegEncoding.writeNat work t.1 base)
          =
        RegEncoding.bit p base :=
      RegEncoding.bit_writeNat_out
        (r := work)
        (v := t.1)
        (b := base)
        (q := p)
        hp

    calc
      RegEncoding.bit p bout
          =
        RegEncoding.bit p
          (RegEncoding.writeNat work z.1 base) :=
            hout_qubit
      _ =
        RegEncoding.bit p base :=
            hout_work_z
      _ =
        RegEncoding.bit p
          (RegEncoding.writeNat work t.1 base) := by
            symm
            exact hout_work_t


/-- A one-qubit write inside `work` still lands in the whole-work-register span. -/
private lemma hregWorkSpan_qubit_write
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (q : ℕ)
    (hq : q ∈ work.qubits)
    (z : Fin (ASize work))
    (v : ℕ) :
    HRegWorkSpan qs work base
      (qs.ket
        (RegEncoding.writeNat
          (qubitReg q)
          v
          (RegEncoding.writeNat work z.1 base))) := by
  rcases
      qubit_write_eq_work_write
        qs work base q hq z v with
    ⟨t, ht⟩

  rw [ht]
  exact hregWorkSpan_ket_write qs work base t


/-- A Hadamard on a qubit inside `work` preserves work-register support. -/
private lemma eval_H_preserves_hregWorkSpan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [HadamardSemantics qs]
    (work : Reg)
    (base : qs.Basis)
    (q : ℕ)
    (hq : q ∈ work.qubits)
    (ψ : qs.State) :
    HRegWorkSpan qs work base ψ →
    HRegWorkSpan qs work base (qs.eval (Gate.H q) ψ) := by
  intro hψ
  rcases hψ with ⟨α, hα⟩

  have heval :
      qs.eval (Gate.H q) ψ
        =
      ∑ t : Fin (ASize work),
        α t •
          qs.eval
            (Gate.H q)
            (qs.ket (RegEncoding.writeNat work t.1 base)) := by
    calc
      qs.eval (Gate.H q) ψ
          =
        qs.eval (Gate.H q)
          (∑ t : Fin (ASize work),
            α t •
              qs.ket (RegEncoding.writeNat work t.1 base)) := by
            rw [hα]

      _ =
        ∑ t : Fin (ASize work),
          qs.eval
            (Gate.H q)
            (α t •
              qs.ket (RegEncoding.writeNat work t.1 base)) := by
            simpa using
              eval_finset_sum
                qs
                (Gate.H q)
                Finset.univ
                (fun t =>
                  α t •
                    qs.ket
                      (RegEncoding.writeNat work t.1 base))

      _ =
        ∑ t : Fin (ASize work),
          α t •
            qs.eval
              (Gate.H q)
              (qs.ket (RegEncoding.writeNat work t.1 base)) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [qs.eval_smul]

  have hterm :
      ∀ t : Fin (ASize work),
        HRegWorkSpan qs work base
          (α t •
            qs.eval
              (Gate.H q)
              (qs.ket (RegEncoding.writeNat work t.1 base))) := by
    intro t

    apply hregWorkSpan_smul qs work base

    rw [HadamardSemantics.eval_H_ket
      (qs := qs)
      (q := q)
      (b := RegEncoding.writeNat work t.1 base)]

    apply hregWorkSpan_smul qs work base
    apply hregWorkSpan_add qs work base

    · exact
        hregWorkSpan_qubit_write
          qs work base q hq t 0

    ·
      apply hregWorkSpan_smul qs work base
      exact
        hregWorkSpan_qubit_write
          qs work base q hq t 1

  have hsum :
      HRegWorkSpan qs work base
        (∑ t : Fin (ASize work),
          α t •
            qs.eval
              (Gate.H q)
              (qs.ket (RegEncoding.writeNat work t.1 base))) := by
    apply hregWorkSpan_sum qs work base
    intro t ht
    exact hterm t

  rw [heval]
  exact hsum


/-- A fold of Hadamards over qubits contained in `work` preserves work-register support. -/
private lemma eval_foldl_H_preserves_hregWorkSpan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [HadamardSemantics qs]
    (work : Reg)
    (base : qs.Basis)
    (qsList : List ℕ) :
    (∀ q, q ∈ qsList → q ∈ work.qubits) →
    ∀ (acc : Gate),
      (∀ ξ : qs.State,
        HRegWorkSpan qs work base ξ →
        HRegWorkSpan qs work base (qs.eval acc ξ)) →
      ∀ ξ : qs.State,
        HRegWorkSpan qs work base ξ →
        HRegWorkSpan qs work base
          (qs.eval
            (qsList.foldl
              (fun acc q => Gate.seq (Gate.H q) acc)
              acc)
            ξ) := by
  induction qsList with
  | nil =>
      intro _ acc hacc ξ hξ
      simpa using hacc ξ hξ

  | cons q qsList ih =>
      intro hmem acc hacc ξ hξ

      have hq : q ∈ work.qubits :=
        hmem q (by simp)

      have htail :
          ∀ r, r ∈ qsList → r ∈ work.qubits := by
        intro r hr
        exact hmem r (by simp [hr])

      have hacc' :
          ∀ ξ : qs.State,
            HRegWorkSpan qs work base ξ →
            HRegWorkSpan qs work base
              (qs.eval (Gate.seq (Gate.H q) acc) ξ) := by
        intro ξ hξ

        have hH :
            HRegWorkSpan qs work base
              (qs.eval (Gate.H q) ξ) :=
          eval_H_preserves_hregWorkSpan
            qs work base q hq ξ hξ

        simpa [qs.eval_seq] using
          hacc (qs.eval (Gate.H q) ξ) hH

      simpa [List.foldl] using
        ih
          htail
          (Gate.seq (Gate.H q) acc)
          hacc'
          ξ
          hξ


/-- Applying register Hadamards to a work-written basis state expands over work labels only. -/
lemma eval_Hreg_work_expansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [HadamardSemantics qs]
    (work : Reg)
    (b : qs.Basis)
    (z : Fin (ASize work)) :
    ∃ β : Fin (ASize work) → ℂ,
      qs.eval (H_reg work)
          (qs.ket (RegEncoding.writeNat work z.1 b))
        =
      ∑ t : Fin (ASize work),
        β t •
          qs.ket (RegEncoding.writeNat work t.1 b) := by
  classical

  have hstart :
      HRegWorkSpan qs work b
        (qs.ket (RegEncoding.writeNat work z.1 b)) :=
    hregWorkSpan_ket_write qs work b z

  have hbounds :
      ∀ q, q ∈ regQubits work → q ∈ work.qubits := by
    intro q hq
    simpa [regQubits] using hq

  have hid :
      ∀ ξ : qs.State,
        HRegWorkSpan qs work b ξ →
        HRegWorkSpan qs work b (qs.eval Gate.id ξ) := by
    intro ξ hξ
    simpa [qs.eval_id] using hξ

  have hfinal :
      HRegWorkSpan qs work b
        (qs.eval
          ((regQubits work).foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            Gate.id)
          (qs.ket (RegEncoding.writeNat work z.1 b))) :=
    eval_foldl_H_preserves_hregWorkSpan
      qs
      work
      b
      (regQubits work)
      hbounds
      Gate.id
      hid
      (qs.ket (RegEncoding.writeNat work z.1 b))
      hstart

  rcases hfinal with ⟨β, hβ⟩
  refine ⟨β, ?_⟩
  simpa [H_reg] using hβ

end WorkRegisterSupportSpans

/-! ---------------------------------------------------------
    Step-1 clean workspace and QPE expansion

This section combines reserve-freshness lemmas with the work-span expansion to
obtain the concrete Step-1 QPE packet and identify its coefficients by inner
products.
--------------------------------------------------------- -/

section Step1QPEExpansion

/-- Freshness of two reserve bits implies freshness of the first reserve bit. -/
lemma ExtReg.freshFor_one_of_two
    {Basis : Type v}
    [RegEncoding Basis]
    (e : ExtReg)
    (b : Basis)
    (hcap : e.CanGrow 2)
    (hfresh : e.FreshFor 2 b) :
    e.FreshFor 1 b := by
  unfold ExtReg.FreshFor FreshZero at hfresh ⊢

  let r2 : Reg := e.newBits 2

  have hr2 : regSize r2 = 2 := by
    simp [
      r2,
      ExtReg.newBits,
      Reg.take,
      regSize,
      Reg.width,
      ExtReg.CanGrow,
      ExtReg.capacity
    ] at hcap ⊢
    omega

  let m : SplitPoint r2 :=
    ⟨1, by omega⟩

  have hsplit :=
    RegEncoding.toNat_split
      (r := r2)
      (m := m)
      (b := b)

  have hleft :
      splitLeft r2 m = e.newBits 1 := by
    cases e
    simp [
      r2,
      m,
      splitLeft,
      ExtReg.newBits,
      Reg.take,
      List.take_take
    ]

  have hr2zero :
      RegEncoding.toNat r2 b = 0 := by
    simpa [r2] using hfresh

  dsimp at hsplit
  rw [hr2zero] at hsplit

  have hzero :
      RegEncoding.toNat (splitLeft r2 m) b = 0 := by
    omega

  simpa [hleft] using hzero

/-- Writing an owned-disjoint active register preserves freshness of another register's reserve. -/
lemma ExtReg.freshFor_write_active_of_ownedDisjoint
    {Basis : Type v}
    [RegEncoding Basis]
    (x z : ExtReg)
    (n value : ℕ)
    (b : Basis)
    (hdisj : ExtReg.OwnedDisjoint x z)
    (hfresh : x.FreshFor n b) :
    x.FreshFor n
      (RegEncoding.writeNat z.active value b) := by
  unfold ExtReg.FreshFor at hfresh ⊢

  apply FreshZero.of_eq_on_bits
    (x.newBits n)
    b
    (RegEncoding.writeNat z.active value b)
    ?_
    hfresh

  intro q hqNew

  have hqReserve :
      q ∈ x.reserve.qubits :=
    List.mem_of_mem_take hqNew

  have hqOwnedX :
      q ∈ x.ownedQubits := by
    exact List.mem_append_right _ hqReserve

  have hqNotActiveZ :
      q ∉ z.active.qubits := by
    intro hqActiveZ

    have hqOwnedZ :
        q ∈ z.ownedQubits :=
      List.mem_append_left _ hqActiveZ

    have h := hdisj
    rw [
      ExtReg.OwnedDisjoint,
      List.disjoint_left
    ] at h

    exact h hqOwnedX hqOwnedZ

  exact
    RegEncoding.bit_writeNat_out
      (r := z.active)
      (v := value)
      (b := b)
      (q := q)
      hqNotActiveZ

/-- Writing a work label preserves the clean Step-1 unsigned PhaseProduct workspace. -/
lemma step1Workspace_clean_write
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N
        cfg.env.data cfg.env.work
        cfg.flag b)
    (z : Fin (ASize cfg.env.work.active)) :
    cfg.env.circuit_workspace.step1Workspace.Clean
      (RegEncoding.writeNat
        cfg.env.work.active z.1 b) := by
  let dataNoCarry : ExtReg :=
    ExtReg.withReserve
      cfg.env.data.active
      (cfg.env.data.reserve.drop 1)
      (by
        unfold Shor.Disjoint
        rw [List.disjoint_left]
        intro q hqActive hqReserve
        have hdisj := cfg.env.data.active_reserve_disjoint
        unfold Shor.Disjoint at hdisj
        rw [List.disjoint_left] at hdisj
        exact hdisj hqActive (List.mem_of_mem_drop hqReserve))

  change
    dataNoCarry.FreshFor 1
        (RegEncoding.writeNat
          cfg.env.work.active z.1 b)
      ∧
    cfg.env.work.FreshFor 1
        (RegEncoding.writeNat
          cfg.env.work.active z.1 b)

  constructor

  · apply ExtReg.freshFor_write_active_of_ownedDisjoint
      dataNoCarry
      cfg.env.work
      1
      z.1
      b
    · unfold ExtReg.OwnedDisjoint
      rw [List.disjoint_left]
      intro q hqData hqWork
      apply cfg.env.circuit_workspace.2.2
      · rw [ExtReg.ownedQubits, List.mem_append] at hqData ⊢
        rcases hqData with hqActive | hqReserve
        · exact Or.inl hqActive
        · exact Or.inr (List.mem_of_mem_drop hqReserve)
      · exact hqWork

    · unfold ExtReg.FreshFor
      apply FreshZero.of_subset
          (dataNoCarry.newBits 1)
          (cfg.env.data.newBits 2)
          b
      · intro q hq
        dsimp [
          dataNoCarry,
          ExtReg.newBits,
          ExtReg.withReserve,
          Reg.take,
          Reg.drop
        ] at hq ⊢
        cases hreserve : cfg.env.data.reserve.qubits with
        | nil =>
            simp [hreserve] at hq
        | cons q₀ rest =>
            cases hrest : rest with
            | nil =>
                simp [hreserve, hrest] at hq
            | cons q₁ tail =>
                simp [hreserve, hrest] at hq ⊢
                exact Or.inr hq
      · exact hb.2.1

  · exact
      ExtReg.freshFor_write_active
        cfg.env.work
        1
        z.1
        b
        hb.2.2.2.1
/-- Step 1 maps one good basis input to a coherent work-label packet. -/
lemma alg1_step1_ket_expansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    ∃ α : Fin (ASize cfg.env.work.active) → ℂ,
      qs.eval
          (step1
            (Basis := qs.Basis)
            cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
          (qs.ket b)
        =
      ∑ t : Fin (ASize cfg.env.work.active),
        α t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
    classical

  let workReg : Reg := cfg.env.work.active
  let dataReg : Reg := cfg.env.data.active
  let ws :=
    cfg.env.circuit_workspace.step1Workspace

  let φ : ℝ :=
    (2 * Real.pi *
        (((cfg.c + cfg.env.N - 1) %
          cfg.env.N : ℕ) : ℝ))
      / (cfg.env.N : ℝ)

  have hworkZero :
      RegEncoding.toNat workReg b = 0 := by
    exact hb.2.2.1

  have hwriteOverwrite :
      ∀ v w : ℕ,
        RegEncoding.writeNat workReg v
            (RegEncoding.writeNat workReg w b)
          =
        RegEncoding.writeNat workReg v b := by
    intro v w
    apply RegEncoding.basis_ext
    intro q

    by_cases hq : q ∈ workReg.qubits

    · exact
        RegEncoding.bit_writeNat_in
          workReg
          v
          (RegEncoding.writeNat workReg w b)
          b
          q
          hq

    · simp only [
        RegEncoding.bit_writeNat_out
          workReg v
          (RegEncoding.writeNat workReg w b)
          q hq,
        RegEncoding.bit_writeNat_out
          workReg v b q hq,
        RegEncoding.bit_writeNat_out
          workReg w b q hq
      ]

  let z0 : Fin (ASize workReg) :=
    ⟨0, by
      have hlt :=
        RegEncoding.toNat_lt_ASize
          workReg b
      simpa [hworkZero] using hlt⟩

  have hz0 :
      RegEncoding.writeNat workReg z0.1 b = b := by
    change RegEncoding.writeNat workReg 0 b = b
    rw [← hworkZero]
    exact RegEncoding.writeNat_toNat workReg b

  obtain ⟨a, ha⟩ :=
    eval_Hreg_work_expansion
      qs workReg b z0

  have hH :
      qs.eval (H_reg workReg) (qs.ket b)
        =
      ∑ z : Fin (ASize workReg),
        a z •
          qs.ket
            (RegEncoding.writeNat workReg z.1 b) := by
    calc
      qs.eval (H_reg workReg) (qs.ket b)
          =
        qs.eval (H_reg workReg)
          (qs.ket
            (RegEncoding.writeNat
              workReg z0.1 b)) := by
                rw [hz0]
      _ =
        ∑ z : Fin (ASize workReg),
          a z •
            qs.ket
              (RegEncoding.writeNat
                workReg z.1 b) := ha

  let L : Fin (ASize workReg) → ℂ :=
    fun z =>
      Classical.choose
        (eval_cphaseprodusing_work_diagonal
          qs
          cfg.ctrl
          φ
          dataReg
          workReg
          ws
          b
          z
          (step1Workspace_clean_write
            qs cfg b hb z))

  have hL :
      ∀ z : Fin (ASize workReg),
        qs.eval
            (Gate.CPhaseProdUsing
              cfg.ctrl φ
              dataReg workReg ws)
            (qs.ket
              (RegEncoding.writeNat
                workReg z.1 b))
          =
        L z •
          qs.ket
            (RegEncoding.writeNat
              workReg z.1 b) := by
    intro z
    exact Classical.choose_spec
      (eval_cphaseprodusing_work_diagonal
        qs
        cfg.ctrl
        φ
        dataReg
        workReg
        ws
        b
        z
        (step1Workspace_clean_write
          qs cfg b hb z))

  let γ :
      Fin (ASize workReg) →
      Fin (ASize workReg) →
      ℂ :=
    fun z =>
      Classical.choose
        (eval_iqft_work_expansion
          qs
          ws.zExt
          (RegEncoding.writeNat
            workReg z.1 b))

  have hγ :
      ∀ z : Fin (ASize workReg),
        qs.eval (IQFT ws.zExt)
            (qs.ket
              (RegEncoding.writeNat
                workReg z.1 b))
          =
        ∑ t : Fin (ASize workReg),
          γ z t •
            qs.ket
              (RegEncoding.writeNat
                workReg t.1 b) := by
    intro z

    have hraw :=
      Classical.choose_spec
        (eval_iqft_work_expansion
          qs
          ws.zExt
          (RegEncoding.writeNat
            workReg z.1 b))

    calc
      qs.eval (IQFT ws.zExt)
          (qs.ket
            (RegEncoding.writeNat
              workReg z.1 b))
        =
      ∑ t : Fin (ASize workReg),
        γ z t •
          qs.ket
            (RegEncoding.writeNat
              workReg t.1
              (RegEncoding.writeNat
                workReg z.1 b)) := by
                  simpa [ws, workReg] using hraw
      _ =
      ∑ t : Fin (ASize workReg),
        γ z t •
          qs.ket
            (RegEncoding.writeNat
              workReg t.1 b) := by
                apply Finset.sum_congr rfl
                intro t _
                rw [hwriteOverwrite t.1 z.1]

  refine
    ⟨fun t =>
      ∑ z : Fin (ASize workReg),
        a z * L z * γ z t,
     ?_⟩

  simp only [step1, qs.eval_seq]

  change
    qs.eval (IQFT ws.zExt)
      (qs.eval
        (Gate.CPhaseProdUsing
          cfg.ctrl φ
          dataReg workReg ws)
        (qs.eval (H_reg workReg) (qs.ket b)))
      =
    ∑ t : Fin (ASize workReg),
      (∑ z : Fin (ASize workReg),
        a z * L z * γ z t) •
          qs.ket
            (RegEncoding.writeNat
              workReg t.1 b)

  rw [hH]

  rw [
    eval_finset_sum,
    eval_finset_sum
  ]

  simp_rw [
    qs.eval_smul,
    hL
  ]

  simp_rw [
    qs.eval_smul,
    hγ,
    Finset.smul_sum,
    smul_smul
  ]

  rw [Finset.sum_comm]

  apply Finset.sum_congr rfl
  intro t _
  simp [Finset.sum_smul, mul_assoc]

/-- Step 1's work-label expansion has coefficients exactly `alg1PhaseCoeff`. -/
lemma alg1_step1_ket_qpe_expansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval
        (ModMulConfig.U1 (Basis := qs.Basis) cfg)
        (qs.ket b)
      =
    ∑ t : Fin (ASize cfg.env.work.active),
      alg1PhaseCoeff qs cfg b t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
  classical

  rcases alg1_step1_ket_expansion qs cfg b hb with ⟨α, hα⟩

  have hαU1 :
      qs.eval
          (ModMulConfig.U1 (Basis := qs.Basis) cfg)
          (qs.ket b)
        =
      ∑ t : Fin (ASize cfg.env.work.active),
        α t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
    simpa [ModMulConfig.U1] using hα

  have hlabel_inj :
      ∀ t u : Fin (ASize cfg.env.work.active),
        RegEncoding.writeNat cfg.env.work.active t.1 b
          =
        RegEncoding.writeNat cfg.env.work.active u.1 b →
        t = u := by
    intro t u hEq
    apply Fin.ext
    calc
      t.1
          =
        RegEncoding.toNat cfg.env.work.active
          (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
          symm
          exact RegEncoding.toNat_writeNat_of_lt
            cfg.env.work.active t.1 b t.isLt
      _ =
        RegEncoding.toNat cfg.env.work.active
          (RegEncoding.writeNat cfg.env.work.active u.1 b) := by
          rw [hEq]
      _ = u.1 :=
          RegEncoding.toNat_writeNat_of_lt
            cfg.env.work.active u.1 b u.isLt

  have hcoeff :
      ∀ t : Fin (ASize cfg.env.work.active),
        alg1PhaseCoeff qs cfg b t = α t := by
    intro t
    unfold alg1PhaseCoeff
    rw [hαU1]
    rw [inner_sum]
    rw [Finset.sum_eq_single t]
    · rw [inner_smul_right, ket_inner_self]
      simp
    · intro u _hu hut
      have hneq :
          RegEncoding.writeNat cfg.env.work.active t.1 b
            ≠
          RegEncoding.writeNat cfg.env.work.active u.1 b := by
        intro hEq
        exact hut ((hlabel_inj t u hEq).symm)
      rw [inner_smul_right, qs.ket_inner_eq_zero_of_ne hneq]
      simp
    · intro ht
      simp at ht

  calc
    qs.eval
        (ModMulConfig.U1 (Basis := qs.Basis) cfg)
        (qs.ket b)
      =
    ∑ t : Fin (ASize cfg.env.work.active),
      α t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work.active t.1 b) := hαU1
    _ =
    ∑ t : Fin (ASize cfg.env.work.active),
      alg1PhaseCoeff qs cfg b t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hcoeff t]

end Step1QPEExpansion

/-! ---------------------------------------------------------
    Valid-state finite expansions

The trace constructor needs a finite basis expansion of an arbitrary state in
the valid-input span. These private helpers extract such an expansion by span
induction while preserving the good-input predicate on every support element.
--------------------------------------------------------- -/

section ValidStateFiniteExpansions

/-- A finite expansion over good modular-multiplication basis inputs. -/
private def HasGoodInputExpansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (φ : qs.State) : Prop :=
  ∃ (s : Finset qs.Basis) (α : qs.Basis → ℂ),
    φ =
      ∑ b ∈ s,
        α b • qs.ket b
    ∧
    ∀ b ∈ s,
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b


/-- Every valid modular-multiplication state has a finite good-input expansion. -/
private lemma good_input_expansion_of_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (hψ : cfg.ValidState qs ψ) :
    HasGoodInputExpansion qs cfg ψ := by
  classical

  dsimp [
    ModMulConfig.ValidState,
    ValidModMulState
  ] at hψ

  let P : qs.State → Prop :=
    HasGoodInputExpansion qs cfg

  change P ψ

  refine Submodule.span_induction
    (s := ({ φ : qs.State |
        ∃ b : qs.Basis,
          GoodModMulBasisInput qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b ∧
          φ = qs.ket b } : Set qs.State))
    (p := fun φ _ => P φ)
    ?_ ?_ ?_ ?_ hψ

  · intro φ hφ
    rcases hφ with ⟨b, hb, rfl⟩
    refine ⟨{b}, fun b' => if b' = b then 1 else 0, ?_, ?_⟩
    · simp
    · intro b' hb'
      have hb_eq : b' = b := by
        simpa using hb'
      subst hb_eq
      exact hb

  · refine ⟨∅, fun _ => 0, ?_, ?_⟩
    · simp
    · simp

  · intro φ χ _hφmem _hχmem hφ hχ
    rcases hφ with ⟨sφ, αφ, hφeq, hφgood⟩
    rcases hχ with ⟨sχ, αχ, hχeq, hχgood⟩

    let α : qs.Basis → ℂ :=
      fun b =>
        (if b ∈ sφ then αφ b else 0)
          +
        (if b ∈ sχ then αχ b else 0)

    refine ⟨sφ ∪ sχ, α, ?_, ?_⟩

    · have hsumφ :
          (∑ b ∈ sφ ∪ sχ,
            (if b ∈ sφ then αφ b else 0) • qs.ket b)
            =
          ∑ b ∈ sφ,
            αφ b • qs.ket b := by
          have h :
              (∑ b ∈ sφ,
                (if b ∈ sφ then αφ b else 0) • qs.ket b)
                =
              ∑ b ∈ sφ ∪ sχ,
                (if b ∈ sφ then αφ b else 0) • qs.ket b := by
            refine Finset.sum_subset Finset.subset_union_left ?_
            intro b hb_union hb_not_mem
            simp [hb_not_mem]
          calc
            (∑ b ∈ sφ ∪ sχ,
              (if b ∈ sφ then αφ b else 0) • qs.ket b)
                =
              ∑ b ∈ sφ,
                (if b ∈ sφ then αφ b else 0) • qs.ket b := h.symm
            _ =
              ∑ b ∈ sφ,
                αφ b • qs.ket b := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  simp [hb]

      have hsumχ :
          (∑ b ∈ sφ ∪ sχ,
            (if b ∈ sχ then αχ b else 0) • qs.ket b)
            =
          ∑ b ∈ sχ,
            αχ b • qs.ket b := by
          have h :
              (∑ b ∈ sχ,
                (if b ∈ sχ then αχ b else 0) • qs.ket b)
                =
              ∑ b ∈ sφ ∪ sχ,
                (if b ∈ sχ then αχ b else 0) • qs.ket b := by
            refine Finset.sum_subset Finset.subset_union_right ?_
            intro b hb_union hb_not_mem
            simp [hb_not_mem]
          calc
            (∑ b ∈ sφ ∪ sχ,
              (if b ∈ sχ then αχ b else 0) • qs.ket b)
                =
              ∑ b ∈ sχ,
                (if b ∈ sχ then αχ b else 0) • qs.ket b := h.symm
            _ =
              ∑ b ∈ sχ,
                αχ b • qs.ket b := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  simp [hb]

      calc
        φ + χ
            =
          (∑ b ∈ sφ, αφ b • qs.ket b)
            +
          (∑ b ∈ sχ, αχ b • qs.ket b) := by
            rw [hφeq, hχeq]
        _ =
          (∑ b ∈ sφ ∪ sχ,
            (if b ∈ sφ then αφ b else 0) • qs.ket b)
            +
          (∑ b ∈ sφ ∪ sχ,
            (if b ∈ sχ then αχ b else 0) • qs.ket b) := by
            rw [hsumφ, hsumχ]
        _ =
          ∑ b ∈ sφ ∪ sχ,
            ((if b ∈ sφ then αφ b else 0) • qs.ket b
              +
             (if b ∈ sχ then αχ b else 0) • qs.ket b) := by
            rw [← Finset.sum_add_distrib]
        _ =
          ∑ b ∈ sφ ∪ sχ,
            α b • qs.ket b := by
            apply Finset.sum_congr rfl
            intro b hb
            simp [α, add_smul]

    · intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact hφgood b hb
      · exact hχgood b hb

  · intro a φ _hφmem hφ
    rcases hφ with ⟨s, α, hφeq, hφgood⟩
    refine ⟨s, fun b => a * α b, ?_, hφgood⟩
    calc
      a • φ
          =
        a • (∑ b ∈ s, α b • qs.ket b) := by
          rw [hφeq]
      _ =
        ∑ b ∈ s, a • (α b • qs.ket b) := by
          rw [Finset.smul_sum]
      _ =
        ∑ b ∈ s, (a * α b) • qs.ket b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [smul_smul]

end ValidStateFiniteExpansions

/-! ---------------------------------------------------------
    Zero-target Step-1 exactness

If the Step-1 target residue is zero, the controlled phase load is trivial on
the work superposition, so the following inverse QFT exactly returns the input
basis state. This fact is used to rule out nonzero good labels in the zero-target
case.
--------------------------------------------------------- -/

section ZeroTargetStep1Exactness

/-- Register Hadamards on a zero active register coincide with QFT on that register. -/
lemma eval_Hreg_zero_eq_QFT
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (work : ExtReg)
    (b : qs.Basis)
    (hwork0 : ExtReg.toNat work b = 0) :
    qs.eval (H_reg work.active) (qs.ket b)
      =
    qs.eval (Gate.QFT work) (qs.ket b) := by
  simpa [H_reg, regQubits] using
    GateSemanticsFacts.eval_Hreg_zero_eq_QFT work b hwork0

/-- Inverse QFT cancels the register-Hadamard preparation of a zero register. -/
lemma eval_IQFT_Hreg_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (work : ExtReg)
    (b : qs.Basis)
    (hwork0 : ExtReg.toNat work b = 0) :
    qs.eval (IQFT work)
      (qs.eval (H_reg work.active) (qs.ket b))
      =
    qs.ket b := by
  rw [eval_Hreg_zero_eq_QFT qs work b hwork0]
  simpa [IQFT] using
    qs.eval_adj_apply (Gate.QFT work) (qs.ket b)

/-- Modularly equal phase numerators give the same complex exponential. -/
private lemma alg1_exp_phase_eq_of_modEq'
    (N u v z : ℕ)
    (hN : 0 < N)
    (huv : Nat.ModEq N u v) :
    Complex.exp
      (((2 * Real.pi) / (N : ℝ)) * Complex.I *
        ((u : ℂ) * (z : ℂ)))
      =
    Complex.exp
      (((2 * Real.pi) / (N : ℝ)) * Complex.I *
        ((v : ℂ) * (z : ℂ))) := by
  have hphase (x y : ℕ) :
      Complex.exp
        (((2 * Real.pi) / (N : ℝ)) * Complex.I *
          ((x : ℂ) * (y : ℂ)))
        =
      qftPhase N x y := by
    simp [qftPhase, ωPow, ω, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

  have hroot : (ω N) ^ N = 1 := by
    have hN0 : (N : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hN
    unfold ω
    rw [← Complex.exp_nat_mul]
    have harg :
        (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))
          =
        Complex.I * ((Real.pi : ℂ) * 2) := by
      field_simp [hN0, mul_assoc, mul_left_comm, mul_comm]
    rw [harg]
    simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.exp_two_pi_mul_I

  have hpow_mod :
      ∀ a b : ℕ, Nat.ModEq N a b → (ω N) ^ a = (ω N) ^ b := by
    intro a b hab
    have hrem : a % N = b % N := by
      simpa [Nat.ModEq] using hab
    calc
      (ω N) ^ a
          =
        (ω N) ^ (a % N + N * (a / N)) := by
          rw [Nat.mod_add_div a N]
      _ =
        (ω N) ^ (a % N) := by
          rw [pow_add, pow_mul, hroot]
          simp
      _ =
        (ω N) ^ (b % N) := by
          rw [hrem]
      _ =
        (ω N) ^ (b % N + N * (b / N)) := by
          rw [pow_add, pow_mul, hroot]
          simp
      _ =
        (ω N) ^ b := by
          rw [Nat.mod_add_div b N]

  have hpow :
      (ω N) ^ (u * z) = (ω N) ^ (v * z) :=
    hpow_mod (u * z) (v * z) (Nat.ModEq.mul_right z huv)

  calc
    Complex.exp
        (((2 * Real.pi) / (N : ℝ)) * Complex.I *
          ((u : ℂ) * (z : ℂ)))
      =
    qftPhase N u z := hphase u z
    _ =
    qftPhase N v z := by
      simpa [qftPhase, ωPow] using hpow
    _ =
    Complex.exp
        (((2 * Real.pi) / (N : ℝ)) * Complex.I *
          ((v : ℂ) * (z : ℂ))) :=
      (hphase v z).symm


/-- When the target residue is zero, the Step-1 controlled PhaseProduct fixes every work-label term. -/
lemma eval_CPhaseProd_fixes_work_of_target_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb : GoodModMulBasisInput qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (hz : alg1TargetResidue cfg b = 0) :
    qs.eval
        (Gate.CPhaseProdUsing
          cfg.ctrl
          ((2 * Real.pi *
              (((cfg.c + cfg.env.N - 1) % cfg.env.N : ℕ) : ℝ))
            / (cfg.env.N : ℝ))
          cfg.env.data.active
          cfg.env.work.active
          cfg.env.circuit_workspace.step1Workspace)
        (qs.eval (H_reg cfg.env.work.active) (qs.ket b))
      =
    qs.eval (H_reg cfg.env.work.active) (qs.ket b) := by
  classical

  let a : ℕ :=
    (cfg.c + cfg.env.N - 1) % cfg.env.N

  let φ : ℝ :=
    (2 * Real.pi * (a : ℝ)) /
      (cfg.env.N : ℝ)

  let workReg : Reg := cfg.env.work.active
  let dataReg : Reg := cfg.env.data.active
  let ws :=
    cfg.env.circuit_workspace.step1Workspace

  have hNpos : 0 < cfg.env.N :=
    Nat.lt_trans Nat.zero_lt_one
      cfg.env.modulus_gt_one

  have hdataWork :
      Disjoint dataReg workReg := by
    rw [Shor.Disjoint, List.disjoint_left]
    intro q hqData hqWork

    have howned := cfg.layout.1
    rw [
      ExtReg.OwnedDisjoint,
      List.disjoint_left
    ] at howned

    exact howned
      (List.mem_append_left _ hqData)
      (List.mem_append_left _ hqWork)

  have hctrlWork :
      cfg.ctrl ∉ workReg.qubits := by
    intro hctrl
    exact cfg.layout.2.2.2.2.1
      (List.mem_append_left _ hctrl)

  have hterm :
      ∀ t : Fin (ASize workReg),
        qs.eval
            (Gate.CPhaseProdUsing
              cfg.ctrl φ
              dataReg workReg ws)
            (qs.ket
              (RegEncoding.writeNat
                workReg t.1 b))
          =
        qs.ket
          (RegEncoding.writeNat
            workReg t.1 b) := by
    intro t

    rw [
      GateSemanticsFacts.eval_CPhaseProdUsing_ket
        qs
        cfg.ctrl
        φ
        dataReg
        workReg
        ws
        (RegEncoding.writeNat workReg t.1 b)
        (step1Workspace_clean_write
          qs cfg b hb t)
    ]

    have hctrlWrite :
        RegEncoding.bit cfg.ctrl
            (RegEncoding.writeNat
              workReg t.1 b)
          =
        RegEncoding.bit cfg.ctrl b :=
      RegEncoding.bit_writeNat_out
        workReg t.1 b cfg.ctrl hctrlWork

    have hdata :
        RegEncoding.toNat dataReg
            (RegEncoding.writeNat
              workReg t.1 b)
          =
        RegEncoding.toNat dataReg b :=
      RegEncoding.toNat_left_write_right
        dataReg workReg hdataWork b t.1

    have hwork :
        RegEncoding.toNat workReg
            (RegEncoding.writeNat
              workReg t.1 b)
          =
        t.1 :=
      RegEncoding.toNat_writeNat_of_lt
        workReg t.1 b t.isLt

    rw [hctrlWrite, hdata, hwork]

    by_cases hctrl :
        RegEncoding.bit cfg.ctrl b

    · let x : ℕ :=
        RegEncoding.toNat dataReg b

      have hzmod :
          Nat.ModEq cfg.env.N (a * x) 0 := by
        change
          (a * x) % cfg.env.N =
            0 % cfg.env.N

        have hz' :
            (a * x) % cfg.env.N = 0 := by
          simpa [
            alg1TargetResidue,
            a,
            x,
            hctrl
          ] using hz

        rw [hz', Nat.zero_mod]

      have hexp :
          Complex.exp
              (φ * Complex.I *
                ((x : ℂ) * (t.1 : ℂ)))
            =
          1 := by
        calc
          Complex.exp
              (φ * Complex.I *
                ((x : ℂ) * (t.1 : ℂ)))
            =
          Complex.exp
              (((2 * Real.pi) /
                  (cfg.env.N : ℝ)) *
                Complex.I *
                (((a * x : ℕ) : ℂ) *
                  (t.1 : ℂ))) := by
                    congr 1
                    dsimp [φ]
                    push_cast
                    ring
          _ =
          Complex.exp
              (((2 * Real.pi) /
                  (cfg.env.N : ℝ)) *
                Complex.I *
                (((0 : ℕ) : ℂ) *
                  (t.1 : ℂ))) :=
            alg1_exp_phase_eq_of_modEq'
              cfg.env.N
              (a * x)
              0
              t.1
              hNpos
              hzmod
          _ = 1 := by simp

      simp [hctrl, x, hexp]

    · simp [hctrl]

  let z0 : Fin (ASize workReg) :=
    ⟨RegEncoding.toNat workReg b,
      RegEncoding.toNat_lt_ASize
        workReg b⟩

  have hz0 :
      RegEncoding.writeNat
        workReg z0.1 b = b := by
    simpa [z0] using
      RegEncoding.writeNat_toNat
        workReg b

  obtain ⟨β, hβ⟩ :=
    eval_Hreg_work_expansion
      qs workReg b z0

  have hH :
      qs.eval (H_reg workReg) (qs.ket b)
        =
      ∑ t : Fin (ASize workReg),
        β t •
          qs.ket
            (RegEncoding.writeNat
              workReg t.1 b) := by
    calc
      qs.eval (H_reg workReg) (qs.ket b)
          =
        qs.eval (H_reg workReg)
          (qs.ket
            (RegEncoding.writeNat
              workReg z0.1 b)) := by
                rw [hz0]
      _ =
        ∑ t : Fin (ASize workReg),
          β t •
            qs.ket
              (RegEncoding.writeNat
                workReg t.1 b) := hβ

  change
    qs.eval
        (Gate.CPhaseProdUsing
          cfg.ctrl φ
          dataReg workReg ws)
        (qs.eval (H_reg workReg) (qs.ket b))
      =
    qs.eval (H_reg workReg) (qs.ket b)

  rw [hH, eval_finset_sum]

  apply Finset.sum_congr rfl
  intro t _
  rw [qs.eval_smul, hterm t]

/-- If the target residue is zero, the whole Step-1 circuit returns the original basis state. -/
lemma alg1_step1_zero_target_exact
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (hz : alg1TargetResidue cfg b = 0):
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
        (qs.ket b)
      =
    qs.ket b := by
  let φ : ℝ :=
    (2 * Real.pi *
        (((cfg.c + cfg.env.N - 1) %
          cfg.env.N : ℕ) : ℝ))
      / (cfg.env.N : ℝ)

  let ws :=
    cfg.env.circuit_workspace.step1Workspace

  have hphase :
      qs.eval
          (Gate.CPhaseProdUsing
            cfg.ctrl
            φ
            cfg.env.data.active
            cfg.env.work.active
            ws)
          (qs.eval
            (H_reg cfg.env.work.active)
            (qs.ket b))
        =
      qs.eval
        (H_reg cfg.env.work.active)
        (qs.ket b) := by
    simpa [φ, ws] using
      eval_CPhaseProd_fixes_work_of_target_zero
        qs cfg b hb hz

  have hworkZero :
      ExtReg.toNat ws.zExt b = 0 := by
    simpa [
      ws,
      ModMulCircuitWorkspaceOK.step1Workspace,
      Gate.PhaseProdWorkspace.zExt,
      ExtReg.toNat
    ] using hb.2.2.1

  calc
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c
          cfg.env.N
          cfg.ctrl
          cfg.env.data
          cfg.env.work
          cfg.env.circuit_workspace)
        (qs.ket b)
      =
    qs.eval (IQFT ws.zExt)
      (qs.eval
        (Gate.CPhaseProdUsing
          cfg.ctrl
          φ
          cfg.env.data.active
          cfg.env.work.active
          ws)
        (qs.eval
          (H_reg cfg.env.work.active)
          (qs.ket b))) := by
            simp [step1, qs.eval_seq, φ, ws]

    _ =
    qs.eval (IQFT ws.zExt)
      (qs.eval
        (H_reg cfg.env.work.active)
        (qs.ket b)) := by
          rw [hphase]

    _ = qs.ket b :=
      eval_IQFT_Hreg_zero
        qs ws.zExt b hworkZero

end ZeroTargetStep1Exactness

/-! ---------------------------------------------------------
    Step-3/4 overflow arithmetic

These arithmetic lemmas relate the good-label fractional approximation to the
comparator cross condition used by Step 4. The endpoint is the equivalence
between the Step-4 cross condition and overflow of the Step-2 sum.
--------------------------------------------------------- -/

section Step34OverflowArithmetic

/-- Rewrites the final controlled multiplication residue through the Step-1 target residue. -/
lemma alg1_output_mod
    (c N x : ℕ)
    (hN : 0 < N) :
    (c * x) % N
      =
    (x + ((((c + N - 1) % N) * x) % N)) % N := by
  let a : ℕ := (c + N - 1) % N

  have ha :
      a ≡ c + N - 1 [MOD N] := by
    dsimp [a]
    exact Nat.mod_modEq (c + N - 1) N

  have hsucc :
      a + 1 ≡ c [MOD N] := by
    have h := Nat.ModEq.add_right 1 ha
    have hsum :
        (c + N - 1) + 1 = c + N := by
      omega
    rw [hsum] at h
    calc
      a + 1 ≡ c + N [MOD N] := h
      _ ≡ c [MOD N] := by
        simp [Nat.ModEq]

  have hcx :
      c * x ≡ (a + 1) * x [MOD N] :=
    Nat.ModEq.mul_right x hsucc.symm

  have hax :
      (a + 1) * x = x + a * x := by
    calc
      (a + 1) * x
          = a * x + 1 * x :=
        Nat.add_mul a 1 x
      _ = a * x + x := by simp
      _ = x + a * x := Nat.add_comm _ _

  have hxr :
      x + ((a * x) % N) ≡
        x + a * x [MOD N] :=
    Nat.ModEq.add_left x
      (Nat.mod_modEq (a * x) N)

  have hmod :
      c * x ≡
        x + ((a * x) % N) [MOD N] := by
    calc
      c * x ≡ (a + 1) * x [MOD N] := hcx
      _ ≡ x + a * x [MOD N] := by
        rw [hax]
      _ ≡ x + ((a * x) % N) [MOD N] :=
        hxr.symm

  simpa [Nat.ModEq, a] using hmod


/-- Cross-multiplication criterion for comparing two positive natural fractions. -/
private lemma nat_fraction_lt_iff_cross
    (a n t m : ℕ)
    (hn : 0 < n)
    (hm : 0 < m) :
    (a : ℝ) / (n : ℝ) <
        (t : ℝ) / (m : ℝ)
      ↔
    a * m < t * n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn

  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm

  constructor

  · intro h
    have h' :=
      (div_lt_div_iff₀ hnR hmR).mp h
    exact_mod_cast h'

  · intro h
    apply (div_lt_div_iff₀ hnR hmR).mpr
    exact_mod_cast h


/-- For good labels, the Step-4 comparator condition is exactly Step-2 overflow. -/
lemma alg1_step4_cross_iff_overflow_of_good
    [QSemantics]
    [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work.active))
    (hb :
      GoodModMulBasisInput
        (inferInstance : QSemantics)
        cfg.env.N
        cfg.env.data
        cfg.env.work
        cfg.flag
        b)
    (ht : t ∈ alg1GoodLabels cfg b)
    (hzero :
      alg1TargetResidue cfg b = 0 →
      t.1 = 0) :
    alg1Step4CrossCondition cfg b t
      ↔
    alg1Overflow cfg b := by
  classical

  let N : ℕ := cfg.env.N
  let A : ℕ := ASize cfg.env.data.active
  let M : ℕ := ASize cfg.env.work.active
  let x : ℕ :=
    RegEncoding.toNat cfg.env.data.active b
  let r : ℕ := alg1TargetResidue cfg b
  let y : ℕ := alg1OutputValue cfg b
  let s : ℕ := x + r

  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.lt_trans
      Nat.zero_lt_one
      cfg.env.modulus_gt_one

  have hApos : 0 < A := by
    dsimp [A, ASize]
    positivity

  have hMpos : 0 < M := by
    dsimp [M, ASize]
    positivity

  have hxlt : x < N := by
    simpa [x, N] using hb.1

  have hrlt : r < N := by
    simpa [r, N] using
      alg1TargetResidue_lt_N cfg b

  have hslt : s < 2 * N := by
    dsimp [s]
    omega

  have hNposR :
      (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hNpos

  have hAposR :
      (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast hApos

  have hMposR :
      (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hMpos

  have hNleA :
      (N : ℝ) ≤ (A : ℝ) := by
    dsimp [N, A]
    exact_mod_cast cfg.env.data_capacity

  have heta :
      η < (1 / 2 : ℝ) :=
    cfg.env.precision.2.1

  have hetaN :
      η * (N : ℝ) <
        (1 / 2 : ℝ) * (N : ℝ) :=
    mul_lt_mul_of_pos_right heta hNposR

  have hhalfNleA :
      (1 / 2 : ℝ) * (N : ℝ) ≤
        (A : ℝ) := by
    nlinarith

  have hdelta :
      η / (A : ℝ) <
        1 / (N : ℝ) := by
    apply
      (div_lt_div_iff₀ hAposR hNposR).mpr
    nlinarith

  have hgood :
      |(r : ℝ) / (N : ℝ) -
          (t.1 : ℝ) / (M : ℝ)|
        <
      η / (A : ℝ) := by
    have hraw :=
      (Finset.mem_filter.mp ht).2

    simpa [
      alg1GoodLabels,
      alg1TargetFraction,
      alg1WorkFraction,
      r, N, M, A
    ] using hraw

  rcases abs_lt.mp hgood with
    ⟨hgood_left, hgood_right⟩

  have hbelow :
      (r : ℝ) / (N : ℝ) -
          η / (A : ℝ)
        <
      (t.1 : ℝ) / (M : ℝ) := by
    linarith

  have habove :
      (t.1 : ℝ) / (M : ℝ)
        <
      (r : ℝ) / (N : ℝ) +
          η / (A : ℝ) := by
    linarith

  have hy_mod :
      y = s % N := by
    dsimp [y, s, r, x, N]

    by_cases hctrl :
        RegEncoding.bit cfg.ctrl b

    · simp only [
        alg1OutputValue,
        alg1TargetResidue,
        hctrl,
        if_true
      ]

      exact
        alg1_output_mod
          cfg.c
          cfg.env.N
          (RegEncoding.toNat
            cfg.env.data.active b)
          (Nat.lt_trans
            Nat.zero_lt_one
            cfg.env.modulus_gt_one)

    · simp [
        alg1OutputValue,
        alg1TargetResidue,
        hctrl,
        Nat.mod_eq_of_lt hb.1
      ]

  change
    y * M < N * t.1 ↔ N ≤ s

  by_cases hover : N ≤ s

  · have hy_over :
        y = s - N := by
      calc
        y = s % N := hy_mod
        _ = (s - N) % N :=
          Nat.mod_eq_sub_mod hover
        _ = s - N :=
          Nat.mod_eq_of_lt (by omega)

    have hylt :
        y < r := by
      rw [hy_over]
      dsimp [s]
      omega

    have hgapNat :
        y + 1 ≤ r :=
      Nat.succ_le_iff.mpr hylt

    have hgapR :
        (y : ℝ) + 1 ≤ (r : ℝ) := by
      exact_mod_cast hgapNat

    have hmul :
        ((y : ℝ) + 1) * (N : ℝ)
          ≤
        (r : ℝ) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right
        hgapR
        (le_of_lt hNposR)

    have hdiv :
        ((y : ℝ) + 1) / (N : ℝ)
          ≤
        (r : ℝ) / (N : ℝ) :=
      (div_le_div_iff₀ hNposR hNposR).mpr <| by
        simpa [mul_comm] using hmul

    have hsplit :
        ((y : ℝ) + 1) / (N : ℝ)
          =
        (y : ℝ) / (N : ℝ) +
          1 / (N : ℝ) := by
      ring

    rw [hsplit] at hdiv

    have hyfrac :
        (y : ℝ) / (N : ℝ)
          <
        (r : ℝ) / (N : ℝ) -
          η / (A : ℝ) := by
      linarith

    have hcrossfrac :
        (y : ℝ) / (N : ℝ)
          <
        (t.1 : ℝ) / (M : ℝ) :=
      lt_trans hyfrac hbelow

    have hcross :
        y * M < N * t.1 := by
      have hraw :=
        (nat_fraction_lt_iff_cross
          y N t.1 M hNpos hMpos).mp
          hcrossfrac

      simpa [Nat.mul_comm] using hraw

    constructor

    · intro _
      exact hover

    · intro _
      exact hcross

  · have hy_no :
        y = s := by
      calc
        y = s % N := hy_mod
        _ = s :=
          Nat.mod_eq_of_lt
            (lt_of_not_ge hover)

    by_cases hxzero : x = 0

    · have hrzero :
          r = 0 := by
        dsimp [r]
        unfold alg1TargetResidue

        by_cases hctrl :
            RegEncoding.bit cfg.ctrl b

        · simp [hctrl]
          simp_all only [
            Nat.cast_pos,
            Nat.cast_le,
            one_div,
            mul_lt_mul_iff_left₀,
            neg_lt_sub_iff_lt_add,
            not_le,
            mul_zero,
            Nat.zero_mod,
            N, A, M, x, r, s, y
          ]

        · simp [hctrl]

      have hyzero :
          y = 0 := by
        rw [hy_no]
        dsimp [s]
        simp [hxzero, hrzero]

      have htzero :
          t.1 = 0 := by
        apply hzero
        simpa [r] using hrzero

      have hnotcross :
          ¬ y * M < N * t.1 := by
        simp [hyzero, htzero]

      constructor

      · intro h
        exact False.elim (hnotcross h)

      · intro h
        exact False.elim (hover h)

    · have hxpos : 0 < x :=
        Nat.pos_of_ne_zero hxzero

      have hgapNat :
          r + 1 ≤ y := by
        rw [hy_no]
        dsimp [s]
        omega

      have hgapR :
          (r : ℝ) + 1 ≤ (y : ℝ) := by
        exact_mod_cast hgapNat

      have hmul :
          ((r : ℝ) + 1) * (N : ℝ)
            ≤
          (y : ℝ) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right
          hgapR
          (le_of_lt hNposR)

      have hdiv :
          ((r : ℝ) + 1) / (N : ℝ)
            ≤
          (y : ℝ) / (N : ℝ) :=
        (div_le_div_iff₀ hNposR hNposR).mpr <| by
          simpa [mul_comm] using hmul

      have hsplit :
          ((r : ℝ) + 1) / (N : ℝ)
            =
          (r : ℝ) / (N : ℝ) +
            1 / (N : ℝ) := by
        ring

      rw [hsplit] at hdiv

      have hyr :
          (r : ℝ) / (N : ℝ) +
              η / (A : ℝ)
            <
          (y : ℝ) / (N : ℝ) := by
        linarith

      have hfrac :
          (t.1 : ℝ) / (M : ℝ)
            <
          (y : ℝ) / (N : ℝ) :=
        lt_trans habove hyr

      have hreverse :
          N * t.1 < y * M := by
        have hraw :=
          (nat_fraction_lt_iff_cross
            t.1 M y N hMpos hNpos).mp
            hfrac

        simpa [Nat.mul_comm] using hraw

      have hnotcross :
          ¬ y * M < N * t.1 := by
        intro hcross
        omega

      constructor

      · intro h
        exact False.elim (hnotcross h)

      · intro h
        exact False.elim (hover h)

end Step34OverflowArithmetic

/-! ---------------------------------------------------------
    Final trace construction

The final lemma assembles the valid-state expansion, Step-1 coefficient
identification, zero-target support fact, and Step-3/4 overflow arithmetic into
the `Alg1Trace` record consumed by the later quantitative bounds.
--------------------------------------------------------- -/

section FinalTraceConstruction

/-- Every valid input state admits the finite Algorithm-1 trace used by the bound proofs. -/
lemma alg1_trace_of_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (hψ : cfg.ValidState qs ψ) :
    ∃ _tr : Alg1Trace qs cfg ψ, True := by
  classical

  rcases good_input_expansion_of_valid qs cfg ψ hψ with
    ⟨support, inputCoeff, hinput, hgood⟩

  let zeroWork : Fin (ASize cfg.env.work.active) :=
    ⟨0, by simp[ASize]⟩

  let phaseCoeff :
      qs.Basis →
        Fin (ASize cfg.env.work.active) →
        ℂ :=
    fun b t => alg1PhaseCoeff qs cfg b t

  have hzero_support :
      ∀ b,
        GoodModMulBasisInput
            qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b →
        ∀ t,
          phaseCoeff b t ≠ 0 →
          alg1TargetResidue cfg b = 0 →
          t.1 = 0 := by
    intro b hb t hcoeff hz
    by_contra ht0

    have hstep1 :
        qs.eval
            (ModMulConfig.U1 (Basis := qs.Basis) cfg)
            (qs.ket b)
          =
        qs.ket b := by
      simpa [ModMulConfig.U1] using
        alg1_step1_zero_target_exact qs cfg b hb hz

    have hlabel_ne :
        RegEncoding.writeNat cfg.env.work.active t.1 b ≠ b := by
      intro hEq
      have ht_read :
          t.1 =
            RegEncoding.toNat cfg.env.work.active
              (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
        symm
        exact RegEncoding.toNat_writeNat_of_lt
          cfg.env.work.active t.1 b t.isLt
      have : t.1 = 0 := by
        calc
          t.1 =
              RegEncoding.toNat cfg.env.work.active
                (RegEncoding.writeNat cfg.env.work.active t.1 b) := ht_read
          _ = RegEncoding.toNat cfg.env.work.active b := by rw [hEq]
          _ = 0 := hb.2.2.1
      exact ht0 this

    have hcoeff_zero : phaseCoeff b t = 0 := by
      simp [phaseCoeff, alg1PhaseCoeff, hstep1,
        qs.ket_inner_eq_zero_of_ne hlabel_ne]

    exact hcoeff hcoeff_zero

  have hphase :
      ∀ b,
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b →
        qs.eval
            (step1
              (Basis := qs.Basis)
              cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
            (qs.ket b)
          =
        ∑ t : Fin (ASize cfg.env.work.active),
          phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
    intro b hb
    simpa [phaseCoeff, ModMulConfig.U1] using
      alg1_step1_ket_qpe_expansion qs cfg b hb

  refine ⟨{
    support := support
    inputCoeff := inputCoeff
    phaseCoeff := phaseCoeff
    input_eq := hinput
    input_good := hgood

    step34_support := by
      intro b hbmem t ht hcoeff

      apply alg1_step4_cross_iff_overflow_of_good
        cfg
        b
        t
        (hgood b hbmem)
        ht

      intro hz

      exact
        hzero_support
          b
          (hgood b hbmem)
          t
          hcoeff
          hz

    full_step1_eq := ?_
  }, trivial⟩

  calc
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
        ψ
      =
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
        (∑ b ∈ support,
          inputCoeff b • qs.ket b) := by
        rw [hinput]

    _ =
    ∑ b ∈ support,
      qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
        (inputCoeff b • qs.ket b) := by
        simpa using
          eval_finset_sum
            qs
            (step1
              (Basis := qs.Basis)
              cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
            support
            (fun b => inputCoeff b • qs.ket b)

    _ =
    ∑ b ∈ support,
      inputCoeff b •
        qs.eval
          (step1
            (Basis := qs.Basis)
            cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
          (qs.ket b) := by
        apply Finset.sum_congr rfl
        intro b hb
        simpa using
          qs.eval_smul
            (step1
              (Basis := qs.Basis)
              cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work cfg.env.circuit_workspace)
            (inputCoeff b)
            (qs.ket b)

    _ =
    ∑ b ∈ support,
      inputCoeff b •
        ∑ t : Fin (ASize cfg.env.work.active),
          phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work.active t.1 b) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hphase b (hgood b hb)]

end FinalTraceConstruction
