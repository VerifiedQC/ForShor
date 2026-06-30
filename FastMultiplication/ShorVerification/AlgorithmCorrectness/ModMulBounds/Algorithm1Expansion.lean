import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModMulBounds.Core

open Shor

universe v

/-!
# Algorithm 1 Expansion Lemmas

Focus theorem: `alg1_trace_of_valid`.

This file expands the staged Algorithm-1 gates on valid basis states and builds
the reference trace used by the quantitative bounds.
-/

/-! =========================================================
    Staged-gate equivalence
========================================================= -/

namespace ModMulConfig

lemma eval_approxGate_eq_staged
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
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

/-! =========================================================
    Primitive-gate expansion lemmas
========================================================= -/

lemma eval_finset_sum
    (qs : QSemantics)
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


lemma eval_iqft_work_expansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [QFTSemantics qs]
    (work : Reg)
    (b : qs.Basis) :
    ∃ α : Fin (ASize work) → ℂ,
      qs.eval (IQFT work) (qs.ket b)
        =
      ∑ t : Fin (ASize work),
        α t • qs.ket (RegEncoding.writeNat work t.1 b) := by
  refine ⟨
    fun t =>
      ((1 / Real.sqrt ((ASize work : ℕ) : ℝ) : ℂ) *
        star (qftPhase (ASize work) (RegEncoding.toNat work b) t.1)),
    ?_
  ⟩
  rw [IQFT]
  rw [QFTSemantics.eval_adj_QFT_ket]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [smul_smul]

lemma eval_cphaseprod_work_diagonal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (ctrl : ℕ)
    (φ : ℝ)
    (data work : Reg)
    (b : qs.Basis)
    (z : Fin (ASize work))
    (hdisj : Disjoint data work) :
    ∃ L : ℂ,
      qs.eval (Gate.CPhaseProd ctrl φ data work)
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
    GateSemanticsFacts.eval_CPhaseProd_ket qs ctrl φ data work b' hdisj

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


private lemma hregWorkSpan_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis) :
    HRegWorkSpan qs work base (0 : qs.State) := by
  refine ⟨fun _ => 0, ?_⟩
  simp


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
    (hqlo : work.lo ≤ q)
    (hqhi : q < work.hi)
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

  by_cases hp : work.lo ≤ p ∧ p < work.hi

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
      RegEncoding.bit_writeNat_in
        (r := work)
        (v := t.1)
        (b1 := base)
        (b2 := bout)
        (q := p)
        hp.1
        hp.2

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
    have hpout : p < work.lo ∨ work.hi ≤ p := by
      by_cases hplow : p < work.lo
      · exact Or.inl hplow
      · right
        omega

    have hqout :
        p < (qubitReg q).lo ∨ (qubitReg q).hi ≤ p := by
      unfold qubitReg Reg.hi
      rcases hpout with hpout | hpout
      · left
        simp_all
        omega
      · right
        simp_all
        omega

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
        hpout

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
        hpout

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


private lemma hregWorkSpan_qubit_write
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (work : Reg)
    (base : qs.Basis)
    (q : ℕ)
    (hqlo : work.lo ≤ q)
    (hqhi : q < work.hi)
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
        qs work base q hqlo hqhi z v with
    ⟨t, ht⟩

  rw [ht]
  exact hregWorkSpan_ket_write qs work base t


private lemma eval_H_preserves_hregWorkSpan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [HadamardSemantics qs]
    (work : Reg)
    (base : qs.Basis)
    (q : ℕ)
    (hqlo : work.lo ≤ q)
    (hqhi : q < work.hi)
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
          qs work base q hqlo hqhi t 0

    ·
      apply hregWorkSpan_smul qs work base
      exact
        hregWorkSpan_qubit_write
          qs work base q hqlo hqhi t 1

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


private lemma mem_regQubits_bounds
    (work : Reg)
    {q : ℕ}
    (hq : q ∈ regQubits work) :
    work.lo ≤ q ∧ q < work.hi := by
  unfold regQubits at hq
  rcases List.mem_map.mp hq with ⟨i, hi, rfl⟩
  have hi' : i < work.size := List.mem_range.mp hi

  constructor
  · omega
  · unfold Reg.hi
    omega


private lemma eval_foldl_H_preserves_hregWorkSpan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [HadamardSemantics qs]
    (work : Reg)
    (base : qs.Basis)
    (qsList : List ℕ) :
    (∀ q, q ∈ qsList → work.lo ≤ q ∧ q < work.hi) →
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
      intro hbounds acc hacc ξ hξ

      have hq : work.lo ≤ q ∧ q < work.hi :=
        hbounds q (by simp)

      have htail :
          ∀ r, r ∈ qsList → work.lo ≤ r ∧ r < work.hi := by
        intro r hr
        exact hbounds r (by simp [hr])

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
            qs work base q hq.1 hq.2 ξ hξ

        simpa [qs.eval_seq] using
          hacc (qs.eval (Gate.H q) ξ) hH

      simpa [List.foldl] using
        ih
          htail
          (Gate.seq (Gate.H q) acc)
          hacc'
          ξ
          hξ


lemma eval_Hreg_work_expansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
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
      ∀ q, q ∈ regQubits work → work.lo ≤ q ∧ q < work.hi := by
    intro q hq
    exact mem_regQubits_bounds work hq

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

lemma alg1_step1_ket_expansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    ∃ α : Fin (ASize cfg.env.work) → ℂ,
      qs.eval
          (step1
            (Basis := qs.Basis)
            cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
          (qs.ket b)
        =
      ∑ t : Fin (ASize cfg.env.work),
        α t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b) := by
  classical

  let φ : ℝ :=
    (2 * Real.pi *
        (((cfg.c + cfg.env.N - 1) % cfg.env.N : ℕ) : ℝ))
      / (cfg.env.N : ℝ)

  have hwork_zero : RegEncoding.toNat cfg.env.work b = 0 := hb.2.2.1

  have hdatawork : Disjoint cfg.env.data cfg.env.work := by
    rcases cfg.layout.1 with h | h
    · left
      apply le_trans ?_ h
      change cfg.env.data.lo + cfg.env.data.size
        ≤ cfg.env.data.lo + (cfg.env.data.size + 1)
      omega
    · exact Or.inr h

  have hwrite_overwrite :
      ∀ v w : ℕ,
        RegEncoding.writeNat cfg.env.work v
            (RegEncoding.writeNat cfg.env.work w b)
          =
        RegEncoding.writeNat cfg.env.work v b := by
    intro v w
    apply RegEncoding.basis_ext
    intro q
    by_cases hqlo : cfg.env.work.lo ≤ q
    · by_cases hqhi : q < cfg.env.work.hi
      · exact
          RegEncoding.bit_writeNat_in
            (r := cfg.env.work) (v := v)
            (b1 := RegEncoding.writeNat cfg.env.work w b)
            (b2 := b) (q := q) hqlo hqhi
      · have hout : q < cfg.env.work.lo ∨ cfg.env.work.hi ≤ q :=
          Or.inr (Nat.le_of_not_gt hqhi)
        rw [RegEncoding.bit_writeNat_out
              (r := cfg.env.work) (v := v)
              (b := RegEncoding.writeNat cfg.env.work w b)
              (q := q) hout,
            RegEncoding.bit_writeNat_out
              (r := cfg.env.work) (v := v)
              (b := b) (q := q) hout,
            RegEncoding.bit_writeNat_out
              (r := cfg.env.work) (v := w)
              (b := b) (q := q) hout]
    · have hout : q < cfg.env.work.lo ∨ cfg.env.work.hi ≤ q :=
        Or.inl (Nat.lt_of_not_ge hqlo)
      rw [RegEncoding.bit_writeNat_out
            (r := cfg.env.work) (v := v)
            (b := RegEncoding.writeNat cfg.env.work w b)
            (q := q) hout,
          RegEncoding.bit_writeNat_out
            (r := cfg.env.work) (v := v)
            (b := b) (q := q) hout,
          RegEncoding.bit_writeNat_out
            (r := cfg.env.work) (v := w)
            (b := b) (q := q) hout]

  let z0 : Fin (ASize cfg.env.work) :=
    ⟨0, by
      simpa [← hwork_zero] using
        RegEncoding.toNat_lt_ASize cfg.env.work b⟩

  have hz0 : RegEncoding.writeNat cfg.env.work z0.1 b = b := by
    change RegEncoding.writeNat cfg.env.work 0 b = b
    rw [← hwork_zero]
    exact RegEncoding.writeNat_toNat (r := cfg.env.work) (b := b)

  rcases eval_Hreg_work_expansion qs cfg.env.work b z0 with
    ⟨a, ha⟩

  let L : Fin (ASize cfg.env.work) → ℂ :=
    fun z =>
      Classical.choose
        (eval_cphaseprod_work_diagonal
          qs cfg.ctrl φ cfg.env.data cfg.env.work b z hdatawork)

  have hL :
      ∀ z : Fin (ASize cfg.env.work),
        qs.eval
            (Gate.CPhaseProd
              cfg.ctrl φ cfg.env.data cfg.env.work)
            (qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b))
          =
        L z •
          qs.ket
            (RegEncoding.writeNat cfg.env.work z.1 b) := by
    intro z
    exact Classical.choose_spec
      (eval_cphaseprod_work_diagonal
        qs cfg.ctrl φ cfg.env.data cfg.env.work b z hdatawork)

  let γ :
      Fin (ASize cfg.env.work) →
        Fin (ASize cfg.env.work) →
          ℂ :=
    fun z =>
      Classical.choose
        (eval_iqft_work_expansion qs cfg.env.work
          (RegEncoding.writeNat cfg.env.work z.1 b))

  have hγ :
      ∀ z : Fin (ASize cfg.env.work),
        qs.eval (IQFT cfg.env.work)
            (qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b))
          =
        ∑ t : Fin (ASize cfg.env.work),
          γ z t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
    intro z
    have hraw := Classical.choose_spec
      (eval_iqft_work_expansion qs cfg.env.work
        (RegEncoding.writeNat cfg.env.work z.1 b))
    calc
      qs.eval (IQFT cfg.env.work)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work z.1 b))
          =
        ∑ t : Fin (ASize cfg.env.work),
          γ z t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1
                (RegEncoding.writeNat cfg.env.work z.1 b)) := hraw
      _ =
        ∑ t : Fin (ASize cfg.env.work),
          γ z t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hwrite_overwrite t.1 z.1]

  refine ⟨fun t => ∑ z, a z * L z * γ z t, ?_⟩

  have hH :
      qs.eval (H_reg cfg.env.work) (qs.ket b)
        =
      ∑ z : Fin (ASize cfg.env.work),
        a z •
          qs.ket
            (RegEncoding.writeNat cfg.env.work z.1 b) := by
    calc
      qs.eval (H_reg cfg.env.work) (qs.ket b)
          =
        qs.eval (H_reg cfg.env.work)
          (qs.ket (RegEncoding.writeNat cfg.env.work z0.1 b)) := by
            rw [hz0]
      _ =
        ∑ z : Fin (ASize cfg.env.work),
          a z •
            qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b) := ha

  have hphase :
      qs.eval
          (Gate.CPhaseProd
            cfg.ctrl φ cfg.env.data cfg.env.work)
          (qs.eval (H_reg cfg.env.work) (qs.ket b))
        =
      ∑ z : Fin (ASize cfg.env.work),
        (a z * L z) •
          qs.ket
            (RegEncoding.writeNat cfg.env.work z.1 b) := by
    rw [hH]
    calc
      qs.eval
          (Gate.CPhaseProd
            cfg.ctrl φ cfg.env.data cfg.env.work)
          (∑ z : Fin (ASize cfg.env.work),
            a z •
              qs.ket
                (RegEncoding.writeNat cfg.env.work z.1 b))
          =
        ∑ z : Fin (ASize cfg.env.work),
          qs.eval
            (Gate.CPhaseProd
              cfg.ctrl φ cfg.env.data cfg.env.work)
            (a z •
              qs.ket
                (RegEncoding.writeNat cfg.env.work z.1 b)) := by
            simpa using
              eval_finset_sum
                qs
                (Gate.CPhaseProd
                  cfg.ctrl φ cfg.env.data cfg.env.work)
                Finset.univ
                (fun z =>
                  a z •
                    qs.ket
                      (RegEncoding.writeNat cfg.env.work z.1 b))
      _ =
        ∑ z : Fin (ASize cfg.env.work),
          a z •
            qs.eval
              (Gate.CPhaseProd
                cfg.ctrl φ cfg.env.data cfg.env.work)
              (qs.ket
                (RegEncoding.writeNat cfg.env.work z.1 b)) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [qs.eval_smul]
      _ =
        ∑ z : Fin (ASize cfg.env.work),
          (a z * L z) •
            qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hL z, smul_smul]

  have hfubini :
      (∑ z : Fin (ASize cfg.env.work),
        (a z * L z) •
          ∑ t : Fin (ASize cfg.env.work),
            γ z t •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b))
      =
      ∑ t : Fin (ASize cfg.env.work),
        (∑ z : Fin (ASize cfg.env.work),
          a z * L z * γ z t) •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
    calc
      (∑ z : Fin (ASize cfg.env.work),
        (a z * L z) •
          ∑ t : Fin (ASize cfg.env.work),
            γ z t •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b))
          =
        ∑ z : Fin (ASize cfg.env.work),
          ∑ t : Fin (ASize cfg.env.work),
            ((a z * L z) * γ z t) •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro t ht
            rw [smul_smul]
      _ =
        ∑ t : Fin (ASize cfg.env.work),
          ∑ z : Fin (ASize cfg.env.work),
            ((a z * L z) * γ z t) •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b) := by
            rw [Finset.sum_comm]
      _ =
        ∑ t : Fin (ASize cfg.env.work),
          (∑ z : Fin (ASize cfg.env.work),
            a z * L z * γ z t) •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b) := by
            simp [Finset.sum_smul, mul_assoc]

  have hmain :
      qs.eval (IQFT cfg.env.work)
      (qs.eval
        (Gate.CPhaseProd
          cfg.ctrl φ cfg.env.data cfg.env.work)
        (qs.eval (H_reg cfg.env.work) (qs.ket b)))
      =
      ∑ t : Fin (ASize cfg.env.work),
        (∑ z : Fin (ASize cfg.env.work),
          a z * L z * γ z t) •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
    rw [hphase]
    calc
      qs.eval (IQFT cfg.env.work)
        (∑ z : Fin (ASize cfg.env.work),
          (a z * L z) •
            qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b))
        =
      ∑ z : Fin (ASize cfg.env.work),
        qs.eval (IQFT cfg.env.work)
          ((a z * L z) •
            qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b)) := by
          simpa using
            eval_finset_sum
              qs
              (IQFT cfg.env.work)
              Finset.univ
              (fun z =>
                (a z * L z) •
                  qs.ket
                    (RegEncoding.writeNat cfg.env.work z.1 b))
      _ =
        ∑ z : Fin (ASize cfg.env.work),
          (a z * L z) •
            qs.eval (IQFT cfg.env.work)
              (qs.ket
                (RegEncoding.writeNat cfg.env.work z.1 b)) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [qs.eval_smul]
      _ =
        ∑ z : Fin (ASize cfg.env.work),
          (a z * L z) •
            ∑ t : Fin (ASize cfg.env.work),
              γ z t •
                qs.ket
                  (RegEncoding.writeNat cfg.env.work t.1 b) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hγ z]
      _ =
        ∑ t : Fin (ASize cfg.env.work),
          (∑ z : Fin (ASize cfg.env.work),
            a z * L z * γ z t) •
              qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b) := hfubini

  simpa [step1, qs.eval_seq, φ] using hmain

lemma alg1_step1_ket_qpe_expansion
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
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
    ∑ t : Fin (ASize cfg.env.work),
      alg1PhaseCoeff qs cfg b t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work t.1 b) := by
  classical

  rcases alg1_step1_ket_expansion qs cfg b hb with ⟨α, hα⟩

  have hαU1 :
      qs.eval
          (ModMulConfig.U1 (Basis := qs.Basis) cfg)
          (qs.ket b)
        =
      ∑ t : Fin (ASize cfg.env.work),
        α t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b) := by
    simpa [ModMulConfig.U1] using hα

  have hlabel_inj :
      ∀ t u : Fin (ASize cfg.env.work),
        RegEncoding.writeNat cfg.env.work t.1 b
          =
        RegEncoding.writeNat cfg.env.work u.1 b →
        t = u := by
    intro t u hEq
    apply Fin.ext
    calc
      t.1
          =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work t.1 b) := by
          symm
          exact RegEncoding.toNat_writeNat_of_lt
            cfg.env.work t.1 b t.isLt
      _ =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work u.1 b) := by
          rw [hEq]
      _ = u.1 :=
          RegEncoding.toNat_writeNat_of_lt
            cfg.env.work u.1 b u.isLt

  have hcoeff :
      ∀ t : Fin (ASize cfg.env.work),
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
          RegEncoding.writeNat cfg.env.work t.1 b
            ≠
          RegEncoding.writeNat cfg.env.work u.1 b := by
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
    ∑ t : Fin (ASize cfg.env.work),
      α t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work t.1 b) := hαU1
    _ =
    ∑ t : Fin (ASize cfg.env.work),
      alg1PhaseCoeff qs cfg b t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work t.1 b) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hcoeff t]

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


private lemma good_input_expansion_of_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
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

private lemma qftPhase_zero_left
    (N y : ℕ) :
    qftPhase N 0 y = 1 := by
  simp [qftPhase, ωPow]

private lemma regQubits_succ_eq_append
    (lo n : ℕ) :
    regQubits ({ lo := lo, size := n + 1 } : Reg)
      =
    regQubits ({ lo := lo, size := n } : Reg) ++ [lo + n] := by
  simp [regQubits, List.range_succ, List.map_append]

private lemma H_reg_succ_eval
    (qs : QSemantics)
    (lo n : ℕ)
    (ψ : qs.State) :
    qs.eval (H_reg ({ lo := lo, size := n + 1 } : Reg)) ψ
      =
    qs.eval (H_reg ({ lo := lo, size := n } : Reg))
      (qs.eval (Gate.H (lo + n)) ψ) := by
  simp [
    H_reg,
    regQubits_succ_eq_append,
    List.foldl_append,
    qs.eval_seq
  ]

private lemma Hreg_QFT_scalar_succ
    (n : ℕ) :
    ((1 / Real.sqrt (2 : ℝ) : ℂ) *
        (1 / Real.sqrt (((2 ^ n : ℕ) : ℝ)) : ℂ))
      =
    (1 / Real.sqrt (((2 ^ (n + 1) : ℕ) : ℝ)) : ℂ) := by
  norm_num [Nat.pow_succ]

private lemma uniform_sum_succ_split
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (lo n : ℕ)
    (b : qs.Basis) :
    (∑ y : Fin (ASize ({ lo := lo, size := n + 1 } : Reg)),
        qs.ket
          (RegEncoding.writeNat
            ({ lo := lo, size := n + 1 } : Reg) y.1 b))
      =
    (∑ y : Fin (ASize ({ lo := lo, size := n } : Reg)),
        qs.ket
          (RegEncoding.writeNat
            ({ lo := lo, size := n } : Reg) y.1
            (RegEncoding.writeNat
              ({ lo := lo + n, size := 1 } : Reg) 0 b)))
      +
    (∑ y : Fin (ASize ({ lo := lo, size := n } : Reg)),
        qs.ket
          (RegEncoding.writeNat
            ({ lo := lo, size := n } : Reg) y.1
            (RegEncoding.writeNat
              ({ lo := lo + n, size := 1 } : Reg) 1 b))) :=
  by
  classical

  let r : Reg := { lo := lo, size := n + 1 }
  let low : Reg := { lo := lo, size := n }
  let high : Reg := { lo := lo + n, size := 1 }
  let M : ℕ := ASize low

  let m : SplitPoint r :=
    ⟨n, by simp [r, regSize]⟩

  have hleft : splitLeft r m = low := by
    simp [r, low, m, splitLeft]

  have hright : splitRight r m = high := by
    simp [r, high, m, splitRight]

  have hdisj : Disjoint low high := by
    unfold Shor.Disjoint
    left
    simp [low, high, Reg.hi]

  have hsize : ASize r = M + M := by
    simp [r, low, M, ASize, regSize, Nat.pow_succ, Nat.mul_two]

  have hhigh_zero : 0 < ASize high := by
    norm_num [high, ASize, regSize]

  have hhigh_one : 1 < ASize high := by
    norm_num [high, ASize, regSize]

  let f : ℕ → qs.State :=
    fun y => qs.ket (RegEncoding.writeNat r y b)

  let g0 : ℕ → qs.State :=
    fun y =>
      qs.ket
        (RegEncoding.writeNat low y
          (RegEncoding.writeNat high 0 b))

  let g1 : ℕ → qs.State :=
    fun y =>
      qs.ket
        (RegEncoding.writeNat low y
          (RegEncoding.writeNat high 1 b))

  have hlow :
      ∀ y : ℕ, y < M → f y = g0 y := by
    intro y hy

    have hs :=
      RegEncoding.writeNat_split
        r m 0 y b
        (by simpa [hleft, M] using hy)
        (by simpa [hright] using hhigh_zero)

    have hs' :
        RegEncoding.writeNat r y b
          =
        RegEncoding.writeNat high 0
          (RegEncoding.writeNat low y b) := by
      simpa [hleft, hright, M] using hs

    have hcomm :
        RegEncoding.writeNat low y
            (RegEncoding.writeNat high 0 b)
          =
        RegEncoding.writeNat high 0
            (RegEncoding.writeNat low y b) :=
      writeNat_comm_of_disjoint low high hdisj y 0 b

    dsimp [f, g0]
    exact congrArg qs.ket (hs'.trans hcomm.symm)

  have hhigh :
      ∀ y : ℕ, y < M → f (M + y) = g1 y := by
    intro y hy

    have hs :=
      RegEncoding.writeNat_split
        r m 1 y b
        (by simpa [hleft, M] using hy)
        (by simpa [hright] using hhigh_one)

    have hs' :
        RegEncoding.writeNat r (M + y) b
          =
        RegEncoding.writeNat high 1
          (RegEncoding.writeNat low y b) := by
      simpa [hleft, hright, M, Nat.add_comm] using hs

    have hcomm :
        RegEncoding.writeNat low y
            (RegEncoding.writeNat high 1 b)
          =
        RegEncoding.writeNat high 1
            (RegEncoding.writeNat low y b) :=
      writeNat_comm_of_disjoint low high hdisj y 1 b

    dsimp [f, g1]
    exact congrArg qs.ket (hs'.trans hcomm.symm)

  have htail :
      (∑ y ∈ Finset.range M, f (M + y))
        =
      ∑ y ∈ Finset.Ico M (M + M), f y := by
    symm
    simpa [Nat.add_sub_cancel] using
      (Finset.sum_Ico_eq_sum_range f M (M + M))

  have hsplit :
      (∑ y ∈ Finset.range M, f y)
        +
      (∑ y ∈ Finset.range M, f (M + y))
        =
      ∑ y ∈ Finset.range (ASize r), f y := by
    calc
      (∑ y ∈ Finset.range M, f y)
          +
        (∑ y ∈ Finset.range M, f (M + y))
          =
        (∑ y ∈ Finset.range M, f y)
          +
        (∑ y ∈ Finset.Ico M (M + M), f y) := by
          rw [htail]

      _ =
        ∑ y ∈ Finset.range (M + M), f y := by
          exact Finset.sum_range_add_sum_Ico f (by omega)

      _ =
        ∑ y ∈ Finset.range (ASize r), f y := by
          rw [hsize]

  have hsum0 :
      (∑ y ∈ Finset.range M, f y)
        =
      ∑ y ∈ Finset.range M, g0 y := by
    apply Finset.sum_congr rfl
    intro y hy
    exact hlow y (Finset.mem_range.mp hy)

  have hsum1 :
      (∑ y ∈ Finset.range M, f (M + y))
        =
      ∑ y ∈ Finset.range M, g1 y := by
    apply Finset.sum_congr rfl
    intro y hy
    exact hhigh y (Finset.mem_range.mp hy)

  have hmain :
      (∑ y : Fin (ASize r), f y.1)
        =
      (∑ y : Fin M, g0 y.1)
        +
      (∑ y : Fin M, g1 y.1) := by
    calc
      (∑ y : Fin (ASize r), f y.1)
          =
        ∑ y ∈ Finset.range (ASize r), f y := by
          simpa using
            (Fin.sum_univ_eq_sum_range f (ASize r))

      _ =
        (∑ y ∈ Finset.range M, f y)
          +
        (∑ y ∈ Finset.range M, f (M + y)) := by
          exact hsplit.symm

      _ =
        (∑ y ∈ Finset.range M, g0 y)
          +
        (∑ y ∈ Finset.range M, g1 y) := by
          rw [hsum0, hsum1]

      _ =
        (∑ y : Fin M, g0 y.1)
          +
        (∑ y : Fin M, g1 y.1) := by
          rw [Fin.sum_univ_eq_sum_range g0 M]
          rw [Fin.sum_univ_eq_sum_range g1 M]

  simpa [r, low, high, M, f, g0, g1] using hmain

lemma eval_Hreg_zero_uniform_sum
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (work : Reg)
    (b : qs.Basis)
    (hwork0 : RegEncoding.toNat work b = 0) :
    qs.eval (H_reg work) (qs.ket b)
      =
    ((1 / Real.sqrt ((ASize work : ℕ) : ℝ) : ℂ)) •
      ∑ y : Fin (ASize work),
        qs.ket (RegEncoding.writeNat work y.1 b) := by
  classical
  rcases work with ⟨lo, n⟩
  induction n generalizing b with
  | zero =>
      have hwrite :
          RegEncoding.writeNat ({ lo := lo, size := 0 } : Reg) 0 b = b := by
        exact
          (congrArg
            (fun v =>
              RegEncoding.writeNat
                ({ lo := lo, size := 0 } : Reg) v b)
            hwork0.symm).trans
            (RegEncoding.writeNat_toNat
              (r := ({ lo := lo, size := 0 } : Reg)) (b := b))
      simp [H_reg, regQubits, ASize, regSize, qs.eval_id, hwrite]
  | succ n ih =>
      let r : Reg := { lo := lo, size := n + 1 }
      let low : Reg := { lo := lo, size := n }
      let high : Reg := { lo := lo + n, size := 1 }
      let q : ℕ := lo + n

      have hsplit0 :
          RegEncoding.toNat low b
            + ASize low * RegEncoding.toNat high b = 0 := by
        have hright_size : n + 1 - n = 1 := by
          omega
        have hsplit :=
          RegEncoding.toNat_split
            (r := r)
            (m := ⟨n, by simp [r, regSize]⟩)
            (b := b)
        rw [hwork0] at hsplit
        have hsplit' :
            0 =
              RegEncoding.toNat low b
                + ASize low * RegEncoding.toNat high b := by
          simpa only [
            r, low, high, splitLeft, splitRight, regSize, ASize,
            hright_size
          ] using hsplit
        exact hsplit'.symm

      have hlow_b : RegEncoding.toNat low b = 0 := by
        omega

      have hdisj : Shor.Disjoint low high := by
        unfold Shor.Disjoint low high Reg.hi
        simp

      have hlow0 :
          RegEncoding.toNat low (RegEncoding.writeNat high 0 b) = 0 := by
        rw [RegEncoding.toNat_left_write_right low high hdisj b 0]
        exact hlow_b

      have hlow1 :
          RegEncoding.toNat low (RegEncoding.writeNat high 1 b) = 0 := by
        rw [RegEncoding.toNat_left_write_right low high hdisj b 1]
        exact hlow_b

      have hqlo : r.lo ≤ q := by
        simp [r, q]

      have hqhi : q < r.hi := by
        simp [r, q, Reg.hi]

      have hbit : RegEncoding.bit q b = false := by
        rw [RegEncoding.bit_eq_testBit_toNat (r := r) (b := b) (q := q) hqlo hqhi]
        rw [hwork0]
        simp [r, q]

      have hHq :
          qs.eval (Gate.H q) (qs.ket b)
            =
          ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
            (qs.ket (RegEncoding.writeNat high 0 b)
              + qs.ket (RegEncoding.writeNat high 1 b)) := by
        have hqh : qubitReg q = high := by
          simp [qubitReg, high, q]
        rw [HadamardSemantics.eval_H_ket]
        simp [hqh, hbit, smul_add]

      have ih0 :=
        ih (RegEncoding.writeNat high 0 b) hlow0

      have ih1 :=
        ih (RegEncoding.writeNat high 1 b) hlow1

      have hleft :
          qs.eval (H_reg r) (qs.ket b)
            =
          ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
            ((((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                ∑ y : Fin (ASize low),
                  qs.ket (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 0 b)))
              +
              (((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                ∑ y : Fin (ASize low),
                  qs.ket (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 1 b)))) := by
        calc
          qs.eval (H_reg r) (qs.ket b)
              =
            qs.eval (H_reg low)
              (qs.eval (Gate.H q) (qs.ket b)) := by
                simpa [r, low, q] using
                  H_reg_succ_eval qs lo n (qs.ket b)
          _ =
            qs.eval (H_reg low)
              (((1 / Real.sqrt (2 : ℝ) : ℂ)) •
                (qs.ket (RegEncoding.writeNat high 0 b)
                  + qs.ket (RegEncoding.writeNat high 1 b))) := by
                rw [hHq]
          _ =
            ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
              (qs.eval (H_reg low)
                  (qs.ket (RegEncoding.writeNat high 0 b))
                +
                qs.eval (H_reg low)
                  (qs.ket (RegEncoding.writeNat high 1 b))) := by
                rw [qs.eval_smul, qs.eval_add]
          _ =
            ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
              ((((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                  ∑ y : Fin (ASize low),
                    qs.ket (RegEncoding.writeNat low y.1
                      (RegEncoding.writeNat high 0 b)))
                +
                (((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                  ∑ y : Fin (ASize low),
                    qs.ket (RegEncoding.writeNat low y.1
                      (RegEncoding.writeNat high 1 b)))) := by
                rw [ih0, ih1]

      have hsum :
          (∑ y : Fin (ASize r),
              qs.ket (RegEncoding.writeNat r y.1 b))
            =
          (∑ y : Fin (ASize low),
              qs.ket
                (RegEncoding.writeNat low y.1
                  (RegEncoding.writeNat high 0 b)))
            +
          (∑ y : Fin (ASize low),
              qs.ket
                (RegEncoding.writeNat low y.1
                  (RegEncoding.writeNat high 1 b))) := by
        simpa [r, low, high] using
          uniform_sum_succ_split qs lo n b

      have hscalar :
          ((1 / Real.sqrt (2 : ℝ) : ℂ) *
              (1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ))
            =
          (1 / Real.sqrt ((ASize r : ℕ) : ℝ) : ℂ) := by
        simpa [r, low, ASize, regSize] using
          Hreg_QFT_scalar_succ n

      calc
        qs.eval (H_reg { lo := lo, size := n + 1 }) (qs.ket b)
            =
          ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
            ((((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                ∑ y : Fin (ASize low),
                  qs.ket (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 0 b)))
              +
              (((1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ)) •
                ∑ y : Fin (ASize low),
                  qs.ket (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 1 b)))) := by
              simpa [r] using hleft
        _ =
          (((1 / Real.sqrt (2 : ℝ) : ℂ) *
              (1 / Real.sqrt ((ASize low : ℕ) : ℝ) : ℂ))) •
            ((∑ y : Fin (ASize low),
                qs.ket
                  (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 0 b)))
              +
              (∑ y : Fin (ASize low),
                qs.ket
                  (RegEncoding.writeNat low y.1
                    (RegEncoding.writeNat high 1 b)))) := by
              simp [smul_add, smul_smul]
        _ =
          ((1 / Real.sqrt ((ASize r : ℕ) : ℝ) : ℂ)) •
            ∑ y : Fin (ASize r),
              qs.ket (RegEncoding.writeNat r y.1 b) := by
              rw [hscalar, hsum]

lemma eval_Hreg_zero_eq_QFT
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (work : Reg)
    (b : qs.Basis)
    (hwork0 : RegEncoding.toNat work b = 0) :
    qs.eval (H_reg work) (qs.ket b)
      =
    qs.eval (Gate.QFT work) (qs.ket b) := by
  rw [eval_Hreg_zero_uniform_sum qs work b hwork0]
  rw [QFTSemantics.eval_QFT_ket]
  simp [ASize, qftPhase_zero_left, hwork0]

lemma eval_IQFT_Hreg_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (work : Reg)
    (b : qs.Basis)
    (hwork0 : RegEncoding.toNat work b = 0) :
    qs.eval (IQFT work)
      (qs.eval (H_reg work) (qs.ket b))
      =
    qs.ket b := by
  rw [eval_Hreg_zero_eq_QFT qs work b hwork0]
  simpa [IQFT] using
    qs.eval_adj_apply (Gate.QFT work) (qs.ket b)

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


lemma eval_CPhaseProd_fixes_work_of_target_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hz : alg1TargetResidue cfg b = 0) :
    qs.eval
        (Gate.CPhaseProd
          cfg.ctrl
          ((2 * Real.pi *
              (((cfg.c + cfg.env.N - 1) % cfg.env.N : ℕ) : ℝ))
            / (cfg.env.N : ℝ))
          cfg.env.data
          cfg.env.work)
        (qs.eval (H_reg cfg.env.work) (qs.ket b))
      =
    qs.eval (H_reg cfg.env.work) (qs.ket b) := by
  classical

  let a : ℕ :=
    (cfg.c + cfg.env.N - 1) % cfg.env.N

  let φ : ℝ :=
    (2 * Real.pi * (a : ℝ)) / (cfg.env.N : ℝ)

  have hNpos : 0 < cfg.env.N :=
    Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

  have hdatawork : Disjoint cfg.env.data cfg.env.work := by
    rcases cfg.layout.1 with h | h
    · left
      change cfg.env.data.lo + cfg.env.data.size ≤ cfg.env.work.lo
      have h' :
          cfg.env.data.lo + (cfg.env.data.size + 1)
            ≤ cfg.env.work.lo := by
        simpa [extendHi, Reg.hi] using h
      omega
    · exact Or.inr h

  have hterm :
      ∀ t : Fin (ASize cfg.env.work),
        qs.eval
            (Gate.CPhaseProd
              cfg.ctrl
              φ
              cfg.env.data cfg.env.work)
            (qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b))
          =
        qs.ket
          (RegEncoding.writeNat cfg.env.work t.1 b) := by
    intro t
    rw [
      GateSemanticsFacts.eval_CPhaseProd_ket
        qs cfg.ctrl
        φ
        cfg.env.data cfg.env.work
        (RegEncoding.writeNat cfg.env.work t.1 b)
        hdatawork
    ]
    have hctrl_write :
        RegEncoding.bit cfg.ctrl
            (RegEncoding.writeNat cfg.env.work t.1 b)
          =
        RegEncoding.bit cfg.ctrl b :=
      RegEncoding.bit_writeNat_out
        (r := cfg.env.work)
        (v := t.1)
        (b := b)
        (q := cfg.ctrl)
        cfg.layout.2.2.2.2.1

    have hdata :
        RegEncoding.toNat cfg.env.data
            (RegEncoding.writeNat cfg.env.work t.1 b)
          =
        RegEncoding.toNat cfg.env.data b :=
      RegEncoding.toNat_left_write_right
        cfg.env.data
        cfg.env.work
        hdatawork
        b
        t.1

    have hwork :
        RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat cfg.env.work t.1 b)
          =
        t.1 :=
      RegEncoding.toNat_writeNat_of_lt cfg.env.work t.1 b t.isLt

    rw [hctrl_write, hdata, hwork]
    by_cases hctrl : RegEncoding.bit cfg.ctrl b
    · let x : ℕ := RegEncoding.toNat cfg.env.data b
      have hzmod :
          Nat.ModEq cfg.env.N (a * x) 0 := by
        change (a * x) % cfg.env.N = 0 % cfg.env.N
        have hz' : (a * x) % cfg.env.N = 0 := by
          simpa [alg1TargetResidue, a, x, hctrl] using hz
        rw [hz', Nat.zero_mod cfg.env.N]
      have hexp :
          Complex.exp
              (φ * Complex.I * ((x : ℂ) * (t.1 : ℂ)))
            =
          1 := by
        calc
          Complex.exp
              (φ * Complex.I * ((x : ℂ) * (t.1 : ℂ)))
            =
          Complex.exp
            (((2 * Real.pi) / (cfg.env.N : ℝ)) *
              Complex.I *
              (((a * x : ℕ) : ℂ) * (t.1 : ℂ))) := by
              congr 1
              dsimp [φ, a]
              push_cast
              ring
          _ =
          Complex.exp
            (((2 * Real.pi) / (cfg.env.N : ℝ)) *
              Complex.I *
              (((0 : ℕ) : ℂ) * (t.1 : ℂ))) :=
            alg1_exp_phase_eq_of_modEq'
              cfg.env.N
              (a * x)
              0
              t.1
              hNpos
              hzmod
          _ =
          Complex.exp
            (((2 * Real.pi) / (cfg.env.N : ℝ)) *
              Complex.I *
              ((0 : ℂ) * (t.1 : ℂ))) := by
            simp
          _ = 1 := by
            simp
      simp [hctrl, x, hexp]
    · simp [hctrl]

  let z0 : Fin (ASize cfg.env.work) :=
    ⟨RegEncoding.toNat cfg.env.work b,
      RegEncoding.toNat_lt_ASize cfg.env.work b⟩

  have hz0 :
      RegEncoding.writeNat cfg.env.work z0.1 b = b := by
    simpa [z0] using
      (RegEncoding.writeNat_toNat cfg.env.work b)

  rcases eval_Hreg_work_expansion qs cfg.env.work b z0 with
    ⟨β, hβ⟩

  have hH :
      qs.eval (H_reg cfg.env.work) (qs.ket b)
        =
      ∑ t : Fin (ASize cfg.env.work),
        β t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b) := by
    calc
      qs.eval (H_reg cfg.env.work) (qs.ket b)
          =
        qs.eval (H_reg cfg.env.work)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work z0.1 b)) := by
              rw [hz0]
      _ =
        ∑ t : Fin (ASize cfg.env.work),
          β t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := hβ

  calc
    qs.eval
        (Gate.CPhaseProd
          cfg.ctrl
          φ
          cfg.env.data
          cfg.env.work)
        (qs.eval (H_reg cfg.env.work) (qs.ket b))
      =
    qs.eval
        (Gate.CPhaseProd
          cfg.ctrl
          φ
          cfg.env.data cfg.env.work)
        (∑ t : Fin (ASize cfg.env.work),
          β t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b)) := by
          rw [hH]

    _ =
    ∑ t : Fin (ASize cfg.env.work),
      qs.eval
        (Gate.CPhaseProd
          cfg.ctrl
          φ
          cfg.env.data cfg.env.work)
        (β t •
          qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b)) := by
          simpa using
            eval_finset_sum
              qs
              (Gate.CPhaseProd
                cfg.ctrl
                φ
                cfg.env.data cfg.env.work)
              Finset.univ
              (fun t =>
                β t •
                  qs.ket
                    (RegEncoding.writeNat cfg.env.work t.1 b))

    _ =
    ∑ t : Fin (ASize cfg.env.work),
      β t •
        qs.eval
          (Gate.CPhaseProd
            cfg.ctrl
            φ
            cfg.env.data cfg.env.work)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [qs.eval_smul]

    _ =
    ∑ t : Fin (ASize cfg.env.work),
      β t •
        qs.ket
          (RegEncoding.writeNat cfg.env.work t.1 b) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hterm t]

    _ =
    qs.eval (H_reg cfg.env.work) (qs.ket b) :=
      hH.symm

lemma alg1_step1_zero_target_exact
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
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
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        (qs.ket b)
      =
    qs.ket b := by
  let φ : ℝ :=
    (2 * Real.pi *
        (((cfg.c + cfg.env.N - 1) % cfg.env.N : ℕ) : ℝ))
      / (cfg.env.N : ℝ)

  have hphase :
      qs.eval
          (Gate.CPhaseProd
            cfg.ctrl φ cfg.env.data cfg.env.work)
          (qs.eval (H_reg cfg.env.work) (qs.ket b))
        =
      qs.eval (H_reg cfg.env.work) (qs.ket b) := by
    simpa [φ] using
      eval_CPhaseProd_fixes_work_of_target_zero qs cfg b hz

  calc
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        (qs.ket b)
      =
    qs.eval (IQFT cfg.env.work)
      (qs.eval
        (Gate.CPhaseProd cfg.ctrl φ cfg.env.data cfg.env.work)
        (qs.eval (H_reg cfg.env.work) (qs.ket b))) := by
          simp [step1, qs.eval_seq, φ]


    _ =
    qs.eval (IQFT cfg.env.work)
      (qs.eval (H_reg cfg.env.work) (qs.ket b)) := by
        rw [hphase]

    _ = qs.ket b :=
      eval_IQFT_Hreg_zero
        (qs := qs)
        cfg.env.work
        b
        hb.2.2.1
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
    have hsum : (c + N - 1) + 1 = c + N := by
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
      (a + 1) * x = a * x + 1 * x := Nat.add_mul a 1 x
      _ = a * x + x := by simp
      _ = x + a * x := Nat.add_comm _ _

  have hxr :
      x + ((a * x) % N) ≡ x + a * x [MOD N] :=
    Nat.ModEq.add_left x (Nat.mod_modEq (a * x) N)

  have hmod :
      c * x ≡ x + ((a * x) % N) [MOD N] := by
    calc
      c * x ≡ (a + 1) * x [MOD N] := hcx
      _ ≡ x + a * x [MOD N] := by rw [hax]
      _ ≡ x + ((a * x) % N) [MOD N] := hxr.symm

  simpa [Nat.ModEq, a] using hmod


private lemma nat_fraction_lt_iff_cross
    (a n t m : ℕ)
    (hn : 0 < n)
    (hm : 0 < m) :
    (a : ℝ) / (n : ℝ) < (t : ℝ) / (m : ℝ)
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

lemma alg1_step4_cross_iff_overflow_of_good
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work))
    (hb :
      GoodModMulBasisInput
        (inferInstance : QSemantics)
        cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (ht : t ∈ alg1GoodLabels cfg b)
    (hzero :
      alg1TargetResidue cfg b = 0 →
      t.1 = 0) :
    alg1Step4CrossCondition cfg b t
      ↔
    alg1Overflow cfg b := by
  classical

  let N : ℕ := cfg.env.N
  let A : ℕ := ASize cfg.env.data
  let M : ℕ := ASize cfg.env.work
  let x : ℕ := RegEncoding.toNat cfg.env.data b
  let r : ℕ := alg1TargetResidue cfg b
  let y : ℕ := alg1OutputValue cfg b
  let s : ℕ := x + r

  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

  have hApos : 0 < A := by
    dsimp [A, ASize]
    positivity

  have hMpos : 0 < M := by
    dsimp [M, ASize]
    positivity

  have hxlt : x < N := by
    simpa [x, N] using hb.1

  have hrlt : r < N := by
    simpa [r, N] using alg1TargetResidue_lt_N cfg b

  have hslt : s < 2 * N := by
    dsimp [s]
    omega

  have hNposR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hNpos

  have hAposR : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast hApos

  have hMposR : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hMpos

  have hNleA : (N : ℝ) ≤ (A : ℝ) := by
    dsimp [N, A]
    exact_mod_cast cfg.env.data_capacity

  have heta :
      η < (1 / 2 : ℝ) :=
    cfg.env.precision.2.1

  have hetaN :
      η * (N : ℝ) < (1 / 2 : ℝ) * (N : ℝ) :=
    mul_lt_mul_of_pos_right heta hNposR

  have hhalfNleA :
      (1 / 2 : ℝ) * (N : ℝ) ≤ (A : ℝ) := by
    nlinarith

  have hdelta :
      η / (A : ℝ) < 1 / (N : ℝ) := by
    apply (div_lt_div_iff₀ hAposR hNposR).mpr
    nlinarith

  have hgood :
      |(r : ℝ) / (N : ℝ) - (t.1 : ℝ) / (M : ℝ)|
        <
      η / (A : ℝ) := by
    have hraw := (Finset.mem_filter.mp ht).2
    simpa [
      alg1GoodLabels,
      alg1TargetFraction,
      alg1WorkFraction,
      r, N, M, A
    ] using hraw

  rcases abs_lt.mp hgood with ⟨hgood_left, hgood_right⟩

  have hbelow :
      (r : ℝ) / (N : ℝ) - η / (A : ℝ)
        <
      (t.1 : ℝ) / (M : ℝ) := by
    linarith

  have habove :
      (t.1 : ℝ) / (M : ℝ)
        <
      (r : ℝ) / (N : ℝ) + η / (A : ℝ) := by
    linarith

  have hy_mod :
      y = s % N := by
    dsimp [y, s, r, x, N]
    by_cases hctrl : RegEncoding.bit cfg.ctrl b
    ·
      simp only [
        alg1OutputValue,
        alg1TargetResidue,
        hctrl,
        if_true
      ]
      exact
        alg1_output_mod
          cfg.c
          cfg.env.N
          (RegEncoding.toNat cfg.env.data b)
          (Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one)
    ·
      simp [
        alg1OutputValue,
        alg1TargetResidue,
        hctrl,
        Nat.mod_eq_of_lt hb.1
      ]

  change y * M < N * t.1 ↔ N ≤ s

  by_cases hover : N ≤ s
  ·
    have hy_over :
        y = s - N := by
      calc
        y = s % N := hy_mod
        _ = (s - N) % N := Nat.mod_eq_sub_mod hover
        _ = s - N := Nat.mod_eq_of_lt (by omega)

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
      mul_le_mul_of_nonneg_right hgapR (le_of_lt hNposR)

    have hdiv :
        ((y : ℝ) + 1) / (N : ℝ)
          ≤
        (r : ℝ) / (N : ℝ) :=
      (div_le_div_iff₀ hNposR hNposR).mpr <| by
        simpa [mul_comm] using hmul

    have hsplit :
        ((y : ℝ) + 1) / (N : ℝ)
          =
        (y : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
      ring

    rw [hsplit] at hdiv

    have hyfrac :
        (y : ℝ) / (N : ℝ)
          <
        (r : ℝ) / (N : ℝ) - η / (A : ℝ) := by
      linarith

    have hcrossfrac :
        (y : ℝ) / (N : ℝ)
          <
        (t.1 : ℝ) / (M : ℝ) :=
      lt_trans hyfrac hbelow

    have hcross :
        y * M < N * t.1 := by
      have hraw :=
        (nat_fraction_lt_iff_cross y N t.1 M hNpos hMpos).mp
          hcrossfrac
      simpa [Nat.mul_comm] using hraw

    constructor
    · intro _
      exact hover
    · intro _
      exact hcross

  ·
    have hy_no :
        y = s := by
      calc
        y = s % N := hy_mod
        _ = s := Nat.mod_eq_of_lt (lt_of_not_ge hover)

    by_cases hxzero : x = 0
    ·
      have hrzero :
          r = 0 := by
        dsimp [r]
        unfold alg1TargetResidue
        by_cases hctrl : RegEncoding.bit cfg.ctrl b
        · simp [hctrl]; simp_all only [Nat.cast_pos, Nat.cast_le, one_div, mul_lt_mul_iff_left₀,
          neg_lt_sub_iff_lt_add, not_le, mul_zero, Nat.zero_mod, N, A, M, x, r, s, y]
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

    ·
      have hxpos : 0 < x :=
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
        mul_le_mul_of_nonneg_right hgapR (le_of_lt hNposR)

      have hdiv :
          ((r : ℝ) + 1) / (N : ℝ)
            ≤
          (y : ℝ) / (N : ℝ) :=
        (div_le_div_iff₀ hNposR hNposR).mpr <| by
          simpa [mul_comm] using hmul

      have hsplit :
          ((r : ℝ) + 1) / (N : ℝ)
            =
          (r : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
        ring

      rw [hsplit] at hdiv

      have hyr :
          (r : ℝ) / (N : ℝ) + η / (A : ℝ)
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
          (nat_fraction_lt_iff_cross t.1 M y N hMpos hNpos).mp
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

lemma alg1_trace_of_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (hψ : cfg.ValidState qs ψ) :
    ∃ _tr : Alg1Trace qs cfg ψ, True := by
  classical

  rcases good_input_expansion_of_valid qs cfg ψ hψ with
    ⟨support, inputCoeff, hinput, hgood⟩

  let zeroWork : Fin (ASize cfg.env.work) :=
    ⟨0, by simp[ASize]⟩

  let phaseCoeff :
      qs.Basis →
        Fin (ASize cfg.env.work) →
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
        RegEncoding.writeNat cfg.env.work t.1 b ≠ b := by
      intro hEq
      have ht_read :
          t.1 =
            RegEncoding.toNat cfg.env.work
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
        symm
        exact RegEncoding.toNat_writeNat_of_lt
          cfg.env.work t.1 b t.isLt
      have : t.1 = 0 := by
        calc
          t.1 =
              RegEncoding.toNat cfg.env.work
                (RegEncoding.writeNat cfg.env.work t.1 b) := ht_read
          _ = RegEncoding.toNat cfg.env.work b := by rw [hEq]
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
              cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
            (qs.ket b)
          =
        ∑ t : Fin (ASize cfg.env.work),
          phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
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
        cfg b t (hgood b hbmem) ht
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
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        ψ
      =
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        (∑ b ∈ support,
          inputCoeff b • qs.ket b) := by
        rw [hinput]

    _ =
    ∑ b ∈ support,
      qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        (inputCoeff b • qs.ket b) := by
        simpa using
          eval_finset_sum
            qs
            (step1
              (Basis := qs.Basis)
              cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
            support
            (fun b => inputCoeff b • qs.ket b)

    _ =
    ∑ b ∈ support,
      inputCoeff b •
        qs.eval
          (step1
            (Basis := qs.Basis)
            cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
          (qs.ket b) := by
        apply Finset.sum_congr rfl
        intro b hb
        simpa using
          qs.eval_smul
            (step1
              (Basis := qs.Basis)
              cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
            (inputCoeff b)
            (qs.ket b)

    _ =
    ∑ b ∈ support,
      inputCoeff b •
        ∑ t : Fin (ASize cfg.env.work),
          phaseCoeff b t •
            qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hphase b (hgood b hb)]
