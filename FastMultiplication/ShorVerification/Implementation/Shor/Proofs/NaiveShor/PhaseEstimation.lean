import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.NaiveShor.Preliminaries
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.NaiveShor.Lemmas

/-!
# NaiveShor — quantum phase estimation / IQFT analysis

The QPE chain for ideal order finding: the pre-IQFT state, the exact inverse-QFT
evaluation, the grouping of outputs by residue class, the measurement projector on
the grouped post-IQFT state, and the paper output-probability formula.
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]

/--
The ideal state immediately before the inverse QFT:

    1 / √Q ∑_{t=0}^{Q-1} |t⟩ |a^t mod N⟩.

Writing this as a definition keeps all later Fourier lemmas independent
of the implementation of `H_reg`, `initY1`, and `modExpIdeal'`.
-/
noncomputable def idealPreIQFTState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (a N : ℕ)
    (x y : ExtReg)
    (b0 : qs.Basis) :
    qs.State :=
  ((1 / Real.sqrt (ASize x.active : ℝ) : ℂ)) •
    ∑ t : Fin (ASize x.active),
      qs.ket
        (RegEncoding.writeNat y.active
          (a ^ t.1 % N)
          (RegEncoding.writeNat x.active t.1 b0))

private def shorOutputBasis
    (a N : ℕ)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (o s : ℕ) : qs.Basis :=
  RegEncoding.writeNat x.active o
    (RegEncoding.writeNat y.active
      (a ^ s % N) b0)

private noncomputable def shorGroupedPostIQFTState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (a N Q r : ℕ)
    (x y : ExtReg)
    (b0 : qs.Basis) : qs.State :=
  ∑ o : Fin Q,
    ∑ s ∈ Finset.range r,
      shorPeriodClassAmplitude Q r s o.1 •
        qs.ket
          (shorOutputBasis
            (qs := qs) a N x y b0 o.1 s)

private lemma active_disjoint_of_ownedDisjoint
    {x y : ExtReg}
    (h : ExtReg.OwnedDisjoint x y) :
    Disjoint x.active y.active := by
  intro q hx hy
  exact
    h
      (List.mem_append_left x.reserve.qubits hx)
      (List.mem_append_left y.reserve.qubits hy)

private lemma eval_finset_sum_local
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
      simp [qs.eval_zero]
  | @insert a s ha ih =>
      simp [Finset.sum_insert, ha, qs.eval_add, ih]

private lemma eval_fintype_sum_local
    [GateSemanticsCore qs]
    (U : Gate)
    {ι : Type*}
    [Fintype ι]
    (f : ι → qs.State) :
    qs.eval U (∑ i, f i)
      =
    ∑ i, qs.eval U (f i) := by
  classical
  simpa using
    (eval_finset_sum_local
      (qs := qs) U
      (Finset.univ : Finset ι) f)

private lemma shor_inv_sqrt_sq
    (Q : ℕ)
    (hQ : 0 < Q) :
    ((1 / Real.sqrt (Q : ℝ) : ℂ) *
      (1 / Real.sqrt (Q : ℝ) : ℂ))
      =
    1 / (Q : ℂ) := by
  have hQr : 0 < (Q : ℝ) := by
    exact_mod_cast hQ

  have hs0 :
      (Real.sqrt (Q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (Real.sqrt_pos.2 hQr))

  have hQ0 :
      (Q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hQ)

  field_simp [hs0, hQ0]
  norm_cast
  simp

/--
Powers of `a` modulo `N` are periodic with period
`ord a N gcd`.
-/
private lemma shor_pow_mod_periodic
    (inst : ShorOrderFindingInstance)
    (t : ℕ) :
    inst.a ^ t % inst.N
      =
    inst.a ^
        (t % ord inst.a inst.N inst.coprime) %
      inst.N := by
  let u : (ZMod inst.N)ˣ :=
    ZMod.unitOfCoprime
      inst.a
      ((Nat.coprime_iff_gcd_eq_one).2 inst.coprime)

  have hu :
      u ^ (t % orderOf u) = u ^ t :=
    pow_mod_orderOf u t

  have hz :
      ((inst.a ^
          (t % ord inst.a inst.N inst.coprime) : ℕ) :
          ZMod inst.N)
        =
      ((inst.a ^ t : ℕ) : ZMod inst.N) := by
    have hcoe :
        ((u : ZMod inst.N) ^ (t % orderOf u))
          =
        ((u : ZMod inst.N) ^ t) :=
      congrArg
        (fun z : (ZMod inst.N)ˣ =>
          (z : ZMod inst.N))
        hu

    simpa [
      u,
      ord,
      ZMod.coe_unitOfCoprime,
      Nat.cast_pow
    ] using hcoe

  have hmod :=
    (ZMod.natCast_eq_natCast_iff'
      (inst.a ^
        (t % ord inst.a inst.N inst.coprime))
      (inst.a ^ t)
      inst.N).1 hz

  exact hmod.symm

/--
Before one full order has elapsed, distinct exponents give distinct
powers modulo `N`.
-/
private lemma shor_pow_mod_injective_below_order
    (inst : ShorOrderFindingInstance)
    {s t : ℕ}
    (hs : s < ord inst.a inst.N inst.coprime)
    (ht : t < ord inst.a inst.N inst.coprime)
    (h : inst.a ^ s % inst.N = inst.a ^ t % inst.N) :
    s = t := by
  let u : (ZMod inst.N)ˣ :=
    ZMod.unitOfCoprime
      inst.a
      ((Nat.coprime_iff_gcd_eq_one).2 inst.coprime)

  have hz :
      ((inst.a ^ s : ℕ) : ZMod inst.N)
        =
      ((inst.a ^ t : ℕ) : ZMod inst.N) :=
    (ZMod.natCast_eq_natCast_iff'
      (inst.a ^ s)
      (inst.a ^ t)
      inst.N).2 h

  have hu :
      u ^ s = u ^ t := by
    apply Units.ext
    simpa [
      u,
      ZMod.coe_unitOfCoprime
    ] using hz

  exact
    (pow_injOn_Iio_orderOf (x := u))
      (by simpa [u, ord] using hs)
      (by simpa [u, ord] using ht)
      hu

/--
Exact inverse-QFT action on a computational-basis state.

This is Fourier inversion: the inverse transform uses the conjugated
`qftPhase`.
-/
private lemma eval_IQFT_ket_exact
    [GateSemanticsFacts qs]
    (x : ExtReg)
    (b : qs.Basis) :
    qs.eval (IQFT x) (qs.ket b)
      =
    ((1 / Real.sqrt (ASize x.active : ℝ) : ℂ)) •
      ∑ o : Fin (ASize x.active),
        star
            (qftPhase
              (ASize x.active)
              (RegEncoding.toNat x.active b)
              o.1) •
          qs.ket
            (RegEncoding.writeNat
              x.active o.1 b) := by
  simpa [IQFT, ExtReg.toNat] using
    (QFTSemantics.eval_adj_QFT_ket
      (qs := qs) x b)

private lemma shor_preIQFT_x_value
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hxy : Disjoint x.active y.active)
    (t : Fin (ASize x.active)) :
    RegEncoding.toNat x.active
        (RegEncoding.writeNat y.active
          (inst.a ^ t.1 % inst.N)
          (RegEncoding.writeNat
            x.active t.1 b0))
      =
    t.1 := by
  rw [
    RegEncoding.toNat_left_write_right
      x.active
      y.active
      hxy
  ]

  exact
    RegEncoding.toNat_writeNat_of_lt
      x.active t.1 b0 t.isLt

private lemma shor_IQFT_output_basis_eq
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hxy : Disjoint x.active y.active)
    (t o : Fin (ASize x.active)) :
    RegEncoding.writeNat x.active o.1
        (RegEncoding.writeNat y.active
          (inst.a ^ t.1 % inst.N)
          (RegEncoding.writeNat
            x.active t.1 b0))
      =
    shorOutputBasis
      (qs := qs)
      inst.a inst.N
      x y b0
      o.1
      (t.1 %
        ord inst.a inst.N inst.coprime) := by
  rw [shor_pow_mod_periodic inst t.1]

  unfold shorOutputBasis

  rw [
    writeNat_comm_of_disjoint
      y.active
      x.active
      (Disjoint.symm hxy)
  ]

  rw [writeNat_overwrite_same_reg]

private lemma shor_group_fixed_output
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hr :
      0 < ord inst.a inst.N inst.coprime)
    (o : Fin (ASize x.active)) :
    (∑ t ∈ Finset.range (ASize x.active),
        ((1 / (ASize x.active : ℂ)) *
          star
            (qftPhase
              (ASize x.active)
              t
              o.1)) •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0
              o.1
              (t %
                ord inst.a inst.N
                  inst.coprime)))
      =
    ∑ s ∈
        Finset.range
          (ord inst.a inst.N inst.coprime),
      shorPeriodClassAmplitude
          (ASize x.active)
          (ord inst.a inst.N inst.coprime)
          s o.1 •
        qs.ket
          (shorOutputBasis
            (qs := qs)
            inst.a inst.N
            x y b0
            o.1 s) := by
  classical

  rw [
    sum_range_group_by_mod
      (ASize x.active)
      (ord inst.a inst.N inst.coprime)
      hr
      (fun s t =>
        ((1 / (ASize x.active : ℂ)) *
          star
            (qftPhase
              (ASize x.active)
              t o.1)) •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0
              o.1 s))
  ]

  apply Finset.sum_congr rfl
  intro s hs

  rw [← Finset.sum_smul]

  congr 1

  simp [
    shorPeriodClassAmplitude,
    Finset.mul_sum
  ]

/--
After IQFT, regroup the exponent sum according to `t % r`.

For a fixed output `o` and residue class `s`, the coefficient is exactly

    1/Q * ∑_{t<Q, t % r = s} conj(qftPhase Q t o),

which is `shorPeriodClassAmplitude`.
-/
private lemma eval_IQFT_idealPreIQFTState_grouped
    [GateSemanticsFacts qs]
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hsetting :
      BasicSetting
        inst.a
        (ord inst.a inst.N inst.coprime)
        inst.N
        (regSize x.active)
        (regSize y.active))
    (hinput :
      IdealOrderFindingInput qs x y b0) :
    qs.eval
        (IQFT x)
        (idealPreIQFTState
          qs inst.a inst.N x y b0)
      =
    shorGroupedPostIQFTState
      qs inst.a inst.N
      (ASize x.active)
      (ord inst.a inst.N inst.coprime)
      x y b0 := by
  classical

  let Q : ℕ :=
    ASize x.active

  let r : ℕ :=
    ord inst.a inst.N inst.coprime

  let c : ℂ :=
    (1 / Real.sqrt (Q : ℝ) : ℂ)

  have hQ : 0 < Q := by
    simp [Q, ASize]

  have hr : 0 < r := by
    simpa [r] using
      (shor_order_parameter_bounds hsetting).1

  have hxy :
      Disjoint x.active y.active :=
    active_disjoint_of_ownedDisjoint
      hinput.2.2

  have hscalar :
      c * c = 1 / (Q : ℂ) := by
    simpa [c] using
      shor_inv_sqrt_sq Q hQ

  change
    qs.eval
        (IQFT x)
        (c •
          ∑ t : Fin Q,
            qs.ket
              (RegEncoding.writeNat y.active
                (inst.a ^ t.1 % inst.N)
                (RegEncoding.writeNat
                  x.active t.1 b0)))
      =
    _

  calc
    qs.eval
        (IQFT x)
        (c •
          ∑ t : Fin Q,
            qs.ket
              (RegEncoding.writeNat y.active
                (inst.a ^ t.1 % inst.N)
                (RegEncoding.writeNat
                  x.active t.1 b0)))
        =
      c •
        ∑ t : Fin Q,
          c •
            ∑ o : Fin Q,
              star
                  (qftPhase Q t.1 o.1) •
                qs.ket
                  (RegEncoding.writeNat
                    x.active o.1
                    (RegEncoding.writeNat y.active
                      (inst.a ^ t.1 % inst.N)
                      (RegEncoding.writeNat
                        x.active t.1 b0))) := by
      rw [
        qs.eval_smul,
        eval_fintype_sum_local
      ]

      congr 1

      apply Finset.sum_congr rfl
      intro t ht

      have hxt :=
        shor_preIQFT_x_value
          (qs := qs)
          inst x y b0 hxy
          (show Fin (ASize x.active) from
            ⟨t.1, by simp[Q]⟩)

      have hiqft :=
        eval_IQFT_ket_exact
          (qs := qs)
          x
          (RegEncoding.writeNat y.active
            (inst.a ^ t.1 % inst.N)
            (RegEncoding.writeNat
              x.active t.1 b0))

      simpa [Q, c, hxt] using hiqft

    _ =
      ∑ t : Fin Q,
        ∑ o : Fin Q,
          ((1 / (Q : ℂ)) *
            star
              (qftPhase Q t.1 o.1)) •
            qs.ket
              (RegEncoding.writeNat
                x.active o.1
                (RegEncoding.writeNat y.active
                  (inst.a ^ t.1 % inst.N)
                  (RegEncoding.writeNat
                    x.active t.1 b0))) := by
      rw [Finset.smul_sum]

      apply Finset.sum_congr rfl
      intro t ht

      rw [smul_smul, Finset.smul_sum]

      apply Finset.sum_congr rfl
      intro o ho

      rw [smul_smul]

      congr 1
      rw [hscalar]

    _ =
      ∑ t : Fin Q,
        ∑ o : Fin Q,
          ((1 / (Q : ℂ)) *
            star
              (qftPhase Q t.1 o.1)) •
            qs.ket
              (shorOutputBasis
                (qs := qs)
                inst.a inst.N
                x y b0
                o.1
                (t.1 % r)) := by
      apply Finset.sum_congr rfl
      intro t ht

      apply Finset.sum_congr rfl
      intro o ho

      have hbasis :=
        shor_IQFT_output_basis_eq
          (qs := qs)
          inst x y b0 hxy
          (show Fin (ASize x.active) from
            ⟨t.1, by simp[Q]⟩)
          (show Fin (ASize x.active) from
            ⟨o.1, by simp[Q]⟩)

      simpa [r] using
        congrArg
          (fun b =>
            ((1 / (Q : ℂ)) *
              star
                (qftPhase Q t.1 o.1)) •
              qs.ket b)
          hbasis

    _ =
      ∑ o : Fin Q,
        ∑ t : Fin Q,
          ((1 / (Q : ℂ)) *
            star
              (qftPhase Q t.1 o.1)) •
            qs.ket
              (shorOutputBasis
                (qs := qs)
                inst.a inst.N
                x y b0
                o.1
                (t.1 % r)) := by
      rw [Finset.sum_comm]

    _ =
      ∑ o : Fin Q,
        ∑ t ∈ Finset.range Q,
          ((1 / (Q : ℂ)) *
            star
              (qftPhase Q t o.1)) •
            qs.ket
              (shorOutputBasis
                (qs := qs)
                inst.a inst.N
                x y b0
                o.1
                (t % r)) := by
      apply Finset.sum_congr rfl
      intro o ho

      exact
        Fin.sum_univ_eq_sum_range
          (fun t =>
            ((1 / (Q : ℂ)) *
              star
                (qftPhase Q t o.1)) •
              qs.ket
                (shorOutputBasis
                  (qs := qs)
                  inst.a inst.N
                  x y b0
                  o.1
                  (t % r)))
          Q

    _ =
      ∑ o : Fin Q,
        ∑ s ∈ Finset.range r,
          shorPeriodClassAmplitude
              Q r s o.1 •
            qs.ket
              (shorOutputBasis
                (qs := qs)
                inst.a inst.N
                x y b0
                o.1 s) := by
      apply Finset.sum_congr rfl
      intro o ho

      simpa [Q, r] using
        (shor_group_fixed_output
          (qs := qs)
          inst x y b0
          (by simpa [r] using hr)
          (show Fin (ASize x.active) from
            ⟨o.1, by simp [Q]⟩))

    _ =
      shorGroupedPostIQFTState
        qs inst.a inst.N
        (ASize x.active)
        (ord inst.a inst.N inst.coprime)
        x y b0 := by
      simp [
        shorGroupedPostIQFTState,
        Q,
        r
      ]

@[simp]
private lemma shorOutputBasis_x_value
    (a N : ℕ)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (o : Fin (ASize x.active))
    (s : ℕ) :
    RegEncoding.toNat x.active
        (shorOutputBasis
          (qs := qs)
          a N x y b0 o.1 s)
      =
    o.1 := by
  exact
    RegEncoding.toNat_writeNat_of_lt
      x.active
      o.1
      (RegEncoding.writeNat y.active
        (a ^ s % N) b0)
      o.isLt

/--
Measuring exponent outcome `o` kills every outer Fourier component
except the component labelled by `o`.
-/
private lemma measProj_shorGroupedPostIQFTState
    [MeasureClass qs]
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (o : Fin (ASize x.active)) :
    MeasureClass.measProj x.active o.1
        (shorGroupedPostIQFTState
          qs
          inst.a inst.N
          (ASize x.active)
          (ord inst.a inst.N inst.coprime)
          x y b0)
      =
    ∑ s ∈
        Finset.range
          (ord inst.a inst.N inst.coprime),
      shorPeriodClassAmplitude
          (ASize x.active)
          (ord inst.a inst.N inst.coprime)
          s o.1 •
        qs.ket
          (shorOutputBasis
            (qs := qs)
            inst.a inst.N
            x y b0 o.1 s) := by
  classical

  let P :=
    MeasureClass.measProj
      (qs := qs) x.active o.1

  unfold shorGroupedPostIQFTState
  change
    P
      (∑ o' : Fin (ASize x.active),
        ∑ s ∈
          Finset.range
            (ord inst.a inst.N inst.coprime),
          shorPeriodClassAmplitude
              (ASize x.active)
              (ord inst.a inst.N inst.coprime)
              s o'.1 •
            qs.ket
              (shorOutputBasis
                (qs := qs)
                inst.a inst.N
                x y b0 o'.1 s))
      =
    _

  rw [map_sum]

  have hkeep :
      P
          (∑ s ∈
            Finset.range
              (ord inst.a inst.N inst.coprime),
            shorPeriodClassAmplitude
                (ASize x.active)
                (ord inst.a inst.N inst.coprime)
                s o.1 •
              qs.ket
                (shorOutputBasis
                  (qs := qs)
                  inst.a inst.N
                  x y b0 o.1 s))
        =
      ∑ s ∈
        Finset.range
          (ord inst.a inst.N inst.coprime),
        shorPeriodClassAmplitude
            (ASize x.active)
            (ord inst.a inst.N inst.coprime)
            s o.1 •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0 o.1 s) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [map_smul]
    dsimp [P]
    rw [MeasureClass.measProj_ket]
    simp [shorOutputBasis_x_value]

  refine
    Finset.sum_eq_single o ?_ ?_ |>.trans hkeep

  · intro o' ho' hne

    have hval :
        o'.1 ≠ o.1 := by
      intro h
      apply hne
      exact Fin.ext h

    rw [map_sum]

    apply Finset.sum_eq_zero
    intro s hs

    rw [map_smul]
    dsimp [P]
    rw [MeasureClass.measProj_ket]

    have hx :
        RegEncoding.toNat x.active
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0 o'.1 s)
          =
        o'.1 := by
      exact
        RegEncoding.toNat_writeNat_of_lt
          x.active
          o'.1
          (RegEncoding.writeNat y.active
            (inst.a ^ s % inst.N) b0)
          o'.isLt

    simp [hx, hval]

  · intro ho
    exact False.elim (ho (Finset.mem_univ o))

private lemma shorOutputBasis_ne_of_residue_ne
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (o : Fin (ASize x.active))
    {s t : ℕ}
    (hs :
      s < ord inst.a inst.N inst.coprime)
    (ht :
      t < ord inst.a inst.N inst.coprime)
    (hst : s ≠ t)
    (hsetting :
      BasicSetting
        inst.a
        (ord inst.a inst.N inst.coprime)
        inst.N
        (regSize x.active)
        (regSize y.active))
    (hinput :
      IdealOrderFindingInput qs x y b0) :
    shorOutputBasis
        (qs := qs)
        inst.a inst.N x y b0 o.1 s
      ≠
    shorOutputBasis
        (qs := qs)
        inst.a inst.N x y b0 o.1 t := by
  classical

  have howned :
      ExtReg.OwnedDisjoint x y :=
    hinput.2.2

  have hxy :
      Disjoint x.active y.active :=
    active_disjoint_of_ownedDisjoint howned

  rcases hsetting with
    ⟨_ha0, _haN, _hord,
      _hmlo, _hmhi, hNlt, _hnhi⟩

  have hNpos :
      0 < inst.N := by
    omega

  have hNlt' :
      inst.N < ASize y.active := by
    simpa [ASize] using hNlt

  have hslt :
      inst.a ^ s % inst.N < ASize y.active := by
    exact lt_trans
      (Nat.mod_lt _ hNpos)
      hNlt'

  have htlt :
      inst.a ^ t % inst.N < ASize y.active := by
    exact lt_trans
      (Nat.mod_lt _ hNpos)
      hNlt'

  have hread_s :
      RegEncoding.toNat y.active
          (shorOutputBasis
            (qs := qs)
            inst.a inst.N x y b0 o.1 s)
        =
      inst.a ^ s % inst.N := by
    unfold shorOutputBasis

    rw [
      RegEncoding.toNat_left_write_right
        y.active
        x.active
        (Disjoint.symm hxy)
    ]

    exact
      RegEncoding.toNat_writeNat_of_lt
        y.active
        (inst.a ^ s % inst.N)
        b0
        hslt

  have hread_t :
      RegEncoding.toNat y.active
          (shorOutputBasis
            (qs := qs)
            inst.a inst.N x y b0 o.1 t)
        =
      inst.a ^ t % inst.N := by
    unfold shorOutputBasis

    rw [
      RegEncoding.toNat_left_write_right
        y.active
        x.active
        (Disjoint.symm hxy)
    ]

    exact
      RegEncoding.toNat_writeNat_of_lt
        y.active
        (inst.a ^ t % inst.N)
        b0
        htlt

  intro heq

  have hpowers :
      inst.a ^ s % inst.N =
      inst.a ^ t % inst.N := by
    have h :=
      congrArg
        (RegEncoding.toNat y.active)
        heq

    simpa [hread_s, hread_t] using h

  apply hst

  exact
    shor_pow_mod_injective_below_order
      inst hs ht hpowers

omit [RegEncoding QSemantics.Basis] in
private lemma norm_sq_sum_eq_sum_norm_sq_of_orthogonal_shor
    {ι : Type*}
    (S : Finset ι)
    (f : ι → qs.State)
    (horth :
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        inner ℂ (f i) (f j) = 0) :
    ‖∑ i ∈ S, f i‖ ^ 2
      =
    ∑ i ∈ S, ‖f i‖ ^ 2 := by
  classical

  revert horth

  induction S using Finset.induction_on with
  | empty =>
      intro _
      simp

  | insert a S ha ih =>
      intro horth

      have horthS :
          ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
            inner ℂ (f i) (f j) = 0 := by
        intro i hi j hj hij
        exact
          horth
            i (Finset.mem_insert_of_mem hi)
            j (Finset.mem_insert_of_mem hj)
            hij

      have hih :
          ‖∑ i ∈ S, f i‖ ^ 2
            =
          ∑ i ∈ S, ‖f i‖ ^ 2 :=
        ih horthS

      have hcross :
          inner ℂ (f a) (∑ i ∈ S, f i) = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro i hi

        apply
          horth
            a
            (by simp)
            i
            (Finset.mem_insert_of_mem hi)

        intro hai
        subst i
        exact ha hi

      calc
        ‖∑ i ∈ insert a S, f i‖ ^ 2
            =
          ‖f a + ∑ i ∈ S, f i‖ ^ 2 := by
            rw [Finset.sum_insert ha]

        _ =
          ‖f a‖ ^ 2
            +
          2 * Complex.re
            (inner ℂ (f a) (∑ i ∈ S, f i))
            +
          ‖∑ i ∈ S, f i‖ ^ 2 := by
            exact norm_add_sq (𝕜 := ℂ) _ _

        _ =
          ‖f a‖ ^ 2 +
          ‖∑ i ∈ S, f i‖ ^ 2 := by
            rw [hcross]
            simp

        _ =
          ‖f a‖ ^ 2 +
          ∑ i ∈ S, ‖f i‖ ^ 2 := by
            rw [hih]

        _ =
          ∑ i ∈ insert a S, ‖f i‖ ^ 2 := by
            rw [Finset.sum_insert ha]

/--
The data-register states corresponding to distinct `s < r` are
orthogonal, so the squared norm of the period-class superposition is
the sum of the squared coefficient norms.
-/
private lemma norm_sq_shor_period_class_sum
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hsetting :
      BasicSetting
        inst.a
        (ord inst.a inst.N inst.coprime)
        inst.N
        (regSize x.active)
        (regSize y.active))
    (hinput :
      IdealOrderFindingInput qs x y b0)
    (o : Fin (ASize x.active)) :
    ‖ ∑ s ∈ Finset.range (ord inst.a inst.N inst.coprime),
        shorPeriodClassAmplitude
            (ASize x.active)
            (ord inst.a inst.N inst.coprime)
            s o.1 •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0 o.1 s)‖ ^ 2
      =
    shorPaperOutcomeProb
      (ASize x.active)
      (ord inst.a inst.N inst.coprime)
      o.1 := by
  classical

  let r : ℕ :=
    ord inst.a inst.N inst.coprime

  let S : Finset ℕ :=
    Finset.range r

  let α : ℕ → ℂ :=
    fun s =>
      shorPeriodClassAmplitude
        (ASize x.active)
        r s o.1

  let label : ℕ → qs.Basis :=
    fun s =>
      shorOutputBasis
        (qs := qs)
        inst.a inst.N
        x y b0 o.1 s

  have horth :
      ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
        inner ℂ
          (α s • qs.ket (label s))
          (α t • qs.ket (label t))
          =
        0 := by
    intro s hs t ht hst

    have hs' : s < r :=
      Finset.mem_range.mp hs

    have ht' : t < r :=
      Finset.mem_range.mp ht

    have hlabel :
        label s ≠ label t := by
      dsimp [label]
      exact
        shorOutputBasis_ne_of_residue_ne
          (qs := qs)
          inst
          x y b0 o
          (by simpa [r] using hs')
          (by simpa [r] using ht')
          hst
          hsetting
          hinput

    rw [
      inner_smul_left,
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne hlabel
    ]

    simp

  have hpyth :
      ‖∑ s ∈ S,
          α s • qs.ket (label s)‖ ^ 2
        =
      ∑ s ∈ S,
        ‖α s • qs.ket (label s)‖ ^ 2 :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_shor
      S
      (fun s =>
        α s • qs.ket (label s))
      horth

  calc
    ‖
      ∑ s ∈
        Finset.range
          (ord inst.a inst.N inst.coprime),
        shorPeriodClassAmplitude
            (ASize x.active)
            (ord inst.a inst.N inst.coprime)
            s o.1 •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0 o.1 s)
    ‖ ^ 2
        =
      ∑ s ∈ S,
        ‖α s • qs.ket (label s)‖ ^ 2 := by
          simpa [S, α, label, r] using hpyth

    _ =
      ∑ s ∈ S,
        ‖α s‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [norm_smul, ket_norm_one qs]

    _ =
      shorPaperOutcomeProb
        (ASize x.active)
        (ord inst.a inst.N inst.coprime)
        o.1 := by
      simp [
        S,
        α,
        r,
        shorPaperOutcomeProb
      ]

/--
Equations (5.4)--(5.7).

Starting from the explicit periodic state, IQFT followed by measurement
of the exponent register has exactly the period-class probability above.

This proof consists of:
* linearity of IQFT;
* Fourier inversion / conjugated `qftPhase`;
* `a^t mod N = a^s mod N` iff `t ≡ s (mod r)`;
* orthogonality of distinct computational basis states of `y`;
* the computational-basis measurement law.
-/
lemma measProbAfter_orderFindingIdeal_eq_paper_formula
    [GateSemanticsFacts qs]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    [MeasureClass qs]
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hsetting : BasicSetting inst.a (ord inst.a inst.N inst.coprime) inst.N (regSize x.active) (regSize y.active))
    (hinput : IdealOrderFindingInput qs x y b0)
    (hpre : qs.eval ((H_reg x.active) ;; (initY1 y.active) ;; (modExpIdeal' qs inst.a inst.N x.active y.active)) (qs.ket b0)
        =
      idealPreIQFTState qs inst.a inst.N x y b0)
    (o : Fin (ASize x.active)) :
    measProbAfter (qs := qs) qs.eval x.active o.1
        (orderFindingIdeal (qs := qs) inst.a inst.N x y)
        (qs.ket b0)
      =
    shorPaperOutcomeProb
      (ASize x.active)
      (ord inst.a inst.N inst.coprime)
      o.1 := by
  classical

  /-
  First expose the final IQFT.
  -/
  have hcircuit :
      qs.eval
          (orderFindingIdeal
            (qs := qs)
            inst.a inst.N x y)
          (qs.ket b0)
        =
      qs.eval
          (IQFT x)
          (idealPreIQFTState
            qs inst.a inst.N x y b0) := by
    have h :=
      congrArg
        (fun ψ : qs.State =>
          qs.eval (IQFT x) ψ)
        hpre

    simpa [
      orderFindingIdeal,
      qs.eval_seq
    ] using h

  /-
  Regroup the final state by residue class modulo r.
  -/
  have hgroup :
      qs.eval
          (IQFT x)
          (idealPreIQFTState
            qs inst.a inst.N x y b0)
        =
      shorGroupedPostIQFTState
        qs
        inst.a inst.N
        (ASize x.active)
        (ord inst.a inst.N inst.coprime)
        x y b0 :=
    eval_IQFT_idealPreIQFTState_grouped
      inst x y b0
      hsetting hinput

  /-
  The x-measurement projector keeps precisely output `o`.
  -/
  have hproj :
      MeasureClass.measProj
          x.active o.1
          (shorGroupedPostIQFTState
            qs
            inst.a inst.N
            (ASize x.active)
            (ord inst.a inst.N inst.coprime)
            x y b0)
        =
      ∑ s ∈
          Finset.range
            (ord inst.a inst.N inst.coprime),
        shorPeriodClassAmplitude
            (ASize x.active)
            (ord inst.a inst.N inst.coprime)
            s o.1 •
          qs.ket
            (shorOutputBasis
              (qs := qs)
              inst.a inst.N
              x y b0 o.1 s) :=
    measProj_shorGroupedPostIQFTState
      inst x y b0 o

  /-
  Distinct residues give orthogonal y-register states.
  -/
  have hnorm :
      ‖∑ s ∈ Finset.range (ord inst.a inst.N inst.coprime),
          shorPeriodClassAmplitude (ASize x.active) (ord inst.a inst.N inst.coprime) s o.1 •
            qs.ket
              (shorOutputBasis (qs := qs) inst.a inst.N x y b0 o.1 s)‖ ^ 2
        =
      shorPaperOutcomeProb
        (ASize x.active)
        (ord inst.a inst.N inst.coprime)
        o.1 :=
    norm_sq_shor_period_class_sum
      inst x y b0
      hsetting hinput o

  unfold measProbAfter
  rw [MeasureClass.probMeas_born]
  rw [hcircuit, hgroup, hproj]

  exact hnorm

end Shor
