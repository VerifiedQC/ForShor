import FastMultiplication.ShorVerification.Implementation.Shor.Assertions
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.NaiveShor.Math

/-!
# Naive Shor Correctness
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [ContinuedFractionPost]
variable [Spec]


/-! =========================================================
    Small arithmetic facts about `ord`
========================================================= -/





omit [ContinuedFractionPost] [Spec] in
lemma basicSetting_of_shor_instance
    (inst : ShorOrderFindingInstance)
    (m n : ℕ)
    (hm : m = Nat.log2 (2 * inst.N^2))
    (hn : n = Nat.log2 (2 * inst.N)) :
    BasicSetting inst.a (ord inst.a inst.N inst.coprime) inst.N m n := by
  have hN : 0 < inst.N := by
    exact lt_trans inst.range.1 inst.range.2

  have hN2 : 0 < inst.N ^ 2 :=
    pow_pos hN _

  obtain ⟨hm_lo, hm_hi⟩ :=
    pow_log2_two_mul_bounds (inst.N ^ 2) hN2

  obtain ⟨hn_lo, hn_hi⟩ :=
    pow_log2_two_mul_bounds inst.N hN

  subst m
  subst n

  refine ⟨inst.range.1, inst.range.2, ?_,
    hm_lo, hm_hi, hn_lo, hn_hi⟩

  unfold Order
  refine
    ⟨(Nat.coprime_iff_gcd_eq_one).2 inst.coprime, ?_⟩

  rfl

omit [Spec] in
lemma goodOutcome_r_found_one
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    {o Q : ℕ}
    (hgood :
      GoodOutcome o Q
        (ord inst.a inst.N inst.coprime)) :
    r_found T
      (fun d => decide ((inst.a ^ d) % inst.N = 1))
      o Q
      (ord inst.a inst.N inst.coprime) = 1 := by
  classical

  let r : ℕ :=
    ord inst.a inst.N inst.coprime

  let verify : OrderVerifier :=
    fun d => decide ((inst.a ^ d) % inst.N = 1)

  have hgood' : GoodOutcome o Q r := by
    simpa [r] using hgood

  have hrpos : 0 < r := by
    dsimp [r]
    exact ord_pos_of_gcd inst.a inst.N inst.coprime

  have hN : 1 < inst.N := by
    exact
      lt_of_le_of_lt
        (Nat.succ_le_of_lt inst.range.1)
        inst.range.2

  have hrcandidate :
      r ∈ orderCandidates T o Q :=
    GoodOutcome.order_mem_candidates T hT hgood'

  have hrpow :
      (inst.a ^ r) % inst.N = 1 := by
    dsimp [r]
    exact
      pow_ord_mod_eq_one
        inst.a inst.N inst.coprime hN

  have hrverify : verify r = true := by
    simp [verify, hrpow]

  have hrverified :
      r ∈ verifiedOrderCandidates T verify o Q :=
    mem_verifiedOrderCandidates
      T verify hrcandidate hrpos hrverify

  have hleast :
      ∀ d ∈ verifiedOrderCandidates T verify o Q,
        r ≤ d := by
    intro d hd

    rw [verifiedOrderCandidates, Finset.mem_filter] at hd

    have hdpos : 0 < d :=
      hd.2.1

    have hdverify : verify d = true :=
      hd.2.2

    have hdpow :
        (inst.a ^ d) % inst.N = 1 := by
      dsimp [verify] at hdverify
      exact of_decide_eq_true hdverify

    dsimp [r]

    exact
      ord_le_of_pow_mod_eq_one
        inst.a inst.N d
        inst.coprime
        hdpos
        hdpow

  have hpost :
      OF_post T verify o Q = r :=
    OF_post_eq_of_mem_of_least
      T verify hrverified hleast

  change
    (if OF_post T verify o Q = r
     then (1 : ℝ)
     else 0) = 1

  rw [if_pos hpost]

omit [MeasureClass qs] [ContinuedFractionPost] [Spec] in
private lemma toNat_qubitReg
    (q : ℕ)
    (b : qs.Basis) :
    RegEncoding.toNat (qubitReg q) b =
      if RegEncoding.bit q b then 1 else 0 := by
  have hlt :
      RegEncoding.toNat (qubitReg q) b < 2 := by
    simpa [ASize] using
      (RegEncoding.toNat_lt_ASize
        (qubitReg q) b)

  have hbit :
      RegEncoding.bit q b =
        Nat.testBit
          (RegEncoding.toNat (qubitReg q) b) 0 := by
    simpa [qubitReg, Reg.singleton, Reg.get,
      regSize, Reg.width] using
      (RegEncoding.bit_eq_testBit_toNat
        (qubitReg q) b
        (⟨0, by simp⟩ :
          Fin (regSize (qubitReg q))))

  have hv :
      RegEncoding.toNat (qubitReg q) b = 0 ∨
      RegEncoding.toNat (qubitReg q) b = 1 := by
    omega

  rcases hv with hv | hv
  · have hb : RegEncoding.bit q b = false := by
      simpa [hv] using hbit
    simp [hv, hb]

  · have hb : RegEncoding.bit q b = true := by
      simpa [hv] using hbit
    simp [hv, hb]


omit [MeasureClass qs] [ContinuedFractionPost] [Spec] in
private lemma toNat_cons_reg
    (ctrl : ℕ)
    (ctrls : List ℕ)
    (hnd : (ctrl :: ctrls).Nodup)
    (b : qs.Basis) :
    RegEncoding.toNat
        (⟨ctrl :: ctrls, hnd⟩ : Reg) b
      =
    (if RegEncoding.bit ctrl b then 1 else 0) +
      2 *
        RegEncoding.toNat
          (⟨ctrls, (List.nodup_cons.mp hnd).2⟩ : Reg) b := by
  let tail : Reg :=
    ⟨ctrls, (List.nodup_cons.mp hnd).2⟩

  have hnot : ctrl ∉ ctrls :=
    (List.nodup_cons.mp hnd).1

  have hdisj :
      Disjoint (qubitReg ctrl) tail := by
    simp [Disjoint, qubitReg, Reg.singleton, tail, hnot]

  have happ :
      Reg.append (qubitReg ctrl) tail hdisj =
        (⟨ctrl :: ctrls, hnd⟩ : Reg) := by
    rfl

  calc
    RegEncoding.toNat
        (⟨ctrl :: ctrls, hnd⟩ : Reg) b
        =
      RegEncoding.toNat
        (Reg.append (qubitReg ctrl) tail hdisj) b := by
          rw [happ]

    _ =
      RegEncoding.toNat (qubitReg ctrl) b +
        ASize (qubitReg ctrl) *
          RegEncoding.toNat tail b :=
      RegEncoding.toNat_append
        (qubitReg ctrl) tail hdisj b

    _ =
      (if RegEncoding.bit ctrl b then 1 else 0) +
        2 *
          RegEncoding.toNat
            (⟨ctrls,
              (List.nodup_cons.mp hnd).2⟩ : Reg) b := by
      simp [toNat_qubitReg, ASize, tail]


omit [MeasureClass qs] [ContinuedFractionPost] in
private theorem eval_modExpIdealSteps_ket
    [GateSemanticsCore qs]
    [IdealCtrlModMulExactSemantics qs]
    (a N : ℕ)
    (y : Reg)
    (hN : 1 < N)
    (ha : Nat.Coprime a N)
    (hsize : N ≤ ASize y)
    (e : ℕ)
    (ctrls : List ℕ)
    (hctrls : ctrls.Nodup)
    (b : qs.Basis)
    (hdisj :
      Disjoint (⟨ctrls, hctrls⟩ : Reg) y)
    (hy : RegEncoding.toNat y b < N) :
    qs.eval
        (modExpIdealSteps qs a N y e ctrls)
        (qs.ket b)
      =
    qs.ket
      (RegEncoding.writeNat y
        ((RegEncoding.toNat y b *
            a ^
              (2 ^ e *
                RegEncoding.toNat
                  (⟨ctrls, hctrls⟩ : Reg) b)) % N)
        b) := by
  induction ctrls generalizing e b with

  | nil =>
      have hx0 :
          RegEncoding.toNat
            (⟨[], hctrls⟩ : Reg) b = 0 := by
        have hlt :=
          RegEncoding.toNat_lt_ASize
            (⟨[], hctrls⟩ : Reg) b
        have : RegEncoding.toNat
            (⟨[], hctrls⟩ : Reg) b < 1 := by
          simpa [ASize, regSize, Reg.width] using hlt
        omega

      simp [modExpIdealSteps, qs.eval_id, hx0,
        Nat.mod_eq_of_lt hy,
        RegEncoding.writeNat_toNat]

  | cons ctrl ctrls ih =>
      have hnd :=
        List.nodup_cons.mp hctrls

      let tail : Reg :=
        ⟨ctrls, hnd.2⟩

      have hdisj_all :
          ∀ q ∈ ctrl :: ctrls,
            q ∉ y.qubits := by
        simpa [Disjoint, List.disjoint_left] using hdisj

      have hctrl_y :
          ctrl ∉ y.qubits :=
        hdisj_all ctrl (by simp)

      have htail_y :
          Disjoint tail y := by
        rw [Disjoint, List.disjoint_left]
        intro q hq
        exact hdisj_all q (by
          right
          simpa [tail] using hq)

      have hx :
          RegEncoding.toNat
              (⟨ctrl :: ctrls, hctrls⟩ : Reg) b
            =
          (if RegEncoding.bit ctrl b then 1 else 0) +
            2 * RegEncoding.toNat tail b := by
        simpa [tail] using
          (toNat_cons_reg
            (qs := qs)
            ctrl ctrls hctrls b)

      let c : ℕ :=
        (a ^ (2 ^ e)) % N

      have hc :
          Nat.Coprime c N := by
        dsimp [c]
        rw [ZMod.coprime_mod_iff_coprime]
        exact Nat.Coprime.pow_left (2 ^ e) ha

      let y0 : ℕ :=
        RegEncoding.toNat y b

      let v : ℕ :=
        if RegEncoding.bit ctrl b then
          (c * y0) % N
        else
          y0

      let b1 : qs.Basis :=
        RegEncoding.writeNat y v b

      have hhead :
          qs.eval
              (Spec.idealCtrlModMul c N y ctrl)
              (qs.ket b)
            =
          qs.ket b1 := by
        simpa [c, y0, v, b1] using
          (IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact
              (qs := qs)
              c N y ctrl b
              hN hsize hc hctrl_y hy)

      have hNpos : 0 < N := by
        omega

      have hvN : v < N := by
        dsimp [v, y0]
        split
        · exact Nat.mod_lt _ hNpos
        · exact hy

      have hvSize : v < ASize y :=
        lt_of_lt_of_le hvN hsize

      have hy1 :
          RegEncoding.toNat y b1 < N := by
        calc
          RegEncoding.toNat y b1 = v := by
            simpa [b1] using
              (RegEncoding.toNat_writeNat_of_lt
                y v b hvSize)
          _ < N := hvN

      have htail1 :
          RegEncoding.toNat tail b1 =
            RegEncoding.toNat tail b := by
        simpa [b1] using
          (RegEncoding.toNat_left_write_right
            tail y htail_y b v)

      have htail_eval :
          qs.eval
              (modExpIdealSteps
                qs a N y (e + 1) ctrls)
              (qs.ket b1)
            =
          qs.ket
            (RegEncoding.writeNat y
              ((RegEncoding.toNat y b1 *
                  a ^
                    (2 ^ (e + 1) *
                      RegEncoding.toNat tail b1)) % N)
              b1) := by
        exact
          ih
            (hctrls := hnd.2)
            (e := e + 1)
            (b := b1)
            htail_y
            hy1

      rw [modExpIdealSteps, qs.eval_seq, hhead, htail_eval]

      apply congrArg qs.ket

      dsimp [b1]
      rw [RegEncoding.writeNat_overwrite]

      have hyread :
          RegEncoding.toNat y
              (RegEncoding.writeNat y v b) = v :=
        RegEncoding.toNat_writeNat_of_lt
          y v b hvSize

      rw [hyread]

      have htailread :
          RegEncoding.toNat tail
              (RegEncoding.writeNat y v b) =
            RegEncoding.toNat tail b :=
        RegEncoding.toNat_left_write_right
          tail y htail_y b v

      rw [htailread, hx]

      apply congrArg
        (fun n => RegEncoding.writeNat y n b)

      simpa [v, c, y0] using
        (modexp_step_arith
          a N e
          (RegEncoding.toNat y b)
          (RegEncoding.toNat tail b)
          (RegEncoding.bit ctrl b))

/-! =========================================================
    Small probability lemmas
========================================================= -/
omit [ContinuedFractionPost] [Spec] in
/-- Every measurement probability is nonnegative. -/
lemma measProbAfter_nonneg
    {Circuit : Type}
    (evalC : Circuit → qs.State → qs.State)
    (r : Reg)
    (o : ℕ)
    (C : Circuit)
    (ψ : qs.State) :
    0 ≤ measProbAfter (qs := qs) evalC r o C ψ := by
  unfold measProbAfter MeasureClass.probMeas
  positivity

omit [Spec] in
/-- The classical success indicator is always nonnegative. -/
lemma r_found_nonneg
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    (o Q r : ℕ) :
    0 ≤ r_found T verify o Q r := by
  unfold r_found
  split <;> norm_num

omit [Spec] in
lemma goodOutcome_mass_le_probability_of_success
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    {Circuit : Type}
    (evalC : Circuit → qs.State → qs.State)
    (x : Reg)
    (Q : ℕ)
    (C : Circuit)
    (ψ : qs.State) :
    (∑ o : Fin Q,
        goodOutcomeIndicator
          o.1 Q
          (ord inst.a inst.N inst.coprime) *
        measProbAfter (qs := qs) evalC x o.1 C ψ)
      ≤
    probability_of_success
      (qs := qs)
      (T := T)
      (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
      (x := x)
      (r := ord inst.a inst.N inst.coprime)
      (Q := Q)
      (evalC := evalC)
      (C := C)
      (ψ := ψ) := by
  classical
  unfold probability_of_success
  apply Finset.sum_le_sum
  intro o ho

  by_cases hgood :
      GoodOutcome o.1 Q
        (ord inst.a inst.N inst.coprime)

  · have hfound :
        r_found T
          (fun d => decide ((inst.a ^ d) % inst.N = 1))
          o.1 Q
          (ord inst.a inst.N inst.coprime) = 1 :=
      goodOutcome_r_found_one T hT inst hgood

    simp [goodOutcomeIndicator, hgood, hfound]

  · simp only [goodOutcomeIndicator]
    rw [if_neg hgood]
    simp only [zero_mul]

    exact mul_nonneg
      (r_found_nonneg
        T
        (fun d => decide ((inst.a ^ d) % inst.N = 1))
        o.1 Q
        (ord inst.a inst.N inst.coprime))
      (measProbAfter_nonneg evalC x o.1 C ψ)

end Shor
