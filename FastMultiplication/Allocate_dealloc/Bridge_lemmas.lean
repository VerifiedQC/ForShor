import FastMultiplication.Allocate_dealloc.Compiler_correctness
----------------------------------------------------------------------------------------------------
------------------------------- Bridge lemmas: prim-op ⇔ symbolic -----------------------------------
----------------------------------------------------------------------------------------------------

-- LSB alloc simulates symbolic shiftL, and updates delta-len
lemma bridge_allocLSB
  {k : ℕ} (σ : State k) (ctx : StCtx k)
  (vF : ValidFor σ ctx)
  (i : Fin k) (n : Nat) :
  eval_prim_op_single (k := k) (prim_ops.Alloc i true n) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) (State.shiftLReg σ i n) { ctx with curLen := incLen ctx.curLen i n } := by
  have hcurLen:=vF.curLen_len
  cases ctx with
  | mk ρ baseW curLen =>
    -- now hcurLen : curLen.length = k, goal is the old one modulo packaging
    unfold eval_prim_op_single
    simp
    unfold AllocLSB
    funext j
    split_ifs with h1
    ·
      subst h1
      unfold stateToSt
      simp
      constructor
      ·
        rw [add_assoc, incLen_to_sum]
        rw [hcurLen]
      ·
        have hW :
          baseW j + (incLen curLen j n).getD j.val 0 = (baseW j + curLen.getD j.val 0) + n := by
          have hinc := incLen_getD_self (k := k) (curLen := curLen) (n := n) (j := j) hcurLen
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            congrArg (fun t => baseW j + t) hinc

        have hE :
            evalRegister ((σ j).shiftL n) ρ = (evalRegister (σ j) ρ) * (2 : ℤ) ^ n := by
          simpa using evalRegister_shiftL (r := (σ j)) (ρ := ρ) (n := n)

        have :=
          BitVec.ofNat_append_zeros_eqv
            (baseW j + curLen.getD (j.val) 0) n
            (((evalRegister (σ j) ρ).emod (2 ^ (baseW j + curLen[j.val]?.getD 0))).toNat)

        apply HEq.trans this
        rw [hW, hE]
        simp [pow_add]

        have h_mod_rhs :
          2 ^ baseW j * 2 ^ (incLen curLen j n)[j.val]?.getD 0
            =
          2 ^ (baseW j + curLen.getD (j.val) 0) * 2 ^ n := by
          rw [← Nat.pow_add, ← Nat.pow_add]
          aesop

        congr
        set a := (evalRegister (σ j) ρ)
        rw [← incLen_to_sum, pow_add, ← mul_assoc]
        set b := ((2 : ℤ) ^ baseW j * 2 ^ curLen[j.val]?.getD 0)
        norm_cast
        rw [← Int.emod_mul_right, Int.toNat_mul]
        simp
        left
        norm_cast
        apply Int.emod_nonneg
        aesop
        aesop
        aesop
        assumption
    ·
      unfold stateToSt
      simp_all
      constructor
      ·
        unfold incLen setLen
        have := getElem?_setAt_ne curLen (i.val) (j.val) (v := (getLen curLen ↑i + n))
        rw [this]
        subst hcurLen
        simp_all
        simp_all only [ne_eq]
        apply Aesop.BuiltinRules.not_intro
        intro a
        have : j = i := by omega
        contradiction
      ·
        have : (incLen curLen i n).getD (j.val) 0 = curLen.getD (j.val) 0 := by
          unfold incLen setLen
          simp_all
          rw [getElem?_setAt_ne curLen i.val j.val (getLen curLen i.val + n)]
          subst hcurLen
          simp_all
          simp_all only [ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          have : j = i := by omega
          contradiction
        rw [this]
        aesop

-- MSB alloc is sign-extend: symbolic value unchanged, only length delta updates
lemma bridge_allocMSB
  {k : ℕ} (σ : State k) (ctx : StCtx k)
  (hV : ValidFor (k := k) σ ctx)
  (i : Fin k) (n : Nat) :
  eval_prim_op_single (k := k) (prim_ops.Alloc i false n) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ { ctx with curLen := incLen ctx.curLen i n } := by
  cases ctx with
  | mk ρ baseW curLen =>
    have hcurLen : curLen.length = k := by
      simpa using hV.curLen_len
    have hfit_i : FitsSigned (baseW i + curLen.getD i.val 0) (evalRegister (σ i) ρ) := by
      simpa [FitsSignedAt, stWidth] using (hV.fits_all i)

    have ha : 0 < baseW i + curLen.getD i.val 0 := hfit_i.1
    have hb_lo : -(2:ℤ) ^ ((baseW i + curLen.getD i.val 0)-1) ≤ evalRegister (σ i) ρ := hfit_i.2.1
    have hb_hi : evalRegister (σ i) ρ <  (2:ℤ) ^ ((baseW i + curLen.getD i.val 0)-1) := hfit_i.2.2

    unfold eval_prim_op_single
    simp
    unfold AllocMSB
    funext j
    split_ifs with h1
    ·
      subst h1
      unfold stateToSt
      simp
      constructor
      ·
        rw[add_comm, add_assoc,incLen_to_sum]
        exact hcurLen
      ·
        set l := (n + (baseW j + curLen.getD (j.val) 0))
        rw[← incLen_to_sum]
        set a := (baseW j + curLen.getD (j.val) 0)
        conv =>
          lhs
          change BitVec.signExtend l (BitVec.ofNat a ((evalRegister (σ j) ρ).emod (2 ^ a)).toNat)
        set b := (evalRegister (σ j) ρ)
        have hl : baseW j + (incLen curLen j n).getD (↑j) 0 = a + n := by
          have := incLen_to_sum k curLen n j hcurLen
          simp_all [a]
          rw[← this, add_assoc]
        have := BitVec.toInt_signExtend_eq_toNat_bmod (v := l) (w := a)
          ((BitVec.ofNat a (b.emod (2 ^ a)).toNat))
        simp[BitVec.ofNat_emod_eq_ofInt]
        rw[hl]
        simp [l, Nat.add_comm, Nat.add_left_comm]
        have :(incLen ?curLen ?j ?n)[↑j]?.getD 0 = (incLen curLen j n).getD (↑j) 0 := by simp
        rw[← this] at hl
        have hl2 : n + (baseW j + curLen.getD (j.val) 0) = a + n := by
          rw[add_comm, add_assoc]
        rw[hl2]
        simp_all
        have := BitVec.toInt_inj
          (x := BitVec.signExtend (a + n) (BitVec.ofInt a b))
          (y := BitVec.ofNat (a + n) (b.emod (2 ^ (a + n))).toNat).mp
        apply this
        rw[BitVec.toInt_signExtend]
        simp
        have := BitVec.toInt_ofNat' (n := a + n) (b.emod (2 ^ (a + n))).toNat
        simp[this]
        have := Int.emod_nonneg b (b := (2 ^ (a + n))) (by simp)
        have : max (b.emod (2 ^ (a + n))) 0 = (b.emod (2 ^ (a + n))) := by
          simp
          exact this
        rw[this]
        have := Int.emod_bmod b ((2) ^ (a + n))
        have h2 :
          (b.emod (2 ^ (a + n))).bmod (2 ^ (a + n))
            =
          (b % (((2 ^ (a + n)):ℕ):ℕ)).bmod (2 ^ (a + n)) := by
          simp_all [a, l, b]
          exact this
        rw[h2, this]
        simp_all only
        have hbmod_a : b.bmod (2^a) = b := by
          have h1 : (BitVec.ofInt a b).toInt = b :=
            BitVec.toInt_ofInt_eq_self (w := a) ha hb_lo hb_hi
          have h2 : (BitVec.ofInt a b).toInt = b.bmod (2^a) := by aesop
          exact by aesop
        have hbmod_an : b.bmod (2^(a+n)) = b := by
          have ha' : 0 < a + n := by
            exact lt_of_lt_of_le ha (Nat.le_add_right a n)
          have h_exp : a - 1 ≤ a + n - 1 := by
            omega
          have hpow : (2 : ℤ) ^ (a - 1) ≤ (2 : ℤ) ^ (a + n - 1) := by
            have := Nat.pow_le_pow_right (n := (2)) (by simp) (i := a-1) (j := a+n-1) h_exp
            norm_cast
          clear hl hl2 h2 this
          repeat clear this
          have hb_hi' : b < (2 : ℤ) ^ (a + n - 1) := by
            exact lt_of_lt_of_le hb_hi hpow
          have hb_lo' : -(2 : ℤ) ^ (a + n - 1) ≤ b := by
            have hneg : -(2 : ℤ) ^ (a + n - 1) ≤ -(2 : ℤ) ^ (a - 1) := by
              exact neg_le_neg hpow
            exact le_trans hneg hb_lo
          have h_toInt : (BitVec.ofInt (a + n) b).toInt = b :=
            BitVec.toInt_ofInt_eq_self (w := a + n) ha' hb_lo' hb_hi'
          have h_bmod : (BitVec.ofInt (a + n) b).toInt = b.bmod (2 ^ (a + n)) := by
            aesop
          aesop
        simp[hbmod_a, hbmod_an]
        exact hcurLen
    ·
      unfold stateToSt
      simp_all
      constructor
      ·
        unfold incLen setLen
        rw[getElem?_setAt_ne]
        subst hcurLen
        simp_all
        simp_all only [ne_eq]
        apply Aesop.BuiltinRules.not_intro
        intro a
        have: j=i := by omega
        contradiction
      ·
        have:(incLen curLen i n).getD (j.val) 0 = curLen.getD (j.val) 0 := by
          unfold incLen setLen
          simp_all
          rw[getElem?_setAt_ne curLen i.val j.val (getLen curLen i.val + n)]
          subst hcurLen
          simp_all
          simp_all only [ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          have: j=i := by omega
          contradiction
        rw[this]
        aesop

-- Negate
lemma bridge_negate
  {k : ℕ} (σ : State k) (ctx : StCtx k)
  (hV : ValidFor (k := k) σ ctx)
  (i : Fin k) :
  eval_prim_op_single (k := k) (prim_ops.negate i) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) (State.negateReg σ i) ctx := by
  cases ctx with
  | mk ρ baseW curLen =>
    unfold eval_prim_op_single
    simp
    unfold Negation
    funext j
    split_ifs with h1
    ·
      unfold stateToSt
      subst h1
      simp_all
      set a := (baseW j + curLen.getD (j.val) 0)
      unfold Register.negate evalRegister
      have h_sum :
          (∑ j_1, (fun j_2 => -σ j j_2) j_1 * ρ j_1) = -(∑ j_1, σ j j_1 * ρ j_1) := by
        simp only [neg_mul, Finset.sum_neg_distrib]
      rw[h_sum]
      set S := ∑ j_1, σ j j_1 * ρ j_1
      have h_ofInt_lhs : BitVec.ofNat a (S.emod (2 ^ a)).toNat = BitVec.ofInt a S := by
        simp [BitVec.ofInt]
        conv =>
          lhs
          change BitVec.ofNat a (S % (2 ^ a)).toNat
        rw[BitVec.ofNatLT_eq_ofNat]
      have h_ofInt_rhs : BitVec.ofNat a ((-S).emod (2 ^ a)).toNat = BitVec.ofInt a (-S) := by
        simp [BitVec.ofInt]
        conv =>
          lhs
          change BitVec.ofNat a ((-S) % (2 ^ a)).toNat
        rw[BitVec.ofNatLT_eq_ofNat]
      change -BitVec.ofNat a (S.emod (2 ^ (a))).toNat = BitVec.ofNat a ((-S).emod (2 ^ (a))).toNat
      rw [h_ofInt_lhs, h_ofInt_rhs]
      rw[BitVec.ofInt_neg]
    ·
      unfold stateToSt
      simp_all



@[simp]lemma max_emod_zero(a n:ℤ) (hn:n≠0):
max (a.emod n) 0 = a.emod n:= by {
  simp
  apply Int.emod_nonneg
  simp[hn]
}
-- Add / Free bridges (stubs kept as-is)

lemma bridge_add
  {k : ℕ} (σ : State k) (ctx : StCtx k)
  (dst src : Fin k)
  (hV : ValidFor (k := k) σ ctx)
  (hW : stWidth ctx dst ≤ stWidth ctx src)
  :
  eval_prim_op_single (k := k) (prim_ops.Add dst src) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) (State.addScaledReg σ dst src false 0) ctx := by
  have hcurLen: ctx.curLen.length=k:=by simpa using hV.curLen_len
  cases ctx with
  | mk ρ baseW curLen =>
    unfold eval_prim_op_single
    simp
    unfold Adder
    funext j
    split_ifs with h1
    ·
      subst h1
      unfold stateToSt
      simp
      --rw [List.getD_eq_getElem?_getD]
      set wj : Nat := baseW j + curLen.getD (↑j) 0
      set ws : Nat := baseW src + curLen.getD (↑src) 0
      have heval_add :
      evalRegister ((σ j).addScaled (σ src) false 0) ρ
        = evalRegister (σ j) ρ + evalRegister (σ src) ρ := by
        unfold Register.addScaled evalRegister
        simp [pow_zero, Finset.sum_add_distrib, mul_add, add_comm, mul_comm]
      simp [heval_add]
      apply (BitVec.toNat_inj).1
      simp [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
            Nat.add_mod]
      repeat' (simp)
      have hpowj_pos : (0 : ℤ) < (2 : ℤ) ^ (baseW j + curLen[↑j]?.getD 0) := by
        exact pow_pos (by decide : (0 : ℤ) < 2) _
      have hpowj_lt :
          (evalRegister (σ j) ρ).emod (2 ^ (baseW j + curLen[↑j]?.getD 0)) <
            (2 : ℤ) ^ (baseW j + curLen[↑j]?.getD 0) := by
        -- emod_lt_of_pos
        simpa using Int.emod_lt_of_pos (evalRegister (σ j) ρ) hpowj_pos

      have hpowsrc_pos : (0 : ℤ) < (2 : ℤ) ^ (baseW src + curLen[↑src]?.getD 0) := by
        exact pow_pos (by decide : (0 : ℤ) < 2) _
      have hpowsrc_lt :
          (evalRegister (σ src) ρ).emod (2 ^ (baseW src + curLen[↑src]?.getD 0)) <
            (2 : ℤ) ^ (baseW src + curLen[↑src]?.getD 0) := by
        simpa using Int.emod_lt_of_pos (evalRegister (σ src) ρ) hpowsrc_pos
      have hj_toNat_lt :
      ((evalRegister (σ j) ρ).emod (2 ^ (baseW j + curLen[↑j]?.getD 0))).toNat <
        2 ^ (baseW j + curLen[↑j]?.getD 0) := by
        -- `toNat_lt` + coercions
        rw[Int.toNat_lt]
        aesop
        apply Int.emod_nonneg
        simp


      have hsrc_toNat_lt :
          ((evalRegister (σ src) ρ).emod (2 ^ (baseW src + curLen[↑src]?.getD 0))).toNat <
            2 ^ (baseW src + curLen[↑src]?.getD 0) := by
        rw[Int.toNat_lt]
        aesop
        apply Int.emod_nonneg
        simp

      have hj_drop :
          ((evalRegister (σ j) ρ).emod (2 ^ (baseW j + curLen[↑j]?.getD 0))).toNat %
            2 ^ (baseW j + curLen[↑j]?.getD 0)
          =
          ((evalRegister (σ j) ρ).emod (2 ^ (baseW j + curLen[↑j]?.getD 0))).toNat := by
        exact Nat.mod_eq_of_lt hj_toNat_lt

      have hsrc_drop :
          ((evalRegister (σ src) ρ).emod (2 ^ (baseW src + curLen[↑src]?.getD 0))).toNat %
            2 ^ (baseW src + curLen[↑src]?.getD 0)
          =
          ((evalRegister (σ src) ρ).emod (2 ^ (baseW src + curLen[↑src]?.getD 0))).toNat := by
        exact Nat.mod_eq_of_lt hsrc_toNat_lt
      unfold ws
      conv_lhs=>
        arg 1
        arg 2
        change ((evalRegister (σ src) ρ).emod (2 ^ (baseW src + curLen[src]?.getD 0))).toNat % 2 ^ (baseW src + curLen[src]?.getD 0)
      rw[hsrc_drop]
      have h_rhs_lt : ((evalRegister (σ j) ρ + evalRegister (σ src) ρ).emod (2 ^ wj)).toNat < 2 ^ wj := by
        rw[Int.toNat_lt]
        simp
        have:=Int.emod_lt (a:=(evalRegister (σ j) ρ + evalRegister (σ src) ρ)) (b:=2^wj) (by simp)
        have h1:((2:ℤ) ^ wj).natAbs=((2:ℤ)^wj):= by norm_cast
        rw[h1] at this
        change (evalRegister (σ j) ρ + evalRegister (σ src) ρ) % (2 ^ wj) < 2 ^ wj
        apply this
        apply Int.emod_nonneg
        simp
      nth_rewrite 2 [Nat.mod_eq_of_lt]
      apply Int.ofNat_inj.mp
      push_cast
      rw [Int.toNat_of_nonneg]
      rw [Int.add_emod]
      set a:=(evalRegister (σ j) ρ)
      set b:=(evalRegister (σ src) ρ)
      set n:=(baseW j + curLen[j.val]?.getD 0)
      set m:=(baseW src + curLen[src]?.getD 0)
      have h_nwj : n = wj := by rfl
      simp[h_nwj] at *
      have h_b_nonneg : 0 ≤ b.emod (2 ^ m) := Int.emod_nonneg _ (by positivity)
      have h_ab_nonneg : 0 ≤ (a + b).emod (2 ^ wj) := Int.emod_nonneg _ (by positivity)
      change _ = (a+b) % (2^wj)
      rw[Int.add_emod]
      set N : ℤ := (2 : ℤ) ^ wj
      set M : ℤ := (2 : ℤ) ^ m
      have hN0 : N ≠ 0 := by
        subst N; exact pow_ne_zero _ (by decide : (2 : ℤ) ≠ 0)

      have hwm:(wj≤m):= by unfold stWidth at hW;simp at hW; unfold wj m; apply hW
      -- 2^wj ∣ 2^m
      have hdiv : N ∣ M := by
        subst N; subst M
        refine ⟨(2 : ℤ) ^ (m - wj), ?_⟩
        have hm : wj + (m - wj) = m := Nat.add_sub_of_le hwm
        calc
          (2 : ℤ) ^ m
              = (2 : ℤ) ^ (wj + (m - wj)) := by simp[hm]
          _   = (2 : ℤ) ^ wj * (2 : ℤ) ^ (m - wj) := by simp [pow_add]
      change (a % N % N + b % M % N) % N = (a + b) % N
      rw[Int.emod_emod_of_dvd, Int.emod_emod_of_dvd,← Int.add_emod]
      apply hdiv
      simp
      apply Int.emod_nonneg
      simp
      apply h_rhs_lt
    · unfold stateToSt
      simp_all


lemma bridge_freeLSB
  {k : ℕ} (σ σ' : State k) (ctx : StCtx k)
  (i : Fin k) (n : Nat)
  (hn : n ≤ ctx.curLen.getD i.1 0)
  (h : State.shiftRReg? σ i n = some σ')
  (hV : ValidFor (k := k) σ ctx)

  :
  eval_prim_op_single (k := k) (prim_ops.Free i true n) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ' { ctx with curLen := decLen ctx.curLen i n } := by
  have hcurLen: ctx.curLen.length=k:=by simpa using hV.curLen_len
  cases ctx with
  | mk ρ baseW curLen =>
    unfold eval_prim_op_single
    simp
    unfold FreeLSB
    funext j
    split_ifs with h1
    ·
      subst h1
      unfold stateToSt
      simp
      constructor
      {
        rw[add_comm, add_comm, Nat.add_sub_assoc,decLen_to_diff]
        simpa using hV.curLen_len
        aesop
      }
      {
        rw[← decLen_to_diff,← Nat.add_sub_assoc]
        set a:=(baseW j + curLen[j.val]?.getD 0)
        have:(decLen curLen j n).getD (j.val) 0= curLen.getD (j.val) 0 - n:= by
          simp
          rw[decLen_to_diff]
          simp[hcurLen]
        rw[this]
        rw[← Nat.add_sub_assoc]
        set b:=baseW j + curLen.getD (j.val) 0 - n
        {
          have h1:=evalRegister_setReg_div_pow2 σ σ' ρ j n h
          rw[h1]
          set c:=(evalRegister (σ j) ρ)
          congr
          have h_emod_range : (c.emod (2 ^ a)).toNat < 2 ^ a := by
            simp
            have:=Int.emod_lt ((c)) (b:=2^a) (by simp)
            aesop
          rw [Nat.mod_eq_of_lt h_emod_range]
          have h_exp : (2:ℤ) ^ a = 2 ^ n * 2 ^ (a - n) := by
            rw [← pow_add, Nat.add_sub_cancel']
            unfold a
            simp at hn;linarith
          rw[h_exp]
          change (c % (2 ^ n * 2 ^ (a - n))).toNat / (2) ^ n = ((c / 2 ^ n) % (2 ^ (a - n))).toNat
          --rw[Int.toNat_emod, Int.toNat_emod, Int.toNat_mul]
          have h1:2^n=((2:ℤ) ^ n).toNat:= by norm_cast
          rw[h1]
          set N : ℤ := (2 : ℤ) ^ n
          set K : ℤ := (2 : ℤ) ^ (a - n)
          set M : ℤ := N * K

          have hNpos : 0 < N := by
            unfold N; simp
          have hKpos : 0 < K := by
            unfold K; simp
          have hMpos : 0 < M := by
            simpa [M] using mul_pos hNpos hKpos

          have hN0 : N ≠ 0 := ne_of_gt hNpos
          have hK0 : K ≠ 0 := ne_of_gt hKpos

          set r : ℤ := c % M
          set q : ℤ := c / M

          have h_decomp : r + M * q = c := by
            simpa [r, q] using (Int.emod_add_mul_ediv c M)

          have hr_nonneg : 0 ≤ r := by
            simpa [r] using Int.emod_nonneg c (ne_of_gt hMpos)
          have hr_lt : r < M := by
            simpa [r] using Int.emod_lt_of_pos c hMpos

          -- N divides M*q (since M = N*K)
          have hNdvd : N ∣ M * q := by
            refine ⟨K * q, ?_⟩
            simp [M, mul_assoc]

          -- Divide the decomposition by N; since N ∣ M*q, division distributes
          have h_div_by_N : c / N = r / N + K * q := by
            calc
              c / N = (r + M * q) / N := by simp[h_decomp]
              _ = r / N + (M * q) / N := by
                    simpa using (Int.add_ediv_of_dvd_right (a := r) (b := M*q) (c := N) hNdvd)
              _ = r / N + K * q := by
                    -- (M*q)/N = (N*(K*q))/N = K*q
                    have : (M * q) / N = K * q := by
                      calc
                        (M * q) / N = (N * (K * q)) / N := by
                          simp [M, mul_assoc]
                        _ = K * q := by
                          simpa using (Int.mul_ediv_cancel_left (a := N) (b := K*q) hN0)
                    simp[this]

          have h_rem : (c / N) % K = r / N := by
            have hrN_nonneg : 0 ≤ r / N := by
              -- ediv_nonneg_iff_of_pos : 0 ≤ r / N ↔ 0 ≤ r when N>0
              have := (Int.ediv_nonneg_iff_of_pos (a := r) (b := N) hNpos)
              exact this.mpr hr_nonneg

            have hrN_lt_absK : r / N < |K| := by
              -- From r < N*K = M, we get r/N < K (since N>0). Then |K| = K.
              have hrN_ltK : r / N < K := by
                -- rewrite hr_lt : r < N*K but in the order needed for ediv_lt_of_lt_mul
                have hr_lt' : r < K * N := by
                  simpa [M, mul_assoc, mul_left_comm, mul_comm] using hr_lt
                -- standard lemma: if 0 < N and r < K*N then r/N < K
                exact Int.ediv_lt_of_lt_mul hNpos hr_lt'
              simpa [abs_of_pos hKpos] using hrN_ltK

            have hx :
                (c / N) / K = q ∧ (c / N) % K = r / N := by
              constructor
              rw [h_div_by_N]
              rw [Int.add_mul_ediv_left _ _ hK0]
              have : r / N / K = 0 := by
                apply Int.ediv_eq_zero_of_lt hrN_nonneg
                rwa [abs_of_pos hKpos] at hrN_lt_absK
              rw [this, Int.zero_add]
              rw [h_div_by_N]
              rw [Int.add_mul_emod_self_left]
              apply Int.emod_eq_of_lt hrN_nonneg
              rwa [abs_of_pos hKpos] at hrN_lt_absK
            exact hx.2

          have h_toNat_div : r.toNat / N.toNat = (r / N).toNat := by
            have hrN_nonneg : 0 ≤ r / N := by
              have := (Int.ediv_nonneg_iff_of_pos (a := r) (b := N) hNpos)
              exact this.mpr hr_nonneg
            have hcoe : ((r.toNat / N.toNat : Nat) : ℤ) = r / N := by
              have hr_cast : (r.toNat : ℤ) = r := by
                simp [Int.toNat_of_nonneg hr_nonneg]
              have hN_cast : (N.toNat : ℤ) = N := by
                simp[Int.toNat_of_nonneg (le_of_lt hNpos)]
              simp[hr_cast, hN_cast]
            have := congrArg Int.toNat hcoe
            have h1:=Int.toNat_of_nonneg hrN_nonneg

            have h2:(0:ℤ)≤ r.toNat / N.toNat:=by simp_all
            have h3:=Int.toNat_of_nonneg h2
            rw[← this]
            norm_cast at h3
          calc
            (c % (2 ^ n * 2 ^ (a - n))).toNat / ((2:ℤ) ^ n).toNat
                = r.toNat / N.toNat := by
                    simp [r, N, K, M]
            _   = (r / N).toNat := by simp [h_toNat_div]
            _   = ((c / N) % K).toNat := by simp[h_rem]
            _   = (c / 2 ^ n % 2 ^ (a - n)).toNat := by
                    simp [N, K]

        }
        assumption
        assumption
        assumption
      }

    ·
      unfold stateToSt
      simp_all
      constructor
      ·
        unfold decLen setLen
        rw[getElem?_setAt_ne]
        subst hcurLen
        simp_all
        simp_all only [ne_eq]
        apply Aesop.BuiltinRules.not_intro
        intro a
        have: j=i := by omega
        contradiction
      ·
        have:(decLen curLen i n).getD (j.val) 0 = curLen.getD (j.val) 0 := by
          unfold decLen setLen
          simp_all
          rw[getElem?_setAt_ne curLen i.val j.val (getLen curLen i.val - n)]
          simp_all
          simp_all only [ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          have: j=i := by omega
          contradiction
        rw[this]
        unfold State.shiftRReg? at h
        cases hR : Register.shiftR? (σ i) n with
        | none =>
            simp [hR] at h
        | some r' =>
            have hσ' : σ' = State.setReg σ i r' := by
              exact (Option.some.inj (by simpa [hR] using h)).symm
            have hreg : σ' j = σ j := by
              subst hσ'
              unfold State.setReg
              have : (j = i) = False := by
                exact propext ⟨(fun hj => False.elim (h1 hj)), (fun hf => False.elim hf)⟩
              simp [h1]
            have hlenj :
              (decLen curLen i n)[↑j]?.getD 0 = curLen.getD (↑j) 0 := by
                unfold decLen setLen
                simp_all
                rw[getElem?_setAt_ne curLen i.val j.val (getLen curLen i.val - n)]
                simp[hcurLen]
                simp_all
                intro a
                have: j=i := by omega
                contradiction
            simp [hreg]
            congr
            unfold decLen setLen
            simp_all
            rw[getElem?_setAt_ne]
            aesop
            intro a
            have: j=i := by omega
            contradiction


lemma ofNat_emod_pow2_lowbits_eq
  (b a1 a2 : ℕ) (c : ℤ)
  (hb1 : b ≤ a1) (hb2 : b ≤ a2) :
  BitVec.ofNat b (c.emod (2 ^ a1)).toNat ≍
    BitVec.ofNat b (c.emod (2 ^ a2)).toNat := by
  have:= heq_eq_eq (a:=BitVec.ofNat b (c.emod (2 ^ a1)).toNat) (b:=BitVec.ofNat b (c.emod (2 ^ a2)).toNat)
  rw[this]
  apply BitVec.eq_of_toNat_eq
  simp_all
  have h_mod (a : ℕ) (hba : b ≤ a) : (c.emod (2 ^ a)).toNat % 2 ^ b = (c.emod (2 ^ b)).toNat := by
    have h1 : 2 ^ b = Int.toNat ((2:ℤ)^b):= by norm_cast

    rw[h1,← Int.toNat_emod]
    ·
      change (c % (2 ^ a) % 2 ^ b).toNat = (c.emod (2 ^ b)).toNat
      rw [Int.emod_emod_of_dvd]
      aesop
      refine ⟨2 ^ (a - b), ?_⟩
      -- show: 2^a = 2^b * 2^(a-b)
      have hab : b + (a - b) = a := Nat.add_sub_of_le hba
      calc
        (2:ℤ) ^ a
            = 2 ^ (b + (a - b)) := by simp[hab]
        _   = 2 ^ b * 2 ^ (a - b) := by simp[pow_add]
    ·
      apply Int.emod_nonneg
      simp
    · simp
  rw[h_mod a1 hb1, h_mod a2 hb2]

lemma bridge_freeMSB
  {k : ℕ} (σ : State k) (ctx : StCtx k)
  (i : Fin k) (n : Nat)
  (hn : n ≤ ctx.curLen.getD i.1 0)
  (hV : ValidFor (k := k) σ ctx)
  :
  eval_prim_op_single (k := k) (prim_ops.Free i false n) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ { ctx with curLen := decLen ctx.curLen i n } := by
  have hcurLen: ctx.curLen.length=k:=by simpa using hV.curLen_len
  cases ctx with
  | mk ρ baseW curLen =>
    unfold eval_prim_op_single
    simp
    unfold FreeMSB
    funext j
    split_ifs with h1
    ·
      subst h1
      unfold stateToSt
      simp
      constructor
      {
        rw[add_comm, add_comm, Nat.add_sub_assoc,decLen_to_diff]
        simpa using hV.curLen_len
        aesop
      }
      {
        rw[← decLen_to_diff,← Nat.add_sub_assoc]
        set a:=(baseW j + curLen[j.val]?.getD 0)
        have:(decLen curLen j n).getD (j.val) 0= curLen.getD (j.val) 0 - n:= by
          simp
          rw[decLen_to_diff]
          simp[hcurLen]
        rw[this]
        rw[← Nat.add_sub_assoc]
        set b:=baseW j + curLen.getD (j.val) 0 - n
        {
          apply ofNat_emod_pow2_lowbits_eq
          aesop
          aesop
        }
        assumption
        assumption
        assumption
      }

    ·
      unfold stateToSt
      simp_all
      constructor
      ·
        unfold decLen setLen
        rw[getElem?_setAt_ne]
        subst hcurLen
        simp_all
        intro a
        have: j=i := by omega
        contradiction
      ·
        have:(decLen curLen i n).getD (j.val) 0 = curLen.getD (j.val) 0 := by
          unfold decLen setLen
          simp_all
          rw[getElem?_setAt_ne curLen i.val j.val (getLen curLen i.val - n)]
          simp_all
          simp_all only [ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          have: j=i := by omega
          contradiction
        rw[this]
        aesop

open Operations

lemma add_Scaled_compile_curLen(dst src:Fin k) (hds:¬dst=src)(curLen:List ℕ):
(compile1 (valid_ops.addScaled dst src false 0) curLen).2 = incLen curLen dst (1 + (getLen curLen ↑dst).max (getLen curLen ↑src) - getLen curLen ↑dst):=by
  unfold compile1 compile_op_to_prim_single
  simp[hds]

lemma shiftL_compile_curLen(src: Fin k) (curLen: List ℕ):
  (compile1 (valid_ops.shiftL src sh) curLen).2 = incLen curLen src sh:=by {
    simp[compile1,compile_op_to_prim_single]
  }
----------------------------------------------------------------------------------------------------
------------------------------- Compiler simulation theorems ----------------------------------------
----------------------------------------------------------------------------------------------------

lemma negate_add_negate_eq_addScaled_true0
  {k : ℕ} (σ : State k) (dst src : Fin k) (hds:dst≠src):
  State.negateReg (State.addScaledReg (State.negateReg σ src) dst src false 0) src
    =
  State.addScaledReg σ dst src true 0 := by
  ext i j
  by_cases hid : i = dst
  · rw[hid]
    aesop
  · by_cases his : i = src
    · subst his
      simp [State.negateReg, State.addScaledReg, State.setReg, hid]
    ·
      simp [State.negateReg, State.addScaledReg, State.setReg, hid, his]

open Operations

lemma le_one_add_max
  (a b : Nat) : a ≤ 1 + Nat.max a b := by
  -- a ≤ max a b
  have h : a ≤ Nat.max a b := Nat.le_max_left a b
  -- max a b ≤ 1 + max a b
  have h' : Nat.max a b ≤ 1 + Nat.max a b := by
    simp[Nat.le_succ _]
  exact le_trans h h'





lemma bridge_compile1_addScaled
  {k : ℕ}
  (σ σ2 : State k)
  (ctx : StCtx k)
  (dst src : Fin k)
  (hds: ¬ dst=src)
  (sh : ℕ)
  (hsh:¬ sh=0)
  (hV : ValidFor (k := k) σ ctx)
  (hV_step : ValidForStep (k := k) ctx)
  (hstep : applyOp? σ (valid_ops.addScaled dst src true sh) = some σ2)
  :
  eval_prim_ops
      (compile1 (valid_ops.addScaled dst src true sh) ctx.curLen).1
      (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ2
    { ρ := ctx.ρ, baseW := ctx.baseW,
      curLen := (compile1 (valid_ops.addScaled dst src true sh) ctx.curLen).2 } := by
      unfold compile1 compile_op_to_prim_single
      simp[hds,hsh]
      simp[eval_prim_ops]
      set a:=1 + (getLen (incLen ctx.curLen src sh) ↑dst).max (getLen (incLen ctx.curLen src sh) ↑src)
      split_ifs with h1 h2 h3<;>simp
      {
        set lenDst : Nat := getLen (incLen ctx.curLen src sh) (↑dst) with hlenDst
        set lenSrc : Nat := getLen (incLen ctx.curLen src sh) (↑src) with hlenSrc

        have ha_le : a ≤ lenDst := by
          exact (Nat.sub_eq_zero_iff_le).1 (by simpa [lenDst] using h1)
        have hlenDst_lt : lenDst < a := by
          have hle : lenDst ≤ Nat.max lenDst lenSrc := Nat.le_max_left _ _
          have:=(Nat.lt_succ_of_le hle)
          simp [lenDst, lenSrc, Nat.succ_eq_add_one] at this
          unfold lenDst a
          linarith
        have : False := (Nat.not_lt_of_ge ha_le) hlenDst_lt
        exact False.elim this
      }
      {
        set ld : Nat := getLen (incLen ctx.curLen src sh) ↑dst
        set ls : Nat := getLen (incLen ctx.curLen src sh) ↑src

        have ld_lt_a : ld < a := by
          have hle : ld + 1 ≤ a := by
            have : ld ≤ Nat.max ld ls := Nat.le_max_left _ _
            have : ld + 1 ≤ Nat.max ld ls + 1 := Nat.succ_le_succ this
            unfold a ld
            linarith
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self ld) hle
        have a_le_ld : a ≤ ld := by
          exact (Nat.sub_eq_zero_iff_le).1 (by simpa [ld] using h1)
        have : False := (Nat.not_le_of_lt ld_lt_a) a_le_ld
        exact False.elim this
      }
      {
        exfalso
        set lenSrc : Nat := getLen (incLen ctx.curLen src sh) (↑src) with hlenSrc
        have h_le_max : lenSrc ≤ (getLen ctx.curLen (↑dst)).max lenSrc := by
          aesop
        have h_succ_le_a : lenSrc.succ ≤ a := by
          dsimp [a];nth_rewrite 2 [add_comm]
          have:=Nat.succ_le_succ h_le_max
          simp_all
        have h_a_le_lenSrc : a ≤ lenSrc := by
          have : a - lenSrc = 0 := by simpa [lenSrc, hlenSrc] using h3
          exact (Nat.sub_eq_zero_iff_le).1 this
        have : lenSrc.succ ≤ lenSrc := le_trans h_succ_le_a h_a_le_lenSrc
        exact Nat.not_succ_le_self lenSrc this
      }
      {
        simp[eval_prim_ops]
        have hV4:ValidFor (σ.negateReg src) ctx:=by
            unfold ValidForStep at *
            have:= hV_step σ (σ.negateReg src) (valid_ops.negate src) ctx.curLen
            simp[applyOp?,Prog.OpOK] at this
            apply this
            apply hV
        have hV5:ValidFor ((σ.negateReg src).shiftLReg src sh) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen src sh }:=by
          have:= hV_step ((σ.negateReg src)) (((σ.negateReg src).shiftLReg src sh)) (valid_ops.shiftL src sh) (ctx.curLen) (by simp[applyOp?]) (by simp[Prog.OpOK]) hV4
          simp at this; rw[shiftL_compile_curLen] at this; apply this
        have hV6:ValidFor ((σ.negateReg src).shiftLReg src sh) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst) }:=by
          have:=ValidFor_incLen dst (n:=(a - getLen (incLen ctx.curLen src sh) ↑dst)) ((σ.negateReg src).shiftLReg src sh) ({ ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen src sh })
          simp_all
        have hV2:ValidFor ((σ.negateReg src).shiftLReg src sh) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst)) src (a - getLen (incLen ctx.curLen src sh) ↑src) }:= by
          have:=ValidFor_incLen src (n:=(a - getLen (incLen ctx.curLen src sh) ↑src)) ((σ.negateReg src).shiftLReg src sh) ({ ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst) })
          simp_all
        have hV3:ValidFor (((σ.negateReg src).shiftLReg src sh).addScaledReg dst src false 0) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst)) src (a - getLen (incLen ctx.curLen src sh) ↑src) }:= by {
          have:= hV_step ((σ.negateReg src).shiftLReg src sh) (((σ.negateReg src).shiftLReg src sh).addScaledReg dst src false 0) (valid_ops.addScaled dst src false 0) (incLen ctx.curLen src sh)
          have:= this (by simp) (by simp[Prog.OpOK,hds]) (hV5)
          simp_all
          simp[compile1,compile_op_to_prim_single,hds] at this;set c:=(incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst))
          have hinc:= ValidFor_incLen src (((σ.negateReg src).shiftLReg src sh).addScaledReg dst src false 0) (n:=(a - getLen (incLen ctx.curLen src sh) ↑src)) ({ ρ := ctx.ρ, baseW := ctx.baseW, curLen := c }) this
          simp_all
        }

        have hW:stWidth { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst)) src (a - getLen (incLen ctx.curLen src sh) ↑src) } dst = stWidth { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst)) src (a - getLen (incLen ctx.curLen src sh) ↑src) } src:=by {
          unfold stWidth;simp
          rw[incLen_comm, incLen_incLen_add, ← incLen_to_sum];unfold getLen
          set l1:=(incLen ctx.curLen src sh);set b:=a - l1.getD (↑src) 0; set c:= a - l1.getD (↑dst) 0
          conv_rhs=>
            arg 2
            change (incLen (incLen ctx.curLen src (sh + b)) dst c).getD src 0
          rw[incLen_getD_ne'];unfold c l1;rw[incLen_getD_ne'];simp;

          have h1:((incLen ctx.curLen src (sh + b))[dst.val]?.getD 0 + (a - (incLen ctx.curLen src sh).getD (↑dst) 0))=a:=by {
            rw[add_comm,incLen_getD_ne'];unfold a getLen;simp;simp[← List.getD_eq_getElem?_getD];
            nth_rewrite 1 [incLen_getD_ne'];nth_rewrite 2 [incLen_getD_ne'];nth_rewrite 2 [incLen_getD_ne'];all_goals try assumption
            rw[incLen_getD_self];rw[Nat.sub_add_cancel];
            rw[← Nat.succ_eq_one_add]
            apply le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
            all_goals apply hV.curLen_len
          }
          rw[incLen_getD_ne'] at h1;simp at h1;rw[h1];rw[← List.getD_eq_getElem?_getD,incLen_getD_self];unfold b l1;rw[incLen_getD_self]
          simp
          nth_rewrite 4 [add_comm];rw[hV.baseW_eq (i:=dst) (j:=src)];simp;set s : Nat := ctx.curLen[src.val]?.getD 0
          symm
          calc
            s + (a - (s + sh) + sh)
                = s + ((a - (s + sh)) + sh) := by simp
            _   = s + (a - (s + sh)) + sh := by simp [Nat.add_assoc]
            _   = s + sh + (a - (s + sh)) := by
                    simp [Nat.add_assoc, Nat.add_comm]
            _   = (s + sh) + (a - (s + sh)) := by simp [Nat.add_assoc]
            _   = a := by rw[Nat.add_sub_of_le];unfold a getLen;rw[incLen_getD_self];simp;set b:=(incLen ctx.curLen src sh)[dst.val]?.getD 0; change s + sh ≤ 1 + b.max (s + sh)
                          have:=le_one_add_max (s+sh) b; rw[Nat.max_eq_max] at this;
                          rw[Nat.max_eq_max, Nat.max_comm];apply this; apply hV.curLen_len
          all_goals try apply hV.curLen_len
          all_goals try simp[hds]
          all_goals try rw[incLen_pres_len]; try apply hV.curLen_len
          intro h;simp_all
        }
        rw[bridge_negate σ ctx hV,bridge_allocLSB (vF:=hV4), bridge_allocMSB (hV:=hV5), bridge_allocMSB (hV:=hV6), bridge_add (hV:=hV2) (hW:=by simp[hW])]
        clear hW
        rw[bridge_freeMSB (hn:=by rw[incLen_getD_self];simp;rw[incLen_pres_len,incLen_pres_len,hV.curLen_len]) (hV:=hV3)];simp
        set σA :=
          (((σ.negateReg src).shiftLReg src sh).addScaledReg dst src false 0)

        set ctxA : StCtx k :=
          { ρ := ctx.ρ, baseW := ctx.baseW,
            curLen := incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) (↑dst)) }
        have hn : sh ≤ ctxA.curLen.getD src.1 0 := by
          unfold ctxA;rw[incLen_getD_ne'];simp;rw[← incLen_to_sum];linarith;apply hV.curLen_len;rw[incLen_pres_len];apply hV.curLen_len;intro h;
          simp_all
        have hLat:=State.shiftRReg?_after_neg_shiftL_addScaled_eq σ dst src sh hds
        obtain ⟨σA', hshift⟩ : ∃ σA', State.shiftRReg? σA src sh = some σA' := by
          unfold σA
          apply State.exists_shiftRReg_after_neg_shiftL_addScaled
          simp[hds]

        have hV_A : ValidFor σA ctxA := by
          unfold ctxA
          have:= hV_step ((σ.negateReg src).shiftLReg src sh) σA (valid_ops.addScaled dst src false 0)  (incLen ctx.curLen src sh) (by simp[σA]) (by simp[Prog.OpOK,hds]) (hV5)
          rw[add_Scaled_compile_curLen] at this;unfold a
          simp_all
          apply hds
        have hFree :
          eval_prim_op_single (k := k) (prim_ops.Free src true sh) (stateToSt (k := k) σA ctxA)
            =
          stateToSt (k := k) σA' { ctxA with curLen := decLen ctxA.curLen src sh } :=
        by
          simpa [σA, ctxA] using (bridge_freeLSB (k := k) (σ := σA) (σ' := σA') (ctx := ctxA) (i := src) (n := sh) hn hshift hV_A)
        rw [hFree]
        rw[bridge_negate];congr
        {
          clear hFree hV_A hn hV_step hV hV6 ctxA hV2 hV3 hV5 hV4 h3 h1 a
          have hLat' :
            σA.shiftRReg? src sh = some (State.setReg σA src ((σ.negateReg src) src)) := by
            unfold σA;simp_all
          have hσA' : σA' = State.setReg σA src ((σ.negateReg src) src) := by
            apply Option.some.inj
            simp_all
          subst hσA'
          have h_final :
              (State.negateReg (State.setReg σA src ((σ.negateReg src) src)) src)
                =
              σ.addScaledReg dst src true sh := by {
                apply setReg_negateReg_pipeline_eq_addScaled σ dst src sh hds
              }
          have hσ2 : σ2 = σ.addScaledReg dst src true sh := by
            have hs : some (σ.addScaledReg dst src true sh) = some σ2 := by
              simpa [applyOp?] using hstep
            exact (Option.some.inj hs).symm
          simpa [hσ2] using h_final
        }
        {
          have:= hV_step σA σA' (valid_ops.shiftR src sh) ctxA.curLen (hshift) (by simp[Prog.OpOK]) hV_A;
          simp[compile1,compile_op_to_prim_single] at this
          simp_all[ctxA]
        }
      }


lemma bridge_compile1_addScaled_helper2
  {k : ℕ}
  (σ σ2 : State k)
  (ctx : StCtx k)
  (dst src : Fin k)
  (hds: ¬ dst=src)
  (sh : ℕ)
  (hsh:sh=0)
  (hV : ValidFor (k := k) σ ctx)
  (hV_step : ValidForStep (k := k) ctx)
  (hstep : applyOp? σ (valid_ops.addScaled dst src false sh) = some σ2)
  :
  eval_prim_ops
      (compile1 (valid_ops.addScaled dst src false sh) ctx.curLen).1
      (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ2
    { ρ := ctx.ρ, baseW := ctx.baseW,
      curLen := (compile1 (valid_ops.addScaled dst src false sh) ctx.curLen).2 } := by
      unfold compile1 compile_op_to_prim_single
      simp[hds,hsh]
      set a:=1 + (getLen ctx.curLen ↑dst).max (getLen ctx.curLen ↑src)
      split_ifs with h1 h2 h3<;>simp
      {
        set lenDst : Nat := getLen ctx.curLen (↑dst) with hlenDst
        have hlt : lenDst < a := by
          have hle : lenDst ≤ Nat.max lenDst (getLen ctx.curLen (↑src)) := by
            exact Nat.le_max_left _ _
          have:= Nat.lt_succ_of_le hle
          simp [a, lenDst]
          linarith

        have hle : a ≤ lenDst := by
          exact (Nat.sub_eq_zero_iff_le).1 (by simpa [lenDst] using h1)
        have : False := by
          have : lenDst < lenDst := Nat.lt_of_lt_of_le hlt hle
          exact (Nat.lt_irrefl _ this)
        exact False.elim this
      }
      {
        set ld : Nat := getLen ctx.curLen (↑dst) with hld
        set ls : Nat := getLen ctx.curLen (↑src) with hls

        have ld_lt_a : ld < a := by
          have hle : ld + 1 ≤ a := by
            have : ld ≤ Nat.max ld ls := Nat.le_max_left _ _
            have : ld + 1 ≤ Nat.max ld ls + 1 := Nat.succ_le_succ this
            unfold a ld
            linarith
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self ld) hle
        have a_le_ld : a ≤ ld := by
          exact (Nat.sub_eq_zero_iff_le).1 (by simpa [ld] using h1)
        have : False := (Nat.not_le_of_lt ld_lt_a) a_le_ld
        exact False.elim this
      }
      {
        exfalso
        set lenSrc : Nat := getLen ctx.curLen (↑src) with hlenSrc
        have h_le_max : lenSrc ≤ (getLen ctx.curLen (↑dst)).max lenSrc := by
          aesop
        have h_succ_le_a : lenSrc.succ ≤ a := by
          dsimp [a];nth_rewrite 2 [add_comm]
          apply Nat.succ_le_succ h_le_max

        have h_a_le_lenSrc : a ≤ lenSrc := by
          have : a - lenSrc = 0 := by simpa [lenSrc, hlenSrc] using h3
          exact (Nat.sub_eq_zero_iff_le).1 this
        have : lenSrc.succ ≤ lenSrc := le_trans h_succ_le_a h_a_le_lenSrc
        exact Nat.not_succ_le_self lenSrc this
      }
      {
        simp[eval_prim_ops]
        subst hsh
        have hV1:ValidFor (σ.negateReg src) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst) }:=by
          unfold ValidForStep at *
          have:= hV_step σ (σ.negateReg src) (valid_ops.negate src) (incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst))
          simp[applyOp?,Prog.OpOK] at this
          apply this
          apply ValidFor_incLen
          apply hV
        have hV2:ValidFor σ { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst) }:=by apply ValidFor_incLen;assumption
        have hV3:ValidFor σ { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst)) src (a - getLen ctx.curLen ↑src) }:=by {
          have:=ValidFor_incLen (n:=(a - getLen ctx.curLen ↑src)) (k:=k) src σ ({ ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst) }) hV2
          apply this
        }
        have hV4:ValidFor (σ.addScaledReg dst src false 0) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst)) src (a - getLen ctx.curLen ↑src) }:=by
          have h1:=hV_step σ (σ.addScaledReg dst src false 0) (valid_ops.addScaled dst src false 0) (ctx.curLen) (by simp) (by simp[Prog.OpOK,hds]) (by simp[hV])
          simp[compile1,compile_op_to_prim_single,hds] at h1
          set δdst := a - getLen ctx.curLen ↑dst
          set δsrc := a - getLen ctx.curLen ↑src
          have:= ValidFor_incLen (n:=δsrc) (k:=k) src (σ.addScaledReg dst src false 0) ({ ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen dst δdst }) h1
          simp_all

        have hW:stWidth { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst)) src (a - getLen ctx.curLen ↑src) } dst = stWidth { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst)) src (a - getLen ctx.curLen ↑src) } src:=by {
          unfold stWidth;simp;have:=incLen_getD_ne' (k:=k);simp at this;rw[this]
          rw[incLen_incLen_disjoint_comm];nth_rewrite 2[this];rw[← incLen_to_sum];rw[← incLen_to_sum];
          unfold getLen
          have h1:(ctx.curLen[dst.val]?.getD 0 + (a - ctx.curLen.getD (↑dst) 0))=a:=by {
            simp;rw[add_comm,Nat.sub_add_cancel];unfold a getLen;simp
            simpa using le_one_add_max (a := ctx.curLen[↑dst]?.getD 0) (b := ctx.curLen[↑src]?.getD 0)
          }
          have h2:(ctx.curLen[src.val]?.getD 0 + (a - ctx.curLen.getD (↑src) 0))=a:=by {
            simp;rw[add_comm,Nat.sub_add_cancel];unfold a getLen;simp
            have:= le_one_add_max (a := ctx.curLen[↑src]?.getD 0) (b := ctx.curLen[↑dst]?.getD 0)
            rw[Nat.max_eq_max,max_comm];aesop
          }
          rw[h1,h2,hV.baseW_eq];apply hV.curLen_len;apply hV.curLen_len;rw[incLen_pres_len];apply hV.curLen_len
          intro h;subst h;simp at hds;simp[hds];rw[incLen_pres_len];apply hV.curLen_len;apply hds
        }

        rw[bridge_allocMSB (hV:=hV),bridge_allocMSB (hV:=hV2), bridge_add (hW:=(by simp_all)) (hV:=hV3)];
        rw[bridge_freeMSB (hV:=hV4)]
        simp;congr;simp[applyOp?] at hstep;apply hstep
        simp
        rw[incLen_incLen_disjoint_comm];simp[← List.getD_eq_getElem?_getD];rw[incLen_getD_ne'];rw[incLen_getD_self]
        nth_rewrite 2 [Nat.add_comm];rw[Nat.add_assoc];nth_rewrite 2 [Nat.add_comm];rw[← Nat.add_assoc]
        rw[Nat.sub_add_cancel];simp;unfold a; omega
        apply hV.curLen_len;rw[incLen_pres_len,hV.curLen_len];intro ha;simp[ha] at hds;simp[hds]
      }


lemma shiftRReg?_shiftL_addScaled0_eq_addScaled_sh
  {k : ℕ} (σ : State k) (dst src : Fin k) (sh : ℕ) (hds : dst ≠ src) :
  ((σ.shiftLReg src sh).addScaledReg dst src false 0).shiftRReg? src sh
    =
  some (σ.addScaledReg dst src false sh) := by
  classical
  -- Your lemma gives the result as `some σA'` where `σA' = setReg σA src (σ src)`
  set σA : State k := (σ.shiftLReg src sh).addScaledReg dst src false 0
  set σA' : State k := State.setReg σA src (σ src)

  have hmain : σA.shiftRReg? src sh = some σA' := by
    simpa [σA, σA'] using
      (State.shiftRReg?_after_shiftL_addScaled_eq
        (σ := σ) (dst := dst) (src := src) (sh := sh) hds)

  -- Now show that this σA' is exactly `σ.addScaledReg dst src false sh`
  have hσA' : σA' = σ.addScaledReg dst src false sh := by
    ext r j
    by_cases hr_src : r = src
    · subst hr_src;have hds:r≠dst:=by omega
      simp [σA', State.setReg, State.addScaledReg, hds]
    · by_cases hr_dst : r = dst
      · subst hr_dst
        simp [σA, σA', State.addScaledReg, State.shiftLReg, State.setReg,
              Register.addScaled, Register.shiftL, hr_src,
              pow_zero,  mul_left_comm, mul_comm]
      ·
        simp [σA, σA', State.addScaledReg, State.shiftLReg, State.setReg,
              hr_src, hr_dst]
  simpa [σA, hσA'] using hmain


-- Now your exact goal shape:
-- hstep : σ.addScaledReg dst src false sh = σ2
-- ⊢ ((σ.shiftLReg src sh).addScaledReg dst src false 0).shiftRReg? src sh = some σ2

lemma bridge_compile1_addScaled_helper3
  {k : ℕ}
  (σ σ2 : State k)
  (ctx : StCtx k)
  (dst src : Fin k)
  (hds: ¬ dst=src)
  (sh : ℕ)
  (hsh:sh≠0)
  (hV : ValidFor (k := k) σ ctx)
  (hV_step : ValidForStep (k := k) ctx)
  (hstep : applyOp? σ (valid_ops.addScaled dst src false sh) = some σ2)
  :
  eval_prim_ops
      (compile1 (valid_ops.addScaled dst src false sh) ctx.curLen).1
      (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ2
    { ρ := ctx.ρ, baseW := ctx.baseW,
      curLen := (compile1 (valid_ops.addScaled dst src false sh) ctx.curLen).2 } := by
      unfold compile1 compile_op_to_prim_single
      simp[hds,hsh]
      simp[eval_prim_ops]
      set a:=1 + (getLen (incLen ctx.curLen src sh) ↑dst).max (getLen (incLen ctx.curLen src sh) ↑src)
      split_ifs with h1 h2 h3<;>simp
      {
        set lenDst : Nat := getLen (incLen ctx.curLen src sh) (↑dst) with hlenDst
        set lenSrc : Nat := getLen (incLen ctx.curLen src sh) (↑src) with hlenSrc

        have ha_le : a ≤ lenDst := by
          exact (Nat.sub_eq_zero_iff_le).1 (by simpa [lenDst] using h1)
        have hlenDst_lt : lenDst < a := by
          have hle : lenDst ≤ Nat.max lenDst lenSrc := Nat.le_max_left _ _
          have:=(Nat.lt_succ_of_le hle)
          simp [lenDst, lenSrc, Nat.succ_eq_add_one] at this
          unfold lenDst a
          linarith
        have : False := (Nat.not_lt_of_ge ha_le) hlenDst_lt
        exact False.elim this
      }
      {
        set ld : Nat := getLen (incLen ctx.curLen src sh) ↑dst
        set ls : Nat := getLen (incLen ctx.curLen src sh) ↑src

        have ld_lt_a : ld < a := by
          have hle : ld + 1 ≤ a := by
            have : ld ≤ Nat.max ld ls := Nat.le_max_left _ _
            have : ld + 1 ≤ Nat.max ld ls + 1 := Nat.succ_le_succ this
            unfold a ld
            linarith
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self ld) hle
        have a_le_ld : a ≤ ld := by
          exact (Nat.sub_eq_zero_iff_le).1 (by simpa [ld] using h1)
        have : False := (Nat.not_le_of_lt ld_lt_a) a_le_ld
        exact False.elim this
      }
      {
        exfalso
        set lenSrc : Nat := getLen (incLen ctx.curLen src sh) (↑src) with hlenSrc
        have h_le_max : lenSrc ≤ (getLen ctx.curLen (↑dst)).max lenSrc := by
          aesop
        have h_succ_le_a : lenSrc.succ ≤ a := by
          dsimp [a];nth_rewrite 2 [add_comm]
          have:=Nat.succ_le_succ h_le_max
          simp_all
        have h_a_le_lenSrc : a ≤ lenSrc := by
          have : a - lenSrc = 0 := by simpa [lenSrc, hlenSrc] using h3
          exact (Nat.sub_eq_zero_iff_le).1 this
        have : lenSrc.succ ≤ lenSrc := le_trans h_succ_le_a h_a_le_lenSrc
        exact Nat.not_succ_le_self lenSrc this
      }
      {
        simp[eval_prim_ops]
        have hV1:ValidFor (σ.shiftLReg src sh) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen src sh }:=by
          unfold ValidForStep at *
          have:= hV_step σ (σ.shiftLReg src sh) (valid_ops.shiftL src sh) (ctx.curLen);simp_all
          simp[applyOp?, Prog.OpOK, compile1, compile_op_to_prim_single] at this
          apply this

        have hV2:ValidFor (σ.shiftLReg src sh) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst) }:=by
          have:=ValidFor_incLen (n:=((a - getLen (incLen ctx.curLen src sh) ↑dst))) dst (σ.shiftLReg src sh) ({ ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen src sh }) hV1
          apply this

        have hV3:ValidFor (σ.shiftLReg src sh) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst)) src (a - getLen (incLen ctx.curLen src sh) ↑src) } := by
          set b:=incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst)
          have:= ValidFor_incLen (n:=((a - getLen (incLen ctx.curLen src sh) src))) src (σ.shiftLReg src sh) ({ ρ := ctx.ρ, baseW := ctx.baseW, curLen := b }) hV2
          apply this

        have hW: stWidth { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst)) src (a - getLen (incLen ctx.curLen src sh) ↑src) } dst
          =
          stWidth { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst)) src (a - getLen (incLen ctx.curLen src sh) ↑src) } src := by
          unfold stWidth;simp
          rw[incLen_comm, incLen_incLen_add, ← incLen_to_sum];unfold getLen
          set l1:=(incLen ctx.curLen src sh);set b:=a - l1.getD (↑src) 0; set c:= a - l1.getD (↑dst) 0
          conv_rhs=>
            arg 2
            change (incLen (incLen ctx.curLen src (sh + b)) dst c).getD src 0
          rw[incLen_getD_ne'];unfold c l1;rw[incLen_getD_ne'];simp;

          have h1:((incLen ctx.curLen src (sh + b))[dst.val]?.getD 0 + (a - (incLen ctx.curLen src sh).getD (↑dst) 0))=a:=by {
            rw[add_comm,incLen_getD_ne'];unfold a getLen;simp;simp[← List.getD_eq_getElem?_getD];
            nth_rewrite 1 [incLen_getD_ne'];nth_rewrite 2 [incLen_getD_ne'];nth_rewrite 2 [incLen_getD_ne'];all_goals try assumption
            rw[incLen_getD_self];rw[Nat.sub_add_cancel];
            rw[← Nat.succ_eq_one_add]
            apply le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
            all_goals apply hV.curLen_len
          }
          rw[incLen_getD_ne'] at h1;simp at h1;rw[h1];rw[← List.getD_eq_getElem?_getD,incLen_getD_self];unfold b l1;rw[incLen_getD_self]
          simp
          nth_rewrite 4 [add_comm];rw[hV.baseW_eq (i:=dst) (j:=src)];simp;set s : Nat := ctx.curLen[src.val]?.getD 0
          symm
          calc
            s + (a - (s + sh) + sh)
                = s + ((a - (s + sh)) + sh) := by simp
            _   = s + (a - (s + sh)) + sh := by simp [Nat.add_assoc]
            _   = s + sh + (a - (s + sh)) := by
                    simp [Nat.add_assoc, Nat.add_comm]
            _   = (s + sh) + (a - (s + sh)) := by simp [Nat.add_assoc]
            _   = a := by rw[Nat.add_sub_of_le];unfold a getLen;rw[incLen_getD_self];simp;set b:=(incLen ctx.curLen src sh)[dst.val]?.getD 0; change s + sh ≤ 1 + b.max (s + sh)
                          have:=le_one_add_max (s+sh) b; rw[Nat.max_eq_max] at this;
                          rw[Nat.max_eq_max, Nat.max_comm];apply this; apply hV.curLen_len
          all_goals try apply hV.curLen_len
          all_goals try simp[hds]
          all_goals try rw[incLen_pres_len]; try apply hV.curLen_len
          intro h;simp_all


        have hV4:ValidFor ((σ.shiftLReg src sh).addScaledReg dst src false 0) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen (incLen ctx.curLen src sh) dst (a - getLen (incLen ctx.curLen src sh) ↑dst)) src (a - getLen (incLen ctx.curLen src sh) ↑src) }:=by {
          --set b:=incLen ctx.curLen src sh
          clear hW h1 h3
          have h2:= hV_step (σ.shiftLReg src sh) ((σ.shiftLReg src sh).addScaledReg dst src false 0) (valid_ops.addScaled dst src false 0) (incLen ctx.curLen src sh ) (by simp[applyOp?]) (by simp[Prog.OpOK,hds]) hV1
          simp[compile1, compile_op_to_prim_single, hds] at h2;
          have h1:(a - getLen (incLen ctx.curLen src sh) ↑dst)=(1 + (getLen (incLen ctx.curLen src sh) ↑dst).max (getLen (incLen ctx.curLen src sh) ↑src) - getLen (incLen ctx.curLen src sh) ↑dst):=by
            unfold a;simp
          rw[h1]
          set b:=(incLen (incLen ctx.curLen src sh) dst (1 + (getLen (incLen ctx.curLen src sh) ↑dst).max (getLen (incLen ctx.curLen src sh) ↑src) - getLen (incLen ctx.curLen src sh) ↑dst))
          have h3:=ValidFor_incLen (n:=(a - getLen (incLen ctx.curLen src sh) ↑src)) (k:=k) src ((σ.shiftLReg src sh).addScaledReg dst src false 0) ({ ρ := ctx.ρ, baseW := ctx.baseW, curLen := b }) h2
          apply h3
        }

        rw[bridge_allocLSB (vF:=hV), bridge_allocMSB (hV:=hV1), bridge_allocMSB (hV:= hV2), bridge_add (hV:=hV3) (hW:=by simp_all)]
        clear hW h1 h3
        rw[bridge_freeMSB (hn:=by rw[incLen_getD_self];simp;rw[incLen_pres_len,incLen_pres_len,hV.curLen_len]) (hV:=hV4)]
        simp_all
        set δdst : Nat := a - getLen (incLen ctx.curLen src sh) (↑dst)
        have hn :
          sh ≤ (incLen (incLen ctx.curLen src sh) dst δdst).getD src.1 0 := by
          have hdst_ne : dst ≠ src := hds
          have hout :
            (incLen (incLen ctx.curLen src sh) dst δdst).getD src.1 0
              =
            (incLen ctx.curLen src sh).getD src.1 0 := by
            have:= incLen_getD_ne' (k := k) (curLen := incLen ctx.curLen src sh)
              (i := dst) (j := src) (n := δdst) (by rw[incLen_pres_len,hV.curLen_len]) (by intro h;simp[h] at hdst_ne)
            apply this
          have hin :
            (incLen ctx.curLen src sh).getD src.1 0 = ctx.curLen.getD src.1 0 + sh := by
            simpa using incLen_getD_self (k := k) (curLen := ctx.curLen) (n := sh) (j := src) hV.curLen_len
          calc
            sh ≤ ctx.curLen.getD src.1 0 + sh := Nat.le_add_left sh (ctx.curLen.getD src.1 0)
            _ = (incLen ctx.curLen src sh).getD src.1 0 := by rw[hin]
            _ = (incLen (incLen ctx.curLen src sh) dst δdst).getD src.1 0 := by rw[hout]
        rw[bridge_freeLSB (hn:=hn)]
        simpa [hstep] using (shiftRReg?_shiftL_addScaled0_eq_addScaled_sh (σ := σ) (dst := dst) (src := src) (sh := sh) hds)
        set σA:=((σ.shiftLReg src sh).addScaledReg dst src false 0)
        have:= hV_step (σ.shiftLReg src sh) σA (valid_ops.addScaled dst src false 0)  (incLen ctx.curLen src sh) (by simp[σA]) (by simp[Prog.OpOK,hds]) hV1
        simp[compile1, compile_op_to_prim_single,hds] at this;unfold δdst a;simp_all
      }


lemma compile1_addScaled_correct {k : ℕ}
    (σ σ2: State k) (ctx : StCtx k)
    (dst src : Fin k) (negSrc : Bool) (sh : ℕ)
    (hV : ValidFor σ ctx)
    (hV_step : ValidForStep (k := k) ctx)
    (hOK : Prog.OpOK (valid_ops.addScaled dst src negSrc sh))
    (hstep : σ.addScaledReg dst src negSrc sh = σ2)
    (hPrim :
      let (ops, _nextLen) := compile1 (valid_ops.addScaled dst src negSrc sh) ctx.curLen
      PrimOKTrace (k := k) ops ctx)
    :
    let (ops, nextLen) := compile1 (valid_ops.addScaled dst src negSrc sh) ctx.curLen
    eval_prim_ops ops (stateToSt σ ctx) =
    stateToSt σ2 { ctx with curLen := nextLen } := by
        simp
        by_cases hds : dst = src
        ·
          simp [compile1, compile_op_to_prim_single, hds] at hstep ⊢
          cases hstep
          simp [eval_prim_ops]
          simp [Prog.OpOK] at hOK
          contradiction
        ·
          by_cases hneg:negSrc<;>by_cases hsh:sh=0
          {
            unfold compile1 compile_op_to_prim_single
            simp[hneg,hds,hsh]
            set a:=1 + (getLen ctx.curLen ↑dst).max (getLen ctx.curLen ↑src)
            simp[eval_prim_ops]
            split_ifs with h1 h2 h3<;>simp
            {
              simp[eval_prim_ops]
              set lenDst : Nat := getLen ctx.curLen (↑dst) with hlenDst
              have hlt : lenDst < a := by
                have hle : lenDst ≤ Nat.max lenDst (getLen ctx.curLen (↑src)) := by
                  exact Nat.le_max_left _ _
                have:= Nat.lt_succ_of_le hle
                simp [a, lenDst]
                linarith

              have hle : a ≤ lenDst := by
                exact (Nat.sub_eq_zero_iff_le).1 (by simpa [lenDst] using h1)
              have : False := by
                have : lenDst < lenDst := Nat.lt_of_lt_of_le hlt hle
                exact (Nat.lt_irrefl _ this)
              exact False.elim this
            }
            {
              set ld : Nat := getLen ctx.curLen (↑dst) with hld
              set ls : Nat := getLen ctx.curLen (↑src) with hls

              have ld_lt_a : ld < a := by
                have hle : ld + 1 ≤ a := by
                  have : ld ≤ Nat.max ld ls := Nat.le_max_left _ _
                  have : ld + 1 ≤ Nat.max ld ls + 1 := Nat.succ_le_succ this
                  unfold a ld
                  linarith
                exact Nat.lt_of_lt_of_le (Nat.lt_succ_self ld) hle
              have a_le_ld : a ≤ ld := by
                exact (Nat.sub_eq_zero_iff_le).1 (by simpa [ld] using h1)
              have : False := (Nat.not_le_of_lt ld_lt_a) a_le_ld
              exact False.elim this
            }
            {
              exfalso
              set lenSrc : Nat := getLen ctx.curLen (↑src) with hlenSrc
              have h_le_max : lenSrc ≤ (getLen ctx.curLen (↑dst)).max lenSrc := by
                aesop
              have h_succ_le_a : lenSrc.succ ≤ a := by
                dsimp [a];nth_rewrite 2 [add_comm]
                apply Nat.succ_le_succ h_le_max

              have h_a_le_lenSrc : a ≤ lenSrc := by
                have : a - lenSrc = 0 := by simpa [lenSrc, hlenSrc] using h3
                exact (Nat.sub_eq_zero_iff_le).1 this
              have : lenSrc.succ ≤ lenSrc := le_trans h_succ_le_a h_a_le_lenSrc
              exact Nat.not_succ_le_self lenSrc this
            }
            {
              simp[eval_prim_ops]
              have hV1:ValidFor (σ.negateReg src) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst) }:=by
                unfold ValidForStep at *
                have:= hV_step σ (σ.negateReg src) (valid_ops.negate src) (incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst))
                simp[applyOp?,Prog.OpOK] at this
                apply this
                apply ValidFor_incLen
                apply hV
              have hV3:ValidFor (σ.negateReg src) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst)) src (a - getLen ctx.curLen ↑src) }:=by
                have:= hV_step σ (σ.negateReg src) (valid_ops.negate src) (incLen (incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst)) src (a - getLen ctx.curLen ↑src))
                simp[applyOp?,Prog.OpOK,compile1,compile_op_to_prim_single] at this
                apply this
                have hV2:ValidFor σ { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst) }:=by apply ValidFor_incLen;assumption
                have:=ValidFor_incLen (n:=(a - getLen ctx.curLen ↑src)) (k:=k) src σ ({ ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst) }) hV2
                simp at this;apply this
              have hV4:ValidFor (σ.negateReg src) ctx:=by
                unfold ValidForStep at *
                have:= hV_step σ (σ.negateReg src) (valid_ops.negate src) ctx.curLen
                simp[applyOp?,Prog.OpOK] at this
                apply this
                apply hV
              have:=hV_step (σ.negateReg src) ((σ.negateReg src).addScaledReg dst src false 0) (valid_ops.addScaled dst src false sh) ctx.curLen (by simp[hsh]) hOK hV4;simp at this
              have hV5:ValidFor ((σ.negateReg src).addScaledReg dst src false 0) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst) }:=by
                subst hsh;rw[add_Scaled_compile_curLen (k:=k) dst src hds ctx.curLen] at this;aesop
              have hV6:stWidth { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst)) src (a - getLen ctx.curLen ↑src) } dst = stWidth { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen (incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst)) src (a - getLen ctx.curLen ↑src) } src:=by {
                unfold stWidth;simp;have:=incLen_getD_ne' (k:=k);simp at this;rw[this]
                rw[incLen_incLen_disjoint_comm];nth_rewrite 2[this];rw[← incLen_to_sum];rw[← incLen_to_sum];
                unfold getLen
                have h1:(ctx.curLen[dst.val]?.getD 0 + (a - ctx.curLen.getD (↑dst) 0))=a:=by {
                  simp;rw[add_comm,Nat.sub_add_cancel];unfold a getLen;simp
                  simpa using le_one_add_max (a := ctx.curLen[↑dst]?.getD 0) (b := ctx.curLen[↑src]?.getD 0)
                }
                have h2:(ctx.curLen[src.val]?.getD 0 + (a - ctx.curLen.getD (↑src) 0))=a:=by {
                  simp;rw[add_comm,Nat.sub_add_cancel];unfold a getLen;simp
                  have:= le_one_add_max (a := ctx.curLen[↑src]?.getD 0) (b := ctx.curLen[↑dst]?.getD 0)
                  rw[Nat.max_eq_max,max_comm];aesop
                }
                rw[h1,h2,hV.baseW_eq];apply hV.curLen_len;apply hV.curLen_len;rw[incLen_pres_len];apply hV.curLen_len
                intro h;subst h;simp at hds;simp[hds];rw[incLen_pres_len];apply hV.curLen_len;apply hds
              }
              rw[bridge_negate σ ctx hV,bridge_allocMSB (hV:=hV4),bridge_allocMSB (hV:=hV1)]
              rw[bridge_add (hV:=hV3) (hW:=by simp[hV6]), bridge_freeMSB , bridge_negate (hV:=by simp;apply hV5)]
              simp;congr;rw[State.negate_addScaledReg_negate];subst hsh;subst negSrc;apply hstep;simp[hds]
              simp
              have h1:=incLen_to_sum k ((incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst))) (a - getLen ctx.curLen ↑src) src (by simp_all;rw[incLen_pres_len]; apply hV.curLen_len)
              simp;rw[← h1];have h2:=incLen_getD_ne' (ctx.curLen) dst src (a - getLen ctx.curLen ↑dst) hV.curLen_len (by aesop)
              conv_rhs=>
                arg 1;arg 1;change (incLen ctx.curLen dst (a - getLen ctx.curLen ↑dst)).getD (↑src) 0
                rw[h2]
              rw[add_assoc];omega;
              set σ' := ((σ.negateReg src).addScaledReg dst src false 0)
              set δdst := a - getLen ctx.curLen ↑dst
              set δsrc := a - getLen ctx.curLen ↑src
              set ctxDst : StCtx k := { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen dst δdst }
              have : ValidFor (k := k) σ' { ctxDst with curLen := incLen ctxDst.curLen src δsrc } := by
                exact ValidFor_incLen (k := k) (σ := σ') (ctx := ctxDst) (i := src) (n := δsrc) hV5
              simpa [σ', ctxDst, δdst, δsrc] using this
            }

          }
          {
            subst hneg
            apply bridge_compile1_addScaled σ σ2 ctx dst src hds sh hsh hV hV_step
            simp[applyOp?,hstep]
          }
          {
            simp at hneg; subst hneg
            apply bridge_compile1_addScaled_helper2 σ σ2 ctx dst src hds sh hsh hV hV_step (by simp_all)
          }
          {
            have:=bridge_compile1_addScaled_helper3 σ σ2 ctx dst src hds sh hsh hV hV_step (by simp_all)
            simp_all
          }












theorem compile1_simulates
  {k : ℕ}
  (op : valid_ops k)
  (σ : State k)
  (ctx : StCtx k)
  (hV : ValidFor (k := k) σ ctx)
  (hV_step : ValidForStep (k := k) ctx)
  (hPrim :  PrimOKTrace (compile1 op ctx.curLen).1 ctx)
  (σ2 : State k)
  (hstep : applyOp? σ op = some σ2)
  (hOK : Prog.OpOK op) :
  let (opsP, curLen') := compile1 (k := k) op ctx.curLen
  eval_prim_ops (k := k) opsP (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ2 { ctx with curLen := curLen' } := by
  cases ctx with
  | mk ρ baseW curLen =>
    have hcurLen : curLen.length = k := by
      simpa using hV.curLen_len

    cases op with
    | shiftL i n =>
        simp [compile1, compile_op_to_prim_single, applyOp?] at hstep ⊢
        cases hstep
        simpa [eval_prim_ops_singleton] using
          (bridge_allocLSB (k := k) (σ := σ) (ctx := ⟨ρ, baseW, curLen⟩)
            (vF := hV) (i := i) (n := n))

    | shiftR i n =>
        simp [compile1, compile_op_to_prim_single, applyOp?] at hstep ⊢
        have:=(bridge_freeLSB (k := k) (σ := σ) (σ' := σ2) (ctx := ⟨ρ, baseW, curLen⟩)
            (i := i) (n := n) (h := hstep) (hV:=hV))
        apply this
        unfold PrimOKForCtxListRun compile1 compile_op_to_prim_single at *
        simp at *; rcases hPrim with ⟨h1,h2⟩; unfold PrimOKForCtx at h1; simp at h1; assumption

    | negate i =>
        simp [compile1, compile_op_to_prim_single, applyOp?] at hstep ⊢
        cases hstep
        simpa [eval_prim_ops_singleton] using
          (bridge_negate (k := k) (σ := σ) (ctx := ⟨ρ, baseW, curLen⟩) (i := i) hV)

    | phaseProduct i =>
        simp [compile1, compile_op_to_prim_single, applyOp?, eval_prim_ops, eval_prim_op_single] at *
        simp [hstep]

    | addScaled dst src negSrc sh =>
        simp_all
        have:= (compile1_addScaled_correct σ σ2) {ρ:=ρ,baseW:=baseW,curLen:=curLen} dst src negSrc sh hV hV_step hOK hstep
        apply this
        simp[hPrim]



lemma compile1_pres_len {k} (op : valid_ops k) (curLen : List Nat)
  (h : curLen.length = k) :
  (compile1 (k:=k) op curLen).2.length = k :=by
  cases op with
  |shiftL i sh=>{
    unfold compile1 compile_op_to_prim_single
    simp[incLen_pres_len,h]
  }
  |shiftR i sh=>{
    unfold compile1 compile_op_to_prim_single
    simp[decLen_pres_len,h]
  }
  |addScaled dst src negsrc sh=>{
    unfold compile1 compile_op_to_prim_single
    simp
    split_ifs with h1 h2<;>simp[h,incLen_pres_len,decLen_pres_len]
  }
  |negate=>{
    unfold compile1 compile_op_to_prim_single
    simp[h]
  }
  |phaseProduct=>{
    unfold compile1 compile_op_to_prim_single
    simp[h]
  }

theorem compileProg_simulates_go
  {k : ℕ}
  (ops : Prog k)
  (σ : State k)
  (ctx0 : StCtx k)
  (curLenNow : List Nat)
  (σ2 : State k)
  (hstep : run? (k := k) ops σ = some σ2)
  (hOK : Prog.WellFormed ops)
  (hV : ValidFor (k := k) σ { ctx0 with curLen := curLenNow })
  (hStepValid : ValidForStep (k := k) ctx0) :
  let ctxNow : StCtx k := { ctx0 with curLen := curLenNow }
  let (opsP, curLen') := compileProg (k := k) ops curLenNow
  eval_prim_ops (k := k) opsP (stateToSt (k := k) σ ctxNow)
    =
  stateToSt (k := k) σ2 { ctx0 with curLen := curLen' } := by
  induction ops generalizing σ curLenNow σ2 with
  | nil =>
      simp [run?] at hstep
      cases hstep
      simp [compileProg, eval_prim_ops]
  | cons op ops ih =>
      have hOK_head : Prog.OpOK op := by
        aesop
      have hOK_tail : Prog.WellFormed ops := by
        simp [Prog.WellFormed] at hOK
        unfold Prog.WellFormed
        rcases hOK with ⟨hl, hr⟩
        intro op hop
        exact hr op hop

      simp [run?] at hstep
      cases hσ1 : applyOp? σ op with
      | none =>
          simp [hσ1] at hstep
      | some σ1 =>
          have hstep_tail : run? (k := k) ops σ1 = some σ2 := by
            simpa [hσ1] using hstep

          -- compile head
          cases hC1 : compile1 (k := k) op curLenNow with
          | mk opsP1 curLen1 =>
              -- simulate the head using compile1_simulates
              have hsim_head :
                eval_prim_ops (k := k) opsP1 (stateToSt (k := k) σ { ctx0 with curLen := curLenNow })
                  =
                stateToSt (k := k) σ1 { ctx0 with curLen := curLen1 } := by
                  have:=compile1_simulates op σ ctx0 (by sorry)
                  sorry

              -- get ValidFor for the tail state/context via the step-preservation hypothesis
              have hV1 :
                ValidFor (k := k) σ1 { ctx0 with curLen := curLen1 } := by
                -- unfold the step rule at exactly this situation
                have := hStepValid σ σ1 op curLenNow hσ1 hOK_head hV
                -- rewrite `curLen1` to match compile1's result
                simpa [hC1] using this

              -- apply IH to the tail
              have hsim_tail :
                let (opsP, curLen') := compileProg (k := k) ops curLen1
                eval_prim_ops (k := k) opsP (stateToSt (k := k) σ1 { ctx0 with curLen := curLen1 })
                  =
                stateToSt (k := k) σ2 { ctx0 with curLen := curLen' } := by
                simpa using
                  (ih (σ := σ1) (curLenNow := curLen1) (σ2 := σ2)
                    (hstep := hstep_tail) (hOK := hOK_tail) (hV := hV1))

              -- stitch head ++ tail
              simp [compileProg, hC1]
              simpa [eval_prim_ops_append, hsim_head] using hsim_tail

theorem compileProg_simulates
  {k : ℕ}
  (ops : Prog k)
  (σ : State k)
  (ctx : StCtx k)
  (σ2 : State k)
  (hstep : run? (k := k) ops σ = some σ2)
  (hOK : Prog.WellFormed ops)
  (hV : ValidFor (k := k) σ ctx)
  (hStepValid : ValidForStep (k := k) ctx) :
  let (opsP, curLen') := compileProg (k := k) ops ctx.curLen
  eval_prim_ops (k := k) opsP (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ2 { ctx with curLen := curLen' } := by
  simpa using
    (compileProg_simulates_go (k := k)
      (ops := ops) (σ := σ) (ctx0 := ctx) (curLenNow := ctx.curLen)
      (σ2 := σ2) (hstep := hstep) (hOK := hOK) (hV := hV) (hStepValid := hStepValid))
