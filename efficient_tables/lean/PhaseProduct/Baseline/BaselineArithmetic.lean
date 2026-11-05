import Model.Interpreter.Interpreter

/-!
# Baseline arithmetic

Run lemmas for the baseline's constant-addition words: `addConstFrom_run`
describes the effect of adding a constant multiple of a register, and
`addConstFrom_addOnly` and `addConstFrom_safe` show such words are add-only and
safe. It also gives the inverse of add-only words (`inverse_addOnly`,
`run_inverse_addOnly`).
-/

namespace Paper.BaselineArithmetic

theorem setReg_same {k : Nat} (sigma : TableGeneration.State k) (dst : Fin k) :
    TableGeneration.State.setReg sigma dst (sigma dst) = sigma := by
  funext i j
  by_cases hi : i = dst <;> simp [TableGeneration.State.setReg, hi]

theorem addScaled_then_setReg {k : Nat} (sigma : TableGeneration.State k)
    (dst src : Fin k) (negSrc : Bool) (shift : Nat) (c : Int)
    (hsep : dst ≠ src) :
    TableGeneration.State.setReg
      (TableGeneration.State.addScaledReg sigma dst src negSrc shift) dst
      (fun j => (TableGeneration.State.addScaledReg sigma dst src negSrc shift) dst j +
        c * (TableGeneration.State.addScaledReg sigma dst src negSrc shift) src j) =
    TableGeneration.State.setReg sigma dst
      (fun j => sigma dst j +
        ((if negSrc then (-1 : Int) else 1) * (2 : Int) ^ shift + c) *
          sigma src j) := by
  funext i j
  by_cases hi : i = dst
  · subst i
    have hs : src ≠ dst := Ne.symm hsep
    cases negSrc <;>
      simp [TableGeneration.State.setReg,
        TableGeneration.State.addScaledReg, TableGeneration.Register.addScaled,
        hs] <;> ring
  · simp [TableGeneration.State.setReg,
      TableGeneration.State.addScaledReg, hi]

theorem addConstAuxFuel_run {k : Nat} (dst src : Fin k) (negSrc : Bool)
    (fuel n shift : Nat) (sigma : TableGeneration.State k)
    (hsep : dst ≠ src) (hfuel : n ≤ fuel) :
    TableGeneration.run?
      (TableGeneration.addConstAuxFuel dst src negSrc fuel n shift) sigma =
      some (TableGeneration.State.setReg sigma dst
        (fun j => sigma dst j +
          (if negSrc then (-1 : Int) else 1) * (n : Int) *
            sigma src j * (2 : Int) ^ shift)) := by
  induction fuel generalizing n shift sigma with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      simpa [TableGeneration.addConstAuxFuel, TableGeneration.run?] using
        (setReg_same sigma dst).symm
  | succ fuel ih =>
      cases n with
      | zero =>
          simpa [TableGeneration.addConstAuxFuel, TableGeneration.run?] using
            (setReg_same sigma dst).symm
      | succ n =>
          have hrec : (n + 1) / 2 ≤ fuel := by omega
          by_cases hodd : (n + 1) % 2 = 1
          · let sigma1 := TableGeneration.State.addScaledReg sigma dst src negSrc shift
            have hr := ih ((n + 1) / 2) (shift + 1) sigma1 hrec
            have hb : ((n + 1 : Nat) : Int) =
                1 + 2 * (((n + 1) / 2 : Nat) : Int) := by omega
            simp only [TableGeneration.addConstAuxFuel, hodd, ↓reduceIte,
              TableGeneration.run?, TableGeneration.applyOp?]
            rw [hr]
            simp only [Option.some.injEq]
            change TableGeneration.State.setReg sigma1 dst
                (fun j => sigma1 dst j +
                  (if negSrc then (-1 : Int) else 1) *
                    (((n + 1) / 2 : Nat) : Int) * sigma1 src j *
                      (2 : Int) ^ (shift + 1)) = _
            rw [show (fun j => sigma1 dst j +
                  (if negSrc then (-1 : Int) else 1) *
                    (((n + 1) / 2 : Nat) : Int) * sigma1 src j *
                      (2 : Int) ^ (shift + 1)) =
                  (fun j => sigma1 dst j +
                    ((if negSrc then (-1 : Int) else 1) *
                      (((n + 1) / 2 : Nat) : Int) *
                      (2 : Int) ^ (shift + 1)) * sigma1 src j) by
                    funext j; ring]
            dsimp only [sigma1]
            rw [addScaled_then_setReg sigma dst src negSrc shift _ hsep]
            funext i j
            by_cases hi : i = dst
            · subst i
              rw [hb, pow_succ]
              simp [TableGeneration.State.setReg]
              cases negSrc <;> simp <;> ring
            · simp [TableGeneration.State.setReg, hi]
          · have hr := ih ((n + 1) / 2) (shift + 1) sigma hrec
            have hb : ((n + 1 : Nat) : Int) =
                2 * (((n + 1) / 2 : Nat) : Int) := by omega
            simp only [TableGeneration.addConstAuxFuel, hodd, ↓reduceIte]
            rw [hr]
            simp only [Option.some.injEq]
            funext i j
            by_cases hi : i = dst
            · subst i
              rw [hb, pow_succ]
              simp [TableGeneration.State.setReg]
              ring
            · simp [TableGeneration.State.setReg, hi]

theorem signed_natAbs (c : Int) :
    (if decide (c < 0) then (-1 : Int) else 1) * (Int.natAbs c : Int) = c := by
  cases c with
  | ofNat n => simp
  | negSucc n => simp [Int.natAbs]; omega

theorem addConstFrom_run {k : Nat} (dst src : Fin k) (c : Int)
    (sigma : TableGeneration.State k) (hsep : dst ≠ src) :
    TableGeneration.run? (TableGeneration.addConstFrom dst src c) sigma =
      some (TableGeneration.State.setReg sigma dst
        (fun j => sigma dst j + c * sigma src j)) := by
  by_cases hc : c = 0
  · subst c
    simpa [TableGeneration.addConstFrom, TableGeneration.run?] using
      (setReg_same sigma dst).symm
  · unfold TableGeneration.addConstFrom
    rw [if_neg hc]
    change TableGeneration.run?
      (TableGeneration.addConstAuxFuel dst src (decide (c < 0))
        (Int.natAbs c + 1) (Int.natAbs c) 0) sigma = _
    rw [addConstAuxFuel_run dst src (decide (c < 0))
      (Int.natAbs c + 1) (Int.natAbs c) 0 sigma hsep (by omega)]
    congr 1
    funext i j
    by_cases hi : i = dst
    · subst i
      simp only [TableGeneration.State.setReg, ↓reduceIte, pow_zero, mul_one]
      rw [signed_natAbs]
    · simp [TableGeneration.State.setReg, hi]

theorem addConstAuxFuel_addOnly {k : Nat} (dst src : Fin k) (negSrc : Bool)
    (fuel n shift : Nat) (hsep : dst ≠ src) :
    ∀ op ∈ TableGeneration.addConstAuxFuel dst src negSrc fuel n shift,
      ∃ (d s : Fin k) (b : Bool) (sh : Nat),
        op = .addScaled d s b sh ∧ d ≠ s := by
  induction fuel generalizing n shift with
  | zero => simp [TableGeneration.addConstAuxFuel]
  | succ fuel ih =>
      cases n with
      | zero => simp [TableGeneration.addConstAuxFuel]
      | succ n =>
          by_cases ho : (n + 1) % 2 = 1
          · simp only [TableGeneration.addConstAuxFuel, ho, ↓reduceIte,
              List.mem_cons]
            intro op hop
            rcases hop with heq | hrest
            · subst op
              exact ⟨dst, src, negSrc, shift, rfl, hsep⟩
            · exact ih ((n + 1) / 2) (shift + 1) op hrest
          · simp only [TableGeneration.addConstAuxFuel, ho, ↓reduceIte]
            exact ih ((n + 1) / 2) (shift + 1)

theorem addConstFrom_addOnly {k : Nat} (dst src : Fin k) (c : Int)
    (hsep : dst ≠ src) :
    ∀ op ∈ TableGeneration.addConstFrom dst src c,
      ∃ (d s : Fin k) (b : Bool) (sh : Nat),
        op = .addScaled d s b sh ∧ d ≠ s := by
  by_cases hc : c = 0
  · simp [TableGeneration.addConstFrom, hc]
  · simp only [TableGeneration.addConstFrom, hc, ↓reduceIte]
    exact addConstAuxFuel_addOnly dst src _ _ _ _ hsep

theorem addOnly_safe {k : Nat} (w : TableGeneration.Prog k)
    (h : ∀ op ∈ w, ∃ (d s : Fin k) (b : Bool) (sh : Nat),
      op = .addScaled d s b sh ∧ d ≠ s) :
    TableGeneration.safeProg? w = true := by
  induction w with
  | nil => rfl
  | cons op ops ih =>
      obtain ⟨d, s, b, sh, heq, hsep⟩ := h op (by simp)
      subst op
      have ht : TableGeneration.safeProg? ops = true :=
        ih (by intro x hx; exact h x (by simp [hx]))
      change TableGeneration.Prog.wellFormed? ops = true at ht
      simpa [TableGeneration.safeProg?, TableGeneration.Prog.wellFormed?,
        TableGeneration.Prog.OpOK?, hsep] using ht

theorem addConstAuxFuel_safe {k : Nat} (dst src : Fin k) (negSrc : Bool)
    (fuel n shift : Nat) (hsep : dst ≠ src) :
    TableGeneration.safeProg?
      (TableGeneration.addConstAuxFuel dst src negSrc fuel n shift) = true :=
  addOnly_safe _ (addConstAuxFuel_addOnly dst src negSrc fuel n shift hsep)

theorem addConstFrom_safe {k : Nat} (dst src : Fin k) (c : Int)
    (hsep : dst ≠ src) :
    TableGeneration.safeProg? (TableGeneration.addConstFrom dst src c) = true :=
  addOnly_safe _ (addConstFrom_addOnly dst src c hsep)

theorem run_append {k : Nat} (w v : TableGeneration.Prog k)
    (sigma : TableGeneration.State k) :
    TableGeneration.run? (w ++ v) sigma =
      (TableGeneration.run? w sigma).bind (TableGeneration.run? v) := by
  induction w generalizing sigma with
  | nil => rfl
  | cons op ops ih =>
      simp only [List.cons_append, TableGeneration.run?]
      cases h : TableGeneration.applyOp? sigma op with
      | none => simp [h]
      | some sigma1 => simpa [h] using ih sigma1

theorem addScaled_inverse_state {k : Nat} (sigma : TableGeneration.State k)
    (dst src : Fin k) (negSrc : Bool) (shift : Nat) (hsep : dst ≠ src) :
    TableGeneration.State.addScaledReg
      (TableGeneration.State.addScaledReg sigma dst src negSrc shift)
      dst src (!negSrc) shift = sigma := by
  funext i j
  by_cases hi : i = dst
  · subst i
    have hs : src ≠ dst := Ne.symm hsep
    cases negSrc <;>
      simp [TableGeneration.State.addScaledReg, TableGeneration.State.setReg,
        TableGeneration.Register.addScaled, hs] <;> ring
  · simp [TableGeneration.State.addScaledReg, TableGeneration.State.setReg, hi]

theorem inverse_addOnly {k : Nat} (w : TableGeneration.Prog k)
    (h : ∀ op ∈ w, ∃ (d s : Fin k) (b : Bool) (sh : Nat),
      op = .addScaled d s b sh ∧ d ≠ s) :
    ∀ op ∈ TableGeneration.apply_Op_inverse w,
      ∃ (d s : Fin k) (b : Bool) (sh : Nat),
        op = .addScaled d s b sh ∧ d ≠ s := by
  intro op hop
  simp only [TableGeneration.apply_Op_inverse, List.mem_map] at hop
  obtain ⟨q, hq, heq⟩ := hop
  have hmem : q ∈ w := List.mem_reverse.mp hq
  obtain ⟨d, s, b, sh, hqeq, hsep⟩ := h q hmem
  subst q
  subst op
  exact ⟨d, s, !b, sh, rfl, hsep⟩

theorem inverse_addOnly_safe {k : Nat} (w : TableGeneration.Prog k)
    (h : ∀ op ∈ w, ∃ (d s : Fin k) (b : Bool) (sh : Nat),
      op = .addScaled d s b sh ∧ d ≠ s) :
    TableGeneration.safeProg? (TableGeneration.apply_Op_inverse w) = true :=
  addOnly_safe _ (inverse_addOnly w h)

theorem run_inverse_addOnly {k : Nat} (w : TableGeneration.Prog k)
    (sigma sigma' : TableGeneration.State k)
    (h : ∀ op ∈ w, ∃ (d s : Fin k) (b : Bool) (sh : Nat),
      op = .addScaled d s b sh ∧ d ≠ s)
    (hr : TableGeneration.run? w sigma = some sigma') :
    TableGeneration.run? (TableGeneration.apply_Op_inverse w) sigma' =
      some sigma := by
  induction w generalizing sigma sigma' with
  | nil =>
      simp [TableGeneration.run?] at hr
      subst sigma'
      rfl
  | cons op ops ih =>
      obtain ⟨d, s, b, sh, heq, hsep⟩ := h op (by simp)
      subst op
      have ht : ∀ q ∈ ops, ∃ (d s : Fin k) (b : Bool) (sh : Nat),
          q = .addScaled d s b sh ∧ d ≠ s := by
        intro q hq
        exact h q (by simp [hq])
      let sigma1 := TableGeneration.State.addScaledReg sigma d s b sh
      have hrest : TableGeneration.run? ops sigma1 = some sigma' := by
        simpa [TableGeneration.run?, TableGeneration.applyOp?, sigma1] using hr
      have hi := ih sigma1 sigma' ht hrest
      simp only [TableGeneration.apply_Op_inverse, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil]
      rw [run_append]
      change (TableGeneration.run? (TableGeneration.apply_Op_inverse ops) sigma').bind
        (TableGeneration.run? [TableGeneration.Operations.inv
          (.addScaled d s b sh)]) = some sigma
      rw [hi]
      change some (TableGeneration.State.addScaledReg sigma1 d s (!b) sh) = some sigma
      rw [show TableGeneration.State.addScaledReg sigma1 d s (!b) sh = sigma from
        addScaled_inverse_state sigma d s b sh hsep]

end Paper.BaselineArithmetic
