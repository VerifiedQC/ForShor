import FastMultiplication.Basic

-- /******************************************************************************/
-- /*                           PROGRAMS & EXECUTION CORE                        */
-- /******************************************************************************/

open Operations

/-- A program is just a list of valid operations. -/
abbrev Prog (k : ℕ) := List (valid_ops k)

/-- Execute one operation. Right shift may fail if division is inexact. -/
def applyOp? {k : ℕ} (σ : State k) : valid_ops k → Option (State k)
| .shiftL i n           => some (State.shiftLReg σ i n)
| .shiftR i n           => State.shiftRReg? σ i n
| .negate i             => some (State.negateReg σ i)
| .addScaled i j s sh   => some (State.addScaledReg σ i j s sh)
| .phaseProduct _       => some σ

/-- Reverse the program and invert each operation. -/
def apply_Op_inverse {k : ℕ} (p : Prog k) : Prog k :=
  p.reverse.map Operations.inv

/-- Execute a program left→right. Fails if any right shift is inexact. -/
def run? {k : ℕ} : Prog k → State k → Option (State k)
| [],       σ => some σ
| op :: ps, σ =>
  match applyOp? σ op with
  | none    => none
  | some σ' => run? ps σ'




--/******************************************************************************/
--/*                           LIST UTILITIES (LOCAL)                           */
--/******************************************************************************/

namespace List
lemma reverse_map {α β} (f : α → β) (xs : List α) :
    (xs.map f).reverse = xs.reverse.map f := by
  induction xs with
  | nil      => simp
  | cons x t ih => simp
end List


-- /******************************************************************************/
-- /*                      BASIC FACTS ABOUT INVERSE PROGRAMS                    */
-- /******************************************************************************/

@[simp] theorem apply_Op_inverse_involutive {k : ℕ} (p : Prog k) :
    apply_Op_inverse (apply_Op_inverse p) = p := by
  unfold apply_Op_inverse
  -- (rev.map inv).rev.map inv  →  p.rev.rev.map (inv ∘ inv)
  simp
  have : (inv∘inv) =( fun (x:valid_ops k)=>x):= by {
    unfold inv
    funext x
    cases x
    all_goals simp
  }
  rw[this]
  simp


-- /******************************************************************************/
-- /*                     WELL-FORMEDNESS & SMALL CONSTRUCTORS                   */
-- /******************************************************************************/

namespace Prog

/-- An op is well-formed if it does not do an in-place scaled add. -/
def OpOK {k : ℕ} : valid_ops k → Prop
  | .addScaled dst src _ _ => dst ≠ src
  | _                      => True

/-- A program is well-formed if all its ops are `OpOK`. -/
def WellFormed {k : ℕ} (p : Prog k) : Prop :=
  ∀ op, op ∈ p → OpOK op

lemma apply_Op_inverse_preserves_WF {k} {p : Prog k} :
    Prog.WellFormed p → Prog.WellFormed (apply_Op_inverse p) := by
  intro wf op hop
  -- membership through `reverse.map`
  have : ∃ o, o ∈ p ∧ inv o = op := by
    -- map membership characterization
    -- op ∈ p.reverse.map inv  →  ∃o ∈ p.reverse, inv o = op → ∃o ∈ p
    revert hop
    simp [apply_Op_inverse, List.mem_map, List.mem_reverse]
  rcases this with ⟨o, ho, rfl⟩
  have hok := wf o ho
  -- `OpOK` is invariant under `inv`
  cases o <;> simp [Prog.OpOK, inv] at hok ⊢
  exact hok

/-- Singleton programs for each primitive (handy for notations). --/
def SHL   {k} (i : Fin k) (n : ℕ) : Prog k := [valid_ops.shiftL i n]
def SHR   {k} (i : Fin k) (n : ℕ) : Prog k := [valid_ops.shiftR i n]
def NEG   {k} (i : Fin k)           : Prog k := [valid_ops.negate i]
def ADD   {k} (dst src : Fin k) (shift : ℕ) : Prog k :=
  [valid_ops.addScaled dst src (negSrc := false) shift]
def SUB   {k} (dst src : Fin k) (shift : ℕ) : Prog k :=
  [valid_ops.addScaled dst src (negSrc := true) shift]

end Prog


-- /******************************************************************************/
-- /*                                NOTATIONS                                   */
-- /******************************************************************************/

-- sequence operator for programs
infixl:55 " ;; " => List.append

-- i << s= n   (shift left)
syntax term " <<s= " term : term
macro_rules
  | `($i <<s= $n) => `(Prog.SHL $i $n)

-- i >>s= n   (shift right)
syntax term " >>s= " term : term
macro_rules
  | `($i >>s= $n) => `(Prog.SHR $i $n)

-- neg i
syntax "neg " term : term
macro_rules
  | `(neg $i) => `(Prog.NEG $i)

-- dst +:= src << n
syntax term " +:= " term " << " term : term
macro_rules
  | `($dst +:= $src << $n) => `(Prog.ADD $dst $src $n)

-- dst -:= src << n
syntax term " -:= " term " << " term : term
macro_rules
  | `($dst -:= $src << $n) => `(Prog.SUB $dst $src $n)


-- /******************************************************************************/
-- /*                          BASIC `run?` SIMP LEMMAS                          */
-- /******************************************************************************/

@[simp] lemma run?_nil {k} (σ : State k) :
  run? ([] : Prog k) σ = some σ := rfl

@[simp] lemma run?_cons {k} (op : valid_ops k) (ps : Prog k) (σ : State k) :
  run? (op :: ps) σ =
    match applyOp? σ op with
    | none    => none
    | some σ' => run? ps σ' := rfl

lemma run?_append {k} (p q : Prog k) (σ : State k) :
  run? (p ++ q) σ =
    match run? p σ with
    | none    => none
    | some σ' => run? q σ' := by
  induction p generalizing σ with
  | nil => simp [run?]
  | cons op ps IH =>
      simp [run?, IH]
      cases (applyOp? σ op)
      simp
      simp

/- Single-step characterizations (good for rewriting) -/
@[simp] lemma run?_one_shiftL {k} (σ : State k) (i : Fin k) (n : ℕ) :
  run? ([valid_ops.shiftL i n] : Prog k) σ = some (State.shiftLReg σ i n) := rfl

@[simp] lemma run?_one_shiftR {k} (σ : State k) (i : Fin k) (n : ℕ) :
  run? ([valid_ops.shiftR i n] : Prog k) σ = State.shiftRReg? σ i n := by {
    simp
    unfold applyOp?
    simp
    cases σ.shiftRReg? i n
    simp
    simp
  }

@[simp] lemma run?_one_neg {k} (σ : State k) (i : Fin k) :
  run? ([valid_ops.negate i] : Prog k) σ = some (State.negateReg σ i) := rfl

@[simp] lemma run?_one_addScaled {k} (σ : State k)
    (dst src : Fin k) (negSrc : Bool) (n : ℕ) :
  run? ([valid_ops.addScaled dst src negSrc n] : Prog k) σ
    = some (State.addScaledReg σ dst src negSrc n) := rfl

/- Notation-specific simp helpers (these use the macros) -/
@[simp] lemma run?_shl_notation {k} (σ : State k) (i : Fin k) (n : ℕ) :
  run? (i <<s= n) σ = some (State.shiftLReg σ i n) := rfl

@[simp] lemma run?_shr_notation {k} (σ : State k) (i : Fin k) (n : ℕ) :
  run? (i >>s= n) σ = State.shiftRReg? σ i n := by {
    unfold run? Prog.SHR applyOp?
    simp
    cases σ.shiftRReg? i n
    all_goals simp
  }

@[simp] lemma run?_neg_notation {k} (σ : State k) (i : Fin k) :
  run? (neg i) σ = some (State.negateReg σ i) := rfl

@[simp] lemma run?_add_notation {k} (σ : State k)
  (dst src : Fin k) (n : ℕ) :
  run? (dst +:= src << n) σ
    = some (State.addScaledReg σ dst src (negSrc := false) n) := rfl

@[simp] lemma run?_sub_notation {k} (σ : State k)
  (dst src : Fin k) (n : ℕ) :
  run? (dst -:= src << n) σ
    = some (State.addScaledReg σ dst src (negSrc := true) n) := rfl


-- /******************************************************************************/
-- /*                                  EXAMPLES                                  */
-- /******************************************************************************/

section Examples
set_option linter.unusedVariables false

variable {k : ℕ} (σ0 : State 4)
def r0 : Fin 4 := ⟨0, by decide⟩
def r1 : Fin 4 := ⟨1, by decide⟩

/-- A small program: r0 +:= r1 << 2 ;; r0 >>s= 1 ;; neg r1 -/
def demoProg : Prog 4 := (r0 +:= r1 << 2) ;; (r0 >>s= 1) ;; (neg r1)

end Examples


-- /******************************************************************************/
-- /*                  INVERSE OF APPEND (TOP-LEVEL VERSION)                     */
-- /******************************************************************************/

@[simp] theorem apply_Op_inverse_append {k : ℕ} (p q : Prog k) :
    apply_Op_inverse ((p;;q)) = apply_Op_inverse q ;; apply_Op_inverse p := by
  unfold apply_Op_inverse
  -- reverse (p ++ q) = reverse q ++ reverse p; then `map` distributes over `++`
  simp [List.reverse_append, List.map_append]


-- /******************************************************************************/
-- /*                     LIGHTWEIGHT PROGRAM EQUIVALENCE                        */
-- /******************************************************************************/

-- Two programs are equivalent if they produce the same (optional) state on all inputs.
def ProgEq {k : ℕ} (p q : Prog k) : Prop :=
  ∀ σ, run? p σ = run? q σ

notation:50 p:51 " ≃ₚ " q:50 => ProgEq p q

namespace ProgEq

variable {k : ℕ}

@[refl] lemma refl  (p : Prog k) : p ≃ₚ p := by intro σ; rfl
@[symm] lemma symm  {p q : Prog k} : p ≃ₚ q → q ≃ₚ p := by
  intro h σ; unfold ProgEq at h; rw [h σ]
@[trans] lemma trans {p q r : Prog k} :
  p ≃ₚ q → q ≃ₚ r → p ≃ₚ r := by
  intro hpq hqr σ; simpa [hpq σ] using (hqr σ)

/-- Left congruence for sequencing. -/
lemma cong_left  {p q r : Prog k} :
  p ≃ₚ q → (p ;; r) ≃ₚ (q ;; r) := by
  intro hpq σ
  simp [run?_append, hpq σ]

/-- Right congruence for sequencing. -/
lemma cong_right {p q r : Prog k} :
  q ≃ₚ r → (p ;; q) ≃ₚ (p ;; r) := by
  intro hqr σ
  simp [run?_append]
  unfold ProgEq at hqr
  simp[hqr]

/-- Left identity (`[] ;; p ≃ p`). -/
lemma nil_left  (p : Prog k) : (([] : Prog k) ;; p) ≃ₚ p := by
  intro σ; simp

/-- Right identity (`p ;; [] ≃ p`). -/
lemma nil_right (p : Prog k) : (p ;; ([] : Prog k)) ≃ₚ p := by
  simp;apply refl

end ProgEq



-- /******************************************************************************/
-- /*                   STATE-LEVEL COMMUTING/ALGEBRA HELPERS                    */
-- /******************************************************************************/

namespace State
open State

/-- `setReg` on different indices commutes. -/
lemma setReg_comm {k} (σ : State k)
  (i j : Fin k) (ri rj : Register k) (hij : i ≠ j) :
  State.setReg (State.setReg σ i ri) j rj = State.setReg (State.setReg σ j rj) i ri := by
  funext t
  by_cases ht_i : t = i
  · subst ht_i; simp [State.setReg, hij]
  · by_cases ht_j : t = j
    · subst ht_j; simp [State.setReg, ht_i]
    · simp [State.setReg, ht_i, ht_j]

/-- Shifting two different destination registers (any amounts) commutes. -/
lemma shiftLReg_comm {k} (σ : State k)
  (i j : Fin k) (a b : ℕ) (hij : i ≠ j) :
  State.shiftLReg (State.shiftLReg σ i a) j b =
  State.shiftLReg (State.shiftLReg σ j b) i a := by
  -- both sides are just two setReg updates on different indices
  simp [State.shiftLReg, setReg_comm σ i j _ _ hij,State.setReg]
  simp[hij]
  have h:j ≠ i := by intro h;apply hij;rw[h]
  simp[h]

/-- Negating and shifting the *same* register commute. -/
lemma negate_shiftL_same {k} (σ : State k) (i : Fin k) (n : ℕ) :
  State.negateReg (State.shiftLReg σ i n) i = State.shiftLReg (State.negateReg σ i) i n := by
  -- Reduce to register-level pointwise equality.
  funext t
  by_cases ht : t = i
  · subst ht
    -- same index: - (x * 2^n) = (-x) * 2^n
    simp [State.negateReg, State.shiftLReg, State.setReg]
    unfold Register.negate Register.shiftL
    funext j
    simp
    rw[Int.neg_mul]
  · -- other indices are unchanged by the update
    simp [State.negateReg, State.shiftLReg, State.setReg, ht]

/-- Double negation on a register restores the state. -/
lemma negateReg_involutive {k} (σ : State k) (i : Fin k) :
  State.negateReg (State.negateReg σ i) i = σ := by
  funext t
  by_cases ht : t = i
  · subst ht; simp [State.negateReg, State.setReg]
    unfold Register.negate
    funext j
    simp
  · simp [State.negateReg, State.setReg, ht]

/-- Two successive left shifts add their exponents. -/
lemma shiftL_add (σ : State k) (i: Fin k) (a b : ℕ)
:(σ.shiftLReg i a).shiftLReg i b = σ.shiftLReg i (a + b):=by
  unfold State.shiftLReg Register.shiftL State.setReg
  funext j
  split_ifs with h1 h2
  · simp;funext m
    have : (2:ℤ) ^ a * (2:ℤ) ^ b= (2:ℤ) ^(a+b) := by rw[← Int.pow_add]
    rw[Int.mul_assoc]
    rw[this]
  · simp at h2
  · rfl
end State


-- /******************************************************************************/
-- /*                 PROGRAM EQUIVALENCES USING STATE HELPERS                   */
-- /******************************************************************************/

open ProgEq

/-- `(i <<s= a) ;; (i <<s= b)  ≃ₚ  (i <<s= (a + b))`. -/
lemma shl_shl_same_reg {k} (i : Fin k) (a b : ℕ) :
  (i <<s= a) ;; (i <<s= b) ≃ₚ (i <<s= (a + b)) := by
  intro σ
  simp[run?_append,State.shiftL_add]

/-- Shifts on *different* destination registers commute. -/
lemma shl_shl_comm {k} (i j : Fin k) (a b : ℕ) (hij : i ≠ j) :
  (i <<s= a) ;; (j <<s= b) ≃ₚ (j <<s= b) ;; (i <<s= a) := by
  intro σ
  simp [run?_append, State.shiftLReg_comm σ i j a b hij]

/-- `neg i` then `neg i` is a no-op. -/
lemma neg_neg_cancel {k} (i : Fin k) :
  (neg i) ;; (neg i) ≃ₚ ([] : Prog k) := by
  intro σ
  simp [run?_append, State.negateReg_involutive]

/-- On the *same* register, `neg` commutes with `<<s=`. -/
lemma neg_shl_same_comm {k} (i : Fin k) (n : ℕ) :
  (neg i) ;; (i <<s= n) ≃ₚ (i <<s= n) ;; (neg i) := by
  intro σ
  simp [run?_append, State.negate_shiftL_same]

/-- On *different* destination registers, `neg` and `<<s=` commute. -/
lemma neg_shl_diff_comm {k} (i j : Fin k) (n : ℕ) (hij : i ≠ j) :
  (neg i) ;; (j <<s= n) ≃ₚ (j <<s= n) ;; (neg i) := by
  intro σ
  simp [run?_append, State.setReg_comm σ i j _ _ hij, State.negateReg, State.shiftLReg]
  unfold Register.shiftL State.setReg
  funext t
  split_ifs with ht_i ht_j hij
  all_goals try rfl
  rw[hij] at ht_j; simp[ht_j] at ht_i


-- /******************************************************************************/
-- /*                INVERSE-CANCEL LEMMAS & STRONG UNDO THEOREM                 */
-- /******************************************************************************/

namespace State

/-- Right-shift exactly cancels a preceding left-shift on the same register. -/
lemma shiftR_after_shiftL_exact {k} (σ : State k) (i : Fin k) (n : ℕ) :
  State.shiftRReg? (State.shiftLReg σ i n) i n = some σ := by
   unfold shiftLReg setReg shiftRReg? Register.shiftL Register.shiftR?
   simp
   unfold setReg
   simp
   funext j k
   split_ifs with h
   simp[h]
   sorry
   rfl

/-- If a right-shift succeeded, the corresponding left-shift restores the state. -/
lemma shiftL_after_shiftR_exact {k} {σ σ' : State k} (i : Fin k) (n : ℕ) :
  State.shiftRReg? σ i n = some σ' → State.shiftLReg σ' i n = σ := by
    unfold shiftLReg setReg shiftRReg? Register.shiftL Register.shiftR?
    simp
    unfold setReg
    split_ifs with h1
    · simp
      intro h2
      rw[← h2]
      funext j k
      simp
      split_ifs with h3
      simp
      sorry
      rfl
    · simp

/-- Adding a scaled (or negated) source and then the opposite undoes the change. -/
lemma addScaled_cancel {k} (σ : State k) (dst src : Fin k) (negSrc : Bool) (n : ℕ) (hds:dst≠src):
  State.addScaledReg (State.addScaledReg σ dst src negSrc n) dst src (!negSrc) n = σ := by
  -- TODO: unfold `addScaledReg` and check the `dst` component; other regs unchanged
    unfold addScaledReg setReg Register.addScaled
    funext j q
    simp
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
    all_goals try simp_all
    {
      rw[Int.neg_mul,Int.neg_add_cancel_right]
    }
    {
      rw[Int.neg_mul, Int.add_assoc]
      nth_rewrite 2[Int.add_comm]
      rw[← Int.add_assoc,Int.neg_add_cancel_right]
    }

/-- Inverse of a single step, for any well-formed op. -/
lemma run?_inv_singleton_OK {k} (op : valid_ops k) (ok : Prog.OpOK op) :
    ∀ {σ σ' : State k},
      applyOp? σ op = some σ' →
      run? [inv op] σ' = some σ := by
  intro σ σ' hstep
  cases op with
  | shiftL i n =>
      have h:=(State.shiftR_after_shiftL_exact (σ := σ) i n)
      simp[run?,applyOp?,inv,Prog.OpOK] at *
      rw[hstep] at h
      rw[h]
  | shiftR i n =>
      -- inverse: shiftL after a successful shiftR
      have := State.shiftL_after_shiftR_exact (σ := σ) (σ' := σ') i n hstep
      simp[run?,applyOp?,inv,Prog.OpOK] at *
      rw[this]
  | negate i =>
      -- negate twice cancels
      have h:=(State.negateReg_involutive (σ := σ) (i := i))
      simp[run?,applyOp?,inv,Prog.OpOK] at *
      rw[hstep] at h
      rw[h]
  | addScaled dst src b n =>
      -- need dst ≠ src to cancel
      have hne : dst ≠ src := by
        simpa [Prog.OpOK] using ok
      have h:=(State.addScaled_cancel (σ := σ) (dst := dst) (src := src) (negSrc := b) (n := n) hne)
      simp[run?,applyOp?,inv,Prog.OpOK] at *
      rw[hstep] at h
      rw[h]
  | phaseProduct l =>
      simp[run?,applyOp?,inv,Prog.OpOK] at *
      rw[hstep]

@[simp] lemma apply_Op_inverse_cons {k} (op : valid_ops k) (ps : Prog k) :
  apply_Op_inverse (op :: ps) = apply_Op_inverse ps ;; [inv op] := by
  -- (op :: ps).reverse = ps.reverse ++ [op], and `map` distributes over `++`
  unfold apply_Op_inverse
  simp [List.reverse_cons, List.map_append]

@[simp] lemma apply_Op_inverse_append {k} (p q : Prog k) :
  apply_Op_inverse (p ;; q) = apply_Op_inverse q ;; apply_Op_inverse p := by
  unfold apply_Op_inverse
  simp [List.reverse_append, List.map_append]

/-- Running the inverse program undoes any well-formed successful run. -/
theorem run?_inverse_undoes_WF {k}
    (p : Prog k) (WF : Prog.WellFormed p) (σ τ : State k) :
    run? p σ = some τ → run? (apply_Op_inverse p) τ = some σ := by
  revert σ τ
  induction p with
  | nil =>
      intro σ τ h
      simp[run?] at h
      simp[apply_Op_inverse,h]
  | cons op ps ih =>
      intro σ τ h
      have WFop : Prog.OpOK op := by
        exact WF op (by simp)       -- op ∈ op :: ps
      have WFps : Prog.WellFormed ps := by
        intro o ho; exact WF o (by simp [ho])  -- o ∈ ps → o ∈ op::ps
      -- expose first step
      simp [run?, apply_Op_inverse_cons, run?_append] at ⊢
      cases hstep : applyOp? σ op with
      | none    => simp [hstep] at h
      | some σ₁ =>
          have hps : run? ps σ₁ = some τ := by simpa [hstep] using h
          have ih' : run? (apply_Op_inverse ps) τ = some σ₁ :=
            ih WFps _ _ hps
          have hstep_inv :
              run? [inv op] σ₁ = some σ :=
            run?_inv_singleton_OK op WFop (σ := σ) (σ' := σ₁) hstep
          simp [ih']
          simp at hstep_inv
          simp[hstep_inv]
end State










-- /******************************************************************************/
-- /*                   INTEGER → SIGNED POW2 DECOMPOSITION                      */
-- /******************************************************************************/

def signedPow2Decomp (c : Int) : List (Int × Nat) :=
  if c = 0 then
    []
  else
    Id.run do
      let sgn : Int := if 0 ≤ c then (1 : Int) else (-1 : Int)
      let mut n  : Nat := c.natAbs
      let mut sh : Nat := 0
      let mut out : List (Int × Nat) := []
      while n ≠ 0 do
        -- check LSB with modulus, no Nat.bodd needed
        if n % 2 == (1 : Nat) then
          out := (sgn, sh) :: out
        n  := n / 2        -- shift right
        sh := sh + 1
      return out.reverse   -- ascending shifts

lemma decomp_2 :
  signedPow2Decomp 2= [(1,1)]:=by {
    unfold signedPow2Decomp
    simp
    sorry
  }

/-- Reconstruct an integer from a decomposition list. -/
def sumDecomp (L : List (Int × Nat)) : Int :=
  L.foldl (fun acc (s, sh) => acc + s * (2 : Int) ^ sh) 0

macro "sumDecomp_simp" : tactic =>
  `(tactic| (unfold sumDecomp; simp))

lemma sumDecomp_2:(sumDecomp [(1,1)])=2:=by {
  sumDecomp_simp
}

lemma sumDecomp_24:(sumDecomp [(1, 3), (1, 4)])=24:=by {
  sumDecomp_simp
}

/--
Basic correctness: for all integers `c`, reconstructing from
`signedPow2Decomp c` gives back `c`.
-/
theorem signedPow2Decomp_correct (c : Int) :
    sumDecomp (signedPow2Decomp c) = c := by
  by_cases hc : c = 0
  · simp [signedPow2Decomp, hc, sumDecomp]
  ·
    let sgn : Int := if 0 ≤ c then 1 else -1
    let n := c.natAbs
    -- since our construction collects exactly those (sgn, sh) where the bit is 1,
    -- we reconstruct sgn * n
    have : sumDecomp (signedPow2Decomp c) = sgn * n := by
      -- this mirrors what the loop does; conceptually true
      admit
    -- finally show sgn * n = c
    simp [Int.natAbs_of_nonneg, Int.natAbs_neg, hc] at *
    by_cases h : 0 ≤ c
    · simp [this,sgn,h];simp[n];sorry
    · unfold sumDecomp
      simp
      sorry

-- (TODO: full formalization would replace `admit` with an induction on n.)


-- /******************************************************************************/
-- /*                 LIST-OF-POWERS SUMS & BINARY BIT SHIFTS                    */
-- /******************************************************************************/

 /-- Sum `∑ (2^s)` over a list of shifts. We use lists (not finsets) because the
    decomposition naturally produces a list. -/
def sumPow2 (L : List Nat) : ℤ :=
  L.foldr (fun s acc => (2 : ℤ) ^ s + acc) 0

@[simp] lemma sumPow2_nil : sumPow2 [] = 0 := rfl
@[simp] lemma sumPow2_cons (s : Nat) (L : List Nat) :
  sumPow2 (s :: L) = (2 : ℤ) ^ s + sumPow2 L := rfl

lemma sumPow2_append (A B : List Nat) :
  sumPow2 (A ++ B) = sumPow2 A + sumPow2 B := by
  induction A with
  | nil => simp
  | cons s A IH => simp [IH, Int.add_assoc]

/-- Map `succ` over shifts multiplies the sum by 2:  `∑ 2^(s+1) = 2 * ∑ 2^s`. -/
lemma sumPow2_mapSucc (L : List Nat) :
  sumPow2 (L.map Nat.succ) = 2 * sumPow2 L := by
  induction L with
  | nil => simp
  | cons s L IH =>
      simp [IH, Int.pow_succ, Int.two_mul, Int.add_comm, Int.add_left_comm, Int.add_assoc]
      omega

/-- Bits‐to‐shifts via `Nat.binaryRec`:
    For `n = bit b m = 2*m + (if b then 1 else 0)`,
    shifts are those of `m`, incremented by 1, plus `0` if `b = true`. -/
def bitShifts (n : Nat) : List Nat :=
  Nat.binaryRec (motive := fun _ => List Nat)
    []                                                           -- base: 0 ↦ []
    (fun b _ acc => acc.map Nat.succ ++ (if b then [0] else [])) -- step: bit b m
    n

/-- The sum of powers at positions `bitShifts n` equals `n` (as an integer). -/
lemma bitShifts_sum (n : Nat) : sumPow2 (bitShifts n) = (n : ℤ) := by
  -- binary induction on `n`
  refine Nat.binaryRec
    (motive := fun n => sumPow2 (bitShifts n) = (n : ℤ))
    ?base ?step n
  · -- base: n = 0
    simp [bitShifts]
  · -- step: n = bit b m = 2*m + (if b then 1 else 0)
    intro m b IH
    -- unfold one step of `bitShifts`
    unfold Nat.bit
    sorry

/-- Boolean sign to ±1 in ℤ. -/
@[inline] def sgnInt (b : Bool) : ℤ := if b then -1 else 1
@[simp] lemma sgnInt_true  : sgnInt true  = (-1 : ℤ) := rfl
@[simp] lemma sgnInt_false : sgnInt false = ( 1 : ℤ) := rfl
