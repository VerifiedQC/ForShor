import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Layout

/-!
# Phase-Product Compiler: the exact working width

The recursive phase product grows every limb slot to one common working width
before running a table. The original compiler chose that width with a symbolic
scan (`scanNeededWidthsAux`, kept in `Widths.lean` as `foldNeededWidths`): one
bit more at every `addScaled` and `negate`, whether or not the value grows.
That is sufficient, not necessary.

This file defines the **exact** width, from the values the table can actually
produce, and the integer-level facts about it. `Widths.lean` makes it the width
the compiler uses; `Proofs/Compiler/WidthSoundness.lean` proves the lowering's
fit obligation from it; `Proofs/Compiler/ExactWidthBound.lean` proves it never
exceeds the scan and characterises it as least.

## The model

A register of the table holds an integer row `r : Register k`; read on the
operand's limbs `L : Fin k → ℤ` it is `rowVal r L = ∑ⱼ r j * L j` (exactly how
`evalRowX`/`evalRowZ` read a row against the basis: lower chunks as unsigned
digits, the top chunk as signed, `Proofs/Compiler/Support.lean`). The limbs of
an operand of active width `w`, split at lower-limb width `W`, range over the
box `exactLimbLo w W ≤ L ≤ exactLimbHi w W`: chunk `j` has the logical width
`t = phaseSplitLogicalWidth w W k j` of the compiler's own split; a lower chunk
is unsigned (`[0, 2^t - 1]`), the top chunk is signed (`[-2^(t-1), 2^(t-1) - 1]`,
and `[0, 0]` when `t = 0`, as `tcDecodeWidth 0` reads it).

Over a box a row ranges over `[rowLo, rowHi]` (coordinatewise min/max), both
ends attained at a corner. A signed `E`-bit register holds the row iff
`rowDemand ≤ 2^(E-1)`, `rowDemand = max(-rowLo, rowHi + 1)`.

* `exactReachRows ops`: every row of every state the program visits from
  `State.start_state` (the state before each operation and the final one).
  Every state a prefix reaches is visited (`mem_exactReachStates`), so every
  checkpoint operand and every intermediate value is covered.
* `tightSignedWidthOfWidths ops xw zw`: `1 + ⌈log₂ D⌉`, `D` the largest demand
  over the reachable rows on both operands' boxes (lower-limb width
  `W = min (xw / k) (zw / k)`, as `phaseLimbWidth`). The least `E` holding every
  reachable value at every point of the limb box (`ExactWidthBound.lean`, `tightSignedWidth_le_iff`).
* `floorSignedWidthOfWidths k xw zw`: `1 +` the widest initial chunk, i.e.
  `commonNeededWidth` of the initial width state. ForShor's allocation
  (`allocChunkGate`, `Proofs/Compiler/Allocation.lean` `extraDelta_xslot_pos`)
  grows **every** slot by at least one bit; the floor keeps that invariant, so
  the allocation proofs are unchanged.
* `exactSignedWidthOfWidths ops xw zw = max tight floor`: the width the
  compiler now uses (`Widths.lean`). For a Toom-Cook table at a width where the
  lower limbs are non-empty the floor is never binding (a point other than `0`
  and `∞` gives a row with every coefficient non-zero, whose demand already
  exceeds the top chunk's), but that is not used anywhere: the definition is
  the `max`, and agreement with STO's `tightWidth` is checked, not assumed.

Everything is computable. `exactTab` re-tabulates each visited state into
arrays, so a row entry costs one lookup instead of re-walking the chain of
`addScaled` closures (which branches two ways per `addScaled`).
-/

namespace Shor
open Operations
open scoped BigOperators

/-! ## Tabulation (an evaluation device, extensionally the identity) -/

/-- `σ`, with every entry computed once into arrays. -/
def exactTab {k : ℕ} (σ : State k) : State k :=
  let a : Array (Array ℤ) := Array.ofFn fun i => Array.ofFn (σ i)
  fun i j => (a.getD i.1 #[]).getD j.1 0

theorem exactTab_eq {k : ℕ} (σ : State k) : exactTab σ = σ := by
  funext i j
  simp [exactTab, Array.getD_eq_getD_getElem?]

/-! ## The states and rows a program visits -/

/-- The states a run visits: the state before each operation and the final one.
Stops at an inexact right shift (where `run?` fails); a table satisfying C4 has
none. -/
def exactReachStates {k : ℕ} : State k → Prog k → List (State k)
  | σ, [] => [σ]
  | σ, op :: ops =>
      σ :: (match applyOp? σ op with
        | none => []
        | some σ' => exactReachStates (exactTab σ') ops)

/-- Every state a prefix of the program reaches is visited. -/
theorem mem_exactReachStates {k : ℕ} :
    ∀ (pre rest : Prog k) (σ0 σ : State k),
      run? pre σ0 = some σ → σ ∈ exactReachStates σ0 (pre ++ rest)
  | [], rest, σ0, σ, h => by
      simp only [run?, Option.some.injEq] at h
      subst h
      cases rest <;> simp [exactReachStates]
  | op :: pre, rest, σ0, σ, h => by
      simp only [run?] at h
      cases hs : applyOp? σ0 op with
      | none => rw [hs] at h; cases h
      | some σ1 =>
          rw [hs] at h
          simp only [List.cons_append, exactReachStates, hs, exactTab_eq]
          exact List.mem_cons_of_mem _ (mem_exactReachStates pre rest σ1 σ h)

/-- Conversely, every visited state is reached by a prefix. -/
theorem run_of_mem_exactReachStates {k : ℕ} :
    ∀ (ops : Prog k) (σ0 σ : State k), σ ∈ exactReachStates σ0 ops →
      ∃ pre rest, ops = pre ++ rest ∧ run? pre σ0 = some σ
  | [], σ0, σ, h => by
      simp only [exactReachStates, List.mem_singleton] at h
      subst h
      exact ⟨[], [], rfl, rfl⟩
  | op :: ops, σ0, σ, h => by
      simp only [exactReachStates] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨[], op :: ops, rfl, rfl⟩
      · cases hs : applyOp? σ0 op with
        | none => rw [hs] at h; cases h
        | some σ1 =>
            simp only [hs, exactTab_eq] at h
            obtain ⟨pre, rest, he, hr⟩ := run_of_mem_exactReachStates ops σ1 σ h
            exact ⟨op :: pre, rest, by rw [he]; rfl, by simp only [run?, hs]; exact hr⟩

/-- Every row any register holds in any visited state. -/
def exactReachRows {k : ℕ} (ops : Prog k) : List (Register k) :=
  (exactReachStates State.start_state ops).flatMap fun σ => (List.finRange k).map σ

theorem mem_exactReachRows {k : ℕ} {ops pre rest : Prog k} {σ : State k}
    (hops : ops = pre ++ rest) (hrun : run? pre State.start_state = some σ) (i : Fin k) :
    σ i ∈ exactReachRows ops := by
  unfold exactReachRows
  rw [List.mem_flatMap]
  exact ⟨σ, hops ▸ mem_exactReachStates pre rest _ σ hrun,
    List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩

theorem exists_of_mem_exactReachRows {k : ℕ} {ops : Prog k} {r : Register k}
    (h : r ∈ exactReachRows ops) :
    ∃ pre rest σ i, ops = pre ++ rest ∧ run? pre State.start_state = some σ ∧ σ i = r := by
  unfold exactReachRows at h
  obtain ⟨σ, hσ, hr⟩ := List.mem_flatMap.mp h
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
  obtain ⟨pre, rest, hops, hrun⟩ := run_of_mem_exactReachStates _ _ _ hσ
  exact ⟨pre, rest, σ, i, hops, hrun, rfl⟩

/-! ## Fast evaluation (`@[csimp]`: proved equal, used by compiled code)

`exactReachStates` re-tabulates with `exactTab`, whose array the code
generator may recompute inside the returned closure; and `exactRowLo/Hi`
recompute the box bounds (`2^t`) for every row. The definitions above are the
specification; the versions below carry the state as an `Array` value (never a
closure) and take the bounds as arrays computed once per call. The `@[csimp]`
theorems make every compiled caller use them; they are equalities, so nothing
the kernel checks changes. -/

/-- A state as arrays. -/
def stArr {k : ℕ} (σ : State k) : Array (Array ℤ) := Array.ofFn fun i => Array.ofFn (σ i)

/-- Arrays read back as a state. -/
def arrState {k : ℕ} (a : Array (Array ℤ)) : State k := fun i j => (a.getD i.1 #[]).getD j.1 0

theorem arrState_stArr {k : ℕ} (σ : State k) : arrState (stArr σ) = σ := by
  funext i j
  simp [arrState, stArr, Array.getD_eq_getD_getElem?]

/-- `exactReachStates`, carrying array states. -/
def exactReachArr {k : ℕ} : Array (Array ℤ) → Prog k → List (Array (Array ℤ))
  | a, [] => [a]
  | a, op :: ops =>
      a :: (match applyOp? (arrState a) op with
        | none => []
        | some σ' => exactReachArr (stArr σ') ops)

theorem exactReachArr_eq {k : ℕ} :
    ∀ (ops : Prog k) (σ : State k),
      (exactReachArr (stArr σ) ops).map arrState = exactReachStates σ ops
  | [], σ => by simp [exactReachArr, exactReachStates, arrState_stArr]
  | op :: ops, σ => by
      simp only [exactReachArr, exactReachStates, List.map_cons, arrState_stArr]
      congr 1
      cases applyOp? σ op with
      | none => rfl
      | some σ' => simp only [exactTab_eq]; exact exactReachArr_eq ops σ'

/-- `exactReachRows`, through array states. -/
def exactReachRowsFast {k : ℕ} (ops : Prog k) : List (Register k) :=
  (exactReachArr (stArr (State.start_state (k := k))) ops).flatMap fun a => (List.finRange k).map (arrState a)

@[csimp] theorem exactReachRows_eq_fast : @exactReachRows = @exactReachRowsFast := by
  funext k ops
  unfold exactReachRows exactReachRowsFast
  rw [← exactReachArr_eq ops State.start_state, List.flatMap_map]


/-! ## The limb box and row ranges -/

/-- The value of row `r` on limbs `L`. -/
def rowVal {k : ℕ} (r : Register k) (L : Fin k → ℤ) : ℤ := ∑ j, r j * L j

/-- Least value of chunk `j` of an operand of width `w` at lower-limb width `W`. -/
def exactLimbLo (w W : ℕ) {k : ℕ} (j : Fin k) : ℤ :=
  if isTopChunk j then
    (if phaseSplitLogicalWidth w W k j = 0 then 0
     else -(2 : ℤ) ^ (phaseSplitLogicalWidth w W k j - 1))
  else 0

/-- Greatest value of chunk `j`. -/
def exactLimbHi (w W : ℕ) {k : ℕ} (j : Fin k) : ℤ :=
  if isTopChunk j then
    (if phaseSplitLogicalWidth w W k j = 0 then 0
     else (2 : ℤ) ^ (phaseSplitLogicalWidth w W k j - 1) - 1)
  else (2 : ℤ) ^ (phaseSplitLogicalWidth w W k j) - 1

/-- `L` lies in the limb box of an operand of width `w` at lower-limb width `W`. -/
def InExactBox (w W : ℕ) {k : ℕ} (L : Fin k → ℤ) : Prop :=
  ∀ j, exactLimbLo w W j ≤ L j ∧ L j ≤ exactLimbHi w W j

theorem exactLimbLo_le_hi (w W : ℕ) {k : ℕ} (j : Fin k) :
    exactLimbLo w W j ≤ exactLimbHi w W j := by
  unfold exactLimbLo exactLimbHi
  split
  · split
    · exact le_rfl
    · have : (1 : ℤ) ≤ 2 ^ (phaseSplitLogicalWidth w W k j - 1) := one_le_pow₀ (by norm_num)
      linarith
  · have : (1 : ℤ) ≤ 2 ^ (phaseSplitLogicalWidth w W k j) := one_le_pow₀ (by norm_num)
    linarith

/-- Least value of the row over the box (a list sum, so it evaluates). -/
def exactRowLo (w W : ℕ) {k : ℕ} (r : Register k) : ℤ :=
  ((List.finRange k).map fun j => min (r j * exactLimbLo w W j) (r j * exactLimbHi w W j)).sum

/-- Greatest value of the row over the box. -/
def exactRowHi (w W : ℕ) {k : ℕ} (r : Register k) : ℤ :=
  ((List.finRange k).map fun j => max (r j * exactLimbLo w W j) (r j * exactLimbHi w W j)).sum

/-- The magnitude the row demands: a signed `E`-bit register holds every value
of the row over the box iff `exactRowDemand ≤ 2^(E-1)` (`0 < E`). -/
def exactRowDemand (w W : ℕ) {k : ℕ} (r : Register k) : ℕ :=
  max (-exactRowLo w W r).toNat (exactRowHi w W r + 1).toNat

theorem exactRowLo_eq (w W : ℕ) {k : ℕ} (r : Register k) :
    exactRowLo w W r = ∑ j, min (r j * exactLimbLo w W j) (r j * exactLimbHi w W j) :=
  (Fin.sum_univ_def _).symm

theorem exactRowHi_eq (w W : ℕ) {k : ℕ} (r : Register k) :
    exactRowHi w W r = ∑ j, max (r j * exactLimbLo w W j) (r j * exactLimbHi w W j) :=
  (Fin.sum_univ_def _).symm

theorem exact_term_bounds {c l lo hi : ℤ} (h1 : lo ≤ l) (h2 : l ≤ hi) :
    min (c * lo) (c * hi) ≤ c * l ∧ c * l ≤ max (c * lo) (c * hi) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h1 hc),
      le_trans (mul_le_mul_of_nonneg_left h2 hc) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left h2 hc),
      le_trans (mul_le_mul_of_nonpos_left h1 hc) (le_max_left _ _)⟩

/-- **Interval soundness**: on the box, a row's value lies in `[rowLo, rowHi]`. -/
theorem exact_row_bounds (w W : ℕ) {k : ℕ} (r : Register k) {L : Fin k → ℤ}
    (hL : InExactBox w W L) :
    exactRowLo w W r ≤ rowVal r L ∧ rowVal r L ≤ exactRowHi w W r := by
  rw [exactRowLo_eq, exactRowHi_eq]
  unfold rowVal
  exact ⟨Finset.sum_le_sum fun j _ => (exact_term_bounds (c := r j) (hL j).1 (hL j).2).1,
    Finset.sum_le_sum fun j _ => (exact_term_bounds (c := r j) (hL j).1 (hL j).2).2⟩

/-- The corner of the box where the row is largest. -/
def exactCornerHi (w W : ℕ) {k : ℕ} (r : Register k) : Fin k → ℤ :=
  fun j => if 0 ≤ r j then exactLimbHi w W j else exactLimbLo w W j

/-- The corner of the box where the row is least. -/
def exactCornerLo (w W : ℕ) {k : ℕ} (r : Register k) : Fin k → ℤ :=
  fun j => if 0 ≤ r j then exactLimbLo w W j else exactLimbHi w W j

theorem exactCornerHi_box (w W : ℕ) {k : ℕ} (r : Register k) :
    InExactBox w W (exactCornerHi w W r) := fun j => by
  have := exactLimbLo_le_hi w W j
  unfold exactCornerHi; split <;> constructor <;> omega

theorem exactCornerLo_box (w W : ℕ) {k : ℕ} (r : Register k) :
    InExactBox w W (exactCornerLo w W r) := fun j => by
  have := exactLimbLo_le_hi w W j
  unfold exactCornerLo; split <;> constructor <;> omega

/-- **Attainment** of the upper end. -/
theorem exact_rowHi_attained (w W : ℕ) {k : ℕ} (r : Register k) :
    rowVal r (exactCornerHi w W r) = exactRowHi w W r := by
  rw [exactRowHi_eq]
  unfold rowVal exactCornerHi
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle := exactLimbLo_le_hi w W j
  split
  · rename_i h; exact (max_eq_right (mul_le_mul_of_nonneg_left hle h)).symm
  · rename_i h; exact (max_eq_left (mul_le_mul_of_nonpos_left hle (by omega))).symm

/-- **Attainment** of the lower end. -/
theorem exact_rowLo_attained (w W : ℕ) {k : ℕ} (r : Register k) :
    rowVal r (exactCornerLo w W r) = exactRowLo w W r := by
  rw [exactRowLo_eq]
  unfold rowVal exactCornerLo
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle := exactLimbLo_le_hi w W j
  split
  · rename_i h; exact (min_eq_left (mul_le_mul_of_nonneg_left hle h)).symm
  · rename_i h; exact (min_eq_right (mul_le_mul_of_nonpos_left hle (by omega))).symm

/-- Demand bound ⇒ fit. -/
theorem fits_of_exactDemand {E : ℕ} {z lo hi : ℤ} (hE : 0 < E) (hlo : lo ≤ z) (hhi : z ≤ hi)
    (hd : max (-lo).toNat (hi + 1).toNat ≤ 2 ^ (E - 1)) : FitsSignedWidth E z := by
  have h1 : (-lo).toNat ≤ 2 ^ (E - 1) := le_trans (le_max_left _ _) hd
  have h2 : (hi + 1).toNat ≤ 2 ^ (E - 1) := le_trans (le_max_right _ _) hd
  have e1 := Int.self_le_toNat (-lo)
  have e2 := Int.self_le_toNat (hi + 1)
  have c1 : ((-lo).toNat : ℤ) ≤ ((2 ^ (E - 1) : ℕ) : ℤ) := by exact_mod_cast h1
  have c2 : ((hi + 1).toNat : ℤ) ≤ ((2 ^ (E - 1) : ℕ) : ℤ) := by exact_mod_cast h2
  refine ⟨hE, ?_, ?_⟩
  · unfold signedMin; omega
  · unfold signedMax; omega

/-- Fit at both attained ends ⇒ demand bound. -/
theorem exactDemand_le_of_fits {E : ℕ} (w W : ℕ) {k : ℕ} (r : Register k)
    (hhi : FitsSignedWidth E (exactRowHi w W r)) (hlo : FitsSignedWidth E (exactRowLo w W r)) :
    exactRowDemand w W r ≤ 2 ^ (E - 1) := by
  obtain ⟨-, -, h2⟩ := hhi
  obtain ⟨-, h1, -⟩ := hlo
  unfold signedMin at h1
  unfold signedMax at h2
  unfold exactRowDemand
  refine max_le ?_ ?_
  · have : (-exactRowLo w W r).toNat ≤ ((2 ^ (E - 1) : ℕ) : ℤ).toNat :=
      Int.toNat_le_toNat (by omega)
    simpa using this
  · have : (exactRowHi w W r + 1).toNat ≤ ((2 ^ (E - 1) : ℕ) : ℤ).toNat :=
      Int.toNat_le_toNat (by omega)
    simpa using this

/-! ## Maxima and the least exponent -/

/-- The largest entry of a list of naturals (`0` for the empty list). -/
def exactListMax : List ℕ → ℕ
  | [] => 0
  | a :: as => max a (exactListMax as)

theorem le_exactListMax : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ exactListMax l
  | [], _, h => by cases h
  | b :: l, a, h => by
      simp only [exactListMax]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (le_exactListMax h) (le_max_right _ _)

theorem exactListMax_le {l : List ℕ} {B : ℕ} (h : ∀ a ∈ l, a ≤ B) : exactListMax l ≤ B := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
      simp only [exactListMax]
      exact max_le (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- Least `e ≥ e₀` with `D ≤ 2^e`, searching at most `f` steps. -/
def exactLeastExp (D : ℕ) : ℕ → ℕ → ℕ
  | 0, e => e
  | f + 1, e => if D ≤ 2 ^ e then e else exactLeastExp D f (e + 1)

theorem exactLeastExp_spec (D : ℕ) : ∀ (f e : ℕ), D ≤ 2 ^ (e + f) → (∀ e' < e, ¬ D ≤ 2 ^ e') →
    D ≤ 2 ^ exactLeastExp D f e ∧ ∀ e' < exactLeastExp D f e, ¬ D ≤ 2 ^ e'
  | 0, e, h, hm => ⟨by simpa [exactLeastExp] using h, hm⟩
  | f + 1, e, h, hm => by
      simp only [exactLeastExp]
      split
      · exact ⟨‹_›, hm⟩
      · rename_i hne
        refine exactLeastExp_spec D f (e + 1) (by rwa [show e + 1 + f = e + (f + 1) by omega]) ?_
        intro e' he'
        rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h' | rfl
        · exact hm e' h'
        · exact hne

/-! ## The widths -/

/-- The lower-limb width the compiler splits two operands of widths `xw`, `zw`
at (`phaseLimbWidth`, from widths alone). -/
def exactLimbWidth (k xw zw : ℕ) : ℕ := min (phaseLimbWidthOfWidth xw k) (phaseLimbWidthOfWidth zw k)

/-- The largest demand over the reachable rows, on both operands' boxes. -/
def exactDemand {k : ℕ} (ops : Prog k) (xw zw : ℕ) : ℕ :=
  exactListMax ((exactReachRows ops).map fun r =>
    max (exactRowDemand xw (exactLimbWidth k xw zw) r) (exactRowDemand zw (exactLimbWidth k xw zw) r))

/-- Row demand with the box bounds passed as arrays. -/
def rowDemandArr {k : ℕ} (lo hi : Array ℤ) (r : Register k) : ℕ :=
  max (-((List.finRange k).map fun j => min (r j * lo.getD j.1 0) (r j * hi.getD j.1 0)).sum).toNat
    (((List.finRange k).map fun j => max (r j * lo.getD j.1 0) (r j * hi.getD j.1 0)).sum + 1).toNat

/-- The demand, bounds computed once. -/
def exactDemandWith {k : ℕ} (rows : List (Register k)) (xlo xhi zlo zhi : Array ℤ) : ℕ :=
  exactListMax (rows.map fun r => max (rowDemandArr xlo xhi r) (rowDemandArr zlo zhi r))

def exactDemandFast {k : ℕ} (ops : Prog k) (xw zw : ℕ) : ℕ :=
  exactDemandWith (exactReachRows ops)
    (Array.ofFn (exactLimbLo xw (exactLimbWidth k xw zw) (k := k)))
    (Array.ofFn (exactLimbHi xw (exactLimbWidth k xw zw) (k := k)))
    (Array.ofFn (exactLimbLo zw (exactLimbWidth k xw zw) (k := k)))
    (Array.ofFn (exactLimbHi zw (exactLimbWidth k xw zw) (k := k)))

theorem rowDemandArr_ofFn {k : ℕ} (w W : ℕ) (r : Register k) :
    rowDemandArr (Array.ofFn (exactLimbLo w W (k := k))) (Array.ofFn (exactLimbHi w W (k := k))) r
      = exactRowDemand w W r := by
  simp [rowDemandArr, exactRowDemand, exactRowLo, exactRowHi, Array.getD_eq_getD_getElem?]

@[csimp] theorem exactDemand_eq_fast : @exactDemand = @exactDemandFast := by
  funext k ops xw zw
  simp only [exactDemand, exactDemandFast, exactDemandWith, rowDemandArr_ofFn]


/-- **The tight width**: `1 + ⌈log₂ D⌉`, the least `E ≥ 1` with `D ≤ 2^(E-1)`. -/
def tightSignedWidthOfWidths {k : ℕ} (ops : Prog k) (xw zw : ℕ) : ℕ :=
  1 + exactLeastExp (exactDemand ops xw zw) (exactDemand ops xw zw) 0

/-- The initial chunk widths, as the compiler's initial width state records them. -/
def exactInitNeed (k xw zw : ℕ) : NeededWidths k where
  xneed := fun i => phaseSplitLogicalWidth xw (exactLimbWidth k xw zw) k i
  zneed := fun i => phaseSplitLogicalWidth zw (exactLimbWidth k xw zw) k i

/-- **The floor**: one bit above the widest initial chunk, the least width
that grows every slot (ForShor's allocation sign- or zero-extends each slot by at
least one bit). -/
def floorSignedWidthOfWidths (k xw zw : ℕ) : ℕ := commonNeededWidth (exactInitNeed k xw zw)

/-- **The exact working width** the compiler uses: the tight width, or the
floor if that is larger. -/
def exactSignedWidthOfWidths {k : ℕ} (ops : Prog k) (xw zw : ℕ) : ℕ :=
  max (tightSignedWidthOfWidths ops xw zw) (floorSignedWidthOfWidths k xw zw)

/-- The exact width as a uniform `NeededWidths` record: every slot is asked
for `E - 1`, so `commonNeededWidth` of it is `E` (`commonNeededWidth_exactNeeded`). -/
def exactNeededWidths {k : ℕ} (ops : Prog k) (xw zw : ℕ) : NeededWidths k where
  xneed := fun _ => exactSignedWidthOfWidths ops xw zw - 1
  zneed := fun _ => exactSignedWidthOfWidths ops xw zw - 1

theorem tightSignedWidth_spec {k : ℕ} (ops : Prog k) (xw zw : ℕ) :
    exactDemand ops xw zw ≤ 2 ^ (tightSignedWidthOfWidths ops xw zw - 1) ∧
      ∀ e < tightSignedWidthOfWidths ops xw zw - 1, ¬ exactDemand ops xw zw ≤ 2 ^ e := by
  have h := exactLeastExp_spec (exactDemand ops xw zw) (exactDemand ops xw zw) 0
    (by simpa using Nat.lt_two_pow_self.le) (fun _ h => absurd h (Nat.not_lt_zero _))
  simpa [tightSignedWidthOfWidths] using h

theorem tightSignedWidth_pos {k : ℕ} (ops : Prog k) (xw zw : ℕ) :
    0 < tightSignedWidthOfWidths ops xw zw := by
  unfold tightSignedWidthOfWidths; omega

theorem floorSignedWidth_pos (k xw zw : ℕ) : 0 < floorSignedWidthOfWidths k xw zw := by
  unfold floorSignedWidthOfWidths commonNeededWidth; omega

theorem exactSignedWidth_pos {k : ℕ} (ops : Prog k) (xw zw : ℕ) :
    0 < exactSignedWidthOfWidths ops xw zw :=
  lt_of_lt_of_le (tightSignedWidth_pos ops xw zw) (le_max_left _ _)

theorem tight_le_exactSignedWidth {k : ℕ} (ops : Prog k) (xw zw : ℕ) :
    tightSignedWidthOfWidths ops xw zw ≤ exactSignedWidthOfWidths ops xw zw := le_max_left _ _

theorem floor_le_exactSignedWidth {k : ℕ} (ops : Prog k) (xw zw : ℕ) :
    floorSignedWidthOfWidths k xw zw ≤ exactSignedWidthOfWidths ops xw zw := le_max_right _ _

/-- The demand of a reachable row is at most `2^(E-1)` at the tight width. -/
theorem exactRowDemand_le_tight {k : ℕ} {ops : Prog k} {xw zw : ℕ} {r : Register k}
    (hr : r ∈ exactReachRows ops) :
    exactRowDemand xw (exactLimbWidth k xw zw) r ≤ 2 ^ (tightSignedWidthOfWidths ops xw zw - 1) ∧
    exactRowDemand zw (exactLimbWidth k xw zw) r ≤ 2 ^ (tightSignedWidthOfWidths ops xw zw - 1) := by
  have hmem : max (exactRowDemand xw (exactLimbWidth k xw zw) r)
      (exactRowDemand zw (exactLimbWidth k xw zw) r) ≤ exactDemand ops xw zw :=
    le_exactListMax (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hD := (tightSignedWidth_spec ops xw zw).1
  exact ⟨le_trans (le_trans (le_max_left _ _) hmem) hD,
    le_trans (le_trans (le_max_right _ _) hmem) hD⟩

/-- `commonNeededWidth` of the uniform record is the exact width (`0 < k`). -/
theorem commonNeededWidth_exactNeeded {k : ℕ} (hk : 0 < k) (ops : Prog k) (xw zw : ℕ) :
    commonNeededWidth (exactNeededWidths ops xw zw) = exactSignedWidthOfWidths ops xw zw := by
  unfold commonNeededWidth exactNeededWidths
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  simp only [max_self]
  rw [Finset.sup_const hne]
  have := exactSignedWidth_pos ops xw zw
  omega

/-- Every initial chunk is at most `E - 1`, so every slot grows by at least one bit. -/
theorem exactInit_le {k : ℕ} (ops : Prog k) (xw zw : ℕ) (i : Fin k) :
    (exactInitNeed k xw zw).xneed i ≤ exactSignedWidthOfWidths ops xw zw - 1 ∧
    (exactInitNeed k xw zw).zneed i ≤ exactSignedWidthOfWidths ops xw zw - 1 := by
  have hsup : max ((exactInitNeed k xw zw).xneed i) ((exactInitNeed k xw zw).zneed i)
      ≤ Finset.univ.sup (fun j : Fin k =>
          max ((exactInitNeed k xw zw).xneed j) ((exactInitNeed k xw zw).zneed j)) :=
    Finset.le_sup (f := fun j : Fin k =>
      max ((exactInitNeed k xw zw).xneed j) ((exactInitNeed k xw zw).zneed j)) (Finset.mem_univ i)
  have hfl := floor_le_exactSignedWidth ops xw zw
  unfold floorSignedWidthOfWidths commonNeededWidth at hfl
  constructor <;> omega

end Shor
