import Model.Interpreter.FullDSL
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Row mass and capacity bounds

Works with the column-weighted mass of an integer row. Proves how mass behaves under negation, scaling and addition (`mass_neg`, `mass_mul`, `mass_add`), the identity rows being bounded (`identity_bounded`), and capacity facts for shifts and additions such as `cap_shiftL` and `cap_add`.
-/

namespace Paper.RowMass

open Paper.FullDSL

theorem cap_shiftL (w n m : Nat) (h : m ≤ 2^w) :
    2^n*m ≤ 2^(w+n) := by
  calc
    2^n*m ≤ 2^n*2^w := Nat.mul_le_mul_left _ h
    _ = 2^(w+n) := by rw [pow_add]; ac_rfl

theorem cap_shiftR (w n old new : Nat)
    (hexact : old = 2^n * new) (hpositive : 0 < new) (hbound : old ≤ 2^w) :
    n ≤ w ∧ new ≤ 2^(w-n) := by
  have hpow : 2^n ≤ 2^w := by
    calc
      2^n ≤ 2^n * new := Nat.le_mul_of_pos_right _ hpositive
      _ = old := hexact.symm
      _ ≤ 2^w := hbound
  have hguard : n ≤ w := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  constructor
  · exact hguard
  · have hp : 2^w = 2^n * 2^(w-n) := by
      conv_lhs => rw [← Nat.add_sub_of_le hguard]
      rw [pow_add]
    have hm : 2^n * new ≤ 2^n * 2^(w-n) := by
      rw [← hexact, ← hp]
      exact hbound
    exact Nat.le_of_mul_le_mul_left hm (Nat.pow_pos (by decide))

theorem cap_add (wd ws n x a b : Nat)
    (ha : a ≤ 2^wd) (hb : b ≤ 2^ws) (hx : x ≤ a+2^n*b) :
    x ≤ 2^(1+max wd (ws+n)) := by
  let M := max wd (ws+n)
  have hdb : 2^wd ≤ 2^M := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  have hsb : 2^(ws+n) ≤ 2^M := Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  calc
    x ≤ a + 2^n*b := hx
    _ ≤ 2^wd + 2^(ws+n) := Nat.add_le_add ha (cap_shiftL ws n b hb)
    _ ≤ 2^M + 2^M := Nat.add_le_add hdb hsb
    _ = 2^(1+max wd (ws+n)) := by simp [M, pow_add, pow_succ]; omega

theorem mass_neg {k : Nat} (weights : Fin k → Nat) (row : Fin k → Int) :
    weightedMass weights (fun j => -row j) = weightedMass weights row := by
  simp [weightedMass]

theorem mass_zero {k : Nat} (weights : Fin k → Nat) (row : Fin k → Int)
    (h : weightedMass weights row = 0) : ∀ j, row j = 0 := by
  intro j
  have hj : (row j).natAbs * 2 ^ weights j ≤ weightedMass weights row := by
    unfold weightedMass
    exact Finset.single_le_sum (f := fun x => (row x).natAbs * 2 ^ weights x)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hzprod : (row j).natAbs * 2 ^ weights j = 0 := Nat.eq_zero_of_le_zero (h ▸ hj)
  have hz : (row j).natAbs = 0 :=
    (mul_eq_zero.mp hzprod).resolve_right (pow_ne_zero _ (by decide))
  exact Int.natAbs_eq_zero.mp hz

theorem mass_mul {k : Nat} (weights : Fin k → Nat) (row : Fin k → Int) (n : Nat) :
    weightedMass weights (fun j => row j * (2:Int)^n) = 2^n * weightedMass weights row := by
  simp only [weightedMass, Int.natAbs_mul, Int.natAbs_pow]
  simp only [show (2:Int).natAbs = 2 by decide]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_assoc, mul_left_comm]

theorem mass_scaled {k : Nat} (weights : Fin k → Nat) (row : Fin k → Int)
    (negSrc : Bool) (n : Nat) :
    weightedMass weights (fun j => ((if negSrc then -1 else 1) * (2:Int)^n) * row j) =
      2^n * weightedMass weights row := by
  cases negSrc <;> simp [weightedMass, Int.natAbs_mul, Finset.mul_sum,
    mul_assoc, mul_left_comm]

theorem mass_add {k : Nat} (weights : Fin k → Nat) (a b : Fin k → Int) :
    weightedMass weights (fun j => a j + b j) ≤
      weightedMass weights a + weightedMass weights b := by
  unfold weightedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  calc
    (a j + b j).natAbs * 2 ^ weights j ≤
        (a j).natAbs * 2 ^ weights j + (b j).natAbs * 2 ^ weights j := by
          rw [← Nat.add_mul]
          exact Nat.mul_le_mul_right _ (Int.natAbs_add_le (a j) (b j))

theorem identity_mass {k : Nat} (weights : Fin k → Nat) (i : Fin k) :
    weightedMass weights (identity k i) = 2 ^ weights i := by
  simp only [weightedMass, identity, Matrix.one_apply]
  have hh : (∑ j : Fin k, (if i = j then (1:Int) else 0).natAbs * 2 ^ weights j) =
      ∑ j : Fin k, if i = j then 2 ^ weights j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    split <;> simp
  rw [hh, Finset.sum_ite_eq]
  simp

theorem identity_bounded {k : Nat} (weights : Fin k → Nat) :
    Bounded weights (identity k) weights := by
  intro i
  rw [identity_mass]

theorem bound_shiftL {k : Nat} (weights : Fin k → Nat)
    (rows : Rows k) (w : Paper.Scanner.Widths k) (i : Fin k) (n : Nat)
    (hb : Bounded weights rows w) :
    Bounded weights
      (rows.updateRow i (fun j => rows i j * (2:Int)^n))
      (Paper.Scanner.step (.shiftL i n) w) := by
  intro r
  by_cases hr : r = i
  · subst r
    simpa [Paper.Scanner.step, Matrix.updateRow_self, mass_mul] using
      cap_shiftL (w i) n (weightedMass weights (rows i)) (hb i)
  · simpa [Paper.Scanner.step, Matrix.updateRow_ne hr, hr] using hb r

theorem bound_negate {k : Nat} (weights : Fin k → Nat)
    (rows : Rows k) (w : Paper.Scanner.Widths k) (i : Fin k)
    (hb : Bounded weights rows w) :
    Bounded weights
      (rows.updateRow i (fun j => -rows i j))
      (Paper.Scanner.step (.negate i) w) := by
  intro r
  by_cases hr : r = i
  · subst r
    have hle : 2 ^ w i ≤ 2 ^ (w i + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa [Paper.Scanner.step, Matrix.updateRow_self, mass_neg] using (hb i).trans hle
  · simpa [Paper.Scanner.step, Matrix.updateRow_ne hr, hr] using hb r

theorem bound_addScaled {k : Nat} (weights : Fin k → Nat)
    (rows : Rows k) (w : Paper.Scanner.Widths k) (d s : Fin k) (negSrc : Bool) (n : Nat)
    (hb : Bounded weights rows w) :
    Bounded weights
      (rows.updateRow d (fun j => rows d j +
        ((if negSrc then -1 else 1) * (2:Int)^n) * rows s j))
      (Paper.Scanner.step (.addScaled d s n) w) := by
  intro r
  by_cases hr : r = d
  · subst r
    have htriangle := mass_add weights (rows d)
      (fun j => ((if negSrc then -1 else 1) * (2:Int)^n) * rows s j)
    rw [mass_scaled] at htriangle
    have hh : weightedMass weights
          (fun j => rows d j + ((if negSrc then -1 else 1) * (2:Int)^n) * rows s j) ≤
          2 ^ (1 + max (w d) (w s+n)) :=
      cap_add (w d) (w s) n _ _ _ (hb d) (hb s) htriangle
    simpa [Paper.Scanner.step, Matrix.updateRow_self] using hh
  · simpa [Paper.Scanner.step, Matrix.updateRow_ne hr, hr] using hb r

theorem bound_shiftR {k : Nat} (weights : Fin k → Nat)
    (rows next : Rows k) (w : Paper.Scanner.Widths k) (i : Fin k) (n : Nat)
    (hb : Bounded weights rows w)
    (hexact : ∀ j, rows i j = (2:Int)^n * next i j)
    (hother : ∀ r, r ≠ i → next r = rows r)
    (hnz : ∃ j, next i j ≠ 0) :
    n ≤ w i ∧ Bounded weights next (Paper.Scanner.step (.shiftR i n) w) := by
  have hm : weightedMass weights (rows i) = 2^n * weightedMass weights (next i) := by
    calc
      weightedMass weights (rows i) = weightedMass weights (fun j => next i j * (2:Int)^n) := by
        congr 1
        funext j
        rw [hexact j]
        ac_rfl
      _ = 2^n * weightedMass weights (next i) := mass_mul weights (next i) n
  have hpos : 0 < weightedMass weights (next i) := by
    obtain ⟨j, hj⟩ := hnz
    by_contra h
    have hz : weightedMass weights (next i) = 0 := Nat.eq_zero_of_not_pos h
    exact hj (mass_zero weights (next i) hz j)
  obtain ⟨hguard, hnew⟩ := cap_shiftR (w i) n _ _ hm hpos (hb i)
  constructor
  · exact hguard
  · intro r
    by_cases hr : r = i
    · subst r
      simpa [Paper.Scanner.step] using hnew
    · simpa [Paper.Scanner.step, hr, hother r hr] using hb r

/-- One successful integer-row instruction preserves the mass cap and derives
the exact right-shift guard used by the scanner. -/
theorem step_mass_noUnderflow {k : Nat} (weights : Fin k → Nat)
    (op : Instruction k) (rows next : Rows k) (w : Paper.Scanner.Widths k)
    (hb : Bounded weights rows w)
    (hstep : rowStep op rows = some next)
    (hnz : NonzeroRows next) :
    Paper.Scanner.stepNoUnderflow (widthOp op) w ∧
      Bounded weights next (Paper.Scanner.step (widthOp op) w) := by
  cases op with
  | shiftL i n =>
      have heq : next = rows.updateRow i (fun j => rows i j * (2:Int)^n) := by
        exact Option.some.inj (by simpa [rowStep] using hstep.symm)
      subst next
      exact ⟨trivial, bound_shiftL weights rows w i n hb⟩
  | shiftR i n =>
      have hexact := shiftR_success_exact rows next i n hstep
      have hup : next = rows.updateRow i (fun j => rows i j / (2:Int)^n) := by
        by_cases hdiv : ∀ j : Fin k, rows i j % (2:Int)^n = 0
        · have hs : some (rows.updateRow i (fun j => rows i j / (2:Int)^n)) =
              some next := by simpa [rowStep, hdiv] using hstep
          exact (Option.some.inj hs).symm
        · simp [rowStep, hdiv] at hstep
      have hother : ∀ r, r ≠ i → next r = rows r := by
        intro r hr
        rw [hup, Matrix.updateRow_ne hr]
      obtain ⟨hguard, hnext⟩ :=
        bound_shiftR weights rows next w i n hb hexact hother (hnz i)
      exact ⟨by simpa [widthOp, Paper.Scanner.stepNoUnderflow] using hguard,
        by simpa [widthOp] using hnext⟩
  | negate i =>
      have heq : next = rows.updateRow i (fun j => -rows i j) := by
        exact Option.some.inj (by simpa [rowStep] using hstep.symm)
      subst next
      exact ⟨trivial, bound_negate weights rows w i hb⟩
  | addScaled d s negSrc n =>
      by_cases hds : d = s
      · simp [rowStep, hds] at hstep
      · have heq : next = rows.updateRow d (fun j => rows d j +
            ((if negSrc then -1 else 1) * (2:Int)^n) * rows s j) := by
          exact Option.some.inj (by simpa [rowStep, hds] using hstep.symm)
        subst next
        exact ⟨trivial, bound_addScaled weights rows w d s negSrc n hb⟩
  | phaseProduct i =>
      have heq : next = rows := by
        exact Option.some.inj (by simpa [rowStep] using hstep.symm)
      subst next
      exact ⟨trivial, hb⟩

/-- Any successful word started at the identity has no scanner underflow and
respects the weighted row-mass cap at its final state. -/
theorem runRows_mass_noUnderflow {k : Nat} (weights : Fin k → Nat)
    (word : List (Instruction k)) (final : Rows k)
    (hsuccess : runRows word (identity k) = some final) :
    Paper.Scanner.noUnderflow (widthWord word) weights ∧
      Bounded weights final (Paper.Scanner.runWidths (widthWord word) weights) := by
  have hgeneral : ∀ (suffix : List (Instruction k)) (rows : Rows k)
      (w : Paper.Scanner.Widths k),
      Matrix.det rows ≠ 0 → Bounded weights rows w →
      (∃ final, runRows suffix rows = some final) →
      ∀ final, runRows suffix rows = some final →
        Paper.Scanner.noUnderflow (widthWord suffix) w ∧
          Bounded weights final (Paper.Scanner.runWidths (widthWord suffix) w) := by
    intro suffix
    induction suffix with
    | nil =>
        intro rows w hdet hb hex final hrun
        simp only [runRows, Option.some.injEq] at hrun
        subst final
        exact ⟨trivial, hb⟩
    | cons op rest ih =>
        intro rows w hdet hb hex final hrun
        obtain ⟨next, hstep, hrest⟩ := runRows_cons_success hrun
        have hdetnext := rowStep_det_ne_zero hstep hdet
        have hnz : NonzeroRows next := by
          intro i
          exact rows_nonzero_of_det_ne_zero hdetnext i
        obtain ⟨hguard, hbound⟩ :=
          step_mass_noUnderflow weights op rows next w hb hstep hnz
        obtain ⟨hguards, hfinal⟩ := ih next (Paper.Scanner.step (widthOp op) w)
          hdetnext hbound ⟨final, hrest⟩ final hrest
        exact ⟨⟨hguard, hguards⟩, hfinal⟩
  exact hgeneral word (identity k) weights (identity_det_ne_zero k)
    (identity_bounded weights) ⟨final, hsuccess⟩ final hsuccess

end Paper.RowMass
