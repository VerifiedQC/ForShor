import Model.Interpreter.FullDSL
import Model.Scanner.C11
import Model.Scanner.Planner
import Model.Scanner.Profile
import Model.Interpreter.Mass
import Model.Scanner.SplitHelper

/-!
# Connection of the C11 table to the full language

Connects the scanner-level C11 word to the full instruction language. Proves step and run correspondence of rows (`c11_step_rows`, `c11_run_rows`) and records facts about the translated word such as its charge `c11_charge`, row restoration `c11_rows_restore` and the child-width formula `c11_childWidth`.
-/

set_option maxHeartbeats 500000

namespace Paper.FullDSL

theorem c11_step_rows {s s' : C11.State} {op : C11.Instruction}
    (h : C11.step s op = some s') :
    rowStep (fromC11 op) s.rows = some s'.rows := by
  cases op with
  | add dst src neg shift =>
      by_cases heq : dst = src
      · simp [C11.step, heq] at h
      · cases neg with
        | false =>
            simp [C11.step, heq, fromC11, rowStep] at h ⊢
            cases h
            congr 1
            funext i j
            by_cases hi : i = dst
            · subst i
              simp [C11.updateRow, Matrix.updateRow_self]
            · simp [C11.updateRow, Matrix.updateRow_ne, hi]
        | true =>
            simp [C11.step, heq, fromC11, rowStep] at h ⊢
            cases h
            congr 1
            funext i j
            by_cases hi : i = dst
            · subst i
              simp [C11.updateRow, Matrix.updateRow_self]
            · simp [C11.updateRow, Matrix.updateRow_ne, hi]
  | negate dst =>
      simp [C11.step, fromC11, rowStep] at h ⊢
      cases h
      congr 1
      funext i j
      by_cases hi : i = dst
      · subst i
        simp [C11.updateRow, Matrix.updateRow_self]
      · simp [C11.updateRow, Matrix.updateRow_ne, hi]
  | mark row target =>
      simp [C11.step] at h
      obtain ⟨_, hs⟩ := h
      subst s'
      rfl

theorem c11_run_rows (word : List C11.Instruction)
    {s s' : C11.State} (h : C11.run word s = some s') :
    runRows (word.map fromC11) s.rows = some s'.rows := by
  induction word generalizing s with
  | nil =>
      simp only [C11.run, Option.some.injEq] at h
      subst s'
      rfl
  | cons op rest ih =>
      simp only [C11.run] at h
      obtain ⟨mid, hs, ht⟩ : ∃ mid, C11.step s op = some mid ∧
          C11.run rest mid = some s' := by
        cases hs : C11.step s op with
        | none => simp [hs] at h
        | some mid =>
            simp only [hs, Option.bind_some] at h ⊢
            exact ⟨mid, rfl, h⟩
      simpa [runRows, c11_step_rows hs] using ih ht

theorem c11_charge : wordCharge c11Word = 11 := by decide

theorem c11_rows_restore :
    runRows c11Word (identity 3) = some (identity 3) := by
  have hi : C11.initial.rows = identity 3 := by
    funext i j
    simp [C11.initial, C11.identity, identity, Matrix.one_apply]
  have ho : C11.result.rows = identity 3 := by
    funext i j
    simpa [C11.identity, identity, Matrix.one_apply] using
      C11.replay_restores i j
  have h := c11_run_rows C11.word C11.replay_success
  simpa [c11Word, hi, ho] using h

theorem c11_width_peak_zero :
    (Scanner.scan (widthWord c11Word)
      (Scanner.fresh (fun _ : Fin 3 => 0))).peak = 6 := by decide

theorem c11_width_peak_two :
    (Scanner.scan (widthWord c11Word)
      (Scanner.fresh (Scanner.balanced (2 : Fin 3) 0 2))).peak = 7 := by decide

theorem c11_childWidth (w : Nat) :
    Planner.childWidth 3 c11Profile w =
      w / 3 + 1 + max 6 (5 + w % 3) := rfl

theorem c11_balanced_literal (q r : Nat) :
    Scanner.balanced (2 : Fin 3) q r =
      (fun i : Fin 3 => if i = 2 then q + r else q) := by
  funext i
  by_cases hi : i = 2 <;> simp [Scanner.balanced, hi]

theorem c11_childWidth_split (q r : Nat) (hr : r < 3) :
    Planner.childWidth 3 c11Profile (3 * q + r) =
      q + 1 + max 6 (5 + r) := by
  simp only [c11_childWidth]
  omega

theorem c11_noUnderflow (r : Nat) :
    Scanner.noUnderflow (widthWord c11Word)
      (Scanner.balanced (2 : Fin 3) 0 r) := by
  exact (RowMass.runRows_mass_noUnderflow
    (Scanner.balanced (2 : Fin 3) 0 r) c11Word
    (identity 3) c11_rows_restore).1

theorem c11_peak_profile (r : Nat) (hr : r ≤ 2) :
    (Scanner.scan (widthWord c11Word)
      (Scanner.fresh (Scanner.balanced (2 : Fin 3) 0 r))).peak =
      max 6 (5 + r) := by
  have hprof := Profile.fresh_peak_profile_affine
    (2 : Fin 3) (widthWord c11Word) 2 r hr
  have hw : Scanner.balanced (2 : Fin 3) 0 0 =
      (fun _ : Fin 3 => 0) := by
    funext i
    simp [Scanner.balanced]
  have h0 :
      (Scanner.scan (widthWord c11Word)
        (Scanner.fresh (Scanner.balanced (2 : Fin 3) 0 0))).peak = 6 := by
    rw [hw]
    exact c11_width_peak_zero
  simpa only [h0, c11_width_peak_two, Nat.reduceSub] using hprof

theorem c11_peak_split (q r : Nat) (hr : r ≤ 2) :
    (Scanner.scan (widthWord c11Word)
      (Scanner.fresh (Scanner.balanced (2 : Fin 3) q r))).peak =
      q + max 6 (5 + r) := by
  have ht := Profile.fresh_peak_translate (2 : Fin 3) (widthWord c11Word)
    q r (c11_noUnderflow r)
  simpa only [c11_peak_profile r hr] using ht

theorem c11_scanner_childWidth (q r : Nat) (hr : r < 3) :
    1 + (Scanner.scan (widthWord c11Word)
      (Scanner.fresh (Scanner.balanced (2 : Fin 3) q r))).peak =
      Planner.childWidth 3 c11Profile (3 * q + r) := by
  rw [c11_peak_split q r (by omega), c11_childWidth_split q r hr]
  omega

theorem legal_peak_profile {k : Nat} (top : Fin k)
    (word : List (Instruction k)) (final : Rows k)
    (hsuccess : runRows word (identity k) = some final)
    (L R r : Nat) (hr : r ≤ R) :
    (Scanner.scan (widthWord word)
      (Scanner.fresh (Scanner.balanced top L r))).peak =
      L + max
        ((Scanner.scan (widthWord word)
          (Scanner.fresh (Scanner.balanced top 0 0))).peak)
        ((Scanner.scan (widthWord word)
          (Scanner.fresh (Scanner.balanced top 0 R))).peak - (R - r)) := by
  have hno := (RowMass.runRows_mass_noUnderflow
    (Scanner.balanced top 0 r) word final hsuccess).1
  have ht := Profile.fresh_peak_translate top (widthWord word) L r hno
  have hp := Profile.fresh_peak_profile top (widthWord word) R r hr
  rw [hp] at ht
  exact ht

theorem legal_program_childWidth {k : Nat} (top : Fin k)
    (htop : top.val + 1 = k)
    (word : List (Instruction k)) (final : Rows k)
    (hsuccess : runRows word (identity k) = some final)
    (w : Nat) :
    1 + (Scanner.scan (widthWord word)
      (Scanner.fresh
        (fun i : Fin k =>
          if i.val + 1 = k then w - i.val * (w / k) else w / k))).peak =
      Planner.childWidth k
        ⟨wordCharge word,
          (Scanner.scan (widthWord word)
            (Scanner.fresh (Scanner.balanced top 0 0))).peak,
          (Scanner.scan (widthWord word)
            (Scanner.fresh (Scanner.balanced top 0 (k - 1)))).peak - (k - 1)⟩
        w := by
  have hk : 0 < k := Nat.lt_of_lt_of_le (Nat.zero_lt_succ top.val) (by omega)
  have hr : w % k ≤ k - 1 := by
    have hm := Nat.mod_lt w hk
    omega
  rw [RowMass.literalSourceSplit_eq_balanced top htop w]
  have hno := (RowMass.runRows_mass_noUnderflow
    (Scanner.balanced top 0 (w % k)) word final hsuccess).1
  have ht := Profile.fresh_peak_translate top (widthWord word)
    (w / k) (w % k) hno
  have hp := Profile.fresh_peak_profile_affine top (widthWord word)
    (k - 1) (w % k) hr
  rw [hp] at ht
  rw [ht]
  simp only [Planner.childWidth]
  omega

theorem c11_literal_source_peak (w : Nat) :
    (Scanner.scan (widthWord c11Word)
      (Scanner.fresh
        (fun i : Fin 3 =>
          if i.val + 1 = 3 then w - i.val * (w / 3) else w / 3))).peak =
      w / 3 + max 6 (5 + w % 3) := by
  rw [RowMass.literalSourceSplit_eq_balanced (2 : Fin 3) (by decide) w]
  exact c11_peak_split (w / 3) (w % 3) (by omega)

theorem c11_literal_source_childWidth (w : Nat) :
    1 + (Scanner.scan (widthWord c11Word)
      (Scanner.fresh
        (fun i : Fin 3 =>
          if i.val + 1 = 3 then w - i.val * (w / 3) else w / 3))).peak =
      Planner.childWidth 3 c11Profile w := by
  rw [c11_literal_source_peak, c11_childWidth]
  omega

end Paper.FullDSL
