import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Values.Exact
/-!
# The threshold acceptance rule at exact widths

A banded policy says which table to use at each width (`choose`: the first band whose
threshold is `≤ w`). Its semantics (`evalPhaseD`, `evalPhaseTight`, `evalPhase`) silently fall back to the
leaf when the chosen table does not shrink the width, so a threshold set too low is not a
correctness fault of the semantics: it is a policy that does not do what it declares. The
harness rejects such a policy. This file states the rule it applies.

`chainContractsTight P n` (a `Bool`, decided by the kernel in the certificate): on the
exact-width recursion from `n` (`ladderX`), every band chosen

* strictly shrinks the width (`ptpTightWidth T w < w`), and
* is applied only where its limbs are not degenerate (`T.k ≤ w`; below that the lower limbs
  `w / k` have width 0).

`chainContractsTight_iff_reach` restates it without the ladder: for every width `m` the exact
recursion from `n` reaches (`ExactReach`) and every table `T` chosen there,
`T.k ≤ m ∧ ptpTightWidth T m < m`. `chainContractsTight_iff` is the one-step unfolding.
-/

namespace Shor
namespace PTP

namespace PTPPolicy




theorem ladderFuelX_fuel (P : PTPPolicy) :
    ∀ (f g m : ℕ), m < f → m < g → P.ladderFuelX f m = P.ladderFuelX g m
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, g + 1, m, hf, hg => by
      simp only [ladderFuelX]
      split
      · rfl
      · rename_i T _
        by_cases h : ptpTightWidth T m < m
        · simp only [h, ↓reduceIte]
          rw [ladderFuelX_fuel P f g (ptpTightWidth T m) (by omega) (by omega)]
        · simp only [h, ↓reduceIte]

theorem ladderX_none (P : PTPPolicy) {n : ℕ} (hc : P.choose n = none) :
    P.ladderX n = [(n, none)] := by
  simp only [ladderX, ladderFuelX, hc]

theorem ladderX_stuck (P : PTPPolicy) {n : ℕ} {T : PTPTable} (hc : P.choose n = some T)
    (h : ¬ ptpTightWidth T n < n) : P.ladderX n = [(n, none)] := by
  simp only [ladderX, ladderFuelX, hc, h, ↓reduceIte]

theorem ladderX_step (P : PTPPolicy) {n : ℕ} {T : PTPTable} (hc : P.choose n = some T)
    (h : ptpTightWidth T n < n) :
    P.ladderX n = (n, some T.k) :: P.ladderX (ptpTightWidth T n) := by
  unfold ladderX
  conv_lhs => simp only [ladderFuelX, hc, h, ↓reduceIte]
  rw [ladderFuelX_fuel P n (ptpTightWidth T n + 1) (ptpTightWidth T n) h (by omega)]

/-- One-step unfolding of the rule. -/
theorem chainContractsTight_iff (P : PTPPolicy) (n : ℕ) :
    P.chainContractsTight n = true ↔
      ∀ T, P.choose n = some T →
        T.k ≤ n ∧ ptpTightWidth T n < n ∧ P.chainContractsTight (ptpTightWidth T n) = true := by
  rcases hc : P.choose n with _ | T
  · simp [chainContractsTight, ladderX_none P hc, rungOK, hc]
  · by_cases h : ptpTightWidth T n < n
    · simp only [chainContractsTight, ladderX_step P hc h, List.all_cons, rungOK,
        Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq]
      constructor
      · rintro ⟨h1, h2⟩ T' rfl
        exact ⟨h1, h, h2⟩
      · intro H
        obtain ⟨h1, -, h2⟩ := H T rfl
        exact ⟨h1, h2⟩
    · simp only [chainContractsTight, ladderX_stuck P hc h, List.all_cons, List.all_nil,
        rungOK, hc, Option.isNone_some, Bool.and_true, Bool.false_eq_true, false_iff, not_forall]
      exact ⟨T, rfl, fun H => h H.2.1⟩

theorem ExactReach.trans_step {P : PTPPolicy} {n m : ℕ} {T : PTPTable}
    (hc : P.choose n = some T) (h : P.ExactReach (ptpTightWidth T n) m) : P.ExactReach n m := by
  induction h with
  | refl => exact .step .refl hc
  | step _ hc' ih => exact .step ih hc'

/-- **The rule, without the ladder**: `chainContractsTight P n` holds iff every table chosen at
every width the exact recursion from `n` reaches has `k ≤ m` and strictly shrinks the width. -/
theorem chainContractsTight_iff_reach (P : PTPPolicy) (n : ℕ) :
    P.chainContractsTight n = true ↔
      ∀ (m : ℕ) (T : PTPTable), P.ExactReach n m → P.choose m = some T →
        T.k ≤ m ∧ ptpTightWidth T m < m := by
  constructor
  · intro H m T hr hc
    have key : ∀ m, P.ExactReach n m → P.chainContractsTight m = true := by
      intro m hr
      induction hr with
      | refl => exact H
      | step _ hc' ih => exact (((chainContractsTight_iff P _).mp ih) _ hc').2.2
    obtain ⟨h1, h2, -⟩ := (chainContractsTight_iff P m).mp (key m hr) T hc
    exact ⟨h1, h2⟩
  · induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H
      refine (chainContractsTight_iff P n).mpr fun T hc => ?_
      obtain ⟨h1, h2⟩ := H n T .refl hc
      exact ⟨h1, h2, ih _ h2 fun m T' hr hc' => H m T' (ExactReach.trans_step hc hr) hc'⟩

end PTPPolicy

end PTP
end Shor
