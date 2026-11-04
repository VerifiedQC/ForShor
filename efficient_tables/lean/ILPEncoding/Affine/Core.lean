import Model.Defs

/-! # Affine Decorations
Defines `Decoration` and the width recursion `nextWidth`, with `terminalProduct`, `terminalWidth` and the predicate `AllResidues` for decoration lists. Proves `step_divisor_residue`, `terminal_forces_all_residues` and the cleared form of contraction `cleared_contraction`.
-/

namespace Paper.AffineILP

structure Decoration where
  k : ℤ
  r : ℤ
  y : ℤ
  hk : 2 ≤ k
  hr0 : 0 ≤ r
  hrk : r < k

def nextWidth (P x : ℤ) (d : Decoration) : ℤ :=
  x + (P * d.k) * d.y - P * d.r

theorem step_divisor_residue (P x : ℤ) (d : Decoration)
    (hP : 0 < P) (hdiv : (P * d.k) ∣ nextWidth P x d) :
    P ∣ x ∧ x / P % d.k = d.r := by
  obtain ⟨z, hz⟩ := hdiv
  have hx : x = P * (d.k * (z - d.y) + d.r) := by
    dsimp [nextWidth] at hz
    nlinarith [hz]
  constructor
  · exact ⟨d.k * (z - d.y) + d.r, hx⟩
  · rw [hx]
    have hP0 : P ≠ 0 := ne_of_gt hP
    rw [Int.mul_ediv_cancel_left _ hP0]
    have hr : d.r % d.k = d.r := Int.emod_eq_of_lt d.hr0 d.hrk
    rw [Int.add_emod, Int.mul_emod, hr]
    simp [hr]

def terminalProduct (P : ℤ) : List Decoration → ℤ
  | [] => P
  | d :: rest => terminalProduct (P * d.k) rest

def terminalWidth (P x : ℤ) : List Decoration → ℤ
  | [] => x
  | d :: rest => terminalWidth (P * d.k) (nextWidth P x d) rest

def AllResidues (P x : ℤ) : List Decoration → Prop
  | [] => P ∣ x
  | d :: rest =>
      P ∣ x ∧ x / P % d.k = d.r ∧
        AllResidues (P * d.k) (nextWidth P x d) rest

theorem terminal_forces_all_residues (P x : ℤ) (ds : List Decoration)
    (hP : 0 < P)
    (hterminal : terminalProduct P ds ∣ terminalWidth P x ds) :
    AllResidues P x ds := by
  induction ds generalizing P x with
  | nil => exact hterminal
  | cons d rest ih =>
      have hk : 0 < d.k := lt_of_lt_of_le (by decide : (0 : ℤ) < 2) d.hk
      have hPk : 0 < P * d.k := mul_pos hP hk
      have hrest := ih (P * d.k) (nextWidth P x d) hPk hterminal
      have hdiv : P * d.k ∣ nextWidth P x d := by
        cases rest with
        | nil => exact hrest
        | cons e tail => exact hrest.1
      have hstep := step_divisor_residue P x d hP hdiv
      exact ⟨hstep.1, hstep.2, hrest⟩

theorem cleared_contraction (P k w w' : ℤ) (hP : 0 < P) (hk : 2 ≤ k) :
    P * k ≤ k * (P * w) - (P * k) * w' ↔ 1 ≤ w - w' := by
  have hPk : 0 < P * k := mul_pos hP (by omega : 0 < k)
  have heq : k * (P * w) - (P * k) * w' = (P * k) * (w - w') := by ring
  rw [heq]
  constructor
  · intro h
    by_contra hn
    have hd : w - w' ≤ 0 := by omega
    have hm : (P * k) * (w - w') ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hPk) hd
    omega
  · intro h
    have hd : 0 ≤ w - w' - 1 := by omega
    have hm : 0 ≤ (P * k) * (w - w' - 1) :=
      mul_nonneg (le_of_lt hPk) hd
    nlinarith

end Paper.AffineILP
