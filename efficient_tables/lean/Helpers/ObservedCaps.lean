import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

namespace Paper

theorem observed_caps_preserve
    (a b l h r : Int) (hl : l ≤ r) (hr : r ≤ h) :
    max (max a (l + b)) (r + max (a - h) b) = max a (r + b) := by
  omega

theorem observed_caps_rectangle
    (a b x y l h : Int) (hlh : l ≤ h) :
    (max x (l + y) ≤ max a (l + b) ∧ max x (h + y) ≤ max a (h + b)) ↔
    (x ≤ max a (l + b) ∧ y ≤ max (a - h) b) := by
  omega

theorem observed_caps_canonical
    (a b l h R : Int)
    (hb : 0 ≤ b) (hba : b ≤ a) (hab : a ≤ b + R)
    (hl : 0 ≤ l) (hlh : l ≤ h) (hh : h ≤ R) :
    let A := max a (l + b)
    let B := max (a - h) b
    0 ≤ B ∧ B ≤ A ∧ A ≤ B + R ∧ a ≤ A ∧ b ≤ B := by
  dsimp
  omega

theorem observed_caps_kink
    (a b l h : Int) (hlh : l ≤ h) :
    max a (l + b) - max (a - h) b = min h (max l (a - b)) := by
  omega

theorem observed_caps_control :
    (max (6 : Int) (0 + 5), max (6 - 0) 5) = (6,6) ∧
    (max (6 : Int) (2 + 5), max (6 - 2) 5) = (7,5) := by
  decide

end Paper
