import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Angles as rational multiples of `π`

Every angle appearing in the gate language is a rational multiple of `π`.
Storing the rational coefficient instead of the real number is computable and
loses no information: `Angle.toReal` recovers the real angle whenever it is
needed for semantics.
-/

namespace Shor

/-- An angle in units of `π`: `a : Angle` denotes `a * π` radians. -/
abbrev Angle := ℚ

/-- Interpret an `Angle` (a multiple of `π`) as a real number of radians. -/
noncomputable def Angle.toReal (a : Angle) : ℝ := (a : ℝ) * Real.pi

@[simp] theorem Angle.toReal_zero : Angle.toReal 0 = 0 := by
  simp only [Angle.toReal]; push_cast; ring

theorem Angle.toReal_add (a b : Angle) :
    Angle.toReal (a + b) = Angle.toReal a + Angle.toReal b := by
  simp only [Angle.toReal]; push_cast; ring

theorem Angle.toReal_neg (a : Angle) :
    Angle.toReal (-a) = -Angle.toReal a := by
  simp only [Angle.toReal]; push_cast; ring

theorem Angle.toReal_sub (a b : Angle) :
    Angle.toReal (a - b) = Angle.toReal a - Angle.toReal b := by
  simp only [Angle.toReal]; push_cast; ring

theorem Angle.toReal_mul_rat (a c : ℚ) :
    Angle.toReal (a * c) = Angle.toReal a * (c : ℝ) := by
  simp only [Angle.toReal]; push_cast; ring

theorem Angle.toReal_div (a n : ℚ) :
    Angle.toReal (a / n) = Angle.toReal a / (n : ℝ) := by
  simp only [Angle.toReal]; push_cast; ring

theorem Angle.toReal_intCast (n : ℤ) :
    Angle.toReal (n : Angle) = (n : ℝ) * Real.pi := by
  simp only [Angle.toReal]; push_cast; ring

theorem Angle.toReal_natCast (n : ℕ) :
    Angle.toReal (n : Angle) = (n : ℝ) * Real.pi := by
  simp only [Angle.toReal]; push_cast; ring

end Shor
