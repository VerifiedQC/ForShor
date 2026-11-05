import Mathlib.Data.Int.Basic

/- Elementary scanner identities only; no global optimizer is formalized. -/
namespace Paper.GlobalScanner

theorem collapse_right (x y s c : ℤ) (hc : 0 ≤ c) :
    max (max 0 (x-s)) (max 0 (y-s)-c) =
      max 0 (max x (y-c)-s) := by omega

theorem collapse_left (x y s c : ℤ) :
    max (x+s) (y+s-c) = max x (y-c)+s := by omega

theorem collapse_neg (x y c : ℤ) :
    max (x+1) (y+1-c) = max x (y-c)+1 := by omega

theorem collapse_add (p q pR qR s c : ℤ) :
    max (1+max p (q+s)) (1+max pR (qR+s)-c) =
      1+max (max p (pR-c)) (max q (qR-c)+s) := by omega

theorem collapse_history (h hR x xR c : ℤ) :
    max (max h x) (max hR xR-c) =
      max (max h (hR-c)) (max x (xR-c)) := by omega

theorem collapse_cap (h hR a c : ℤ) :
    (h ≤ a ∧ hR ≤ a+c) ↔ max h (hR-c) ≤ a := by omega

theorem collapse_initial (r d : ℤ) (hd : 0 ≤ d) :
    max 0 (r-(r-d)) = d := by omega

theorem backward_right (v s r : ℤ) :
    max v (max 0 (v-s)+r) = max r (v+max 0 (r-s)) := by omega

theorem backward_add (p q s r : ℤ) (hr : 0 ≤ r) :
    max p (1+max p (q+s)+r) = max (p+r+1) (q+s+r+1) := by omega

end Paper.GlobalScanner
