import Mathlib.Tactic
import Mathlib
import PhaseProduct.Catalog.EndToEnd
import ILPEncoding.Bounds.StopBudget
import ILPEncoding.Bundles.Encoding
/- BEGIN Suffix.lean source_sha256=820b0256db3e8bb01226605a5f848480068d4f8a255f8aa74ff1f321a6677086 body_sha256=246fbe4949ac5e9f9c83787b9262e25b1072f4bbf002bae2491154026c8dea85 -/

set_option autoImplicit false

namespace Backend.Suffix

/-- The inclusive integer loop in `sp_ilp.suffix_search` and
`sp_lattice.svp_enum` starts at `floor(center)-q` and ends at
`floor(center)+q+1`. The extra endpoint is harmless. -/
theorem floor_window_complete (center : ℚ) (floor q z : ℤ)
    (hfloor : (floor : ℚ) ≤ center ∧ center < (floor : ℚ) + 1)
    (hq : 0 ≤ q)
    (hsq : ((z : ℚ) - center) ^ 2 ≤ (q : ℚ) ^ 2) :
    floor - q ≤ z ∧ z ≤ floor + q + 1 := by
  have hqQ : (0 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hleft : -(q : ℚ) ≤ (z : ℚ) - center := by
    by_contra h
    have h1 : 0 < -((z : ℚ) - center) - (q : ℚ) := by linarith
    have h2 : 0 < -((z : ℚ) - center) + (q : ℚ) := by linarith
    have hp := mul_pos h1 h2
    nlinarith
  have hright : (z : ℚ) - center ≤ (q : ℚ) := by
    by_contra h
    have h1 : 0 < ((z : ℚ) - center) - (q : ℚ) := by linarith
    have h2 : 0 < ((z : ℚ) - center) + (q : ℚ) := by linarith
    have hp := mul_pos h1 h2
    nlinarith
  constructor
  · exact_mod_cast (show ((floor - q : ℤ) : ℚ) ≤ (z : ℚ) by
      push_cast
      linarith [hfloor.1, hleft])
  · exact_mod_cast (show (z : ℚ) ≤ ((floor + q + 1 : ℤ) : ℚ) by
      push_cast
      linarith [hfloor.2, hright])

/-- A successful exact GS norm comparison cannot prune a candidate outside
the Fortran loop interval, provided `rroot` returned an upper square-root
bound and the Gram–Schmidt squared length is positive. -/
theorem residual_window_complete (center radius spent h : ℚ)
    (floor q z : ℤ)
    (hfloor : (floor : ℚ) ≤ center ∧ center < (floor : ℚ) + 1)
    (hq : 0 ≤ q) (hh : 0 < h)
    (hroot : radius - spent ≤ h * (q : ℚ) ^ 2)
    (hcandidate : spent + h * ((z : ℚ) - center) ^ 2 ≤ radius) :
    floor - q ≤ z ∧ z ≤ floor + q + 1 := by
  have hmul : h * ((z : ℚ) - center) ^ 2 ≤ h * (q : ℚ) ^ 2 := by
    linarith
  have hsq : ((z : ℚ) - center) ^ 2 ≤ (q : ℚ) ^ 2 := by
    exact (mul_le_mul_iff_of_pos_left hh).mp hmul
  exact floor_window_complete center floor q z hfloor hq hsq

end Backend.Suffix
/- END Suffix.lean -/

/- BEGIN Section.lean source_sha256=53e494738688b149d2ce64b195168bb94c3337e61b6c1aea39ddb4ee8cf418bd body_sha256=cddda535d178ec0bc293a8e216f3d76ac046c581ebbe132dbbeef96976d219a6 -/

set_option autoImplicit false

namespace Backend.Section

def dot {n : Nat} (a x : Fin n → ℚ) : ℚ :=
  ∑ j, a j * x j

def sectionPoint {n d : Nat} (x0 : Fin n → ℚ)
    (h : Fin n → Fin d → ℚ) (y : Fin d → ℚ) : Fin n → ℚ :=
  fun k => x0 k + ∑ j, h k j * y j

def sectionRows {m n d : Nat} (a : Fin m → Fin n → ℚ)
    (h : Fin n → Fin d → ℚ) : Fin m → Fin d → ℚ :=
  fun i j => ∑ k, a i k * h k j

def sectionRhs {m n : Nat} (a : Fin m → Fin n → ℚ)
    (b : Fin m → ℚ) (x0 : Fin n → ℚ) : Fin m → ℚ :=
  fun i => b i - dot (a i) x0

/-- Exact algebra of `sp_ilp.section_solve` lines 252–267: `qmm(a,h)` and
`b-qdot(a,x0)` describe precisely the preimage of every original row under
`x=x0+h*y`. No inequality is relaxed or strengthened. -/
theorem row_transform {m n d : Nat} (a : Fin m → Fin n → ℚ)
    (b : Fin m → ℚ) (x0 : Fin n → ℚ)
    (h : Fin n → Fin d → ℚ) (y : Fin d → ℚ) (i : Fin m) :
    dot (a i) (sectionPoint x0 h y) ≤ b i ↔
      dot (sectionRows a h i) y ≤ sectionRhs a b x0 i := by
  have heq : dot (a i) (sectionPoint x0 h y) =
      dot (a i) x0 + dot (sectionRows a h i) y := by
    simp only [dot, sectionPoint, sectionRows, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc]
  rw [heq]
  simp only [sectionRhs]
  constructor <;> intro hrow <;> linarith

theorem system_transform {m n d : Nat} (a : Fin m → Fin n → ℚ)
    (b : Fin m → ℚ) (x0 : Fin n → ℚ)
    (h : Fin n → Fin d → ℚ) (y : Fin d → ℚ) :
    (∀ i, dot (a i) (sectionPoint x0 h y) ≤ b i) ↔
      (∀ i, dot (sectionRows a h i) y ≤ sectionRhs a b x0 i) := by
  constructor <;> intro hrows i
  · exact (row_transform a b x0 h y i).mp (hrows i)
  · exact (row_transform a b x0 h y i).mpr (hrows i)

end Backend.Section
/- END Section.lean -/

/- BEGIN Bezout.lean source_sha256=95d6aee7c18a1874bd77f6098775f86c7e73d560d5bd9e5994a47211fb23cd04 body_sha256=6bc96679d43573b00f4eac7fab1148f5fe8eeb1122236758b246f5c2b6ba83eb -/

set_option autoImplicit false

namespace Backend.Bezout

/-- One two-column update performed by `sp_lattice.row_gcd`: the Bezout
column is `(s,t)` and the complementary column is `(-b/g,a/g)=(−B,A)`.
The hypotheses are the exact postconditions of `qbezout` and exact division. -/
theorem unit_det (a b g A B s t : ℤ)
    (ha : a = g * A) (hb : b = g * B)
    (hbez : s * a + t * b = g) (hg : g ≠ 0) :
    s * A + t * B = 1 := by
  have hmul : g * (s * A + t * B) = g * 1 := by
    calc
      g * (s * A + t * B) = s * a + t * b := by rw [ha, hb]; ring
      _ = g := hbez
      _ = g * 1 := by ring
  exact (mul_left_cancel₀ hg) hmul

theorem forward_row (a b g A B s t u v : ℤ)
    (ha : a = g * A) (hb : b = g * B)
    (hbez : s * a + t * b = g) :
    a * (s * u - B * v) + b * (t * u + A * v) = g * u := by
  calc
    a * (s * u - B * v) + b * (t * u + A * v) =
        (s * a + t * b) * u + (b * A - a * B) * v := by ring
    _ = g * u := by rw [hbez, ha, hb]; ring

theorem inverse_coordinates (A B s t x y : ℤ)
    (hdet : s * A + t * B = 1) :
    s * (A * x + B * y) - B * (-t * x + s * y) = x ∧
      t * (A * x + B * y) + A * (-t * x + s * y) = y := by
  constructor
  · calc
      s * (A * x + B * y) - B * (-t * x + s * y) =
          (s * A + t * B) * x := by ring
      _ = x := by rw [hdet]; ring
  · calc
      t * (A * x + B * y) + A * (-t * x + s * y) =
          (s * A + t * B) * y := by ring
      _ = y := by rw [hdet]; ring

/-- A single `row_gcd` Bezout update gives a bijective integral coordinate
change. Thus an affine row has an integer solution exactly when its gcd
divides the right-hand side; recursive section search loses no integer point
at this update. -/
theorem affine_row_iff (a b g A B s t rhs x y : ℤ)
    (ha : a = g * A) (hb : b = g * B)
    (hbez : s * a + t * b = g) (hg : g ≠ 0) :
    (a * x + b * y = rhs) ↔
      ∃ u v : ℤ, x = s * u - B * v ∧
        y = t * u + A * v ∧ g * u = rhs := by
  have hdet := unit_det a b g A B s t ha hb hbez hg
  constructor
  · intro hrow
    refine ⟨A * x + B * y, -t * x + s * y, ?_, ?_, ?_⟩
    · exact (inverse_coordinates A B s t x y hdet).1.symm
    · exact (inverse_coordinates A B s t x y hdet).2.symm
    · rw [ha, hb] at hrow
      nlinarith [hrow]
  · rintro ⟨u, v, hx, hy, hu⟩
    rw [hx, hy, forward_row a b g A B s t u v ha hb hbez]
    exact hu

theorem obstruction (a b g A B rhs x y : ℤ)
    (ha : a = g * A) (hb : b = g * B)
    (hrow : a * x + b * y = rhs) : g ∣ rhs := by
  refine ⟨A * x + B * y, ?_⟩
  rw [ha, hb] at hrow
  nlinarith [hrow]

end Backend.Bezout
/- END Bezout.lean -/

/- BEGIN Arithmetic.lean source_sha256=5dd08a18a7546e37f9d22361c845bc4054dc0e456dc1fa6d69644940a7a91a88 body_sha256=02455fe6197a0af84ecf919bf556c46e90b8ea5592ea9e9c1b069359d77b3d86 -/


set_option autoImplicit false

namespace Backend.Certificate

/-- The mathematical predicate checked by `sp_ilp.fits`: every original
integer row, lifted exactly to rational handles, accepts the candidate. -/
def rationalFits {m n : Nat} (a : Fin m → Fin n → ℤ)
    (b : Fin m → ℤ) (qx : Fin n → ℚ) : Prop :=
  ∀ i, (∑ j, (a i j : ℚ) * qx j) ≤ (b i : ℚ)

def integerFits {m n : Nat} (a : Fin m → Fin n → ℤ)
    (b : Fin m → ℤ) (x : Fin n → ℤ) : Prop :=
  ∀ i, (∑ j, a i j * x j) ≤ b i

/-- Successful `rtoi` conversions preserve every checked original row.
This is the exact output-certificate implication for public status 0; status
1, 2, 3 and 4 are not converted into certificates by this theorem. -/
theorem native_success_sound {m n : Nat} (a : Fin m → Fin n → ℤ)
    (b : Fin m → ℤ) (qx : Fin n → ℚ) (x : Fin n → ℤ)
    (hfit : rationalFits a b qx)
    (hconvert : ∀ j, qx j = (x j : ℚ)) : integerFits a b x := by
  intro i
  have hi := hfit i
  simp only [hconvert] at hi
  exact_mod_cast hi

/-- The native integer certificate is equivalent to nonnegativity of the
row slack `b-A*x`. This is the sign convention needed for the F7 row
evaluation bridge. -/
theorem native_row_slack {m n : Nat} (a : Fin m → Fin n → ℤ)
    (b : Fin m → ℤ) (x : Fin n → ℤ) (i : Fin m) :
    (∑ j, a i j * x j) ≤ b i ↔
      0 ≤ b i - ∑ j, a i j * x j := by
  omega

end Backend.Certificate


set_option autoImplicit false

namespace Backend.Rtoi

/-- Digits are supplied most-significant first, matching the descending
`j=size(...),1,-1` loop in `sp_rational.rtoi`. -/
def magnitude (base : ℤ) (digits : List ℤ) : ℤ :=
  digits.foldl (fun v digit => v * base + digit) 0

def negativeAccumulator (base : ℤ) (digits : List ℤ) : ℤ :=
  digits.foldl (fun v digit => v * base - digit) 0

theorem foldl_negative (base : ℤ) (digits : List ℤ) (start : ℤ) :
    digits.foldl (fun v digit => v * base - digit) (-start) =
      -(digits.foldl (fun v digit => v * base + digit) start) := by
  induction digits generalizing start with
  | nil => simp
  | cons digit rest ih =>
      simp only [List.foldl_cons]
      convert ih (start * base + digit) using 1 <;> ring

/-- The successful native-output Horner loop reconstructs precisely the
arbitrary-precision signed numerator, provided every native step is
representable. Its overflow guard is a separate range obligation. -/
theorem negativeAccumulator_eq (base : ℤ) (digits : List ℤ) :
    negativeAccumulator base digits = -magnitude base digits := by
  exact foldl_negative base digits 0

def signedOutput (base : ℤ) (negative : Bool) (digits : List ℤ) : ℤ :=
  if negative then negativeAccumulator base digits
  else -negativeAccumulator base digits

theorem signedOutput_eq (base : ℤ) (negative : Bool)
    (digits : List ℤ) :
    signedOutput base negative digits =
      (if negative then -magnitude base digits else magnitude base digits) := by
  simp [signedOutput, negativeAccumulator_eq]

end Backend.Rtoi


set_option autoImplicit false

namespace Backend.Limb

/-- The largest native intermediate in one `sp_rational.bmul` inner step:
old output digit + input-digit product + carry. Base is exactly 10^6. -/
theorem bmul_inner_lt_trillion (a b carry old : Nat)
    (ha : a < 1000000) (hb : b < 1000000)
    (hc : carry < 1000000) (ho : old < 1000000) :
    old + a * b + carry < 1000000000000 := by
  have hab : a * b ≤ 999999 * 999999 :=
    Nat.mul_le_mul (Nat.le_of_lt_succ ha) (Nat.le_of_lt_succ hb)
  omega

/-- Division/modulus normalization maintains a base-10^6 carry. -/
theorem bmul_next_carry_lt_base (a b carry old : Nat)
    (ha : a < 1000000) (hb : b < 1000000)
    (hc : carry < 1000000) (ho : old < 1000000) :
    (old + a * b + carry) / 1000000 < 1000000 := by
  have h := bmul_inner_lt_trillion a b carry old ha hb hc ho
  omega

/-- The `bsmall` multiply-by-one-digit path has the same bound. -/
theorem bsmall_inner_lt_trillion (a k carry : Nat)
    (ha : a < 1000000) (hk : k < 1000000)
    (hc : carry < 1000000) :
    a * k + carry < 1000000000000 := by
  have hak : a * k ≤ 999999 * 999999 :=
    Nat.mul_le_mul (Nat.le_of_lt_succ ha) (Nat.le_of_lt_succ hk)
  omega

end Backend.Limb
/- END Arithmetic.lean -/

/- BEGIN Greedy.lean source_sha256=b4415c46f2c55a550e5b0db5c518ff67fe2c7d388d584f516a0a774fbb5d572d body_sha256=a808dc76f035c3b6e513b408c9b4f3fc1bdf3f686ec1a9eb366aa65f2d502541 -/

set_option autoImplicit false

namespace Backend.Greedy

/-- A completed greedy exchange scan excludes any vertex replacement whose
determinant is more than twice the current simplex determinant. The usual
replacement-determinant identity then bounds that barycentric coordinate. -/
theorem barycentric_abs_le_two (det coord : ℚ)
    (hdet : 0 < det)
    (hreplace : |coord * det| ≤ 2 * det) : |coord| ≤ 2 := by
  rw [abs_mul, abs_of_pos hdet] at hreplace
  nlinarith

/-- Coordinates in [-2,2], centered at any point in [0,1], lie in the
closed radius-squared 9n ball. In the Fortran greedy simplex, the center
coordinate is 1/(n+1), and the strict version follows from n>=1. -/
theorem radius_sq_le_nine {n : Nat}
    (coord center : Fin n → ℚ)
    (hcoord : ∀ j, -2 ≤ coord j ∧ coord j ≤ 2)
    (hcenter : ∀ j, 0 ≤ center j ∧ center j ≤ 1) :
    (∑ j, (coord j - center j) ^ 2) ≤ 9 * n := by
  have hterm : ∀ j : Fin n, (coord j - center j) ^ 2 ≤ (9 : ℚ) := by
    intro j
    have hc := hcoord j
    have hd := hcenter j
    have hlow : 0 ≤ 3 + (coord j - center j) := by linarith
    have hhigh : 0 ≤ 3 - (coord j - center j) := by linarith
    nlinarith [mul_nonneg hlow hhigh]
  calc
    (∑ j, (coord j - center j) ^ 2) ≤ ∑ _j : Fin n, (9 : ℚ) :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = 9 * n := by simp [mul_comm]

end Backend.Greedy

/- END Greedy.lean -/

/- BEGIN Local.lean source_sha256=5ca1f6bef01e65db66178b3b724814d4dd1bdfc0fb245f7c1fddbdb274608337 body_sha256=cc81f2e95f653b2b32735d24a97a6bfdd60b33054fe1d58a0d60655009506492 -/

set_option autoImplicit false

/-!
Source-refinement bookkeeping for the live Fortran threshold frontend.

`seenTrace` and `eventTrace` abstract the `mark_targets` bitset scan in
`sp_oracle.f90:338–349` and `verify_seed:905–916`.  A separate refinement
must still establish that the Fortran limb rows and macros match the formal
integer-row/scanner transitions.  These declarations do not assert that.
-/

namespace ExecutionAlignment.Local

variable {α : Type*} [DecidableEq α]

def fresh (seen matched : Finset α) : Finset α := matched \ seen

def seenAfter (seen matched : Finset α) : Finset α := seen ∪ matched

def seenTrace : List (Finset α) → Finset α → Finset α
  | [], seen => seen
  | matched :: rest, seen => seenTrace rest (seenAfter seen matched)

noncomputable def eventTrace : List (Finset α) → Finset α → List α
  | [], _ => []
  | matched :: rest, seen =>
      (fresh seen matched).toList ++ eventTrace rest (seenAfter seen matched)

theorem seen_subset_seenTrace (ms : List (Finset α)) (seen : Finset α) :
    seen ⊆ seenTrace ms seen := by
  induction ms generalizing seen with
  | nil => simp [seenTrace]
  | cons matched rest ih =>
      simpa only [seenTrace, seenAfter] using
        (Finset.Subset.trans (Finset.subset_union_left) (ih (seen ∪ matched)))

theorem mem_eventTrace_iff {ms : List (Finset α)} {seen : Finset α} {x : α} :
    x ∈ eventTrace ms seen ↔ x ∈ seenTrace ms seen ∧ x ∉ seen := by
  induction ms generalizing seen with
  | nil => simp [eventTrace, seenTrace]
  | cons matched rest ih =>
      simp only [eventTrace, seenTrace, List.mem_append,
        Finset.mem_toList, fresh, Finset.mem_sdiff]
      rw [ih]
      simp only [seenAfter, Finset.mem_union]
      have hmatched : x ∈ matched → x ∈ seenTrace rest (seen ∪ matched) := by
        intro hx
        exact seen_subset_seenTrace rest (seen ∪ matched)
          (Finset.mem_union.mpr (Or.inr hx))
      tauto

theorem eventTrace_nodup (ms : List (Finset α)) (seen : Finset α) :
    (eventTrace ms seen).Nodup := by
  induction ms generalizing seen with
  | nil => simp [eventTrace]
  | cons matched rest ih =>
      simp only [eventTrace]
      apply List.nodup_append'.mpr
      refine ⟨Finset.nodup_toList _, ih (seenAfter seen matched), ?_⟩
      intro x hxFresh hxRest
      have hf : x ∈ matched ∧ x ∉ seen := by
        simpa [fresh] using hxFresh
      have hr := (mem_eventTrace_iff (ms := rest)
        (seen := seenAfter seen matched) (x := x)).mp hxRest
      exact (hr.2 (Finset.mem_union.mpr (Or.inr hf.1))).elim

theorem complete_eventTrace_perm {targets : Finset α}
    {ms : List (Finset α)} (hsub : seenTrace ms ∅ ⊆ targets)
    (hcomplete : targets ⊆ seenTrace ms ∅) :
    (eventTrace ms ∅).Perm targets.toList := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact eventTrace_nodup ms ∅
  · exact targets.nodup_toList
  · ext x
    simp [mem_eventTrace_iff, Finset.Subset.antisymm hsub hcomplete]

/- Monotone-cap NO reuse is the logic behind `sp_outer.f90:26–31,424–453`. -/
theorem dominated_no {F : Nat → Nat → Nat → Prop}
    (hmono : ∀ {a b c a' b' c'}, a ≤ a' → b ≤ b' → c ≤ c' →
      F a b c → F a' b' c')
    {a b c A B C : Nat}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (hno : ¬ F A B C) : ¬ F a b c := by
  intro hyes
  exact hno (hmono ha hb hc hyes)

/- Equal endpoint thresholds certify every skipped intermediate charge. -/
theorem plateau_of_equal_endpoints {θ : Nat → Nat}
    (hmono : ∀ {c d}, c ≤ d → θ d ≤ θ c)
    {lo mid hi : Nat} (hl : lo ≤ mid) (hh : mid ≤ hi)
    (heq : θ lo = θ hi) : θ mid = θ lo := by
  have hupper := hmono hl
  have hlower := hmono hh
  omega

/- A strict drop at c certifies exact minimum charge for each profile cap
   between θ(c) and θ(c−1)−1, assuming the threshold decision contract. -/
theorem drop_exact_minimum {θ : Nat → Nat} {F : Nat → Nat → Prop}
    (hiff : ∀ c a, F c a ↔ θ c ≤ a)
    (hmono : ∀ {c d a}, c ≤ d → F c a → F d a)
    {c a : Nat} (hc : 0 < c)
    (hyes : θ c ≤ a) (hno : a < θ (c - 1)) :
    F c a ∧ ∀ d < c, ¬ F d a := by
  constructor
  · exact (hiff c a).mpr hyes
  · intro d hd hfd
    have hprev : F (c - 1) a := hmono (by omega) hfd
    have := (hiff (c - 1) a).mp hprev
    omega

/- `sp_outer.f90:743–783` stores native rows as A*v ≤ b; F6/F7 stores
   the same row as intercept b and coefficients −A, evaluated ≥ 0. -/
theorem native_row_iff (t : Nat) (A v : Fin t → ℤ) (b : ℤ) :
    (∑ i, A i * v i) ≤ b ↔
      0 ≤ b + ∑ i, (-A i) * v i := by
  have hsum : (∑ i, (-A i) * v i) = -(∑ i, A i * v i) := by
    calc
      (∑ i, (-A i) * v i) = ∑ i, -(A i * v i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = -(∑ i, A i * v i) := by rw [Finset.sum_neg_distrib]
  rw [hsum]
  omega

/- The first 2t native rows are a finite box for every declared column.
   For t=0 the assignment type `Fin 0 → ℤ` is a singleton.  This elementary
   implication is the source-level boundedness input to the ILP backend;
   actual array/column-order identification remains a separate invariant. -/
theorem native_box_bounds (t : Nat) (lo hi v : Fin t → ℤ)
    (hrows : ∀ i : Fin t, v i ≤ hi i ∧ -v i ≤ -lo i) :
    ∀ i : Fin t, lo i ≤ v i ∧ v i ≤ hi i := by
  intro i
  obtain ⟨hupper, hlower⟩ := hrows i
  constructor <;> omega

end ExecutionAlignment.Local
/- END Local.lean -/

/- BEGIN Semantics.lean source_sha256=8a3b7c21f747a8337d15beb9c9367d9783cfb269e49923e58406d548164cd2c9 body_sha256=076aafe907f32b511c06b8dcc60ae752504565230a34a85bb467ee3633b59ddc -/

set_option autoImplicit false

/-! Mathematical semantics of the nonnegative native arithmetic in
`sp_arithmetic.f90:14–34,178–202`. Machine range and error propagation
remain separate implementation-refinement obligations. -/

namespace NativeArithmetic.Semantics

def satAdd (M x y : Nat) : Nat :=
  if M - y < x then M else x + y

def satMul (M x y : Nat) : Nat :=
  if x = 0 || y = 0 then 0
  else if M / y < x then M else x * y

theorem satAdd_eq_min (M x y : Nat) (hy : y ≤ M) :
    satAdd M x y = min M (x + y) := by
  unfold satAdd
  split_ifs with h
  · exact (min_eq_left (by omega : M ≤ x + y)).symm
  · exact (min_eq_right (by omega : x + y ≤ M)).symm

theorem satMul_eq_min (M x y : Nat) :
    satMul M x y = min M (x * y) := by
  unfold satMul
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  simp [hx, hy]
  split_ifs with h
  · have hlt : M < x * y := by
      exact (Nat.div_lt_iff_lt_mul (by omega : 0 < y)).mp h
    simp [min_eq_left (by omega : M ≤ x * y)]
  · have hle : x * y ≤ M := by
      have hn : ¬ M < x * y := by
        intro hlt
        exact h ((Nat.div_lt_iff_lt_mul (by omega : 0 < y)).mpr hlt)
      omega
    simp [min_eq_right hle]

def nativeLeaf (M : Nat) (price : Nat → Nat) (N w : Nat) : Nat :=
  let R := satMul M (satMul M N w) w
  if R = M then M else satMul M R (4 + price R)

theorem min_mul_right (M x y : Nat) :
    min M (min M x * y) = min M (x * y) := by
  by_cases hy : y = 0
  · simp [hy]
  have hypos : 1 ≤ y := by omega
  by_cases hx : x ≤ M
  · rw [min_eq_right hx]
  · have hMx : M ≤ x := by omega
    have hMy : M ≤ M * y := by
      calc M = M * 1 := by omega
           _ ≤ M * y := Nat.mul_le_mul_left M hypos
    have hxy : M ≤ x * y := by
      calc M ≤ x := hMx
           _ = x * 1 := by omega
           _ ≤ x * y := Nat.mul_le_mul_left x hypos
    rw [min_eq_left hMx, min_eq_left hMy, min_eq_left hxy]

theorem nativeLeaf_eq_clamped (M : Nat) (price : Nat → Nat)
    (N w : Nat) (hM : 1 ≤ M) :
    nativeLeaf M price N w = min M (Paper.PPEndToEnd.leafPP price N w) := by
  have hR : satMul M (satMul M N w) w = min M (N * w ^ 2) := by
    rw [satMul_eq_min, satMul_eq_min]
    rw [min_mul_right]
    congr 1
    ring
  unfold nativeLeaf
  rw [hR]
  by_cases hclamp : min M (N * w ^ 2) = M
  · rw [if_pos hclamp]
    have hbase : M ≤ N * w ^ 2 := by
      exact (min_eq_left_iff.mp hclamp)
    have hcost : M ≤ Paper.PPEndToEnd.leafPP price N w := by
      simp only [Paper.PPEndToEnd.leafPP]
      nlinarith [Nat.zero_le (price (N * w ^ 2))]
    exact (min_eq_left hcost).symm
  · rw [if_neg hclamp]
    have hbase : N * w ^ 2 < M := by
      have hle := min_le_left M (N * w ^ 2)
      omega
    rw [min_eq_right (by omega : N * w ^ 2 ≤ M)]
    rw [satMul_eq_min]
    simp only [Paper.PPEndToEnd.leafPP]
    congr 1
    ring

theorem exactChild (w k a b c : Nat) :
    w / k + 1 + max a (w % k + b) =
      Paper.Planner.childWidth k ⟨c,a,b⟩ w := by
  simp only [Paper.Planner.childWidth]
  rw [Nat.add_comm (w % k) b]

end NativeArithmetic.Semantics
/- END Semantics.lean -/

/- BEGIN SparseThreshold.lean source_sha256=d4aa729709ed68d912be289648b14463ac945d00c4110480dd798fd31ded5693 body_sha256=5a55c94f14927dc8cc6e28fa651153830638a930c975d02cb465b0fb9b08e3ce -/

set_option autoImplicit false

namespace ExecutionAlignment.SparseThreshold

open Paper.CountStage.StopBudget

/-- Accepted numeric polynomial envelope for the root-stop cost. -/
def thresholdEnvelope (k : Nat) : Nat := 2004 * k ^ 4

/-- Yes predicate for the actual numeric objective `opt`, not for its envelope. -/
def thresholdYes (opt : Nat → Nat) (k B : Nat) : Prop := opt k ≤ B

inductive ThresholdSymbol where
  | unary
  | separator
  | bit (value : Bool)
  deriving DecidableEq, Repr

/-- Exactly `log₂(B)+1` little-endian bits, indexed by position. -/
def binaryBits (B : Nat) : List Bool :=
  List.ofFn (fun i : Fin (Nat.log2 B + 1) => Nat.testBit B i)

/-- A canonical framed code: k unary marks, a separator, then a fixed-width bit field. -/
def thresholdCode (k B : Nat) : List ThresholdSymbol :=
  List.replicate k .unary ++ [.separator] ++ (binaryBits B).map .bit

def thresholdCodeLength (k B : Nat) : Nat := k + 1 + Nat.log2 B + 1

/-- Literal Boolean-list frame for the clipped-binary auxiliary language:
`0^k 1 binary(B)`. The separator makes the unary prefix uniquely parseable. -/
def thresholdBits (k B : Nat) : List Bool :=
  List.replicate k false ++ [true] ++ binaryBits B

/-- The original tally frame used in the hardness notes: `1^k 0 1^B`.
This remains a distinct encoding from the clipped-binary auxiliary. -/
def tallyThresholdBits (k B : Nat) : List Bool :=
  List.replicate k true ++ [false] ++ List.replicate B true

theorem binaryBits_length (B : Nat) : (binaryBits B).length = Nat.log2 B + 1 := by
  simp [binaryBits]

theorem thresholdBits_length (k B : Nat) :
    (thresholdBits k B).length = thresholdCodeLength k B := by
  simp [thresholdBits, thresholdCodeLength, binaryBits_length] <;> omega

theorem tallyThresholdBits_length (k B : Nat) :
    (tallyThresholdBits k B).length = k + B + 1 := by
  simp [tallyThresholdBits, Nat.add_assoc]

theorem tallyThresholdBits_injective :
    Function.Injective (fun p : Nat × Nat => tallyThresholdBits p.1 p.2) := by
  intro a b hab
  have hu := congrArg (List.takeWhile id) hab
  have hk : a.1 = b.1 := by
    have hlen := congrArg List.length hu
    simpa [tallyThresholdBits] using hlen
  have hd := congrArg (List.drop (a.1 + 1)) hab
  have hB : a.2 = b.2 := by
    have hlen := congrArg List.length hd
    simp only [tallyThresholdBits, hk, List.length_drop, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil] at hlen
    omega
  exact Prod.ext hk hB
theorem binaryBits_injective : Function.Injective binaryBits := by
  intro a b hab
  have hw : Nat.log2 a = Nat.log2 b := by
    have := congrArg List.length hab
    simpa [binaryBits] using this
  have hab' : binaryBits a = binaryBits b := by simpa [hw] using hab
  have hfun : (fun i : Fin (Nat.log2 a + 1) => Nat.testBit a i) =
      (fun i : Fin (Nat.log2 a + 1) => Nat.testBit b i) := by
    apply List.ofFn_injective
    simpa [binaryBits, hw] using hab'
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < Nat.log2 a + 1
  · exact congrFun hfun ⟨i, hi⟩
  · have hi' : Nat.log2 a + 1 ≤ i := by omega
    have ha : a < 2 ^ (Nat.log2 a + 1) := by
      by_cases hz : a = 0
      · simp [hz]
      · exact (Nat.log2_lt hz).mp (by omega)
    have hb : b < 2 ^ (Nat.log2 b + 1) := by
      by_cases hz : b = 0
      · simp [hz]
      · exact (Nat.log2_lt hz).mp (by omega)
    have hp : 2 ^ (Nat.log2 a + 1) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by decide) hi'
    have hpa : a < 2 ^ i := ha.trans_le hp
    have hpb : b < 2 ^ i := by simpa [hw] using hb.trans_le (by simpa [hw] using hp)
    rw [Nat.testBit_eq_false_of_lt hpa, Nat.testBit_eq_false_of_lt hpb]

theorem thresholdBits_injective :
    Function.Injective (fun p : Nat × Nat => thresholdBits p.1 p.2) := by
  intro a b hab
  have hu := congrArg (List.takeWhile (fun x => !x)) hab
  have hk : a.1 = b.1 := by
    have hlen := congrArg List.length hu
    simpa [thresholdBits] using hlen
  have hd := congrArg (List.drop (a.1 + 1)) hab
  have hb : binaryBits a.2 = binaryBits b.2 := by
    simpa [thresholdBits, hk, List.drop_append] using hd
  exact Prod.ext hk (binaryBits_injective hb)

theorem thresholdCode_injective : Function.Injective (fun p : Nat × Nat => thresholdCode p.1 p.2) := by
  intro a b h
  have hu := congrArg (List.takeWhile (fun s => decide (s = .unary))) h
  have hk : a.1 = b.1 := by
    have hlen := congrArg List.length hu
    simpa [thresholdCode] using hlen
  have hd := congrArg (List.drop (a.1 + 1)) h
  have hb : (binaryBits a.2).map ThresholdSymbol.bit =
      (binaryBits b.2).map ThresholdSymbol.bit := by
    simpa [thresholdCode, hk, List.drop_append] using hd
  have hmap : Function.Injective (ThresholdSymbol.bit : Bool → ThresholdSymbol) := by
    intro x y hxy
    cases hxy
    rfl
  have hbits : binaryBits a.2 = binaryBits b.2 :=
    (List.map_injective_iff.mpr hmap) hb
  have hv := binaryBits_injective hbits
  exact Prod.ext hk hv

theorem thresholdCode_length (k B : Nat) :
    (thresholdCode k B).length = thresholdCodeLength k B := by
  simp [thresholdCode, thresholdCodeLength, binaryBits_length, List.length_map] <;> omega

theorem unary_parameter_le_code_length (k B : Nat) :
    k ≤ thresholdCodeLength k B := by
  unfold thresholdCodeLength
  omega

theorem thresholdEnvelope_mono {a b : Nat} (hab : a ≤ b) :
    thresholdEnvelope a ≤ thresholdEnvelope b := by
  unfold thresholdEnvelope
  exact Nat.mul_le_mul_left 2004 ((Nat.pow_le_pow_left hab) 4)

theorem rootThreshold_fits_envelope {k : Nat} (hk : 1 ≤ k) :
    rootStopBudget k ≤ thresholdEnvelope k := rootStopBudget_le_2004_n4 hk

/-- Finite census of yes pairs for any optimization objective. -/
def boundedYesPairCensus (opt : Nat → Nat) (N : Nat) : Finset (Nat × Nat) :=
  ((Finset.range N).product (Finset.range (thresholdEnvelope N + 1))).filter
    (fun p => opt (p.1 + 1) ≤ p.2)

theorem boundedYesPairCensus_card_le (opt : Nat → Nat) (N : Nat) :
    (boundedYesPairCensus opt N).card ≤ N * (thresholdEnvelope N + 1) := by
  unfold boundedYesPairCensus
  calc
    _ ≤ ((Finset.range N).product
        (Finset.range (thresholdEnvelope N + 1))).card := by
      exact Finset.card_filter_le _ _
    _ = N * (thresholdEnvelope N + 1) := by simp

theorem bounded_code_in_census {opt : Nat → Nat} {N k B : Nat}
    (hk : 1 ≤ k)
    (hsize : thresholdCodeLength k B ≤ N)
    (hB : B ≤ thresholdEnvelope k)
    (hfit : opt k ≤ thresholdEnvelope k)
    (hyes : opt k ≤ B) :
    (k - 1, B) ∈ boundedYesPairCensus opt N := by
  have hlen : k ≤ N := (unary_parameter_le_code_length k B).trans hsize
  unfold boundedYesPairCensus
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · rw [Finset.mem_range]
      omega
    · rw [Finset.mem_range]
      have hp := thresholdEnvelope_mono hlen
      omega
  · simpa [Nat.sub_add_cancel hk] using hyes

def canonicalBinaryWidthValues (m : Nat) : Finset Nat :=
  (Finset.range (2 ^ (m - 1))).image (fun j => 2 ^ (m - 1) + j)

theorem canonicalBinaryWidthValues_card {m : Nat} :
    (canonicalBinaryWidthValues m).card = 2 ^ (m - 1) := by
  unfold canonicalBinaryWidthValues
  calc
    _ = (Finset.range (2 ^ (m - 1))).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      change 2 ^ (m - 1) + a = 2 ^ (m - 1) + b at hab
      exact Nat.add_left_cancel hab
    _ = 2 ^ (m - 1) := by simp

theorem canonicalBinaryWidthValues_upper {m B : Nat}
    (hm : 1 ≤ m) (hB : B ∈ canonicalBinaryWidthValues m) : B < 2 ^ m := by
  unfold canonicalBinaryWidthValues at hB
  rcases Finset.mem_image.mp hB with ⟨j, hj, rfl⟩
  have hj' : j < 2 ^ (m - 1) := Finset.mem_range.mp hj
  have hpow : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
    calc
      2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ (m - 1) * 2 := by ring
      _ = 2 ^ (m - 1 + 1) := by rw [Nat.pow_succ]
      _ = 2 ^ m := by rw [hm']
  omega

theorem canonicalBinaryWidthValues_lower {m B : Nat}
    (hB : B ∈ canonicalBinaryWidthValues m) : 2 ^ (m - 1) ≤ B := by
  unfold canonicalBinaryWidthValues at hB
  rcases Finset.mem_image.mp hB with ⟨j, hj, rfl⟩
  omega

theorem canonicalBinaryWidthValues_log2 {m B : Nat}
    (hm : 1 ≤ m) (hB : B ∈ canonicalBinaryWidthValues m) :
    Nat.log2 B = m - 1 := by
  have hlo := canonicalBinaryWidthValues_lower hB
  have hhi := canonicalBinaryWidthValues_upper hm hB
  have hne : B ≠ 0 := by
    have hp : 0 < 2 ^ (m - 1) := Nat.pow_pos (by decide)
    omega
  have hloLog : m - 1 ≤ Nat.log2 B := (Nat.le_log2 hne).2 hlo
  have hhiLog : Nat.log2 B < m := (Nat.log2_lt hne).mpr hhi
  omega

theorem canonicalBinaryWidthValues_code_length {k m B : Nat}
    (hm : 1 ≤ m) (hB : B ∈ canonicalBinaryWidthValues m) :
    (thresholdBits k B).length = k + m + 1 := by
  rw [thresholdBits_length]
  unfold thresholdCodeLength
  rw [canonicalBinaryWidthValues_log2 hm hB]
  omega

def canonicalBinaryWidthCodes (k m : Nat) : Finset (List Bool) :=
  (canonicalBinaryWidthValues m).image (fun B => thresholdBits k B)

theorem canonicalBinaryWidthCodes_card {k m : Nat} :
    (canonicalBinaryWidthCodes k m).card = 2 ^ (m - 1) := by
  unfold canonicalBinaryWidthCodes
  calc
    _ = (canonicalBinaryWidthValues m).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      have hp : (k, a) = (k, b) :=
        thresholdBits_injective (by simpa using hab)
      exact congrArg Prod.snd hp
    _ = 2 ^ (m - 1) := canonicalBinaryWidthValues_card

def canonicalBinaryWidthYesValues (opt : Nat → Nat) (k m : Nat) :
    Finset Nat :=
  (canonicalBinaryWidthValues m).filter (fun B => decide (opt k ≤ B))

noncomputable def canonicalBinaryWidthYesCodes (opt : Nat → Nat) (k m : Nat) :
    Finset (List Bool) :=
  (canonicalBinaryWidthYesValues opt k m).image (fun B => thresholdBits k B)

theorem unbounded_binary_tail_yes_count {opt : Nat → Nat} {k m : Nat}
    (hm : 1 ≤ m) (hopt : opt k ≤ 2 ^ (m - 1)) :
    (canonicalBinaryWidthYesValues opt k m).card = 2 ^ (m - 1) := by
  have hall : canonicalBinaryWidthYesValues opt k m = canonicalBinaryWidthValues m := by
    unfold canonicalBinaryWidthYesValues
    apply Finset.filter_eq_self.mpr
    intro B hB
    have _hwidth := canonicalBinaryWidthValues_upper hm hB
    simp only [decide_eq_true_eq]
    exact le_trans hopt (canonicalBinaryWidthValues_lower hB)
  rw [hall, canonicalBinaryWidthValues_card]

theorem canonicalBinaryWidthYesCodes_card {opt : Nat → Nat} {k m : Nat}
    (hm : 1 ≤ m) (hopt : opt k ≤ 2 ^ (m - 1)) :
    (canonicalBinaryWidthYesCodes opt k m).card = 2 ^ (m - 1) := by
  unfold canonicalBinaryWidthYesCodes
  calc
    _ = (canonicalBinaryWidthYesValues opt k m).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      have hp : (k, a) = (k, b) :=
        thresholdBits_injective (by simpa using hab)
      exact congrArg Prod.snd hp
    _ = 2 ^ (m - 1) := unbounded_binary_tail_yes_count hm hopt

theorem canonicalBinaryWidthYesCodes_length {opt : Nat → Nat} {k m : Nat}
    (hm : 1 ≤ m) (hopt : opt k ≤ 2 ^ (m - 1))
    {code : List Bool} (hcode : code ∈ canonicalBinaryWidthYesCodes opt k m) :
    code.length = k + m + 1 := by
  unfold canonicalBinaryWidthYesCodes at hcode
  rcases Finset.mem_image.mp hcode with ⟨B, hB, rfl⟩
  have hB' : B ∈ canonicalBinaryWidthValues m :=
    (Finset.mem_filter.mp hB).1
  exact canonicalBinaryWidthValues_code_length hm hB'

theorem normalize_threshold_iff {opt : Nat → Nat} {k B : Nat}
    (hfit : opt k ≤ thresholdEnvelope k) :
    thresholdYes opt k B ↔ thresholdYes opt k (min B (thresholdEnvelope k)) := by
  unfold thresholdYes
  omega

theorem normalize_root_stop_threshold_iff {k B : Nat} (hk : 1 ≤ k) :
    thresholdYes rootStopBudget k B ↔
      thresholdYes rootStopBudget k (min B (thresholdEnvelope k)) :=
  normalize_threshold_iff (rootThreshold_fits_envelope hk)

/-- The accepted finite optimizer objective at width W, with arity bound K fixed. -/
noncomputable def actualBenchmarkOpt (K W : Nat) : Nat :=
  (Paper.ComputableProfileProvider.optimize K W 1).benchmarkCost Paper.PPEndToEnd.tauRS 1

/-- The actual benchmark optimum is bounded by the accepted root-stop budget. -/
theorem actualBenchmarkOpt_le_rootStop {K W : Nat}
    (hK : 2 ≤ K) (hW : 1 ≤ W) :
    actualBenchmarkOpt K W ≤ rootStopBudget W := by
  obtain ⟨_, v', _, _, hv, hroot, _, _, _, _, _, _, _, _, _⟩ :=
    Paper.F7MatrixFinal.optimizer_canonical_matrix_bits hK hW
  change (Paper.ComputableProfileProvider.optimize K W 1).benchmarkCost Paper.PPEndToEnd.tauRS 1 ≤ rootStopBudget W
  rw [← hv]
  exact hroot

/-- For fixed K, the actual optimizer threshold fits the numeric envelope. -/
theorem actualBenchmarkOpt_le_envelope {K W : Nat}
    (hK : 2 ≤ K) (hW : 1 ≤ W) :
    actualBenchmarkOpt K W ≤ thresholdEnvelope W := by
  exact (actualBenchmarkOpt_le_rootStop hK hW).trans
    (rootThreshold_fits_envelope hW)


/-- Census specialization for the actual accepted benchmark objective, with K fixed.
The optimizer-to-root-stop bound is imported from the accepted F7 optimizer theorem. -/
theorem actual_optimizer_code_in_census {K W N B : Nat}
    (hK : 2 ≤ K) (hW : 1 ≤ W)
    (hsize : thresholdCodeLength W B ≤ N)
    (hB : B ≤ thresholdEnvelope W)
    (hyes : actualBenchmarkOpt K W ≤ B) :
    (W - 1, B) ∈ boundedYesPairCensus (actualBenchmarkOpt K) N := by
  apply bounded_code_in_census (opt := actualBenchmarkOpt K) (hk := hW)
    (hsize := hsize) (hB := hB)
    (hfit := actualBenchmarkOpt_le_envelope hK hW) (hyes := hyes)
end ExecutionAlignment.SparseThreshold




/- END SparseThreshold.lean -/
