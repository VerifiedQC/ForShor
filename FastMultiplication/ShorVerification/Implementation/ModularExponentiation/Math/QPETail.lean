import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic

/-!
# QPE Tail Bounds — Pure Mathematics

The numerical core of Algorithm 1's Step-1 quantum-phase-estimation tail-mass
bound, extracted from `Proofs/Step1QPE.lean` as a semantics-free module: the
finite QPE kernel `qpeKernel`, its chord-bound estimate, and the floor-shell
summation argument that turns the pointwise majorant into the closed-form tail
bound `qpeKernel_bad_mass_le_grid_ratio`. Nothing here refers to the project's
state-semantics or register-encoding layer — every declaration is stated
purely in terms of `M : ℕ`, real phases, and finite sums.
-/

/--
The normalized Fourier kernel for a phase `θ`, sampled on an `M`-point
inverse-QFT grid.

The caller supplies `θ` as the ratio of its target residue to the modulus.
-/
noncomputable def qpeKernel
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M) : ℂ :=
  (1 / (M : ℂ)) *
    ∑ z : Fin M,
      Complex.exp
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (((θ : ℂ) - ((t.1 : ℂ) / (M : ℂ))) * (z.1 : ℂ)))

/-! =========================================================
    Circular distance and the zero-phase kernel

The tail estimate is stated in terms of the distance from `θ` to a grid point
measured on the unit circle, since a label just below `1` is close to a phase
just above `0`. This section fixes that notion and the associated tail set,
then disposes of the degenerate case `θ = 0`: there the kernel is a geometric
sum over a nontrivial root of unity, so it vanishes at every nonzero label and
the bad mass is zero outright rather than merely small.
========================================================= -/

section CircularDistanceAndZeroPhase

/--
Distance on the `M`-point QPE circle between a phase `θ ∈ [0,1)` and
the output label `t / M`.

The absolute value around the second term keeps the definition nonnegative
without making any range assumption in the definition itself.
-/
noncomputable def qpeCircularDistance
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M) : ℝ :=
  min
    |θ - ((t.1 : ℝ) / (M : ℝ))|
    |1 - (|θ - ((t.1 : ℝ) / (M : ℝ))|)|

/-- The labels whose circular distance to `θ` is at least `δ`, i.e. the tail. -/
noncomputable def qpeCircularTail
    (M : ℕ)
    (θ δ : ℝ) : Finset (Fin M) :=
  Finset.univ.filter
    (fun t => δ ≤ qpeCircularDistance M θ t)

/-- At zero phase the kernel is a plain geometric sum of a root of unity. -/
private lemma qpeKernel_zero_phase_eq_geometric_sum
    (M : ℕ)
    (t : Fin M)
    (_hM : 0 < (M : ℝ)) :
    qpeKernel M 0 t
      =
    (1 / (M : ℂ)) *
      ∑ z : Fin M,
        (Complex.exp
          (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            ((t.1 : ℂ) / (M : ℂ)))) ^ z.1) := by
  unfold qpeKernel
  apply congrArg (fun S : ℂ => (1 / (M : ℂ)) * S)
  apply Finset.sum_congr rfl
  intro z hz
  simp
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- The zero-phase root is an `M`-th root of unity. -/
private lemma qpe_zero_phase_root_pow_M
    (M j : ℕ)
    (hM : 0 < (M : ℝ)) :
    (Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((j : ℂ) / (M : ℂ)))) ^ M) = 1 := by
  have hMnat : 0 < M := by exact_mod_cast hM
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hMnat
  rw [← Complex.exp_nat_mul]
  have harg :
      (M : ℂ) * (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((j : ℂ) / (M : ℂ))))
        = -((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    field_simp [hM0]
    push_cast
    ring
  rw [harg]
  have hbase : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I]
    simp
  calc
    Complex.exp (-((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)))
        = Complex.exp ((j : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I))) := by
          congr 1
          ring
    _ = (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I))) ^ j := by
          rw [Complex.exp_nat_mul]
    _ = 1 := by simp [hbase]

/-- For a nonzero label below `M`, that root of unity is not `1`. -/
private lemma qpe_zero_phase_root_ne_one
    (M j : ℕ)
    (hM : 0 < (M : ℝ))
    (hjpos : 0 < j)
    (hjlt : j < M) :
    Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((j : ℂ) / (M : ℂ)))) ≠ 1 := by
  intro hroot
  have hMnat : 0 < M := by exact_mod_cast hM
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hMnat
  rcases Complex.exp_eq_one_iff.mp hroot with ⟨k, hk⟩
  have hfactor :
      (-((j : ℝ) / (M : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    calc
      (-((j : ℝ) / (M : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
          = -(((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((j : ℂ) / (M : ℂ))) := by
            field_simp [hM0]
            push_cast
            ring
      _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by simpa using hk
  have hscalarC : (-((j : ℝ) / (M : ℝ)) : ℂ) = (k : ℂ) := by
    exact mul_right_cancel₀ Complex.two_pi_I_ne_zero hfactor
  have hscalar : -((j : ℝ) / (M : ℝ)) = (k : ℝ) := by
    simpa using congrArg Complex.re hscalarC
  have hjRpos : 0 < (j : ℝ) := by exact_mod_cast hjpos
  have hjRlt : (j : ℝ) < (M : ℝ) := by exact_mod_cast hjlt
  have hfrac_pos : 0 < (j : ℝ) / (M : ℝ) := div_pos hjRpos hM
  have hfrac_lt_one : (j : ℝ) / (M : ℝ) < 1 := (div_lt_one hM).2 hjRlt
  have hk_lt_zero : (k : ℝ) < 0 := by linarith
  have hminus_one_lt_k : (-1 : ℝ) < (k : ℝ) := by linarith
  have hk_lt_zero_int : k < 0 := by exact_mod_cast hk_lt_zero
  have hminus_one_lt_k_int : (-1 : ℤ) < k := by exact_mod_cast hminus_one_lt_k
  omega

/-- A full geometric sum over a nontrivial `M`-th root of unity vanishes. -/
private lemma qpe_zero_phase_geometric_sum_eq_zero
    (M : ℕ)
    (ζ : ℂ)
    (hζM : ζ ^ M = 1)
    (hζne : ζ ≠ 1) :
    ∑ z : Fin M, ζ ^ z.1 = 0 := by
  have hgeom : (∑ z : Fin M, ζ ^ z.1) * (ζ - 1) = ζ ^ M - 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using (geom_sum_mul ζ M)
  have hzero : (∑ z : Fin M, ζ ^ z.1) * (ζ - 1) = 0 := by simpa [hζM] using hgeom
  exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hζne)

/-- Hence the zero-phase kernel vanishes at every nonzero label. -/
private lemma qpeKernel_zero_phase_eq_zero_of_nonzero_label
    (M : ℕ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (ht : t.1 ≠ 0) :
    qpeKernel M 0 t = 0 := by
  let ζ : ℂ := Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t.1 : ℂ) / (M : ℂ))))
  have htpos : 0 < t.1 := Nat.pos_of_ne_zero ht
  have hpow : ζ ^ M = 1 := by simpa [ζ] using qpe_zero_phase_root_pow_M M t.1 hM
  have hne : ζ ≠ 1 := by
    simpa [ζ] using qpe_zero_phase_root_ne_one M t.1 hM htpos t.isLt
  calc
    qpeKernel M 0 t = (1 / (M : ℂ)) * ∑ z : Fin M, ζ ^ z.1 := by
          simpa [ζ] using qpeKernel_zero_phase_eq_geometric_sum M t hM
    _ = 0 := by
      rw [qpe_zero_phase_geometric_sum_eq_zero M ζ hpow hne]
      simp

/--
For zero phase, the finite QPE kernel is exactly the computational-basis
delta distribution: its only nonzero amplitude is label zero.
-/
lemma qpeKernel_zero_phase_bad_mass_zero
    (M : ℕ)
    (δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hδ : 0 < δ) :
    ∑ t ∈ Finset.univ.filter
        (fun t : Fin M => ¬ |(0 : ℝ) - ((t.1 : ℝ) / (M : ℝ))| < δ),
      ‖qpeKernel M 0 t‖ ^ 2 = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t ht
  have ht_bad : ¬ |(0 : ℝ) - ((t.1 : ℝ) / (M : ℝ))| < δ := (Finset.mem_filter.mp ht).2
  have ht_nonzero : t.1 ≠ 0 := by
    intro ht0
    apply ht_bad
    simp [ht0, hδ]
  rw [qpeKernel_zero_phase_eq_zero_of_nonzero_label M t hM ht_nonzero]
  simp

end CircularDistanceAndZeroPhase

/-! =========================================================
    Chord bound on the kernel

The pointwise estimate that drives everything numerical. Writing the kernel as
a geometric sum in the root `qpeRoot` gives
`M * kernel * (root - 1) = root ^ M - 1`. The right-hand side has modulus at
most `2`, while the chord `‖root - 1‖` is bounded below by `4` times the
circular distance, using `2 * min u (1 - u) ≤ |sin (π u)|`. Rearranging yields
the majorant `‖kernel‖ ^ 2 ≤ 1 / (4 * (M * dist) ^ 2)`.
========================================================= -/

section KernelChordBound

/-- Signed offset of the label `t` from the phase `θ`. -/
private noncomputable def qpeOffset
    (M : ℕ) (θ : ℝ) (t : Fin M) : ℝ :=
  θ - ((t.1 : ℝ) / (M : ℝ))

/-- The unit-circle root whose powers the kernel sums. -/
private noncomputable def qpeRoot
    (M : ℕ) (θ : ℝ) (t : Fin M) : ℂ :=
  Complex.exp
    (Complex.I *
      ((2 * Real.pi * qpeOffset M θ t : ℝ) : ℂ))

/--
Geometric-sum identity: `M * kernel * (root - 1) = root ^ M - 1`.

This is the only place the kernel is manipulated as a sum; everything after it
is an estimate on the two sides of this equation.
-/
private lemma qpeKernel_mul_root_chord
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ)) :
    qpeKernel M θ t *
        ((M : ℂ) * (qpeRoot M θ t - 1))
      =
    (qpeRoot M θ t) ^ M - 1 := by
  classical
  let ζ : ℂ := qpeRoot M θ t

  change
    qpeKernel M θ t * ((M : ℂ) * (ζ - 1))
      =
    ζ ^ M - 1

  have hM0R : (M : ℝ) ≠ 0 :=
    ne_of_gt hM

  have hM0 : (M : ℂ) ≠ 0 := by
    exact_mod_cast hM0R

  have hfrac :
      (((t.1 : ℝ) / (M : ℝ) : ℂ))
        =
      (t.1 : ℂ) / (M : ℂ) := by
    norm_cast

  have hterm :
      ∀ z : Fin M,
        Complex.exp
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            (((θ : ℂ) - ((t.1 : ℂ) / (M : ℂ))) * (z.1 : ℂ)))
          =
        ζ ^ z.1 := by
    intro z
    dsimp [ζ, qpeRoot, qpeOffset]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

  have hkernel : qpeKernel M θ t = (1 / (M : ℂ)) * ∑ z : Fin M, ζ ^ z.1 := by
    unfold qpeKernel
    apply congrArg (fun S : ℂ => (1 / (M : ℂ)) * S)
    apply Finset.sum_congr rfl
    intro z hz
    exact hterm z
  have hgeom : (∑ z : Fin M, ζ ^ z.1) * (ζ - 1) = ζ ^ M - 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact geom_sum_mul ζ M
  have hcancel : (1 / (M : ℂ)) * (M : ℂ) = 1 := by field_simp [hM0]
  calc
    qpeKernel M θ t * ((M : ℂ) * (ζ - 1))
        = ((1 / (M : ℂ)) * ∑ z : Fin M, ζ ^ z.1) * ((M : ℂ) * (ζ - 1)) := by rw [hkernel]
    _ = ((1 / (M : ℂ)) * (M : ℂ)) * ((∑ z : Fin M, ζ ^ z.1) * (ζ - 1)) := by ring
    _ = (∑ z : Fin M, ζ ^ z.1) * (ζ - 1) := by
          rw [hcancel]
          simp
    _ = ζ ^ M - 1 := hgeom

/--
Jordan-type inequality `2 * min u (1 - u) ≤ |sin (π u)|` on the unit interval.

Concavity of the sine on `[0, π]` makes the chord through the endpoints a lower
bound; the `min` accounts for the two halves of the interval.
-/
private lemma qpe_two_mul_min_le_abs_sin
    (u : ℝ)
    (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    2 * min u (1 - u) ≤ |Real.sin (Real.pi * u)| := by
  by_cases hhalf : u ≤ (1 / 2 : ℝ)
  ·
    have hmin : min u (1 - u) = u := by
      apply min_eq_left
      linarith
    have harg_nonneg : 0 ≤ Real.pi * u := mul_nonneg (le_of_lt Real.pi_pos) hu0
    have harg_le : Real.pi * u ≤ Real.pi / 2 := by
      have hprod : 0 ≤ Real.pi * ((1 / 2 : ℝ) - u) :=
        mul_nonneg (le_of_lt Real.pi_pos) (by linarith)
      nlinarith
    have hJordan :=
      Real.mul_abs_le_abs_sin (x := Real.pi * u)
        (by
          rw [abs_of_nonneg harg_nonneg]
          exact harg_le)
    rw [abs_of_nonneg harg_nonneg] at hJordan
    calc
      2 * min u (1 - u) = 2 * u := by rw [hmin]
      _ = (2 / Real.pi) * (Real.pi * u) := by field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (Real.pi * u)| := hJordan
  ·
    have hhalf' : (1 / 2 : ℝ) < u := lt_of_not_ge hhalf
    have hcomp0 : 0 ≤ 1 - u := by linarith
    have hcomp_half : 1 - u ≤ (1 / 2 : ℝ) := by linarith
    have hmin : min u (1 - u) = 1 - u := by
      apply min_eq_right
      linarith
    have harg_nonneg : 0 ≤ Real.pi * (1 - u) := mul_nonneg (le_of_lt Real.pi_pos) hcomp0
    have harg_le : Real.pi * (1 - u) ≤ Real.pi / 2 := by
      have hprod : 0 ≤ Real.pi * ((1 / 2 : ℝ) - (1 - u)) :=
        mul_nonneg (le_of_lt Real.pi_pos) (by linarith)
      nlinarith
    have hJordan :=
      Real.mul_abs_le_abs_sin (x := Real.pi * (1 - u))
        (by
          rw [abs_of_nonneg harg_nonneg]
          exact harg_le)
    rw [abs_of_nonneg harg_nonneg] at hJordan
    have hsin : Real.sin (Real.pi * (1 - u)) = Real.sin (Real.pi * u) := by
      calc
        Real.sin (Real.pi * (1 - u)) = Real.sin (Real.pi - Real.pi * u) := by
            congr 1
            ring
        _ = Real.sin (Real.pi * u) := Real.sin_pi_sub _
    calc
      2 * min u (1 - u) = 2 * (1 - u) := by rw [hmin]
      _ = (2 / Real.pi) * (Real.pi * (1 - u)) := by field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (Real.pi * (1 - u))| := hJordan
      _ = |Real.sin (Real.pi * u)| := by rw [hsin]

/--
Chord length lower bound: `4 * min |x| |1 - |x|| ≤ ‖exp (2 π i x) - 1‖`.

The chord equals `2 * |sin (π x)|`, so this is the previous lemma restated on
the circle.
-/
private lemma qpeRoot_chord_lower_bound
    (x : ℝ)
    (hxlo : -1 ≤ x)
    (hxhi : x ≤ 1) :
    4 * min |x| |(1 - |x|)| ≤ ‖Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖ := by
  let u : ℝ := |x|
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact abs_nonneg _
  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact (abs_le).2 ⟨by linarith, hxhi⟩
  have hone : 0 ≤ 1 - |x| := by simpa [u] using sub_nonneg.mpr hu1
  have hdist : min |x| |(1 - |x|)| = min u (1 - u) := by
    dsimp [u]
    rw [abs_of_nonneg hone]
  have hsin_abs : |Real.sin (Real.pi * u)| = |Real.sin (Real.pi * x)| := by
    dsimp [u]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    ·
      have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      rw [abs_of_nonpos hx']
      rw [show Real.pi * (-x) = -(Real.pi * x) by ring, Real.sin_neg, abs_neg]
  have hsin_lower : 2 * min u (1 - u) ≤ |Real.sin (Real.pi * x)| := by
    calc
      2 * min u (1 - u) ≤ |Real.sin (Real.pi * u)| := qpe_two_mul_min_le_abs_sin u hu0 hu1
      _ = |Real.sin (Real.pi * x)| := hsin_abs
  have hchord :
      ‖Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [Real.norm_eq_abs]
    have hangle : (2 * Real.pi * x) / 2 = Real.pi * x := by ring
    rw [hangle, abs_mul]
    norm_num
  calc
    4 * min |x| |(1 - |x|)| = 2 * (2 * min u (1 - u)) := by
        rw [hdist]
        ring
    _ ≤ 2 * |Real.sin (Real.pi * x)| := mul_le_mul_of_nonneg_left hsin_lower (by norm_num)
    _ = ‖Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖ := hchord.symm

/-- The complex norm of a natural number cast. -/
private lemma norm_natCast_complex
    (M : ℕ) :
    ‖(M : ℂ)‖ = (M : ℝ) := by
  simp

/--
Pointwise majorant for the kernel mass: away from the phase, the amplitude
decays like the reciprocal of the circular distance.

Divide the chord identity `M * kernel * (root - 1) = root ^ M - 1` by the chord.
The numerator is bounded by `2` and the chord below by `4 * dist`, giving
`‖kernel‖ ≤ 1 / (2 * M * dist)`, whose square is the stated bound. This is the
estimate that is summed over the tail in the sections below.
-/
lemma qpeKernel_norm_sq_le_circular_majorant
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hpos : 0 < qpeCircularDistance M θ t) :
    ‖qpeKernel M θ t‖ ^ 2 ≤ 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) := by
  classical
  let x : ℝ := qpeOffset M θ t
  let ζ : ℂ := qpeRoot M θ t
  let d : ℝ := qpeCircularDistance M θ t
  let A : ℝ := (M : ℝ) * d
  have hMnat : 0 < M := by exact_mod_cast hM
  have hM0 : 0 ≤ (M : ℝ) := le_of_lt hM
  have hy0 : 0 ≤ (t.1 : ℝ) / (M : ℝ) := by positivity
  have hty : (t.1 : ℝ) < (M : ℝ) := by exact_mod_cast t.isLt
  have hy1 : (t.1 : ℝ) / (M : ℝ) < 1 := (div_lt_one hM).2 hty
  have hxlo : -1 ≤ x := by
    dsimp [x, qpeOffset]
    linarith
  have hxhi : x ≤ 1 := by
    dsimp [x, qpeOffset]
    linarith
  have hd : 0 < d := by simpa [d] using hpos
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos hM hd
  have hroot_norm : ‖ζ‖ = 1 := by
    dsimp [ζ, qpeRoot]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Complex.norm_exp_I_mul_ofReal (2 * Real.pi * qpeOffset M θ t)
  have hgeom : qpeKernel M θ t * ((M : ℂ) * (ζ - 1)) = ζ ^ M - 1 := by
    simpa [ζ] using qpeKernel_mul_root_chord M θ t hM
  have hnumerator : ‖ζ ^ M - 1‖ ≤ 2 := by
    calc
      ‖ζ ^ M - 1‖ ≤ ‖ζ ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [norm_pow, hroot_norm]
        norm_num
  have hchord : 4 * d ≤ ‖ζ - 1‖ := by
    simpa [ζ, d, x, qpeRoot, qpeCircularDistance, qpeOffset] using
      qpeRoot_chord_lower_bound x hxlo hxhi
  have hscaled_chord : 4 * A ≤ ‖(M : ℂ)‖ * ‖ζ - 1‖ := by
    rw [norm_natCast_complex]
    calc
      4 * A = (M : ℝ) * (4 * d) := by
          dsimp [A]
          ring
      _ ≤ (M : ℝ) * ‖ζ - 1‖ := mul_le_mul_of_nonneg_left hchord hM0
  have hproduct : ‖qpeKernel M θ t‖ * (‖(M : ℂ)‖ * ‖ζ - 1‖) = ‖ζ ^ M - 1‖ := by
    have := congrArg norm hgeom
    simpa [norm_mul, mul_assoc] using this
  have hmain : ‖qpeKernel M θ t‖ * (4 * A) ≤ 2 := by
    calc
      ‖qpeKernel M θ t‖ * (4 * A) ≤ ‖qpeKernel M θ t‖ * (‖(M : ℂ)‖ * ‖ζ - 1‖) :=
        mul_le_mul_of_nonneg_left hscaled_chord (norm_nonneg _)
      _ = ‖ζ ^ M - 1‖ := hproduct
      _ ≤ 2 := hnumerator
  have hhalf : ‖qpeKernel M θ t‖ * (2 * A) ≤ 1 := by nlinarith
  have hbound : ‖qpeKernel M θ t‖ ≤ 1 / (2 * A) := by
    exact (le_div_iff₀ (by positivity : 0 < 2 * A)).2 hhalf
  have hsquare : ‖qpeKernel M θ t‖ ^ 2 ≤ (1 / (2 * A)) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) hbound
  calc
    ‖qpeKernel M θ t‖ ^ 2 ≤ (1 / (2 * A)) ^ 2 := hsquare
    _ = 1 / (4 * A ^ 2) := by
      field_simp [ne_of_gt hA]
      ring
    _ = 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) := by simp [A, d]

end KernelChordBound

/-! =========================================================
    Reciprocal-square tail sums

Two elementary real estimates, independent of any quantum content. Summing
`1 / n ^ 2` over `Icc L M` telescopes against `1 / (n - 1) - 1 / n`, and
starting the sum at `⌊a⌋₊` for `4 ≤ a` gives the constant `128 / a` used as the
final tail bound.
========================================================= -/

section ReciprocalSquareTails

/-- Telescoping bound `∑_{n = L}^{M} 1 / n ^ 2 ≤ 1 / (L - 1)` for `2 ≤ L`. -/
private lemma reciprocal_square_Icc_le
    (L M : ℕ)
    (hL : 2 ≤ L) :
    ∑ n ∈ Finset.Icc L M, 1 / ((n : ℝ) ^ 2) ≤ 1 / (((L - 1 : ℕ) : ℝ)) := by
  classical
  by_cases hLM : L ≤ M
  ·
    let f : ℕ → ℝ := fun n => -(1 / (((n - 1 : ℕ) : ℝ)))
    have hpoint : ∀ n ∈ Finset.Icc L M, 1 / ((n : ℝ) ^ 2) ≤ f (n + 1) - f n := by
      intro n hn
      have hnL : L ≤ n := (Finset.mem_Icc.mp hn).1
      have hn2 : 2 ≤ n := le_trans hL hnL
      have hn1 : 1 ≤ n := by omega
      have hnSubPosNat : 0 < n - 1 := by omega
      have hnPos : 0 < (n : ℝ) := by
        norm_num
        omega
      have hnSubPos : 0 < (((n - 1 : ℕ) : ℝ)) := by exact_mod_cast hnSubPosNat
      dsimp [f]
      simp
      rw [Nat.cast_sub hn1]
      field_simp [ne_of_gt hnPos, ne_of_gt hnSubPos]
      have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      have hden : 0 < (n : ℝ) - ((1 : ℕ) : ℝ) := by
        norm_num
        omega
      exact (le_div_iff₀ (a := (n : ℝ) + 1) (b := (n : ℝ) ^ 2) (c := (n : ℝ) - ((1 : ℕ) : ℝ))
        hden).2 (by
        ring_nf
        linarith)
    have hsum : ∑ n ∈ Finset.Icc L M, 1 / ((n : ℝ) ^ 2) ≤ ∑ n ∈ Finset.Icc L M, (f (n + 1) - f n) :=
      Finset.sum_le_sum hpoint
    have htel : ∑ n ∈ Finset.Icc L M, (f (n + 1) - f n) = f (M + 1) - f L := by
      rw [← Finset.Ico_add_one_right_eq_Icc L M]
      exact Finset.sum_Ico_sub f (Nat.le_succ_of_le hLM)
    have htail : f (M + 1) - f L ≤ 1 / (((L - 1 : ℕ) : ℝ)) := by
      have hnonneg : 0 ≤ 1 / (M : ℝ) := by positivity
      simp only [f, Nat.succ_sub_one]
      linarith
    calc
      ∑ n ∈ Finset.Icc L M, 1 / ((n : ℝ) ^ 2) ≤ ∑ n ∈ Finset.Icc L M, (f (n + 1) - f n) := hsum
      _ = f (M + 1) - f L := htel
      _ ≤ 1 / (((L - 1 : ℕ) : ℝ)) := htail
  ·
    have hML : M < L := Nat.lt_of_not_ge hLM
    have hempty : Finset.Icc L M = ∅ := by exact Finset.Icc_eq_empty_of_lt hML
    have hsubPosNat : 0 < L - 1 := by omega
    have hsubPos : 0 < (((L - 1 : ℕ) : ℝ)) := by exact_mod_cast hsubPosNat
    rw [hempty]
    positivity

/--
The reciprocal-square tail starting at `⌊a⌋₊` is at most `128 / a` for `4 ≤ a`.

The crude constant absorbs both the factor `2` in front and the loss from
replacing `⌊a⌋₊ - 1` by `a`.
-/
private lemma reciprocal_square_floor_tail_le
    (a : ℝ)
    (M : ℕ)
    (ha : 4 ≤ a) :
    2 * ∑ n ∈ Finset.Icc ⌊a⌋₊ M, 1 / ((n : ℝ) ^ 2) ≤ 128 / a := by
  let L : ℕ := ⌊a⌋₊
  have haPos : 0 < a := by linarith
  have hL4 : 4 ≤ L := by
    apply (Nat.le_floor_iff' (by norm_num : (4 : ℕ) ≠ 0)).2
    simpa [L] using ha
  have hL2 : 2 ≤ L := by omega
  have hLsubPosNat : 0 < L - 1 := by omega
  have hLsubPos : 0 < (((L - 1 : ℕ) : ℝ)) := by exact_mod_cast hLsubPosNat
  have hsum : ∑ n ∈ Finset.Icc L M, 1 / ((n : ℝ) ^ 2) ≤ 1 / (((L - 1 : ℕ) : ℝ)) :=
    reciprocal_square_Icc_le L M hL2
  have hfloorLt : a < (L : ℝ) + 1 := by simpa [L] using (Nat.lt_floor_add_one a)
  have hL4Real : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
  have hscale : a ≤ 64 * (((L - 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ L)]
    have hsmall : (L : ℝ) + 1 ≤ 64 * ((L : ℝ) - 1) := by nlinarith
    norm_num at hsmall ⊢
    linarith
  have hfrac : 2 / (((L - 1 : ℕ) : ℝ)) ≤ 128 / a := by
    apply (div_le_div_iff₀ hLsubPos haPos).2
    nlinarith [hscale]
  calc
    2 * ∑ n ∈ Finset.Icc ⌊a⌋₊ M, 1 / ((n : ℝ) ^ 2) = 2 * ∑ n ∈ Finset.Icc L M, 1 / ((n : ℝ) ^ 2) := by
        simp [L]
    _ ≤ 2 * (1 / (((L - 1 : ℕ) : ℝ))) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 2 / (((L - 1 : ℕ) : ℝ)) := by ring
    _ ≤ 128 / a := hfrac

end ReciprocalSquareTails

/-! =========================================================
    Floor-shell geometry of the tail

Summing the pointwise majorant over the tail requires knowing how many labels
can share a given value of `⌊M * dist⌋₊`. This section answers that. The
circular distance is resolved into four explicit cases according to whether the
minimum is attained directly or after wrapping, and whether the grid point lies
left or right of `θ`; the pair of these choices is recorded as a `qpeShellTag`.
Labels in a common shell have distances within `1 / M` of each other, and grid
points that close together must coincide, so shell index together with tag
determines the label uniquely — which caps each shell at four tags times two
sides.
========================================================= -/

section FloorShellGeometry

/-- The tail labels whose scaled circular distance has integer part `n`. -/
private noncomputable def qpeCircularFloorShell
    (M : ℕ)
    (θ δ : ℝ)
    (n : ℕ) : Finset (Fin M) :=
  (qpeCircularTail M θ δ).filter (fun t => ⌊(M : ℝ) * qpeCircularDistance M θ t⌋₊ = n)

/-- The circular distance is nonnegative. -/
private lemma qpeCircularDistance_nonneg
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M) :
    0 ≤ qpeCircularDistance M θ t := by
  unfold qpeCircularDistance
  simp_all only [le_inf_iff, abs_nonneg, and_self]

/-- The grid point `t / M` represented by the label `t`. -/
private noncomputable def qpeGridPoint
    (M : ℕ)
    (t : Fin M) : ℝ :=
  (t.1 : ℝ) / (M : ℝ)

/-- The distance from `θ` to the grid point measured on the line, before wrapping. -/
private noncomputable def qpeRawDistance
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M) : ℝ :=
  |θ - qpeGridPoint M t|

/--
Which of the four cases of `qpeCircularDistance` a label falls into: whether the
minimum is attained without wrapping, and whether the grid point is left of `θ`.
-/
private noncomputable def qpeShellTag
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M) : Bool × Bool :=
  (decide (qpeRawDistance M θ t ≤ (1 / 2 : ℝ)), decide (qpeGridPoint M t ≤ θ))

/-- Grid points lie in `[0, 1)`. -/
private lemma qpeGridPoint_bounds
    (M : ℕ)
    (t : Fin M)
    (hM : 0 < (M : ℝ)) :
    0 ≤ qpeGridPoint M t ∧ qpeGridPoint M t < 1 := by
  constructor
  ·
    unfold qpeGridPoint
    positivity
  ·
    unfold qpeGridPoint
    apply (div_lt_one hM).2
    exact_mod_cast t.isLt

/-- Unwrapped case, grid point left of `θ`: the circular distance is `θ - t / M`. -/
private lemma qpeCircularDistance_direct_left
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (hθ1 : θ < 1)
    (hdirect : qpeRawDistance M θ t ≤ (1 / 2 : ℝ))
    (hleft : qpeGridPoint M t ≤ θ) :
    qpeCircularDistance M θ t = θ - qpeGridPoint M t := by
  rcases qpeGridPoint_bounds M t hM with ⟨hy0, _hy1⟩
  have habs : |θ - qpeGridPoint M t| = θ - qpeGridPoint M t := abs_of_nonneg (sub_nonneg.mpr hleft)
  have hle_one : θ - qpeGridPoint M t ≤ 1 := by linarith
  have houter : |1 - (θ - qpeGridPoint M t)| = 1 - (θ - qpeGridPoint M t) :=
    abs_of_nonneg (sub_nonneg.mpr hle_one)
  have hdirect' : θ - qpeGridPoint M t ≤ (1 / 2 : ℝ) := by simpa [qpeRawDistance, habs] using hdirect
  unfold qpeCircularDistance
  unfold qpeGridPoint at *
  rw [habs, houter]
  exact min_eq_left (by linarith)

/-- Unwrapped case, grid point right of `θ`: the circular distance is `t / M - θ`. -/
private lemma qpeCircularDistance_direct_right
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hdirect : qpeRawDistance M θ t ≤ (1 / 2 : ℝ))
    (hright : θ ≤ qpeGridPoint M t) :
    qpeCircularDistance M θ t = qpeGridPoint M t - θ := by
  rcases qpeGridPoint_bounds M t hM with ⟨_hy0, hy1⟩
  have habs : |θ - qpeGridPoint M t| = qpeGridPoint M t - θ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hright)]
    ring
  have hle_one : qpeGridPoint M t - θ ≤ 1 := by linarith
  have houter : |1 - (qpeGridPoint M t - θ)| = 1 - (qpeGridPoint M t - θ) :=
    abs_of_nonneg (sub_nonneg.mpr hle_one)
  have hdirect' : qpeGridPoint M t - θ ≤ (1 / 2 : ℝ) := by simpa [qpeRawDistance, habs] using hdirect
  unfold qpeCircularDistance qpeGridPoint at *
  rw [habs, houter]
  exact min_eq_left (by linarith)

/-- Wrapped case, grid point left of `θ`: the distance goes the other way round. -/
private lemma qpeCircularDistance_wrap_left
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (hθ1 : θ < 1)
    (hwrap : ¬ qpeRawDistance M θ t ≤ (1 / 2 : ℝ))
    (hleft : qpeGridPoint M t ≤ θ) :
    qpeCircularDistance M θ t = 1 - (θ - qpeGridPoint M t) := by
  rcases qpeGridPoint_bounds M t hM with ⟨hy0, _hy1⟩
  have habs : |θ - qpeGridPoint M t| = θ - qpeGridPoint M t := abs_of_nonneg (sub_nonneg.mpr hleft)
  have hle_one : θ - qpeGridPoint M t ≤ 1 := by linarith
  have houter : |1 - (θ - qpeGridPoint M t)| = 1 - (θ - qpeGridPoint M t) :=
    abs_of_nonneg (sub_nonneg.mpr hle_one)
  have hwrap' : ¬ θ - qpeGridPoint M t ≤ (1 / 2 : ℝ) := by simpa [qpeRawDistance, habs] using hwrap
  unfold qpeCircularDistance qpeGridPoint at *
  rw [habs, houter]
  exact min_eq_right (by linarith)

/-- Wrapped case, grid point right of `θ`: the distance goes the other way round. -/
private lemma qpeCircularDistance_wrap_right
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hwrap : ¬ qpeRawDistance M θ t ≤ (1 / 2 : ℝ))
    (hright : θ ≤ qpeGridPoint M t) :
    qpeCircularDistance M θ t = 1 - (qpeGridPoint M t - θ) := by
  rcases qpeGridPoint_bounds M t hM with ⟨_hy0, hy1⟩
  have habs : |θ - qpeGridPoint M t| = qpeGridPoint M t - θ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hright)]
    ring
  have hle_one : qpeGridPoint M t - θ ≤ 1 := by linarith
  have houter : |1 - (qpeGridPoint M t - θ)| = 1 - (qpeGridPoint M t - θ) :=
    abs_of_nonneg (sub_nonneg.mpr hle_one)
  have hwrap' : ¬ qpeGridPoint M t - θ ≤ (1 / 2 : ℝ) := by simpa [qpeRawDistance, habs] using hwrap
  unfold qpeCircularDistance qpeGridPoint at *
  rw [habs, houter]
  exact min_eq_right (by linarith)

/--
Two labels in the same floor shell have circular distances within `1 / M`.

Both scaled distances have the same integer part `n`, so they lie in a common
half-open interval of length one.
-/
private lemma qpe_same_floor_shell_distance_close
    (M : ℕ)
    (θ : ℝ)
    (a b : Fin M)
    (n : ℕ)
    (hM : 0 < (M : ℝ))
    (ha : ⌊(M : ℝ) * qpeCircularDistance M θ a⌋₊ = n)
    (hb : ⌊(M : ℝ) * qpeCircularDistance M θ b⌋₊ = n) :
    |qpeCircularDistance M θ a - qpeCircularDistance M θ b| < 1 / (M : ℝ) := by
  have ha_nonneg : 0 ≤ (M : ℝ) * qpeCircularDistance M θ a :=
    mul_nonneg (le_of_lt hM) (qpeCircularDistance_nonneg M θ a)
  have hb_nonneg : 0 ≤ (M : ℝ) * qpeCircularDistance M θ b :=
    mul_nonneg (le_of_lt hM) (qpeCircularDistance_nonneg M θ b)
  have ha_bounds : (n : ℝ) ≤ (M : ℝ) * qpeCircularDistance M θ a ∧
      (M : ℝ) * qpeCircularDistance M θ a < (n : ℝ) + 1 := by
    simpa [ha] using (Nat.floor_eq_iff ha_nonneg).mp ha
  have hb_bounds : (n : ℝ) ≤ (M : ℝ) * qpeCircularDistance M θ b ∧
      (M : ℝ) * qpeCircularDistance M θ b < (n : ℝ) + 1 := by
    simpa [hb] using (Nat.floor_eq_iff hb_nonneg).mp hb
  have ha_upper : qpeCircularDistance M θ a < ((n : ℝ) + 1) / (M : ℝ) :=
    (lt_div_iff₀ hM).2 (by simpa [mul_comm] using ha_bounds.2)
  have hb_upper : qpeCircularDistance M θ b < ((n : ℝ) + 1) / (M : ℝ) :=
    (lt_div_iff₀ hM).2 (by simpa [mul_comm] using hb_bounds.2)
  have ha_lower : (n : ℝ) / (M : ℝ) ≤ qpeCircularDistance M θ a :=
    (div_le_iff₀ hM).2 (by simpa [mul_comm] using ha_bounds.1)
  have hb_lower : (n : ℝ) / (M : ℝ) ≤ qpeCircularDistance M θ b :=
    (div_le_iff₀ hM).2 (by simpa [mul_comm] using hb_bounds.1)
  have hwidth : ((n : ℝ) + 1) / (M : ℝ) - (n : ℝ) / (M : ℝ) = 1 / (M : ℝ) := by
    field_simp [ne_of_gt hM]
    ring
  apply (abs_lt).2
  constructor
  · nlinarith [ha_upper, hb_lower, hwidth]
  · nlinarith [hb_upper, ha_lower, hwidth]

/-- Distinct labels have grid points at least `1 / M` apart, hence are equal if closer. -/
private lemma qpe_grid_labels_eq_of_fraction_close
    (M : ℕ)
    (a b : Fin M)
    (hM : 0 < (M : ℝ))
    (hclose : |qpeGridPoint M a - qpeGridPoint M b| < 1 / (M : ℝ)) :
    a = b := by
  have hfrac : |(a.1 : ℝ) - (b.1 : ℝ)| / (M : ℝ) < 1 / (M : ℝ) := by
    calc
      |(a.1 : ℝ) - (b.1 : ℝ)| / (M : ℝ) = |qpeGridPoint M a - qpeGridPoint M b| := by
          symm
          unfold qpeGridPoint
          calc
            |(a.1 : ℝ) / (M : ℝ) - (b.1 : ℝ) / (M : ℝ)|
                = |((a.1 : ℝ) - (b.1 : ℝ)) / (M : ℝ)| := by
                congr 1
                ring
            _ = |(a.1 : ℝ) - (b.1 : ℝ)| / (M : ℝ) := by rw [abs_div, abs_of_pos hM]
      _ < 1 / (M : ℝ) := hclose
  have hval : |(a.1 : ℝ) - (b.1 : ℝ)| < 1 := (div_lt_div_iff_of_pos_right hM).mp hfrac
  have hab : a.1 = b.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hba
    ·
      have hcast : (a.1 : ℝ) + 1 ≤ (b.1 : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hab)
      have hlarge : 1 ≤ |(a.1 : ℝ) - (b.1 : ℝ)| := by
        rw [abs_of_nonpos]
        · linarith
        · linarith
      linarith
    ·
      have hcast : (b.1 : ℝ) + 1 ≤ (a.1 : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hba)
      have hlarge : 1 ≤ |(a.1 : ℝ) - (b.1 : ℝ)| := by
        rw [abs_of_nonneg]
        · linarith
        · linarith
      linarith
  exact Fin.ext hab

/--
Shell index plus case tag determines the label.

Within one shell and one case, the circular distance is an affine function of
the grid point with slope `±1`, so distances within `1 / M` force grid points
within `1 / M`, and the previous lemma collapses the two labels. This is the
combinatorial content behind the shell cardinality bound.
-/
private lemma qpe_same_floor_shell_same_tag
    (M : ℕ)
    (θ : ℝ)
    (a b : Fin M)
    (n : ℕ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (ha : ⌊(M : ℝ) * qpeCircularDistance M θ a⌋₊ = n)
    (hb : ⌊(M : ℝ) * qpeCircularDistance M θ b⌋₊ = n)
    (htag : qpeShellTag M θ a = qpeShellTag M θ b) :
    a = b := by
  have hclose : |qpeCircularDistance M θ a - qpeCircularDistance M θ b| < 1 / (M : ℝ) :=
    qpe_same_floor_shell_distance_close M θ a b n hM ha hb
  have hdirect_tag : decide (qpeRawDistance M θ a ≤ (1 / 2 : ℝ)) =
      decide (qpeRawDistance M θ b ≤ (1 / 2 : ℝ)) := by
    simpa [qpeShellTag] using congrArg Prod.fst htag
  have hside_tag : decide (qpeGridPoint M a ≤ θ) = decide (qpeGridPoint M b ≤ θ) := by
    simpa [qpeShellTag] using congrArg Prod.snd htag
  by_cases ha_direct : qpeRawDistance M θ a ≤ (1 / 2 : ℝ)
  ·
    have hb_direct : qpeRawDistance M θ b ≤ (1 / 2 : ℝ) := by
      have hbool : decide (qpeRawDistance M θ b ≤ (1 / 2 : ℝ)) = true := by
        calc
          decide (qpeRawDistance M θ b ≤ (1 / 2 : ℝ))
              = decide (qpeRawDistance M θ a ≤ (1 / 2 : ℝ)) := hdirect_tag.symm
          _ = true := by exact decide_eq_true ha_direct
      simpa using hbool
    by_cases ha_left : qpeGridPoint M a ≤ θ
    ·
      have hb_left : qpeGridPoint M b ≤ θ := by
        have hbool : decide (qpeGridPoint M b ≤ θ) = true := by
          calc
            decide (qpeGridPoint M b ≤ θ) = decide (qpeGridPoint M a ≤ θ) := hside_tag.symm
            _ = true := by simp [ha_left]
        simpa using hbool
      have hda := qpeCircularDistance_direct_left M θ a hM hθ1 ha_direct ha_left
      have hdb := qpeCircularDistance_direct_left M θ b hM hθ1 hb_direct hb_left
      apply qpe_grid_labels_eq_of_fraction_close M a b hM
      calc
        |qpeGridPoint M a - qpeGridPoint M b|
            = |qpeCircularDistance M θ a - qpeCircularDistance M θ b| := by
              rw [hda, hdb]
              rw [show (θ - qpeGridPoint M a) - (θ - qpeGridPoint M b)
                = -(qpeGridPoint M a - qpeGridPoint M b) by ring]
              rw [abs_neg]
        _ < 1 / (M : ℝ) := hclose
    ·
      have ha_right : θ ≤ qpeGridPoint M a := le_of_lt (lt_of_not_ge ha_left)
      have hb_right : θ ≤ qpeGridPoint M b := by
        have hb_not_left : ¬ qpeGridPoint M b ≤ θ := by
          have hbool : decide (qpeGridPoint M b ≤ θ) = false := by
            calc
              decide (qpeGridPoint M b ≤ θ) = decide (qpeGridPoint M a ≤ θ) := hside_tag.symm
              _ = false := by simp [ha_left]
          simpa using hbool
        exact le_of_lt (lt_of_not_ge hb_not_left)
      have hda := qpeCircularDistance_direct_right M θ a hM hθ0 ha_direct ha_right
      have hdb := qpeCircularDistance_direct_right M θ b hM hθ0 hb_direct hb_right
      apply qpe_grid_labels_eq_of_fraction_close M a b hM
      calc
        |qpeGridPoint M a - qpeGridPoint M b|
            = |qpeCircularDistance M θ a - qpeCircularDistance M θ b| := by
              rw [hda, hdb]
              congr 1
              ring
        _ < 1 / (M : ℝ) := hclose
  ·
    have hb_wrap : ¬ qpeRawDistance M θ b ≤ (1 / 2 : ℝ) := by
      intro hb_direct
      have hbool : decide (qpeRawDistance M θ a ≤ (1 / 2 : ℝ)) = true := by
        calc
          decide (qpeRawDistance M θ a ≤ (1 / 2 : ℝ))
              = decide (qpeRawDistance M θ b ≤ (1 / 2 : ℝ)) := hdirect_tag
          _ = true := by exact decide_eq_true hb_direct
      exact ha_direct (by simpa using hbool)
    by_cases ha_left : qpeGridPoint M a ≤ θ
    ·
      have hb_left : qpeGridPoint M b ≤ θ := by
        have hbool : decide (qpeGridPoint M b ≤ θ) = true := by
          calc
            decide (qpeGridPoint M b ≤ θ) = decide (qpeGridPoint M a ≤ θ) := hside_tag.symm
            _ = true := by simp [ha_left]
        simpa using hbool
      have hda := qpeCircularDistance_wrap_left M θ a hM hθ1 ha_direct ha_left
      have hdb := qpeCircularDistance_wrap_left M θ b hM hθ1 hb_wrap hb_left
      apply qpe_grid_labels_eq_of_fraction_close M a b hM
      calc
        |qpeGridPoint M a - qpeGridPoint M b|
            = |qpeCircularDistance M θ a - qpeCircularDistance M θ b| := by
              rw [hda, hdb]
              congr 1
              ring
        _ < 1 / (M : ℝ) := hclose
    ·
      have ha_right : θ ≤ qpeGridPoint M a := le_of_lt (lt_of_not_ge ha_left)
      have hb_right : θ ≤ qpeGridPoint M b := by
        have hb_not_left : ¬ qpeGridPoint M b ≤ θ := by
          intro hb_left
          have hbool : decide (qpeGridPoint M a ≤ θ) = true := by
            calc
              decide (qpeGridPoint M a ≤ θ) = decide (qpeGridPoint M b ≤ θ) := hside_tag
              _ = true := by simp [hb_left]
          exact ha_left (by simpa using hbool)
        exact le_of_lt (lt_of_not_ge hb_not_left)
      have hda := qpeCircularDistance_wrap_right M θ a hM hθ0 ha_direct ha_right
      have hdb := qpeCircularDistance_wrap_right M θ b hM hθ0 hb_wrap hb_right
      apply qpe_grid_labels_eq_of_fraction_close M a b hM
      calc
        |qpeGridPoint M a - qpeGridPoint M b|
            = |qpeCircularDistance M θ a - qpeCircularDistance M θ b| := by
              rw [hda, hdb]
              rw [show (1 - (qpeGridPoint M a - θ)) - (1 - (qpeGridPoint M b - θ))
                = -(qpeGridPoint M a - qpeGridPoint M b) by ring]
              rw [abs_neg]
        _ < 1 / (M : ℝ) := hclose
end FloorShellGeometry

/-! =========================================================
    Summing the majorant over the tail

With the geometry settled the estimate assembles. The tail is reindexed by
floor shells, each shell holds at most eight labels and contributes at most
`2 / n ^ 2`, and the reciprocal-square tail sum turns the total into
`128 / (M * δ)`. Feeding the pointwise chord bound through this chain gives
`qpeKernel_circular_tail_le`, the analytic heart of the file.
========================================================= -/

section TailMajorantSummation

/--
Reindex the tail by the natural floor shell of `M * circularDistance`.

Every tail label lies in one such shell, and its shell index lies between
`⌊M * δ⌋₊` and `M`.
-/
private lemma qpeCircular_tail_floor_shell_partition
    (M : ℕ)
    (θ δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (f : Fin M → ℝ) :
    ∑ t ∈ qpeCircularTail M θ δ, f t
      = ∑ n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M, ∑ t ∈ qpeCircularFloorShell M θ δ n, f t := by
  classical
  let s : Finset (Fin M) := qpeCircularTail M θ δ
  let I : Finset ℕ := Finset.Icc ⌊(M : ℝ) * δ⌋₊ M
  let shell : Fin M → ℕ := fun t => ⌊(M : ℝ) * qpeCircularDistance M θ t⌋₊
  have hshell_mem : ∀ t ∈ s, shell t ∈ I := by
    intro t ht
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · have ht' : t ∈ qpeCircularTail M θ δ := by simpa [s] using ht
      have htail : δ ≤ qpeCircularDistance M θ t := by
        simpa [qpeCircularTail] using (Finset.mem_filter.mp ht').2
      have hmul : (M : ℝ) * δ ≤ (M : ℝ) * qpeCircularDistance M θ t :=
        mul_le_mul_of_nonneg_left htail (le_of_lt hM)
      simpa [shell, I] using Nat.floor_le_floor hmul
    ·
      let y : ℝ := (t.1 : ℝ) / (M : ℝ)
      have hy0 : 0 ≤ y := by
        dsimp [y]
        positivity
      have htM : (t.1 : ℝ) < (M : ℝ) := by exact_mod_cast t.isLt
      have hy1 : y < 1 := by
        dsimp [y]
        exact (div_lt_one hM).2 htM
      have hdiff : |θ - y| ≤ 1 := by
        apply (abs_le).2
        constructor <;> linarith
      have hdist_le_one : qpeCircularDistance M θ t ≤ 1 := by
        unfold qpeCircularDistance
        exact le_trans (min_le_left _ _) hdiff
      have hscaled : (M : ℝ) * qpeCircularDistance M θ t ≤ (M : ℝ) := by
        calc
          (M : ℝ) * qpeCircularDistance M θ t ≤ (M : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hdist_le_one (le_of_lt hM)
          _ = (M : ℝ) := by ring
      simpa [shell, I] using Nat.floor_le_of_le hscaled
  have hpartition :
      ∑ t ∈ s, f t = ∑ n ∈ I, ∑ t ∈ s.filter (fun t => shell t = n), f t := by
    calc
      ∑ t ∈ s, f t = ∑ t ∈ s, ∑ n ∈ I, if shell t = n then f t else 0 := by
          apply Finset.sum_congr rfl
          intro t ht
          symm
          simp
          simp [hshell_mem t ht]
      _ = ∑ n ∈ I, ∑ t ∈ s, if shell t = n then f t else 0 := by rw [Finset.sum_comm]
      _ = ∑ n ∈ I, ∑ t ∈ s.filter (fun t => shell t = n), f t := by
          apply Finset.sum_congr rfl
          intro n hn
          change (∑ t ∈ s, if shell t = n then f t else 0)
            = ∑ t ∈ s.filter (fun t => shell t = n), f t
          exact (Finset.sum_filter (s := s) (fun t => shell t = n) f).symm
  simpa [s, I, shell, qpeCircularFloorShell] using hpartition

/--
Each floor shell contains at most eight labels.

By `qpe_same_floor_shell_same_tag` a shell has at most one label per case tag,
and the tag ranges over a pair of booleans; the bound `8` leaves slack rather
than tracking the exact count.
-/
private lemma qpeCircular_floor_shell_card_le_eight
    (M : ℕ)
    (θ δ : ℝ)
    (n : ℕ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) :
    (qpeCircularFloorShell M θ δ n).card ≤ 8 := by
  classical
  let S : Finset (Fin M) := qpeCircularFloorShell M θ δ n
  let tag : Fin M → Bool × Bool := qpeShellTag M θ
  have hinj : Set.InjOn tag (↑S : Set (Fin M)) := by
    intro a ha b hb hab
    have ha_floor : ⌊(M : ℝ) * qpeCircularDistance M θ a⌋₊ = n := by
      have ha' : a ∈ qpeCircularTail M θ δ ∧
          ⌊(M : ℝ) * qpeCircularDistance M θ a⌋₊ = n := by
        simpa [S, qpeCircularFloorShell] using ha
      exact ha'.2
    have hb_floor : ⌊(M : ℝ) * qpeCircularDistance M θ b⌋₊ = n := by
      have hb' : b ∈ qpeCircularTail M θ δ ∧
          ⌊(M : ℝ) * qpeCircularDistance M θ b⌋₊ = n := by
        simpa [S, qpeCircularFloorShell] using hb
      exact hb'.2
    exact qpe_same_floor_shell_same_tag M θ a b n hM hθ0 hθ1 ha_floor hb_floor
      (by simpa [tag] using hab)
  have hmaps : Set.MapsTo tag (↑S : Set (Fin M))
      (↑(Finset.univ : Finset (Bool × Bool)) : Set (Bool × Bool)) := by
    intro x hx
    simp
  have hcard : S.card ≤ (Finset.univ : Finset (Bool × Bool)).card :=
    Finset.card_le_card_of_injOn tag hmaps hinj
  have htag_card : (Finset.univ : Finset (Bool × Bool)).card = 4 := by decide
  have hfour : S.card ≤ 4 := by simpa [htag_card] using hcard
  have height : S.card ≤ 8 := by omega
  simpa [S] using height

/--
The majorant summed over one shell is at most `2 / n ^ 2`.

Every label in shell `n` has `n ≤ M * dist`, so each of the at most eight terms
is at most `1 / (4 * n ^ 2)`.
-/
private lemma qpeCircular_floor_shell_majorant_le
    (M : ℕ)
    (θ δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcutoff : 4 ≤ (M : ℝ) * δ)
    (n : ℕ)
    (hn : n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M) :
    ∑ t ∈ qpeCircularFloorShell M θ δ n, 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
      ≤ 2 / ((n : ℝ) ^ 2) := by
  classical
  let S : Finset (Fin M) := qpeCircularFloorShell M θ δ n
  let c : ℝ := 1 / (4 * ((n : ℝ) ^ 2))
  have hfloor_four : 4 ≤ ⌊(M : ℝ) * δ⌋₊ := by
    apply (Nat.le_floor_iff' (by norm_num : (4 : ℕ) ≠ 0)).2
    simpa using hcutoff
  have hn_four : 4 ≤ n := le_trans hfloor_four (Finset.mem_Icc.mp hn).1
  have hn_pos : 0 < n := by omega
  have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have hpoint : ∀ t ∈ S, 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) ≤ c := by
    intro t ht
    have ht' : t ∈ qpeCircularFloorShell M θ δ n := by simpa [S] using ht
    have hfilter : t ∈ (qpeCircularTail M θ δ).filter
        (fun t => ⌊(M : ℝ) * qpeCircularDistance M θ t⌋₊ = n) := by
      simpa [qpeCircularFloorShell] using ht'
    have hfloor : ⌊(M : ℝ) * qpeCircularDistance M θ t⌋₊ = n := (Finset.mem_filter.mp hfilter).2
    have hscaled_nonneg : 0 ≤ (M : ℝ) * qpeCircularDistance M θ t :=
      mul_nonneg (le_of_lt hM) (qpeCircularDistance_nonneg M θ t)
    have hfloor_le : (n : ℝ) ≤ (M : ℝ) * qpeCircularDistance M θ t := by
      have h := Nat.floor_le hscaled_nonneg
      simpa [hfloor] using h
    have hscaled_pos : 0 < (M : ℝ) * qpeCircularDistance M θ t := lt_of_lt_of_le hnR_pos hfloor_le
    have hsq : (n : ℝ) ^ 2 ≤ ((M : ℝ) * qpeCircularDistance M θ t) ^ 2 := by
      nlinarith [sq_nonneg ((M : ℝ) * qpeCircularDistance M θ t - (n : ℝ))]
    have hden : 4 * ((n : ℝ) ^ 2) ≤ 4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    have hden_pos : 0 < 4 * ((n : ℝ) ^ 2) := by positivity
    change 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) ≤ 1 / (4 * ((n : ℝ) ^ 2))
    exact one_div_le_one_div_of_le hden_pos hden
  have hsum : ∑ t ∈ S, 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) ≤ ∑ _t ∈ S, c := by
    apply Finset.sum_le_sum
    intro t ht
    exact hpoint t ht
  have hcard : S.card ≤ 8 := by
    simpa [S] using qpeCircular_floor_shell_card_le_eight M θ δ n hM hθ0 hθ1
  have hcardR : (S.card : ℝ) ≤ 8 := by exact_mod_cast hcard
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hconst : ∑ _t ∈ S, c = (S.card : ℝ) * c := by simp [nsmul_eq_mul]
  have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
  calc
    ∑ t ∈ qpeCircularFloorShell M θ δ n, 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
        = ∑ t ∈ S, 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) := by simp [S]
    _ ≤ ∑ _t ∈ S, c := hsum
    _ = (S.card : ℝ) * c := hconst
    _ ≤ 8 * c := mul_le_mul_of_nonneg_right hcardR hc_nonneg
    _ = 2 / ((n : ℝ) ^ 2) := by
      dsimp [c]
      field_simp [hnR_ne]
      ring

/-- Summing the per-shell bound over all shells above the cutoff. -/
private lemma qpeCircular_tail_majorized_by_floor_shells
    (M : ℕ)
    (θ δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcutoff : 4 ≤ (M : ℝ) * δ) :
    ∑ t ∈ qpeCircularTail M θ δ, 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
      ≤ 2 * ∑ n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M, 1 / ((n : ℝ) ^ 2) := by
  calc
    ∑ t ∈ qpeCircularTail M θ δ, 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
        = ∑ n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M,
            ∑ t ∈ qpeCircularFloorShell M θ δ n,
              1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) := by
      exact qpeCircular_tail_floor_shell_partition M θ δ hM hθ0 hθ1
        (fun t => 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)))
    _ ≤ ∑ n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M, 2 / ((n : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact qpeCircular_floor_shell_majorant_le M θ δ hM hθ0 hθ1 hcutoff n hn
    _ = 2 * ∑ n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M, 1 / ((n : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- The majorant over the whole tail is at most `128 / (M * δ)`. -/
lemma qpeCircular_majorant_tail_le
    (M : ℕ)
    (θ δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcutoff : 4 ≤ (M : ℝ) * δ) :
    ∑ t ∈ qpeCircularTail M θ δ, 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
      ≤ 128 / ((M : ℝ) * δ) := by
  let a : ℝ := (M : ℝ) * δ
  have hshell :
      ∑ t ∈ qpeCircularTail M θ δ, 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
        ≤ 2 * ∑ n ∈ Finset.Icc ⌊a⌋₊ M, 1 / ((n : ℝ) ^ 2) := by
    simpa [a] using qpeCircular_tail_majorized_by_floor_shells M θ δ hM hθ0 hθ1 hcutoff
  have hrecip : 2 * ∑ n ∈ Finset.Icc ⌊a⌋₊ M, 1 / ((n : ℝ) ^ 2) ≤ 128 / a := by
    exact reciprocal_square_floor_tail_le a M (by simpa [a] using hcutoff)
  calc
    ∑ t ∈ qpeCircularTail M θ δ, 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
        ≤ 2 * ∑ n ∈ Finset.Icc ⌊a⌋₊ M, 1 / ((n : ℝ) ^ 2) := hshell
    _ ≤ 128 / a := hrecip
    _ = 128 / ((M : ℝ) * δ) := by simp [a]

/--
Combine the pointwise sine estimate with the reciprocal-square tail sum.
-/
lemma qpeKernel_circular_tail_le
    (M : ℕ)
    (θ δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hδ : 0 < δ)
    (hcutoff : 4 ≤ (M : ℝ) * δ) :
    ∑ t ∈ qpeCircularTail M θ δ, ‖qpeKernel M θ t‖ ^ 2 ≤ 128 / ((M : ℝ) * δ) := by
  calc
    ∑ t ∈ qpeCircularTail M θ δ, ‖qpeKernel M θ t‖ ^ 2
        ≤ ∑ t ∈ qpeCircularTail M θ δ, 1 / (4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) := by
      apply Finset.sum_le_sum
      intro t ht
      have htail : δ ≤ qpeCircularDistance M θ t := by
        simpa [qpeCircularTail] using (Finset.mem_filter.mp ht).2
      have hpos : 0 < qpeCircularDistance M θ t := lt_of_lt_of_le hδ htail
      exact qpeKernel_norm_sq_le_circular_majorant M θ t hM hθ0 hθ1 hpos
    _ ≤ 128 / ((M : ℝ) * δ) := qpeCircular_majorant_tail_le M θ δ hM hθ0 hθ1 hcutoff

end TailMajorantSummation

/-! =========================================================
    The tail bound for an ordinary fraction

The bound is now specialized to the phases Algorithm 1 actually produces,
`θ = r / N` with `0 < r < N`. The window used by the algorithm is stated with
the ordinary absolute value rather than the circular distance, so the first
lemma checks that every label the algorithm discards does lie in the circular
tail. Combining this with the precision hypothesis, which supplies both
`4 ≤ M * δ` and `δ < 1 / 2`, gives the bound `128 * D / (M * η)`.
========================================================= -/

section OrdinaryFractionTailBound

/--
Every label outside the ordinary precision window lies in the circular tail.

The cutoff `η / D` is below one half, so a label that is far in the ordinary
sense cannot be close after wrapping either.
-/
private lemma qpe_ordinary_bad_mem_circularTail
    (η : ℝ)
    (N D M r : ℕ)
    (hηhalf : η < (1 / 2 : ℝ))
    (hN : 0 < (N : ℝ))
    (hD : 0 < (D : ℝ))
    (hND : N ≤ D)
    (hrpos : 0 < r)
    (hr : r < N)
    (t : Fin M)
    (ht : t ∈ Finset.univ.filter
        (fun t : Fin M => ¬ |((r : ℝ) / (N : ℝ)) - ((t.1 : ℝ) / (M : ℝ))| < η / (D : ℝ))) :
    t ∈ qpeCircularTail M ((r : ℝ) / (N : ℝ)) (η / (D : ℝ)) := by
  classical
  let θ : ℝ := (r : ℝ) / (N : ℝ)
  let y : ℝ := (t.1 : ℝ) / (M : ℝ)
  let δ : ℝ := η / (D : ℝ)
  have hNleD : (N : ℝ) ≤ (D : ℝ) := by exact_mod_cast hND
  have hηlt_one : η < 1 := by linarith
  have hηN_lt_N : η * (N : ℝ) < 1 * (N : ℝ) := mul_lt_mul_of_pos_right hηlt_one hN
  have hηN_lt_D : η * (N : ℝ) < (D : ℝ) := by
    calc
      η * (N : ℝ) < 1 * (N : ℝ) := hηN_lt_N
      _ = (N : ℝ) := by ring
      _ ≤ (D : ℝ) := hNleD
  have hδ_lt_invN : δ < 1 / (N : ℝ) := by
    dsimp [δ]
    apply (div_lt_div_iff₀ hD hN).2
    simpa using hηN_lt_D
  have hMnat : 0 < M := by
    by_contra hMnot
    have hMzero : M = 0 := Nat.eq_zero_of_not_pos hMnot
    subst M
    exact (Nat.not_lt_zero t.1) t.isLt
  have hM : 0 < (M : ℝ) := by exact_mod_cast hMnat
  have hr_real : (r : ℝ) < (N : ℝ) := by exact_mod_cast hr
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    positivity
  have hθ1 : θ < 1 := by
    dsimp [θ]
    exact (div_lt_one hN).2 hr_real
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hty : (t.1 : ℝ) < (M : ℝ) := by exact_mod_cast t.isLt
  have hy1 : y < 1 := by
    dsimp [y]
    exact (div_lt_one hM).2 hty
  have hbad : ¬ |θ - y| < δ := by simpa [θ, y, δ] using (Finset.mem_filter.mp ht).2
  have hord : δ ≤ |θ - y| := le_of_not_gt hbad
  have hwrap : δ ≤ |1 - (|θ - y|)| := by
    by_cases hyθ : y ≤ θ
    ·
      have habs : |θ - y| = θ - y := abs_of_nonneg (sub_nonneg.mpr hyθ)
      have hrsucc : (r : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hr)
      have hrle : (r : ℝ) ≤ (N : ℝ) - 1 := by linarith
      have hθle : θ ≤ 1 - 1 / (N : ℝ) := by
        dsimp [θ]
        calc
          (r : ℝ) / (N : ℝ) ≤ ((N : ℝ) - 1) / (N : ℝ) := (div_le_div_iff_of_pos_right hN).2 hrle
          _ = 1 - 1 / (N : ℝ) := by field_simp [ne_of_gt hN]
      have houter_nonneg : 0 ≤ 1 - (θ - y) := by linarith
      have hinv_le : 1 / (N : ℝ) ≤ 1 - (θ - y) := by linarith
      calc
        δ ≤ 1 / (N : ℝ) := le_of_lt hδ_lt_invN
        _ ≤ 1 - (θ - y) := hinv_le
        _ = |1 - (|θ - y|)| := by
          rw [habs]
          exact (abs_of_nonneg houter_nonneg).symm
    ·
      have hθy : θ ≤ y := le_of_lt (lt_of_not_ge hyθ)
      have habs : |θ - y| = y - θ := by
        rw [abs_of_nonpos (sub_nonpos.mpr hθy)]
        ring
      have h1le_r : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hrpos)
      have hinv_le_θ : 1 / (N : ℝ) ≤ θ := by
        dsimp [θ]
        exact (div_le_div_iff_of_pos_right hN).2 h1le_r
      have houter_nonneg : 0 ≤ 1 - (y - θ) := by linarith
      have hinv_le : 1 / (N : ℝ) ≤ 1 - (y - θ) := by linarith
      calc
        δ ≤ 1 / (N : ℝ) := le_of_lt hδ_lt_invN
        _ ≤ 1 - (y - θ) := hinv_le
        _ = |1 - (|θ - y|)| := by
          rw [habs]
          exact (abs_of_nonneg houter_nonneg).symm
  simpa [qpeCircularTail, qpeCircularDistance, θ, y, δ] using le_min hord hwrap

/-- Hence the ordinary bad mass is dominated by the circular-tail mass. -/
lemma qpe_ordinary_bad_mass_le_circular_tail
    (η : ℝ)
    (N D M r : ℕ)
    (hηhalf : η < (1 / 2 : ℝ))
    (hN : 0 < (N : ℝ))
    (hD : 0 < (D : ℝ))
    (hND : N ≤ D)
    (hrpos : 0 < r)
    (hr : r < N) :
    ∑ t ∈ Finset.univ.filter
        (fun t : Fin M => ¬ |((r : ℝ) / (N : ℝ)) - ((t.1 : ℝ) / (M : ℝ))| < η / (D : ℝ)),
      ‖qpeKernel M ((r : ℝ) / (N : ℝ)) t‖ ^ 2
      ≤ ∑ t ∈ qpeCircularTail M ((r : ℝ) / (N : ℝ)) (η / (D : ℝ)),
          ‖qpeKernel M ((r : ℝ) / (N : ℝ)) t‖ ^ 2 := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro t ht
    exact qpe_ordinary_bad_mem_circularTail η N D M r hηhalf hN hD hND hrpos hr t ht
  · intro t _htTail _htNotSmall
    exact sq_nonneg _

/--
The precision hypothesis forces the cutoff `M * (η / D)` to be at least `4`.

This is the hypothesis `qpeKernel_circular_tail_le` needs in order to start the
reciprocal-square tail at a usable index.
-/
lemma qpe_grid_cutoff_ge_four
    (η : ℝ)
    (D M : ℕ)
    (hη : 0 < η)
    (hD : 0 < (D : ℝ))
    (hgrid : (2 + 1 / (2 * η)) ^ 2 ≤ (M : ℝ) / (D : ℝ)) :
    4 ≤ (M : ℝ) * (η / (D : ℝ)) := by
  let B : ℝ := (2 + 1 / (2 * η)) ^ 2
  have hbase : 4 ≤ η * B := by
    have hden : 0 < 4 * η := by positivity
    have hsq : 0 ≤ (4 * η - 1) ^ 2 := sq_nonneg (4 * η - 1)
    have hid : η * B - 4 = (4 * η - 1) ^ 2 / (4 * η) := by
      dsimp [B]
      field_simp [ne_of_gt hη]
      ring
    have hnonneg : 0 ≤ (4 * η - 1) ^ 2 / (4 * η) := div_nonneg hsq (le_of_lt hden)
    nlinarith [hid]
  have hgrid' : B ≤ (M : ℝ) / (D : ℝ) := by simpa [B] using hgrid
  have hMD : B * (D : ℝ) ≤ (M : ℝ) := (le_div_iff₀ hD).mp hgrid'
  have hleft : 4 * (D : ℝ) ≤ (η * B) * (D : ℝ) := mul_le_mul_of_nonneg_right hbase (le_of_lt hD)
  have hright : (η * B) * (D : ℝ) ≤ (M : ℝ) * η := by
    calc
      (η * B) * (D : ℝ) = (B * (D : ℝ)) * η := by ring
      _ ≤ (M : ℝ) * η := mul_le_mul_of_nonneg_right hMD (le_of_lt hη)
  have hmain : 4 * (D : ℝ) ≤ (M : ℝ) * η := hleft.trans hright
  calc
    4 ≤ ((M : ℝ) * η) / (D : ℝ) := (le_div_iff₀ hD).2 hmain
    _ = (M : ℝ) * (η / (D : ℝ)) := by field_simp [ne_of_gt hD]

/--
The Algorithm-1 cutoff is below one half of the unit circle.
-/
lemma qpe_precision_cutoff_lt_half
    (η : ℝ)
    (D : ℕ)
    (hη : 0 < η)
    (hηhalf : η < (1 / 2 : ℝ))
    (hD : 0 < D) :
    η / (D : ℝ) < (1 / 2 : ℝ) := by
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  have hDone : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hD)
  have hmul : η ≤ η * (D : ℝ) := by simpa using (mul_le_mul_of_nonneg_left hDone (le_of_lt hη))
  have hdiv : η / (D : ℝ) ≤ η := (div_le_iff₀ hDreal).2 hmul
  exact lt_of_le_of_lt hdiv hηhalf

/--
Pure field normalization of the circular-tail denominator.
-/
lemma qpe_tail_scale_rewrite
    (η : ℝ)
    (D M : ℕ)
    (hη : 0 < η)
    (hD : 0 < (D : ℝ))
    (hM : 0 < (M : ℝ)) :
    128 / ((M : ℝ) * (η / (D : ℝ))) = 128 * ((D : ℝ) / ((M : ℝ) * η)) := by
  field_simp [ne_of_gt hη, ne_of_gt hD, ne_of_gt hM]

/--
The actual analytic QPE estimate.
-/
lemma qpeKernel_bad_mass_le_grid_ratio
    (η : ℝ)
    (N D M r : ℕ)
    (hη : 0 < η)
    (hηhalf : η < (1 / 2 : ℝ))
    (hN : 0 < (N : ℝ))
    (hD : 0 < (D : ℝ))
    (hM : 0 < (M : ℝ))
    (hND : N ≤ D)
    (hr : r < N)
    (hgrid : (2 + 1 / (2 * η)) ^ 2 ≤ (M : ℝ) / (D : ℝ)) :
    ∑ t ∈ Finset.univ.filter
        (fun t : Fin M => ¬ |((r : ℝ) / (N : ℝ)) - ((t.1 : ℝ) / (M : ℝ))| < η / (D : ℝ)),
      ‖qpeKernel M ((r : ℝ) / (N : ℝ)) t‖ ^ 2 ≤ 128 * ((D : ℝ) / ((M : ℝ) * η)) := by
  classical
  have hδ : 0 < η / (D : ℝ) := div_pos hη hD
  have hDnat : 0 < D := by exact_mod_cast hD
  have hδhalf : η / (D : ℝ) < (1 / 2 : ℝ) := qpe_precision_cutoff_lt_half η D hη hηhalf hDnat
  have hcutoff : 4 ≤ (M : ℝ) * (η / (D : ℝ)) := qpe_grid_cutoff_ge_four η D M hη hD hgrid
  by_cases hrzero : r = 0
  · subst r
    have hzero :
        ∑ t ∈ Finset.univ.filter
            (fun t : Fin M => ¬ |(0 : ℝ) - ((t.1 : ℝ) / (M : ℝ))| < η / (D : ℝ)),
          ‖qpeKernel M 0 t‖ ^ 2 = 0 :=
      qpeKernel_zero_phase_bad_mass_zero M (η / (D : ℝ)) hM hδ
    norm_cast
    calc
      ∑ t ∈ Finset.univ.filter
          (fun t : Fin M => ¬ |((0 : ℝ) / (N : ℝ)) - ((t.1 : ℝ) / (M : ℝ))| < η / (D : ℝ)),
        ‖qpeKernel M ((0 : ℝ) / (N : ℝ)) t‖ ^ 2 = 0 := by simpa using hzero
      _ ≤ 128 * ((D : ℝ) / ((M : ℝ) * η)) := by positivity
  ·
    have hrpos : 0 < r := Nat.pos_of_ne_zero hrzero
    have hr_real : (r : ℝ) < (N : ℝ) := by exact_mod_cast hr
    have hθ0 : 0 ≤ (r : ℝ) / (N : ℝ) := div_nonneg (by positivity) (le_of_lt hN)
    have hθ1 : (r : ℝ) / (N : ℝ) < 1 := (div_lt_one hN).2 hr_real
    calc
      ∑ t ∈ Finset.univ.filter
          (fun t : Fin M => ¬ |((r : ℝ) / (N : ℝ)) - ((t.1 : ℝ) / (M : ℝ))| < η / (D : ℝ)),
        ‖qpeKernel M ((r : ℝ) / (N : ℝ)) t‖ ^ 2
          ≤ ∑ t ∈ qpeCircularTail M ((r : ℝ) / (N : ℝ)) (η / (D : ℝ)),
              ‖qpeKernel M ((r : ℝ) / (N : ℝ)) t‖ ^ 2 :=
        qpe_ordinary_bad_mass_le_circular_tail η N D M r hηhalf hN hD hND hrpos hr
      _ ≤ 128 / ((M : ℝ) * (η / (D : ℝ))) :=
        qpeKernel_circular_tail_le M ((r : ℝ) / (N : ℝ)) (η / (D : ℝ)) hM hθ0 hθ1 hδ hcutoff
      _ = 128 * ((D : ℝ) / ((M : ℝ) * η)) := qpe_tail_scale_rewrite η D M hη hD hM

end OrdinaryFractionTailBound
