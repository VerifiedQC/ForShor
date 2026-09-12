import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
/-! =========================================================
    Shifted scalar recurrence envelope
========================================================= -/

/--
A natural-valued scalar majorant for the shifted recurrence.

For positive `t`:

  P(t) =
    A * (M + t / k) + B
      + q * P(t / k).

The recursion is well-founded because `t / k < t` when `t > 0`
and `k > 1`.
-/
def shiftedMasterEnvelope
    (k q M A B D : ℕ)
    (hk : 1 < k) :
    ℕ → ℕ
  | 0 => D
  | t + 1 =>
      A * (M + (t + 1) / k) + B
        + q *
          shiftedMasterEnvelope
            k q M A B D hk ((t + 1) / k)
termination_by t => t
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos t) (by omega)

/-- Unfolds the shifted envelope at positive arguments, exposing the recurrence
used in the family induction. -/
lemma shiftedMasterEnvelope_eq_of_pos
    (k q M A B D : ℕ)
    (hk : 1 < k)
    (t : ℕ)
    (ht : 0 < t) :
    shiftedMasterEnvelope k q M A B D hk t
      =
    A * (M + t / k) + B
      + q *
        shiftedMasterEnvelope k q M A B D hk (t / k) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simp [shiftedMasterEnvelope]

/-- The shift `M = k * (c + 1) + 1` absorbs the additive child-width constant
`c`, turning `ceil((M+t)/k) + c` into `M + t/k`. -/
lemma shifted_ceilDiv_le
    (k c t : ℕ)
    (hk : 1 < k) :
    let M := k * (c + 1) + 1
    (M + t + k - 1) / k + c
      ≤ M + t / k := by
  dsimp
  have hkpos : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  have hkc : 2 * (c + 1) ≤ k * (c + 1) :=
    Nat.mul_le_mul_right (c + 1) hk2
  have hnum :
      k * (c + 1) + 1 + t + k - 1 = t + k * (c + 2) := by
    have hmul : k * (c + 2) = k * (c + 1) + k := by
      ring
    omega
  calc
    (k * (c + 1) + 1 + t + k - 1) / k + c
        =
      (t + k * (c + 2)) / k + c := by
      rw [hnum]
    _ =
      (t / k + (c + 2)) + c := by
      rw [Nat.add_mul_div_left t (c + 2) hkpos]
    _ ≤
      k * (c + 1) + 1 + t / k := by
      omega

/-- The scalar envelope is monotone, allowing child bounds at smaller shifted
sizes to be reused at larger shifted sizes. -/
lemma shiftedMasterEnvelope_monotone
    (k q M A B D : ℕ)
    (hk : 1 < k)
    (hq : 1 ≤ q) :
    Monotone
      (shiftedMasterEnvelope k q M A B D hk) := by
  let P : ℕ → ℕ := shiftedMasterEnvelope k q M A B D hk

  have hsucc : ∀ n : ℕ, P n ≤ P (n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        cases n with
        | zero =>
            have hdiv : 1 / k = 0 :=
              Nat.div_eq_of_lt hk
            simp [P, shiftedMasterEnvelope, hdiv]
            have hDq : D ≤ q * D := by
              simpa using Nat.mul_le_mul_right D hq
            omega
        | succ n =>
            have hnpos : 0 < n + 1 := Nat.succ_pos n
            have hn2pos : 0 < n + 2 := Nat.succ_pos (n + 1)

            have hlocal :
                ∀ {a b : ℕ}, a ≤ b → b ≤ n + 1 → P a ≤ P b := by
              intro a b hab hb
              induction hab with
              | refl =>
                  exact le_rfl
              | @step b hab ihab =>
                  exact
                    le_trans
                      (ihab (Nat.le_of_succ_le hb))
                      (ih b (Nat.lt_of_succ_le hb))

            have hdivle :
                (n + 1) / k ≤ (n + 2) / k :=
              Nat.div_le_div_right (Nat.le_succ (n + 1))

            have hdivtop :
                (n + 2) / k ≤ n + 1 :=
              Nat.lt_succ_iff.mp
                (Nat.div_lt_self hn2pos hk)

            have hrec :
                P ((n + 1) / k) ≤ P ((n + 2) / k) :=
              hlocal hdivle hdivtop

            have hwork :
                A * (M + (n + 1) / k) + B
                    + q * P ((n + 1) / k)
                  ≤
                A * (M + (n + 2) / k) + B
                    + q * P ((n + 2) / k) := by
              have hwidth :
                  A * (M + (n + 1) / k)
                    ≤ A * (M + (n + 2) / k) :=
                Nat.mul_le_mul_left A
                  (Nat.add_le_add_left hdivle M)
              have hchildren :
                  q * P ((n + 1) / k)
                    ≤ q * P ((n + 2) / k) :=
                Nat.mul_le_mul_left q hrec
              omega

            simpa [P,
              shiftedMasterEnvelope_eq_of_pos
                k q M A B D hk (n + 1) hnpos,
              shiftedMasterEnvelope_eq_of_pos
                k q M A B D hk (n + 2) hn2pos]
              using hwork

  exact monotone_nat_of_le_succ hsucc

/-! =========================================================
    Finite geometric sums for unrolling recurrence levels
========================================================= -/

/-!
`masterGeom q m = 1 + q + ... + q^(m-1)`.
-/
def masterGeom (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 1 + q * masterGeom q m

/-!
`masterMixed q k m` is the mixed geometric sum generated by the
linear part of the recurrence:

  masterMixed q k 0       = 0
  masterMixed q k (m + 1) = k^m + q * masterMixed q k m.
-/
def masterMixed (q k : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => k ^ m + q * masterMixed q k m

/-- The geometric sum is bounded by the next power of `q` when `q ≥ 2`. -/
lemma masterGeom_add_one_le_pow
    (q m : ℕ)
    (hq : 2 ≤ q) :
    masterGeom q m + 1 ≤ q ^ m := by
  induction m with
  | zero =>
      simp [masterGeom]

  | succ m ih =>
      calc
        masterGeom q (m + 1) + 1
            = q * masterGeom q m + 2 := by
                simp [masterGeom]
                omega
        _ ≤ q * masterGeom q m + q := by
              omega
        _ = q * (masterGeom q m + 1) := by
              ring
        _ ≤ q * q ^ m :=
              Nat.mul_le_mul_left q ih
        _ = q ^ (m + 1) := by
              simp [pow_succ, Nat.mul_comm]

/-- Coarser form of the geometric-sum bound used in the level estimate. -/
lemma masterGeom_le_pow
    (q m : ℕ)
    (hq : 2 ≤ q) :
    masterGeom q m ≤ q ^ m := by
  have h := masterGeom_add_one_le_pow q m hq
  omega

/-- The mixed sum from the linear `k^m` work terms is also controlled by
`q^m` once the branching factor dominates the shrink factor. -/
lemma masterMixed_add_pow_le_pow
    (q k m : ℕ)
    (hkq : k + 1 ≤ q) :
    masterMixed q k m + k ^ m ≤ q ^ m := by
  induction m with
  | zero =>
      simp [masterMixed]

  | succ m ih =>
      have hcoeff :
          (k + 1) * k ^ m ≤ q * k ^ m :=
        Nat.mul_le_mul_right (k ^ m) hkq

      calc
        masterMixed q k (m + 1) + k ^ (m + 1)
            =
          q * masterMixed q k m +
            (k + 1) * k ^ m := by
              simp [masterMixed, pow_succ]
              ring
        _ ≤
          q * masterMixed q k m + q * k ^ m :=
            Nat.add_le_add_left hcoeff _
        _ =
          q * (masterMixed q k m + k ^ m) := by
            ring
        _ ≤
          q * q ^ m :=
            Nat.mul_le_mul_left q ih
        _ =
          q ^ (m + 1) := by
            simp [pow_succ, Nat.mul_comm]

/-- Coarser mixed-sum bound used to collapse the level estimate to one
constant times `q^m`. -/
lemma masterMixed_le_pow
    (q k m : ℕ)
    (hkq : k + 1 ≤ q) :
    masterMixed q k m ≤ q ^ m := by
  have h := masterMixed_add_pow_le_pow q k m hkq
  omega

/-! =========================================================
    Natural-number bounds after a fixed number of levels
========================================================= -/

/-- Unrolls the scalar recurrence for `m` levels when `t < k^m`, keeping the
base contribution, constant work, and linear work as separate sums. -/
lemma shiftedMasterEnvelope_level_bound
    (k q M A B D : ℕ)
    (hk : 1 < k)
    (hq : 1 ≤ q)
    (m t : ℕ)
    (ht : t < k ^ m) :
    shiftedMasterEnvelope k q M A B D hk t
      ≤
    q ^ m * D
      + (A * M + B) * masterGeom q m
      + A * masterMixed q k m := by
  induction m generalizing t with
  | zero =>
      have ht0 : t = 0 := by
        simpa using ht

      subst t
      simp [shiftedMasterEnvelope, masterGeom, masterMixed]

  | succ m ih =>
      by_cases ht0 : t = 0

      · subst t

        have hqpow : 1 ≤ q ^ (m + 1) :=
          one_le_pow₀ hq

        have hD :
            D ≤ q ^ (m + 1) * D := by
          have :=
            Nat.mul_le_mul_right D hqpow
          simpa using this

        calc
          shiftedMasterEnvelope k q M A B D hk 0
              = D := by
                  simp [shiftedMasterEnvelope]
          _ ≤ q ^ (m + 1) * D :=
                hD
          _ ≤
              q ^ (m + 1) * D
                + (A * M + B) * masterGeom q (m + 1)
                + A * masterMixed q k (m + 1) := by
                omega

      · have htpos : 0 < t :=
          Nat.pos_of_ne_zero ht0

        have hdiv :
            t / k < k ^ m := by
          by_contra h

          have hle :
              k ^ m ≤ t / k :=
            Nat.le_of_not_gt h

          have hmul :
              k ^ m * k ≤ (t / k) * k :=
            Nat.mul_le_mul_right k hle

          have hdivmul :
              (t / k) * k ≤ t :=
            Nat.div_mul_le_self t k

          have hpowle :
              k ^ (m + 1) ≤ t := by
            calc
              k ^ (m + 1)
                  = k ^ m * k := by
                      simp [pow_succ]
              _ ≤ (t / k) * k :=
                    hmul
              _ ≤ t :=
                    hdivmul

          omega

        have hchild :=
          ih (t / k) hdiv

        have hdivle :
            t / k ≤ k ^ m :=
          Nat.le_of_lt hdiv

        have hlinear :
            A * (t / k) ≤ A * k ^ m :=
          Nat.mul_le_mul_left A hdivle

        have hrecursive :
            q *
                shiftedMasterEnvelope
                  k q M A B D hk (t / k)
              ≤
            q *
              (q ^ m * D
                + (A * M + B) * masterGeom q m
                + A * masterMixed q k m) :=
          Nat.mul_le_mul_left q hchild

        have hrecurrence :
            shiftedMasterEnvelope k q M A B D hk t
              =
            (A * M + B)
              + A * (t / k)
              + q *
                shiftedMasterEnvelope
                  k q M A B D hk (t / k) := by
          rw [
            shiftedMasterEnvelope_eq_of_pos
              k q M A B D hk t htpos
          ]
          ring

        rw [hrecurrence]

        calc
          (A * M + B)
                + A * (t / k)
                + q *
                  shiftedMasterEnvelope
                    k q M A B D hk (t / k)
              ≤
            (A * M + B)
                + A * k ^ m
                + q *
                  shiftedMasterEnvelope
                    k q M A B D hk (t / k) := by
              exact
                Nat.add_le_add_right
                  (Nat.add_le_add_left
                    hlinear
                    (A * M + B))
                  _

          _ ≤
            (A * M + B)
                + A * k ^ m
                + q *
                  (q ^ m * D
                    + (A * M + B) * masterGeom q m
                    + A * masterMixed q k m) := by
              exact
                Nat.add_le_add_left
                  hrecursive
                  ((A * M + B) + A * k ^ m)

          _ =
            q ^ (m + 1) * D
              + (A * M + B) * masterGeom q (m + 1)
              + A * masterMixed q k (m + 1) := by
              simp [masterGeom, masterMixed, pow_succ]
              ring

/-- Collapses the detailed level bound to a single coarse constant times
`q^m`. -/
lemma shiftedMasterEnvelope_coarse_level_bound
    (k q M A B D : ℕ)
    (hk : 1 < k)
    (hq2 : 2 ≤ q)
    (hkq : k + 1 ≤ q)
    (m t : ℕ)
    (ht : t < k ^ m) :
    shiftedMasterEnvelope k q M A B D hk t
      ≤
    (D + (A * M + B) + A) * q ^ m := by
  have hlevel :=
    shiftedMasterEnvelope_level_bound
      k q M A B D hk
      (by omega)
      m t ht

  have hgeom :
      masterGeom q m ≤ q ^ m :=
    masterGeom_le_pow q m hq2

  have hmixed :
      masterMixed q k m ≤ q ^ m :=
    masterMixed_le_pow q k m hkq

  calc
    shiftedMasterEnvelope k q M A B D hk t
        ≤
      q ^ m * D
        + (A * M + B) * masterGeom q m
        + A * masterMixed q k m :=
      hlevel

    _ ≤
      q ^ m * D
        + (A * M + B) * q ^ m
        + A * q ^ m := by
      gcongr

    _ =
      (D + (A * M + B) + A) * q ^ m := by
      ring

/-! =========================================================
    Converting level bounds to real-power bounds
========================================================= -/

/-- The power selected by `Nat.clog` is at most one factor of `k` larger than
the target size; this bridges level counts to polynomial size bounds. -/
lemma pow_clog_le_mul_self
    (k n : ℕ)
    (hk : 1 < k)
    (hn : 1 ≤ n) :
    k ^ Nat.clog k n ≤ k * n := by
  by_cases hn1 : n = 1

  · simp[hn1]
    omega

  · have hnlt : 1 < n := by
      omega

    let m := Nat.clog k n

    have hmpos : 0 < m := by
      dsimp [m]
      exact Nat.clog_pos hk hnlt

    have hpred :
        k ^ m.pred < n := by
      dsimp [m]
      exact Nat.pow_pred_clog_lt_self hk hnlt

    have hpredle :
        k ^ m.pred ≤ n :=
      Nat.le_of_lt hpred

    calc
      k ^ Nat.clog k n
          = k ^ m := by
              rfl
      _ = k ^ (m.pred + 1) := by
            congr 1
            simp
            rw[Nat.sub_add_cancel]
            omega
      _ = k ^ m.pred * k := by
            simp [pow_succ]
      _ ≤ n * k :=
            Nat.mul_le_mul_right k hpredle
      _ = k * n := by
            rw [Nat.mul_comm]

/-- Rewrites `q^clog_k(t+1)` as a real power using `k^α = q`, then bounds it
by a constant multiple of `(M+t)^α`. -/
lemma q_pow_clog_le_q_mul_rpow
    (k q M t : ℕ)
    (α : ℝ)
    (hk : 1 < k)
    (hM : 1 ≤ M)
    (hα : 1 < α)
    (hkα :
      Real.rpow (k : ℝ) α = (q : ℝ)) :
    ((q ^ Nat.clog k (t + 1) : ℕ) : ℝ)
      ≤
    (q : ℝ) * Real.rpow (M + t : ℝ) α := by
  let m := Nat.clog k (t + 1)

  have hα0 : 0 ≤ α := by
    linarith

  have hkpow :
      k ^ m ≤ k * (t + 1) := by
    dsimp [m]
    exact
      pow_clog_le_mul_self
        k (t + 1) hk (by omega)

  have hkpowR :
      (((k ^ m : ℕ) : ℝ))
        ≤
      (((k * (t + 1) : ℕ) : ℝ)) := by
    exact_mod_cast hkpow

  have hrpowBase :
      Real.rpow (((k ^ m : ℕ) : ℝ)) α
        ≤
      Real.rpow (((k * (t + 1) : ℕ) : ℝ)) α :=
    Real.rpow_le_rpow
      (by positivity)
      hkpowR
      hα0

  have hqpow :
      (((q ^ m : ℕ) : ℝ))
        =
      Real.rpow (((k ^ m : ℕ) : ℝ)) α := by
    calc
      (((q ^ m : ℕ) : ℝ))
          = (q : ℝ) ^ m := by
              simp
      _ =
          (Real.rpow (k : ℝ) α) ^ m := by
            rw [hkα]
      _ =
          Real.rpow ((k : ℝ) ^ m) α := by
            simpa using
              Real.rpow_pow_comm
                (show 0 ≤ (k : ℝ) by positivity)
                α m
      _ =
          Real.rpow (((k ^ m : ℕ) : ℝ)) α := by
            simp

  have htM :
      t + 1 ≤ M + t := by
    omega

  have htMR :
      ((t + 1 : ℕ) : ℝ) ≤ ((M + t : ℕ) : ℝ) := by
    exact_mod_cast htM

  have hrpowTM :
      Real.rpow ((t + 1 : ℕ) : ℝ) α
        ≤
      Real.rpow ((M + t : ℕ) : ℝ) α :=
    Real.rpow_le_rpow
      (by positivity)
      htMR
      hα0

  calc
    (((q ^ Nat.clog k (t + 1) : ℕ) : ℝ))
        =
      (((q ^ m : ℕ) : ℝ)) := by
        rfl

    _ =
      Real.rpow (((k ^ m : ℕ) : ℝ)) α :=
      hqpow

    _ ≤
      Real.rpow (((k * (t + 1) : ℕ) : ℝ)) α :=
      hrpowBase

    _ =
      Real.rpow (k : ℝ) α *
        Real.rpow ((t + 1 : ℕ) : ℝ) α := by
      simpa [Nat.cast_mul] using
        Real.mul_rpow
          (show 0 ≤ (k : ℝ) by positivity)
          (show 0 ≤ ((t + 1 : ℕ) : ℝ) by positivity)

    _ =
      (q : ℝ) *
        Real.rpow ((t + 1 : ℕ) : ℝ) α := by
      rw [hkα]

    _ ≤
      (q : ℝ) *
        Real.rpow ((M + t : ℕ) : ℝ) α :=
      mul_le_mul_of_nonneg_left
        hrpowTM
        (by positivity)

    _ =
      (q : ℝ) *
        Real.rpow (M + t : ℝ) α := by
      simp [Nat.cast_add]

/-! =========================================================
    Scalar shifted Master theorem
========================================================= -/

/--
The scalar recurrence

  P(0) = D
  P(t) = A * (M + t/k) + B + q * P(t/k)

has growth `O((M+t)^α)` when `k^α = q` and `α > 1`.
-/
lemma shiftedMasterEnvelope_rpow_bound
    (k q M A B D : ℕ)
    (α : ℝ)
    (hk : 1 < k)
    (hM : 1 ≤ M)
    (hα : 1 < α)
    (hkα :
      Real.rpow (k : ℝ) α = (q : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℕ,
        (shiftedMasterEnvelope
            k q M A B D hk t : ℝ)
          ≤
        C * Real.rpow (M + t : ℝ) α := by
  have hkR : (1 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk

  have hkqReal : (k : ℝ) < (q : ℝ) := by
    calc
      (k : ℝ)
          = Real.rpow (k : ℝ) 1 := by
              simp
      _ <
          Real.rpow (k : ℝ) α :=
            Real.rpow_lt_rpow_of_exponent_lt
              hkR hα
      _ =
          (q : ℝ) :=
            hkα

  have hkq : k + 1 ≤ q := by
    have : k < q := by
      exact_mod_cast hkqReal
    omega

  have hq2 : 2 ≤ q := by
    omega

  let K : ℕ := D + (A * M + B) + A
  let C : ℝ := (K : ℝ) * (q : ℝ) + 1

  have hC : 0 < C := by
    dsimp [C]
    positivity

  refine ⟨C, hC, ?_⟩
  intro t

  let m : ℕ := Nat.clog k (t + 1)

  have htPow :
      t < k ^ m := by
    have hclog :
        t + 1 ≤ k ^ m := by
      dsimp [m]
      exact Nat.le_pow_clog hk (t + 1)

    omega

  have hEnvelopeNat :
      shiftedMasterEnvelope k q M A B D hk t
        ≤
      K * q ^ m := by
    simpa [K] using
      shiftedMasterEnvelope_coarse_level_bound
        k q M A B D hk
        hq2 hkq
        m t htPow

  have hEnvelopeReal :
      (shiftedMasterEnvelope
          k q M A B D hk t : ℝ)
        ≤
      (K : ℝ) * ((q ^ m : ℕ) : ℝ) := by
    exact_mod_cast hEnvelopeNat

  have hqPow :
      ((q ^ m : ℕ) : ℝ)
        ≤
      (q : ℝ) *
        Real.rpow (M + t : ℝ) α := by
    simpa [m] using
      q_pow_clog_le_q_mul_rpow
        k q M t α hk hM hα hkα

  have hKnonneg : 0 ≤ (K : ℝ) := by
    positivity

  have hrateNonneg :
      0 ≤ Real.rpow (M + t : ℝ) α :=
    Real.rpow_nonneg
      (by positivity)
      α

  calc
    (shiftedMasterEnvelope
        k q M A B D hk t : ℝ)
        ≤
      (K : ℝ) * ((q ^ m : ℕ) : ℝ) :=
      hEnvelopeReal

    _ ≤
      (K : ℝ) *
        ((q : ℝ) *
          Real.rpow (M + t : ℝ) α) :=
      mul_le_mul_of_nonneg_left
        hqPow
        hKnonneg

    _ =
      ((K : ℝ) * (q : ℝ)) *
        Real.rpow (M + t : ℝ) α := by
      ring

    _ ≤
      C * Real.rpow (M + t : ℝ) α := by
      apply
        mul_le_mul_of_nonneg_right
          _ hrateNonneg
      dsimp [C]
      linarith


/-- If `k^α = q` with `k > 1` and `α > 1`, then the branching factor `q` is at
least one.  This is needed for monotonicity of the scalar envelope. -/
lemma one_le_q_of_rpow_eq
    (k q : ℕ)
    (α : ℝ)
    (hk : 1 < k)
    (hα : 1 < α)
    (hkα :
      Real.rpow (k : ℝ) α = (q : ℝ)) :
    1 ≤ q := by
  have hk₁ : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (le_of_lt hk)
  have hα₀ : (0 : ℝ) ≤ α := by
    linarith
  have hpow : (1 : ℝ) ≤ Real.rpow (k : ℝ) α :=
    Real.one_le_rpow hk₁ hα₀
  rw [hkα] at hpow
  exact_mod_cast hpow

/-- Since the final rate uses `max 1 n`, the real-power factor is always at
least one.  This absorbs the finite prefix of the induction. -/
lemma one_le_rpow_max_one
    (n : ℕ)
    (α : ℝ)
    (hα : 0 ≤ α) :
    1 ≤
      Real.rpow
        (((max 1 n : ℕ) : ℝ))
        α := by
  exact
    Real.one_le_rpow
      (by exact_mod_cast Nat.le_max_left 1 n)
      hα

/-- Family-level shifted Master theorem used by the gate-count proof.

It turns a recurrence over arbitrary instances,
`cost i ≤ A * next i + B + q * child_bound`, with
`next i ≤ ceil(size i / k) + c`, into the uniform bound
`cost i = O((max 1 (size i))^α)`. -/
lemma shifted_master_theorem_exact_family
    {ι : Type*}
    (k q c A B : ℕ)
    (α : ℝ)
    (hk : 1 < k)
    (hα : 1 < α)
    (hkα : Real.rpow (k : ℝ) α = (q : ℝ))
    (size next cost: ι → ℕ)
    (hnext : ∀ i : ι,  next i ≤ (size i + k - 1) / k + c)
    (hbounded : ∀ N : ℕ, ∃ D : ℕ, ∀ i : ι, size i ≤ N → cost i ≤ D)
    (hstep : ∀ i : ι,  next i < size i → ∀ D : ℕ,
          (∀ j : ι, size j = next i → cost j ≤ D) →
          cost i ≤ A * next i + B + q * D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ i : ι,
        (cost i : ℝ) ≤
          C * Real.rpow (((max 1 (size i) : ℕ) : ℝ)) α := by
  classical

  /-
  The shift is chosen so that

      ceil((M+t)/k) + c ≤ M + floor(t/k).
  -/
  let M : ℕ := k * (c + 1) + 1

  have hM : 1 ≤ M := by
    dsimp [M]
    omega

  /- Uniform bound for every object whose size is at most `M`. -/
  obtain ⟨D, hD⟩ := hbounded M

  have hq : 1 ≤ q :=
    one_le_q_of_rpow_eq k q α hk hα hkα

  let P : ℕ → ℕ :=
    shiftedMasterEnvelope k q M A B D hk

  have hPmono : Monotone P := by
    simpa [P] using
      shiftedMasterEnvelope_monotone
        k q M A B D hk hq

  obtain ⟨C₀, hC₀, hPpoly⟩ :=
    shiftedMasterEnvelope_rpow_bound
      k q M A B D α hk hM hα hkα

  /-
  The main family-specific induction:

      cost i ≤ P (size i - M).

  This is not supplied by the scalar Master theorem.
  -/
  have hcostP :
      ∀ n : ℕ, ∀ i : ι,
        size i = n →
        cost i ≤ P (n - M) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih i hsize

    by_cases hn : n ≤ M

    · -- Finite base region.
      have hsmall : cost i ≤ D := by
        apply hD i
        simpa [hsize] using hn

      have hsub : n - M = 0 :=
        Nat.sub_eq_zero_of_le hn

      simpa [P, hsub, shiftedMasterEnvelope] using hsmall

    · -- Recursive region.
      have hMn : M < n :=
        Nat.lt_of_not_ge hn

      let t : ℕ := n - M

      have ht : 0 < t := by
        dsimp [t]
        exact Nat.sub_pos_of_lt hMn

      have hn_eq : n = M + t := by
        dsimp [t]
        omega

      /-
      First use the supplied width estimate, then absorb `c` using `M`.
      -/
      have hnext₀ :
          next i ≤ (n + k - 1) / k + c := by
        simpa [hsize] using hnext i

      have hnextBound :
          next i ≤ M + t / k := by
        rw [hn_eq] at hnext₀

        have hshift :
            (M + t + k - 1) / k + c
              ≤ M + t / k := by
          simpa [M] using
            shifted_ceilDiv_le k c t hk

        exact hnext₀.trans hshift

      have htdiv : t / k < t :=
        Nat.div_lt_self ht (by omega)

      have hnext_lt_n : next i < n := by
        rw [hn_eq]
        omega

      /-
      Every child of exact size `next i` is bounded by `P (t/k)`.

      The induction hypothesis gives

          cost j ≤ P (size j - M),

      and monotonicity upgrades this using

          size j - M ≤ t/k.
      -/
      have hchildren :
          ∀ j : ι,
            size j = next i →
            cost j ≤ P (t / k) := by
        intro j hj

        have hjlt : size j < n := by
          rw [hj]
          exact hnext_lt_n

        have hij :
            cost j ≤ P (size j - M) :=
          ih (size j) hjlt j rfl

        have hshiftedChild :
            size j - M ≤ t / k := by
          have hsizej_bound : size j ≤ M + t / k := by
            rw [hj]
            exact hnextBound
          calc
            size j - M ≤ (M + t / k) - M :=
              Nat.sub_le_sub_right hsizej_bound M
            _ = t / k := by
              simp

        exact hij.trans (hPmono hshiftedChild)

      have hrecursive :
          next i < size i := by
        simpa [hsize] using hnext_lt_n

      have hnode :
          cost i
            ≤
          A * next i + B + q * P (t / k) :=
        hstep i hrecursive (P (t / k)) hchildren

      have hscaledNext :
          A * next i ≤ A * (M + t / k) :=
        Nat.mul_le_mul_left A hnextBound

      have hnode' :
          A * next i + B + q * P (t / k)
            ≤
          A * (M + t / k) + B + q * P (t / k) := by
        omega

      have hPstep :
          P t =
            A * (M + t / k) + B
              + q * P (t / k) := by
        simpa [P] using
          shiftedMasterEnvelope_eq_of_pos
            k q M A B D hk t ht

      calc
        cost i
            ≤
          A * next i + B + q * P (t / k) :=
          hnode
        _ ≤
          A * (M + t / k) + B + q * P (t / k) :=
          hnode'
        _ = P t :=
          hPstep.symm
        _ = P (n - M) := by
          rfl

  /-
  One final constant handles both:

  * the finite region `size i ≤ M`, bounded by `D`;
  * the asymptotic region, bounded by `C₀`.
  -/
  let C : ℝ := max 1 (max C₀ (D : ℝ))

  have hC : 0 < C := by
    dsimp [C]
    positivity

  refine ⟨C, hC, ?_⟩
  intro i

  by_cases hi : size i ≤ M

  · -- Finite prefix.
    have hcostD : cost i ≤ D :=
      hD i hi

    have hcostDR :
        (cost i : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast hcostD

    have hDC : (D : ℝ) ≤ C := by
      dsimp [C]
      exact
        le_trans
          (le_max_right C₀ (D : ℝ))
          (le_max_right 1 (max C₀ (D : ℝ)))

    have hα0 : 0 ≤ α :=
      le_trans (by norm_num) (le_of_lt hα)

    have hrate :
        1 ≤
          Real.rpow
            (((max 1 (size i) : ℕ) : ℝ))
            α :=
      one_le_rpow_max_one (size i) α hα0

    have hC0 : 0 ≤ C :=
      le_of_lt hC

    calc
      (cost i : ℝ)
          ≤ (D : ℝ) :=
        hcostDR
      _ ≤ C :=
        hDC
      _ = C * 1 := by
        ring
      _ ≤
        C *
          Real.rpow
            (((max 1 (size i) : ℕ) : ℝ))
            α :=
        mul_le_mul_of_nonneg_left hrate hC0

  · -- Asymptotic region.
    have hMi : M < size i :=
      Nat.lt_of_not_ge hi

    let t : ℕ := size i - M

    have hMt : M + t = size i := by
      dsimp [t]
      omega

    have hcostNat :
        cost i ≤ P t := by
      simpa [t] using
        hcostP (size i) i rfl

    have hcostReal :
        (cost i : ℝ) ≤ (P t : ℝ) := by
      exact_mod_cast hcostNat

    have hpoly :
        (P t : ℝ)
          ≤
        C₀ * Real.rpow (M + t : ℝ) α := by
      simpa [P] using hPpoly t

    have hC₀C : C₀ ≤ C := by
      dsimp [C]
      exact
        le_trans
          (le_max_left C₀ (D : ℝ))
          (le_max_right 1 (max C₀ (D : ℝ)))

    have hpowNonneg :
        0 ≤ Real.rpow (M + t : ℝ) α :=
      Real.rpow_nonneg (by positivity) α

    have hsizeOne : 1 ≤ size i :=
      hM.trans (Nat.le_of_lt hMi)

    calc
      (cost i : ℝ)
          ≤ (P t : ℝ) :=
        hcostReal
      _ ≤
        C₀ * Real.rpow (M + t : ℝ) α :=
        hpoly
      _ ≤
        C * Real.rpow (M + t : ℝ) α :=
        mul_le_mul_of_nonneg_right hC₀C hpowNonneg
      _ =
        C *
          Real.rpow
            (((max 1 (size i) : ℕ) : ℝ))
            α := by
        have hMtR : (M : ℝ) + (t : ℝ) = (size i : ℝ) := by
          exact_mod_cast hMt
        rw [hMtR]
        simp [max_eq_right hsizeOne]
