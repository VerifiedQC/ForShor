import ForShor.ShorVerification.Implementation.Readout.ShorStatement
import ForShor.ShorVerification.Implementation.Readout.Proofs.Approx

/-!
# Readout: success probability of a semiclassical run, and its stability

* `probability_of_success_M_eq_sum`: with `Q = 2^m`, the success probability is
  the finite sum `∑_{|w| = m} r_found(readoutOfRecord w) · P(w)` over the records
  of length `m`.
* `probability_of_success_M_ge_sub`: for two runs `u`, `v`,
  `success(u) ≥ success(v) - ∑_{|w| = m} |P_u(w) - P_v(w)|`, because each weight
  `r_found ∈ {0, 1}` (here only `0 ≤ r_found ≤ 1` is used). This is the full
  `ℓ¹` distance, not half of it: halving would need both runs to have total
  probability `1`, and an implemented run whose rotations are only contractions
  (`hRc`) may lose probability. With the `ℓ¹` bound `2 ∑ (ε + ρ)` this gives the
  loss `2 ∑ (ε + ρ)`, the same form as the existing coherent loss
  `2 · regSize x · stepErr K η`.
-/

namespace Shor
namespace Readout

variable {qs : QSemantics}

/-- `r_found` is `0` or `1`, so it lies in `[0, 1]`. -/
theorem r_found_mem_unit (T : ℕ → ℕ) (verify : ℕ → Bool) (o Q r : ℕ) :
    0 ≤ r_found (T := T) verify o Q r ∧ r_found (T := T) verify o Q r ≤ 1 := by
  unfold r_found
  split_ifs <;> norm_num

/-- `recordOutcomeProb` as a finite sum over the records of length `m`. -/
theorem recordOutcomeProb_eq_sum (m : ℕ) (ψ : MState qs) (o : ℕ) :
    recordOutcomeProb m ψ o
      = ∑ w : List.Vector Bool m,
          if readoutOfRecord w.1 = o then recordProb ψ w.1 else 0 := by
  rw [recordOutcomeProb, tsum_eq_sum_vector m _ fun r hr => by simp [hr]]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [w.2]

/-- **Success probability as a sum over records.** With `Q = 2^m`, the success
probability of a run is `∑_{|w| = m} r_found(readoutOfRecord w) · P(w)`. -/
theorem probability_of_success_M_eq_sum (T : ℕ → ℕ) (verify : ℕ → Bool) (m r Q : ℕ)
    (hQ : Q = 2 ^ m) (ψ : MState qs) :
    probability_of_success_M T verify m r Q ψ
      = ∑ w : List.Vector Bool m,
          r_found (T := T) verify (readoutOfRecord w.1) Q r * recordProb ψ w.1 := by
  unfold probability_of_success_M
  simp only [recordOutcomeProb_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hlt : readoutOfRecord w.1 < Q := by
    have := readoutOfRecord_lt w.1
    rwa [w.2, ← hQ] at this
  rw [Finset.sum_eq_single ⟨readoutOfRecord w.1, hlt⟩]
  · simp
  · intro o _ ho
    split_ifs with h
    · exact absurd (Fin.ext h.symm) ho
    · rw [mul_zero]
  · simp

/-- **Stability of the success probability.** For any two runs `u`, `v`, with
`Q = 2^m`: `success(u) ≥ success(v) - ∑_{|w| = m} |P_u(w) - P_v(w)|`. -/
theorem probability_of_success_M_ge_sub (T : ℕ → ℕ) (verify : ℕ → Bool) (m r Q : ℕ)
    (hQ : Q = 2 ^ m) (u v : MState qs) :
    probability_of_success_M T verify m r Q u
      ≥ probability_of_success_M T verify m r Q v
        - ∑ w : List.Vector Bool m, |recordProb u w.1 - recordProb v w.1| := by
  rw [probability_of_success_M_eq_sum T verify m r Q hQ u,
    probability_of_success_M_eq_sum T verify m r Q hQ v, ge_iff_le, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  obtain ⟨h0, h1⟩ := r_found_mem_unit T verify (readoutOfRecord w.1) Q r
  set ρ := r_found (T := T) verify (readoutOfRecord w.1) Q r
  have hd : -|recordProb u w.1 - recordProb v w.1| ≤ recordProb u w.1 - recordProb v w.1 :=
    neg_abs_le _
  have ha := abs_nonneg (recordProb u w.1 - recordProb v w.1)
  nlinarith

/-- Two runs with the same record probabilities have the same success
probability. -/
theorem probability_of_success_M_congr (T : ℕ → ℕ) (verify : ℕ → Bool) (m r Q : ℕ)
    {u v : MState qs} (h : ∀ rec, recordProb u rec = recordProb v rec) :
    probability_of_success_M T verify m r Q u = probability_of_success_M T verify m r Q v := by
  simp only [probability_of_success_M, recordOutcomeProb, h]

end Readout
end Shor
