import ForShor.ShorVerification.Implementation.Readout.Proofs.Basic
import ForShor.ShorVerification.Implementation.Shor.Proofs.NaiveShor.GoodOutcomeMassLowerBound

/-!
# Readout: the coherent inverse-QFT readout, and comparing the two

* `coherent_measProj`: from a basis ket `|b₀⟩` with exponent register `x = 0`
  and data `= 1`, the circuit `H_reg x ;; modExpIdeal' a N x data ;; IQFT x`
  followed by the projector onto `x = o` (`o < 2^|x|`) gives

    `(1/√M · 1/√M) ∑_{t < M} conj(ω_M^(t·o)) |b₀ with x := o, data := a^t mod N⟩`,  `M = 2^|x|`.

  It reuses the existing exact lemmas `eval_Hreg_zero_uniform_sum`,
  `eval_modExpIdeal_ket` and `QFTSemantics.eval_adj_QFT_ket`.
* `norm_sum_smul_ket_map`: relabelling the kets of a finite combination by a
  map that is injective on them does not change its norm.
-/

namespace Shor
namespace Readout

open MeasureClass

variable {qs : QSemantics} [RegEncoding qs.Basis]

omit [RegEncoding qs.Basis] in
/-- Relabelling kets by a map `G` that does not merge any two of the kets
`h i` (`i ∈ s`) keeps the norm of `∑ g i • |h i⟩`. -/
theorem norm_sum_smul_ket_map {ι : Type*} (s : Finset ι) (g : ι → ℂ) (h : ι → qs.Basis)
    (G : qs.Basis → qs.Basis) (hG : ∀ i ∈ s, ∀ j ∈ s, G (h i) = G (h j) → h i = h j) :
    ‖∑ i ∈ s, g i • qs.ket (G (h i))‖ = ‖∑ i ∈ s, g i • qs.ket (h i)‖ := by
  have hinner : inner ℂ (∑ i ∈ s, g i • qs.ket (G (h i))) (∑ i ∈ s, g i • qs.ket (G (h i)))
      = inner ℂ (∑ i ∈ s, g i • qs.ket (h i)) (∑ i ∈ s, g i • qs.ket (h i)) := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun i hi => ?_
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    by_cases e : h j = h i
    · rw [e, ket_inner_self, ket_inner_self]
    · rw [ket_inner_ne qs e, ket_inner_ne qs (fun e' => e (hG j hj i hi e'))]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (∑ i ∈ s, _), hinner]

variable [GateSemanticsFacts qs] [MeasureClass qs]

/-- **The coherent readout, projected on `x = o`.** -/
theorem coherent_measProj (a N : ℕ) (x : ExtReg) (data : Reg) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N)
    (hxdata : Disjoint x.active data)
    (hx0 : RegEncoding.toNat x.active b₀ = 0) (hdata1 : RegEncoding.toNat data b₀ = 1)
    (o : ℕ) (ho : o < ASize x.active) :
    measProj x.active o
        (qs.eval (H_reg x.active ;; modExpIdeal' qs a N x.active data ;; IQFT x) (qs.ket b₀))
      = ((1 / Real.sqrt (ASize x.active : ℝ) : ℂ) * (1 / Real.sqrt (ASize x.active : ℝ) : ℂ)) •
        ∑ t ∈ Finset.range (ASize x.active), star (qftPhase (ASize x.active) t o) •
          qs.ket (RegEncoding.writeNat x.active o
            (RegEncoding.writeNat data (a ^ t % N) b₀)) := by
  set M := ASize x.active
  set k : ℂ := (1 / Real.sqrt (M : ℝ) : ℂ)
  have hdx : Disjoint data x.active := Disjoint.symm hxdata
  -- one exponent value `t`
  have hket : ∀ t : Fin M,
      measProj x.active o (qs.eval (IQFT x) (qs.eval (modExpIdeal' qs a N x.active data)
          (qs.ket (RegEncoding.writeNat x.active t.1 b₀))))
        = k • (star (qftPhase M t.1 o) • qs.ket (RegEncoding.writeNat x.active o
            (RegEncoding.writeNat data (a ^ t.1 % N) b₀))) := by
    intro t
    have hxt : RegEncoding.toNat x.active (RegEncoding.writeNat x.active t.1 b₀) = t.1 :=
      RegEncoding.toNat_writeNat_of_lt _ _ _ t.isLt
    have hdt : RegEncoding.toNat data (RegEncoding.writeNat x.active t.1 b₀) = 1 := by
      rw [toNat_left_write_right data x.active hdx, hdata1]
    rw [eval_modExpIdeal_ket a N x.active data _ hN ha hxdata hNdata (by rw [hdt]; exact hN),
      hdt, hxt, one_mul, IQFT, QFTSemantics.eval_adj_QFT_ket, map_smul, map_sum]
    have hβ : ExtReg.toNat x (RegEncoding.writeNat data (a ^ t.1 % N)
        (RegEncoding.writeNat x.active t.1 b₀)) = t.1 := by
      rw [ExtReg.toNat, toNat_left_write_right x.active data hxdata, hxt]
    rw [hβ]
    congr 1
    simp only [map_smul, MeasureClass.measProj_ket]
    rw [Finset.sum_eq_single ⟨o, ho⟩]
    · rw [RegEncoding.toNat_writeNat_of_lt _ _ _ ho, ite_eq_left_of_eq_true _ _ (eq_self o),
        writeNat_comm_of_disjoint data x.active hdx, RegEncoding.writeNat_overwrite]
    · intro y _ hy
      rw [RegEncoding.toNat_writeNat_of_lt _ _ _ y.isLt]
      split_ifs with h
      · exact absurd (Fin.ext h) hy
      · exact smul_zero _
    · simp
  rw [qs.eval_seq, qs.eval_seq, eval_Hreg_zero_uniform_sum x b₀ hx0]
  set L : qs.State →ₗ[ℂ] qs.State := (measProj x.active o).toLinearMap ∘ₗ
    gateL (IQFT x) ∘ₗ gateL (modExpIdeal' qs a N x.active data)
  have hL : ∀ φ, measProj x.active o (qs.eval (IQFT x)
      (qs.eval (modExpIdeal' qs a N x.active data) φ)) = L φ := fun φ => rfl
  rw [hL, map_smul, map_sum]
  simp only [← hL, hket]
  rw [← Finset.smul_sum, smul_smul,
    Fin.sum_univ_eq_sum_range (fun t => star (qftPhase M t o) • qs.ket (RegEncoding.writeNat
      x.active o (RegEncoding.writeNat data (a ^ t % N) b₀))) M]

end Readout
end Shor
