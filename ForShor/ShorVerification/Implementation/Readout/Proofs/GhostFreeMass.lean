import ForShor.ShorVerification.Implementation.Readout.Main
import ForShor.ShorVerification.Implementation.Readout.Proofs.ShorSetup
import ForShor.ShorVerification.Implementation.Readout.Proofs.ShorSuccess

/-!
# Readout: the ideal success probability as a model-independent number

The ideal semiclassical readout (`semiclassicalIdeal a N m data c`) from a basis ket
with data `= 1` and control `0` ends, on the record reading `o`, in the branch

  `(1/2^m) ∑_{κ < 2^m} exp(-2πi o κ / 2^m) |b₀ with data := a^κ mod N⟩`

(`Readout.branch_closed_form`; only the NUMBER `m` of rounds enters, no exponent
register). The kets `|b₀ with data := v⟩`, `v < N`, are orthonormal in every
`QSemantics`, so the squared norm of that branch is the squared norm of the same
combination of the standard basis vectors `e_v` of `ℂ^N`, written in coordinates:

  `outcomeMass a N m o = ∑_{v < N} ‖(1/2^m) ∑_{κ < 2^m, a^κ mod N = v} exp(-2πi o κ / 2^m)‖²`.

`successMass T verify a N m r = ∑_{o < 2^m} r_found T verify o 2^m r · outcomeMass a N m o`
is then the ideal success probability, a pure real number:

* `norm_sq_combination_eq_outcomeMass`: for ANY family of kets `F v` that is injective on
  `v < N`, `‖(1/2^m) ∑_κ exp(…) • |F (a^κ mod N)⟩‖² = outcomeMass a N m o`;
* `semiclassical_success_eq_mass`: in every `QSemantics`, the success probability of the
  ideal semiclassical readout with `m` rounds and `Q = 2^m` is `successMass … m …`. No
  exponent register appears in the statement or the hypotheses;
* `coherent_success_eq_mass`: the textbook ideal circuit `orderFindingIdeal` (which has an
  exponent register `x`, `m = regSize x.active`) has the same success probability
  `successMass … m …` (by `coherent_projected_state`'s vector and the same lemma);
* `successMass_ge_of_semantics`: in every `QSemantics` with the gate facts, for an
  order-finding instance and `m = log₂(2N²)`, `successMass ≥ κ / log(log₂ N + 1)`. Proof: build
  FRESH registers `y = [0, n)`, `x = [n, n+m)` and the ket `b0` zero on both (every
  `QSemantics` reads and writes every qubit index), apply the existing ideal bound
  `Shor_correct` to `orderFindingIdeal` there, and rewrite it with
  `coherent_success_eq_mass`. These registers live only inside the proof. The pure
  statement (no `qs`) is `Model.successMass_ge` at the concrete model.
-/

namespace Shor
namespace Readout

open MeasureClass

/-- The amplitude on the data value `v` of the ideal branch reading `o`:
`(1/2^m) ∑_{κ < 2^m, a^κ mod N = v} exp(-2πi o κ / 2^m)`. -/
noncomputable def massAmp (a N m o v : ℕ) : ℂ :=
  (1 / 2 ^ m : ℂ) * ∑ κ ∈ (Finset.range (2 ^ m)).filter (fun κ => a ^ κ % N = v),
    Complex.exp (-(2 * Real.pi * Complex.I * ((o : ℂ) * κ) / 2 ^ m))

/-- The probability of the outcome `o` of the ideal readout with `m` rounds: the squared
norm in `ℂ^N` of `(1/2^m) ∑_{κ < 2^m} exp(-2πi o κ / 2^m) e_{a^κ mod N}`, in coordinates. -/
noncomputable def outcomeMass (a N m o : ℕ) : ℝ :=
  ∑ v ∈ Finset.range N, ‖massAmp a N m o v‖ ^ 2

end Readout

/-- **The ideal success probability, model-independent.** With `m` rounds, `Q = 2^m`,
continued-fraction post-processing `r_found T verify o Q r` on the outcome `o`:
`successMass T verify a N m r = ∑_{o < 2^m} r_found T verify o 2^m r · outcomeMass a N m o`. -/
noncomputable def successMass (T : ℕ → ℕ) (verify : ℕ → Bool) (a N m r : ℕ) : ℝ :=
  ∑ o : Fin (2 ^ m), r_found (T := T) verify o.1 (2 ^ m) r * Readout.outcomeMass a N m o.1

namespace Readout

section Norm
variable {qs : QSemantics}

/-- **Orthonormal kets turn the norm into a pure number.** For any kets `F v` that are
pairwise distinct for `v < N` (`N > 0`), the squared norm of
`(1/2^m) ∑_{κ < 2^m} exp(-2πi o κ / 2^m) • |F (a^κ mod N)⟩` is `outcomeMass a N m o`. -/
theorem norm_sq_combination_eq_outcomeMass (a N m o : ℕ) (hN : 0 < N) (F : ℕ → qs.Basis)
    (hF : ∀ v < N, ∀ w < N, F v = F w → v = w) :
    ‖(1 / 2 ^ m : ℂ) • ∑ κ ∈ Finset.range (2 ^ m),
        Complex.exp (-(2 * Real.pi * Complex.I * ((o : ℂ) * κ) / 2 ^ m)) •
          qs.ket (F (a ^ κ % N))‖ ^ 2
      = outcomeMass a N m o := by
  classical
  set e : ℕ → ℂ := fun κ => Complex.exp (-(2 * Real.pi * Complex.I * ((o : ℂ) * κ) / 2 ^ m))
    with he
  have hregroup : ∑ κ ∈ Finset.range (2 ^ m), e κ • qs.ket (F (a ^ κ % N))
      = ∑ v ∈ Finset.range N,
          (∑ κ ∈ (Finset.range (2 ^ m)).filter (fun κ => a ^ κ % N = v), e κ) • qs.ket (F v) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun κ => a ^ κ % N) (t := Finset.range N)
      (fun κ _ => Finset.mem_range.2 (Nat.mod_lt _ hN))]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun κ hκ => ?_
    rw [(Finset.mem_filter.1 hκ).2]
  rw [hregroup, Finset.smul_sum, norm_sq_sum_eq_sum_norm_sq_of_orthogonal]
  · unfold outcomeMass massAmp
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_smul, norm_smul, ket_norm_one, mul_one]
  · intro v hv w hw hvw
    rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      ket_inner_ne qs (fun h => hvw (hF v (Finset.mem_range.1 hv) w (Finset.mem_range.1 hw) h))]
    simp

end Norm

section Semiclassical
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  [LowerGateClass qs] [MeasureClass qs]

/-- The ideal semiclassical readout puts probability `outcomeMass a N m o` on the records
reading `o < 2^m`. Hypotheses: `1 < N ≤ 2^|data|`, `a` coprime to `N`, `c ∉ data`, and
`b₀` has data `= 1` and `c = 0`. No other register. -/
theorem recordOutcomeProb_semiclassicalIdeal (a N m : ℕ) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hdata1 : RegEncoding.toNat data b₀ = 1) (hc0 : RegEncoding.bit c b₀ = false)
    (o : ℕ) (ho : o < 2 ^ m) :
    recordOutcomeProb m ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b₀))) o
      = outcomeMass a N m o := by
  obtain ⟨r₀, hl, hv⟩ := exists_record_of_lt m o ho
  rw [recordOutcomeProb, tsum_eq_single r₀]
  · simp only [hl, hv, and_self, ite_true]
    rw [recordProb, semiclassicalIdeal_eq,
      branch_closed_form a N m data c b₀ hN hNdata ha hc hdata1 hc0 m le_rfl r₀ hl, closedBranch]
    simp only [Nat.sub_self, pow_zero, one_mul, ph, hv]
    refine norm_sq_combination_eq_outcomeMass a N m o (by omega)
      (fun v => RegEncoding.writeNat data v b₀) fun v hv' w hw' h => ?_
    have := congrArg (RegEncoding.toNat data) h
    rwa [RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le hv' hNdata),
      RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le hw' hNdata)] at this
  · intro r hne
    rw [ite_eq_right_iff]
    rintro ⟨hrl, hrv⟩
    exact absurd (readoutOfRecord_inj (hrl.trans hl.symm) (hrv.trans hv.symm)) hne

end Semiclassical

end Readout

section Semiclassical
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  [LowerGateClass qs] [MeasureClass qs]

/-- **The ideal semiclassical success is `successMass`, in every model, without an
exponent register.** Hypotheses: `1 < N ≤ 2^|data|`, `a` coprime to `N`, the control `c`
not in `data`, and the start ket `b₀` has data `= 1` and `c = 0`. For every `m`, `T`,
`verify`, `r`: the success probability (`Q = 2^m`) of the ideal semiclassical readout
with `m` rounds is `successMass T verify a N m r`. -/
theorem semiclassical_success_eq_mass (T : ℕ → ℕ) (verify : ℕ → Bool) (a N m r : ℕ)
    (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hdata1 : RegEncoding.toNat data b₀ = 1) (hc0 : RegEncoding.bit c b₀ = false) :
    probability_of_success_M T verify m r (2 ^ m)
        ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b₀)))
      = successMass T verify a N m r := by
  unfold probability_of_success_M successMass
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Readout.recordOutcomeProb_semiclassicalIdeal a N m data c b₀ hN hNdata ha hc hdata1 hc0
    o.1 o.2]

end Semiclassical

section Coherent
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [MeasureClass qs]

/-- **The textbook ideal circuit has the same success, `successMass`.** For
`orderFindingIdeal qs a N x y` from `|b0⟩` (`x = 0`, `y = 0`, `x`, `y` disjoint,
`1 < N ≤ 2^|y|`, `a` coprime to `N`), with `m = regSize x.active`. -/
theorem coherent_success_eq_mass (T : ℕ → ℕ) (verify : ℕ → Bool) (a N r : ℕ)
    (x y : ExtReg) (b0 : qs.Basis)
    (hN : 1 < N) (hNy : N ≤ ASize y.active) (ha : Nat.Coprime a N)
    (hxy : Disjoint x.active y.active) (hy : 0 < regSize y.active)
    (hx0 : RegEncoding.toNat x.active b0 = 0) (hy0 : RegEncoding.toNat y.active b0 = 0) :
    probability_of_success (qs := qs) (T := T) (verify := verify) (x := x.active) (r := r)
        (Q := ASize x.active) (evalC := qs.eval) (C := orderFindingIdeal qs a N x y)
        (ψ := qs.ket b0)
      = successMass T verify a N (regSize x.active) r := by
  have hx1 : RegEncoding.toNat x.active (Readout.semiclassicalStartKet y b0) = 0 := by
    rw [Readout.semiclassicalStartKet, toNat_left_write_right x.active y.active hxy, hx0]
  have hy1 : RegEncoding.toNat y.active (Readout.semiclassicalStartKet y b0) = 1 :=
    RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le hN hNy)
  unfold probability_of_success successMass
  rw [Readout.orderFindingIdeal_eval_start a N x y b0 hxy hy hx0 hy0]
  refine Finset.sum_congr rfl fun o _ => ?_
  congr 1
  rw [MeasureClass.probMeas, coherent_projected_state a N x y.active _ hN hNy ha hxy hx1 hy1 o.1 o.2]
  refine Readout.norm_sq_combination_eq_outcomeMass a N _ o.1 (by omega)
    (fun v => RegEncoding.writeNat x.active o.1
      (RegEncoding.writeNat y.active v (Readout.semiclassicalStartKet y b0)))
    fun v hv w hw h => ?_
  have hread : ∀ t, t < N → RegEncoding.toNat y.active (RegEncoding.writeNat x.active o.1
      (RegEncoding.writeNat y.active t (Readout.semiclassicalStartKet y b0))) = t := fun t ht => by
    rw [toNat_left_write_right y.active x.active (Disjoint.symm hxy),
      RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le ht hNy)]
  have := congrArg (RegEncoding.toNat y.active) h
  rwa [hread v hv, hread w hw] at this

/-- **The ideal bound on `successMass`, from any model.** In every `QSemantics` with the
gate facts and measurement: for every `T` making the continued-fraction search complete
and every order-finding instance, with `m = log₂(2N²)`,
`successMass T verify a N m (ord a N) ≥ κ / log(log₂ N + 1)` (`verify d = (a^d mod N = 1)`).
The registers used in the proof are built inside it. -/
theorem successMass_ge_of_semantics (qs : QSemantics) [RegEncoding qs.Basis]
    [GateSemanticsFacts qs] [MeasureClass qs]
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) (inst : ShorOrderFindingInstance) :
    successMass T (fun d => decide ((inst.a ^ d) % inst.N = 1)) inst.a inst.N
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1) := by
  set n := Nat.log2 (2 * inst.N)
  set m := Nat.log2 (2 * inst.N ^ 2)
  -- fresh registers: data `y = [0, n)`, exponent `x = [n, n + m)`, no reserves
  let y : ExtReg := ExtReg.ofReg (Reg.interval 0 n)
  let x : ExtReg := ExtReg.ofReg (Reg.interval n m)
  have hsize : ∀ lo s, regSize (Reg.interval lo s) = s := fun lo s => by
    simp [regSize, Reg.width, Reg.interval]
  have hxm : regSize x.active = m := hsize n m
  have hyn : regSize y.active = n := hsize 0 n
  have hown : ExtReg.OwnedDisjoint x y := by
    intro q hqx hqy
    simp [x, y, ExtReg.ofReg, ExtReg.ownedQubits, Reg.interval, Reg.empty] at hqx hqy
    omega
  have hxy : Disjoint x.active y.active := ExtReg.activeDisjoint_of_ownedDisjoint hown
  have hyx : Disjoint y.active x.active := List.disjoint_left.2 fun _ h1 h2 => hxy h2 h1
  let b0 : qs.Basis :=
    RegEncoding.writeNat y.active 0 (RegEncoding.writeNat x.active 0 RegEncoding.zero)
  have hy0 : RegEncoding.toNat y.active b0 = 0 :=
    RegEncoding.toNat_writeNat_of_lt _ _ _ (by unfold ASize; positivity)
  have hx0 : RegEncoding.toNat x.active b0 = 0 := by
    rw [toNat_left_write_right x.active y.active hxy]
    exact RegEncoding.toNat_writeNat_of_lt _ _ _ (by unfold ASize; positivity)
  have hideal := Shor_correct (qs := qs) T hT inst x y b0 hxm hyn ⟨hx0, hy0, hown⟩
  unfold ShorCorrect at hideal
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hNy : inst.N ≤ ASize y.active := by
    simpa [ASize, hyn] using shor_data_capacity_from_log2 inst.N
  have ha : Nat.Coprime inst.a inst.N := Nat.coprime_iff_gcd_eq_one.2 inst.coprime
  have hy : 0 < regSize y.active := Readout.regSize_pos_of_log2 inst.N hN _ hyn
  rw [coherent_success_eq_mass T _ inst.a inst.N _ x y b0 (by omega) hNy ha hxy hy hx0 hy0,
    hxm] at hideal
  exact hideal

end Coherent

end Shor
