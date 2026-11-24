import ForShor.ShorVerification.Implementation.Readout.Proofs.Record
import ForShor.ShorVerification.Implementation.Readout.Proofs.Deferred

/-!
# Readout: the closed form of every branch of the semiclassical readout

Fix `a, N`, the data register `data`, the control `c` and the number of rounds
`m`, and let round `j` use the ideal controlled multiplier by
`a ^ (2^(m-1-j)) mod N` (`semiclassicalIdeal`). Start from a basis ket `|b₀⟩`
with `c = 0` and `data = 1`. After `k ≤ m` rounds, the branch at a record `r`
of length `k` is (`branch_closed_form`)

  `(1/2^k) · ∑_{κ < 2^k} exp(-2πi · v · κ / 2^k) · |b₀ with data := a^(2^(m-k) · κ) mod N⟩`,

where `v = readoutOfRecord r` (little-endian). The proof is an induction on `k`
with the one-round identity `round_branch` (Griffiths-Niu): the round splits
`κ' < 2^(k+1)` into `2κ` (control `0`) and `2κ + 1` (control `1`), and the
feed-forward phase `ffAngle k r = -(v / 2^k)` (`ffAngle_eq_neg_readout_div`) is
exactly the phase that turns `exp(-2πi v κ / 2^k)` into
`exp(-2πi v' (2κ+1) / 2^(k+1))` with `v' = v + b · 2^k`.

At `k = m` this is `(1/2^m) ∑_κ exp(-2πi o κ / 2^m) |data = a^κ mod N⟩` with
`o = readoutOfRecord r`, the state `Readout/Main.lean` compares with the
coherent inverse-QFT readout.
-/

namespace Shor
namespace Readout

open MeasureClass
open Complex

/-! ## The phase -/

/-- `exp(-2πi · v · κ / 2^k)`. -/
noncomputable def ph (k v κ : ℕ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((v : ℂ) * κ) / 2 ^ k))

theorem ph_zero_zero : ph 0 0 0 = 1 := by simp [ph]

/-- Even index: `exp(-2πi (v + b 2^k) (2κ) / 2^(k+1)) = exp(-2πi v κ / 2^k)`. -/
theorem ph_succ_even (k v κ : ℕ) (b : Bool) :
    ph (k + 1) (v + bitVal b * 2 ^ k) (2 * κ) = ph k v κ := by
  unfold ph
  have h : -(2 * (Real.pi : ℂ) * I * (((v + bitVal b * 2 ^ k : ℕ) : ℂ) * ((2 * κ : ℕ) : ℂ))
        / 2 ^ (k + 1))
      = -(2 * Real.pi * I * ((v : ℂ) * κ) / 2 ^ k)
        + ((-(bitVal b * κ : ℕ) : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast
    field_simp
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Odd index: the extra factor is the round's outcome sign times the
feed-forward phase `exp(iπ · (-(v / 2^k)))`. -/
theorem ph_succ_odd (k v κ : ℕ) (b : Bool) :
    ph (k + 1) (v + bitVal b * 2 ^ k) (2 * κ + 1)
      = ph k v κ * (outcomeSign b *
          Complex.exp (((Angle.toReal (-((v : ℚ) / 2 ^ k)) : ℝ) : ℂ) * I)) := by
  unfold ph
  rw [Angle.toReal]
  cases b
  · have h : -(2 * (Real.pi : ℂ) * I * (((v + bitVal false * 2 ^ k : ℕ) : ℂ)
          * ((2 * κ + 1 : ℕ) : ℂ)) / 2 ^ (k + 1))
        = -(2 * Real.pi * I * ((v : ℂ) * κ) / 2 ^ k)
          + ((((-((v : ℚ) / 2 ^ k) : ℚ) : ℝ) * Real.pi : ℝ) : ℂ) * I := by
      simp only [bitVal]
      push_cast
      field_simp
      ring
    rw [h, Complex.exp_add, outcomeSign]
    simp
  · have h : -(2 * (Real.pi : ℂ) * I * (((v + bitVal true * 2 ^ k : ℕ) : ℂ)
          * ((2 * κ + 1 : ℕ) : ℂ)) / 2 ^ (k + 1))
        = -(2 * Real.pi * I * ((v : ℂ) * κ) / 2 ^ k)
          + ((((-((v : ℚ) / 2 ^ k) : ℚ) : ℝ) * Real.pi : ℝ) : ℂ) * I
          + ((-(κ : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I) + (-(Real.pi * I)) := by
      simp only [bitVal]
      push_cast
      field_simp
      ring
    rw [h, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      Complex.exp_neg ((Real.pi : ℂ) * I), Complex.exp_pi_mul_I, outcomeSign]
    simp

/-- At the last round the phase is the conjugated QFT phase:
`exp(-2πi o κ / 2^m) = conj(ω_{2^m}^(κ·o))`. -/
theorem ph_eq_star_qftPhase (m o κ : ℕ) :
    ph m o κ = star (qftPhase (2 ^ m) κ o) := by
  unfold ph qftPhase ωPow ω
  rw [← Complex.exp_nat_mul]
  change _ = (starRingEnd ℂ) _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_div₀, map_natCast, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-! ## Sums over `κ < 2^(k+1)` split by parity -/

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ∑ i ∈ Finset.range (2 * n), g i = ∑ i ∈ Finset.range n, (g (2 * i) + g (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

/-! ## The closed form -/

section ClosedForm

variable {qs : QSemantics} [RegEncoding qs.Basis]
  [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]

/-- The multiplier schedule of `semiclassicalIdeal`: round `j` multiplies by
`a ^ (2^(m-1-j)) mod N`, controlled by `c`. -/
def schedule (a N m : ℕ) (data : Reg) (c : ℕ) : ℕ → Gate :=
  fun j => Gate.idealCtrlModMul ((a ^ (2 ^ (m - 1 - j))) % N) N data c

/-- Each multiplier `a^e mod N` of the schedule is coprime to `N`. -/
theorem coprime_pow_mod (a N : ℕ) (ha : Nat.Coprime a N) (e : ℕ) :
    Nat.Coprime (a ^ e % N) N := by
  have hp : Nat.Coprime (a ^ e) N := ha.pow_left _
  have hg : Nat.gcd (a ^ e % N) N = Nat.gcd (a ^ e) N := by
    rw [Nat.gcd_comm (a ^ e) N, ← Nat.gcd_rec]
  unfold Nat.Coprime
  rw [hg]; exact hp

omit [RegEncoding qs.Basis] [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] in
theorem semiclassicalIdeal_eq (a N m : ℕ) (data : Reg) (c : ℕ) :
    semiclassicalIdeal a N m data c = readoutRounds (schedule a N m data c) c m := rfl

/-- One more round is `readoutRound` (`Proofs/Deferred.lean`) after the others. -/
theorem readoutRounds_succ_eval (U : ℕ → Gate) (c k : ℕ) (ψ : MState qs) :
    (readoutRounds U c (k + 1)).eval ψ
      = (readoutRound c (U k) k).eval ((readoutRounds U c k).eval ψ) := rfl

/-- The closed-form branch after `k` rounds at a record reading `v`:
`(1/2^k) ∑_{κ < 2^k} exp(-2πi v κ / 2^k) |b₀ with data := a^(2^(m-k)·κ) mod N⟩`. -/
noncomputable def closedBranch (a N m : ℕ) (data : Reg) (b₀ : qs.Basis) (k v : ℕ) :
    qs.State :=
  (1 / 2 ^ k : ℂ) • ∑ κ ∈ Finset.range (2 ^ k),
    ph k v κ • qs.ket (RegEncoding.writeNat data (a ^ (2 ^ (m - k) * κ) % N) b₀)

omit [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] in
/-- The closed-form branch is a combination of kets with `c = 0` and data `< N`. -/
theorem inRange_closedBranch (a N m : ℕ) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (hc : c ∉ data.qubits)
    (hc0 : RegEncoding.bit c b₀ = false) (k v : ℕ) :
    InRange c data N (closedBranch a N m data b₀ k v) := by
  unfold closedBranch InRange
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun κ _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, ?_⟩, rfl⟩))
  · rw [RegEncoding.bit_writeNat_out _ _ _ _ hc, hc0]
  · have hlt : a ^ (2 ^ (m - k) * κ) % N < N := Nat.mod_lt _ (by omega)
    rw [RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le hlt hNdata)]
    exact hlt

omit [LowerGateClass qs] [MeasureClass qs] in
/-- The uncontrolled action `X c (U (X c ·))` as a linear map. -/
theorem uncontrolledAction_eq_linear [PauliXSemantics qs] (c : ℕ) (U : Gate) (φ : qs.State) :
    uncontrolledAction c U φ
      = (gateL (Gate.X c) ∘ₗ gateL U ∘ₗ gateL (Gate.X c)) φ := rfl

omit [LowerGateClass qs] in
/-- The uncontrolled action of the round-`k` multiplier on a closed-form ket:
it multiplies the data value by `a^(2^(m-1-k)) mod N`, which turns the exponent
`2^(m-k)·κ` into `2^(m-(k+1))·(2κ+1)`. -/
theorem uncontrolledAction_schedule_ket [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs]
    (a N m : ℕ) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hc0 : RegEncoding.bit c b₀ = false) (k : ℕ) (hk : k < m) (κ : ℕ) :
    uncontrolledAction c (schedule a N m data c k)
        (qs.ket (RegEncoding.writeNat data (a ^ (2 ^ (m - k) * κ) % N) b₀))
      = qs.ket (RegEncoding.writeNat data (a ^ (2 ^ (m - (k + 1)) * (2 * κ + 1)) % N) b₀) := by
  set v := a ^ (2 ^ (m - k) * κ) % N with hv
  have hvN : v < N := Nat.mod_lt _ (by omega)
  have hak : Nat.Coprime (a ^ 2 ^ (m - 1 - k) % N) N := coprime_pow_mod a N ha _
  have hxd : RegEncoding.toNat data (RegEncoding.writeNat data v b₀) = v :=
    RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le hvN hNdata)
  have hxc : RegEncoding.bit c (RegEncoding.writeNat data v b₀) = false := by
    rw [RegEncoding.bit_writeNat_out _ _ _ _ hc, hc0]
  obtain ⟨-, -, -, h4⟩ := idealCtrlModMul_round_hyps_ket (a ^ 2 ^ (m - 1 - k) % N) N data c
    (RegEncoding.writeNat data v b₀) hN hNdata hak hc (by rw [hxd]; exact hvN) hxc
  unfold schedule
  rw [h4, hxd, RegEncoding.writeNat_overwrite]
  congr 2
  rw [hv, ← Nat.mul_mod, ← pow_add]
  congr 2
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [show k + d + 1 - 1 - k = d by omega, show k + d + 1 - k = d + 1 by omega,
    show k + d + 1 - (k + 1) = d by omega, pow_succ]
  ring

variable [HadamardSemantics qs] [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs]

/-- **Closed form of the semiclassical readout's branches.** Let `|b₀⟩` have
the control `c` at `0` and the data register at `1`, with `1 < N ≤ 2^|data|`,
`a` coprime to `N`, `c ∉ data`. After `k ≤ m` rounds of the schedule of
`semiclassicalIdeal a N m data c`, the branch at every record `r` of length
`k` is `closedBranch a N m data b₀ k (readoutOfRecord r)`, i.e.

  `(1/2^k) ∑_{κ < 2^k} exp(-2πi v κ / 2^k) |b₀ with data := a^(2^(m-k)·κ) mod N⟩`,
  `v = readoutOfRecord r`. -/
theorem branch_closed_form (a N m : ℕ) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hdata1 : RegEncoding.toNat data b₀ = 1) (hc0 : RegEncoding.bit c b₀ = false) :
    ∀ (k : ℕ), k ≤ m → ∀ (r : Record), r.length = k →
      (readoutRounds (schedule a N m data c) c k).eval (MState.init (qs.ket b₀)) r
        = closedBranch a N m data b₀ k (readoutOfRecord r) := by
  intro k
  induction k with
  | zero =>
    intro _ r hr
    rw [List.length_eq_zero_iff] at hr
    subst hr
    simp only [readoutRounds, MGate.eval_unitary, MState.init, ite_true, GateSemanticsCore.eval_id,
      closedBranch, pow_zero, Finset.range_one, Finset.sum_singleton, mul_zero, readoutOfRecord,
      ph_zero_zero, one_smul, div_one]
    rw [Nat.mod_eq_of_lt hN, ← hdata1, RegEncoding.writeNat_toNat]
  | succ k ih =>
    intro hk r hr
    rcases List.eq_nil_or_concat r with rfl | ⟨r₀, b, rfl⟩
    · simp at hr
    rw [List.concat_eq_append] at hr ⊢
    have hr₀ : r₀.length = k := by simpa using hr
    set ψ := (readoutRounds (schedule a N m data c) c k).eval (MState.init (qs.ket b₀)) with hψ
    have hIH : ψ r₀ = closedBranch a N m data b₀ k (readoutOfRecord r₀) := ih (by omega) r₀ hr₀
    have hin : InRange c data N (ψ r₀) := by
      rw [hIH]; exact inRange_closedBranch a N m data c b₀ hN hNdata hc hc0 k _
    obtain ⟨h1, h2, h3⟩ := round_hyps_of_inRange (a ^ 2 ^ (m - 1 - k) % N) N data c hN hNdata
      (coprime_pow_mod a N ha _) hc _ hin
    rw [readoutRounds_succ_eval]
    rw [round_branch c (schedule a N m data c k) k ψ r₀ b h1 h2 h3]
    rw [hIH, ffAngle_eq_neg_readout_div k r₀ hr₀, readoutOfRecord_append, hr₀]
    set v := readoutOfRecord r₀
    set E := outcomeSign b * Complex.exp (((Angle.toReal (-((v : ℚ) / 2 ^ k)) : ℝ) : ℂ) * I)
    -- the uncontrolled action on the closed form
    have hT : uncontrolledAction c (schedule a N m data c k) (closedBranch a N m data b₀ k v)
        = (1 / 2 ^ k : ℂ) • ∑ κ ∈ Finset.range (2 ^ k), ph k v κ •
            qs.ket (RegEncoding.writeNat data (a ^ (2 ^ (m - (k + 1)) * (2 * κ + 1)) % N) b₀) := by
      rw [uncontrolledAction_eq_linear, closedBranch, map_smul, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro κ _
      rw [map_smul, ← uncontrolledAction_eq_linear,
        uncontrolledAction_schedule_ket a N m data c b₀ hN hNdata ha hc hc0 k (by omega) κ]
    have hB : closedBranch a N m data b₀ k v
        = (1 / 2 ^ k : ℂ) • ∑ κ ∈ Finset.range (2 ^ k), ph k v κ •
            qs.ket (RegEncoding.writeNat data (a ^ (2 ^ (m - (k + 1)) * (2 * κ)) % N) b₀) := by
      unfold closedBranch
      congr 1
      apply Finset.sum_congr rfl
      intro κ _
      congr 4
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show k < m by omega)
      rw [show k + d + 1 - k = d + 1 by omega, show k + d + 1 - (k + 1) = d by omega, pow_succ]
      ring
    rw [hT, hB]
    unfold closedBranch
    rw [show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k by ring, sum_range_two_mul]
    simp only [ph_succ_even, ph_succ_odd, Finset.sum_add_distrib]
    rw [show ∀ g : ℕ → qs.State, ∑ κ ∈ Finset.range (2 ^ k), (ph k v κ * E) • g κ
        = E • ∑ κ ∈ Finset.range (2 ^ k), ph k v κ • g κ from fun g => by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun κ _ => by rw [mul_comm, mul_smul]]
    rw [show (1 / 2 ^ (k + 1) : ℂ) = 1 / 2 * (1 / 2 ^ k) by ring]
    module

end ClosedForm

end Readout
end Shor
