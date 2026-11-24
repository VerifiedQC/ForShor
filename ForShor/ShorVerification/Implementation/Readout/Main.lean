import ForShor.ShorVerification.Implementation.Readout.Statement
import ForShor.ShorVerification.Implementation.Readout.Proofs.Branch
import ForShor.ShorVerification.Implementation.Readout.Proofs.Coherent

/-!
# Readout: the semiclassical readout equals the inverse-QFT readout

Main result, `semiclassical_eq_iqft` (ideal gates): for every integer `o`, the
probability that the semiclassical readout `semiclassicalIdeal a N m data c`
(one recycled control qubit `c`, `m = |x|` rounds, multipliers
`a^(2^(m-1)), …, a^2, a` in this order, feed-forward phases `ffAngle`) produces
a record of length `m` whose little-endian reading `readoutOfRecord` is `o`
EQUALS the probability of outcome `o` when the exponent register `x` is
measured after the coherent readout `H_reg x ;; modExpIdeal' a N x data ;; IQFT x`.
Both circuits start from the same basis ket `|b₀⟩`: exponent register `x = 0`,
data register `= 1`, control `c = 0`.

The record-level form `semiclassical_recordProb_eq` says more: each single
record `r` of length `m` has exactly the coherent probability of the outcome
`readoutOfRecord r` (distinct records of length `m` read distinct integers).

Proof: the closed form of every branch (`Proofs/Branch.lean`, induction over
rounds with `round_branch`), the exact coherent state projected on `x = o`
(`Proofs/Coherent.lean`, from the existing ideal order-finding lemmas), and the
fact that both are the same combination of orthonormal kets up to relabelling
(`norm_sum_smul_ket_map`).

What pins the phase convention: the starting ket is real, so the outcome
DISTRIBUTION is unchanged if every phase is conjugated (a feed-forward phase of
the opposite sign, or `QFT` in place of `IQFT`, gives the same probabilities).
`semiclassical_eq_iqft` therefore does not by itself pin the sign of `ffAngle`
or the orientation of the Fourier transform. Nor is it proved in Lean that the
distribution theorem alone pins the multiplier order and the endianness of
`readoutOfRecord` for `m ≥ 2`; beyond the concrete `m = 1, 2` cases of `Readout/Tests.lean`,
that check is numeric (the benchmark repository's tests), not a Lean theorem. What Lean does
prove is the state-level statement: `semiclassical_branch_state` gives the semiclassical branch at a
record reading `o` as the explicit vector
`(1/2^m) ∑_{κ < 2^m} exp(-2πi o κ / 2^m) |b₀ with data := a^κ mod N⟩`, and
`coherent_projected_state` gives the coherent state projected on `x = o` as the
SAME vector with `x := o` written into every ket. The coefficient
`exp(-2πi o κ / 2^m)`, sign included, is part of both claims. On a record of
length `j`, `ffAngle j rec = -(readoutOfRecord rec) / 2^j`
(`ffAngle_eq_neg_readout_div`).
-/

namespace Shor

open MeasureClass

/-- `readoutOfRecord` reads slot `i` of the record as bit `i` (little-endian;
missing slots read `0`). This is the bit order `RegEncoding.toNat` gives an
outcome `o` of `probMeas`, so a record and the outcome it is compared with have
the same bits. -/
theorem readoutOfRecord_testBit (rec : Record) (i : ℕ) :
    (readoutOfRecord rec).testBit i = rec.getD i false :=
  Readout.readoutOfRecord_testBit rec i

/-- The feed-forward angle of round `j`, read on a record of length `j`, is
`-(readoutOfRecord rec) / 2^j` (units of `π`). -/
theorem ffAngle_eq_neg_readout_div (j : ℕ) (rec : Record) (h : rec.length = j) :
    ffAngle j rec = -((readoutOfRecord rec : ℚ) / 2 ^ j) :=
  Readout.ffAngle_eq_neg_readout_div j rec h

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  [LowerGateClass qs] [MeasureClass qs]

/-- **State level, semiclassical side.** Same hypotheses as
`semiclassical_eq_iqft`; `m = regSize x.active`. For every record `r` with `m`
entries, reading `o = readoutOfRecord r`, the (unnormalised) branch of the
semiclassical readout at `r` is exactly

  `(1/2^m) ∑_{κ < 2^m} exp(-2πi o κ / 2^m) |b₀ with data := a^κ mod N⟩`

(the control `c` is back at `0`, every other qubit as in `b₀`). Compare
`coherent_projected_state`: the same coefficients, with `x := o` written into
each ket. -/
theorem semiclassical_branch_state
    (a N : ℕ) (x : ExtReg) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N)
    (hc : c ∉ data.qubits)
    (hdata1 : RegEncoding.toNat data b₀ = 1)
    (hc0 : RegEncoding.bit c b₀ = false) (r : Record) (hr : r.length = regSize x.active) :
    (semiclassicalIdeal a N (regSize x.active) data c).eval (MState.init (qs.ket b₀)) r
      = (1 / 2 ^ regSize x.active : ℂ) • ∑ κ ∈ Finset.range (2 ^ regSize x.active),
          Complex.exp (-(2 * Real.pi * Complex.I * ((readoutOfRecord r : ℂ) * κ)
            / 2 ^ regSize x.active)) •
          qs.ket (RegEncoding.writeNat data (a ^ κ % N) b₀) := by
  rw [Readout.semiclassicalIdeal_eq,
    Readout.branch_closed_form a N _ data c b₀ hN hNdata ha hc hdata1 hc0 _ le_rfl r hr,
    Readout.closedBranch]
  simp only [Nat.sub_self, pow_zero, one_mul, Readout.ph]

omit [LowerGateClass qs] in
/-- **State level, coherent side.** Same register and ket hypotheses as
`semiclassical_eq_iqft` (the control `c` plays no role); `m = regSize x.active`.
For every `o < 2^m`, the state after `H_reg x ;; modExpIdeal' a N x data ;;
IQFT x` projected onto exponent outcome `o` is exactly

  `(1/2^m) ∑_{κ < 2^m} exp(-2πi o κ / 2^m) |b₀ with data := a^κ mod N, then x := o⟩`,

i.e. the vector of `semiclassical_branch_state` (for a record reading `o`)
with `x := o` written into every ket, coefficients identical. -/
theorem coherent_projected_state
    (a N : ℕ) (x : ExtReg) (data : Reg) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N)
    (hxdata : Disjoint x.active data)
    (hx0 : RegEncoding.toNat x.active b₀ = 0) (hdata1 : RegEncoding.toNat data b₀ = 1)
    (o : ℕ) (ho : o < 2 ^ regSize x.active) :
    measProj x.active o
        (qs.eval (H_reg x.active ;; modExpIdeal' qs a N x.active data ;; IQFT x) (qs.ket b₀))
      = (1 / 2 ^ regSize x.active : ℂ) • ∑ κ ∈ Finset.range (2 ^ regSize x.active),
          Complex.exp (-(2 * Real.pi * Complex.I * ((o : ℂ) * κ) / 2 ^ regSize x.active)) •
          qs.ket (RegEncoding.writeNat x.active o (RegEncoding.writeNat data (a ^ κ % N) b₀)) := by
  rw [Readout.coherent_measProj a N x data b₀ hN hNdata ha hxdata hx0 hdata1 o ho]
  congr 1
  · rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp [ASize]
  · refine Finset.sum_congr rfl fun κ _ => ?_
    rw [show ASize x.active = 2 ^ regSize x.active from rfl, ← Readout.ph_eq_star_qftPhase]
    rfl

/-- **Record by record.** Hypotheses: `1 < N ≤ 2^|data|`, `a` coprime to `N`,
the control `c` outside `data`, the exponent register `x` disjoint from `data`,
and the initial basis ket `|b₀⟩` has `x = 0`, `data = 1`, `c = 0`. Then for
every record `r` with `m = |x|` entries, the probability of `r` in the
semiclassical readout equals the probability of reading `o = readoutOfRecord r`
from `x` after the coherent readout. (A consequence of the state-level
`semiclassical_branch_state` and `coherent_projected_state`; this proof goes
through the same internal closed forms.) -/
theorem semiclassical_recordProb_eq
    (a N : ℕ) (x : ExtReg) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N)
    (hc : c ∉ data.qubits) (hxdata : Disjoint x.active data)
    (hx0 : RegEncoding.toNat x.active b₀ = 0) (hdata1 : RegEncoding.toNat data b₀ = 1)
    (hc0 : RegEncoding.bit c b₀ = false) (r : Record) (hr : r.length = regSize x.active) :
    recordProb ((semiclassicalIdeal a N (regSize x.active) data c).eval
        (MState.init (qs.ket b₀))) r
      = probMeas x.active (readoutOfRecord r)
          (qs.eval (H_reg x.active ;; modExpIdeal' qs a N x.active data ;; IQFT x)
            (qs.ket b₀)) := by
  set m := regSize x.active with hm
  set o := readoutOfRecord r with hodef
  have ho : o < ASize x.active := by
    have := Readout.readoutOfRecord_lt r
    rwa [hr] at this
  rw [recordProb, probMeas, Readout.semiclassicalIdeal_eq,
    Readout.branch_closed_form a N m data c b₀ hN hNdata ha hc hdata1 hc0 m le_rfl r hr,
    Readout.coherent_measProj a N x data b₀ hN hNdata ha hxdata hx0 hdata1 o ho,
    Readout.closedBranch, norm_smul, norm_smul]
  congr 2
  · -- the scalars: `1/2^m = (1/√(2^m))²`
    rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp [ASize, hm]
  · -- the sums: same coefficients, kets relabelled by `writeNat x o`
    rw [Readout.norm_sum_smul_ket_map (Finset.range (ASize x.active))
      (fun t => star (qftPhase (ASize x.active) t o))
      (fun t => RegEncoding.writeNat data (a ^ t % N) b₀) (RegEncoding.writeNat x.active o)]
    · congr 1
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [Readout.ph_eq_star_qftPhase, Nat.sub_self, pow_zero, one_mul]
      rfl
    · intro i _ j _ hij
      have hread : ∀ t, RegEncoding.toNat data (RegEncoding.writeNat x.active o
          (RegEncoding.writeNat data (a ^ t % N) b₀)) = a ^ t % N := fun t => by
        rw [toNat_left_write_right data x.active (Disjoint.symm hxdata),
          RegEncoding.toNat_writeNat_of_lt _ _ _
            (lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hNdata)]
      have := congrArg (RegEncoding.toNat data) hij
      simp only [hread] at this
      simp only [this]

/-- **Semiclassical readout = inverse-QFT readout (ideal gates).**

Hypotheses: `1 < N ≤ 2^|data|` and `a` coprime to `N` (so every multiplier is
a permutation of the data values `< N`); the control qubit `c` is not in the
data register; the exponent register `x` is disjoint from the data register;
the common initial basis ket `|b₀⟩` has exponent register `x = 0`, data
register `= 1` and control `c = 0`. Let `m = regSize x.active` (the number of
exponent qubits) and run the semiclassical readout with `m` rounds.

Then for EVERY natural number `o`: the total probability of the records `r`
with `m` entries whose little-endian reading `readoutOfRecord r` is `o` equals
the probability `probMeas x.active o` of outcome `o` when the exponent register
is measured after the coherent readout `H_reg x ;; modExpIdeal' a N x data ;;
IQFT x`. (For `o < 2^m` exactly one record contributes; for `o ≥ 2^m` both
sides are `0`.)

This is a statement about distributions only: since `|b₀⟩` is real, it would
also hold with every phase conjugated, so it does not pin the sign of `ffAngle`
or `IQFT` versus `QFT`. The state-level `semiclassical_branch_state` and
`coherent_projected_state` do. -/
theorem semiclassical_eq_iqft
    (a N : ℕ) (x : ExtReg) (data : Reg) (c : ℕ) (b₀ : qs.Basis)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N)
    (hc : c ∉ data.qubits) (hxdata : Disjoint x.active data)
    (hx0 : RegEncoding.toNat x.active b₀ = 0) (hdata1 : RegEncoding.toNat data b₀ = 1)
    (hc0 : RegEncoding.bit c b₀ = false) (o : ℕ) :
    (∑' r : Record, if r.length = regSize x.active ∧ readoutOfRecord r = o then
        recordProb ((semiclassicalIdeal a N (regSize x.active) data c).eval
          (MState.init (qs.ket b₀))) r else 0)
      = probMeas x.active o
          (qs.eval (H_reg x.active ;; modExpIdeal' qs a N x.active data ;; IQFT x)
            (qs.ket b₀)) := by
  set m := regSize x.active with hm
  by_cases ho : o < 2 ^ m
  · obtain ⟨r₀, hl, hv⟩ := Readout.exists_record_of_lt m o ho
    rw [tsum_eq_single r₀]
    · simp only [hl, hv, and_self, ite_true]
      rw [semiclassical_recordProb_eq a N x data c b₀ hN hNdata ha hc hxdata
        hx0 hdata1 hc0 r₀ hl, hv]
    · intro r hne
      rw [ite_eq_right_iff]
      rintro ⟨hrl, hrv⟩
      exact absurd (Readout.readoutOfRecord_inj (hrl.trans hl.symm) (hrv.trans hv.symm)) hne
  · have hzero : ∀ r : Record, (if r.length = m ∧ readoutOfRecord r = o then
        recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b₀))) r
        else 0) = 0 := by
      intro r
      rw [ite_eq_right_iff]
      rintro ⟨hrl, hrv⟩
      have := Readout.readoutOfRecord_lt r
      rw [hrl, hrv] at this
      exact absurd this ho
    simp only [hzero, tsum_zero]
    rw [probMeas, MeasureClass.measProj_zero_outOfRange _ _ _ (not_lt.mp ho)]
    simp

/-- `semiclassical_eq_iqft` with the control's placement given by a
`SemiclassicalLayout` (the control outside the data, work, scratch registers
and the flag of the modular multiplication), the data register being the
active part of `y`. Only the field `c_not_mem_data` is used here; the other
layout fields are for the real (approximate) multiplier (`Shor.lean`). -/
theorem semiclassical_eq_iqft_of_layout
    (a N : ℕ) (x y work scratch : ExtReg) (flag c : ℕ) (b₀ : qs.Basis)
    (hlayout : SemiclassicalLayout c y work scratch flag)
    (hN : 1 < N) (hNdata : N ≤ ASize y.active) (ha : Nat.Coprime a N)
    (hxdata : Disjoint x.active y.active)
    (hx0 : RegEncoding.toNat x.active b₀ = 0) (hdata1 : RegEncoding.toNat y.active b₀ = 1)
    (hc0 : RegEncoding.bit c b₀ = false) (o : ℕ) :
    (∑' r : Record, if r.length = regSize x.active ∧ readoutOfRecord r = o then
        recordProb ((semiclassicalIdeal a N (regSize x.active) y.active c).eval
          (MState.init (qs.ket b₀))) r else 0)
      = probMeas x.active o
          (qs.eval (H_reg x.active ;; modExpIdeal' qs a N x.active y.active ;; IQFT x)
            (qs.ket b₀)) :=
  semiclassical_eq_iqft a N x y.active c b₀ hN hNdata ha
    (fun h => hlayout.c_not_mem_data (List.mem_append_left _ h)) hxdata hx0 hdata1 hc0 o

end Shor
