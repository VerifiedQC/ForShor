import ForShor.ShorVerification.Implementation.Readout.Proofs.LocalityIdeal
import ForShor.ShorVerification.Implementation.Readout.Locality

/-!
# Readout: the ideal semiclassical circuit inside the general locality theory

`semiclassicalIdeal a N m data c` (rounds of `H c ;; idealCtrlModMul (a^(2^(m-1-j)) mod N) N
data c ;; ffPhase c j ;; H c ;; measureReset c`) is an `MGate.IdealSafe` program on the domain
`IdealDom qs N data` (span of the kets with data value `< N`) for every qubit `q ∉ data`,
`q ≠ c`, and it keeps that domain (`MGate.KeepsDom`). Hypotheses throughout (those of the ideal
multiplier's ket law): `1 < N ≤ 2^|data|`, `a` coprime to `N`, `c ∉ data`.

* `semiclassicalIdeal_keepsDom`, `semiclassicalIdeal_idealSafe`, `semiclassicalIdeal_spectatorOn`.
* For ANY start state `ψ₀ ∈ IdealDom qs N data` (no condition on the control, no condition on the
  data value beyond `< N`, any FINITE linear combination of such kets: `IdealDom` is the
  algebraic span):
  - `semiclassicalIdeal_branch_X_dom`: every branch from `X q ψ₀` is `X q` of the branch from
    `ψ₀`;
  - `semiclassicalIdeal_recordProb_init_X_dom`: the same record distribution;
  - `semiclassicalIdeal_recordProb_decomp_dom`: decomposition along `q`;
  - `semiclassicalIdeal_recordProb_init_X_inRange`: the `InRange` start states of
    `Proofs/Deferred.lean` are covered.
* Ket forms, `toNat data b < N`: `semiclassicalIdeal_recordProb_flipBits_dom` (finitely many
  flips of qubits outside `data ∪ {c}`), `semiclassicalIdeal_recordProb_of_agree_dom` (a ket
  agreeing with `b` on `data` and `c`, finitely many differences),
  `semiclassicalIdeal_recordProb_superpose_dom` (one such qubit in any superposition `α|0⟩ + β|1⟩`).

Flipping the control `c` or a data qubit in the start state is NOT covered (and changes the
record distribution in general). The flip/agreement forms take finite lists / need `hfin`
(finitely many differing qubits): harmless for physical kets, a restriction of the abstract
basis only.

## Relation to T1

T1 (`semiclassicalIdeal_recordProb_flipBit`, closed form) needs data `= 1` and `c = 0` in the
start ket. The new theorems need only data `< N` (the closed form is not used at all), so they
imply T1: `semiclassicalIdeal_recordProb_flipBit_of_dom` re-proves T1's exact statement from
`semiclassicalIdeal_recordProb_flipBits_dom` (`1 < N` makes data `= 1` in range; the hypothesis
`c = 0` is not used). The converse fails in scope: T1 says nothing for data `≠ 1`, `c = 1`, or
superposed start states.

NOT covered: start states outside `IdealDom` (e.g. a ket with data `≥ N`, on which the classes do
not determine the ideal multiplier); qubits of `data` or `c` itself.
-/

namespace Shor
namespace Readout

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

section Structure
variable {a N m : ℕ} {data : Reg} {c : ℕ}

/-- Readout rounds keep `IdealDom N data` if every multiplier does and `c ∉ data`. -/
theorem readoutRounds_keepsDom {U : ℕ → Gate} (hU : ∀ j, (U j).KeepsDom N data)
    (hc : c ∉ data.qubits) : ∀ k, (readoutRounds U c k).KeepsDom N data := by
  intro k
  induction k with
  | zero => exact .unitary _ .id
  | succ k ih =>
    exact .seq _ _ ih (.seq _ _ (.unitary _ (.H c hc)) (.seq _ _ (.unitary _ (hU k))
      (.seq _ _ (.ffPhase c k) (.seq _ _ (.unitary _ (.H c hc)) (.measureReset c hc)))))

/-- Readout rounds are `IdealSafe` on `IdealDom N data` if every multiplier is, every multiplier
keeps the domain, `c ∉ data` and `q ≠ c`. -/
theorem readoutRounds_idealSafe {U : ℕ → Gate} {q : ℕ}
    (hUs : ∀ j, (U j).IdealSafe qs (IdealDom qs N data) q) (hUk : ∀ j, (U j).KeepsDom N data)
    (hc : c ∉ data.qubits) (hqc : q ≠ c) :
    ∀ k, (readoutRounds U c k).IdealSafe qs (IdealDom qs N data) q := by
  have hH : (MGate.unitary (Gate.H c)).IdealSafe qs (IdealDom qs N data) q :=
    .local_ _ trivial (by simpa [MGate.exactSupport, Gate.exactSupport] using hqc)
  have hHk : (MGate.unitary (Gate.H c)).KeepsDom N data := .unitary _ (.H c hc)
  have hTail : ∀ j, (MGate.seq (.ffPhase c j) (.seq (.unitary (Gate.H c)) (.measureReset c))).IdealSafe
      qs (IdealDom qs N data) q := fun _ =>
    .local_ _ ⟨trivial, trivial, trivial⟩
      (by simpa [MGate.exactSupport, Gate.exactSupport] using hqc)
  intro k
  induction k with
  | zero => exact .local_ _ trivial (by simp [readoutRounds, MGate.exactSupport, Gate.exactSupport])
  | succ k ih =>
    refine .seq _ _ ih (.seq _ _ hH (.seq _ _ (.unitary _ (hUs k)) (hTail k)
      (MGate.KeepsDom.preserves (.unitary _ (hUk k)))) hHk.preserves) ?_
    exact (readoutRounds_keepsDom hUk hc k).preserves

/-- **The ideal readout keeps its domain**, structurally. -/
theorem semiclassicalIdeal_keepsDom (hN : 1 < N) (hNdata : N ≤ ASize data)
    (ha : Nat.Coprime a N) (hc : c ∉ data.qubits) :
    (semiclassicalIdeal a N m data c).KeepsDom N data :=
  readoutRounds_keepsDom (fun _ => .ideal _ c hN hNdata (coprime_pow_mod a N ha _) hc) hc m

/-- **The ideal readout is `IdealSafe` on its domain** for every `q ∉ data`, `q ≠ c`. -/
theorem semiclassicalIdeal_idealSafe (hN : 1 < N) (hNdata : N ≤ ASize data)
    (ha : Nat.Coprime a N) (hc : c ∉ data.qubits) {q : ℕ} (hqd : q ∉ data.qubits) (hqc : q ≠ c) :
    (semiclassicalIdeal a N m data c).IdealSafe qs (IdealDom qs N data) q :=
  readoutRounds_idealSafe
    (fun _ => .ideal _ N data c hN hNdata (coprime_pow_mod a N ha _) hc hqd hqc le_rfl)
    (fun _ => .ideal _ c hN hNdata (coprime_pow_mod a N ha _) hc) hc hqc m

end Structure

/-- **`q` is a spectator of the ideal readout on its domain.** -/
theorem semiclassicalIdeal_spectatorOn (a N m : ℕ) (data : Reg) (c : ℕ) (hN : 1 < N)
    (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits) {q : ℕ}
    (hqd : q ∉ data.qubits) (hqc : q ≠ c) :
    (semiclassicalIdeal a N m data c).SpectatorOn q (IdealDom qs N data) :=
  MGate.spectatorOn_of_idealSafe (semiclassicalIdeal_idealSafe hN hNdata ha hc hqd hqc)

/-- **Branch level, any start state in the domain.** -/
theorem semiclassicalIdeal_branch_X_dom (a N m : ℕ) (data : Reg) (c : ℕ) (hN : 1 < N)
    (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits) {q : ℕ}
    (hqd : q ∉ data.qubits) (hqc : q ≠ c) {ψ₀ : qs.State} (hψ : ψ₀ ∈ IdealDom qs N data)
    (r : Record) :
    (semiclassicalIdeal a N m data c).eval (MState.init (qs.eval (Gate.X q) ψ₀)) r
      = qs.eval (Gate.X q) ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀) r) :=
  (semiclassicalIdeal_spectatorOn a N m data c hN hNdata ha hc hqd hqc).eval_init_X hψ r

/-- **Record distribution, any start state in the domain.** -/
theorem semiclassicalIdeal_recordProb_init_X_dom (a N m : ℕ) (data : Reg) (c : ℕ) (hN : 1 < N)
    (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits) {q : ℕ}
    (hqd : q ∉ data.qubits) (hqc : q ≠ c) {ψ₀ : qs.State} (hψ : ψ₀ ∈ IdealDom qs N data)
    (r : Record) :
    recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.eval (Gate.X q) ψ₀))) r
      = recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r :=
  (semiclassicalIdeal_spectatorOn a N m data c hN hNdata ha hc hqd hqc).recordProb_init_X hψ r

/-- **`InRange` start states** (control `0`, data `< N`) are covered. -/
theorem semiclassicalIdeal_recordProb_init_X_inRange (a N m : ℕ) (data : Reg) (c : ℕ)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits) {q : ℕ}
    (hqd : q ∉ data.qubits) (hqc : q ≠ c) {ψ₀ : qs.State} (hψ : InRange c data N ψ₀)
    (r : Record) :
    recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.eval (Gate.X q) ψ₀))) r
      = recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r :=
  semiclassicalIdeal_recordProb_init_X_dom a N m data c hN hNdata ha hc hqd hqc
    (inRange_mem_idealDom hψ) r

/-- **Decomposition along `q`, any start state in the domain.** -/
theorem semiclassicalIdeal_recordProb_decomp_dom (a N m : ℕ) (data : Reg) (c : ℕ) (hN : 1 < N)
    (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits) {q : ℕ}
    (hqd : q ∉ data.qubits) (hqc : q ≠ c) {ψ₀ : qs.State} (hψ : ψ₀ ∈ IdealDom qs N data)
    (r : Record) :
    recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((semiclassicalIdeal a N m data c).eval
          (MState.init (MeasureClass.measProj (qubitReg q) o ψ₀))) r :=
  (semiclassicalIdeal_spectatorOn a N m data c hN hNdata ha hc hqd hqc).recordProb_decomp hψ r

/-- **Finitely many flips, any ket with data `< N`.** -/
theorem semiclassicalIdeal_recordProb_flipBits_dom (a N m : ℕ) (data : Reg) (c : ℕ) (hN : 1 < N)
    (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits) (b : qs.Basis)
    (hb : RegEncoding.toNat data b < N) (l : List ℕ) (hl : ∀ q ∈ l, q ∉ data.qubits ∧ q ≠ c)
    (r : Record) :
    recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket (flipBits l b)))) r
      = recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b))) r :=
  MGate.recordProb_flipBits_on _ l
    (fun q hq => semiclassicalIdeal_spectatorOn a N m data c hN hNdata ha hc (hl q hq).1 (hl q hq).2)
    (fun q hq x hx => by rw [← eval_X_ket_flipBit]; exact idealDom_X (hl q hq).1 hx)
    b (ket_mem_idealDom hb) r

/-- **Agreement form, any ket with data `< N`.** `b'` agrees with `b` on `data` and on `c` and
differs at finitely many qubits. -/
theorem semiclassicalIdeal_recordProb_of_agree_dom (a N m : ℕ) (data : Reg) (c : ℕ) (hN : 1 < N)
    (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits) (b b' : qs.Basis)
    (hb : RegEncoding.toNat data b < N)
    (hagree : ∀ p, p ∈ data.qubits ∨ p = c → RegEncoding.bit p b' = RegEncoding.bit p b)
    (hfin : {p | RegEncoding.bit p b' ≠ RegEncoding.bit p b}.Finite) (r : Record) :
    recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b'))) r
      = recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b))) r := by
  have hne : ∀ q, RegEncoding.bit q b' ≠ RegEncoding.bit q b → q ∉ data.qubits ∧ q ≠ c :=
    fun q hq => ⟨fun h => hq (hagree q (Or.inl h)), fun h => hq (hagree q (Or.inr h))⟩
  exact MGate.recordProb_of_agree_on _ b b' (ket_mem_idealDom hb)
    (fun q hq => semiclassicalIdeal_spectatorOn a N m data c hN hNdata ha hc (hne q hq).1
      (hne q hq).2)
    (fun q hq x hx => by rw [← eval_X_ket_flipBit]; exact idealDom_X (hne q hq).1 hx) hfin r

/-- **Superposed spectator, any ket with data `< N`.** -/
theorem semiclassicalIdeal_recordProb_superpose_dom (a N m : ℕ) (data : Reg) (c : ℕ) (hN : 1 < N)
    (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits) (b : qs.Basis)
    (hb : RegEncoding.toNat data b < N) {q : ℕ} (hqd : q ∉ data.qubits) (hqc : q ≠ c)
    (α β : ℂ) (r : Record) :
    recordProb ((semiclassicalIdeal a N m data c).eval
        (MState.init (α • qs.ket b + β • qs.ket (flipBit q b)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2)
        * recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b))) r :=
  (semiclassicalIdeal_spectatorOn a N m data c hN hNdata ha hc hqd hqc).recordProb_superpose
    (ket_mem_idealDom hb) (ket_mem_idealDom (by rwa [toNat_flipBit hqd])) α β r

/-- **`T1 ⇐ new`.** The exact statement of T1 (`semiclassicalIdeal_recordProb_flipBit`: data `= 1`,
`c = 0`), derived from the domain theorem without the closed form. The hypothesis `hc0` is not
needed (kept to match T1's statement). -/
theorem semiclassicalIdeal_recordProb_flipBit_of_dom (a N m : ℕ) (data : Reg) (c : ℕ)
    (b₀ : qs.Basis) (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N)
    (hc : c ∉ data.qubits) (hdata1 : RegEncoding.toNat data b₀ = 1)
    (_hc0 : RegEncoding.bit c b₀ = false) {q : ℕ} (hqd : q ∉ data.qubits) (hqc : q ≠ c)
    (r : Record) :
    recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket (flipBit q b₀)))) r
      = recordProb ((semiclassicalIdeal a N m data c).eval (MState.init (qs.ket b₀))) r :=
  semiclassicalIdeal_recordProb_flipBits_dom a N m data c hN hNdata ha hc b₀ (by omega) [q]
    (fun q' h => by simp only [List.mem_singleton] at h; subst h; exact ⟨hqd, hqc⟩) r

omit [LowerGateClass qs] [MeasureClass qs] in
/-- **The ideal node acts non-trivially on the domain** (non-degeneracy of the A2 witnesses). On a
ket with data `N - 1` and control `1`, the node by a multiplier `c` with `c mod N ≠ 1` writes the
data value `c (N - 1) mod N`, which differs from `N - 1`: the basis state is moved. -/
theorem idealCtrlModMul_moves_top (c N : ℕ) (data : Reg) (ctrl : ℕ) (b : qs.Basis) (hN : 1 < N)
    (hNdata : N ≤ ASize data) (hcop : Nat.Coprime c N) (hctrl : ctrl ∉ data.qubits)
    (hb : RegEncoding.toNat data b = N - 1) (hcb : RegEncoding.bit ctrl b = true)
    (hc1 : c % N ≠ 1) :
    qs.eval (Gate.idealCtrlModMul c N data ctrl) (qs.ket b)
        = qs.ket (RegEncoding.writeNat data (c * (N - 1) % N) b) ∧
      RegEncoding.toNat data (RegEncoding.writeNat data (c * (N - 1) % N) b)
        ≠ RegEncoding.toNat data b := by
  refine ⟨?_, ?_⟩
  · rw [IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_ket_exact c N data ctrl b hN hNdata
      hcop hctrl (by omega), hcb, hb]
    rfl
  · have hlt : c * (N - 1) % N < N := Nat.mod_lt _ (by omega)
    rw [RegEncoding.toNat_writeNat_of_lt _ _ _ (lt_of_lt_of_le hlt hNdata), hb]
    intro h
    apply hc1
    have e : c * (N - 1) + c = c * N := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h0 : c * (N - 1) + c ≡ (N - 1) + 1 [MOD N] := by
      rw [e, show N - 1 + 1 = N by omega]
      simp [Nat.ModEq]
    have h2 : c * (N - 1) ≡ N - 1 [MOD N] := by
      unfold Nat.ModEq; rw [h, Nat.mod_eq_of_lt (by omega)]
    have := Nat.ModEq.add_left_cancel h2 h0
    unfold Nat.ModEq at this
    rw [this, Nat.mod_eq_of_lt hN]

end Readout
end Shor
