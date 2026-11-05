import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Support.Language

/-!
# PhaseTripleProduct: the table contract and the banded policy, with their lemmas

`Statement.lean` defines the table (`PTPTable`), its Boolean contract (`PTPTable.contract`), the
width scan (`childWidth3`) and the banded policy (`PTPPolicy`, `check`, `choose`). This file proves
what the rest of the development needs of them.

## Table contract (`PTPTable.contract`)

The PTP point count is `3 k - 2 = 3 (k - 1) + 1` (`pointCount_eq`): three limb polynomials of
degree `≤ k - 1` multiply to a polynomial of degree `≤ 3 (k - 1)`, which `3 (k - 1) + 1` distinct
projective points determine. `contract_iff` unfolds the Boolean contract into its parts: the point
list is valid (`ValidPTPPoints`: right length, pairwise distinct after normalisation, each a point
the benchmark admits) and the program passes the three checks of `CheckedProg` (consumption,
safety, round trip). `contract_iff_framework` restates it in the Framework's own language:
`ProgConsumesPtsSafe` and `run? ops start = some start`.

## Banded policy (`PTPPolicy`)

Bands widest first, strictly decreasing thresholds; at width `n` the first band with
`threshold ≤ n` is used (ForShor's `choose`), and the node recurses at `childWidth n T.ops` when
that is `< n`, else takes the 3-way grid leaf. `choose_mem`, `check_tables` and `check_sorted`
are the facts about `choose` and `check` that every later proof starts from. The scan-board
ladder (`chainFuel`, `ladderFuel`) is defined here because only reports and proofs use it.
-/

namespace Shor
namespace PTP

open Operations

/-! ## Table contract -/




theorem pointCount_eq (k : Nat) (hk : 0 < k) : pointCount k = 3 * (k - 1) + 1 := by
  unfold pointCount; omega

/-- What the contract asks of the point list: `3k - 2` points, pairwise distinct after
normalisation (so projectively distinct), each one the benchmark admits. -/
def ValidPTPPoints (k : ℕ) (pts : List Point) : Prop :=
  pts.length = pointCount k ∧
    (pts.map normalizePoint).Nodup ∧
    pts.all validPoint? = true

namespace PTPTable



/-- `contract` is exactly: `k ≥ 2`, valid points, and a program that passes the Boolean checks. -/
theorem contract_iff (T : PTPTable) :
    T.contract = true ↔
      ∃ hk : 2 ≤ T.k, ValidPTPPoints T.k T.pts ∧
        CheckedProg (positive_of_ge_two hk) State.start_state T.ops T.pts := by
  unfold contract
  split
  · rename_i hk
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨⟨⟨⟨hl, hn⟩, ha⟩, hc⟩, hs⟩, hr⟩
      exact ⟨hk, ⟨hl, hn, ha⟩, ⟨hc, hs, hr⟩⟩
    · rintro ⟨_, ⟨hl, hn, ha⟩, ⟨hc, hs, hr⟩⟩
      exact ⟨⟨⟨⟨⟨hl, hn⟩, ha⟩, hc⟩, hs⟩, hr⟩
  · rename_i hk
    simp [hk]

/-- The contract in the Framework's language: the consumption and safety conditions
(`ProgConsumesPtsSafe`) and the round trip `run? ops start = some start`. -/
theorem contract_iff_framework (T : PTPTable) :
    T.contract = true ↔
      ∃ hk : 2 ≤ T.k, ValidPTPPoints T.k T.pts ∧
        ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state T.ops T.pts ∧
        run? T.ops State.start_state = some State.start_state := by
  rw [contract_iff]
  refine exists_congr fun hk => and_congr_right fun _ => ?_
  exact checkedProg_iff_framework _ _ _ _

end PTPTable

theorem limbWidth_eq (n k : Nat) : limbWidth n k = n / k := by
  simp [limbWidth, limbWidth3]

/-! ## Banded PTP policy -/



namespace PTPPolicy


theorem choose_mem {P : PTPPolicy} {n : Nat} {T : PTPTable} (h : P.choose n = some T) :
    ∃ b ∈ P.bands, b.table = T := by
  unfold choose at h
  rcases hb : P.bands.find? (fun b => decide (b.threshold ≤ n)) with _ | b
  · rw [hb] at h; cases h
  · rw [hb] at h
    exact ⟨b, List.mem_of_find?_eq_some hb, by simpa using h⟩


theorem check_tables {P : PTPPolicy} (h : P.check = true) :
    ∀ b ∈ P.bands, b.table.contract = true := by
  unfold check at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

theorem check_sorted {P : PTPPolicy} (h : P.check = true) :
    (P.bands.map PTPBand.threshold).IsChain (· > ·) := by
  unfold check at h
  simp only [Bool.and_eq_true] at h
  exact (sortedDesc_iff _).mp h.1

/-- Fuelled walk: every table selected from `n` strictly shrinks the width. -/
def chainFuel (P : PTPPolicy) : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, n =>
      match P.choose n with
      | none => true
      | some T => decide (childWidth n T.ops < n) && chainFuel P f (childWidth n T.ops)

def chainContracts (P : PTPPolicy) (n : Nat) : Bool := chainFuel P (n + 1) n

def ladderFuel (P : PTPPolicy) : Nat → Nat → List (Nat × Option Nat)
  | 0, n => [(n, none)]
  | f + 1, n =>
      match P.choose n with
      | none => [(n, none)]
      | some T =>
          if childWidth n T.ops < n then (n, some T.k) :: ladderFuel P f (childWidth n T.ops)
          else [(n, none)]

/-- Widths and table sizes visited from `n` (reports). -/
def ladder (P : PTPPolicy) (n : Nat) : List (Nat × Option Nat) := ladderFuel P (n + 1) n

end PTPPolicy

end PTP
end Shor
