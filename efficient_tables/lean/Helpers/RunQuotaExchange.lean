import Mathlib.Data.Int.Basic

/- Narrow integer lemmas only; see FORMAL_PREREG.2026-10-15T201400.md. -/
namespace Paper.RunQuota

def shortDelta (top height : ℤ) : ℤ :=
  if height > top then 0 else
  if height = top then 1 else
  if height = top - 1 then 0 else -1

theorem earlier_short_exchange (low high height : ℤ)
    (htops : low ≤ high) (hbelow : height < high) :
    shortDelta high height ≤ shortDelta low height := by
  unfold shortDelta
  split_ifs <;> omega

def runDelta (bottom top height : ℤ) : ℤ :=
  if height > top then 0 else
  if height = top then 1 else
  if bottom < height then height - top + 1 else 2 - (top - bottom)

theorem compaction_lower_tails (bottom top height : ℤ)
    (hlength : 2 ≤ top - bottom) (hbelow : height < top) :
    runDelta bottom top height ≤ 0 := by
  unfold runDelta
  split_ifs <;> omega

theorem forced_one_ordinary (group compact slack : ℤ)
    (hsaturated : slack = group - 1)
    (htop : compact ≤ slack)
    (hbelow : 2 * group - compact ≤ slack + 2) :
    compact = group - 1 := by omega

theorem forbidden_compact_bottom (group ordinaryLength oldTail capHeight : ℤ)
    (hsaturated : capHeight = oldTail + group - 1 + ordinaryLength)
    (htail : oldTail + ordinaryLength + (group - 1) + 1 ≤ capHeight) : False := by
  omega

theorem duplicate_carry_capacity (oldHigher cap height : ℤ)
    (hcapacity : oldHigher + 2 ≤ cap - height) :
    oldHigher + 1 ≤ cap - (height + 1) := by omega

theorem combine_endpoint_caps (height0 heightR cap0 capR : ℤ) :
    (height0 ≤ cap0 ∧ heightR ≤ capR) ↔
    max height0 (heightR + cap0 - capR) ≤ cap0 := by omega

end Paper.RunQuota
