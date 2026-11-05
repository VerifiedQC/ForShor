import Mathlib.Data.Int.Basic

/- Narrow integer lemmas only. Definitions are inlined for the trusted adapter. -/
namespace Paper.RunQuotaRepair

theorem earlier_short_exchange (low high height : ℤ)
    (htops : low ≤ high) (hbelow : height < high) :
    (if height > high then (0 : ℤ) else
     if height = high then 1 else if height = high - 1 then 0 else -1) ≤
    (if height > low then (0 : ℤ) else
     if height = low then 1 else if height = low - 1 then 0 else -1) := by
  split_ifs <;> omega

theorem compaction_lower_tails (bottom top height : ℤ)
    (hlength : 2 ≤ top - bottom) (hbelow : height < top) :
    (if height > top then (0 : ℤ) else if height = top then 1 else
     if bottom < height then height - top + 1 else 2 - (top - bottom)) ≤ 0 := by
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

end Paper.RunQuotaRepair
