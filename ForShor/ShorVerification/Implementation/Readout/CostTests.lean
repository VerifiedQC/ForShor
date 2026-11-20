import ForShor.ShorVerification.Implementation.Readout.Cost

/-!
# Readout: tests of the exact counts

The skeleton `readoutRounds (fun _ => Gate.id) c m` at `m = 0, 1, 2`, computed from
the definitions (not from `readout_counts`): one round has two Hadamards, one
measurement and one feed-forward phase, which is trivial (`ffAngle 0 = 0`); the
second round's phase is the first nontrivial one.
-/

namespace Shor
namespace Readout

/-- No rounds: nothing. -/
theorem readout_counts_zero (c : ℕ) :
    (readoutRounds (fun _ => Gate.id) c 0).counts = ⟨0, 0, 0, 0⟩ := by
  rfl

/-- One round: two `H`, one measurement, one feed-forward phase, none nontrivial. -/
theorem readout_counts_m1 (c : ℕ) :
    (readoutRounds (fun _ => Gate.id) c 1).counts = ⟨2, 1, 1, 0⟩ := by
  rfl

/-- Two rounds: four `H`, two measurements, two feed-forward phases, one nontrivial. -/
theorem readout_counts_m2 (c : ℕ) :
    (readoutRounds (fun _ => Gate.id) c 2).counts = ⟨4, 2, 2, 1⟩ := by
  rfl

/-- A multiplier with one written `H` adds one `H` per round and nothing else. -/
theorem readout_counts_H_multiplier (c q : ℕ) :
    (readoutRounds (fun _ => Gate.H q) c 2).counts = ⟨6, 2, 2, 1⟩ := by
  rfl

end Readout
end Shor
