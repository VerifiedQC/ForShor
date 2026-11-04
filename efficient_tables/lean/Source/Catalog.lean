import Source.BestKnown
import Source.Model

/-!
# Catalog of PhaseProduct candidates

Defines the `Candidate` structure, a verified PhaseProduct program available to the recursive planner, with `key` and `analyze` (analysis at a balanced `n`-bit node). Provides `bestKnownCandidate` for one `k` and the list `bestKnownCandidates`.
-/

namespace TableGeneration.RecursiveCost

/-- One verified PhaseProduct program available to the recursive planner. -/
structure Candidate where
  policyId : String
  k : Nat
  hk : k >= 2
  program : Prog k

namespace Candidate

/-- Stable display key for a policy at one `k`. -/
def key (candidate : Candidate) : String :=
  candidate.policyId ++ ":k=" ++ toString candidate.k

/-- Analyze a candidate at a balanced `n`-bit PhaseProduct node. -/
def analyze (candidate : Candidate) (n : Nat) : ProgramAnalysis :=
  analyzeBalancedProgram n candidate.program

end Candidate

/-- Current promoted PhaseProduct program for one `k`. -/
def bestKnownCandidate (k : Nat) (hk : k >= 2) : Candidate where
  policyId := bestKnownPolicyId .PhaseProduct k
  k
  hk
  program := bestKnownGenerate .PhaseProduct k hk

/--
Initial standalone catalog. Promotion can regenerate this list when the
published policy catalog grows beyond one promoted program per `k`.
-/
def bestKnownCandidates : List Candidate :=
  [ bestKnownCandidate 2 (by decide)
  , bestKnownCandidate 3 (by decide)
  , bestKnownCandidate 4 (by decide)
  , bestKnownCandidate 5 (by decide)
  , bestKnownCandidate 6 (by decide)
  , bestKnownCandidate 7 (by decide)
  , bestKnownCandidate 8 (by decide)
  , bestKnownCandidate 9 (by decide)
  , bestKnownCandidate 10 (by decide)
  , bestKnownCandidate 11 (by decide)
  , bestKnownCandidate 12 (by decide)
  , bestKnownCandidate 13 (by decide)
  , bestKnownCandidate 14 (by decide)
  , bestKnownCandidate 15 (by decide)
  , bestKnownCandidate 16 (by decide) ]

end TableGeneration.RecursiveCost
