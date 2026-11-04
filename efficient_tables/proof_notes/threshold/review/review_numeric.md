# Numeric adversarial review of ENCODING_LEMMA.md

Code and raw outputs: wp2/test/ (lib.py, t1..t6.py, out_*.txt). All run with `python3 -I`, fixed seeds, exact integer/Fraction arithmetic. Independent zero/integrality oracle (carry propagation on a sparse signed-power multiset, no H, handles exponents ~1e12) used as ground truth.

## Result: no violation found for any claim tested. Ranges are limited; see each item.

### 1. Lemma 1 (t1.py, t6.py)
- Exact symbolic replayer: templates Q, P, R, negation, eps=+-1, random distinct source/destination rows (same row used as source and destination at different steps occurs freely). k=2,3,4; A (additions) up to 9 (8 for k=4), plus random negations.
- 9000 (skeleton, x) pairs (5892 with all prefixes integral, 3108 with integrality failing), 593,992 (prefix, entry) checks. Occurrence count <= 2^alpha_tau: 0 violations. All eta in {-1,0,1}: 0 violations. All constants 0: 0 violations. eta_s = 0 before instruction s executes: 0 violations. Symbolic sum equals exact Fraction matrix replay: 0 mismatches.
- Max ratio |O|/2^alpha = 1.0 (bound is attained, for each of Q, P, R separately; single-template skeletons, k=2..4, A<=10, 900 skeletons).
- Extra observation (t6, 683,872 occurrences): every variable h_s has a single sign across all occurrences (+1 for Q, P; -1 for R). So eta_v - eta_u in {-1,0,1}, and pattern rows have |alpha| <= 1, tighter than the stated 2 (harmless; the bound 2 is valid but not attained; max alpha observed 1).

### 2. Lemmas 2-3 (t2.py)
- 203,195 sums (each tested for zero and for integrality with anchor, using H=C+2 where C is the minimal with m <= 2^C+1, m counting anchor/target): exhaustive m<=4, exponents -3..3, all signs; 60,000 random sums m<=40 with gaps drawn from {0..2, H-2..H+1, 0..H-1, H..3H}; 19,037 builder cases (cascades 1+1+2+4+..-2^j, 2^t copies minus 2^t, perturbed, groups offset by H-2,H-1,H,H+1,2H or ~1e9, whole sum shifted so a term/top/bottom of cluster sits at 0 or +-1,H-1,H); 48,000 at exactly m = 2^C+1 for C=1..6 (zero test with M real terms; integrality with M-1 terms + anchor); 72,000 two-cluster cases with gap H-2,H-1,H,H+1 and m up to 2^C+1, C=1..6.
- 0 disagreements between cluster-test and oracle (zero verdict true in 16,469 cases, integral-nonzero in 128,094).
- Teeth: with H' = C (too small) the cascade 2^C copies of 1 minus 2^C gives the wrong verdict for every C=1..6 (out_t2_teeth.txt). H=C+1 also passes all cases; H=C+2 has 2 bits of slack. Max m tested 65 (C=6); beyond is not tested.

### 3. Lemma E pattern determinacy (t3.py)
- 16,537 scalar constraints (types Z with true/false/random targets +-2^e, e<k^2, and I with anchor) on random skeletons k=2,3,4, A in 2..8, charge up to ~30, x* with exponents up to ~1e6 and mixes of exact/small/(H-1,H,H+1)-shifted values; up to 32 terms per constraint; 4000 with at least one LARGE gap.
- Acceptance computed from the labelled pattern alone equals the true verdict at x* in all cases (0 violations).
- 658,840 further integer points x' satisfying L(pi) exactly (saturated integer kernel of the equality rows via unimodular reduction, random-direction walks inside the feasible interval of the LARGE rows and x>=0, step sizes uniform, near boundary, and up to 1e12, so clusters moved by exponentially large offsets: 357,732 points had max coordinate >1e6; 469,676 were more than H away from x*). The verdict was unchanged in every case: 0 violations.
- Limitation: the sampler moves within the lattice of the equality rows plus inequality feasibility, so it covers all x' reachable that way, but is random, not exhaustive. Constraints with m>32 terms were not generated here (A<=8).

### 4. Lemma 4 (t3.py, t4.py)
- Pattern rows (all 16,537 patterns, H=charge+2): max |alpha| = 1 (claim <=2); max |beta| = 39 with constants of the form g - (c_v - c_u), observed max(|beta|-H) = 15 = k^2-1 at k=4 (claim |beta| <= H + k^2): OK.
- Scanner rows (t4.py): replayed the max-plus scanner (add 1+max(U_d, U_s+h), left +h, right -h, neg +1, including pre-shift transients of P and R, both starts (0..0,r), r in {0,k-1}) for all d<k: 1,500 skeletons per k, A<=12, 2,007,394 distinct affine path forms. Max |alpha| (with the a column) = 1, max |beta| = 18 (below both 8k^2 and the draft's 6k^2+3k). Zero rows exceeded the bounds.
- Arithmetic at the budget C = 6k^2-1 (not simulated at that charge, as 2^C occurrences are unenumerable): pattern |beta| <= H+k^2-1 and scanner |beta| <= C+2k-2 are <= 8k^2 for k=2,3,4,5,10,50 (printed in out_t4.txt). Real skeleton tests used charge <=~36.

### 5. Hidden exponential constants (t5.py, t5b.py, plus t2 cascades)
- t5: 810,958 integrality constraints at every prefix and entry (k=2..4, A 4..12, R shifts chosen at maximal valuation). Max nu_2 of a nonzero cluster relative value found: 7 (cluster with 32 terms); worst pattern |beta| = 5; max |alpha| = 1.
- t5b: hill-climbed k=2,3 skeletons (A=12) with entry value having nu_2 = 5 or 6 and 65-90 terms in the single cluster: all pattern rows have beta = 0, alpha<=1.
- Cascade 1+1+2+...-2^j (nu_2 ~ number of terms, m up to 65) with anchor inside, at top, at bottom (t2 builders): cluster-test verdict equals oracle; the rows needed are the adjacent gaps (0 or 1), all <= H-1.
- No constraint type tried (zero, integrality at every prefix, marker targets, exact right-shift legality as post-shift prefix integrality, scanner rows) produced a constant outside {gap<=H-1, constant offsets <k^2, C+k-1}. Not tested: the imported facts (marker exponent <k^2, normalized template form, the small-integer-point lemma, scanner soundness) are taken as given; markers were modelled only as a subtracted +-2^e occurrence with e<k^2.

## Not shown by these tests
Asymptotic claims (log S = O(k^2 log k)); k>=5; charge near 6k^2 at occurrence level; the small-integer-point lemma; soundness of the scanner relaxation; completeness for real F2 skeletons (random skeletons were used, not F2 tables).
