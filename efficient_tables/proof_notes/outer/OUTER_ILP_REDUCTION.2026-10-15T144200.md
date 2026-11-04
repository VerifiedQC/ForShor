# Exact polynomial outer optimization through few distinct arities

Status: candidate paper proof awaiting independent review and primary-source verification of the integer-programming runtime. This is a theorem about optimization from a supplied complete minimum-charge catalogue. It is not a polynomial table-synthesis theorem. The parent coordinates the source verification and independent audit.

This new artifact supersedes no existing file. It develops the arithmetic compression in ARITY_WORDS_AND_MEMORY.2026-10-15T143600.md using the parent's key observation that the number of distinct arities is small enough for a t^{O(t)} integer-programming algorithm.

## Assumptions and imports

1. The PP model, exact canonical profiles, shared-table rule, root bound U, depth and bit-complexity facts are exactly those specified in Sections 1 and 2 of the earlier artifact and fixed_execution_2026-10-15/coordinator/FINITE_PROFILE_REDUCTION.2026-10-15T150000.md. They apply without modification.
2. A complete catalogue provides c_min(k,a,b), the least charged count of a legal table under each canonical cap, and a reconstructing witness reference. Free padding makes that witness have the exact cap profile. Used pairs satisfy 0<=a<=n-2 and max(0,a-k+1)<=b<=a. Infeasible caps have value infinity. These are the prior exact profile and padding theorems, in the same objective and legality model.
3. NEW IMPORT, parent/profile agent to pin and audit: every feasible cap (a,b) has a table with c<=3ka, obtained from a nonnegative potential that increases by at least one per charged operation and ends at most ka. In particular, its minimum-charge realization satisfies this bound. This artifact does not independently prove the scanner potential.
4. Prior explicit F2 paired construction supplies charge c_0<=6k^2 and canonical offsets a_0,b_0<=8k^2. Applicability is the same fixed F2 PP family and primitive costs. If those source bounds change, the constant below must be recomputed.
5. EXTERNAL ALGORITHMIC IMPORT, parent to source before promoting status: integer linear feasibility in t integer variables with binary input length L is solvable deterministically in t^{O(t)} poly(L), with a feasible integer point reconstructed. A mere 2^{O(t^2)} algorithm would NOT suffice for the argument below.

Every use of these assumptions is explicit below. All polynomial bounds are in numeric operand bitwidth n, K and catalogue encoding length; no polynomial-in-log(n) claim is made.

## 1. Uniform charge labels independent of n

Write d=a-b, so 0<=d<=k-1 and a>=d. At fixed k,d, both offsets increase when a increases; cap feasibility is upward closed and c_min(k,a,a-d) is nonincreasing. Consequently, for any fixed integer charge c, its equality set is either empty or a single integer interval [ell,u] inside [d,n-2]. A supplied catalogue lets us find all such intervals by scanning. A monotone realization-value oracle would let us find their endpoints by binary search.

Let a_*=max(a_0,b_0+d). For a>=a_*, the paired construction fits under (a,a-d), and free padding realizes the cap with c<=c_0<=6k^2. For a<a_*, the potential bound gives c_min<=3ka<3ka_*; since a_*<=8k^2+k-1, this is less than 27k^3. Thus at every feasible used cap,

    0 <= c_min(k,a,a-d) <= 27k^3.

This bound is independent of n. It is a bound on the charge value, not a polynomial algorithm for finding the minimum-charge table.

## 2. Polynomially many decorated words

Enumerate finite words with product Q=product_i(2k_i-1)<=U. At each occurrence decorate its arity with a residue r_i in [0,k_i-1], kink d_i in [0,k_i-1], and charge c_i in [0,27k_i^3]. Reject decorations for which repeated arities disagree in d or c. The count can overestimate by allowing independent d,c at every occurrence before filtering.

There are B(k)=k^2(27k^3+1)<=28k^5 decorations per occurrence. Put q=2k-1>=3. Then

    sum_{k>=2} B(k)/q^10
      <= 28 sum_{m>=3} m^(-5)
      <= (28/27) sum_{m>=3} m^(-2)
      <= 14/27 < 1.

The weighted sum over all decorated finite words is at most 1/(1-14/27)=27/13. Every word with Q<=U has weight Q^(-10)>=U^(-10). Thus fewer than 3U^10 decorated words need to be considered, uniformly in growing K.

A depth-first generator processes exactly accepted decorated prefixes, so its runtime is polynomial in U up to polynomial arithmetic and word-output overhead. Filtering inconsistent repeated d/c choices, impossible cap intervals and the root residue only lowers this count. Include the empty word separately as the root-stop candidate.

## 3. Distinct arities permit t^{O(t)} work

Let t be the number of distinct arities in a word. In increasing order, k_j>=j+1, so

    t! <= product_{distinct k}(2k-1) <= Q <= U.

For t>=4, t!>=(t/2)^(t/2)>=t^(t/4). Hence t log t<=4 log U. Therefore t^{O(t)}=U^{O(1)}; bounded t<4 only changes constants. This is stronger than the depth bound alone: D=O(log U) would not turn D^{O(D)} into a polynomial, but the distinct-arity factorial bound does.

The planned ILP must have ONLY t integer variables. Introducing the intermediate widths as separate integer variables would lose this argument, so they are eliminated explicitly below.

## 4. Eliminate all widths

Fix a consistent decorated word of depth D. For each distinct arity k the sole integer variable is a_k, constrained to its catalogue interval [ell_(k,d,c),u_(k,d,c)]. Define the following constants and affine expressions:

    P_0=1; P_(i+1)=P_i k_i;
    N_0=1; N_(i+1)=N_i(2k_i-1);
    h_i=1+max(0,r_i-d_(k_i));
    x_0=n;
    x_(i+1)=x_i+P_(i+1)(a_(k_i)+h_i)-P_i r_i;
    w_i=x_i/P_i.

There are no x or w decision variables: these symbols stand for explicitly substituted affine rational expressions in the t variables a_k.

For each possible terminal width z=1,...,n, impose the one linear equality

    x_D=P_D z.

This guarantees all intermediate integrality and prescribed residues. For any i, every increment after index i is divisible by P_(i+1). Thus x_D=0 mod P_D implies x_i-P_i r_i=0 mod P_(i+1). Consequently x_i/P_i is integer and has residue r_i modulo k_i. The affine recurrence is therefore the exact canonical scanner width recurrence, not an approximation. It also forces the chosen root residue to agree with n.

Impose each strict contraction as the integer linear inequality

    k_i x_i-x_(i+1) >= P_(i+1).

This is exactly w_i-w_(i+1)>=1. Since w_0=n and w_D=z>=1, these inequalities also place every intermediate width in [1,n]. They retain the model's strict-contracting requirement without a monotonicity or exchange premise.

## 5. Exact objective and feasibility queries

For fixed z, the terminal cost L(N_D,z) is a known exact integer. Local cost is the affine rational expression

    A(a)=8 sum_{i=0}^{D-1} N_i c_(k_i) (x_(i+1)/P_(i+1)-1).

Because P_(i+1) divides P_D, multiplying by P_D clears every denominator. On feasible points A(a) is an integer, as established by Section 4.

For each integer trial budget T<=U, append the linear inequality

    P_D A(a) <= P_D (T-L(N_D,z)).

This is one further integer-coefficient inequality, with no extra variable. Fixed-dimensional integer feasibility decides whether the decorated word has a legal shared-profile ladder of cost at most T and terminal width z. If L(N_D,z)>U, discard that z immediately. Binary search T=0,...,U finds the least attainable cost with O(log(U+1)) feasibility calls, and the final call reconstructs its t offsets. A catalogue witness for each chosen (k,a_k,a_k-d_k) reconstructs the shared tables. Only used arities need these capped witnesses; unused arities may use the prior explicit construction.

Each ILP solution is sound: offsets are in the exact minimum-charge equality intervals; repeated arities use the same a,d,c, hence the same canonical profile and one selected witness; residues and integer widths are exact; contractions hold; the objective is the chosen benchmark. Conversely every catalogue ladder of total cost at most U produces an enumerated decoration, its true terminal z, and a feasible ILP assignment with exactly its cost. Therefore minimizing all returned costs yields precisely the original optimum over the supplied complete catalogue.

## 6. Bit complexity and total runtime

For any enumerated word, D<=log_3 U, N_i<=U, and P_i=product_{h<i}k_h<=N_i<=U. All profile offsets lie in [0,n-2]. Charges are at most 27K^3; residues and kinks are less than K. Each affine expression has t+1 rational coefficients, built from O(D) terms whose factors have polynomial numeric bounds in n,K,U. Clearing denominators by P_D therefore produces integer coefficients with polynomial bit length in log(n+1),log(K+1),log(U+1) and D. There are O(D+t) constraints. Computing exact leaf costs has polynomial bit complexity by the earlier integer tau theorem.

The external t^{O(t)} poly(L) algorithm is U^{O(1)} poly(L) by Section 3. Multiplying by fewer than 3U^10 decorations, n terminal widths, O(log(U+1)) budget calls, and polynomial preparation still gives polynomial runtime in n,K and catalogue input length.

This is a uniform polynomial outer optimizer. It does not assume fixed K, monotone arities, contiguous arities, bounded live assignments, or independent table selection at repeated arities. Its exponent may be very large; this is a complexity theorem, not a practical performance estimate.

## 7. Remaining obligations before promotion

* Independently verify and pin the potential bound c<=3ka and the explicit paired-construction constants used in Section 1.
* Verify a primary-source deterministic t^{O(t)} poly(L) integer-feasibility algorithm, including reconstruction and binary encoding, and cite it exactly. A weaker dimension dependence cannot be substituted silently.
* Audit the single-terminal-equality congruence argument and strict-contraction inequalities independently; these are the central applicability steps.
* Verify the reduction on finite synthetic catalogues by comparing direct shared-profile enumeration with the decorated ILP or exhaustive-offset equivalent. Existing fixed-word DP checks validate a different implementation and do not alone validate this reduction.

Even after these items pass, polynomial realization of the complete minimum-charge catalogue remains a separate open obligation for an end-to-end polynomial algorithm. The present route closes only the global shared-arity selection obstacle once that catalogue is supplied.
