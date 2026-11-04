# Exact finite profile reduction for the selected recursive PP benchmark

Status: new paper proof submitted for independent review. This does **not** prove polynomial-time optimization. Original source files are preserved. The domain is the owner's fixed KMY Appendix F.2 family, arbitrary legal helper states and marker order, the repository's common-child-width PP cost, and one fixed table per arity. K grows. n denotes physical operand bitwidth; no binary-n convention is attributed to the owner.

## Assumptions and applicable imports

1. n>=1 and 2<=k<=K. Every recursion step strictly decreases its natural width. These are the `CostL` constructors in packet17 `lean_T/Constrained.lean`; width cannot reach zero because every table child width is peak+1.
2. Table legality and marker normalization are those of `contract_astra/CONTRACT.md` **with its ADDENDUM**. The F2 point set has 2k-1 points. The cost is specifically PhaseProduct; PTP has not been bridged.
3. `helpers_astra/PROFILE_THEOREMS.2026-10-15T140100.md` supplies the exact completed-table profile and cap oracle. Applicability: same primitive operations, initial identity, exact divisions, nonzero rows, balanced split, scanner, and charged cost. These are paper proofs pending independent review, not imported as new Lean theorems.
4. The PP model has local cost N*8*(W-1)*c, calls 2k-1, and terminal cost R*(4+tau(R)), R=N*w^2. All these costs are nonnegative. At positive leaf width, terminal cost is at least N. This is also proved in existing packet17 `Tcount.lean` (`leafPP_ge`).
5. Padding is legal and has no direct charge. There is no additional objective such as history qubits, no fixed marker order, and no table instruction-count limit. Adding one of these constraints would require a new applicability check.

The argument below concerns the exact selected benchmark, not KMY's branch-specific estimator and not measured hardware cost.

## 1. A polynomial number of width functions suffices

Write a table's canonical profile as (c,a,b):

    W(w) = floor(w/k)+1+max(a,(w mod k)+b),
    max(0,a-k+1) <= b <= a.

If this table is used in any legal ladder rooted at n, its use contracts at some w<=n. Hence

    a+1 <= W(w) <= w-1 <= n-1,

and therefore **0<=a<=n-2**. In particular, the raw offsets A,B are also <=a. This bound holds for every used table, not merely for the supplied constructions or cost-optimal ones.

For each k, enumerate

    a=0,...,n-2,
    b=max(0,a-k+1),...,a.

There are sum_{a=0}^{n-2} min(k,a+1) such pairs, at most (n-1)*min(k,n-1), and fewer than n^2. For n=1 the list is empty and the leaf is the only policy.

For each requested pair, run the exact finite cap oracle from the helpers proof. Discard infeasible pairs. For a feasible pair keep a minimum-charge witness under the cap, then apply free padding to give it that **exact** width function. Call its charge c_min(k,a,b).

Replacement theorem. In any admissible one-table-per-arity ladder, replace each used table at arity k by the corresponding single padded minimum-charge witness. Its width map is identical at every operand width, its charge is no larger, and its number of child calls remains 2k-1. Every subsequent width, multiplicity, arity choice, leaf width and legality test is preserved. Repeated occurrences of k use the same replacement. Therefore the resulting total cost cannot increase.

Conversely, every retained witness is an actual legal table, so every policy constructed from this catalogue belongs to the original feasible universe. Thus minimizing over this finite catalogue has exactly the unrestricted optimum. This is not a relaxation and does not assume width monotonicity of the optimized continuation.

The total catalogue has M < K*n^2 entries. Each entry has three integers, but constructing it need not be polynomial-time and its primitive witness need not have polynomial length.

## 2. Exact evaluation needs no real-number oracle

Let R>=1. The benchmark constants are exact rationals, 3.075=123/40 and 0.86=43/50, and Lean's rounding convention is floor(x+1/2). Consequently

    tau(R) = floor((615*log2(100R)+272)/200)
           = floor((log2((100R)^615)+272)/200)
           = (floor(log2((100R)^615))+272) div 200.

The last equality follows because for integer m, integer d>=1 and real x, floor((x+m)/d)=floor((floor(x)+m)/d). The fractional part of x is less than one and cannot cross the next multiple of d after the integer numerator is divided by d.

Thus Python's exact expression is

    (((100*R)**615).bit_length()-1+272)//200.

The exponent 615 is fixed. Integer powering and bit length take polynomial time in bitlength(R). R=0 has Lean log(0)=0 and tau(0)=1; its leaf contribution is zero. All actually reached leaves here have R>=1.

`exact_rotation_cost.py` implements this formula, the exact leaf cost, profile widths and fixed-table ladder evaluation. Its validation JSON records 4,783 cases through 1,024-bit inputs, independently compared with 180-digit Decimal logarithms and checked against exact integer threshold inequalities. The general equality follows from the proof, not those samples. This closes the scalar cost-evaluation gap, not table synthesis or policy optimization.

## 3. Only logarithmically many levels can improve on stopping

Let U=leafPP(1,n), the cost of the empty ladder. U=O(n^2 log(n+1)) from the exact formula. Because costs are natural numbers and the empty ladder is feasible, an optimum exists with total cost <=U.

If a competing ladder has D levels, its leaf multiplicity is

    N_D = product_{i=0}^{D-1}(2k_i-1) >= 3^D.

Its leaf width is at least one, so total cost >=leafPP(N_D,w_D)>=N_D. Therefore any ladder of cost <=U obeys

    3^D <= N_D <= U,
    D <= floor(log_3 U) = O(log(n+1)).

The same bound allows safe pruning of any prefix with N>U. U itself remains a valid incumbent, so policies costlier than U need not be retained. This argument does not bound k by a fixed constant and does not imply any particular best arity near n=50,000.

## 4. Uniform exact outer algorithm, with an explicit quasipolynomial bound

Given the M-entry complete catalogue, enumerate ladder prefixes of length at most D_max=floor(log_3 U). At each step:

1. Choose a catalogue entry (k,c,a,b). If k occurred before, require the exact same retained entry.
2. Compute W from its profile. Reject W>=w, and reject N*(2k-1)>U.
3. Update the exact accumulated local cost and multiplicity, and evaluate stopping using the exact integer leaf formula.
4. Keep the best stopping choice, including the empty ladder.

The replacement theorem and depth bound prove completeness. Every accepted sequence is realizable using one table per arity, proving soundness. The number of prefixes is at most sum_{d=0}^{D_max} M^d; for M>=2 this is <=2*M^D_max. Cases M=0 or1 are simpler.

Along a retained prefix N<=U, w<=n, so all rotation counts have O(log(n+1)) bits. Catalogue minimum-charge values have polynomially many bits in n,K by the state-count bound below. The work per prefix is polynomial in n,K and profile bit length.

With M<K*n^2 the outer algorithm takes

    (K*n^2)^{O(log(n+1))} * poly(n,K)
      <= exp(O(log^2(n+K+2))) * poly(n,K).

This is a **uniform exact quasipolynomial upper bound for the outer problem when a complete catalogue is supplied**. It is not polynomial, does not independently choose a new table on each occurrence, and does not enumerate all arity assignments in advance. A polynomial table-realization oracle would give this quasipolynomial end-to-end bound; it would not by itself complete the desired P proof under the one-table-per-arity rule.

## 5. Uniform finite algorithm for the whole original problem

For a requested profile, the helpers graph has at most

    V(k,a,b) <= (2^(a+1)+1)^(k^2) * (a+1)^k * (a+k)^k * 2^(2k-1)

states. Since a<=n-2 and k<=K, the logarithm of this bound is O(K^2*n+K*log(n+K)+K). Per-state branching and exact arithmetic are polynomial in n,K. A shortest path can be chosen without repeated graph states, even when some edges have zero cost, so its charge is at most 3*(V-1). Its charge encoding is polynomial in n,K, while its explicit instruction count can be exponential. Padding adds at most four shift instructions.

Run these finite searches for fewer than K*n^2 pairs and then the exact outer algorithm. This is a uniform exact algorithm with time and explicit-witness size bounded by **2^{poly(n,K)}**. It proves decidability and exact solvability with a derived finite state cap; it does not prove membership in P. If n is supplied only in binary, this is a bound in its numeric value and may be doubly exponential in log(n); no binary-input complexity class is claimed from it.

For a cost-only or succinct-output problem, output requirements must be stated separately. The existence of a small three-integer summary does not prove a short realizable instruction witness.

## 6. Precisely what remains for P

Two sufficient next obligations are now concrete:

* A uniform polynomial-time algorithm producing a minimum-charge realization for each relevant canonical width pair, or a polynomially constructible subcatalogue proved to preserve a global optimum. The present cap oracle is exponential.
* A polynomial-time exact optimizer for this catalogue with the global one-table-per-arity rule, or a normal-form theorem that removes that coupling. The present complete bound is quasipolynomial; no contiguity/monotone-arity conjecture is assumed.

There may be a joint algorithm that bypasses this decomposition. These two obligations describe this sufficient route, not logical necessities for every possible proof of P. The practical observation k=11..15 near n=50,000 is useful for experiments, but proves neither obligation for growing K.
