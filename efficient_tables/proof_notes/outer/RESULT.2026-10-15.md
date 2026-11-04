# Gap-closure result: polynomial outer optimization; realization still open

The shared-table optimization gap has a complete paper proof that passed independent adversarial review: **given complete minimum-charge profile information, exact recursive PP T-count optimization with one fixed table per arity is uniformly polynomial in n and growing K.** Constructive profile realization remains open. Consequently this work does not establish the requested end-to-end P/FP theorem.

Throughout, n is the physical operand bitwidth and complexity is polynomial in numeric n, not in log(n). The target remains KMY Appendix F.2 points, repository marker normalization, arbitrary legal writable-row helpers and marker ordering, identity endpoints, common child width, and one fixed table reused whenever its arity recurs. The practical observation that arities are small at relevant moduli is not used as a fixed-K assumption.

## 1. Exact outer theorem and proof

Let c_min(k,a,b) be the minimum charge over legal complete tables under canonical profile cap (a,b). Canonical pairs satisfy max(0,a-k+1)<=b<=a. Free identity padding makes cap-minimum and exact-profile minimum charges identical. The child width of an exact profile is

    W_k(w) = floor(w/k) + 1 + max(a_k, (w mod k)+b_k).

At multiplicity N, its local PP cost is 8N(W_k(w)-1)c_k, and the next multiplicity is N(2k-1). Each used step must contract strictly. Replacing a table once per arity by a cheaper table with precisely the same width function preserves every recursion width and lowers or preserves cost. Thus minimum charge at each canonical profile is sufficient, without relaxing the shared-table rule.

**Theorem.** Given the complete c_min catalogue for used caps a<=n-2, the minimum recursive PP T-count can be computed in polynomial time uniformly in n and K. If the catalogue also supplies realizing witnesses, an optimal shared-table family and ladder can be recovered in polynomial time. A polynomial constructive realization oracle therefore suffices for the full uniform result.

Here is the core argument. The full reduction, all inequalities and bit bounds are in [the planner proof](planner_astra/OUTER_ILP_REDUCTION.2026-10-15T144200.md).

1. Stopping immediately gives a known exact incumbent U=O(n^2 log(n+1)). Any competitive ladder has call product Q=product_i(2k_i-1)<=U. Its depth is at most log_3 U.
2. Every feasible minimum charge is at most 27k^3, as proved below. Write d=a-b. For each fixed k,d,c, the equality set c_min(k,a,a-d)=c is an integer interval, possibly empty, because c_min is nonincreasing along a fixed-d ray. Retain a as a free integer variable within that interval; do not replace every choice by its narrowest endpoint.
3. Decorate each arity occurrence with its residue r, d, and charge c. There are at most B(k)=k^2(27k^3+1)<=28k^5 decorations. The convergent sum sum_{k>=2} B(k)/(2k-1)^10 <=14/27 implies fewer than 3U^10 decorated words with Q<=U. This bound is uniform in K. Reject decorations that give inconsistent d or c to repeated arities.
4. For a fixed decorated word, there is only one unknown offset a_k per distinct used arity. Let t count those distinct arities. Since their sorted values are at least 2,3,...,t+1, we have t!<=Q<=U. Thus t log t=O(log U).
5. Eliminate all intermediate widths. Set P_0=1, P_(i+1)=P_i k_i, x_0=n, and h_i=1+max(0,r_i-d_(k_i)). Define the affine expressions

       x_(i+1)=x_i + P_(i+1)(a_(k_i)+h_i) - P_i r_i,
       w_i=x_i/P_i.

   These are expressions, not extra integer variables. Enumerate terminal width z in[1,n] and impose x_D=P_D z. Every later increment is divisible by the appropriate prefix product; this single terminal equality forces all intermediate widths to be integral and every prescribed residue to be correct. Strict contraction is exactly the linear inequality k_i x_i-x_(i+1)>=P_(i+1). Positive terminal z and contraction bound every width in[1,n].
6. For fixed terminal z, the leaf cost is constant and the local-cost sum is affine in the t offsets. Clear denominators by P_D<=Q<=U and binary-search the integer budget. The result is an integer linear feasibility problem with exactly t integer variables and polynomially sized coefficients. Kannan's deterministic algorithm takes t^O(t) poly(input length) bit time, which is polynomial in U because t!<=U. Multiplying by the polynomial decorated-word and terminal-width counts preserves polynomial time.

The accepted primary-source import is Kannan, *Minkowski's Convex Body Theorem and Integer Programming* (1987), Theorem 5.4; see [source and bit-complexity verification](coordinator/KANNAN_APPLICABILITY.2026-10-15.md) and the [primary paper](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Kannan/Kannan1.pdf). The reduction only needs its decision procedure. Bounded coordinate queries recover offsets, so no separate native witness-recovery theorem is assumed.

This proof explicitly enforces all repeated-arity assignments. It needs neither monotone nor contiguous arity sequences. The large theoretical exponent is not a practical runtime claim; Kannan's algorithm was imported as a theorem, not implemented or benchmarked here.

## 2. New realization results

For a legal prefix, let X be its integer row matrix, u its scanner widths, and d_X=log_2|det X|. Consider

    Phi = sum_i u_i - d_X.

Exact left and right shifts change the two terms equally. The earlier no-clipping lemma is essential for right shifts. Negation increases Phi by one. An addition increases it by 1+max(0,u_src+s-u_dst), at least one. Identity endpoints have determinant magnitude one. If t counts additions and negations, the two endpoint scans therefore give

    t <= min(ka, kb+(k-1)^2),       c <= 3t.

Split any witness at every charged operation and marker. Within each shift-only block, replace each row's shifts by its net shift. The endpoint row is integral, so a net right shift is legal; scanner endpoints agree and peaks cannot increase. Four free prefix shifts restore the exact original canonical profile. Thus a same-charge same-profile witness needs at most

    (k+1)(t+2k-1)+k+4

instructions. This proves polynomial witness length in numeric k,a, and hence in n,K for used profiles. It does not give polynomial search.

For the uniform charge ceiling, use the existing legal paired constructor with c_0<=6k^2 and offsets a_0,b_0<=8k^2. On the ray d=a-b, let a_*=max(a_0,b_0+d). Above a_* the constructor can be padded to the requested profile. Below a_*, the potential gives c_min<=3ka<27k^3. Therefore every feasible minimum charge is at most 27k^3, and a minimum witness can be compressed to O(k^4) instructions.

Consequences supported by the [profile paper](profile_astra/POLYNOMIAL_WITNESSES.2026-10-15T151500.md), [charge staircase proof](profile_astra/CHARGE_STAIRCASES.2026-10-15T152500.md), and [XP algorithm](profile_astra/XP_REALIZATION.2026-10-15T153000.md):

* Uniform NP membership for profile decision and the full recursive decision problem under numeric/unary width encoding; FP^NP upper bounds for exact optimum and witness recovery.
* At most O(k^4) finite charge plateaux per arity, with their padding parameters retained.
* An exact realization algorithm with bound (k^2(a+1))^O(k^4) poly(k,a). This is XP in k: polynomial at each fixed k, not uniform P for growing K.
* Complete k=2 classification: a canonical cap is feasible exactly when b>=2, and its minimum charge is four.

## 3. The remaining sufficient theorem

For 0<=d<k and 0<=C<=27k^3, define

    theta(k,d,C)=min{a>=d: some complete legal F2 table has
                     charge<=C and profile <=(a,a-d)},

with infinity if no witness exists. The precise outstanding task is to compute theta truncated at n-2, together with a realizing table when finite, in time polynomial in n,k uniformly in k.

Then c_min(k,a,a-d)=min{C:theta(k,d,C)<=a}. Only O(k^4) threshold queries per arity are needed, and padding transports threshold witnesses to every requested exact profile. This constructive threshold theorem would combine with Section 1 to finish the requested uniform result. It remains unproved; it is not disguised as an available oracle.

A new [Newton-state construction](profile_astra/NEWTON_STATE_OBSTRUCTION.2026-10-15T154100.md) rules out one proposed intermediate route: a quotient preserving every short target-service answer needs exponentially many helper-state classes even under polynomial preparation and width bounds. The [review clarification](profile_astra/ROOT_REVIEW_AND_NEXT_TARGET.2026-10-15T154500.md) uses extended-natural service costs and states the narrow scope. These states are not proved necessary on globally optimal complete tables. The result does not prove hardness, non-P, or failure of whole-table replacement algorithms.

## 4. Decreasing arities: current scope

The user's conjecture concerns the optimum over all legal tables and remains open. A restricted catalogue of actual legal padded F2 tables has optimal arity sequence (5,5,3,5), so monotonicity cannot be assumed from the recursive form alone. This is not a counterexample to the unrestricted all-table conjecture.

Further tests on unpadded constructor families support decreasing optimal arities on the completed tested ranges. Residue-wise exchange arguments also improve adjacent local costs and composed child widths in these families. However continuation costs can decrease when the input width increases, and some feasible full ladders become more expensive after a locally improving swap. Thus those local exchange properties do not by themselves prove global monotonicity. The separate adversary follow-up records exact tested domains and policy examples. None of this is needed by the polynomial outer theorem.

## 5. Verification and framework use

Parallel Astra agents handled profile theory, planner theory and adversarial counterexamples; a separate Astra agent reviewed the proofs. The [independent audit](review_astra/REVIEW.2026-10-15T194000.md) found no blocking mathematical defect in the polynomial witnesses, charge ceiling, XP realization or conditional outer theorem. Its [addendum](review_astra/ADDENDUM.2026-10-15T195500.md) checks the source import, formalization scope and Newton-state result. This was independent adversarial review with proofs visible, not blinded HG7.

The independent implementation checked 3,096 exact program replays and 110,000 affine assignments. Author checks separately compared 168 fixed-word optima and 207,945 decorated assignments; these finite checks support implementation fidelity, not the universal proofs. The Newton construction checked 888 states, 2,586 member routes and 15,516 residuals.

ResearchSkills preregistrations and InventMath proof/refutation separation were used. The deterministic autoresearcher source-fetch adapter acquired the primary paper. Its existing Lean workbench and autoformalizer trusted replay checked [nine elementary integer lemmas](coordinator/FORMAL_CERTIFICATE.2026-10-15.md). The full table semantics and complexity theorems are not machine formalized. MindPalace's schema validated [two staged claims](coordinator/MINDPALACE_PROPOSAL.2026-10-15.json); no canonical graph claims were changed. No local model inference was used.

Original inquiry, ledgers, constructions and prior reports remain untouched. This report is the new entry point for this research round. The end-to-end uniform growing-K exact recursive T-count P theorem remains OPEN solely at the constructive profile-realization obligation identified above, within the retained model and encoding.
