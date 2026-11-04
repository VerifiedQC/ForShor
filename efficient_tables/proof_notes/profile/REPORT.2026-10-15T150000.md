# Independent adversarial review of the fixed F.2 PP reduction

Date: 2026-10-15. Verdict: **paper-review PASS under the explicitly pinned contract; no counterexample found in the claims audited below.** This is independent mathematical/source review plus bounded deterministic computation. It is not a new Lean proof, an assertion of physical cost faithfulness, or a proof of P. Existing author files were read only. No local inference was used.

## Scope and reviewed materials

Reviewed helpers `PROFILE_THEOREMS.2026-10-15T140100.md` and `RESULT_ADDENDUM.2026-10-15T140600.md`; contract `CONTRACT.md` with `ADDENDUM.2026-10-15.md`, `BRIDGES.md`, and the constructor trace generator; coordinator `exact_rotation_cost.py` and `FINITE_PROFILE_REDUCTION.2026-10-15T150000.md`.

Source inspection included actual `TableGeneration/Basic.lean`, `Language.lean`, `RecursiveCost/Model.lean`, packet17 `lean_T/Core.lean`, `Tcount.lean`, `Constrained.lean`, `TableProblem.lean`, `C1Bound.lean`, `C1Final.lean`, `C1Main.lean`, and the local KMY v4 `main.tex` F.2 passage. The accepted scientific problem here is fixed F.2 targets, exact repository marker normalization, arbitrary marker permutation and legal helpers, return to identity, balanced operands, common child width, growing K, and one table per used arity. The initial binary-n default in CONTRACT is superseded by its addendum.

The source distinguishes three different models. KMY's discussion allows branch-specific widths and uses a CR-phi cost in its displayed search. `Model.lean` supplies the conservative scanner and a separate logical-gate overhead. Packet17 `Tcount.lean` defines the PP charged T-count used here. The new results are correctly scoped to the last model combined with the scanner; they do not prove equivalence to KMY's estimator.

## 1. Three-integer profile: independently checked proof

The decisive legality condition is present in source: `Prog.OpOK` rejects `dst=src`, and `ProgConsumesPtsSafe.safe_add` requires it. Hence every allowed algebraic step is invertible over the rationals. From identity, every row remains nonzero.

For any natural initial scan vector z, the invariant `0 < ||X_i||_1 <= 2^u_i` is valid. A right shift by s is legal only when all row entries are divisible by 2^s. A nonzero such integer row has mass at least 2^s. Thus s<=u_i, and the scanner's natural subtraction never truncates. This is a proof about safe, legal prefixes; the raw operation datatype and `applyOp?` by themselves do not prohibit self-addition. Omitting `safe_add` would invalidate this argument. The reviewed claims include that hypothesis.

With truncation removed, max-plus influence propagation is exact. Taking a columnwise maximum across every row and every time, including time zero, commutes with the maximum over initial coordinates. The history peak is `max_j(z_j+h_j)` with h_j>=0. The balanced input `(L,...,L,L+r)` therefore gives

    W(w)=L+1+max(A,r+B).

For R=k-1, setting `a=max(A,B)` and `b=max(A,R+B)-R` gives `max(0,a-R)<=b<=a`. The three cases B>=A, A>=R+B, and B<=A<=R+B verify `max(A,r+B)=max(a,r+b)` on every 0<=r<=R, including equalities. Endpoints r=0,R uniquely recover a,b. This establishes exact width-function equivalence, not merely a large-width approximation or a bound.

Together with charge c and fixed arity k, these parameters determine the reviewed planner's local charge, common child width and multiplicity at every invocation. They do not summarize intermediate states for synthesis; nor do they summarize unequal operand widths, additional history-qubit objectives, or branch-specific children.

## 2. Padding and global replacement: pass

The left/right shift pair on an initial basis row is legal and returns both algebraic state and current scanner width exactly. Its retained peak remains. Distinct lower and top rows exist because k>=2. The four prefix shifts therefore replace raw `(A,B)` with `(max(A,p),max(B,q))`, without changing charge, markers or restoration.

For a requested canonical cap (a,b), its endpoint inequalities imply raw A<=a and raw B<=b. Padding with p=a,q=b makes the exact canonical pair (a,b): canonicality gives `a>=b` and `R+b>=a`, so no hidden renormalization changes the result.

Consequently a charge-minimal cap witness can replace a table of that exact pair everywhere the arity is used. All widths, multiplicities, admissibility decisions and terminal rotations stay equal; only nonnegative own-cost terms decrease. This handles the global table constraint and requires no monotonicity of the optimized continuation. No counterexample was found. A componentwise-smaller width map alone would not justify the same replacement without the free padding argument.

## 3. Finite exact cap oracle: pass, with exponential output caveat

State `(X,u0,uR,S)` is sufficient. The two width vectors retain the quantities needed for all future transitions. Discarding a transition immediately when an endpoint cap is exceeded enforces history caps without separately storing the past peak. Marker availability depends on exact X; arbitrary order makes the consumed subset sufficient. End state requires X=I and all targets, not restoration of scanner widths.

The mass invariant at the all-zero initial vector bounds every coefficient by 2^a. Current u0 lies in [0,a], and uR in [0,R+b]. Every nontrivial legal shift has amount <=a. For an addition, post-width >=s+1 bounds its exponent by a-1. Thus the enumerated graph has finite complete branching; no independent guessed exponent cutoff is being smuggled in.

The stated product state bound is a valid overcount. Dijkstra on finite nonnegative edge weights returns the minimum charge; zero-cost cycles are harmless. Removing repeated full graph states yields a shortest simple path, so charge <=3(V-1) and instruction count <=V-1 before padding. The exact matrix arithmetic and distance bits are polynomial in k,a, but V and output length may be exponential. Automatic first-occurrence marking is sound only because markers have zero cost and no state/width effect, order is arbitrary, and no layer objective is present. These conditions hold in the pinned problem.

## 4. Finite profile reduction and outer optimization: pass

At any used arity, contraction at w<=n gives `a+1<=W(w)<=w-1<=n-1`, hence a<=n-2. This covers every used legal table, without invoking incumbent constructions, optimum existence, or a charged budget. The canonical pair count is `sum_a min(k,a+1)`, below n^2. For n=1 only the empty ladder is possible.

Replacing each used table with the single minimum-charge padded realization of its pair proves optimum preservation from the unrestricted universe to the finite catalogue. Every catalogue entry is realizable, giving the converse. Repeated use of an arity remains the same entry. The proof does not justify independently choosing different entries at different levels; the outer algorithm correctly rejects that.

For U=leaf(1,n), every cost<=U ladder has terminal multiplicity N>=3^D, positive terminal width, and terminal cost>=N. Therefore D<=floor(log_3 U). Exact tau gives U=O(n^2 log(n+1)); the enumerated depth is O(log(n+1)). The geometric prefix count and `(K n^2)^{O(log(n+1))}` outer bound are valid. Along admitted prefixes, N<=U and w<=n give polynomial-size cost arithmetic. A supplied catalogue must include realizability evidence or reconstructed witnesses, not merely unverified integer pairs.

Combining the finite graph bound with fewer than K n^2 calls gives the stated `2^{poly(n,K)}` exact algorithm and explicit-output bound. This is a bound in physical n, not in log(n). The reduction is a meaningful exact finite synthesis theorem, but not a polynomial synthesis theorem. Even a polynomial local realization algorithm yields only the stated quasipolynomial outer upper bound by this proof.

Minor output convention to keep explicit: the cap covers **used** arities. If a deliverable requires an entire table family for every 2<=k<=K, fill unused arities with the supplied legal F.2 C1 construction. Do not require unused tables to satisfy a<=n-2. This completion preserves the optimum and the claimed finite complexity bounds.

## 5. Exact rotation cost: pass

For positive integer R,

    tau(R)=floor((615 log2(100R)+272)/200).

Let Q=(100R)^615 and m=floor(log2 Q). Writing log2 Q=m+f, 0<=f<1, shows the integer numerator m+272 and the fractional f cannot cross a multiple of 200 after division. Thus tau=(m+272)//200 exactly. `Q.bit_length()-1` computes m. No numerical-separation assumption, irrationality argument or floating logarithm is needed. The exponent 615 is a constant, so integer power evaluation is polynomial in the bit length of R. Lean's real-log convention at zero and floor rounding yield tau(0)=1. The Python implementation follows this derivation.

The independent checks use exact integer threshold inequalities, not Decimal agreement as a proof. The helper `ladder_cost` checks profile consistency and contraction but does not validate target realizability or canonicality. It is a scalar evaluator, not a synthesis validator; this is consistent with its intended use.

## 6. Construction and dominance claims: pass

The local F.2 passage matches the stated point prefix and 2k-1 paired / 2k-2 singleton addition counts. The signed reciprocal map and conjugation preserve addition count and exact legality, with marker signs corrected. They do not preserve charged signs or top-remainder width, as the authors expressly say.

C1 build/reset counts and sign corrections are valid. The inspected general `genOps_bound` and `arith_genOps` statements genuinely quantify over arbitrary eligible point lists; applying them to F.2 is a paper instantiation, not a silently existing Lean theorem about F.2. The stated polynomial construction length and loose dense-replay bound are sound.

In the paired constructor row1 never depends on row0, while basis sources j>=2 stay untouched. Subtracting each active build shift gives the claimed normalized-width recurrence and the loose 8k^2 profile bound. Connector scans with starting widths u,v end at `max(u+3,v+3)` without marker negations and `max(u+5,v+5)` with the two marker negations, regardless of whether these occur after connector one or two. Widths rise through the connector segment. Positive-first and negative-first have the same entire child-width function; positive-first saves two charged units per pair. The resulting `16 p (W-1)` local PP saving is correct, multiplied by N at that level. This is dominance within that family, not global optimality.

The isolated macro addition lower bound is also consistent with the allowed dyadic units. Separate macro expansion is not globally optimal in general; the source does not claim it is.

## 7. Independent deterministic checks

`audit_checks.2026-10-15T150000.py` is a new, independent scanner, mass checker, max-plus extractor, and small capped Dijkstra implementation. It imports author constructor functions only to obtain instruction traces, which it replays independently; it imports tau only to test exact threshold inequalities. Output is `CHECKS.2026-10-15T150000.json`.

Result: PASS in 15.21 seconds.

- 240 seeded legal closed schedules, k=2..9, including legal inverse right shifts; 3,960 direct width checks and exact padding checks.
- 22,103 raw-pair canonicalizations, k=2..24, A,B=0..30, checked at every residue.
- 68 C1/paired constructor cases over PP/PTP, k=2..18, each independently replayed at six widths including 2,048 and 50,000; exact markers/restoration, profile bounds, charge bounds and both connector orders checked.
- 10,361 exact tau threshold checks, inputs through 2,042 bits.
- Seven complete finite cap searches with k=2 and charged budget 8. The requested (a,b)=(2,2) query has optimum charge 4. Queries (3,2),(3,3) likewise return 4. Null answers for smaller caps mean no solution within budget 8, not an uncapped infeasibility assertion.
- Exhaustive small canonical profiles and contracting uses checked the a<=n-2 implication.

The sampling supports implementation consistency; universal results rest on the independent proof review above. No new Lean file was created or elaborated. Existing Lean source was inspected, not rebuilt. No claim is made that the new profile, padding, cap oracle, F.2 instantiation, or finite-catalogue reduction has already been kernel checked.

## Refutation outcome and remaining work

No mathematical counterexample or fatal gap was found in the audited primary claims. The main potential failures were explicitly tested or discharged: zero-row truncation, small-width effects, raw/canonical mismatch, loss of accumulated peaks, missing exponent bounds, illegal global candidate switching, floating-point rounding, and output-size concealment.

The next obstacles to P remain both local realization and the globally constrained outer optimization, with reconstruction obligations included. Neither finite state count nor the polynomial number of completed width summaries solves those obstacles. PTP recursive T-count, unequal inputs, and additional objectives need separate bridges.
