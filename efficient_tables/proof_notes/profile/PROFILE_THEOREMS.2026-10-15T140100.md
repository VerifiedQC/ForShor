# Exact three-integer planner profiles and finite profile realization

Status: analytical proofs with exact deterministic witnesses; not independently reviewed or Lean formalized.
Scope: PP in the existing recursive T-count planner, growing unary k >= 2, fixed KMY F.2 targets,
arbitrary legal order/helpers/all writable rows, start/end identity. All existing sources preserved.
PTP may use the width results, but its recursive T-count formula is not established here.
Method: ResearchSkills S03, counterexample-first, explicit assumptions, exact arithmetic witnesses.

## 1. Outcome

Every complete legal table P has a continuation-complete planner profile consisting of THREE
nonnegative integers `(c,a,b)`, in addition to its arity k:

    child_P(w) = floor(w/k) + 1 + max(a, (w mod k) + b),
    c = a_plus + 3 a_minus + nu,
    max(0,a-(k-1)) <= b <= a.

The summary is exact at all operand widths, including small widths. It preserves the existing
planner's local cost `8*(child-1)*c`, child multiplicity `2k-1`, and every recursive use of the
same table at the same arity. No monotonicity of the optimized continuation function is assumed.

This is compression of COMPLETED table behavior, not a polynomial enumeration of retained
states or a polynomial-time synthesis algorithm. Realizability of such triples remains the
uniform bottleneck. Section 7 supplies an exact finite realization algorithm with explicit
exponential cap dependence, including reconstruction. It is not claimed polynomial.

## 2. Assumptions and source anchors

1. `k >= 2`; the top limb is row k-1. Used to distinguish a lower row for padding.
2. Table operations are exact integer row additions with distinct source/destination, left shifts,
   coefficientwise legal right shifts, negation, and markers. All rows remain nonzero because the
   operations are invertible over the rationals. Used to remove width truncation.
3. Initial rows are identity and initial scan widths are `L,...,L,L+r`, where `w=kL+r`, `0<=r<k`.
4. The scanner uses addition `u_d <- 1+max(u_d,u_s+shift)`, negation `u_d <- u_d+1`, left shift
   `u_d <- u_d+n`, right shift `u_d <- max(0,u_d-n)`, and markers do not change widths. It retains
   the maximum at EVERY instruction and returns maximum+1.
5. Charged shifts/markers cost zero, plus costs 1, minus costs 3, negate costs 1. This is the
   existing PP benchmark definition; the additions-only free-negation objective is different.
6. There is no separate cap forbidding the prefix padding gadget. When synthesizing under a
   specified profile cap, the padded gadget obeys that same requested cap by construction.

Exact sources read:

- `../../../../plan_a/lean_repo/TableGeneration/RecursiveCost/Model.lean`, lines 33-37 (top-heavy
  split), 115-156 (`initBalancedWidths`, `updateBalancedWidths`, peak scan and final +1).
- Packet 17 `lean_T/FloorMass.lean`, `Inv`, `inv_step`: existing row-mass invariant mechanism.
  We instantiate its elementary proof below, including the nonzero/divisibility step needed here.
- Packet 17 `lean_T/Tcount.lean`, lines 12-21 and 32-50: PP charged cost and multiplicity.
- Packet 17 `lean_T/Bridge.lean`, lines 22-35: charged count and existing prefix padding gadget.
- `../../../L1_retained_state/FRAMEWORK.md`, section 0: polynomial representation length is not
  polynomial representative count. The distinction remains binding.
- `../../../../notes/helper_state_compression.md`, sections 1, 7-10: R replaces whole paths in
  a restricted two-row model. None of that completeness is imported for arbitrary helpers.

Paths above are navigation descriptions relative to program structure; the script JSON pins its
own source/config hashes. The source definitions, rather than older prose objective summaries,
are load-bearing. No external theorem or web source is needed for the proofs below.

## 3. Legal right shifts never activate the scanner's zero truncation

Lemma 1. For any legal prefix from I, any nonnegative initial widths, and its exact row X_i,
the scan width u_i satisfies `||X_i||_1 <= 2^u_i`.

Proof. Initially every mass is 1. An addition of 2^s times another row has mass at most
`2^u_d+2^(u_s+s) <= 2^(1+max(u_d,u_s+s))`. A left shift multiplies mass by 2^n.
A negation preserves mass while its width increases. For a legal right shift by n, the nonzero
integer row before the shift is divisible by 2^n, so its mass is at least 2^n. The induction
hypothesis gives u_i >= n. Thus natural subtraction equals ordinary integer subtraction, and
the row's mass is divided by 2^n. Markers change neither quantity. Induction proves the claim.

The nonzero assumption is essential to THIS proof step. It holds for every reachable state here.
This does not authorize arbitrary right shifts: exact row divisibility is still checked separately.

## 4. Max-plus extraction and the two-parameter width formula

Let `-infinity` mean an absent term. Associate each current row with an influence vector
F_i in `(Z union {-infinity})^k`, initially F_ij=0 for i=j and -infinity otherwise.
The corresponding width expression is `max_j(z_j+F_ij)`.

- Left/right shifts add/subtract the amount to all finite entries of F_i.
- Negation adds 1 to them.
- Addition sets `F_dj=max(F_dj+1,F_sj+s+1)`.
- A marker changes nothing.

These rules exactly represent the unclamped scan. Lemma 1 proves that, for each natural initial
vector z, the unclamped scan agrees with the actual natural-number scan for a legal program.
Let h_j be the maximum F_ij over all rows i and all instants, INCLUDING initial time. Thus h_j>=0.
The total peak for arbitrary natural z is `max_j(z_j+h_j)`.

Define raw A=`max_{j<k-1} h_j` and B=`h_{k-1}`. Substitution of the balanced split yields

    child_P(w) = 1 + L + max(A,r+B).                         (1)

This proves the proposed form, including all scan-history effects. The shape follows from the
actual top-heavy split, not from a balanced-every-limb approximation.

Canonicalization. Put R=k-1, `a=max(A,B)` and `b=max(A,R+B)-R`.
Then `0<=b<=a` and `a-R<=b`. For every integer r in [0,R],

    max(A,r+B) = max(a,r+b).                                 (2)

Proof by the three cases B>=A, A>=R+B, and B<=A<=R+B. In the first case both sides are r+B;
in the second both are A; in the third (a,b)=(A,B). Endpoints determine the canonical pair:
`a=child(0)-1`, `b=child(R)-1-R`. Therefore canonical profiles are unique as WIDTH FUNCTIONS,
although raw influence pairs can be redundant.

Extraction requires O(number_of_ops*k) max/add operations, storing O(k^2) integers. Magnitudes
are bounded by the sum of shift amounts plus operation count, so bit length is polynomial in
the explicit instruction encoding. This does not bound the number of different profiles.

## 5. Exact padding closure and safe dominance

Theorem 2. For any legal complete table P with raw pair (A,B), prepend

    shiftL row0 p; shiftR row0 p;
    shiftL row(k-1) q; shiftR row(k-1) q.

Both divisions are legal; the gadget returns algebraic rows and CURRENT scan widths to their
initial values. Its only effect is to retain additional peaks z_0+p and z_(k-1)+q. Consequently
the resulting raw pair is `(max(A,p),max(B,q))`, and c is unchanged. Fixed targets, their order,
and restoration remain valid; the gadget adds no marker.

If Q's canonical profile `(c_Q,a_Q,b_Q)` is componentwise <= P's canonical profile `(c_P,a_P,b_P)`,
then Q's raw A_Q<=a_P (look at r=0) and raw B_Q<=b_P (look at r=R). Pad Q with p=a_P and q=b_P.
The resulting table has EXACTLY P's width map for every w and charge c_Q<=c_P.

Thus any recursive plan using P can replace its globally fixed table at that arity by this ONE
padded Q. All child widths, subsequent arities, multiplicities, leaf widths, and admissibility
tests remain identical, while every local cost weakly decreases. This proves a sound dominance
relation without assuming that the optimized continuation cost is monotone in width.

## 6. A complete fixed-KMY counterexample to one-scalar overhead

Two explicit legal PP k=3 tables consume exactly `0,infinity,-1,+1,-1/2` and return to I.
Both use the same reset constructions, except the insertion order for the first nontrivial target:

- Table P: `R0 -= R1; R0 += R2; mark -1`, then reverse those two additions.
- Table Q: `R0 += R2; R0 -= R1; mark -1`, then reverse those two additions.

Then both construct/mark/reset +1 by `R0 += R1; R0 += R2`, and construct/mark/reset -1/2 by
`R0 <<= 2; R0 -= 2 R1; R0 += R2`. Endpoint markers 0/infinity occur initially. Every right shift
is exact, and marker rows are respectively `(1,0,0),(0,0,1),(1,-1,1),(1,1,1),(4,-2,1)`.

Exact replay gives:

| Table | additions | charged c | a | b | child(30) | child(31) | child(32) |
|---|---:|---:|---:|---:|---:|---:|---:|
| P | 12 | 24 | 14 | 13 | 25 | 25 | 26 |
| Q | 12 | 24 | 14 | 14 | 25 | 26 | 27 |

Therefore `(c, overhead at widths divisible by k)` is not a sufficient planner summary. The
three-integer profile distinguishes them. This is not a proof that both are globally optimal;
indeed P dominates Q. It refutes unrestricted continuation equivalence of the scalar summary,
not existence of some optimum-preserving scalar representative chosen by a separate theorem.

Witness script and JSON: `profile_witness.2026-10-15T135900.py`,
`PROFILE_WITNESS.2026-10-15T135900.json`. Also checked 120 seeded closed legal schedules for
k=2..6 at 50 widths each, plus padding on both explicit fixed-KMY tables. All passed in 2.21 s.
The general theorem is supported by the proof, not inferred from these finite checks.

## 7. Uniform exact realization oracle under a requested profile cap

Input: k, fixed target list of q=2k-1 points, a canonical pair (a,b), and optionally a charged
budget C. Ask for the minimum charge of a complete table whose child function is <=
`floor(w/k)+1+max(a,(w mod k)+b)` for every w. Since (2) holds, the cap is equivalent to TWO tests:
the scan peak at w=0 is <=a, and at w=R is <=R+b.

Use a directed weighted state graph with nodes

    (X, u^0, u^R, S),

where X is the exact k-by-k integer row matrix, u^0 and u^R are current width arrays for initial
operand widths 0 and R, and S is the consumed-target subset. Start with X=I, width arrays
`(0,...,0)` and `(0,...,0,R)`, empty S. Apply each primitive operation to X and both width arrays;
reject illegal right shifts and any step exceeding either peak cap. Since every step is checked,
there is no need to retain separate peak accumulators. Mark an unconsumed required target when
an allowed exact marker row is present. Finish at X=I and full S, with arbitrary final width arrays.

Lemma 1 at w=0 gives `|X_ij| <= ||X_i||_1 <= 2^a`. Current entries satisfy
`0<=u_i^0<=a`, `0<=u_i^R<=R+b<=a+R`. Every left shift and legal right shift has amount <=a.
Every addition has exponent <=a-1 because its post-width at w=0 is at least s+1. Thus finite
branching is O(k^2(a+1)+qk), with no assumed helper-exponent bound.

A crude state count is

    (2^(a+1)+1)^(k^2) * (a+1)^k * (a+k)^k * 2^q
      = 2^O(k^2(a+1)+k log(a+k)+q).                         (3)

Many counted matrices are unreachable; that only makes this an upper bound. Use Dijkstra/0-cost
closure with weights 1 for plus, 3 for minus, 1 for negation, 0 for shifts and markers. Distances
and predecessors yield the minimum charge and a reconstructible witness. A budget C can prune
larger distances. Zero-cost cycles cause no correctness issue in a finite nonnegative graph.

Soundness: every returned path replays legally, respects both caps and target coverage, and
returns to identity; (1)-(2) give its all-width cap. Completeness: every legal table under that
cap maps to such a path; coefficient and exponent bounds were derived from the cap, not imposed
independently. Hence this is an exact oracle for the cap question.

Finally pad the returned witness with p=a,q=b. Its raw components are <=a,b by the endpoint
tests, so Theorem 2 realizes the requested canonical profile EXACTLY at the same charge.
Consequently the cap oracle also realizes a charged-minimal table with any specified canonical
width function. Exact-charge feasibility is a different question and is not needed for minimization.

Complexity: (3) is exponential in k^2*a; the arithmetic per state uses O(k^2*a) coefficient bits.
If a is binary-encoded, this is not polynomial in its bit length. The oracle is a genuine uniform
exact algorithm and explicit finite cap theorem, but it does not establish the required polynomial
realizability bound. A polynomial universe of requested triples alone does not make these graph
searches polynomial. The all-k recursive optimization endpoint remains OPEN.

## 8. Supporting additions-only exact edge family

For an arbitrary reachable retained matrix X and a nonzero exact marker v, put `c=v X^-1`
over D=Z[1/2], s=|supp(c)|. Any program from X that reaches v in any row needs at least s-1
additions (free signs/shifts in THIS supplementary objective). Equality holds iff every nonzero
c_i is a dyadic unit, provided marker unit scaling is allowed; the same unit condition suffices
for the exact unscaled integer marker.

Proof: form the causal DAG of the final target, suppressing unary unit scales. It has g binary
addition nodes and l distinct initial-row leaves, with l>=s. It is connected and has 2g input
edges, hence g>=l-1>=s-1. If the whole program has s-1 additions, equality forces g=s-1,l=s and
the underlying graph to be a tree. Each leaf then has one path to the root, so its coefficient
is a product of signed dyadic units. Conversely choose a nonzero c_j, scale row j by c_j, and
inject c_i times each remaining source row once. This gives s-1 additions. Clear temporary
denominators by dyadic row scales, then divide the resulting target row exactly to v; no cap is
claimed preserved. For s=1 the assertion reduces to free unit scaling.

If v is exact with odd common factor relative to X, do NOT weaken the condition to merely
pairwise dyadic-unit ratios: actual coefficients must be units. The claim fixes no other final
rows. For a one-row endpoint replacement it gives an exact edge when the changed row has unit
self coefficient and all other nonzero coefficients units; the construction leaves all other
rows unchanged. This supplementary edge family does not settle helper completeness, restore
the whole table, or replace charged-T/scan-width optimization.

## 9. Remaining obligations

- Prove a uniform polynomial-time realization/minimization method for achievable `(c,a,b)`, or
  an optimum-preserving restricted family covering it. The finite graph is exponential.
- Supply polynomial profile bounds for the intended binary/unary input convention and recursive
  incumbent. No such bound is inferred solely from polynomial explicit witness length.
- Independently review the analytical profile/padding/oracle proof and formalize its load-bearing
  legality and scanner bridge before headline promotion.
- PTP's recursive cost formula remains a separate missing model bridge.
