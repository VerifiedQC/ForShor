# Independent audit: constructive thresholds and primitive scanner normalization

2026-10-15. Status: no blocking mathematical defect found in the k-only FPT threshold theorem or the scanner primitive-normalization theorem. The requested uniform growing-K polynomial-time optimizer remains OPEN. This is an independent adversarial review with the full proofs visible after preregistration, not blinded HG7 review and not a machine-checked proof.

## 1. Reviewed claims and exact verdict

Reviewed `../algorithm_astra/SYMBOLIC_THRESHOLD.2026-10-15T190000.md` and `../normalform_astra/PRIMITIVE_NORMAL_FORM.2026-10-15T145600.md`. Read the accepted gap-closure RESULT, its polynomial-witness proof, the pinned F2 CONTRACT, PROFILE_THEOREMS, the local KANNAN_APPLICABILITY source-verification record, and the historical `ShorOptimization_Polynomial/notes/primitive_normal_form.md`.

Accept the following theorem, conditional only on the explicitly imported and previously reviewed bounded-witness/profile facts and fixed-dimension integer-feasibility theorem:

For k>=2, 0<=d<k, 0<=C<=27k^3, one can compute theta(k,d,C) truncated at n-2 and return a compact complete legal realizing table when finite in

    2^(2^O(k^3)) poly(log(n+1))

bit time. The polynomial exponent on log(n+1) is absolute. Every writable helper, marker ordering, exact division prefix, exact repository F2 target and identity endpoint remains in scope. This is a local constructive FPT result with parameter k. It is not polynomial in growing k, not an implementation of the enormous enumeration, and not a proof that primitive helper states have a polynomial-size representative family.

Also accept the new normal-form theorem: any complete legal table has a replacement preserving each signed paid-operation count and exact markers/endpoints, with no larger scanner peak for every nonnegative initialization, and at most 3A+nu+(2k-1) instructions. Consequently a cap-minimum witness has O(k^3) instructions after the accepted charge ceiling. This result is not needed for the FPT theorem, which already uses the accepted O(k^4) bound.

## 2. Independence and preregistered falsifiers

`PREREGISTRATION.2026-10-15T145944.md` was written before either new proof was read. The parent had supplied the broad symbolic-exponent/linear-systems route; this is disclosed and prevents describing this review as blind. Before exposure to the author's cluster proof, I independently derived a different carry/cancellation-forest proof for signed-power zero equality and integrality. The full comparison below was performed after reading the author proof.

The preregistered failure modes were: restricted workspace/order; n-dependent skeleton length; pairwise-cancellation-only treatment; omission of fractional prefix legality; hidden n-dependent pattern counts/dimensions; scanner/range substitution; projective target substitution; uncharged expanded-matrix cost; unjustified optimization/witness recovery; unproved scanner transfer from the historical range theorem; and promotion of FPT to P. None was found in the reviewed final argument.

## 3. Independent second derivation of the algebraic reduction

Let S=sum_(i=1)^m epsilon_i 2^(E_i(x)), with epsilon_i in {-1,+1} and integer affine exponent forms E_i. Keep repeated occurrences distinct.

A carry/cancellation forest is built from the following reductions on the current signed monomials:

- Opposite signs at an equal exponent cancel.
- Equal signs at an equal exponent merge into one monomial of the same sign at exponent+1.

Both rules preserve the exact dyadic value and strictly decrease the number of terms. Each derived exponent can be represented by one leaf's affine exponent plus its carry depth, at most m. To certify a reduction it suffices to impose an affine equality between the two current exponents. Hence a forest of at most m reductions uses only finitely many affine equalities with constants bounded in terms of m.

**Zero equality.** If a concrete signed sum is zero, inspect its least surviving exponent e. Cancel opposite signs at e. If an odd nonzero multiplicity remains, division by 2^e makes that coefficient odd and every higher contribution even, contradicting zero. Otherwise merge same-sign pairs at e. Repeat. The process ends at the empty list, since every step reduces term count. Conversely any reduction to empty proves zero by preservation of value. Enumerating all forests therefore expresses zero equality as a finite union of integer-linear systems.

**Integrality.** Apply the same reasoning only while the least surviving exponent e is negative. If S is an integer, S/2^e is divisible by 2 and so an odd least coefficient again contradicts parity. Thus a reduction exists whose surviving roots all have exponent>=0. Conversely those inequalities make every surviving monomial integral, and the reductions preserved S. This proves the exact integrality equivalence, including cancellation among individually fractional terms.

The enumeration needs at most O(m) reduction choices with O(m^2) possible pairs per step and optional surviving-root selection. A conservative bound is 2^O(m log(m+1)) patterns. There are no extra unbounded variables: intermediate exponent forms can be substituted directly from leaves and integer carry depths. Adding exact target constants simply adds occurrences. This gives a second proof of the finite-disjunction principle used by the author, without relying on exponent-gap clustering.

## 4. Audit of the author's cluster proof

The zero-cluster proof uses the necessary strict bound 2^H>M. A lowest cluster whose maximum exponent is A has absolute sum <=M2^A, strictly below 2^B for the next cluster minimum B. The higher terms belong to the lattice 2^B Z, so the lower cluster must vanish if the whole sum does. This is valid for negative B as well: it concerns integer multiples of a positive rational lattice step, not an assumption that the individual terms are integers.

For integrality, the zero-coefficient anchor at exponent zero is essential. Every cluster below the anchor cluster has next minimum B<=0, so both the assumed integer total and every later cluster belong to 2^B Z. Peeling the lower cluster is valid. The anchored cluster has bounded relative exponents fixed by the small gaps; all clusters above it have positive exponents. Thus its finite rational integrality test is necessary and sufficient. Repeated exponents, carrying, exact zero, empty scalar entries, and anchor ties are all covered.

The number of patterns is bounded independently of n. With A_add<=C<=27k^3, each symbolic scalar list has <=2^A_add occurrences. Target subtraction and the integrality anchor add only constant-many occurrences. H=27k^3+2 is safely large. A cluster spans at most O(MH), so its finite arithmetic uses a k-only bit length even though actual absolute program exponents may be arbitrarily large before truncation.

## 5. Complete legal programs, prefix integrality and scanners

The accepted bounded-witness theorem applies to the cap minimum. If any charge<=C witness exists, the minimum-charge cap witness also satisfies C and the accepted O(k^4) length bound. Enumerating all primitive instruction types, distinct source/destination row indices, signs, and marker permutations therefore loses no legal table. All k rows are available. Separate nonnegative exponent coordinates permit arbitrary legal left shifts, right shifts and source shifts.

Symbolic replay expands each entry into signed powers with integer affine exponent forms. Each addition at most doubles the current maximum occurrence count; shifts alter exponents and negations alter signs. Integrality is required at every prefix. Because each elementary rational row operation is invertible, every prefix row is nonzero. An integral post-right-shift row means the preceding integral row was coefficientwise divisible by that exact shift power. Exact marker equations and final-I equations are imposed entrywise. No target rescaling or sign substitution is used.

The scanner formulation is sound despite using inequalities at max updates. Start the upper variables at the exact initial widths. The exact rational/algebraic constraints independently establish legal integral row prefixes. The mass invariant then proves no actual right shift clips: if a nonzero row is divided by 2^h exactly, its predivision mass is at least 2^h, forcing actual width>=h. Inductively actual widths remain <= the proposed U variables through both max inequalities and shift equalities. Capping every U at every prefix therefore caps the actual history peak. Conversely choose actual widths as U for any legal witness. Both directions are exact.

Capping every exponent by a is justified by the zero-initialized scanner, not by a conjectured helper bound. Both ends of a legal unary shift lie in [0,a], and a source-shift addition has postwidth at least h+1. Thus no allowed witness is excluded by h<=a. The two endpoint scans are precisely the previously established canonical-cap tests.

There is no hidden universal or alternating quantifier. After a finite pattern choice, all remaining variables are existential integer coordinates: the exponents, a, and O(kL) scanner bounds. Repeated appearances of one exponent use the same coordinate. Dimensions and constraint counts depend only on k.

## 6. Bit complexity and reconstruction

The number of skeletons is 2^poly(k). The number of scalar constraints is polynomial in k; each has <=2^O(k^3) occurrences. Multiplying their finite gap-pattern choices gives at most 2^(2^O(k^3)) systems. Their construction and constant-only cluster tests fit the same loose parameter bound.

The local KANNAN_APPLICABILITY record explicitly translates the imported arithmetic-operation and integer-size bounds into t^O(t) poly(s) bit time. Here t=poly(k); the ILP input length is a k-only quantity plus O(poly(k) log(n+1)). Repeated binary cap constants therefore introduce only a k-dependent factor. They do not make the exponent on log n depend on k. I inspected the existing source-verification record; I did not claim a second independent visual inspection of the primary scan.

Threshold decision is monotone in the cap. First decide at n-2, then binary-search the least feasible cap. Recover a feasible coordinate vector by bounded feasibility queries, fixing each chosen coordinate before continuing. Exponents and a are bounded by n; U variables by n+k. This requires only poly(k) log(n+k) additional feasibility calls. Output the instruction skeleton with binary exponent values. No expanded coefficient matrix is required.

A complete expanded trace may contain O(n)-bit entries, and printing or ordinary replay of those entries has an additional polynomial dependence on numeric n. The compact algorithm does not claim to print that trace in poly(log n) time. Short DSL output alone also does not establish binary-input NP verification without a separate certificate analysis.

Two harmless implementation clarifications, sent to the author: immediately return theta>n-2 when n-2<d; and write the input-length estimate with its poly(k) multiplicity of log(n+1). Neither changes the theorem.

## 7. Primitive scanner-normalization bridge and provenance

The historical `notes/primitive_normal_form.md` already proves the algebraic positive-power primitive-row transform under coefficient-range caps and different full-width paid prices. That result cannot be cited alone to preserve the current history scanner or its plus/minus/negation prices. The new paper supplies the missing scanner invariant explicitly and deserves credit as a port/strengthening, not as discovery of primitive normalization from nothing.

At every old boundary write X_i=2^g_i Y_i and v_i=u_i-g_i. The mass invariant gives v_i>=0 for every nonnegative initialization. Old unary shifts change g and u equally and disappear. Negation increments both old and new widths equally. Primitive exact targets retain g=0 at their markers.

For an old source exponent s, set e=s+g_h-g_d. If e>=0, the normalized add has predivision width u'_d-g_d<=u'_d and exact normalization restores v'_d=u'_d-g'_d. If e<0, left-shifting the destination by p=-e has width u_d-s-g_h<=u_d; the subsequent exponent-zero add has width u'_d-s-g_h<=u'_d. Exact normalization again yields the boundary invariant. Those algebraic equalities apply independently to every scanner initialization while using one and the same replacement program. This directly proves all-peak preservation and closes the historical model mismatch.

Signed additions and negations are reproduced individually, so the current asymmetric charge is preserved. Arbitrary helpers remain arbitrary primitive integer rows, not a prescribed basis completion. Identity endpoints have zero valuations. The O(k^3) minimum-witness length follows from 3A+nu+2k-1<=3c+2k-1 and the accepted charge ceiling.

The exact-loop-erasure argument is also valid: a marker-free exact matrix loop has rational transfer I, whose max-plus diagonal entries must be nonnegative by the stated coefficient bound; its final widths dominate its initial widths. Deletion cannot enlarge any future monotone scanner peak. This supplies no polynomial bound on distinct primitive states. Likewise the target-pair determinant divisibility observation does not prove an optimal whole table must visit such pairs. The new paper correctly limits both conclusions.

## 8. Independent finite checks and final boundary

`CARRY_CHECKS.2026-10-15T150500.json` records an independent deterministic parity-carry implementation compared against exact Python Fraction values:

- 111,111 exhaustive signed sums, lengths 0..5 and exponents -2..2;
- 10,000 seeded random sums, up to 49 terms and exponents -500..500;
- 24 structured long-carry cases, including 2,048 repeated occurrences.

Both zero equality and integrality matched in every case. These tests exercise the independently derived algebraic lemma. They do not execute the full ILP threshold algorithm, replace the proof, or certify the recursive optimizer.

Accepted advancement: constructive k-only FPT profile thresholds, plus a scanner-preserving global primitive normalization and sharper XP exponent. Combining the local result with the accepted outer theorem gives a parameter-dependent F(K) poly(n) complete shared-table optimizer under the numeric-n convention. The factor F(K) is enormous and is not bounded by a polynomial in K. The uniform growing-K P claim remains unproved.

Original sources and other agents' artifacts were not modified. Only new timestamped audit artifacts were written in this independent lane. No local inference was used.
