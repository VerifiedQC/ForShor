# Primary-source verification of the integer-programming import

Source: Ravi Kannan, *Minkowski's Convex Body Theorem and Integer Programming*, Mathematics of Operations Research 12(3), 1987, 415–440, DOI [10.1287/moor.12.3.415](https://doi.org/10.1287/moor.12.3.415). Public [primary-paper scan](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Kannan/Kannan1.pdf).

The coordinator downloaded the scan through the deterministic `autoresearcher.fetch.url_download` adapter, with no model calls. Local `Kannan1987.source.pdf` SHA256: `408174c9db49c35050e84775e42e85a6b7499d335798b8ec1cbb0778631834c8`. It has 26 scanned pages and no usable text layer. Visual inspection used rendered pages 1, 2, 16–22; the relevant theorem is PDF page 18, printed page 432.

## Verified source statement

Theorem 5.4 bounds the integer-feasibility algorithm by O(t^(9t/2) s) arithmetic operations and O(t^(2t) s) bits per intermediate integer, where t is dimension and s is input length. Section 5, printed pages 430–431, describes preprocessing for boundedness and lower-dimensional feasible regions. Printed page 433 completes the runtime argument. The original integer-size bound is sufficient here; the improvement using Frank–Tardos is unnecessary.

## Application in this research

Using ordinary polynomial-time binary integer arithmetic, the two displayed bounds imply t^O(t) poly(s) bit complexity. In particular, multiplying the operation count by a quadratic bound in the intermediate bit length still gives t^O(t) times a fixed polynomial in s. This inference is separate from the verbatim source theorem; no unit-cost arithmetic assumption is being hidden.

The constructed ILPs have rational affine expressions cleared to integer coefficients, finite coordinate bounds, and exactly one integer variable for each distinct used arity. Equalities are allowed as pairs of inequalities. Lower dimension is therefore not an applicability obstruction. There are no separately quantified width variables.

The source algorithm need only decide feasibility. Given bounded offsets, recover a feasible vector by binary-searching coordinate bounds, fixing each selected coordinate before proceeding. This adds O(t log(n+1)) calls, with the same dimension and polynomial input lengths. Likewise binary-searching the integer objective adds O(log(U+1)) calls.

For the planner, t! <= U and hence t log t = O(log(U+1)). Thus this specific algorithm has polynomial cost in U. An arbitrary fixed-dimension algorithm with a larger parameter dependence would not justify this conclusion.

This verifies external import 5 of `../planner_astra/OUTER_ILP_REDUCTION.2026-10-15T144200.md`. It does not prove or assume polynomial table realization. No claim is made that this algorithm is practically efficient, nor polynomial in binary log(n).
