# Contract clarification and profile bounds

This addendum corrects CONTRACT.md's default-runtime sentence: the owner confirmed **growing K**, fixed F2, common child width, and one table per arity, but did **not** choose an encoding convention for n. Keep both objectives visible: polynomial in physical operand bitwidth n and K, and the stronger polynomial in log(n) and K when n is given in binary. Neither full exact synthesis theorem is established. The original local construction/synthesis question measures k in unary. Binary-n was an analyst default, not an owner instruction.

The benchmark's exact real-round evaluation is handled separately in the coordinating directory's `exact_rotation_cost.py`; this agent has not independently verified that proof or imported it as a premise of the constructive results.

For the parent's exact profile representation, the emitted C1 and paired tables have **constructible** profiles `(c,A,B)` with `W(w)=floor(w/k)+1+max(A,(w mod k)+B)`. The general profile theorem belongs to the helpers agent. Here `f2_profiles.py` computes these pairs by exact max-plus propagation and checks that the natural right shifts never clip for these constructors; `f2_profiles_bounded.py` records a bounded direct-scan cross-check, including operand widths near 2048 and 50000. These are local candidate-width values, not recursively optimized T-counts.

Both C1 and paired constructions admit A,B<=8k^2; C1 has c<=12k^2 and the positive-first paired constructor has c<=6k^2. The sharper exact charged formulas are in BRIDGES. These inequalities bound supplied incumbents; they do not prove every globally relevant optimal table lies in that profile box.

For the paired width bound, remove the currently active build shifts alpha_0,alpha_1 from accumulator widths. Each alpha is between0 and E=(k-1)e_max, and returns to0 at block end. Basis rows j>=2 are never written. The normalized row1 width gets contributions only from basis rows, with effective exponents at most E; after A1 additions into row1 it is at most cap+E+A1. Row0 has basis contributions bounded by cap+E, and connector contributions from row1 with effective exponent alpha_1-alpha_0+s<=E+1. Thus normalized row0 is at most cap+2E+1+A+nu. Restoring the active scale adds at most E. Choose all starting widths conservatively equal to cap=L+r. Including the final signed bit gives

    W <= L+r+3E+2+A+nu.

Setting r=0 in the exact profile representation bounds max(A_profile,B_profile)<=3E+1+A+nu. Since e_max<=k, addition count A<=3k^2, and nu<=3k-4, this is <=6k^2-3 and hence <=8k^2. The scalar cap calculation deliberately overestimates the untouched lower limbs. Right shifts remain exact by the constructive restoration argument; their normalized action is zero. There is no row0-to-row1 cross-coupling, which is the essential hypothesis of this constructor bound.

For charged count, each pair contributes at most4k-1 including its possible two marker negations; a singleton contributes at most4k-2. With q=M-2=2p+s<=3k-4 this gives

    c_pair <= (2k-1)q + (2k-1)s <= (2k-1)(3k-3) <=6k^2.

C1's exact count gives `c<=4(k-1)(3k-4)+(3k-4)<=12k^2`. Its general width lemma applied with all initial widths L+r gives `max(A_profile,B_profile)<=2E+2kM<=8k^2`. All bounds are paper proofs, independent of the sampled scan checks, and await independent review.

The first broad profile script was stopped before it wrote output because its dense exhaustive scans at k=96,128 were unnecessary for validating the exact symbolic computation. The successful bounded rerun declares its actual finite domain in the output. No failed assertion or incomplete search is represented as a proof.
