# Saturation implementation and polynomial-bound clarifications

This additive note accompanies SATURATION_AND_SINGLE_EXP_FPT.2026-10-15T190800.md. No earlier artifact is modified.

## Exact weighted budget

In Section7's normalized word search, prune every prefix whose accumulated charge exceeds C, with positive add=1, negative add=3, negation=1. The bound of at most C charged macros is a necessary length bound, not a replacement for the weighted-budget test. Both the imported normalized search and the theorem retain the weighted budget; this sentence makes the implementation requirement explicit.

## Why closing intercluster gaps alone does not prove polynomial saturation

Cluster translations preserve a single signed-power identity, but the SAME instruction exponent variables appear in many identities and scanner paths. Those identities' translations therefore cannot generally be chosen independently.

This already fails for the generic exact signed-power system

    2^(x1)-2=0,
    2^(x2)-2=0,
    2^(x_(i+2))-2^(x_(i+1)+x_i)=0,  i>=1.

Every equation has just two terms, all terms have coefficient+1 or-1, every nonconstant exponent has variable coefficients0 or1, and each true signature has a single zero-gap cancellation cluster. Nevertheless the system forces x1=x2=1 and Fibonacci growth. There are no large intercluster gaps to close. Merely requiring polynomially many short clusters, or using the fact that path exponents are sums of instruction exponents, does not rule out exponential coordinates.

This is a generic symbolic-system obstruction ONLY. No embedding into necessary F2 optimum constraints has been proved, and no lower bound on actual theta follows. A polynomial threshold bound could still use a whole-table replacement that discards such coupled systems, or a theorem that the systems retained by some optimum have a more restricted matrix structure. Neither statement has been established.

## Optional instruction-count sharpening

The parity argument in Section3 also shows at most two primitive instructions per normalized addition: shifted-source add alone, destination-left-shift plus unshifted add, or unshifted add plus right division. Thus a cap-preserving normalized table has length at most2A+nu+(2k-1), rather than the earlier3A+nu+(2k-1). This observation is not needed for the saturation dimension or singly exponential parameter bound; those already count only the one free exponent per addition. It does not alter exact-profile padding obligations.

## Independent review status

The independent reviewer read the complete saturation note and reported no blocking defect, including the explicit constants, lower-dimensional convex argument, one-variable templates, and saturated XP consequence. The weighted-budget sentence above was its requested exposition clarification. Its earlier review also requested an immediate n-2<d rejection and literal ILP encoding size f0(k)+O(poly(k)log(n+1)); the former is explicit in the saturation algorithm, and the latter is absorbed by the FPT factor in both reports.

The result remains an exact singly exponential FPT theorem. Uniform polynomial time in growing k remains OPEN.
