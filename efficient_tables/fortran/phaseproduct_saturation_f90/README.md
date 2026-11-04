# PhaseProduct saturation and coupled optimization (Fortran90)

This application implements saturation-based PhaseProduct thresholds and full coupled recursion-policy optimization through arity K, using Kannan SHORTEST and suffix-batch integer programming. Every repeated arity reuses the same literal table and profile; the arity sequence can increase or decrease. The repository cost model is unchanged. PhaseTripleProduct is not part of this application.

The solver checks every result by literal-table replay before printing `STATUS OPTIMAL`; the local saturation module is additionally validated by replay, including theta(3,1,11)=6.

## Build and run

From this directory:

```sh
python -B build.py --debug
python -B build.py
echo '&run n=60, kmax=3, use_bounds=.true. /' | ./build/release/phaseproduct_saturation
```

The build uses `gfortran` from `PATH`; `--compiler` or `FC` selects another GNU compiler. The release build uses `-O3`; debug enables bounds and integer-overflow checks. GNU's earliest standard switch is `-std=f95`, so the additional `tests/audit_f90.py` guard checks the required Fortran90 subset.

Input is the `run` namelist with positive `n`, positive `kmax`, and optional `use_bounds` (default true). K=1 permits only stopping; K=2 uses the proved complete single-arity specialization. Larger K uses the full coupled algorithm and may close early through a proved exact lower bound. Arity greater than the current width cannot contract. There are no time, node, or state-budget options. The mathematical charge limits inside threshold decisions are part of the exact algorithm.

`STATUS OPTIMAL` is printed only after final literal-table replay. `LEVEL` records are `(k,c,a,b,child,parent multiplicity)`; one `TABLE` and its `OP` records are emitted per used arity. Public widths, charges, indices, and outer coefficient encodings have checked native integer ranges; backend intermediate rational arithmetic is arbitrary precision. Unsupported range or allocation failure is an ERROR, never an infeasibility or optimum certificate. The solver APIs use module state and are not reentrant.

## Algorithm and bounds

The local engine constructs the proved saturation cap, decides charge-bounded feasibility exactly, and recovers thresholds by cap bisection. The frontend recovers every charge plateau and its full interval of free-padding offsets. A relaxed width/multiplicity DAG can exclude profiles only with a proved lower bound. A negative cap result can be reused only for contained caps and no larger charge.

The outer stage enumerates decorated arity words with one integer offset variable per distinct arity. Terminal integrality, strict contraction, profile intervals, and the exact objective become bounded integer linear constraints. Kannan's actual recursive SHORTEST and suffix-batch algorithm solves them. No monotone arity order or monotone continuation-cost assumption is imposed.

The local threshold bound is `2^{O(k^4 log(k+1))} poly(log n)`. The supplied-catalogue outer stage remains separately polynomial in the numerical input width and catalogue encoding, and the full route has `2^{O(K^4 log(K+1))} poly(n)` complexity in the ideal exact-arithmetic model. Our vertex-rounding preprocessing contributes `m^{O(t)}` to a generic bounded ILP. For this outer family, `m=O(log U)` and `t!<=U`, making both that factor and Kannan's `t^{O(t)}` uniformly polynomial in root-stop cost U. We do not claim generic polynomial dependence on arbitrary H-polytope row count m.

## Verification and measurement

`tests/test_frontend.py` independently enumerates finite catalogues. It includes a strict shared/unshared optimum gap and a case whose optimal arity sequence is `(3,4)`. Its widened fixture actually executes HKZ and suffix enumeration. These synthetic/restricted catalogue tests establish outer correctness, not unrestricted physical table optimality by themselves. `tests/test_local.py`, `tests/test_threshold_positive.py`, and `tests/test_backend.py` check the local and lattice layers; `tests/test_solver.py` independently replays the complete application output.

```sh
python -B tests/test_solver.py build/debug/phaseproduct_saturation
python -B tests/audit_f90.py
```
