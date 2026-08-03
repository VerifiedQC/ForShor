# Modular Multiplication Bounds

This folder formalizes the error analysis for In-place classical-quantum modular multiplication. Algorithm 1 approximately implements

```text
|x> |0>  |->  |c*x mod N> |0>
```



## Main theorems

The single-call theorem is in `FinalModMul.lean`:

```lean
modMul_approx_valid_dist_uniform
```

It says that, for every valid normalized input state, Algorithm 1's approximate
controlled modular multiplication gate is within `stepErr K eta` of the ideal
controlled modular multiplication gate. The constant `K` is uniform: it does
not depend on the precision `eta`, the particular modular-multiplication
configuration, or the input state.

The modular-exponentiation theorem is in `ModExp.lean`:

```lean
modExpApprox_valid_dist_uniform
```

It applies the single-call theorem across the controlled modular
multiplications used in modular exponentiation, accumulating one error term per
exponent-control qubit.


## Algorithm 1 Proof Outline

### Step 1: Fractional Load Into The Work Register

This step computes a work-register value representing

```text
w = (((c - 1) * x) mod N) / N
```

up to `m` bits of precision. Operationally this is implemented using
Hadamards, a controlled phase product, and an inverse QFT. The analysis treats
the resulting work register as a QPE distribution around the target fraction.

Lean files:

- `Algorithm1Expansion.lean` expands `U1` on valid basis inputs.
- `Step1QPE.lean` proves the QPE tail estimate for the fractional load.
- `Step1Bound.lean` lifts that basis-state estimate to arbitrary valid unit states 
<!-- and also prepares the matching Step 5 cleanup estimate. -->

The important conceptual split is between retained work labels, whose encoded
fractions are close enough to `w`, and discarded labels, whose total norm is
bounded by the QPE tail estimate.

### Step 2: Add `N*w` To The Data Register
Step 2 then uses the work value to transform the data register approximately
as

```text
|x> |w>  |->  |x + N*w> |w>.
```

For retained work labels, `N*w` is close enough to `((c - 1) * x) mod N` that
the resulting data value is close to either `c*x mod N` or `c*x mod N + N`.

Lean file:

- `Step2Bound.lean`

This file proves the quantitative Fourier stability bound for Step 2. It first
proves the estimate for one retained work label, then recombines the orthogonal
work-label components to obtain the uniform Step 2 error theorem.

### Steps 3 And 4: Exact Conditional Subtraction And Flag Cleanup

Step 3 checks whether the grown data register is at least `N` and
subtracts `N` if needed. Step 4 uncomputes the comparison flag. These are not
approximation steps in this proof.

Lean file:

- `Step34Exact.lean`

The focus theorem is:

```lean
alg1_step34_reference_exact
```

It proves that the reference state after Step 2 is transformed exactly into the
reference state after Steps 3 and 4. The core arithmetic lemma is
`alg1_step3_reduces_to_modmul`, which uses the fact that the Step 2 value is
below `2*N`, so one conditional subtraction is enough.

### Step 5: Uncompute The Work Register

Step 5 subtracts the inverse fractional value from the work register
so that the work register returns to `|0>`. The Lean proof relates this cleanup
to the same QPE tail bound used for Step 1.

Lean file:

- `Step1Bound.lean`

This is why Step 5 does not have a separate file: the Step 1 and Step 5 errors
are controlled by the same fractional-load/QPE estimate, just viewed on
opposite sides of the exact modular multiplication map.

### Final Assembly

Lean file:

- `FinalModMul.lean`

This file combines:

- the Step 1 error bound,
- the Step 2 error bound,
- the Step 5 cleanup error bound,
- the exactness of Steps 3 and 4,
- unitary norm preservation,
- and a three-link triangle inequality.

The result is `modMul_approx_valid_dist_uniform`.