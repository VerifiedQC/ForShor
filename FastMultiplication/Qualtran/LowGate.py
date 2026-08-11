"""Qualtran implementations of ForShor LowGate arithmetic operators.

This module is self-contained apart from its Qualtran dependency.  It implements
exact Qualtran Bloqs corresponding to the four arithmetic constructors in
ForShor's `LowGate` language:

    ShiftL    : ExtReg -> Nat -> LowGate
    ShiftR    : ExtReg -> Nat -> LowGate
    Negate    : ExtReg -> LowGate
    AddScaled : ExtReg -> ExtReg -> Bool -> Nat -> LowGate

Semantic conventions
--------------------
* Active registers are interpreted as fixed-width two's-complement integers.
* Qualtran's QInt is big-endian (MSB at index 0).
* ForShor's `Reg.qubits` list is logical-bit-order / LSB-first, so a later
  Lean->Qualtran translator must reverse `r.active.qubits` when wiring a Lean
  active register into one of these QInt registers.
* ShiftL and ShiftR are defined as total reversible permutations.  On the
  subspaces promised by ForShor's Lean semantics, they coincide exactly with
  multiplication/division by powers of two.
"""

from functools import cached_property

from attrs import frozen

from qualtran import Bloq, BloqBuilder, QInt, Register, Signature
from qualtran.bloqs.arithmetic import Add
from qualtran.bloqs.arithmetic import Negate as QualtranNegate
from qualtran.bloqs.basic_gates import CNOT
import numpy as np
import sympy
from qualtran.bloqs.basic_gates import CNOT, CZPowGate, Toffoli

# ============================================================================
# Fixed-width two's-complement helpers
# ============================================================================


def _check_bitsize(bitsize: int) -> None:
    if not isinstance(bitsize, int) or bitsize <= 0:
        raise ValueError(f"bitsize must be a positive integer, got {bitsize!r}")


def _check_shift(shift: int) -> None:
    if not isinstance(shift, int) or shift < 0:
        raise ValueError(f"shift must be a nonnegative integer, got {shift!r}")


def tc_wrap(bitsize: int, value: int) -> int:
    """Wrap `value` to a signed `bitsize`-bit two's-complement integer.

    This is the Python analogue of ForShor's `tcWrapInt bitsize value`.
    """
    _check_bitsize(bitsize)
    modulus = 1 << bitsize
    unsigned = int(value) % modulus
    sign_threshold = 1 << (bitsize - 1)
    return unsigned - modulus if unsigned >= sign_threshold else unsigned


def fits_signed(bitsize: int, value: int) -> bool:
    """Whether `value` lies in the signed `bitsize`-bit two's-complement range."""
    _check_bitsize(bitsize)
    lo = -(1 << (bitsize - 1))
    hi = 1 << (bitsize - 1)
    return lo <= int(value) < hi


def _to_unsigned(bitsize: int, value: int) -> int:
    return int(value) % (1 << bitsize)


def _to_bits_be(bitsize: int, value: int) -> list[int]:
    """Return the two's-complement bit pattern MSB-first (Qualtran order)."""
    unsigned = _to_unsigned(bitsize, value)
    return [
        (unsigned >> (bitsize - 1 - i)) & 1
        for i in range(bitsize)
    ]


def _from_bits_be(bits: list[int]) -> int:
    """Interpret an MSB-first bit list as a signed two's-complement integer."""
    if not bits:
        raise ValueError("cannot decode an empty signed bit-vector")

    unsigned = 0
    for bit in bits:
        unsigned = (unsigned << 1) | int(bit)
    return tc_wrap(len(bits), unsigned)


# ============================================================================
# Total reversible shift permutations
# ============================================================================


def _shift_left_permutation(bitsize: int, shift: int, value: int) -> int:
    """Total reversible completion used by `ForShorShiftL`.

    For 0 < shift < bitsize:
      1. cyclically rotate the bit-vector left by `shift`;
      2. XOR the new sign bit into each of the `shift` wrapped low bits.

    On inputs satisfying ForShor's no-overflow promise this equals
        value * 2**shift.

    If shift >= bitsize, the Lean promise can hold only for value == 0, so we
    choose the identity as a simple reversible completion outside that promise.
    """
    _check_bitsize(bitsize)
    _check_shift(shift)

    value = tc_wrap(bitsize, value)
    if shift == 0 or shift >= bitsize:
        return value

    bits = _to_bits_be(bitsize, value)

    # Logical left rotation.  This is only a wire permutation in the Qualtran
    # decomposition; no SWAP Bloqs are required at this abstraction level.
    bits = bits[shift:] + bits[:shift]

    # Under the Lean no-overflow promise, every wrapped bit equals the new sign
    # bit.  XORing with that sign therefore turns the wrapped suffix into zeros.
    sign = bits[0]
    for i in range(bitsize - shift, bitsize):
        bits[i] ^= sign

    return _from_bits_be(bits)


def _shift_right_permutation(bitsize: int, shift: int, value: int) -> int:
    """Exact inverse of `_shift_left_permutation`.

    For 0 < shift < bitsize:
      1. XOR the current sign bit into each of the lowest `shift` bits;
      2. cyclically rotate right by `shift`.

    On inputs satisfying ForShor's exact-divisibility promise this equals
        value / 2**shift.
    """
    _check_bitsize(bitsize)
    _check_shift(shift)

    value = tc_wrap(bitsize, value)
    if shift == 0 or shift >= bitsize:
        return value

    bits = _to_bits_be(bitsize, value)

    sign = bits[0]
    for i in range(bitsize - shift, bitsize):
        bits[i] ^= sign

    bits = bits[-shift:] + bits[:-shift]
    return _from_bits_be(bits)

# ============================================================================
# Signed phase-product helpers
# ============================================================================


def _signed_bit_weight(bitsize: int, index_be: int) -> int:
    """Two's-complement weight of a Qualtran QInt bit.

    Qualtran QInt bits are MSB-first.

    For example, QInt(4) has bit weights

        index:   0   1   2   3
        weight: -8   4   2   1

    because index 0 is the sign bit.
    """
    _check_bitsize(bitsize)

    if not 0 <= index_be < bitsize:
        raise ValueError(
            f"bit index {index_be} outside QInt({bitsize})"
        )

    if index_be == 0:
        return -(1 << (bitsize - 1))

    return 1 << (bitsize - 1 - index_be)


def _phase_product_exponent(
    phi,
    x_weight: int,
    z_weight: int,
):
    """Exponent t for CZPowGate(t).

    CZPowGate(t) contributes

        exp(i * pi * t)

    on |11>.

    We require

        exp(i * phi * x_weight * z_weight),

    hence

        t = phi * x_weight * z_weight / pi.
    """
    return sympy.simplify(
        sympy.sympify(phi)
        * x_weight
        * z_weight
        / sympy.pi
    )

# ============================================================================
# LowGate.ShiftL
# ============================================================================


@frozen
class ForShorShiftL(Bloq):
    """Qualtran realization of `LowGate.ShiftL`.

    Lean specification on computational-basis inputs:

        FitsSignedWidth(bitsize, 2**shift * x)
        ------------------------------------------------
        ShiftL(x) = 2**shift * x

    The Bloq itself is a total unitary permutation, implemented by rewiring plus
    `shift` CNOTs when 0 < shift < bitsize.
    """

    bitsize: int
    shift: int

    def __attrs_post_init__(self) -> None:
        _check_bitsize(self.bitsize)
        _check_shift(self.shift)

    @cached_property
    def signature(self) -> Signature:
        return Signature([Register("r", QInt(self.bitsize))])

    def on_classical_vals(self, r: int) -> dict[str, int]:
        return {
            "r": _shift_left_permutation(self.bitsize, self.shift, int(r))
        }

    def build_composite_bloq(self, bb: BloqBuilder, r):
        if self.shift == 0 or self.shift >= self.bitsize:
            return {"r": r}

        bits = list(bb.split(r))  # MSB first for QInt.

        # Cyclic left rotation is a pure reordering of quantum variables.
        bits = bits[self.shift:] + bits[:self.shift]

        # Clear the wrapped sign-extension bits reversibly.
        for i in range(self.bitsize - self.shift, self.bitsize):
            bits[0], bits[i] = bb.add(
                CNOT(), ctrl=bits[0], target=bits[i]
            )

        r = bb.join(bits, dtype=QInt(self.bitsize))
        return {"r": r}

    def adjoint(self) -> Bloq:
        return ForShorShiftR(self.bitsize, self.shift)

    def __str__(self) -> str:
        return f"ForShorShiftL({self.bitsize}, {self.shift})"


# ============================================================================
# LowGate.ShiftR
# ============================================================================


@frozen
class ForShorShiftR(Bloq):
    """Qualtran realization of `LowGate.ShiftR`.

    Lean specification on computational-basis inputs:

        x = 2**shift * q     and     FitsSignedWidth(bitsize, q)
        ---------------------------------------------------------
        ShiftR(x) = q

    This Bloq is the exact adjoint/inverse of `ForShorShiftL` on the entire
    Hilbert space, not merely on the Lean-promised subspace.
    """

    bitsize: int
    shift: int

    def __attrs_post_init__(self) -> None:
        _check_bitsize(self.bitsize)
        _check_shift(self.shift)

    @cached_property
    def signature(self) -> Signature:
        return Signature([Register("r", QInt(self.bitsize))])

    def on_classical_vals(self, r: int) -> dict[str, int]:
        return {
            "r": _shift_right_permutation(self.bitsize, self.shift, int(r))
        }

    def build_composite_bloq(self, bb: BloqBuilder, r):
        if self.shift == 0 or self.shift >= self.bitsize:
            return {"r": r}

        bits = list(bb.split(r))  # MSB first for QInt.

        # Undo the sign correction used by ShiftL.
        for i in range(self.bitsize - self.shift, self.bitsize):
            bits[0], bits[i] = bb.add(
                CNOT(), ctrl=bits[0], target=bits[i]
            )

        # Undo ShiftL's cyclic left rotation.
        bits = bits[-self.shift:] + bits[:-self.shift]

        r = bb.join(bits, dtype=QInt(self.bitsize))
        return {"r": r}

    def adjoint(self) -> Bloq:
        return ForShorShiftL(self.bitsize, self.shift)

    def __str__(self) -> str:
        return f"ForShorShiftR({self.bitsize}, {self.shift})"


# ============================================================================
# LowGate.Negate
# ============================================================================


@frozen
class ForShorNegate(Bloq):
    """Qualtran realization of `LowGate.Negate`.

    Implements the exact ForShor modular semantics

        r := tcWrapInt(bitsize, -r).

    Qualtran's arithmetic `Negate(QInt(bitsize))` already implements this
    two's-complement operation, so this class is just a ForShor-named wrapper.
    """

    bitsize: int

    def __attrs_post_init__(self) -> None:
        _check_bitsize(self.bitsize)

    @cached_property
    def signature(self) -> Signature:
        return Signature([Register("r", QInt(self.bitsize))])

    def on_classical_vals(self, r: int) -> dict[str, int]:
        return {"r": tc_wrap(self.bitsize, -int(r))}

    def build_composite_bloq(self, bb: BloqBuilder, r):
        r = bb.add(QualtranNegate(QInt(self.bitsize)), x=r)
        return {"r": r}

    def adjoint(self) -> Bloq:
        # Two's-complement negation is an involution, including the minimum
        # representable value, which maps to itself modulo 2**bitsize.
        return self

    def __str__(self) -> str:
        return f"ForShorNegate({self.bitsize})"


# ============================================================================
# LowGate.AddScaled
# ============================================================================


@frozen
class ForShorAddScaled(Bloq):
    """Qualtran realization of `LowGate.AddScaled`.

    Implements

        dst := tcWrapInt(
            dst_bitsize,
            dst + sign * 2**shift * src,
        )

    where `sign = -1` when `neg_src` is true and `+1` otherwise.  `src` is
    preserved.

    The decomposition uses one clean `dst_bitsize`-qubit temporary register:
      1. coherently build `2**shift * sign_extend(src)` into the temporary;
      2. optionally negate the temporary;
      3. add the temporary into `dst` with Qualtran's equal-width signed Add;
      4. undo steps 2 and 1 and free the clean temporary.

    This deliberately avoids Qualtran mixed-width signed `Add`, whose narrower
    operand is zero-extended rather than sign-extended.
    """

    dst_bitsize: int
    src_bitsize: int
    neg_src: bool
    shift: int

    def __attrs_post_init__(self) -> None:
        _check_bitsize(self.dst_bitsize)
        _check_bitsize(self.src_bitsize)
        _check_shift(self.shift)
        if not isinstance(self.neg_src, bool):
            raise ValueError(f"neg_src must be bool, got {self.neg_src!r}")

    @cached_property
    def signature(self) -> Signature:
        return Signature([Register("dst", QInt(self.dst_bitsize)), Register("src", QInt(self.src_bitsize))])

    def on_classical_vals(self, dst: int, src: int) -> dict[str, int]:
        coefficient = -1 if self.neg_src else 1
        dst_out = tc_wrap(self.dst_bitsize,int(dst) + coefficient * (1 << self.shift) * int(src))
        return {"dst": dst_out, "src": int(src)}

    def _copy_map(self) -> list[tuple[int, int]]:
        """CNOT map for constructing shifted sign-extension of `src`.

        Returns `(src_index, tmp_index)` pairs in Qualtran's MSB-first indexing.
        The resulting temporary represents

            tcWrapInt(dst_bitsize, 2**shift * src).

        This works for every relationship between src_bitsize and dst_bitsize.
        """
        mapping: list[tuple[int, int]] = []

        for tmp_index in range(self.dst_bitsize):
            # Numerical bit position in the destination, counted from LSB=0.
            tmp_bit_position = self.dst_bitsize - 1 - tmp_index

            # Multiplication by 2**shift leaves these low bits equal to zero.
            src_bit_position = tmp_bit_position - self.shift
            if src_bit_position < 0:
                continue

            if src_bit_position >= self.src_bitsize:
                # Infinite two's-complement sign extension.
                src_index = 0
            else:
                # Convert LSB-oriented position to Qualtran MSB-first index.
                src_index = self.src_bitsize - 1 - src_bit_position

            mapping.append((src_index, tmp_index))

        return mapping

    def build_composite_bloq(self, bb: BloqBuilder, dst, src):
        dst_dtype = QInt(self.dst_bitsize)
        src_dtype = QInt(self.src_bitsize)

        # ------------------------------------------------------------------
        # Compute a clean destination-width copy of
        #     2**shift * sign_extend(src)    (mod 2**dst_bitsize).
        # ------------------------------------------------------------------
        tmp = bb.allocate(dtype=dst_dtype)

        src_bits = list(bb.split(src))
        tmp_bits = list(bb.split(tmp))
        mapping = self._copy_map()

        for src_index, tmp_index in mapping:
            src_bits[src_index], tmp_bits[tmp_index] = bb.add(
                CNOT(),
                ctrl=src_bits[src_index],
                target=tmp_bits[tmp_index],
            )

        src = bb.join(src_bits, dtype=src_dtype)
        tmp = bb.join(tmp_bits, dtype=dst_dtype)

        # Convert +scaled-src to -scaled-src when requested.
        if self.neg_src:
            tmp = bb.add(QualtranNegate(dst_dtype), x=tmp)

        # Equal-width signed Add has the desired modular two's-complement
        # semantics and leaves `tmp` unchanged.
        tmp, dst = bb.add(
            Add(a_dtype=dst_dtype, b_dtype=dst_dtype),
            a=tmp,
            b=dst,
        )

        # Restore the positive temporary before uncomputing its CNOT copy.
        if self.neg_src:
            tmp = bb.add(QualtranNegate(dst_dtype), x=tmp)

        src_bits = list(bb.split(src))
        tmp_bits = list(bb.split(tmp))

        for src_index, tmp_index in reversed(mapping):
            src_bits[src_index], tmp_bits[tmp_index] = bb.add(
                CNOT(),
                ctrl=src_bits[src_index],
                target=tmp_bits[tmp_index],
            )

        src = bb.join(src_bits, dtype=src_dtype)
        tmp = bb.join(tmp_bits, dtype=dst_dtype)
        bb.free(tmp)

        return {"dst": dst, "src": src}

    def adjoint(self) -> Bloq:
        # The inverse of dst += c*src is dst -= c*src.
        return ForShorAddScaled(
            dst_bitsize=self.dst_bitsize,
            src_bitsize=self.src_bitsize,
            neg_src=not self.neg_src,
            shift=self.shift,
        )

    def __str__(self) -> str:
        sign = "-" if self.neg_src else "+"
        return (
            f"ForShorAddScaled(dst={self.dst_bitsize}, src={self.src_bitsize}, "
            f"{sign}2^{self.shift})"
        )

# ============================================================================
# LowGate.Naive_SignedPhaseProd
# ============================================================================


@frozen
class ForShorNaiveSignedPhaseProd(Bloq):
    """Qualtran realization of `LowGate.Naive_SignedPhaseProd`.

    On a computational-basis state |x>|z>, this implements

        |x>|z>
            ->
        exp(i * phi * x * z) |x>|z>,

    where x and z are signed two's-complement integers.

    The implementation expands

        x = sum_i wx[i] * x_i
        z = sum_j wz[j] * z_j

    and therefore

        phi * x * z
            =
        sum_{i,j} phi * wx[i] * wz[j] * x_i * z_j.

    Each term is implemented with a CZPowGate between one x bit
    and one z bit.
    """

    phi: object
    x_bitsize: int
    z_bitsize: int
    eps: float = 1e-10

    def __attrs_post_init__(self) -> None:
        _check_bitsize(self.x_bitsize)
        _check_bitsize(self.z_bitsize)

        if self.eps <= 0:
            raise ValueError(
                f"eps must be positive, got {self.eps!r}"
            )

    @cached_property
    def signature(self) -> Signature:
        return Signature([Register("x", QInt(self.x_bitsize)), Register("z", QInt(self.z_bitsize))])

    def build_composite_bloq(self, bb: BloqBuilder, x,z):
        x_dtype = QInt(self.x_bitsize)
        z_dtype = QInt(self.z_bitsize)

        x_bits = list(bb.split(x))
        z_bits = list(bb.split(z))

        for i in range(self.x_bitsize):
            wx = _signed_bit_weight(self.x_bitsize, i)

            for j in range(self.z_bitsize):
                wz = _signed_bit_weight(self.z_bitsize, j)
                exponent = _phase_product_exponent(self.phi, wx, wz)

                # Avoid inserting an unnecessary identity rotation when phi is concretely zero.
                if exponent == 0:
                    continue

                pair = np.array([x_bits[i], z_bits[j]], dtype=object)
                pair = bb.add(CZPowGate(exponent=exponent, eps=self.eps), q=pair)

                x_bits[i] = pair[0]
                z_bits[j] = pair[1]

        x = bb.join(x_bits, dtype=x_dtype)
        z = bb.join(z_bits, dtype=z_dtype)

        return {"x": x, "z": z}

    def adjoint(self) -> Bloq:
        # Conjugating exp(i phi xz) gives exp(-i phi xz).
        return ForShorNaiveSignedPhaseProd(
            phi=-sympy.sympify(self.phi),
            x_bitsize=self.x_bitsize, z_bitsize=self.z_bitsize,
            eps=self.eps
        )

    def __str__(self) -> str:
        return (
            "ForShorNaiveSignedPhaseProd("
            f"phi={self.phi}, "
            f"x={self.x_bitsize}, "
            f"z={self.z_bitsize})"
        )
    
# ============================================================================
# Pure classical sanity tests
# ============================================================================


def run_self_tests(max_bitsize: int = 6) -> None:
    """Exhaustive small-width checks of the ForShor arithmetic semantics."""
    if max_bitsize <= 0:
        raise ValueError("max_bitsize must be positive")

    # ShiftL / ShiftR: total inverse property + Lean promised semantics.
    for bitsize in range(1, max_bitsize + 1):
        lo = -(1 << (bitsize - 1))
        hi = 1 << (bitsize - 1)
        values = range(lo, hi)

        for shift in range(0, bitsize + 2):
            shl = ForShorShiftL(bitsize, shift)
            shr = ForShorShiftR(bitsize, shift)

            for x in values:
                y = shl.on_classical_vals(x)["r"]
                x_back = shr.on_classical_vals(y)["r"]
                assert x_back == x, (
                    "Shift inverse failure",
                    bitsize,
                    shift,
                    x,
                    y,
                    x_back,
                )

                expected_left = (1 << shift) * x
                if fits_signed(bitsize, expected_left):
                    assert y == expected_left, (
                        "ShiftL Lean-spec failure",
                        bitsize,
                        shift,
                        x,
                        y,
                        expected_left,
                    )

            for q in values:
                x = (1 << shift) * q
                if fits_signed(bitsize, x):
                    got = shr.on_classical_vals(x)["r"]
                    assert got == q, (
                        "ShiftR Lean-spec failure",
                        bitsize,
                        shift,
                        x,
                        got,
                        q,
                    )

    # Negate: exact tcWrapInt semantics.
    for bitsize in range(1, max_bitsize + 1):
        lo = -(1 << (bitsize - 1))
        hi = 1 << (bitsize - 1)
        neg = ForShorNegate(bitsize)

        for x in range(lo, hi):
            got = neg.on_classical_vals(x)["r"]
            assert got == tc_wrap(bitsize, -x)
            assert neg.on_classical_vals(got)["r"] == x

    # AddScaled: exact modular semantics, including mixed widths and signs.
    test_max = min(max_bitsize, 5)  # keep exhaustive startup tests inexpensive
    for dst_bitsize in range(1, test_max + 1):
        dst_lo = -(1 << (dst_bitsize - 1))
        dst_hi = 1 << (dst_bitsize - 1)

        for src_bitsize in range(1, test_max + 1):
            src_lo = -(1 << (src_bitsize - 1))
            src_hi = 1 << (src_bitsize - 1)

            for neg_src in (False, True):
                coefficient = -1 if neg_src else 1

                for shift in range(0, test_max + 2):
                    bloq = ForShorAddScaled(
                        dst_bitsize,
                        src_bitsize,
                        neg_src,
                        shift,
                    )

                    # Check the CNOT map used by the *decomposition* really
                    # constructs the shifted, sign-extended source modulo the
                    # destination width.
                    mapping = bloq._copy_map()
                    for src in range(src_lo, src_hi):
                        src_bits = _to_bits_be(src_bitsize, src)
                        tmp_bits = [0] * dst_bitsize
                        for src_index, tmp_index in mapping:
                            tmp_bits[tmp_index] ^= src_bits[src_index]
                        tmp_value = _from_bits_be(tmp_bits)
                        assert tmp_value == tc_wrap(
                            dst_bitsize, (1 << shift) * src
                        )

                    for dst in range(dst_lo, dst_hi):
                        for src in range(src_lo, src_hi):
                            out = bloq.on_classical_vals(dst=dst, src=src)
                            expected = tc_wrap(
                                dst_bitsize,
                                dst + coefficient * (1 << shift) * src,
                            )
                            assert out["dst"] == expected
                            assert out["src"] == src

                            inv = bloq.adjoint()
                            restored = inv.on_classical_vals(
                                dst=out["dst"], src=out["src"]
                            )
                            assert restored == {"dst": dst, "src": src}

    print(
        "All ForShor LowGate arithmetic self-tests passed "
        f"(widths <= {max_bitsize})."
    )


if __name__ == "__main__":
    run_self_tests()