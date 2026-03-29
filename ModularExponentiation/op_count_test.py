from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional, Tuple, Union
import argparse
import math


# ============================================================
# Points
# ============================================================

@dataclass(frozen=True)
class IntPoint:
    z: int


@dataclass(frozen=True)
class InfPoint:
    pass


Point = Union[IntPoint, InfPoint]


# ============================================================
# High-level ops (valid_ops)
# ============================================================

@dataclass(frozen=True)
class ShiftL:
    i: int
    n: int


@dataclass(frozen=True)
class ShiftR:
    i: int
    n: int


@dataclass(frozen=True)
class Negate:
    i: int


@dataclass(frozen=True)
class AddScaled:
    dst: int
    src: int
    neg_src: bool
    shift: int


@dataclass(frozen=True)
class PhaseProduct:
    i: int


ValidOp = Union[ShiftL, ShiftR, Negate, AddScaled, PhaseProduct]


# ============================================================
# Low-level prim_ops
# ============================================================

@dataclass(frozen=True)
class Alloc:
    i: int
    lsb: bool
    n: int


@dataclass(frozen=True)
class Free:
    i: int
    lsb: bool
    n: int


@dataclass(frozen=True)
class PrimNegate:
    i: int


@dataclass(frozen=True)
class PrimAdd:
    dst: int
    src: int


@dataclass(frozen=True)
class PrimPhaseProduct:
    i: int


PrimOp = Union[Alloc, Free, PrimNegate, PrimAdd, PrimPhaseProduct]


# ============================================================
# Helpers
# ============================================================

def fin_zero(k: int) -> int:
    if k <= 0:
        raise ValueError("k must be positive")
    return 0


def nonzero_fins(k: int) -> List[int]:
    return list(range(1, k))


def popcount(n: int) -> int:
    return n.bit_count()


def highest_bit_index(n: int) -> int:
    if n <= 0:
        raise ValueError("highest_bit_index is only defined for positive n")
    return n.bit_length() - 1


# ============================================================
# Inversion
# ============================================================

def inv(op: ValidOp) -> ValidOp:
    if isinstance(op, ShiftL):
        return ShiftR(op.i, op.n)
    if isinstance(op, ShiftR):
        return ShiftL(op.i, op.n)
    if isinstance(op, Negate):
        return Negate(op.i)
    if isinstance(op, AddScaled):
        return AddScaled(op.dst, op.src, (not op.neg_src), op.shift)
    if isinstance(op, PhaseProduct):
        return PhaseProduct(op.i)
    raise TypeError(f"Unknown op: {op}")


def apply_op_inverse(p: List[ValidOp]) -> List[ValidOp]:
    return [inv(op) for op in reversed(p)]


# ============================================================
# Synthesis: shiftsOf / signedPow2Decomp / addConstFrom
# ============================================================

def shifts_of_aux(n: int, sh: int) -> List[int]:
    if n == 0:
        return []
    rest = shifts_of_aux(n // 2, sh + 1)
    if n % 2 == 1:
        return [sh] + rest
    return rest


def shifts_of(n: int) -> List[int]:
    if n < 0:
        raise ValueError("shifts_of expects n >= 0")
    return shifts_of_aux(n, 0)


def signed_pow2_decomp(c: int) -> List[Tuple[bool, int]]:
    if c == 0:
        return []
    neg = c < 0
    mag = abs(c)
    return [(neg, sh) for sh in shifts_of(mag)]


def pair_to_op(dst: int, src: int, pair: Tuple[bool, int]) -> AddScaled:
    neg, sh = pair
    return AddScaled(dst=dst, src=src, neg_src=neg, shift=sh)


def add_const_aux(dst: int, src: int, neg: bool, n: int, sh: int) -> List[ValidOp]:
    if n == 0:
        return []
    rest = add_const_aux(dst, src, neg, n // 2, sh + 1)
    if n % 2 == 1:
        return [AddScaled(dst=dst, src=src, neg_src=neg, shift=sh)] + rest
    return rest


def add_const_from(dst: int, src: int, c: int) -> List[ValidOp]:
    if c == 0:
        return []
    neg = c < 0
    n = abs(c)
    return add_const_aux(dst, src, neg, n, 0)


def compute_local2(k: int, z: int) -> List[ValidOp]:
    dst = fin_zero(k)
    out: List[ValidOp] = []
    for j in nonzero_fins(k):
        c = z ** j
        out.extend(add_const_from(dst, j, c))
    return out


def ops_for_point_with_product(k: int, pt: Point) -> List[ValidOp]:
    if isinstance(pt, InfPoint):
        last = k - 1
        return [PhaseProduct(last)]
    if isinstance(pt, IntPoint):
        dst = fin_zero(k)
        l = compute_local2(k, pt.z)
        return l + [PhaseProduct(dst)] + apply_op_inverse(l)
    raise TypeError(f"Unknown point: {pt}")


def gen_ops_with_product(k: int, points: List[Point]) -> List[ValidOp]:
    out: List[ValidOp] = []
    for pt in points:
        out.extend(ops_for_point_with_product(k, pt))
    return out


# ============================================================
# Width bookkeeping
# ============================================================

def get_len(cur_len: List[int], idx: int) -> int:
    return cur_len[idx] if 0 <= idx < len(cur_len) else 0


def set_len(cur_len: List[int], i: int, v: int) -> List[int]:
    out = list(cur_len)
    out[i] = v
    return out


def inc_len(cur_len: List[int], i: int, n: int) -> List[int]:
    return set_len(cur_len, i, get_len(cur_len, i) + n)


def dec_len(cur_len: List[int], i: int, n: int) -> List[int]:
    return set_len(cur_len, i, get_len(cur_len, i) - n)


# ============================================================
# Compilation
# ============================================================

def compile_op_to_prim_single(op: ValidOp, cur_len: List[int]) -> Tuple[List[PrimOp], List[int], List[Tuple[int, int]]]:
    if isinstance(op, ShiftL):
        return [Alloc(op.i, True, op.n)], inc_len(cur_len, op.i, op.n), []

    if isinstance(op, ShiftR):
        return [Free(op.i, True, op.n)], dec_len(cur_len, op.i, op.n), []

    if isinstance(op, Negate):
        return [PrimNegate(op.i)], list(cur_len), []

    if isinstance(op, PhaseProduct):
        return [PrimPhaseProduct(op.i)], list(cur_len), []

    if isinstance(op, AddScaled):
        dst = op.dst
        src = op.src
        neg_src = op.neg_src
        sh = op.shift

        if dst == src:
            return [], list(cur_len), []

        neg_ops: List[PrimOp] = [PrimNegate(src)] if neg_src else []
        cur_len1 = list(cur_len)

        shift_ops: List[PrimOp] = [] if sh == 0 else [Alloc(src, True, sh)]
        cur_len2 = inc_len(cur_len1, src, sh)

        len_dst = get_len(cur_len2, dst)
        len_src = get_len(cur_len2, src)
        target = 1 + max(len_dst, len_src)

        delta_dst = target - len_dst
        widen_dst_ops: List[PrimOp] = [] if delta_dst == 0 else [Alloc(dst, False, delta_dst)]
        cur_len3 = inc_len(cur_len2, dst, delta_dst)
        msb_adds = [] if delta_dst == 0 else [(dst, delta_dst)]

        delta_src = target - len_src
        widen_src_ops: List[PrimOp] = [] if delta_src == 0 else [Alloc(src, False, delta_src)]
        cur_len4 = inc_len(cur_len3, src, delta_src)

        adder: List[PrimOp] = [PrimAdd(dst, src)]

        free_src_ops: List[PrimOp] = [] if delta_src == 0 else [Free(src, False, delta_src)]
        cur_len5 = dec_len(cur_len4, src, delta_src)

        unshift_ops: List[PrimOp] = [] if sh == 0 else [Free(src, True, sh)]
        cur_len6 = dec_len(cur_len5, src, sh)

        unneg_ops: List[PrimOp] = list(neg_ops)
        cur_len7 = list(cur_len6)

        ops = neg_ops + shift_ops + widen_dst_ops + widen_src_ops + adder + free_src_ops + unshift_ops + unneg_ops
        return ops, cur_len7, msb_adds

    raise TypeError(f"Unknown high-level op: {op}")


def compile1(op: ValidOp, cur_len: List[int]) -> Tuple[List[PrimOp], List[int]]:
    ops, cur_len2, _ = compile_op_to_prim_single(op, cur_len)
    return ops, cur_len2


def compile_prog(ops: List[ValidOp], cur_len: List[int]) -> Tuple[List[PrimOp], List[int], List[Tuple[int, List[int]]]]:
    """
    Returns:
      - compiled prim ops
      - final cur_len
      - phase trace: list of (phase register, widths immediately before that phaseProduct)
    """
    out: List[PrimOp] = []
    cur = list(cur_len)
    phase_trace: List[Tuple[int, List[int]]] = []

    for op in ops:
        if isinstance(op, PhaseProduct):
            phase_trace.append((op.i, list(cur)))
        prims, cur = compile1(op, cur)
        out.extend(prims)

    return out, cur, phase_trace


# ============================================================
# Formula verification for .int z blocks
# ============================================================

@dataclass
class BlockCheck:
    block_index: int
    point: Point
    start_widths: List[int]
    actual_before_phase: List[int]
    predicted_exact_dst_width: int
    predicted_upper_bound_dst_width: int
    actual_dst_width: int
    ok_exact: bool
    ok_upper: bool
    m: int
    shifts: List[int]
    sources: List[int]


def extract_addscaled_sequence(ops: List[ValidOp]) -> List[AddScaled]:
    return [op for op in ops if isinstance(op, AddScaled)]


def exact_formula_width_before_phase(start_widths: List[int], add_ops: List[AddScaled]) -> int:
    """
    Exact formula from the previous message.

    If the add sequence is:
      (src_0, sh_0), ..., (src_{m-1}, sh_{m-1})
    and D0 is starting width of dst=0, then

      D_m = max( D0 + m, max_r (w[src_r] + sh_r + (m-r)) )

    where r is 0-based.
    """
    d0 = start_widths[0]
    m = len(add_ops)
    if m == 0:
        return d0

    candidates = [d0 + m]
    for r, op in enumerate(add_ops):
        a_r = start_widths[op.src] + op.shift
        candidates.append(a_r + (m - r))
    return max(candidates)


def upper_bound_width_before_phase(start_widths: List[int], add_ops: List[AddScaled]) -> int:
    """
    Safe upper bound:
      D_m <= m + max(D0, max_r(start_widths[src_r] + shift_r))
    """
    d0 = start_widths[0]
    m = len(add_ops)
    if m == 0:
        return d0

    max_a = max(start_widths[op.src] + op.shift for op in add_ops)
    return m + max(d0, max_a)


def popcount_formula_m(k: int, z: int) -> int:
    total = 0
    for j in range(1, k):
        total += popcount(abs(z) ** j)
    return total


def verify_by_blocks(k: int, points: List[Point], init_widths: List[int]) -> List[BlockCheck]:
    """
    Verifies the formula block-by-block against the actual widths produced by compilation.
    """
    cur = list(init_widths)
    checks: List[BlockCheck] = []

    for idx, pt in enumerate(points):
        block_ops = ops_for_point_with_product(k, pt)

        if isinstance(pt, InfPoint):
            # compile the block, record widths before phase
            _, cur_after, phase_trace = compile_prog(block_ops, cur)
            if len(phase_trace) != 1:
                raise RuntimeError("Expected exactly one phaseProduct in an .inf block")
            _, actual_before = phase_trace[0]

            checks.append(
                BlockCheck(
                    block_index=idx,
                    point=pt,
                    start_widths=list(cur),
                    actual_before_phase=actual_before,
                    predicted_exact_dst_width=cur[k - 1],
                    predicted_upper_bound_dst_width=cur[k - 1],
                    actual_dst_width=actual_before[k - 1],
                    ok_exact=(actual_before[k - 1] == cur[k - 1]),
                    ok_upper=(actual_before[k - 1] <= cur[k - 1]),
                    m=0,
                    shifts=[],
                    sources=[],
                )
            )
            cur = cur_after
            continue

        if not isinstance(pt, IntPoint):
            raise TypeError(f"Unknown point: {pt}")

        add_ops = extract_addscaled_sequence(compute_local2(k, pt.z))

        # actual
        _, cur_after, phase_trace = compile_prog(block_ops, cur)
        if len(phase_trace) != 1:
            raise RuntimeError("Expected exactly one phaseProduct in an .int block")
        phase_reg, actual_before = phase_trace[0]
        if phase_reg != 0:
            raise RuntimeError(f"Expected phase on register 0, got {phase_reg}")

        # predicted
        predicted_exact = exact_formula_width_before_phase(cur, add_ops)
        predicted_upper = upper_bound_width_before_phase(cur, add_ops)

        checks.append(
            BlockCheck(
                block_index=idx,
                point=pt,
                start_widths=list(cur),
                actual_before_phase=actual_before,
                predicted_exact_dst_width=predicted_exact,
                predicted_upper_bound_dst_width=predicted_upper,
                actual_dst_width=actual_before[0],
                ok_exact=(actual_before[0] == predicted_exact),
                ok_upper=(actual_before[0] <= predicted_upper),
                m=len(add_ops),
                shifts=[op.shift for op in add_ops],
                sources=[op.src for op in add_ops],
            )
        )

        cur = cur_after

    return checks


# ============================================================
# Parsing / pretty-printing
# ============================================================

def parse_points(s: str) -> List[Point]:
    out: List[Point] = []
    if not s.strip():
        return out
    for tok in s.split(","):
        t = tok.strip().lower()
        if t == "inf":
            out.append(InfPoint())
        else:
            out.append(IntPoint(int(t)))
    return out


def parse_widths(s: str, k: int) -> List[int]:
    """
    Examples:
      "5"         -> [5,5,5,5] if k=4
      "5,5,7,2"   -> exact list
    """
    toks = [x.strip() for x in s.split(",") if x.strip()]
    if len(toks) == 1:
        n = int(toks[0])
        return [n] * k
    widths = [int(x) for x in toks]
    if len(widths) != k:
        raise ValueError(f"Need either one width or exactly k={k} widths")
    return widths


def point_str(pt: Point) -> str:
    if isinstance(pt, InfPoint):
        return "inf"
    if isinstance(pt, IntPoint):
        return str(pt.z)
    return repr(pt)


def op_str(op: ValidOp) -> str:
    if isinstance(op, ShiftL):
        return f"shiftL({op.i}, {op.n})"
    if isinstance(op, ShiftR):
        return f"shiftR({op.i}, {op.n})"
    if isinstance(op, Negate):
        return f"negate({op.i})"
    if isinstance(op, AddScaled):
        sign = "-" if op.neg_src else "+"
        return f"addScaled(dst={op.dst}, src={op.src}, sign={sign}, sh={op.shift})"
    if isinstance(op, PhaseProduct):
        return f"phaseProduct({op.i})"
    return repr(op)


def prim_str(op: PrimOp) -> str:
    if isinstance(op, Alloc):
        end = "LSB" if op.lsb else "MSB"
        return f"Alloc({op.i}, {end}, {op.n})"
    if isinstance(op, Free):
        end = "LSB" if op.lsb else "MSB"
        return f"Free({op.i}, {end}, {op.n})"
    if isinstance(op, PrimNegate):
        return f"negate({op.i})"
    if isinstance(op, PrimAdd):
        return f"Add(dst={op.dst}, src={op.src})"
    if isinstance(op, PrimPhaseProduct):
        return f"phaseProduct({op.i})"
    return repr(op)


# ============================================================
# Demo / CLI
# ============================================================

def main() -> None:
    parser = argparse.ArgumentParser(description="Verify width formula before phaseProduct")
    parser.add_argument("--k", type=int, default=4, help="number of registers")
    parser.add_argument("--pts", type=str, default="2,3,inf,-1", help='comma-separated points, e.g. "2,3,inf,-1"')
    parser.add_argument("--widths", type=str, default="5", help='either one width or k widths, e.g. "5" or "5,5,6,7"')
    parser.add_argument("--show-high-ops", action="store_true")
    parser.add_argument("--show-prim-ops", action="store_true")
    args = parser.parse_args()

    k = args.k
    if k <= 0:
        raise ValueError("k must be positive")

    points = parse_points(args.pts)
    init_widths = parse_widths(args.widths, k)

    print("=" * 72)
    print("INPUT")
    print("=" * 72)
    print(f"k             = {k}")
    print(f"points        = {[point_str(p) for p in points]}")
    print(f"init_widths   = {init_widths}")

    high_ops = gen_ops_with_product(k, points)
    prim_ops, final_widths, phase_trace = compile_prog(high_ops, init_widths)

    print("\n" + "=" * 72)
    print("PROGRAM SIZES")
    print("=" * 72)
    print(f"# high-level ops = {len(high_ops)}")
    print(f"# prim ops       = {len(prim_ops)}")
    print(f"final widths     = {final_widths}")

    if args.show_high_ops:
        print("\n" + "=" * 72)
        print("HIGH-LEVEL OPS")
        print("=" * 72)
        for idx, op in enumerate(high_ops):
            print(f"{idx:4d}: {op_str(op)}")

    if args.show_prim_ops:
        print("\n" + "=" * 72)
        print("PRIM OPS")
        print("=" * 72)
        for idx, op in enumerate(prim_ops):
            print(f"{idx:4d}: {prim_str(op)}")

    checks = verify_by_blocks(k, points, init_widths)

    print("\n" + "=" * 72)
    print("BLOCK-BY-BLOCK VERIFICATION")
    print("=" * 72)

    all_exact = True
    all_upper = True

    for chk in checks:
        print(f"\nBlock {chk.block_index}: point = {point_str(chk.point)}")
        print(f"  start widths              = {chk.start_widths}")
        print(f"  actual before phase       = {chk.actual_before_phase}")
        print(f"  actual target width       = {chk.actual_dst_width}")
        print(f"  predicted exact width     = {chk.predicted_exact_dst_width}")
        print(f"  predicted upper bound     = {chk.predicted_upper_bound_dst_width}")
        print(f"  m (#addScaled in local)   = {chk.m}")

        if isinstance(chk.point, IntPoint):
            print(f"  sources                   = {chk.sources}")
            print(f"  shifts                    = {chk.shifts}")
            print(f"  popcount formula m(z)     = {popcount_formula_m(k, chk.point.z)}")

        print(f"  exact formula correct?    = {chk.ok_exact}")
        print(f"  upper bound correct?      = {chk.ok_upper}")

        all_exact = all_exact and chk.ok_exact
        all_upper = all_upper and chk.ok_upper

    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    print(f"All exact checks passed? {all_exact}")
    print(f"All upper-bound checks passed? {all_upper}")

    if not all_exact:
        raise SystemExit(1)


if __name__ == "__main__":
    main()