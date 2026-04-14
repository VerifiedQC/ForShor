from __future__ import annotations

import argparse
import cmath
import math
import random
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Dict, Iterable, List, Optional, Tuple, Union

import numpy as np


# ============================================================
# Concrete registers, sparse vectors, and matrix-backed gates
# ============================================================


@dataclass(frozen=True)
class Reg:
    """A qubit interval [lo, hi)."""
    lo: int
    hi: int

    @property
    def size(self) -> int:
        return self.hi - self.lo


@dataclass(frozen=True)
class LogicalReg:
    """
    A logical register assembled from explicit Reg ranges.

    This is the key object for the in-place layout: a child chunk may use
    some bits sliced out of its parent register plus only the appended extension
    bits needed to make the arithmetic width large enough.
    """

    segments: Tuple[Reg, ...]

    def __post_init__(self) -> None:
        qubits: List[int] = []
        for segment in self.segments:
            if segment.size <= 0:
                raise ValueError(f"empty segment in LogicalReg: {segment}")
            qubits.extend(range(segment.lo, segment.hi))
        if len(qubits) != len(set(qubits)):
            raise ValueError(f"overlapping segments in LogicalReg: {self.segments}")

    @property
    def size(self) -> int:
        return sum(segment.size for segment in self.segments)


RegLike = Union[Reg, LogicalReg]


def as_logical_reg(reg: RegLike) -> LogicalReg:
    if isinstance(reg, LogicalReg):
        return reg
    return LogicalReg((reg,))


def logical_qubits(reg: RegLike) -> Tuple[int, ...]:
    out: List[int] = []
    for segment in as_logical_reg(reg).segments:
        out.extend(range(segment.lo, segment.hi))
    return tuple(out)


def logical_bit(reg: RegLike, offset: int) -> int:
    bits = logical_qubits(reg)
    if offset < 0 or offset >= len(bits):
        raise ValueError("logical bit offset out of range")
    return bits[offset]


def slice_logical_reg(reg: RegLike, start: int, stop: int) -> LogicalReg:
    if start < 0 or stop < start:
        raise ValueError("invalid logical slice")

    segments: List[Reg] = []
    cursor = 0
    for segment in as_logical_reg(reg).segments:
        seg_start = cursor
        seg_stop = cursor + segment.size
        cursor = seg_stop

        lo = max(start, seg_start)
        hi = min(stop, seg_stop)
        if lo >= hi:
            continue
        segments.append(Reg(segment.lo + (lo - seg_start), segment.lo + (hi - seg_start)))
    return LogicalReg(tuple(segments)) if segments else LogicalReg(())


def concat_logical_regs(*regs: RegLike) -> LogicalReg:
    segments: List[Reg] = []
    for reg in regs:
        segments.extend(as_logical_reg(reg).segments)
    return LogicalReg(tuple(segments)) if segments else LogicalReg(())


def _mask(width: int) -> int:
    return (1 << width) - 1


def encode_twos(value: int, width: int) -> int:
    if width <= 0:
        raise ValueError("width must be positive")
    return value & _mask(width)


def decode_twos(unsigned_value: int, width: int) -> int:
    if width <= 0:
        raise ValueError("width must be positive")
    unsigned_value &= _mask(width)
    sign = 1 << (width - 1)
    return unsigned_value - (1 << width) if unsigned_value & sign else unsigned_value


def signed_width_for_abs(max_abs: int) -> int:
    """Smallest two's-complement width representing every value in [-max_abs, max_abs]."""

    if max_abs < 0:
        raise ValueError("max_abs must be nonnegative")
    width = 1
    while max_abs > (1 << (width - 1)) - 1:
        width += 1
    return width


def get_reg_unsigned(index: int, reg: Reg) -> int:
    out = 0
    for offset, q in enumerate(range(reg.lo, reg.hi)):
        out |= ((index >> q) & 1) << offset
    return out


def get_reg_signed(index: int, reg: Reg) -> int:
    return decode_twos(get_reg_unsigned(index, reg), reg.size)


def set_reg_unsigned(index: int, reg: Reg, value: int) -> int:
    value &= _mask(reg.size)
    for offset, q in enumerate(range(reg.lo, reg.hi)):
        bit = (value >> offset) & 1
        if ((index >> q) & 1) != bit:
            index ^= 1 << q
    return index


def set_reg_signed(index: int, reg: Reg, value: int) -> int:
    return set_reg_unsigned(index, reg, encode_twos(value, reg.size))


def get_logical_unsigned(index: int, reg: RegLike) -> int:
    view = as_logical_reg(reg)
    if view.size <= 0:
        raise ValueError("cannot read an empty logical register")
    out = 0
    for offset, q in enumerate(logical_qubits(view)):
        out |= ((index >> q) & 1) << offset
    return out


def get_logical_signed(index: int, reg: RegLike) -> int:
    view = as_logical_reg(reg)
    return decode_twos(get_logical_unsigned(index, view), view.size)


def set_logical_unsigned(index: int, reg: RegLike, value: int) -> int:
    view = as_logical_reg(reg)
    if view.size <= 0:
        raise ValueError("cannot write an empty logical register")
    value &= _mask(view.size)
    for offset, q in enumerate(logical_qubits(view)):
        bit = (value >> offset) & 1
        if ((index >> q) & 1) != bit:
            index ^= 1 << q
    return index


def set_logical_signed(index: int, reg: RegLike, value: int) -> int:
    return set_logical_unsigned(index, reg, encode_twos(value, as_logical_reg(reg).size))


@dataclass
class QuantumState:
    """
    Sparse state vector over the full 2^n computational basis.

    This is still a genuine vector representation: missing entries are zero.
    It lets us check large fixed-ambient circuits on basis states without
    materializing impossible dense arrays.
    """

    nqubits: int
    amp: Dict[int, complex]

    @staticmethod
    def basis(nqubits: int, index: int) -> "QuantumState":
        if index < 0 or index >= (1 << nqubits):
            raise ValueError("basis index out of range")
        return QuantumState(nqubits, {index: 1.0 + 0.0j})

    def copy(self) -> "QuantumState":
        return QuantumState(self.nqubits, dict(self.amp))

    def prune(self, eps: float = 0.0) -> "QuantumState":
        self.amp = {i: a for i, a in self.amp.items() if abs(a) > eps}
        return self

    def as_dense(self, max_qubits: int = 12):
        if self.nqubits > max_qubits:
            raise ValueError(f"dense vector would have 2^{self.nqubits} entries")
        if np is None:
            vec = [0.0 + 0.0j for _ in range(1 << self.nqubits)]
        else:
            vec = np.zeros((1 << self.nqubits,), dtype=np.complex128)
        for idx, amp in self.amp.items():
            vec[idx] = amp
        return vec

    def single_basis(self, eps: float = 1e-12) -> Tuple[int, complex]:
        nz = [(idx, amp) for idx, amp in self.amp.items() if abs(amp) > eps]
        if len(nz) != 1:
            raise ValueError(f"expected one basis component, found {len(nz)}")
        return nz[0]

    def distance(self, other: "QuantumState") -> float:
        if self.nqubits != other.nqubits:
            raise ValueError("state dimensions differ")
        keys = set(self.amp) | set(other.amp)
        return math.sqrt(sum(abs(self.amp.get(k, 0.0) - other.amp.get(k, 0.0)) ** 2 for k in keys))


class Gate:
    """Linear gate with efficient sparse application and optional dense matrix extraction."""

    name: str

    def apply(self, state: QuantumState) -> QuantumState:
        raise NotImplementedError

    def trace_label(self, state: QuantumState) -> str:
        return self.name

    def matrix(self, nqubits: int, max_qubits: int = 10):
        if nqubits > max_qubits:
            raise ValueError(f"dense matrix would be 2^{nqubits} by 2^{nqubits}")
        dim = 1 << nqubits
        if np is None:
            mat = [[0.0 + 0.0j for _ in range(dim)] for _ in range(dim)]
        else:
            mat = np.zeros((dim, dim), dtype=np.complex128)
        for col in range(dim):
            out = self.apply(QuantumState.basis(nqubits, col))
            for row, amp in out.amp.items():
                if np is None:
                    mat[row][col] = amp
                else:
                    mat[row, col] = amp
        return mat


@dataclass(frozen=True)
class PermutationGate(Gate):
    name: str
    update_index: Callable[[int], int]

    def apply(self, state: QuantumState) -> QuantumState:
        out: Dict[int, complex] = {}
        for idx, amp in state.amp.items():
            j = self.update_index(idx)
            out[j] = out.get(j, 0.0 + 0.0j) + amp
        return QuantumState(state.nqubits, out).prune()


@dataclass(frozen=True)
class DiagonalGate(Gate):
    name: str
    phase_at: Callable[[int], complex]

    def apply(self, state: QuantumState) -> QuantumState:
        return QuantumState(
            state.nqubits,
            {idx: amp * self.phase_at(idx) for idx, amp in state.amp.items()},
        ).prune()


@dataclass(frozen=True)
class SeqGate(Gate):
    name: str
    gates: Tuple[Gate, ...]

    def apply(self, state: QuantumState) -> QuantumState:
        out = state
        for gate in self.gates:
            out = gate.apply(out)
        return out

    def apply_with_trace(self, state: QuantumState) -> Tuple[QuantumState, List[str]]:
        """
        Apply each subgate and record a compact before/after line.

        This is meant for basis-state debugging. It still works for sparse
        superpositions, but it will omit the before/after basis index summary.
        """

        out = state
        trace: List[str] = []
        for step, gate in enumerate(self.gates):
            before = basis_summary(out)
            label = gate.trace_label(out)
            out = gate.apply(out)
            after = basis_summary(out)
            trace.append(f"{step:03d}: {label} | {before} -> {after}")
        return out, trace


def basis_summary(state: QuantumState) -> str:
    try:
        idx, amp = state.single_basis()
    except ValueError:
        return f"{len(state.amp)} basis terms"
    return f"basis={idx}, amp={amp:.6g}"


@dataclass(frozen=True)
class SignFillGate(Gate):
    """
    Reversible sign-extension helper for an in-place chunk.

    Targets are freshly appended bits. The gate CNOTs the source sign bit into
    each target bit, and applying the same gate again clears the extension once
    the arithmetic has been uncomputed.
    """

    name: str
    sign_bit: int
    targets: LogicalReg

    def apply(self, state: QuantumState) -> QuantumState:
        def update(idx: int) -> int:
            if ((idx >> self.sign_bit) & 1) == 0:
                return idx
            out = idx
            for q in logical_qubits(self.targets):
                out ^= 1 << q
            return out

        return PermutationGate(self.name, update).apply(state)

    def trace_label(self, state: QuantumState) -> str:
        return f"{self.name}: copy sign bit q{self.sign_bit} into {self.targets}"


@dataclass(frozen=True)
class TraceCheckpointGate(Gate):
    name: str
    trace: List["PhaseEvent"]
    depth: int
    term: int
    slot: int
    coeff: Fraction
    x_reg: LogicalReg
    z_reg: LogicalReg
    work_width: int

    def apply(self, state: QuantumState) -> QuantumState:
        idx, _amp = state.single_basis()
        self.trace.append(
            PhaseEvent(
                depth=self.depth,
                term=self.term,
                slot=self.slot,
                coeff=self.coeff,
                x_value=get_logical_signed(idx, self.x_reg),
                z_value=get_logical_signed(idx, self.z_reg),
                work_width=self.work_width,
            )
        )
        return state

    def trace_label(self, state: QuantumState) -> str:
        idx, _amp = state.single_basis()
        coeff = (
            f"{self.coeff.numerator}/{self.coeff.denominator}"
            if self.coeff.denominator != 1
            else str(self.coeff.numerator)
        )
        return (
            f"Checkpoint(depth={self.depth}, term={self.term}, slot={self.slot}, coeff={coeff}, "
            f"x_i={get_logical_signed(idx, self.x_reg)}, "
            f"z_i={get_logical_signed(idx, self.z_reg)})"
        )


def negate_gate(reg: RegLike) -> PermutationGate:
    view = as_logical_reg(reg)

    def update(idx: int) -> int:
        value = get_logical_unsigned(idx, view)
        return set_logical_unsigned(idx, view, (-value) & _mask(view.size))

    return PermutationGate(f"Negate{view}", update)


def add_scaled_gate(dst: RegLike, src: RegLike, neg_src: bool, shift: int) -> PermutationGate:
    dst_view = as_logical_reg(dst)
    src_view = as_logical_reg(src)
    if dst_view.size != src_view.size:
        raise ValueError("AddScaled requires equal-width source and destination registers")
    if shift < 0:
        raise ValueError("shift must be nonnegative")

    def update(idx: int) -> int:
        modulus = 1 << dst_view.size
        dst_value = get_logical_unsigned(idx, dst_view)
        src_value = get_logical_unsigned(idx, src_view)
        term = (src_value << shift) % modulus
        new_value = (dst_value - term) % modulus if neg_src else (dst_value + term) % modulus
        return set_logical_unsigned(idx, dst_view, new_value)

    sign = "-" if neg_src else "+"
    return PermutationGate(f"AddScaled({sign},sh={shift})", update)


def shift_l_gate(reg: RegLike, n: int) -> PermutationGate:
    view = as_logical_reg(reg)

    def update(idx: int) -> int:
        value = get_logical_unsigned(idx, view)
        return set_logical_unsigned(idx, view, (value << n) & _mask(view.size))

    return PermutationGate(f"ShiftL({n})", update)


def shift_r_gate(reg: RegLike, n: int) -> PermutationGate:
    view = as_logical_reg(reg)

    def update(idx: int) -> int:
        value = get_logical_unsigned(idx, view)
        if value & _mask(n):
            raise ValueError(f"inexact ShiftR by {n} on register {view}")
        return set_logical_unsigned(idx, view, value >> n)

    return PermutationGate(f"ShiftR({n})", update)


def scaled_naive_phase_product_gate(
    base_phi: float,
    scale: Fraction,
    x_reg: RegLike,
    z_reg: RegLike,
    phase_period: Optional[int] = None,
) -> DiagonalGate:
    """
    Signed PhaseProduct gate.

    PhaseProduct is defined on two's-complement signed integers in this
    prototype. The arithmetic gates may still use unsigned representatives
    internally because they are modular bit operations, but the phase semantic
    value is always the signed integer stored in each register.
    """

    x_view = as_logical_reg(x_reg)
    z_view = as_logical_reg(z_reg)

    def phase(idx: int) -> complex:
        x = get_logical_signed(idx, x_view)
        z = get_logical_signed(idx, z_view)
        multiplier = scale * x * z
        if phase_period is not None:
            reduced = multiplier % phase_period
            angle = 2.0 * math.pi * float(reduced) / float(phase_period)
        else:
            angle = math.remainder(base_phi * float(multiplier), 2.0 * math.pi)
        return cmath.exp(1j * angle)

    return DiagonalGate(f"SignedPhaseProduct(scale={scale})", phase)


def naive_phase_product_gate(
    phi: float,
    x_reg: RegLike,
    z_reg: RegLike,
    phase_period: Optional[int] = None,
) -> DiagonalGate:
    return scaled_naive_phase_product_gate(
        phi,
        Fraction(1),
        x_reg,
        z_reg,
        phase_period=phase_period,
    )


# ============================================================
# Points and valid_ops, mirroring the Lean symbolic layer
# ============================================================


@dataclass(frozen=True)
class IntPoint:
    z: int


@dataclass(frozen=True)
class InfPoint:
    pass


Point = Union[IntPoint, InfPoint]


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
class PhaseCheckpoint:
    i: int


ValidOp = Union[ShiftL, ShiftR, Negate, AddScaled, PhaseCheckpoint]


def inv(op: ValidOp) -> ValidOp:
    if isinstance(op, ShiftL):
        return ShiftR(op.i, op.n)
    if isinstance(op, ShiftR):
        return ShiftL(op.i, op.n)
    if isinstance(op, Negate):
        return Negate(op.i)
    if isinstance(op, AddScaled):
        return AddScaled(op.dst, op.src, not op.neg_src, op.shift)
    if isinstance(op, PhaseCheckpoint):
        return PhaseCheckpoint(op.i)
    raise TypeError(f"unknown op: {op!r}")


def apply_op_inverse(ops: List[ValidOp]) -> List[ValidOp]:
    return [inv(op) for op in reversed(ops)]


def add_const_aux(dst: int, src: int, neg: bool, n: int, sh: int) -> List[ValidOp]:
    if n == 0:
        return []
    rest = add_const_aux(dst, src, neg, n // 2, sh + 1)
    if n % 2 == 1:
        return [AddScaled(dst, src, neg, sh)] + rest
    return rest


def add_const_from(dst: int, src: int, c: int) -> List[ValidOp]:
    if c == 0:
        return []
    return add_const_aux(dst, src, c < 0, abs(c), 0)


def compute_local2(k: int, z: int) -> List[ValidOp]:
    if k <= 0:
        raise ValueError("k must be positive")
    out: List[ValidOp] = []
    for j in range(1, k):
        out.extend(add_const_from(0, j, z**j))
    return out


def ops_for_point_with_product(k: int, point: Point) -> List[ValidOp]:
    if k <= 0:
        raise ValueError("k must be positive")
    if isinstance(point, InfPoint):
        return [PhaseCheckpoint(k - 1)]
    if isinstance(point, IntPoint):
        local = compute_local2(k, point.z)
        return local + [PhaseCheckpoint(0)] + apply_op_inverse(local)
    raise TypeError(f"unknown point: {point!r}")


def gen_ops_with_product(k: int, points: List[Point]) -> List[ValidOp]:
    out: List[ValidOp] = []
    for point in points:
        out.extend(ops_for_point_with_product(k, point))
    return out


# ============================================================
# Interpolation coefficients
# ============================================================


def q(k: int) -> int:
    return 2 * k - 1


def alternating_point(i: int) -> Point:
    if i % 2 == 0:
        return IntPoint(i // 2)
    return IntPoint(-((i + 1) // 2))


def gen_interpolation_points(k: int) -> List[Point]:
    if k <= 1:
        raise ValueError("k must be greater than 1")
    return [alternating_point(i) for i in range(q(k))]


def interp_entry(k: int, point: Point, j: int) -> Fraction:
    if isinstance(point, IntPoint):
        return Fraction(point.z) ** j
    if isinstance(point, InfPoint):
        return Fraction(1 if j == q(k) - 1 else 0)
    raise TypeError(f"unknown point: {point!r}")


def invert_fraction_matrix(matrix: List[List[Fraction]]) -> List[List[Fraction]]:
    n = len(matrix)
    if n == 0 or any(len(row) != n for row in matrix):
        raise ValueError("matrix must be nonempty and square")

    aug = [
        list(row) + [Fraction(1 if i == j else 0) for j in range(n)]
        for i, row in enumerate(matrix)
    ]

    for col in range(n):
        pivot = None
        for row in range(col, n):
            if aug[row][col] != 0:
                pivot = row
                break
        if pivot is None:
            raise ValueError("interpolation matrix is singular")
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]

        pivot_value = aug[col][col]
        aug[col] = [x / pivot_value for x in aug[col]]

        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0:
                continue
            aug[row] = [x - factor * y for x, y in zip(aug[row], aug[col])]

    return [row[n:] for row in aug]


def phase_coeff_from_points(k: int, points: List[Point], radix: int) -> List[Fraction]:
    qk = q(k)
    if len(points) != qk:
        raise ValueError(f"expected {qk} interpolation points, got {len(points)}")
    if radix <= 1:
        raise ValueError("radix must be greater than 1")

    matrix = [[interp_entry(k, point, j) for j in range(qk)] for point in points]
    inv_matrix = invert_fraction_matrix(matrix)
    row = [Fraction(radix) ** j for j in range(qk)]
    return [sum(row[a] * inv_matrix[a][i] for a in range(qk)) for i in range(qk)]


# ============================================================
# In-place one-level PhaseProduct layout
# ============================================================


@dataclass(frozen=True)
class PhaseBlockPlan:
    k: int
    active_width: int
    chunk_width: int
    work_width: int
    radix: int
    coeffs: Tuple[Fraction, ...]


@dataclass(frozen=True)
class PhaseBlockLayout:
    """
    In-place view of one decomposition level.

    The x_regs/z_regs are not a duplicate child bank. Each slot is a LogicalReg
    whose low bits are slices of the parent register and whose high bits are
    only the appended extension bits required for equal-width signed arithmetic.
    """

    plan: PhaseBlockPlan
    x_regs_tuple: Tuple[LogicalReg, ...]
    z_regs_tuple: Tuple[LogicalReg, ...]
    init_gates: Tuple[Gate, ...]
    cleanup_gates: Tuple[Gate, ...]

    @property
    def k(self) -> int:
        return self.plan.k

    @property
    def work_width(self) -> int:
        return self.plan.work_width

    def x_reg(self, i: int) -> LogicalReg:
        return self.x_regs_tuple[i]

    def z_reg(self, i: int) -> LogicalReg:
        return self.z_regs_tuple[i]


@dataclass
class WorkspaceAllocator:
    next_qubit: int

    def allocate(self, width: int) -> LogicalReg:
        if width < 0:
            raise ValueError("cannot allocate negative width")
        if width == 0:
            return LogicalReg(())
        reg = Reg(self.next_qubit, self.next_qubit + width)
        self.next_qubit += width
        return LogicalReg((reg,))


@dataclass(frozen=True)
class PhaseEvent:
    depth: int
    term: int
    slot: int
    coeff: Fraction
    x_value: int
    z_value: int
    work_width: int


@dataclass(frozen=True)
class ChunkLayoutEvent:
    label: str
    slot: int
    role: str
    base_width: int
    sign_fill_width: int
    zero_fill_width: int
    work_width: int
    base_qubits: Tuple[int, ...]
    sign_fill_qubits: Tuple[int, ...]
    zero_fill_qubits: Tuple[int, ...]


def initial_chunk_bounds(source_width: int, plan: "PhaseBlockPlan") -> List[int]:
    """
    Bound the absolute value in each chunk before any valid_ops run.

    PhaseProduct inputs are signed. Conceptually, a shorter source register is
    sign-extended to active_width before chunking. Lower chunks are unsigned
    radix digits; only the leading chunk is interpreted as signed.
    """

    bounds: List[int] = []
    for i in range(plan.k):
        start = i * plan.chunk_width
        active_stop = min((i + 1) * plan.chunk_width, plan.active_width)
        active_width = max(0, active_stop - start)
        if source_width <= 0:
            raise ValueError("source_width must be positive")

        if active_width == 0:
            bounds.append(0)
        elif i == plan.k - 1:
            bounds.append(1 << (active_width - 1))
        else:
            bounds.append((1 << active_width) - 1)
    return bounds


def bound_valid_ops(initial_bounds: List[int], ops: List[ValidOp]) -> int:
    """
    Propagate simple absolute-value bounds through the actual arithmetic program.

    This intentionally follows the concrete valid_ops list instead of sizing
    from interpolation points alone. The transfer rules are conservative:
    - ShiftL multiplies by 2^n.
    - ShiftR keeps the same bound, because proving divisibility is a separate concern.
    - Negate leaves the bound unchanged.
    - AddScaled uses |dst +/- 2^sh * src| <= |dst| + 2^sh * |src|.
    """

    bounds = list(initial_bounds)
    max_seen = max(bounds, default=0)

    for op in ops:
        if isinstance(op, ShiftL):
            bounds[op.i] *= 1 << op.n
        elif isinstance(op, ShiftR):
            bounds[op.i] = bounds[op.i]
        elif isinstance(op, Negate):
            bounds[op.i] = bounds[op.i]
        elif isinstance(op, AddScaled):
            bounds[op.dst] = bounds[op.dst] + (1 << op.shift) * bounds[op.src]
        elif isinstance(op, PhaseCheckpoint):
            pass
        else:
            raise TypeError(f"unknown op: {op!r}")

        max_seen = max(max_seen, *bounds)

    return max_seen


def plan_one_level_phase_block(
    k: int,
    active_width: int,
    points: List[Point],
    ops: List[ValidOp],
    *,
    x_width: int,
    z_width: int,
) -> Optional[PhaseBlockPlan]:
    """
    Plan widths for one PhaseProduct decomposition layer.

    The work width is derived from the actual valid_ops sequence. We start from
    per-chunk input bounds for x and z, take a per-slot maximum so the same
    arithmetic layout works for both sides, and propagate that bound through the
    full compute/checkpoint/uncompute program.
    """

    if k <= 1:
        raise ValueError("k must be greater than 1")
    if active_width <= 1 or active_width < k:
        return None

    chunk_width = math.ceil(active_width / k)
    radix = 1 << chunk_width

    draft_plan = PhaseBlockPlan(
        k=k,
        active_width=active_width,
        chunk_width=chunk_width,
        work_width=chunk_width,
        radix=radix,
        coeffs=(),
    )
    x_bounds = initial_chunk_bounds(x_width, draft_plan)
    z_bounds = initial_chunk_bounds(z_width, draft_plan)
    shared_initial_bounds = [max(x_bounds[i], z_bounds[i]) for i in range(k)]
    max_seen = bound_valid_ops(shared_initial_bounds, ops)
    work_width = signed_width_for_abs(max_seen)

    coeffs = phase_coeff_from_points(k, points, radix)
    return PhaseBlockPlan(
        k=k,
        active_width=active_width,
        chunk_width=chunk_width,
        work_width=work_width,
        radix=radix,
        coeffs=tuple(coeffs),
    )


def chunk_base_slice(source: LogicalReg, plan: PhaseBlockPlan, i: int) -> LogicalReg:
    start = i * plan.chunk_width
    stop = max(start, min((i + 1) * plan.chunk_width, plan.active_width))
    return slice_logical_reg(source, start, stop)


def extend_one_chunk(
    *,
    label: str,
    source: LogicalReg,
    plan: PhaseBlockPlan,
    i: int,
    allocator: WorkspaceAllocator,
    layout_trace: Optional[List[ChunkLayoutEvent]] = None,
) -> Tuple[LogicalReg, Tuple[Gate, ...], Tuple[Gate, ...]]:
    """
    Build the logical register for one in-place chunk.

    The low bits are a slice of the signed source. Missing source bits are
    filled from the source sign bit, because the parent signed integer is
    conceptually sign-extended to active_width before chunking. A complete
    non-leading chunk is still an unsigned radix digit: if its physical bits
    are 111, that digit is 7, not -1. Only the leading chunk receives enough
    sign extension to be read as a signed child value.
    """

    base = chunk_base_slice(source, plan, i)
    base_width = base.size
    sign_bit = logical_bit(source, source.size - 1)
    if i == plan.k - 1:
        sign_fill_width = plan.work_width - base_width
    else:
        sign_fill_width = max(0, plan.chunk_width - base_width)

    if sign_fill_width < 0 or base_width + sign_fill_width > plan.work_width:
        raise ValueError("invalid in-place chunk extension width")

    zero_fill_width = plan.work_width - base_width - sign_fill_width
    sign_fill = allocator.allocate(sign_fill_width)
    zero_fill = allocator.allocate(zero_fill_width)
    slot = concat_logical_regs(base, sign_fill, zero_fill)

    if layout_trace is not None:
        if i == plan.k - 1:
            role = "top chunk: sign-extended to work_width"
        elif sign_fill_width:
            role = "lower chunk: parent sign bits then zero-fill"
        else:
            role = "lower chunk: zero-extended to work_width"
        layout_trace.append(
            ChunkLayoutEvent(
                label=label,
                slot=i,
                role=role,
                base_width=base_width,
                sign_fill_width=sign_fill_width,
                zero_fill_width=zero_fill_width,
                work_width=plan.work_width,
                base_qubits=logical_qubits(base),
                sign_fill_qubits=logical_qubits(sign_fill),
                zero_fill_qubits=logical_qubits(zero_fill),
            )
        )

    init_gates: Tuple[Gate, ...] = ()
    if sign_fill_width:
        init = SignFillGate(
            name=f"sign_extend_{label}_{i}",
            sign_bit=sign_bit,
            targets=sign_fill,
        )
        init_gates = (init,)

    return slot, init_gates, tuple(reversed(init_gates))


def extend_chunks_for_source(
    *,
    label: str,
    source: RegLike,
    plan: PhaseBlockPlan,
    allocator: WorkspaceAllocator,
    layout_trace: Optional[List[ChunkLayoutEvent]] = None,
) -> Tuple[Tuple[LogicalReg, ...], Tuple[Gate, ...], Tuple[Gate, ...]]:
    source_view = as_logical_reg(source)
    regs: List[LogicalReg] = []
    init_gates: List[Gate] = []
    cleanup_gates: List[Gate] = []

    for i in range(plan.k):
        slot, init, cleanup = extend_one_chunk(
            label=label,
            source=source_view,
            plan=plan,
            i=i,
            allocator=allocator,
            layout_trace=layout_trace,
        )
        if slot.size != plan.work_width:
            raise AssertionError("in-place chunk did not reach planned work width")
        regs.append(slot)
        init_gates.extend(init)
        cleanup_gates[:0] = cleanup

    return tuple(regs), tuple(init_gates), tuple(cleanup_gates)


def build_phase_block_layout(
    *,
    plan: PhaseBlockPlan,
    x_reg: RegLike,
    z_reg: RegLike,
    allocator: WorkspaceAllocator,
    layout_trace: Optional[List[ChunkLayoutEvent]] = None,
) -> PhaseBlockLayout:
    x_regs, x_init, x_cleanup = extend_chunks_for_source(
        label="x",
        source=x_reg,
        plan=plan,
        allocator=allocator,
        layout_trace=layout_trace,
    )
    z_regs, z_init, z_cleanup = extend_chunks_for_source(
        label="z",
        source=z_reg,
        plan=plan,
        allocator=allocator,
        layout_trace=layout_trace,
    )
    return PhaseBlockLayout(
        plan=plan,
        x_regs_tuple=x_regs,
        z_regs_tuple=z_regs,
        init_gates=x_init + z_init,
        cleanup_gates=z_cleanup + x_cleanup,
    )


def extension_qubits_for_source_width(plan: PhaseBlockPlan, source_width: int) -> int:
    total = 0
    for i in range(plan.k):
        start = i * plan.chunk_width
        stop = min((i + 1) * plan.chunk_width, plan.active_width, source_width)
        base_width = max(0, stop - start)
        total += plan.work_width - base_width
    return total


def arithmetic_gate_for_op(layout: PhaseBlockLayout, op: ValidOp, x_side: bool) -> Gate:
    reg = layout.x_reg if x_side else layout.z_reg
    if isinstance(op, ShiftL):
        return shift_l_gate(reg(op.i), op.n)
    if isinstance(op, ShiftR):
        return shift_r_gate(reg(op.i), op.n)
    if isinstance(op, Negate):
        return negate_gate(reg(op.i))
    if isinstance(op, AddScaled):
        return add_scaled_gate(reg(op.dst), reg(op.src), op.neg_src, op.shift)
    raise TypeError(f"not an arithmetic op: {op!r}")


def lower_phase_product_one_level_gate(
    base_phi: float,
    x_reg: RegLike,
    z_reg: RegLike,
    *,
    phase_period: Optional[int] = None,
    active_width: int,
    k: int,
    points: Optional[List[Point]],
    allocator: WorkspaceAllocator,
    trace: Optional[List[PhaseEvent]] = None,
    layout_trace: Optional[List[ChunkLayoutEvent]] = None,
) -> Gate:
    """
    Build a one-level PhaseProduct decomposition.

    The returned object is a Gate. A decomposed layer is a sequence:
      view x,z as in-place chunk registers plus appended extension bits;
      initialize only the sign-extension bits needed by signed chunks;
      run arithmetic gates from genOpsWithProduct on those logical chunks;
      at each PhaseCheckpoint, insert a scaled NaivePhaseProduct gate;
      uncompute arithmetic and clear the sign-extension bits.
    """

    if points is None:
        points = gen_interpolation_points(k)
    ops = gen_ops_with_product(k, points)

    plan = plan_one_level_phase_block(
        k,
        active_width,
        points,
        ops,
        x_width=as_logical_reg(x_reg).size,
        z_width=as_logical_reg(z_reg).size,
    )

    if plan is None:
        return scaled_naive_phase_product_gate(
            base_phi,
            Fraction(1),
            x_reg,
            z_reg,
            phase_period=phase_period,
        )

    layout = build_phase_block_layout(
        plan=plan,
        x_reg=x_reg,
        z_reg=z_reg,
        allocator=allocator,
        layout_trace=layout_trace,
    )
    gates: List[Gate] = list(layout.init_gates)

    term = 0
    for op in ops:
        if isinstance(op, PhaseCheckpoint):
            if term >= len(plan.coeffs):
                raise ValueError("more phase checkpoints than interpolation coefficients")
            coeff = plan.coeffs[term]
            child_x_reg = layout.x_reg(op.i)
            child_z_reg = layout.z_reg(op.i)

            if trace is not None:
                gates.append(
                    TraceCheckpointGate(
                        name=f"trace_phase_term_{term}",
                        trace=trace,
                        depth=0,
                        term=term,
                        slot=op.i,
                        coeff=coeff,
                        x_reg=child_x_reg,
                        z_reg=child_z_reg,
                        work_width=plan.work_width,
                    )
                )

            gates.append(
                scaled_naive_phase_product_gate(
                    base_phi,
                    coeff,
                    child_x_reg,
                    child_z_reg,
                    phase_period=phase_period,
                )
            )
            term += 1
        else:
            gates.append(arithmetic_gate_for_op(layout, op, x_side=True))
            gates.append(arithmetic_gate_for_op(layout, op, x_side=False))

    if term != len(plan.coeffs):
        raise ValueError("fewer phase checkpoints than interpolation coefficients")

    gates.extend(layout.cleanup_gates)
    return SeqGate(name=f"OneLevelPhaseProduct(width={active_width})", gates=tuple(gates))


def lower_PhaseProduct(
    base_phi: float,
    x_reg: RegLike,
    z_reg: RegLike,
    *,
    phase_period: Optional[int] = None,
    active_width: int,
    k: int,
    points: Optional[List[Point]],
    allocator: WorkspaceAllocator,
    trace: Optional[List[PhaseEvent]] = None,
    layout_trace: Optional[List[ChunkLayoutEvent]] = None,
) -> Gate:
    """
    Build a fully recursive PhaseProduct decomposition.

    This follows the same in-place chunking logic as the one-level lowering.
    At each checkpoint, the child PhaseProduct is recursively lowered on the
    current child registers. Recursion stops when the next planned child width
    is not strictly smaller than the current subproblem width.
    """

    local_points = gen_interpolation_points(k) if points is None else points

    def lower_at_depth(
        scale: Fraction,
        xr: RegLike,
        zr: RegLike,
        width: int,
        depth: int,
    ) -> Gate:
        ops = gen_ops_with_product(k, local_points)
        plan = plan_one_level_phase_block(
            k,
            width,
            local_points,
            ops,
            x_width=as_logical_reg(xr).size,
            z_width=as_logical_reg(zr).size,
        )

        # A recursive call must make strict progress in the effective child
        # register width. If the next layer would have equal-or-larger width,
        # fall back to the direct signed PhaseProduct on the current subproblem.
        if plan is None or plan.work_width >= width:
            return scaled_naive_phase_product_gate(
                base_phi,
                scale,
                xr,
                zr,
                phase_period=phase_period,
            )

        local_layout_trace = layout_trace if depth == 0 else None
        layout = build_phase_block_layout(
            plan=plan,
            x_reg=xr,
            z_reg=zr,
            allocator=allocator,
            layout_trace=local_layout_trace,
        )
        gates: List[Gate] = list(layout.init_gates)

        term = 0
        for op in ops:
            if isinstance(op, PhaseCheckpoint):
                if term >= len(plan.coeffs):
                    raise ValueError("more phase checkpoints than interpolation coefficients")
                coeff = plan.coeffs[term]
                child_x_reg = layout.x_reg(op.i)
                child_z_reg = layout.z_reg(op.i)

                if trace is not None:
                    gates.append(
                        TraceCheckpointGate(
                            name=f"trace_phase_term_{term}_d{depth}",
                            trace=trace,
                            depth=depth,
                            term=term,
                            slot=op.i,
                            coeff=coeff,
                            x_reg=child_x_reg,
                            z_reg=child_z_reg,
                            work_width=plan.work_width,
                        )
                    )

                gates.append(
                    lower_at_depth(
                        scale * coeff,
                        child_x_reg,
                        child_z_reg,
                        plan.work_width,
                        depth + 1,
                    )
                )
                term += 1
            else:
                gates.append(arithmetic_gate_for_op(layout, op, x_side=True))
                gates.append(arithmetic_gate_for_op(layout, op, x_side=False))

        if term != len(plan.coeffs):
            raise ValueError("fewer phase checkpoints than interpolation coefficients")

        gates.extend(layout.cleanup_gates)
        return SeqGate(name=f"RecursivePhaseProduct(width={width},depth={depth})", gates=tuple(gates))

    return lower_at_depth(Fraction(1), x_reg, z_reg, active_width, 0)


@dataclass(frozen=True)
class ConcretePhaseSpace:
    x_bits: int
    z_bits: int

    @property
    def x_dim(self) -> int:
        return 1 << self.x_bits

    @property
    def z_dim(self) -> int:
        return 1 << self.z_bits

    @property
    def x_min(self) -> int:
        return -(1 << (self.x_bits - 1))

    @property
    def x_max(self) -> int:
        return (1 << (self.x_bits - 1)) - 1

    @property
    def z_min(self) -> int:
        return -(1 << (self.z_bits - 1))

    @property
    def z_max(self) -> int:
        return (1 << (self.z_bits - 1)) - 1

    @property
    def active_width(self) -> int:
        return max(self.x_bits, self.z_bits)


@dataclass(frozen=True)
class ConcretePhaseLayout:
    """
    Physical placement of the original x and z registers.

    The registers do not need to be adjacent. They only need to be disjoint.
    """

    x_reg: RegLike
    z_reg: RegLike

    def __post_init__(self) -> None:
        x_qubits = set(logical_qubits(self.x_reg))
        z_qubits = set(logical_qubits(self.z_reg))
        if not x_qubits:
            raise ValueError("x_reg must be nonempty")
        if not z_qubits:
            raise ValueError("z_reg must be nonempty")
        if x_qubits & z_qubits:
            raise ValueError("x_reg and z_reg must be disjoint")

    @property
    def x_bits(self) -> int:
        return as_logical_reg(self.x_reg).size

    @property
    def z_bits(self) -> int:
        return as_logical_reg(self.z_reg).size

    @property
    def active_width(self) -> int:
        return max(self.x_bits, self.z_bits)

    @property
    def min_total_qubits(self) -> int:
        used = logical_qubits(self.x_reg) + logical_qubits(self.z_reg)
        return (max(used) + 1) if used else 0


def default_concrete_layout(space: ConcretePhaseSpace) -> ConcretePhaseLayout:
    """
    Default adjacent layout used by the original code:
      x on [0, x_bits)
      z on [x_bits, x_bits + z_bits)
    """
    return ConcretePhaseLayout(
        x_reg=Reg(0, space.x_bits),
        z_reg=Reg(space.x_bits, space.x_bits + space.z_bits),
    )


def original_x_reg(space: ConcretePhaseSpace) -> Reg:
    """
    Backward-compatible helper for the default adjacent layout.
    """
    layout = default_concrete_layout(space)
    x_view = as_logical_reg(layout.x_reg)
    if len(x_view.segments) != 1:
        raise ValueError("default x layout is expected to be contiguous")
    return x_view.segments[0]


def original_z_reg(space: ConcretePhaseSpace) -> Reg:
    """
    Backward-compatible helper for the default adjacent layout.
    """
    layout = default_concrete_layout(space)
    z_view = as_logical_reg(layout.z_reg)
    if len(z_view.segments) != 1:
        raise ValueError("default z layout is expected to be contiguous")
    return z_view.segments[0]


def encode_basis_with_layout(
    space: ConcretePhaseSpace,
    layout: ConcretePhaseLayout,
    total_nqubits: int,
    x: int,
    z: int,
) -> int:
    """
    Encode signed x and z into the original physical layout. Any qubits not
    belonging to x_reg or z_reg are left at zero.
    """
    if total_nqubits < layout.min_total_qubits:
        raise ValueError("ambient register is too small for the chosen layout")
    if layout.x_bits != space.x_bits:
        raise ValueError("layout x_reg width does not match space.x_bits")
    if layout.z_bits != space.z_bits:
        raise ValueError("layout z_reg width does not match space.z_bits")
    if not (space.x_min <= x <= space.x_max and space.z_min <= z <= space.z_max):
        raise ValueError("signed basis values out of range")

    idx = 0
    idx = set_logical_signed(idx, layout.x_reg, x)
    idx = set_logical_signed(idx, layout.z_reg, z)
    return idx


def encode_original_basis(
    space: ConcretePhaseSpace,
    total_nqubits: int,
    x: int,
    z: int,
) -> int:
    """
    Backward-compatible wrapper using the default adjacent layout.
    """
    return encode_basis_with_layout(
        space,
        default_concrete_layout(space),
        total_nqubits,
        x,
        z,
    )


def build_one_level_phase_product_gate(
    space: ConcretePhaseSpace,
    *,
    phi: float,
    phase_period: Optional[int] = None,
    k: int,
    points: List[Point],
    trace: Optional[List[PhaseEvent]] = None,
    layout_trace: Optional[List[ChunkLayoutEvent]] = None,
    layout: Optional[ConcretePhaseLayout] = None,
) -> Tuple[Gate, int]:
    """
    Build the one-level decomposed gate for the given physical layout.

    If layout is omitted, use the original adjacent placement.
    """
    if layout is None:
        layout = default_concrete_layout(space)

    allocator = WorkspaceAllocator(next_qubit=layout.min_total_qubits)
    gate = lower_phase_product_one_level_gate(
        phi,
        layout.x_reg,
        layout.z_reg,
        phase_period=phase_period,
        active_width=layout.active_width,
        k=k,
        points=points,
        allocator=allocator,
        trace=trace,
        layout_trace=layout_trace,
    )
    return gate, allocator.next_qubit


def build_recursive_phase_product_gate(
    space: ConcretePhaseSpace,
    *,
    phi: float,
    phase_period: Optional[int] = None,
    k: int,
    points: List[Point],
    trace: Optional[List[PhaseEvent]] = None,
    layout_trace: Optional[List[ChunkLayoutEvent]] = None,
    layout: Optional[ConcretePhaseLayout] = None,
) -> Tuple[Gate, int]:
    """
    Build the fully recursive decomposed gate for the given physical layout.

    If layout is omitted, use the original adjacent placement.
    """
    if layout is None:
        layout = default_concrete_layout(space)

    allocator = WorkspaceAllocator(next_qubit=layout.min_total_qubits)
    gate = lower_PhaseProduct(
        phi,
        layout.x_reg,
        layout.z_reg,
        phase_period=phase_period,
        active_width=layout.active_width,
        k=k,
        points=points,
        allocator=allocator,
        trace=trace,
        layout_trace=layout_trace,
    )
    return gate, allocator.next_qubit


def apply_direct_phase_product_to_basis(
    space: ConcretePhaseSpace,
    *,
    phi: float,
    phase_period: Optional[int] = None,
    x: int,
    z: int,
    total_nqubits: Optional[int] = None,
    layout: Optional[ConcretePhaseLayout] = None,
) -> QuantumState:
    """
    Apply the direct naive PhaseProduct to a basis state in the chosen layout.

    If total_nqubits is omitted, use the minimum size required by the layout.
    """
    if layout is None:
        layout = default_concrete_layout(space)
    if total_nqubits is None:
        total_nqubits = layout.min_total_qubits

    initial = QuantumState.basis(
        total_nqubits,
        encode_basis_with_layout(space, layout, total_nqubits, x, z),
    )
    return naive_phase_product_gate(
        phi,
        layout.x_reg,
        layout.z_reg,
        phase_period=phase_period,
    ).apply(initial)


def apply_one_level_phase_product_to_basis(
    space: ConcretePhaseSpace,
    *,
    phi: float,
    phase_period: Optional[int] = None,
    x: int,
    z: int,
    k: int,
    points: List[Point],
    trace: Optional[List[PhaseEvent]] = None,
    layout_trace: Optional[List[ChunkLayoutEvent]] = None,
    layout: Optional[ConcretePhaseLayout] = None,
) -> Tuple[QuantumState, int, Gate]:
    """
    Apply the one-level decomposed PhaseProduct to a basis state in the chosen
    layout.

    If layout is omitted, use the original adjacent placement.
    """
    gate, total_nqubits = build_one_level_phase_product_gate(
        space,
        phi=phi,
        phase_period=phase_period,
        k=k,
        points=points,
        trace=trace,
        layout_trace=layout_trace,
        layout=layout,
    )

    if layout is None:
        layout = default_concrete_layout(space)

    initial = QuantumState.basis(
        total_nqubits,
        encode_basis_with_layout(space, layout, total_nqubits, x, z),
    )
    return gate.apply(initial), total_nqubits, gate


def apply_recursive_phase_product_to_basis(
    space: ConcretePhaseSpace,
    *,
    phi: float,
    phase_period: Optional[int] = None,
    x: int,
    z: int,
    k: int,
    points: List[Point],
    trace: Optional[List[PhaseEvent]] = None,
    layout_trace: Optional[List[ChunkLayoutEvent]] = None,
    layout: Optional[ConcretePhaseLayout] = None,
) -> Tuple[QuantumState, int, Gate]:
    """
    Apply the fully recursive decomposed PhaseProduct to a basis state in the
    chosen layout.
    """
    gate, total_nqubits = build_recursive_phase_product_gate(
        space,
        phi=phi,
        phase_period=phase_period,
        k=k,
        points=points,
        trace=trace,
        layout_trace=layout_trace,
        layout=layout,
    )
    if layout is None:
        layout = default_concrete_layout(space)
    initial = QuantumState.basis(
        total_nqubits,
        encode_basis_with_layout(space, layout, total_nqubits, x, z),
    )
    return gate.apply(initial), total_nqubits, gate


# ============================================================
# Example: non-adjacent x and z registers
# ============================================================

def example_non_adjacent_layout() -> Tuple[ConcretePhaseSpace, ConcretePhaseLayout]:
    """
    Example layout with a gap between x and z:

      x on qubits 0..3
      gap on qubits 4..7
      z on qubits 8..11
    """
    space = ConcretePhaseSpace(x_bits=4, z_bits=4)
    layout = ConcretePhaseLayout(
        x_reg=Reg(0, 4),
        z_reg=Reg(8, 12),
    )
    return space, layout


def demo_non_adjacent_one_level() -> Tuple[QuantumState, int, Gate, List[PhaseEvent], List[ChunkLayoutEvent]]:
    """
    Small demo using non-adjacent original registers.
    """
    space, layout = example_non_adjacent_layout()
    trace: List[PhaseEvent] = []
    layout_trace: List[ChunkLayoutEvent] = []

    out, total_nqubits, gate = apply_one_level_phase_product_to_basis(
        space,
        phi=2 * math.pi / (1 << space.active_width),
        x=-3,
        z=2,
        k=2,
        points=gen_interpolation_points(2),
        trace=trace,
        layout_trace=layout_trace,
        layout=layout,
    )
    return out, total_nqubits, gate, trace, layout_trace


def compare_phase_product_implementations(
    space: ConcretePhaseSpace,
    *,
    phi: float,
    phase_period: Optional[int] = None,
    x: int,
    z: int,
    k: int,
    points: List[Point],
    layout: Optional[ConcretePhaseLayout] = None,
) -> Tuple[float, float]:
    """
    Compare the one-level and recursive decompositions against the direct
    signed PhaseProduct on the same basis input.
    """
    if layout is None:
        layout = default_concrete_layout(space)

    one_level_gate, one_level_nqubits = build_one_level_phase_product_gate(
        space,
        phi=phi,
        phase_period=phase_period,
        k=k,
        points=points,
        layout=layout,
    )
    recursive_gate, recursive_nqubits = build_recursive_phase_product_gate(
        space,
        phi=phi,
        phase_period=phase_period,
        k=k,
        points=points,
        layout=layout,
    )
    direct_gate = naive_phase_product_gate(phi, layout.x_reg, layout.z_reg, phase_period=phase_period)

    one_level_initial = QuantumState.basis(
        one_level_nqubits,
        encode_basis_with_layout(space, layout, one_level_nqubits, x, z),
    )
    recursive_initial = QuantumState.basis(
        recursive_nqubits,
        encode_basis_with_layout(space, layout, recursive_nqubits, x, z),
    )

    one_level_state = one_level_gate.apply(one_level_initial)
    one_level_direct_state = direct_gate.apply(one_level_initial)
    recursive_state = recursive_gate.apply(recursive_initial)
    recursive_direct_state = direct_gate.apply(recursive_initial)
    return (
        one_level_state.distance(one_level_direct_state),
        recursive_state.distance(recursive_direct_state),
    )


# def run_regression_tests(tolerance: float = 1e-9) -> List[str]:
#     """
#     Run a small regression suite covering representative signed PhaseProduct
#     cases. Raises an AssertionError if any case exceeds tolerance.
#     """
#     lines: List[str] = []

#     representative_cases: List[
#         Tuple[str, ConcretePhaseSpace, ConcretePhaseLayout, int, int, int]
#     ] = []

#     space = ConcretePhaseSpace(x_bits=8, z_bits=8)
#     representative_cases.append(
#         ("adjacent_neg_pos", space, default_concrete_layout(space), -37, 51, 3)
#     )
#     representative_cases.append(
#         ("adjacent_neg_neg", space, default_concrete_layout(space), -37, -51, 3)
#     )

#     space = ConcretePhaseSpace(x_bits=7, z_bits=9)
#     representative_cases.append(
#         ("unequal_widths", space, default_concrete_layout(space), -37, -180, 3)
#     )

#     space, layout = example_non_adjacent_layout()
#     representative_cases.append(
#         ("non_adjacent", space, layout, -3, 2, 2)
#     )

#     for name, space, layout, x, z, k in representative_cases:
#         phi = 2.0 * math.pi / (1 << layout.active_width)
#         phase_period = 1 << layout.active_width
#         points = gen_interpolation_points(k)
#         one_level_dist, recursive_dist = compare_phase_product_implementations(
#             space,
#             phi=phi,
#             phase_period=phase_period,
#             x=x,
#             z=z,
#             k=k,
#             points=points,
#             layout=layout,
#         )
#         if one_level_dist > tolerance:
#             raise AssertionError(
#                 f"{name}: one-level distance {one_level_dist:.3e} exceeds tolerance {tolerance:.3e}"
#             )
#         if recursive_dist > tolerance:
#             raise AssertionError(
#                 f"{name}: recursive distance {recursive_dist:.3e} exceeds tolerance {tolerance:.3e}"
#             )
#         lines.append(
#             f"{name}: one_level={one_level_dist:.3e}, recursive={recursive_dist:.3e}"
#         )

#     small_space = ConcretePhaseSpace(x_bits=4, z_bits=4)
#     small_layout = default_concrete_layout(small_space)
#     small_phi = 2.0 * math.pi / (1 << small_layout.active_width)
#     small_phase_period = 1 << small_layout.active_width
#     small_points = gen_interpolation_points(2)
#     one_level_gate, one_level_nqubits = build_one_level_phase_product_gate(
#         small_space,
#         phi=small_phi,
#         phase_period=small_phase_period,
#         k=2,
#         points=small_points,
#         layout=small_layout,
#     )
#     recursive_gate, recursive_nqubits = build_recursive_phase_product_gate(
#         small_space,
#         phi=small_phi,
#         phase_period=small_phase_period,
#         k=2,
#         points=small_points,
#         layout=small_layout,
#     )
#     direct_gate = naive_phase_product_gate(
#         small_phi,
#         small_layout.x_reg,
#         small_layout.z_reg,
#         phase_period=small_phase_period,
#     )

#     worst_one_level = 0.0
#     worst_recursive = 0.0
#     worst_pair_one_level = (0, 0)
#     worst_pair_recursive = (0, 0)

#     for x in range(small_space.x_min, small_space.x_max + 1):
#         for z in range(small_space.z_min, small_space.z_max + 1):
#             one_level_initial = QuantumState.basis(
#                 one_level_nqubits,
#                 encode_basis_with_layout(small_space, small_layout, one_level_nqubits, x, z),
#             )
#             recursive_initial = QuantumState.basis(
#                 recursive_nqubits,
#                 encode_basis_with_layout(small_space, small_layout, recursive_nqubits, x, z),
#             )
#             one_level_dist = one_level_gate.apply(one_level_initial).distance(
#                 direct_gate.apply(one_level_initial)
#             )
#             recursive_dist = recursive_gate.apply(recursive_initial).distance(
#                 direct_gate.apply(recursive_initial)
#             )

#             if one_level_dist > worst_one_level:
#                 worst_one_level = one_level_dist
#                 worst_pair_one_level = (x, z)
#             if recursive_dist > worst_recursive:
#                 worst_recursive = recursive_dist
#                 worst_pair_recursive = (x, z)

#             if one_level_dist > tolerance:
#                 raise AssertionError(
#                     f"exhaustive_small: one-level distance {one_level_dist:.3e} exceeds tolerance "
#                     f"{tolerance:.3e} at x={x}, z={z}"
#                 )
#             if recursive_dist > tolerance:
#                 raise AssertionError(
#                     f"exhaustive_small: recursive distance {recursive_dist:.3e} exceeds tolerance "
#                     f"{tolerance:.3e} at x={x}, z={z}"
#                 )

#     lines.append(
#         "exhaustive_small: "
#         f"one_level_worst={worst_one_level:.3e} at {worst_pair_one_level}, "
#         f"recursive_worst={worst_recursive:.3e} at {worst_pair_recursive}"
#     )
#     return lines

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Signed PhaseProduct sanity checker"
    )
    parser.add_argument("--x-bits", type=int, default=14, help="width of x register")
    parser.add_argument("--z-bits", type=int, default=14, help="width of z register")
    parser.add_argument("--x", type=int, default=-77, help="signed x input")
    parser.add_argument("--z", type=int, default=41, help="signed z input")
    parser.add_argument("--k", type=int, default=4, help="number of chunks")
    parser.add_argument(
        "--phi",
        type=float,
        default=None,
        help="base phase angle; default is 2*pi / 2^active_width",
    )
    parser.add_argument(
        "--non-adjacent",
        action="store_true",
        help="place x and z in a non-adjacent layout with a gap",
    )
    parser.add_argument(
        "--trace",
        action="store_true",
        help="print the step-by-step gate trace for the decomposed circuit",
    )
    parser.add_argument(
        "--layout-trace",
        action="store_true",
        help="print how each chunk register was assembled",
    )
    # parser.add_argument(
    #     "--run-tests",
    #     action="store_true",
    #     help="run a small regression suite for both one-level and recursive lowering",
    # )
    args = parser.parse_args()

    space = ConcretePhaseSpace(x_bits=args.x_bits, z_bits=args.z_bits)

    if args.non_adjacent:
        gap = max(space.x_bits, 4)
        layout = ConcretePhaseLayout(
            x_reg=Reg(0, space.x_bits),
            z_reg=Reg(space.x_bits + gap, space.x_bits + gap + space.z_bits),
        )
    else:
        layout = default_concrete_layout(space)

    phi = args.phi
    phase_period: Optional[int]
    if phi is None:
        phi = 2.0 * math.pi / (1 << layout.active_width)
        phase_period = 1 << layout.active_width
    else:
        phase_period = None

    points = gen_interpolation_points(args.k)
    trace: Optional[List[PhaseEvent]] = [] if args.trace else None
    recursive_trace: Optional[List[PhaseEvent]] = [] if args.trace else None
    layout_trace: Optional[List[ChunkLayoutEvent]] = [] if args.layout_trace else None

    gate, total_nqubits = build_one_level_phase_product_gate(
        space,
        phi=phi,
        phase_period=phase_period,
        k=args.k,
        points=points,
        trace=trace,
        layout_trace=layout_trace,
        layout=layout,
    )

    initial = QuantumState.basis(
        total_nqubits,
        encode_basis_with_layout(space, layout, total_nqubits, args.x, args.z),
    )

    if args.trace:
        if not isinstance(gate, SeqGate):
            raise TypeError("expected one-level gate to be a SeqGate")
        one_level_state, gate_trace = gate.apply_with_trace(initial)
    else:
        one_level_state = gate.apply(initial)
        gate_trace = []

    direct_state = apply_direct_phase_product_to_basis(
        space,
        phi=phi,
        phase_period=phase_period,
        x=args.x,
        z=args.z,
        total_nqubits=total_nqubits,
        layout=layout,
    )
    recursive_state, recursive_total_nqubits, _recursive_gate = apply_recursive_phase_product_to_basis(
        space,
        phi=phi,
        phase_period=phase_period,
        x=args.x,
        z=args.z,
        k=args.k,
        points=points,
        trace=recursive_trace,
        layout=layout,
    )
    recursive_direct_state = apply_direct_phase_product_to_basis(
        space,
        phi=phi,
        phase_period=phase_period,
        x=args.x,
        z=args.z,
        total_nqubits=recursive_total_nqubits,
        layout=layout,
    )

    dist = one_level_state.distance(direct_state)
    recursive_dist = recursive_state.distance(recursive_direct_state)

    print("One-level PhaseProduct sanity")
    print(f"  x_bits={space.x_bits}, z_bits={space.z_bits}, active_width={layout.active_width}")
    print(f"  input_encoding=signed, x_range=[{space.x_min}, {space.x_max}], z_range=[{space.z_min}, {space.z_max}]")
    print(f"  x={args.x}, z={args.z}")
    print(f"  k={args.k}, q={q(args.k)}")
    print(f"  points={points}")
    print(f"  phi={phi}")
    #print(f"  total_nqubits={total_nqubits}")
    print(f"  one_level_state_distance={dist:.3e}")
    print(f"  recursive_state_distance={recursive_dist:.3e}")
    #print(f"  recursive_total_nqubits={recursive_total_nqubits}")
    #print(f"  layout={'non-adjacent' if args.non_adjacent else 'adjacent'}")
    print(f"  x_reg={layout.x_reg}")
    print(f"  z_reg={layout.z_reg}")

    if layout_trace is not None:
        print("\nChunk layout:")
        for ev in layout_trace:
            print(
                f"  {ev.label}[{ev.slot}] "
                f"role={ev.role}, "
                f"base_width={ev.base_width}, "
                f"sign_fill_width={ev.sign_fill_width}, "
                f"zero_fill_width={ev.zero_fill_width}, "
                f"work_width={ev.work_width}"
            )
            print(f"    base_qubits={ev.base_qubits}")
            print(f"    sign_fill_qubits={ev.sign_fill_qubits}")
            print(f"    zero_fill_qubits={ev.zero_fill_qubits}")

    if trace is not None:
        print("\nOne-level phase checkpoints:")
        for ev in trace:
            coeff_str = (
                f"{ev.coeff.numerator}/{ev.coeff.denominator}"
                if ev.coeff.denominator != 1
                else str(ev.coeff.numerator)
            )
            print(
                f"  term={ev.term}, slot={ev.slot}, coeff={coeff_str}, "
                f"x_value={ev.x_value}, z_value={ev.z_value}, work_width={ev.work_width}"
            )

    if recursive_trace is not None:
        print("\nRecursive phase checkpoints:")
        for ev in recursive_trace:
            coeff_str = (
                f"{ev.coeff.numerator}/{ev.coeff.denominator}"
                if ev.coeff.denominator != 1
                else str(ev.coeff.numerator)
            )
            indent = "  " * ev.depth
            print(
                f"  {indent}depth={ev.depth}, term={ev.term}, slot={ev.slot}, coeff={coeff_str}, "
                f"x_value={ev.x_value}, z_value={ev.z_value}, work_width={ev.work_width}"
            )

    if gate_trace:
        print("\nGate trace:")
        for line in gate_trace:
            print(f"  {line}")

    if dist > 1e-9:
        print("\nWARNING: one-level decomposed circuit does not match direct phase product within tolerance.")
    else:
        print("\nOK: one-level decomposed circuit matches direct phase product within tolerance.")

    if recursive_dist > 1e-9:
        print("WARNING: recursive decomposed circuit does not match direct phase product within tolerance.")
    else:
        print("OK: recursive decomposed circuit matches direct phase product within tolerance.")

    # if args.run_tests:
    #     print("\nRegression tests:")
    #     for line in run_regression_tests():
    #         print(f"  {line}")


if __name__ == "__main__":
    main()
