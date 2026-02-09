from __future__ import annotations
import numpy as np
from dataclasses import dataclass
import math
from typing import Any, Callable, Dict, Hashable, Protocol, runtime_checkable, Sequence, Tuple

# ============================================================
# 0) Basic scalars / labels
# ============================================================

Scalar = complex
Basis = Hashable  # int / tuple / custom basis label


# ============================================================
# 1) Concrete layer: Hilbert spaces + vectors
# ============================================================

class FinHilbert(Protocol):
    """
    A finite-dimensional Hilbert space over C.
    Intrinsic: dimension and inner product exist.
    Representation is NOT fixed.
    """
    dim: int

    def inner(self, x: "Vec", y: "Vec") -> Scalar: ...
    def add(self, x: "Vec", y: "Vec") -> "Vec": ...
    def smul(self, a: Scalar, x: "Vec") -> "Vec": ...


class Vec(Protocol):
    """
    An element of a particular Hilbert space H.
    Intrinsic: belongs to H.
    """
    def space(self) -> FinHilbert: ...

    # intrinsic operations
    def inner(self, other: "Vec") -> Scalar: ...
    def add(self, other: "Vec") -> "Vec": ...
    def smul(self, a: Scalar) -> "Vec": ...

    # derived intrinsic notions
    def norm2(self) -> float:
        z = self.inner(self)
        return float(z.real)

    def is_normalized(self, atol: float = 1e-12) -> bool:
        return abs(self.norm2() - 1.0) <= atol


# ============================================================
# 2) Symbolic layer: states + gates (purely abstract AST)
# ============================================================

class QState:
    """Marker base class: a symbolic quantum state expression."""

    def __add__(self, other: "QState") -> "QState":
        return Add(self, other)

    def __radd__(self, other: "QState") -> "QState":
        return Add(other, self)

    def __sub__(self, other: "QState") -> "QState":
        return Add(self, Smul(-1, other))

    def __rmul__(self, a: Scalar) -> "QState":
        # scalar * state
        return Smul(a, self)


@dataclass(frozen=True)
class Ket(QState):
    """|b>"""
    b: Basis
    def __repr__(self) -> str:
        return f"|{self.b}>"


@dataclass(frozen=True)
class Add(QState):
    """|psi> + |phi>"""
    psi: QState
    phi: QState

    def __repr__(self) -> str:
        return f"({self.psi} + {self.phi})"


@dataclass(frozen=True)
class Smul(QState):
    """a * |psi>"""
    a: Scalar
    psi: QState

    def __repr__(self) -> str:
        return f"({self.a} * {self.psi})"


@dataclass(frozen=True)
class Apply(QState):
    """U |psi>"""
    U: "Gate"
    psi: QState

    def __repr__(self) -> str:
        return f"({self.U} @ {self.psi})"


class Gate:
    """Marker base class: a symbolic gate/operator expression."""

    def __matmul__(self, other):
        # If RHS is a state, interpret as application: U @ |psi>
        if isinstance(other, QState):
            return Apply(self, other)
        # Otherwise interpret as composition: U2 @ U1
        if isinstance(other, Gate):
            return Compose(self, other)
        return NotImplemented

    # dagger / adjoint
    def __invert__(self) -> "Gate":
        return Adjoint(self)

    # optional scalar multiplication of gates (purely symbolic)
    def __rmul__(self, a: Scalar) -> "Gate":
        return ScaleGate(a, self)



@dataclass(frozen=True)
class PrimGate(Gate):
    """
    Opaque primitive gate.
    Examples:
      PrimGate("H", 0)
      PrimGate("CNOT", (0,1))
      PrimGate(my_backend_handle, meta)
    """
    tag: Any
    meta: Any = None

    def __repr__(self) -> str:
        if self.meta is None:
            return f"{self.tag}"
        return f"{self.tag}{self.meta}"


@dataclass(frozen=True)
class Compose(Gate):
    """U2 ∘ U1 (apply U1 then U2)."""
    U2: Gate
    U1: Gate

    def __repr__(self) -> str:
        return f"({self.U2} @ {self.U1})"


@dataclass(frozen=True)
class Adjoint(Gate):
    """U†"""
    U: Gate

    def __repr__(self) -> str:
        return f"({self.U})†"


@dataclass(frozen=True)
class ScaleGate(Gate):
    """a * U (optional; useful for global phases)"""
    a: Scalar
    U: Gate

    def __repr__(self) -> str:
        return f"({self.a} * {self.U})"


# tiny constructors
def ket(b: Basis) -> QState:
    return Ket(b)

def G(tag: Any, meta: Any = None) -> Gate:
    return PrimGate(tag, meta)


# ============================================================
# 3) Concrete layer: linear maps + evaluator
# ============================================================

@runtime_checkable
class LinearMap(Protocol):
    """A concrete linear operator on vectors of some Hilbert space."""
    def apply(self, x: Vec) -> Vec: ...
    def adjoint(self) -> "LinearMap": ...


@dataclass(frozen=True)
class EvalHooks:
    """
    You provide these two functions to give meaning to primitives.
    Everything else is structural recursion on the AST.
    """
    eval_ket: Callable[[FinHilbert, Basis], Vec]
    eval_prim_gate: Callable[[FinHilbert, Any, Any], LinearMap]


@dataclass(frozen=True)
class _ComposeMap:
    """Concrete combinator: (op2 ∘ op1)."""
    op2: LinearMap
    op1: LinearMap

    def apply(self, x: Vec) -> Vec:
        return self.op2.apply(self.op1.apply(x))

    def adjoint(self) -> LinearMap:
        # (op2 ∘ op1)† = op1† ∘ op2†
        return _ComposeMap(self.op1.adjoint(), self.op2.adjoint())


@dataclass(frozen=True)
class _ScaleMap:
    """Concrete combinator: a * op."""
    a: Scalar
    op: LinearMap

    def apply(self, x: Vec) -> Vec:
        return self.op.apply(x).smul(self.a)

    def adjoint(self) -> LinearMap:
        return _ScaleMap(self.a.conjugate(), self.op.adjoint())


class Evaluator:
    """
    Evaluates symbolic QState/Gate into concrete Vec/LinearMap inside a chosen FinHilbert space.
    Primitive meanings are supplied by EvalHooks.
    """
    def __init__(self, hooks: EvalHooks):
        self.hooks = hooks
        self._gate_cache: Dict[tuple[int, int], LinearMap] = {}
        self._state_cache: Dict[tuple[int, int], Vec] = {}

    def eval_state(self, H: FinHilbert, s: QState) -> Vec:
        key = (id(H), id(s))
        if key in self._state_cache:
            return self._state_cache[key]

        if isinstance(s, Ket):
            v = self.hooks.eval_ket(H, s.b)

        elif isinstance(s, Add):
            v = H.add(self.eval_state(H, s.psi), self.eval_state(H, s.phi))

        elif isinstance(s, Smul):
            v = H.smul(s.a, self.eval_state(H, s.psi))

        elif isinstance(s, Apply):
            op = self.eval_gate(H, s.U)
            v = op.apply(self.eval_state(H, s.psi))

        else:
            raise TypeError(f"Unknown QState node: {type(s)}")

        self._state_cache[key] = v
        return v

    def eval_gate(self, H: FinHilbert, U: Gate) -> LinearMap:
        key = (id(H), id(U))
        if key in self._gate_cache:
            return self._gate_cache[key]

        if isinstance(U, PrimGate):
            op = self.hooks.eval_prim_gate(H, U.tag, U.meta)

        elif isinstance(U, Compose):
            op = _ComposeMap(self.eval_gate(H, U.U2), self.eval_gate(H, U.U1))

        elif isinstance(U, Adjoint):
            op = self.eval_gate(H, U.U).adjoint()

        elif isinstance(U, ScaleGate):
            op = _ScaleMap(U.a, self.eval_gate(H, U.U))

        else:
            raise TypeError(f"Unknown Gate node: {type(U)}")

        self._gate_cache[key] = op
        return op



# ============================================================
# 4) Shor's Algorithm gates
# ============================================================

def H(target: int | None = None) -> Gate:
    """
    Symbolic Hadamard gate.
    - If target is provided: Hadamard on that qubit index (common convention).
    - If target is None: a generic Hadamard (eval decides how to interpret).
    """
    return PrimGate("H", target)

@dataclass(frozen=True)
class QFT(Gate):
    """
    Symbolic Quantum Fourier Transform on a list of qubit indices.
    """
    qubits: Sequence[int]

    def __repr__(self) -> str:
        return f"QFT{tuple(self.qubits)}"


def IQFT(qubits: Sequence[int]) -> Gate:
    """Inverse QFT (symbolic)."""
    return ~QFT(qubits)

# --- Basic single-/two-qubit primitives (symbolic tags) --------

def X(target: int) -> Gate:
    """Pauli-X on one qubit."""
    return PrimGate("X", target)

def Z(target: int) -> Gate:
    """Pauli-Z on one qubit."""
    return PrimGate("Z", target)

def CNOT(control: int, target: int) -> Gate:
    """Controlled-NOT."""
    return PrimGate("CNOT", (control, target))

def SWAP(q1: int, q2: int) -> Gate:
    """Swap two qubits."""
    return PrimGate("SWAP", (q1, q2))

def PHASE(target: int, theta: float) -> Gate:
    """Single-qubit phase rotation (convention decided by eval)."""
    return PrimGate("PHASE", (target, theta))

def CPHASE(control: int, target: int, theta: float) -> Gate:
    """Controlled phase rotation (convention decided by eval)."""
    return PrimGate("CPHASE", (control, target, theta))


def CTRL(control: int, U: Gate) -> Gate:
    """
    Controlled-U as a single symbolic gate node.
    (You can choose whether your evaluator expands this or supports it natively.)
    """
    return PrimGate("CTRL", (control, U))

@dataclass(frozen=True)
class PhaseProduct(Gate):
    """
    PhaseProduct(phi, x_reg, z_reg) acts as:
      |x>|z> -> exp(i * phi * x * z) |x>|z>
    where x and z are the integer values encoded by those registers.
    """
    phi: Scalar
    x_reg: Tuple[int, int]   # half-open [lo, hi)
    z_reg: Tuple[int, int]   # half-open [lo, hi)

    def __repr__(self) -> str:
        return f"PhaseProduct(phi={self.phi}, x={self.x_reg}, z={self.z_reg})"


@dataclass(frozen=True)
class CPhaseProduct(Gate):
    """
    Controlled PhaseProduct
    """
    control: int
    phi: Scalar
    x_reg: Tuple[int,int]
    z_reg: Tuple[int,int]

    def __repr__(self) -> str:
        return f"CPhaseProduct(ctrl={self.control}, phi={self.phi}, x={tuple(self.x_reg)}, z={tuple(self.z_reg)})"




def U_cxq(x_reg: Tuple[int,int], z_reg: Tuple[int,int], a: int):
    l=z_reg[1]-z_reg[0]
    return IQFT(z_reg) @ PhaseProduct(phi=(2*math.pi*a/(2**l)),x_reg=x_reg, z_reg=z_reg) @ QFT(z_reg)

def C_U_cxq(ctrl: int, x_reg: Sequence[int], z_reg: Sequence[int], a: int):
    l=z_reg[1]-z_reg[0]
    return IQFT(z_reg) @ CPhaseProduct(phi=(2*math.pi*a/(2**l)), x_reg=x_reg, z_reg=z_reg, control=ctrl) @ QFT(z_reg)

def reg_len(r: Tuple[int, int]) -> int:
    return r[1] - r[0]

def reg_qubits(r: Tuple[int, int]) -> range:
    return range(r[0], r[1])

def H_reg(r: Tuple[int, int]) -> Gate:
    """
    Symbolic H^{⊗m} on the register r.
    Order doesn't matter; we just build a deterministic composition.
    """
    qs = list(reg_qubits(r))
    if not qs:
        return PrimGate("ID", None) 
    U = H(qs[0])
    for q in qs[1:]:
        U = H(q) @ U
    return U



def nbits_for_modulus(N: int) -> int:
    """Smallest n such that N <= 2^n."""
    if N <= 0:
        raise ValueError("N must be positive")
    return (N - 1).bit_length()

def choose_m(n: int, eta: float) -> int:
    """
    Paper: m = n + ceil( 2 log( 2 + 1/(2η) ) ).
    Here we take log base 2 (consistent with qubits / bit growth).
    """
    if not (0 < eta < 1):
        raise ValueError("eta must be in (0,1)")
    extra = math.ceil(2.0 * math.log2(2.0 + 1.0/(2.0*eta)))
    return n + extra


def step1(c: int, N: int,x_reg: Tuple[int, int],z_reg:Tuple[int, int]):

    phi = (2.0 * math.pi * ((c - 1) % N)) / float(N)
    U = IQFT(z_reg) @ PhaseProduct(phi=phi, x_reg=x_reg, z_reg=z_reg) @ H_reg(z_reg)
    return U

def step2(N: int, x_reg: Tuple[int,int], w_reg: Tuple[int,int]):
    """
    Step 2:
      add one ancilla to the top of x, then compute |x>|w> -> |x + Nw>|w>.

    Implemented using U_cxq:
      U_cxq(x_reg = w_reg, z_reg = x_ext_reg, a = N)
    """
    # x_ext is x plus one extra top bit
    x_ext = (x_reg[0], x_reg[1] + 1)

    # U_cxq takes (x_reg, z_reg, a) and does z <- z + a*x (mod 2^len(z))
    # Here we want x_ext <- x_ext + N*w, so:
    return x_ext, U_cxq(x_reg=w_reg, z_reg=x_ext, a=N)


# ============================================================
# Steps 3, 4, 5 for Algorithm 1
#   Step 3: flag := [x_ext > N]; x_ext -= N controlled by flag
#   Step 4: uncompute flag via comparison operator
#   Step 5: uncompute w by subtracting w' = ((1 - c^{-1}) * (cx mod N) mod N) / N from w_reg
# ============================================================

# --- Comparison / controlled-sub primitives (symbolic tags) ----

def CMP_GT_CONST(x_reg: Tuple[int, int], N: int, flag: int) -> Gate:
    """
    flag ^= [ value(x_reg) > N ].
    (Evaluator defines strictness / encoding.)
    """
    return PrimGate("CMP_GT_CONST", (x_reg, N, flag))

def CSUB_CONST(flag: int, x_reg: Tuple[int, int], N: int) -> Gate:
    """
    If flag==1, do x_reg <- x_reg - N (in-place).
    """
    return PrimGate("CSUB_CONST", (flag, x_reg, N))

def CMP_LT_NW(x_reg: Tuple[int, int], w_reg: Tuple[int, int], N: int, flag: int) -> Gate:
    """
    Uncompute flag by comparing whether (left) < N*w.
    In the paper: "compute whether cx mod N < Nw via a comparison operator".
    """
    return PrimGate("CMP_LT_NW", (x_reg, w_reg, N, flag))


# --- Step 3 ----------------------------------------------------

def step3(N: int, x_ext_reg: Tuple[int, int], flag: int) -> Gate:
    """
    Step 3 (symbolic):
      compute flag = [x_ext > N];
      subtract N controlled by flag.
    """
    return CSUB_CONST(flag, x_ext_reg, N) @ CMP_GT_CONST(x_ext_reg, N, flag)


# --- Step 4 ----------------------------------------------------

def step4(N: int, x_ext_reg: Tuple[int, int], w_reg: Tuple[int, int], flag: int) -> Gate:
    """
    Step 4 (symbolic):
      Uncompute the flag ancilla by computing whether (cx mod N) < Nw.
    """
    return CMP_LT_NW(x_ext_reg, w_reg, N, flag)


# --- Step 5 ----------------------------------------------------
# Use the same phase-estimation-style Step 1 but as a SUBTRACT / uncompute on w.
# We'll make a symbolic gate that means:
#   |x>|w> -> |x>|w - approx(((k*x mod N)/N))>
# where k = (1 - c^{-1}) mod N and x is the *current left register* holding cx mod N.

@dataclass(frozen=True)
class CQMulFracSub(Gate):
    """
    Symbolic inverse/uncompute version of Step-1-style fraction loading:
      subtract from w_reg the (approx) fraction (k*x mod N)/N.
    """
    k: int
    N: int
    eta: float
    x_reg: Tuple[int, int]
    w_reg: Tuple[int, int]

    def __repr__(self) -> str:
        return f"CQMulFracSub(k={self.k},N={self.N},eta={self.eta},x={self.x_reg},w={self.w_reg})"


def step5(c: int, N: int, eta: float, x_ext_reg: Tuple[int, int], w_reg: Tuple[int, int]) -> Gate:
    """
    Step 5 (symbolic):
      Subtract w' from the second register to reset it to |0...0|, where
        w' = ((1 - c^{-1}) * (cx mod N) mod N)/N   (approx)
    """
    c_inv = pow(c, -1, N)          # multiplicative inverse mod N
    k5 = (1 - c_inv) % N
    return CQMulFracSub(k=k5, N=N, eta=eta, x_reg=x_ext_reg, w_reg=w_reg)



def mod_mul_InPlace(c: int, N: int, eta: float) -> Gate:
    """
    The full symbolic in-place modular multiplication unitary from Algorithm 1:

        |x>|0^m>|0>|0>  ->  |(c x mod N)>|0^m>|0>|0>    (up to error eta)

    Returns a Gate representing: step5 @ step4 @ step3 @ step2 @ step1
    """
    if N <= 0:
        raise ValueError("N must be positive")
    if not (0 < eta < 1):
        raise ValueError("eta must be in (0,1)")

    # n-qubit x register sufficient to hold values mod N
    n = nbits_for_modulus(N)
    m = choose_m(n, eta)

    # Layout (contiguous)
    x_reg: Tuple[int, int] = (0, n)
    z_reg: Tuple[int, int] = (n + 1, n + m+1)          # this is the "w"/phase-estimation register
    flag_ancilla: int = n + m + 1                # comparison/control ancilla

    # Step 1: produce |x>|0^m> -> |x>|w~> (via H, PhaseProduct, IQFT)
    U1 = step1(c=c, N=N, x_reg=x_reg, z_reg=z_reg)

    # Step 2: extend x with top_ancilla and add N*w into x (using U_cxq)
    x_ext_reg, U2 = step2(N=N, x_reg=x_reg, w_reg=z_reg)

    # Step 3: compute flag = [x_ext > N], then subtract N controlled by flag
    U3 = step3(N=N, x_ext_reg=x_ext_reg, flag=flag_ancilla)

    # Step 4: uncompute flag via comparison operator (cx mod N < Nw)
    U4 = step4(N=N, x_ext_reg=x_ext_reg, w_reg=z_reg, flag=flag_ancilla)

    # Step 5: uncompute w register back to |0^m>
    U5 = step5(c=c, N=N, eta=eta, x_ext_reg=x_ext_reg, w_reg=z_reg)

    # Full algorithm: 5 ∘ 4 ∘ 3 ∘ 2 ∘ 1
    return U5 @ U4 @ U3 @ U2 @ U1

# ----------------------------------------------------------------------------------------
# ---------------------------------Controlled Version-------------------------------------
# ----------------------------------------------------------------------------------------

def CH(target: int, ctrl: int) -> Gate:
    """Controlled-H on one qubit (symbolic)."""
    return PrimGate("CH", (ctrl, target))

def CH_reg(reg: Tuple[int, int], ctrl: int) -> Gate:
    """Controlled H^{⊗m} over a contiguous register interval."""
    lo, hi = reg
    if lo >= hi:
        return PrimGate("ID", None)
    U = CH(lo, ctrl)
    for q in range(lo + 1, hi):
        U = CH(q, ctrl) @ U
    return U

def CQFT(reg: Tuple[int, int], ctrl: int) -> Gate:
    """Controlled QFT on a register (symbolic primitive)."""
    return PrimGate("CQFT", (ctrl, reg))

def CIQFT(reg: Tuple[int, int], ctrl: int) -> Gate:
    """Controlled inverse QFT on a register (symbolic primitive)."""
    return PrimGate("CIQFT", (ctrl, reg))



def step1_ctrl(c: int, N: int, x_reg: Tuple[int,int], z_reg: Tuple[int,int], ctrl: int) -> Gate:
    phi = (2.0 * math.pi * ((c - 1) % N)) / float(N)
    return CIQFT(z_reg, ctrl) @ CPhaseProduct(control=ctrl, phi=phi, x_reg=x_reg, z_reg=z_reg) @ CH_reg(z_reg, ctrl)

def step2_ctrl(N: int, x_reg: Tuple[int,int], w_reg: Tuple[int,int], ctrl: int):
    x_ext = (x_reg[0], x_reg[1] + 1)
    return x_ext, C_U_cxq(ctrl=ctrl, x_reg=w_reg, z_reg=x_ext, a=N)


# ============================================================
# Controlled variants of the *specific* Step3/Step4 primitives
# ============================================================

def CCMP_GT_CONST(ctrl: int, x_reg: Tuple[int, int], N: int, flag: int) -> Gate:
    """
    Controlled compare:
      if ctrl=1: flag ^= [ value(x_reg) > N ]
      else: do nothing
    """
    return PrimGate("CCMP_GT_CONST", (ctrl, x_reg, N, flag))

def CCSUB_CONST(ctrl: int, flag: int, x_reg: Tuple[int, int], N: int) -> Gate:
    """
    Controlled subtract:
      if ctrl=1 and flag=1: x_reg <- x_reg - N
      else: do nothing
    """
    return PrimGate("CCSUB_CONST", (ctrl, flag, x_reg, N))

def CCMP_LT_NW(ctrl: int, x_reg: Tuple[int, int], w_reg: Tuple[int, int], N: int, flag: int) -> Gate:
    """
    Controlled uncompute-compare:
      if ctrl=1: uncompute flag via (x_reg < N*w_reg) comparison rule used in Step 4
      else: do nothing
    """
    return PrimGate("CCMP_LT_NW", (ctrl, x_reg, w_reg, N, flag))


def step3_ctrl(N: int, x_ext_reg: Tuple[int, int], flag: int, ctrl: int) -> Gate:
    """
    Controlled Step 3:
      if ctrl=1:
        flag := [x_ext > N]
        if flag: x_ext -= N
      else identity
    """
    return CCSUB_CONST(ctrl, flag, x_ext_reg, N) @ CCMP_GT_CONST(ctrl, x_ext_reg, N, flag)


def step4_ctrl(N: int, x_ext_reg: Tuple[int, int], w_reg: Tuple[int, int], flag: int, ctrl: int) -> Gate:
    """
    Controlled Step 4:
      if ctrl=1: uncompute flag using the comparison operator
      else identity
    """
    return CCMP_LT_NW(ctrl, x_ext_reg, w_reg, N, flag)


def step5_ctrl(c: int, N: int, x_ext_reg: Tuple[int, int], w_reg: Tuple[int, int], ctrl: int) -> Gate:
    """
    Controlled Step 5 as the inverse-style uncompute using negative phase.
    """
    c_inv = pow(c, -1, N)
    k5 = (1 - c_inv) % N
    phi = (2.0 * math.pi * k5) / float(N)
    return CIQFT(w_reg, ctrl) @ CPhaseProduct(control=ctrl, phi=-phi, x_reg=x_ext_reg, z_reg=w_reg) @ CH_reg(w_reg, ctrl)

def mod_mul_InPlace_ctrl(ctrl: int, c: int, N: int, eta: float) -> Gate:
    """
    Fully controlled Algorithm-1 in-place modular multiplication:
      ctrl=0: identity
      ctrl=1: perform the 5 steps

    Uses the same contiguous layout as your mod_mul_InPlace().
    """
    if N <= 0:
        raise ValueError("N must be positive")
    if not (0 < eta < 1):
        raise ValueError("eta must be in (0,1)")

    n = nbits_for_modulus(N)
    m = choose_m(n, eta)

    x_reg: Tuple[int, int] = (0, n)
    w_reg: Tuple[int, int] = (n + 1, n + m + 1)
    flag_ancilla: int = n + m + 1

    U1 = step1_ctrl(c, N, eta, x_reg, w_reg, ctrl)
    x_ext_reg, U2 = step2_ctrl(N, x_reg, w_reg, ctrl)
    U3 = step3_ctrl(N, x_ext_reg, flag_ancilla, ctrl)
    U4 = step4_ctrl(N, x_ext_reg, w_reg, flag_ancilla, ctrl)
    U5 = step5_ctrl(c, N, eta, x_ext_reg, w_reg, ctrl)

    return U5 @ U4 @ U3 @ U2 @ U1



@dataclass(frozen=True)
class Shifted(Gate):
    """
    Wrap a gate but indicate it should act on qubits shifted by an offset.
    Evaluator can implement this by rewriting all qubit indices in tags/meta.

    This avoids rewriting mod_mul_InPlace_ctrl which hard-codes
    x_reg=(0,n), w_reg=(n+1,...), etc.
    """
    offset: int
    U: Gate

    def __repr__(self) -> str:
        return f"Shifted(offset={self.offset}, U={self.U})"


def shift_gate(U: Gate, offset: int) -> Gate:
    """Convenience constructor."""
    if offset == 0:
        return U
    return Shifted(offset=offset, U=U)


def modexp_inplace(a: int, N: int, eta: float,
                   x_reg: Tuple[int, int],
                   y_reg: Tuple[int, int]) -> Gate:
    """
    Symbolic modular exponentiation using repeated controlled in-place modular multiplication.

    Intended action (standard Shor primitive, extended by linearity):
        |x>|y>  ->  |x>| y * a^x mod N >

    Typical usage for Shor:
        y starts as |1>, so output is |a^x mod N>.

    Inputs:
      - a, N: integers (Shor instance)
      - eta: error target for each controlled multiplier
      - x_reg: (lo, hi) exponent register (bits x_0..x_{t-1})
      - y_reg: (lo, hi) value register holding numbers mod N (n qubits)

    Construction:
      For k=0..t-1:
        c_k = a^(2^k) mod N  (classically precomputed)
        apply controlled in-place multiply-by-c_k on y, controlled by x_k.
    """
    # sanity
    n = nbits_for_modulus(N)
    if (y_reg[1] - y_reg[0]) != n:
        raise ValueError(f"y_reg must have length n={n} (got {y_reg[1]-y_reg[0]})")
    t = x_reg[1] - x_reg[0]
    if t <= 0:
        return PrimGate("ID", None)
    
    # Build product of controlled multiplications:
    U_total: Gate = PrimGate("ID", None)

    for k in range(t):
        ctrl_qubit = x_reg[0] + k
        c_k = pow(a, 1 << k, N)  # a^(2^k) mod N

        # Build the controlled in-place multiplier circuit
        U_k_local = mod_mul_InPlace_ctrl(ctrl=ctrl_qubit, c=c_k, N=N, eta=eta)

        # Shift that local layout so that its "y_reg=(0,n)" aligns to your actual y_reg.
        # local y_reg starts at 0, actual y_reg starts at y_reg[0]
        U_k = shift_gate(U_k_local, offset=y_reg[0])

        # Compose
        U_total = U_k @ U_total

    return U_total

