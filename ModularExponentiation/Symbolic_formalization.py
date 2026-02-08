from __future__ import annotations
import numpy as np
from dataclasses import dataclass
from typing import Any, Callable, Dict, Hashable, Protocol, runtime_checkable, Sequence

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


