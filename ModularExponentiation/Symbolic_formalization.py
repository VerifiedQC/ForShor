from __future__ import annotations
import numpy as np
from dataclasses import dataclass
import math
from typing import Any, Callable, Dict, Hashable, Protocol, runtime_checkable, Sequence, Tuple

# ============================================================
# Basic scalars / labels
# ============================================================

Scalar = complex
Basis = Hashable  

# ============================================================
# Symbolic layer: states + gates 
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

    # dagger 
    def __invert__(self) -> "Gate":
        return Adjoint(self)

    def __rmul__(self, a: Scalar) -> "Gate":
        return ScaleGate(a, self)



@dataclass(frozen=True)
class PrimGate(Gate):
    """
    Opaque primitive gate.
    Examples:
      PrimGate("H", 0)
      PrimGate("CNOT", (0,1))
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
    """ U† """
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
# Shor's Algorithm gates
# ============================================================

def H(target: int ) -> Gate:
    """
    Symbolic Hadamard gate.
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



@dataclass(frozen=True)
class PhaseProduct(Gate):
    """
    PhaseProduct(phi, x_reg, z_reg) acts as:
      |x>|z> -> exp(i * phi * x * z) |x>|z>
    where x and z are the integer values encoded by those registers.
    """
    phi: Scalar
    x_reg: Tuple[int, int]
    z_reg: Tuple[int, int]

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
    Symbolic H^{m} on the register r.
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


# Step 2:
def step2(N: int, x_reg: Tuple[int,int], w_reg: Tuple[int,int]):
    """
    Step 2:
      extend x with a top ancilla bit (n -> n+1),
      then compute |x>|w> -> |x + N*w>|w>  (mod 2^(n+1))
    where w is stored as an m-bit fraction (integer w_int representing w_int / 2^m).

    """
    x_ext = (x_reg[0], x_reg[1] + 1)  # n+1 qubits
    n1 = reg_len(x_ext)
    m  = reg_len(w_reg)

    phi = 2.0 * math.pi * N / float(1 << (m + n1))

    U = IQFT(x_ext) @ PhaseProduct(phi=phi, x_reg=w_reg, z_reg=x_ext) @ QFT(x_ext)
    return x_ext, U

# ============================================================
# Steps 3, 4, 5 for Algorithm 1
# ============================================================


from dataclasses import dataclass
import math
from typing import Any, Tuple

# --- Comparison / controlled-sub primitives ----

def CMP_GE_CONST(x_reg: Tuple[int, int], N: int, flag: int) -> Gate:
    """
    flag ^= [ value(x_reg) >= N ].
    """
    return PrimGate("CMP_GE_CONST", (x_reg, N, flag))

def CSUB_CONST(flag: int, x_reg: Tuple[int, int], N: int) -> Gate:
    """
    If flag==1, do x_reg <- x_reg - N (in-place).
    """
    return PrimGate("CSUB_CONST", (flag, x_reg, N))

def CMP_LT_NW(x_reg: Tuple[int, int], w_reg: Tuple[int, int], N: int, flag: int) -> Gate:
    """
    Uncompute flag by comparing whether (left) < N*w,
    where w_reg stores an m-bit fraction as an integer w_int and N*w means floor(N*w_int/2^m).
    """
    return PrimGate("CMP_LT_NW", (x_reg, w_reg, N, flag))


# --- Step 3 -------------------------------------------------

def step3(N: int, x_ext_reg: Tuple[int, int], flag: int) -> Gate:
    """
    Step 3:
      flag := [x_ext >= N]
      if flag: x_ext -= N
    """
    return CSUB_CONST(flag, x_ext_reg, N) @ CMP_GE_CONST(x_ext_reg, N, flag)


# --- Step 4 ----------------------------------------------------

def step4(N: int, x_ext_reg: Tuple[int, int], w_reg: Tuple[int, int], flag: int) -> Gate:
    """
    Step 4:
      uncompute flag via the paper’s comparison operator
      (semantics live in evaluator).
    """
    return CMP_LT_NW(x_ext_reg, w_reg, N, flag)



# Step 5: MUST be the inverse unitary of a Step-1-style frac loader

def frac_load(k: int, N: int, x_reg: Tuple[int,int], w_reg: Tuple[int,int]) -> Gate:
    """
    Same structure as Step 1:
      |x>|0^m> -> |x>|~w>
    where ~w approximates ((k*x mod N)/N) as an m-bit fraction.
    """
    phi = (2.0 * math.pi * (k % N)) / float(N)
    return IQFT(w_reg) @ PhaseProduct(phi=phi, x_reg=x_reg, z_reg=w_reg) @ H_reg(w_reg)

def step5(c: int, N: int, eta: float, x_ext_reg: Tuple[int,int], w_reg: Tuple[int,int]) -> Gate:
    """
    Step 5:
      uncompute w by applying the adjoint of the frac loader with k = (1 - c^{-1}) mod N
    """
    c_inv = pow(c, -1, N)
    k5 = (1 - c_inv) % N
    return ~frac_load(k5, N, x_ext_reg, w_reg)




# ============================================================
# Algorithm 1: In-place modular multiplication
# ============================================================

def mod_mul_InPlace(c: int, N: int, eta: float) -> Gate:
    """
    In-place classical-quantum modular multiplication :
        |x>|0^m>|0>|0>  ->  |(c x mod N)>|0^m>|0>|0>    (up to error eta)
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

    # Step 1: load w = ((c-1)x mod N)/N into w_reg
    U1 = step1(c=c, N=N, x_reg=x_reg, z_reg=w_reg)

    # Step 2: extend x and add N*w into x 
    x_ext_reg, U2 = step2(N=N, x_reg=x_reg, w_reg=w_reg)

    # Step 3: flag := [x_ext >= N]; x_ext -= N if flag
    U3 = step3(N=N, x_ext_reg=x_ext_reg, flag=flag_ancilla)

    # Step 4: uncompute flag
    U4 = step4(N=N, x_ext_reg=x_ext_reg, w_reg=w_reg, flag=flag_ancilla)

    # Step 5: uncompute w_reg back to |0^m>
    U5 = step5(c=c, N=N, eta=eta, x_ext_reg=x_ext_reg, w_reg=w_reg)

    return U5 @ U4 @ U3 @ U2 @ U1


# ----------------------------------------------------------------------------------------
# ---------------------------------Controlled Version ------------------------------------
# ----------------------------------------------------------------------------------------

def CH(target: int, ctrl: int) -> Gate:
    return PrimGate("CH", (ctrl, target))

def CH_reg(reg: Tuple[int, int], ctrl: int) -> Gate:
    lo, hi = reg
    if lo >= hi:
        return PrimGate("ID", None)
    U = CH(lo, ctrl)
    for q in range(lo + 1, hi):
        U = CH(q, ctrl) @ U
    return U

def CQFT(reg: Tuple[int, int], ctrl: int) -> Gate:
    return PrimGate("CQFT", (ctrl, reg))

def CIQFT(reg: Tuple[int, int], ctrl: int) -> Gate:
    return PrimGate("CIQFT", (ctrl, reg))


def step1_ctrl(c: int, N: int, x_reg: Tuple[int,int], w_reg: Tuple[int,int], ctrl: int) -> Gate:
    phi = (2.0 * math.pi * ((c - 1) % N)) / float(N)
    return CIQFT(w_reg, ctrl) @ CPhaseProduct(control=ctrl, phi=phi, x_reg=x_reg, z_reg=w_reg) @ CH_reg(w_reg, ctrl)


def step2_ctrl(N: int, x_reg: Tuple[int,int], w_reg: Tuple[int,int], ctrl: int):
    """
    Controlled Step 2 (matches fixed Step 2 structure).
    """
    x_ext = (x_reg[0], x_reg[1] + 1)
    n1 = reg_len(x_ext)
    m  = reg_len(w_reg)

    phi = 2.0 * math.pi * N / float(1 << (m + n1))

    U = CIQFT(x_ext, ctrl) @ CPhaseProduct(control=ctrl, phi=phi, x_reg=w_reg, z_reg=x_ext) @ CQFT(x_ext, ctrl)
    return x_ext, U


# Controlled compare/sub primitives
def CCMP_GE_CONST(ctrl: int, x_reg: Tuple[int, int], N: int, flag: int) -> Gate:
    """
    if ctrl=1: flag ^= [value(x_reg) >= N]
    """
    return PrimGate("CCMP_GE_CONST", (ctrl, x_reg, N, flag))

def CCSUB_CONST(ctrl: int, flag: int, x_reg: Tuple[int, int], N: int) -> Gate:
    """
    if ctrl=1 and flag=1: x_reg <- x_reg - N
    """
    return PrimGate("CCSUB_CONST", (ctrl, flag, x_reg, N))

def CCMP_LT_NW(ctrl: int, x_reg: Tuple[int, int], w_reg: Tuple[int, int], N: int, flag: int) -> Gate:
    return PrimGate("CCMP_LT_NW", (ctrl, x_reg, w_reg, N, flag))


def step3_ctrl(N: int, x_ext_reg: Tuple[int, int], flag: int, ctrl: int) -> Gate:
    return CCSUB_CONST(ctrl, flag, x_ext_reg, N) @ CCMP_GE_CONST(ctrl, x_ext_reg, N, flag)

def step4_ctrl(N: int, x_ext_reg: Tuple[int, int], w_reg: Tuple[int, int], flag: int, ctrl: int) -> Gate:
    return CCMP_LT_NW(ctrl, x_ext_reg, w_reg, N, flag)


def frac_load_ctrl(k: int, N: int, x_reg: Tuple[int,int], w_reg: Tuple[int,int], ctrl: int) -> Gate:
    phi = (2.0 * math.pi * (k % N)) / float(N)
    return CIQFT(w_reg, ctrl) @ CPhaseProduct(control=ctrl, phi=phi, x_reg=x_reg, z_reg=w_reg) @ CH_reg(w_reg, ctrl)

def step5_ctrl(c: int, N: int, eta: float, x_ext_reg: Tuple[int, int], w_reg: Tuple[int, int], ctrl: int) -> Gate:
    """
    Controlled Step 5: adjoint of frac_load_ctrl(k5,...).
    """
    c_inv = pow(c, -1, N)
    k5 = (1 - c_inv) % N
    return ~frac_load_ctrl(k5, N, x_ext_reg, w_reg, ctrl)


def mod_mul_InPlace_ctrl(ctrl: int, c: int, N: int, eta: float) -> Gate:
    """
    Controlled Algorithm-1 in-place modular multiplication:
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

    U1 = step1_ctrl(c, N, x_reg, w_reg, ctrl)
    x_ext_reg, U2 = step2_ctrl(N, x_reg, w_reg, ctrl)
    U3 = step3_ctrl(N, x_ext_reg, flag_ancilla, ctrl)
    U4 = step4_ctrl(N, x_ext_reg, w_reg, flag_ancilla, ctrl)
    U5 = step5_ctrl(c, N, eta, x_ext_reg, w_reg, ctrl)

    return U5 @ U4 @ U3 @ U2 @ U1


# ----------------------------------------------------------------------------------------
# Shift wrapper 
# ----------------------------------------------------------------------------------------

@dataclass(frozen=True)
class Shifted(Gate):
    offset: int
    U: Gate
    def __repr__(self) -> str:
        return f"Shifted(offset={self.offset}, U={self.U})"

def shift_gate(U: Gate, offset: int) -> Gate:
    if offset == 0:
        return U
    return Shifted(offset=offset, U=U)


# ----------------------------------------------------------------------------------------
# Modular exponentiation using controlled in-place mod-mul
# ----------------------------------------------------------------------------------------

def modexp_inplace(a: int, N: int, eta: float,
                   x_reg: Tuple[int, int],
                   y_reg: Tuple[int, int]) -> Gate:
    n = nbits_for_modulus(N)
    if (y_reg[1] - y_reg[0]) != n:
        raise ValueError(f"y_reg must have length n={n} (got {y_reg[1]-y_reg[0]})")
    t = x_reg[1] - x_reg[0]
    if t <= 0:
        return PrimGate("ID", None)

    U_total: Gate = PrimGate("ID", None)

    for k in range(t):
        ctrl_qubit = x_reg[0] + k
        c_k = pow(a, 1 << k, N)

        U_k_local = mod_mul_InPlace_ctrl(ctrl=ctrl_qubit, c=c_k, N=N, eta=eta)
        U_k = shift_gate(U_k_local, offset=y_reg[0])
        U_total = U_k @ U_total

    return U_total
