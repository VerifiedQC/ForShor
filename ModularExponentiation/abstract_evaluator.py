from __future__ import annotations
from Symbolic_formalization import *
from dataclasses import dataclass
import math
import cmath
from typing import Any, Tuple, Sequence, Dict, Optional

import numpy as np

# ============================================================
# Bit/register helpers
# ============================================================

def _get_bit(index: int, q: int) -> int:
    return (index >> q) & 1

def _flip_bit(index: int, q: int) -> int:
    return index ^ (1 << q)

def _get_reg_value(index: int, reg: Tuple[int, int]) -> int:
    lo, hi = reg
    v = 0
    for i, q in enumerate(range(lo, hi)):
        v |= (_get_bit(index, q) << i)
    return v

def _set_reg_value(index: int, reg: Tuple[int, int], value: int) -> int:
    lo, hi = reg
    for i, q in enumerate(range(lo, hi)):
        bit = (value >> i) & 1
        if _get_bit(index, q) != bit:
            index = _flip_bit(index, q)
    return index

def _reg_len(reg: Tuple[int, int]) -> int:
    return reg[1] - reg[0]


# ============================================================
# Numpy statevector backend
# ============================================================

@dataclass
class NumpyState:
    nqubits: int
    amp: np.ndarray  # complex vector of length 2^n

    def copy(self) -> "NumpyState":
        return NumpyState(self.nqubits, self.amp.copy())

    @staticmethod
    def basis(nqubits: int, index: int) -> "NumpyState":
        v = np.zeros((1 << nqubits,), dtype=np.complex128)
        v[index] = 1.0 + 0.0j
        return NumpyState(nqubits, v)


# ============================================================
# Low-level gate application to a statevector
# ============================================================

def _apply_single_qubit_unitary(psi: np.ndarray, n: int, q: int, U2: np.ndarray) -> np.ndarray:
    out = psi.copy()
    stride = 1 << q
    block = stride << 1
    for base in range(0, 1 << n, block):
        for off in range(stride):
            i0 = base + off
            i1 = i0 + stride
            a0 = psi[i0]
            a1 = psi[i1]
            out[i0] = U2[0, 0] * a0 + U2[0, 1] * a1
            out[i1] = U2[1, 0] * a0 + U2[1, 1] * a1
    return out


def _apply_two_qubit_unitary(psi: np.ndarray, n: int, q1: int, q2: int, U4: np.ndarray) -> np.ndarray:
    if q1 == q2:
        raise ValueError("q1 and q2 must be distinct")
    a, b = sorted((q1, q2))
    out = psi.copy()

    for idx in range(1 << n):
        # only update each 4-tuple once: enforce bits at a,b both 0
        if _get_bit(idx, a) or _get_bit(idx, b):
            continue

        i00 = idx
        i01 = _flip_bit(idx, b)
        i10 = _flip_bit(idx, a)
        i11 = _flip_bit(i10, b)

        v = np.array([psi[i00], psi[i01], psi[i10], psi[i11]], dtype=np.complex128)
        w = U4 @ v
        out[i00], out[i01], out[i10], out[i11] = w[0], w[1], w[2], w[3]

    return out

def _apply_controlled_single(psi: np.ndarray, n: int, ctrl: int, tgt: int, U2: np.ndarray) -> np.ndarray:
    out = psi.copy()
    stride = 1 << tgt
    block = stride << 1
    for base in range(0, 1 << n, block):
        for off in range(stride):
            i0 = base + off
            i1 = i0 + stride
            if _get_bit(i0, ctrl) == 0:
                continue
            a0 = psi[i0]
            a1 = psi[i1]
            out[i0] = U2[0, 0] * a0 + U2[0, 1] * a1
            out[i1] = U2[1, 0] * a0 + U2[1, 1] * a1
    return out



def _apply_diagonal_phase_product(
    psi: np.ndarray,
    n: int,
    phi: complex,
    x_reg: Tuple[int, int],
    z_reg: Tuple[int, int],
    ctrl: Optional[int] = None,
) -> np.ndarray:
    out = psi.copy()
    for idx in range(1 << n):
        if ctrl is not None and _get_bit(idx, ctrl) == 0:
            continue
        x = _get_reg_value(idx, x_reg)
        z = _get_reg_value(idx, z_reg)
        out[idx] *= cmath.exp(1j * phi * x * z)
    return out


def _apply_permutation(psi: np.ndarray, perm: np.ndarray) -> np.ndarray:
    # out[new_index] = psi[old_index] with new_index = perm[old_index]
    out = np.zeros_like(psi)
    out[perm] = psi
    return out


def _qft_matrix(k: int) -> np.ndarray:
    N = 1 << k
    omega = np.exp(2j * np.pi / N)
    j = np.arange(N).reshape(N, 1)
    l = np.arange(N).reshape(1, N)
    M = omega ** (j * l) / math.sqrt(N)
    return M


def _apply_qft_on_register(psi: np.ndarray, n: int, reg: Tuple[int, int], inverse: bool) -> np.ndarray:
    lo, hi = reg
    k = hi - lo
    if k <= 0:
        return psi
    F = _qft_matrix(k)
    if inverse:
        F = np.conjugate(F.T)

    out = np.zeros_like(psi)
    # group amplitudes by "rest" bits; apply F to the reg subspace
    for rest in range(1 << n):
        ok = True
        for q in range(lo, hi):
            if _get_bit(rest, q):
                ok = False
                break
        if not ok:
            continue

        vec = np.zeros((1 << k,), dtype=np.complex128)
        indices = np.zeros((1 << k,), dtype=np.int64)

        for z in range(1 << k):
            idx = rest
            # set reg bits to z
            for i, q in enumerate(range(lo, hi)):
                if (z >> i) & 1:
                    idx |= (1 << q)
            indices[z] = idx
            vec[z] = psi[idx]

        vec2 = F @ vec
        out[indices] = vec2

    return out


# ============================================================
# Shifting
# ============================================================


def shift_gate_ast(U: "Gate", offset: int) -> "Gate":
    from dataclasses import replace, is_dataclass

    if offset == 0:
        return U

    if U.__class__.__name__ == "Shifted":
        return U.__class__(offset=U.offset + offset, U=U.U)

    if U.__class__.__name__ == "PrimGate":
        tag = U.tag
        meta = U.meta

        def sh_reg(r: Tuple[int, int]) -> Tuple[int, int]:
            return (r[0] + offset, r[1] + offset)

        if tag in {"H", "X", "Z"}:
            return U.__class__(tag=tag, meta=int(meta) + offset)

        if tag in {"CNOT", "SWAP", "CH"}:
            a, b = meta
            return U.__class__(tag=tag, meta=(int(a) + offset, int(b) + offset))

        if tag == "PHASE":
            q, theta = meta
            return U.__class__(tag=tag, meta=(int(q) + offset, theta))

        if tag == "CPHASE":
            ctrl, tgt, theta = meta
            return U.__class__(tag=tag, meta=(int(ctrl) + offset, int(tgt) + offset, theta))

        if tag in {"QFT", "IQFT"}:
            qs = meta
            if isinstance(qs, tuple) and len(qs) == 2 and all(isinstance(x, int) for x in qs):
                lo, hi = qs
                return U.__class__(tag=tag, meta=(lo + offset, hi + offset))
            return U.__class__(tag=tag, meta=[int(q) + offset for q in list(qs)])

        if tag in {"CQFT", "CIQFT"}:
            ctrl, reg = meta
            return U.__class__(tag=tag, meta=(int(ctrl) + offset, sh_reg(reg)))

        if tag == "CMP_GE_CONST":
            x_reg, Nconst, flag = meta
            return U.__class__(tag=tag, meta=(sh_reg(x_reg), Nconst, int(flag) + offset))

        if tag == "CSUB_CONST":
            flag, x_reg, Nconst = meta
            return U.__class__(tag=tag, meta=(int(flag) + offset, sh_reg(x_reg), Nconst))

        if tag == "CMP_LT_NW":
            x_reg, w_reg, Nconst, flag = meta
            return U.__class__(tag=tag, meta=(sh_reg(x_reg), sh_reg(w_reg), Nconst, int(flag) + offset))

        if tag == "CCMP_GE_CONST":
            ctrl, x_reg, Nconst, flag = meta
            return U.__class__(tag=tag, meta=(int(ctrl) + offset, sh_reg(x_reg), Nconst, int(flag) + offset))

        if tag == "CCSUB_CONST":
            ctrl, flag, x_reg, Nconst = meta
            return U.__class__(tag=tag, meta=(int(ctrl) + offset, int(flag) + offset, sh_reg(x_reg), Nconst))

        if tag == "CCMP_LT_NW":
            ctrl, x_reg, w_reg, Nconst, flag = meta
            return U.__class__(tag=tag, meta=(int(ctrl) + offset, sh_reg(x_reg), sh_reg(w_reg), Nconst, int(flag) + offset))

        if tag in {"CQMulFracSub", "CQMulFracAdd"}:
            k, Nconst, x_reg, w_reg = meta
            return U.__class__(tag=tag, meta=(k, Nconst, sh_reg(x_reg), sh_reg(w_reg)))

        return U

    if U.__class__.__name__ == "Compose":
        return U.__class__(U2=shift_gate_ast(U.U2, offset), U1=shift_gate_ast(U.U1, offset))

    if U.__class__.__name__ == "Adjoint":
        return U.__class__(U=shift_gate_ast(U.U, offset))

    if U.__class__.__name__ == "ScaleGate":
        return U.__class__(a=U.a, U=shift_gate_ast(U.U, offset))

    if U.__class__.__name__ == "QFT":
        qs = U.qubits
        if isinstance(qs, tuple) and len(qs) == 2 and all(isinstance(x, int) for x in qs):
            lo, hi = qs
            return U.__class__(qubits=(lo + offset, hi + offset))
        return U.__class__(qubits=[int(q) + offset for q in list(qs)])

    if U.__class__.__name__ == "PhaseProduct":
        x = (U.x_reg[0] + offset, U.x_reg[1] + offset)
        z = (U.z_reg[0] + offset, U.z_reg[1] + offset)
        return U.__class__(phi=U.phi, x_reg=x, z_reg=z)

    if U.__class__.__name__ == "CPhaseProduct":
        x = (U.x_reg[0] + offset, U.x_reg[1] + offset)
        z = (U.z_reg[0] + offset, U.z_reg[1] + offset)
        return U.__class__(control=U.control + offset, phi=U.phi, x_reg=x, z_reg=z)

    if U.__class__.__name__ == "CQMulFracSub":
        x = (U.x_reg[0] + offset, U.x_reg[1] + offset)
        w = (U.w_reg[0] + offset, U.w_reg[1] + offset)
        return U.__class__(k=U.k, N=U.N, eta=U.eta, x_reg=x, w_reg=w)

    if is_dataclass(U):
        def looks_like_reg(t: Any) -> bool:
            return (
                isinstance(t, tuple) and len(t) == 2
                and isinstance(t[0], int) and isinstance(t[1], int)
                and t[0] >= 0 and t[1] > t[0]
                and (t[1] - t[0]) <= 128
            )

        def sh_any(x: Any) -> Any:
            if isinstance(x, Gate):
                return shift_gate_ast(x, offset)
            if looks_like_reg(x):
                return (x[0] + offset, x[1] + offset)
            if isinstance(x, list):
                return [sh_any(y) for y in x]
            if isinstance(x, tuple):
                return tuple(sh_any(y) for y in x)
            if isinstance(x, dict):
                return {sh_any(k): sh_any(v) for k, v in x.items()}
            if isinstance(x, range):
                return range(x.start + offset, x.stop + offset, x.step)
            if is_dataclass(x):
                kwargs2 = {f.name: sh_any(getattr(x, f.name)) for f in x.__dataclass_fields__.values()}  # type: ignore
                try:
                    return replace(x, **kwargs2)
                except Exception:
                    return x
            return x

        kwargs = {f.name: sh_any(getattr(U, f.name)) for f in U.__dataclass_fields__.values()}  # type: ignore
        try:
            return replace(U, **kwargs)
        except Exception:
            return U

    return U



# ============================================================
# Numpy evaluator for your Gate AST
# ============================================================

class NumpyGateEvaluator:
    """
    Concrete evaluator for Gate -> (statevector transformer)
    """

    def __init__(self):
        self._cache: Dict[int, Any] = {}
    def dagger(self, U: "Gate") -> "Gate":
        if U.__class__.__name__ == "Compose":
            return Compose(U2=self.dagger(U.U1), U1=self.dagger(U.U2))
        
        if U.__class__.__name__ == "Adjoint":
            return U.U

        if U.__class__.__name__ == "ScaleGate":
            return U.__class__(a=complex(U.a).conjugate(), U=self.dagger(U.U))

        if U.__class__.__name__ == "QFT":
            return PrimGate("IQFT", U.qubits)

        # PhaseProduct† = PhaseProduct with -phi
        if U.__class__.__name__ == "PhaseProduct":
            return U.__class__(phi=-U.phi, x_reg=U.x_reg, z_reg=U.z_reg)

        if U.__class__.__name__ == "CPhaseProduct":
            return U.__class__(control=U.control, phi=-U.phi, x_reg=U.x_reg, z_reg=U.z_reg)

        if U.__class__.__name__ == "CQMulFracSub":
            return PrimGate("CQMulFracAdd", (U.k, U.N, U.x_reg, U.w_reg))

        if U.__class__.__name__ == "Shifted":
            return U.__class__(offset=U.offset, U=self.dagger(U.U))

        if U.__class__.__name__ == "PrimGate":
            tag, meta = U.tag, U.meta

            if tag in {"ID", "H", "X", "Z", "CNOT", "SWAP", "CH"}:
                return U 
            
            
            
            if tag == "PHASE":
                q, theta = meta
                return PrimGate("PHASE", (q, -float(theta)))

            if tag == "CPHASE":
                ctrl, tgt, theta = meta
                return PrimGate("CPHASE", (ctrl, tgt, -float(theta)))

            if tag == "CQFT":
                ctrl, reg = meta
                return PrimGate("CIQFT", (ctrl, reg))

            if tag == "CIQFT":
                ctrl, reg = meta
                return PrimGate("CQFT", (ctrl, reg))

            # Comparators/subtracts are involutions (permutations = self-adjoint)
            if tag in {
                "CMP_GE_CONST", "CSUB_CONST", "CMP_LT_NW",
                "CCMP_GE_CONST", "CCSUB_CONST", "CCMP_LT_NW",
            }:
                return U

        raise NotImplementedError(f"dagger not defined for node: {U}")


    def apply_gate(self, st: NumpyState, U: "Gate") -> NumpyState:
        # Unwrap/normalize Shifted by rewriting the AST
        if U.__class__.__name__ == "Shifted":
            U2 = shift_gate_ast(U.U, U.offset)
            return self.apply_gate(st, U2)

        # Structural gates
        if U.__class__.__name__ == "Compose":
            st1 = self.apply_gate(st, U.U1)
            return self.apply_gate(st1, U.U2)


        if U.__class__.__name__ == "Adjoint":
            return self.apply_gate(st, self.dagger(U.U))

        if U.__class__.__name__ == "ScaleGate":
            out = st.copy()
            out.amp *= U.a
            return out

        if U.__class__.__name__ == "QFT":
            qs = U.qubits
            if isinstance(qs, tuple) and len(qs) == 2 and isinstance(qs[0], int) and isinstance(qs[1], int):
                reg = (qs[0], qs[1])
            else:
                qlist = list(qs)
                reg = (min(qlist), max(qlist) + 1)

            out = st.copy()
            out.amp = _apply_qft_on_register(out.amp, out.nqubits, reg, inverse=False)
            return out

        if U.__class__.__name__ == "PhaseProduct":
            out = st.copy()
            out.amp = _apply_diagonal_phase_product(out.amp, out.nqubits, U.phi, U.x_reg, U.z_reg, ctrl=None)
            return out

        if U.__class__.__name__ == "CPhaseProduct":
            out = st.copy()
            out.amp = _apply_diagonal_phase_product(out.amp, out.nqubits, U.phi, U.x_reg, U.z_reg, ctrl=U.control)
            return out

        if U.__class__.__name__ == "CQMulFracSub":
            out = st.copy()
            out.amp = self._apply_cqmul_frac_sub(out.amp, out.nqubits, U.k, U.N, U.x_reg, U.w_reg)
            return out

        if U.__class__.__name__ == "PrimGate":
            return self._apply_prim(st, U.tag, U.meta)

        raise TypeError(f"Unsupported gate node: {type(U)}")
    # ---------------- primitives ----------------

    def _apply_prim(self, st: NumpyState, tag: Any, meta: Any) -> NumpyState:
        n = st.nqubits
        psi = st.amp

        if tag == "ID":
            return st

        if tag == "H":
            q = int(meta)
            H2 = np.array([[1, 1], [1, -1]], dtype=np.complex128) / math.sqrt(2.0)
            return NumpyState(n, _apply_single_qubit_unitary(psi, n, q, H2))

        if tag == "X":
            q = int(meta)
            X2 = np.array([[0, 1], [1, 0]], dtype=np.complex128)
            return NumpyState(n, _apply_single_qubit_unitary(psi, n, q, X2))

        if tag == "Z":
            q = int(meta)
            Z2 = np.array([[1, 0], [0, -1]], dtype=np.complex128)
            return NumpyState(n, _apply_single_qubit_unitary(psi, n, q, Z2))

        if tag == "PHASE":
            q, theta = meta
            U2 = np.array([[1, 0], [0, cmath.exp(1j * float(theta))]], dtype=np.complex128)
            return NumpyState(n, _apply_single_qubit_unitary(psi, n, int(q), U2))

        if tag == "CPHASE":
            ctrl, tgt, theta = meta
            U2 = np.array([[1, 0], [0, cmath.exp(1j * float(theta))]], dtype=np.complex128)
            return NumpyState(n, _apply_controlled_single(psi, n, int(ctrl), int(tgt), U2))

        if tag == "CNOT":
            ctrl, tgt = meta
            U4 = np.array(
                [
                    [1, 0, 0, 0],
                    [0, 1, 0, 0],
                    [0, 0, 0, 1],
                    [0, 0, 1, 0],
                ],
                dtype=np.complex128,
            )
            return NumpyState(n, _apply_two_qubit_unitary(psi, n, int(ctrl), int(tgt), U4))

        if tag == "SWAP":
            q1, q2 = meta
            U4 = np.array(
                [
                    [1, 0, 0, 0],
                    [0, 0, 1, 0],
                    [0, 1, 0, 0],
                    [0, 0, 0, 1],
                ],
                dtype=np.complex128,
            )
            return NumpyState(n, _apply_two_qubit_unitary(psi, n, int(q1), int(q2), U4))

        # Controlled-H
        if tag == "CH":
            ctrl, tgt = meta
            H2 = np.array([[1, 1], [1, -1]], dtype=np.complex128) / math.sqrt(2.0)
            return NumpyState(n, _apply_controlled_single(psi, n, int(ctrl), int(tgt), H2))

        # Primitive QFT / IQFT
        if tag == "QFT":
            qs = meta
            if isinstance(qs, tuple) and len(qs) == 2 and isinstance(qs[0], int) and isinstance(qs[1], int):
                reg = (qs[0], qs[1])
            else:
                qlist = list(qs)
                reg = (min(qlist), max(qlist) + 1)
            return NumpyState(n, _apply_qft_on_register(psi, n, reg, inverse=False))

        if tag == "IQFT":
            qs = meta
            if isinstance(qs, tuple) and len(qs) == 2 and isinstance(qs[0], int) and isinstance(qs[1], int):
                reg = (qs[0], qs[1])
            else:
                qlist = list(qs)
                reg = (min(qlist), max(qlist) + 1)
            return NumpyState(n, _apply_qft_on_register(psi, n, reg, inverse=True))

        # Controlled QFT primitives
        if tag == "CQFT":
            ctrl, reg = meta
            out = st.copy()
            lo, hi = reg
            out.amp = self._apply_controlled_qft(out.amp, n, int(ctrl), (lo, hi), inverse=False)
            return out

        if tag == "CIQFT":
            ctrl, reg = meta
            out = st.copy()
            lo, hi = reg
            out.amp = self._apply_controlled_qft(out.amp, n, int(ctrl), (lo, hi), inverse=True)
            return out

        # Algorithm-1 primitives
        if tag == "CMP_GE_CONST":
            x_reg, Nconst, flag = meta
            return NumpyState(n, self._perm_cmp_ge_const(psi, n, x_reg, int(Nconst), int(flag), ctrl=None))

        if tag == "CSUB_CONST":
            flag, x_reg, Nconst = meta
            return NumpyState(n, self._perm_csub_const(psi, n, int(flag), x_reg, int(Nconst), ctrl=None))

        if tag == "CMP_LT_NW":
            x_reg, w_reg, Nconst, flag = meta
            return NumpyState(n, self._perm_cmp_lt_nw(psi, n, x_reg, w_reg, int(Nconst), int(flag), ctrl=None))

        # Controlled variants
        if tag == "CCMP_GE_CONST":
            ctrl, x_reg, Nconst, flag = meta
            return NumpyState(n, self._perm_cmp_ge_const(psi, n, x_reg, int(Nconst), int(flag), ctrl=int(ctrl)))

        if tag == "CCSUB_CONST":
            ctrl, flag, x_reg, Nconst = meta
            return NumpyState(n, self._perm_csub_const(psi, n, int(flag), x_reg, int(Nconst), ctrl=int(ctrl)))

        if tag == "CCMP_LT_NW":
            ctrl, x_reg, w_reg, Nconst, flag = meta
            return NumpyState(n, self._perm_cmp_lt_nw(psi, n, x_reg, w_reg, int(Nconst), int(flag), ctrl=int(ctrl)))

        # Inverse of CQMulFracSub (add delta back)
        if tag == "CQMulFracAdd":
            k, Nconst, x_reg, w_reg = meta
            out = st.copy()
            out.amp = self._apply_cqmul_frac_add(out.amp, out.nqubits, int(k), int(Nconst), x_reg, w_reg)
            return out

        raise TypeError(f"Unsupported PrimGate tag: {tag} meta={meta}")


    # ---------------- controlled QFT helper ----------------

    def _apply_controlled_qft(self, psi: np.ndarray, n: int, ctrl: int, reg: Tuple[int, int], inverse: bool) -> np.ndarray:
        lo, hi = reg
        k = hi - lo
        if k <= 0:
            return psi
        F = _qft_matrix(k)
        if inverse:
            F = np.conjugate(F.T)

        out = psi.copy()

        for rest in range(1 << n):
            if _get_bit(rest, ctrl) != 1:
                continue
            ok = True
            for q in range(lo, hi):
                if _get_bit(rest, q):
                    ok = False
                    break
            if not ok:
                continue

            vec = np.zeros((1 << k,), dtype=np.complex128)
            indices = np.zeros((1 << k,), dtype=np.int64)

            for z in range(1 << k):
                idx = rest
                for i, q in enumerate(range(lo, hi)):
                    if (z >> i) & 1:
                        idx |= (1 << q)
                indices[z] = idx
                vec[z] = out[idx]
                
            vec2 = F @ vec
            out[indices] = vec2

        return out

    # ---------------- Algorithm-1 permutations ----------------

    def _perm_cmp_ge_const(
        self,
        psi: np.ndarray,
        n: int,
        x_reg: Tuple[int, int],
        Nconst: int,
        flag: int,
        ctrl: Optional[int],
    ) -> np.ndarray:
        perm = np.arange(1 << n, dtype=np.int64)
        for idx in range(1 << n):
            if ctrl is not None and _get_bit(idx, ctrl) == 0:
                continue
            x = _get_reg_value(idx, x_reg)
            if x >= Nconst:
                perm[idx] = _flip_bit(idx, flag)
        return _apply_permutation(psi, perm)

    def _perm_csub_const(
        self,
        psi: np.ndarray,
        n: int,
        flag: int,
        x_reg: Tuple[int, int],
        Nconst: int,
        ctrl: Optional[int],
    ) -> np.ndarray:
        L = _reg_len(x_reg)
        mod = 1 << L
        perm = np.arange(1 << n, dtype=np.int64)
        for idx in range(1 << n):
            if ctrl is not None and _get_bit(idx, ctrl) == 0:
                continue
            if _get_bit(idx, flag) == 0:
                continue
            x = _get_reg_value(idx, x_reg)
            x2 = (x - (Nconst % mod)) % mod
            perm[idx] = _set_reg_value(idx, x_reg, x2)
        return _apply_permutation(psi, perm)

    def _perm_cmp_lt_nw(
        self,
        psi: np.ndarray,
        n: int,
        x_reg: Tuple[int, int],
        w_reg: Tuple[int, int],
        Nconst: int,
        flag: int,
        ctrl: Optional[int],
    ) -> np.ndarray:
        """
        Implements step 4's “compare cx mod N < Nw”
        """
        m = _reg_len(w_reg)
        denom = 1 << m
        perm = np.arange(1 << n, dtype=np.int64)
        for idx in range(1 << n):
            if ctrl is not None and _get_bit(idx, ctrl) == 0:
                continue
            x = _get_reg_value(idx, x_reg)
            w_int = _get_reg_value(idx, w_reg)
            Nw = (Nconst * w_int) // denom
            if x < Nw:
                perm[idx] = _flip_bit(idx, flag)
        return _apply_permutation(psi, perm)

    def _apply_cqmul_frac_sub(
        self,
        psi: np.ndarray,
        n: int,
        k: int,
        Nconst: int,
        x_reg: Tuple[int, int],
        w_reg: Tuple[int, int],
    ) -> np.ndarray:
        """
        Algorithm-1 step 5:
            subtract from w_reg the m-bit fraction ((k * x mod N)/N)
        """
        m = _reg_len(w_reg)
        mod = 1 << m
        perm = np.arange(1 << n, dtype=np.int64)
        for idx in range(1 << n):
            x = _get_reg_value(idx, x_reg)
            t = (k * x) % Nconst
            delta = (t * mod) // Nconst
            w = _get_reg_value(idx, w_reg)
            w2 = (w - delta) % mod
            perm[idx] = _set_reg_value(idx, w_reg, w2)
        return _apply_permutation(psi, perm)
    
    def _apply_cqmul_frac_add(
        self,
        psi: np.ndarray,
        n: int,
        k: int,
        Nconst: int,
        x_reg: Tuple[int, int],
        w_reg: Tuple[int, int],
    ) -> np.ndarray:
        """
        Inverse of _apply_cqmul_frac_sub:
        w <- (w + floor(((k*x mod N) * 2^m)/N)) mod 2^m
        """
        m = _reg_len(w_reg)
        mod = 1 << m
        perm = np.arange(1 << n, dtype=np.int64)
        for idx in range(1 << n):
            x = _get_reg_value(idx, x_reg)
            t = (k * x) % Nconst
            delta = (t * mod) // Nconst
            w = _get_reg_value(idx, w_reg)
            w2 = (w + delta) % mod
            perm[idx] = _set_reg_value(idx, w_reg, w2)
        return _apply_permutation(psi, perm)



# ============================================================
# Convenience: evaluate a gate on a basis ket
# ============================================================

def eval_on_basis(nqubits: int, U: "Gate", basis_index: int) -> NumpyState:
    ev = NumpyGateEvaluator()
    st = NumpyState.basis(nqubits, basis_index)
    return ev.apply_gate(st, U)


def close(a: np.ndarray, b: np.ndarray, atol: float = 1e-9) -> bool:
    return np.max(np.abs(a - b)) <= atol


def pretty_state(amp: np.ndarray, n: int, k: int = 10) -> str:
    """Show up to k largest amplitudes."""
    idxs = np.argsort(-np.abs(amp))[:k]
    lines = []
    for i in idxs:
        if abs(amp[i]) < 1e-12:
            continue
        bits = format(i, f"0{n}b")[::-1]  # show little-endian order (q0 on left)
        lines.append(f"{bits} : {amp[i]}")
    return "\n".join(lines) if lines else "(all ~0)"


def apply_gate_to_basis(ev: NumpyGateEvaluator, n: int, U, basis_idx: int) -> np.ndarray:
    st = NumpyState.basis(n, basis_idx)
    out = ev.apply_gate(st, U)
    return out.amp


def test_hadamard_single():
    ev = NumpyGateEvaluator()
    n = 1
    U = H(0)

    out0 = apply_gate_to_basis(ev, n, U, 0)
    out1 = apply_gate_to_basis(ev, n, U, 1)

    target0 = np.array([1, 1], dtype=np.complex128) / math.sqrt(2)
    target1 = np.array([1, -1], dtype=np.complex128) / math.sqrt(2)

    assert close(out0, target0), f"H|0> failed:\n{out0}\n!=\n{target0}"
    assert close(out1, target1), f"H|1> failed:\n{out1}\n!=\n{target1}"
    print("[OK] H on 1 qubit")


def test_cnot():
    ev = NumpyGateEvaluator()
    n = 2
    U = CNOT(0, 1) 
    for q0 in [0, 1]:
        for q1 in [0, 1]:
            idx = q0 + 2 * q1
            out = apply_gate_to_basis(ev, n, U, idx)
            # CNOT flips q1 iff q0=1
            q1p = q1 ^ q0
            idxp = q0 + 2 * q1p
            target = np.zeros((1 << n,), dtype=np.complex128)
            target[idxp] = 1.0
            assert close(out, target), f"CNOT failed on |q0={q0},q1={q1}>"
    print("[OK] CNOT on 2 qubits")


def test_swap():
    ev = NumpyGateEvaluator()
    n = 2
    U = SWAP(0, 1)
    out = apply_gate_to_basis(ev, n, U, 1)
    target = np.zeros((1 << n,), dtype=np.complex128)
    target[2] = 1.0
    assert close(out, target)
    print("[OK] SWAP on 2 qubits")


def test_qft_iqft_roundtrip():
    ev = NumpyGateEvaluator()
    n = 3
    reg = (0, 3)
    U = IQFT(list(range(*reg))) @ QFT(list(range(*reg)))
    for idx in range(1 << n):
        out = apply_gate_to_basis(ev, n, U, idx)
        target = np.zeros((1 << n,), dtype=np.complex128)
        target[idx] = 1.0
        assert close(out, target, atol=1e-8), f"QFT/IQFT failed at idx={idx}"
    print("[OK] QFT then IQFT is identity (3 qubits)")


def test_phaseproduct_diagonal():
    ev = NumpyGateEvaluator()
    n = 2
    U = PhaseProduct(phi=math.pi, x_reg=(0, 1), z_reg=(1, 2))

    for q0 in [0, 1]:
        for q1 in [0, 1]:
            idx = q0 + 2 * q1
            out = apply_gate_to_basis(ev, n, U, idx)
            phase = np.exp(1j * math.pi * (q0 * q1))
            target = np.zeros((1 << n,), dtype=np.complex128)
            target[idx] = phase
            assert close(out, target), f"PhaseProduct failed on ({q0},{q1})"
    print("[OK] PhaseProduct diagonal phases")


def test_controlled_phaseproduct():
    ev = NumpyGateEvaluator()
    n = 3
    U = CPhaseProduct(control=2, phi=math.pi, x_reg=(0, 1), z_reg=(1, 2))

    for q0 in [0, 1]:
        for q1 in [0, 1]:
            for q2 in [0, 1]:
                idx = q0 + 2 * q1 + 4 * q2
                out = apply_gate_to_basis(ev, n, U, idx)
                phase = 1.0
                if q2 == 1:
                    phase = np.exp(1j * math.pi * (q0 * q1))
                target = np.zeros((1 << n,), dtype=np.complex128)
                target[idx] = phase
                assert close(out, target), f"CPhaseProduct failed on ({q0},{q1},{q2})"
    print("[OK] CPhaseProduct controlled diagonal phases")


def test_shifted_h():
    ev = NumpyGateEvaluator()
    n = 3
    U = Shifted(offset=1, U=H(0))
    out = apply_gate_to_basis(ev, n, U, 0)
    target = np.zeros((1 << n,), dtype=np.complex128)
    target[0] = 1 / math.sqrt(2)
    target[2] = 1 / math.sqrt(2)
    assert close(out, target)
    print("[OK] Shifted wrapper works (H shifted)")


def main_test():
    test_hadamard_single()
    test_cnot()
    test_swap()
    test_qft_iqft_roundtrip()
    test_phaseproduct_diagonal()
    test_controlled_phaseproduct()
    test_shifted_h()

def marginal_prob_over_reg(amp: np.ndarray, nqubits: int, reg: Tuple[int, int]) -> np.ndarray:
    """
    Return P[v] = sum_{all basis states with reg=value v} 
    """
    L = reg[1] - reg[0]
    probs = np.zeros((1 << L,), dtype=np.float64)
    for idx in range(1 << nqubits):
        v = _get_reg_value(idx, reg)
        probs[v] += float(np.abs(amp[idx]) ** 2)
    return probs

def test_shifted_modmul(
    c: int,
    N: int,
    eta: float,
    base_offset: int,
    trials: int = 5,
    max_small_shift: int = 3,
):
    n = nbits_for_modulus(N)
    m = choose_m(n, eta)

    base_offset = int(base_offset)
    if base_offset < 0 or base_offset > max_small_shift:
        raise ValueError(f"base_offset must be in [0, {max_small_shift}] (got {base_offset})")

    shifted_x_reg = (base_offset, base_offset + n)
    shifted_flag = base_offset + n + m + 1
    total_qubits_needed = shifted_flag + 1

    U_original = mod_mul_InPlace(c=c, N=N, eta=eta)
    U_shifted = Shifted(offset=base_offset, U=U_original)

    ev = NumpyGateEvaluator()
    min_peak = 0.7#max(0.0, 1.0 - 4.0 * eta)

    print(f"\n--- Testing Shifted ModMul (Small Shift Offset: {base_offset}, n={n}, m={m}) ---")

    for x in range(min(N, trials)):
        expected = (c * x) % N

        basis_idx = x << base_offset
        st0 = NumpyState.basis(total_qubits_needed, basis_idx)

        out = ev.apply_gate(st0, U_shifted)

        probs_y = marginal_prob_over_reg(out.amp, total_qubits_needed, shifted_x_reg)

        y_hat = int(np.argmax(probs_y))
        p_hat = float(probs_y[y_hat])

        ok = (y_hat == expected) and (p_hat >= min_peak)
        status = "OK" if ok else "FAIL"

        print(f"  x={x} -> expected={expected} | measured={y_hat} (prob={p_hat:.4f}) [{status}]")

        if not ok:
            raise AssertionError(f"Shifted test failed at small offset {base_offset} for x={x}")

    print(f"[PASS] Shifted mod_mul at small offset {base_offset} works perfectly.")



def test_inplace_modmul_marginal_peak(
    c: int,
    N: int,
    eta: float,
    trials: int = 50,
    seed: int = 0,
    min_peak: float | None = None,
):
    """
    Tests that for inputs |x>|0...0>, the OUTPUT VALUE REGISTER marginal distribution
    peaks at y = (c*x mod N).
    """
    if min_peak is None:
        min_peak = 0.8 #max(0.0, 1.0 - 4.0 * eta)

    n = nbits_for_modulus(N)
    m = choose_m(n, eta)

    x_reg: Tuple[int, int] = (0, n)
    flag = n + m + 1
    nqubits = flag + 1

    U = mod_mul_InPlace(c=c, N=N, eta=eta)
    ev = NumpyGateEvaluator()
    rng = np.random.default_rng(seed)

    max_x = min(N, 1 << n)
    xs = list(range(max_x)) if max_x <= trials else rng.integers(0, max_x, size=trials).tolist()

    def idx_from_x(x: int) -> int:
        idx = 0
        for i in range(n):
            if (x >> i) & 1:
                idx |= (1 << (x_reg[0] + i))
        return idx

    failures = 0

    for x in xs:
        expected = (c * x) % N
        st0 = NumpyState.basis(nqubits, idx_from_x(x))
        out = ev.apply_gate(st0, U)

        probs_y = marginal_prob_over_reg(out.amp, nqubits, x_reg)

        y_hat = int(np.argmax(probs_y))
        p_hat = float(probs_y[y_hat])
        p_exp = float(probs_y[expected])

        ok = (y_hat == expected) and (p_hat >= min_peak)

        topk = np.argsort(-probs_y)[:min(6, len(probs_y))]
        top_str = ", ".join([f"{int(y)}:{probs_y[int(y)]:.4f}" for y in topk])
        print(
            f"x={x:>2} expected={expected:>2} "
            f"argmax={y_hat:>2} p_argmax={p_hat:.6f} p_expected={p_exp:.6f} "
            f"(min_peak={min_peak:.6f})  {'OK' if ok else 'FAIL'}"
        )
        print("  top y:", top_str)

        if not ok:
            failures += 1

    if failures:
        raise AssertionError(
            f"mod_mul_InPlace marginal-peak test FAILED: {failures}/{len(xs)} cases "
            f"(c={c}, N={N}, eta={eta}, min_peak={min_peak})"
        )
    print(f"[PASS] mod_mul_InPlace marginal-peak test passed on {len(xs)} cases.")






def test_inplace_modmul_at_marginal_peak(
    c: int,
    N: int,
    eta: float,
    base: int,
    trials: int = 50,
    seed: int = 0,
    min_peak: float | None = None,
):
    """
    Same idea as test_inplace_modmul_marginal_peak, but for mod_mul_InPlace_at(..., base).

    Prepares |x> in the VALUE register x_reg=(base, base+n), with all other qubits 0.
    Applies U = mod_mul_InPlace_at(c,N,eta,base).
    Checks that the marginal over x_reg peaks at (c*x mod N) with probability >= min_peak.
    """
    if min_peak is None:
        min_peak = 0.8  # tune as you like

    n = nbits_for_modulus(N)
    m = choose_m(n, eta)

    x_reg: Tuple[int, int] = (base, base + n)
    flag = base + n + m + 1
    nqubits = flag + 1

    U = mod_mul_InPlace_at(c=c, N=N, eta=eta, base=base)
    ev = NumpyGateEvaluator()
    rng = np.random.default_rng(seed)

    max_x = min(N, 1 << n)
    xs = list(range(max_x)) if max_x <= trials else rng.integers(0, max_x, size=trials).tolist()

    def idx_from_x(x: int) -> int:
        idx = 0
        for i in range(n):
            if (x >> i) & 1:
                idx |= (1 << (x_reg[0] + i))
        return idx

    failures = 0

    print(f"\n--- Testing mod_mul_InPlace_at (base={base}, n={n}, m={m}) ---")
    for x in xs:
        expected = (c * x) % N

        st0 = NumpyState.basis(nqubits, idx_from_x(x))
        out = ev.apply_gate(st0, U)

        probs_y = marginal_prob_over_reg(out.amp, nqubits, x_reg)

        y_hat = int(np.argmax(probs_y))
        p_hat = float(probs_y[y_hat])
        p_exp = float(probs_y[expected])

        ok = (y_hat == expected) and (p_hat >= min_peak)

        topk = np.argsort(-probs_y)[:min(6, len(probs_y))]
        top_str = ", ".join([f"{int(y)}:{probs_y[int(y)]:.4f}" for y in topk])
        print(
            f"x={x:>2} expected={expected:>2} "
            f"argmax={y_hat:>2} p_argmax={p_hat:.6f} p_expected={p_exp:.6f} "
            f"(min_peak={min_peak:.6f})  {'OK' if ok else 'FAIL'}"
        )
        print("  top y:", top_str)

        if not ok:
            failures += 1

    if failures:
        raise AssertionError(
            f"mod_mul_InPlace_at marginal-peak test FAILED: {failures}/{len(xs)} cases "
            f"(c={c}, N={N}, eta={eta}, base={base}, min_peak={min_peak})"
        )
    print(f"[PASS] mod_mul_InPlace_at marginal-peak test passed on {len(xs)} cases.")



def run_range_suite():
    test_shifted_modmul(c=2, N=5, eta=0.1, base_offset=0)
    test_shifted_modmul(c=3, N=7, eta=0.1, base_offset=2)

def test_modexp_control_trick_random_x(
    a: int,
    N: int,
    eta: float,
    base: int,
    y0: int = 1,
    trials: int = 50,
    seed: int = 0,
    max_x: int | None = None,
    min_x: int = 0,
    min_peak: float = 0.2,
):
    """
    Randomized test for modexp_control_trick over many *higher* x values.

    Note:
      This builds one U per x
    """
    n = nbits_for_modulus(N)
    m = choose_m(n, eta)

    y_reg: Tuple[int, int] = (base, base + n)

    flag = base + n + m + 1
    nqubits = flag + 1

    rng = np.random.default_rng(seed)

    if max_x is None:
        min_x = max(min_x, 1 << 10)
        max_x = 1 << 11

    if not (0 <= min_x < max_x):
        raise ValueError(f"Need 0 <= min_x < max_x (got min_x={min_x}, max_x={max_x})")

    xs = rng.integers(min_x, max_x, size=trials).tolist()

    def idx_from_y(y: int) -> int:
        idx = 0
        for i in range(n):
            if (y >> i) & 1:
                idx |= (1 << (y_reg[0] + i))
        return idx

    ev = NumpyGateEvaluator()
    failures = 0

    print(f"\n--- Random test: modexp_control_trick (trials={trials}, x in [{min_x},{max_x})) ---")
    print(f"a={a}, N={N}, eta={eta}, base={base}, y0={y0}, n={n}, m={m}, nqubits={nqubits}, min_peak={min_peak}")

    for j, x in enumerate(xs):
        x = int(x)
        expected = (y0 * pow(a, x, N)) % N

        U = modexp_control_trick(a=a, N=N, eta=eta, x_val=x, y_reg=y_reg)

        st0 = NumpyState.basis(nqubits, idx_from_y(y0))
        out = ev.apply_gate(st0, U)

        probs_y = marginal_prob_over_reg(out.amp, nqubits, y_reg)
        y_hat = int(np.argmax(probs_y))
        p_hat = float(probs_y[y_hat])
        p_exp = float(probs_y[expected])

        ok = (y_hat == expected) and (p_hat >= min_peak)

        topk = np.argsort(-probs_y)[:min(6, len(probs_y))]
        top_str = ", ".join([f"{int(y)}:{probs_y[int(y)]:.4f}" for y in topk])

        print(
            f"[{j:02d}] x={x:>6} expected={expected:>2} "
            f"argmax={y_hat:>2} p_argmax={p_hat:.6f} p_expected={p_exp:.6f} "
            f"{'OK' if ok else 'FAIL'}"
        )
        print("     top y:", top_str)

        if not ok:
            failures += 1

    if failures:
        raise AssertionError(
            f"modexp_control_trick RANDOM HIGH-X TEST FAILED: {failures}/{trials} cases "
            f"(a={a}, N={N}, eta={eta}, base={base}, y0={y0}, x_range=[{min_x},{max_x}), min_peak={min_peak})"
        )
    
    print(f"[PASS] modexp_control_trick high-x random test passed on {trials} cases.")


if __name__ == "__main__":
    main_test()
    test_modexp_control_trick_random_x(
        a=3, N=10, eta=0.3,
        base=0, y0=1,
        trials=25, seed=0,
        min_x=8, max_x=64,
        min_peak=0.5
    )

    test_modexp_control_trick_random_x(
        a=2, N=7, eta=0.15,
        base=0, y0=1,
        trials=25, seed=0,
        min_x=8, max_x=64,
        min_peak=0.5
    )
