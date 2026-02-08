import numpy as np
from dataclasses import dataclass
from typing import Tuple, Optional, Callable
import math

# ----------------------------
# Basic quantum "formalization"
# ----------------------------

def ket(dim: int, i: int) -> np.ndarray:
    """|i> in C^dim."""
    v = np.zeros((dim,), dtype=complex)
    v[i % dim] = 1.0
    return v

def kron(*ops: np.ndarray) -> np.ndarray:
    """Kronecker product of many matrices/vectors."""
    out = ops[0]
    for op in ops[1:]:
        out = np.kron(out, op)
    return out

def qft_qubits(n: int) -> np.ndarray:
    """
    QFT on n qubits, i.e. dimension M = 2^n:
      QFT |y> = (1/sqrt(M)) sum_{z=0}^{M-1} exp(2π i y z / M) |z>
    """
    if n < 0:
        raise ValueError("n must be >= 0")
    M = 1 << n  # 2^n
    omega = np.exp(2j * np.pi / M)
    y = np.arange(M).reshape(M, 1) #<y| 
    z = np.arange(M).reshape(1, M)
    F = omega ** (y * z) / np.sqrt(M)
    return F

def apply_unitary(U: np.ndarray, state: np.ndarray) -> np.ndarray:
    return U @ state


def basis_index(dims: Tuple[int, ...], values: Tuple[int, ...]) -> int:
    """Flatten tuple 'values' into computational basis index for tensor dims."""
    idx = 0
    stride = 1
    for d, v in zip(reversed(dims), reversed(values)):
        idx += (v % d) * stride
        stride *= d
    return idx


def unflatten_index(dims: Tuple[int, ...], idx: int) -> Tuple[int, ...]:
    """Inverse of basis_index."""
    vals = []
    for d in reversed(dims):
        vals.append(idx % d)
        idx //= d
    return tuple(reversed(vals))

# -------------------------------------
# PhaseProduct as a black-box "primitive"
# -------------------------------------

def phase_product_unitary(Nx: int, Nz: int, phi: float) -> np.ndarray:
    """
    |x>|z> -> exp(i * phi * x * z) |x>|z>
    Returns a (Nx*Nz) x (Nx*Nz) diagonal unitary.
    """
    x_vals = np.arange(Nx)
    z_vals = np.arange(Nz)
    interaction = np.outer(x_vals, z_vals)          # (Nx, Nz) with entries x*z
    phases = np.exp(1j * phi * interaction).reshape(-1)  # flatten in x-major order
    return np.diag(phases)


def basis_state(dims: Tuple[int, ...], values: Tuple[int, ...]) -> np.ndarray:
    """Computational basis state |values> in C^{prod(dims)}."""
    assert len(dims) == len(values)
    vec = ket(dims[0], values[0])
    for d, v in zip(dims[1:], values[1:]):
        vec = np.kron(vec, ket(d, v))
    return vec


def most_likely_basis_state(state: np.ndarray, dims: Tuple[int, ...]) -> Tuple[Tuple[int, ...], float]:
    probs = np.abs(state) ** 2
    idx = int(np.argmax(probs))
    return unflatten_index(dims, idx), float(probs[idx])

def phase_product_modN_unitary(Nx: int, Nz: int, a: int, N: int) -> np.ndarray:
    phi = 2 * np.pi * (a % N) / N
    return phase_product_unitary(Nx, Nz, phi)




def ucxq_unitary_via_phaseproduct_and_qft(*, nx_qubits: int, mw_qubits: int, a: int) -> np.ndarray:
    """
    Build U_{c×q}(a) acting on |x>|w> with:
      x in Z_{2^{nx_qubits}}
      w in Z_{2^{mw_qubits}}  (this is the modulus for the add)

    Implements:
      (I ⊗ QFT^{-1}) · PhaseProduct_modN(a, N=2^{mw_qubits}) · (I ⊗ QFT)

    Result:
      |x>|w> -> |x>|w + a*x mod 2^{mw_qubits}>
    """
    Nx = 1 << nx_qubits
    Nw = 1 << mw_qubits

    Ft = qft_qubits(mw_qubits)

    Ft_dag = Ft.conj().T

    # Identity on x-register
    Ix = np.eye(Nx, dtype=complex)

    # PhaseProduct diagonal in |x>|z>:
    #   |x>|z> -> exp(2π i * a * x * z / Nw) |x>|z>
    PP = phase_product_modN_unitary(Nx=Nx, Nz=Nw, a=a % Nw, N=Nw)  # shape (Nx*Nw, Nx*Nw)

    # Lift QFT to the joint space
    I_kron_F  = kron(Ix, Ft)
    I_kron_Fd = kron(Ix, Ft_dag)

    # Compose
    U = I_kron_Fd @ PP @ I_kron_F
    return U





# ----------------------------------------------------------------------
# Generic helper: build a permutation unitary from an update rule on basis
# ----------------------------------------------------------------------

def permutation_unitary(dims: Tuple[int, ...], update: Callable[[Tuple[int, ...]], Tuple[int, ...]]) -> np.ndarray:
    """
    Build a unitary U that permutes computational basis states:
      U |v> = |update(v)>
    where v is a tuple of register values (one per dimension in dims).

    Assumes update is a bijection on the full basis set.
    """
    D = int(np.prod(dims))
    U = np.zeros((D, D), dtype=complex)
    for in_idx in range(D):
        v = unflatten_index(dims, in_idx)
        v2 = update(v)
        out_idx = basis_index(dims, v2)
        U[out_idx, in_idx] = 1.0
    return U

# ----------------------------------------------------------------------
# Fixed-point helpers (match the intent of Algorithm 1)
# ----------------------------------------------------------------------

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

def fixed_point_w_int(t: int, N: int, m: int) -> int:
    """
    Given t = ((c-1)x mod N) in [0, N-1],
    return w_int ≈ 2^m * (t / N).

    We use floor; you can switch to rounding if you want.
    """
    M = 1 << m
    return (t * M) // N

def N_times_w_from_int(w_int: int, N: int, m: int) -> int:
    """
    Given w_int representing w ≈ w_int / 2^m,
    return integer approx to N*w: floor(N * w_int / 2^m).
    """
    M = 1 << m
    return (N * w_int) // M

# -------------------------------------
# Algorithm 1 for In-place Modular Multiplication
# -------------------------------------
def hadamard_1q() -> np.ndarray:
    """Single-qubit Hadamard."""
    return (1.0 / np.sqrt(2.0)) * np.array([[1, 1], [1, -1]], dtype=complex)

def hadamard_n(n: int) -> np.ndarray:
    """n-qubit Hadamard = H^{⊗ n}, dimension 2^n."""
    if n < 0:
        raise ValueError("n must be >= 0")
    if n == 0:
        return np.array([[1.0]], dtype=complex)
    H = hadamard_1q()
    out = H
    for _ in range(n - 1):
        out = np.kron(out, H)
    return out

def step1_compute_w_unitary_hadamard(
    *, N: int, c: int, n: int, m: int, use_x_mod_N: bool = True
) -> np.ndarray:
    """
      1) Apply Hadamards to W to create |x> ⊗ sum_z |z>
      2) Apply phase rotation exp(2π i * w(x) * z) where
           w(x) = ((c-1) * x mod N) / N 
      3) Apply inverse QFT on W modulo 2^m

    """
    Xdim = 1 << (n + 1)
    Wdim = 1 << m
    Bdim = 2

    Hm = hadamard_n(m)          # dim Wdim
    Fw = qft_qubits(m)          # dim Wdim
    Fw_dag = Fw.conj().T

    Ix = np.eye(Xdim, dtype=complex)
    Ib = np.eye(Bdim, dtype=complex)

    a = (c - 1) % N
    PP = phase_product_modN_unitary(Nx=Xdim, Nz=Wdim, a=a, N=N)

    # Lift to (X,W,B) space:
    I_kron_F  = kron(Ix, Hm, Ib)
    I_kron_Fd = kron(Ix, Fw_dag, Ib)
    PP_lift   = kron(PP, Ib)
    
    U = I_kron_Fd @ PP_lift @ I_kron_F
    return U

    # Fw_dag = Fw.conj().T

    # Ix = np.eye(Xdim, dtype=complex)
    # Ib = np.eye(Bdim, dtype=complex)

    # # Build diagonal phase on (X,W): |x>|z> -> exp(2π i * w(x) * z) |x>|z>
    # phases = np.zeros((Xdim * Wdim,), dtype=complex)
    # a = (c - 1) % N
    # for x in range(Xdim):
    #     x_eff = (x % N) if use_x_mod_N else x
    #     t = (a * x_eff) % N                    # t in [0, N-1]
    #     w = t / float(N)                       # real fraction in [0,1)
    #     for z in range(Wdim):
    #         idx = x * Wdim + z             
    #         phases[idx] = np.exp(2j * np.pi * w * z)
    # PP = np.diag(phases)                       # acts on (X,W)

    # # Lift to (X,W,B)
    # U_H   = kron(Ix, Hm, Ib)
    # U_iQ  = kron(Ix, Fw_dag, Ib)
    # PP_l  = kron(PP, Ib)

    # return U_iQ @ PP_l @ U_H


def step1_compute_w_unitary(*, N: int, c: int, n: int, m: int) -> np.ndarray:
    """
    Step 1 using Eq. (15) + QFT modulo 2^m.

    Registers: (X, W, B)
      X dimension = 2^(n+1)  (top ancilla included)
      W dimension = 2^m      (the 'fraction' register)
      B dimension = 2

    Action (on X,W only; B untouched):
      |x>|0>  -> approximately |x>| ( (c-1)*x mod N ) / N >  as an m-bit binary fraction
    implemented as:
      (I ⊗ QFT^{-1}_{2^m}) · PhaseProduct_modN(a=c-1, N) · (I ⊗ QFT_{2^m})
    where PhaseProduct_modN applies exp(2π i * a * x * z / N) in the |x>|z> basis.
    """

    Xdim = 1 << (n + 1)
    Wdim = 1 << m
    Bdim = 2

    # QFT on W (dimension 2^m)
    Fw = qft_qubits(m)
    Fw_dag = Fw.conj().T

    Ix = np.eye(Xdim, dtype=complex)
    Ib = np.eye(Bdim, dtype=complex)

    # exp(2π i a x z / N) on |x>|z>, with z in [0, 2^m-1]
    a = (c - 1) % N
    PP = phase_product_modN_unitary(Nx=Xdim, Nz=Wdim, a=a, N=N)

    # Lift to (X,W,B) space:
    I_kron_F  = kron(Ix, Fw, Ib)
    I_kron_Fd = kron(Ix, Fw_dag, Ib)
    PP_lift   = kron(PP, Ib)   # PP acts on (X,W); tensor with identity on B

    U = I_kron_Fd @ PP_lift @ I_kron_F
    return U


# ----------------------------------------------------------------------
# Step 2: compute |x>|w> -> |x + N*w>|w>
# In fixed-point: use N_times_w_from_int(w_int)
# ----------------------------------------------------------------------

def step2_add_Nw_into_x_unitary(*, N: int, n: int, m: int) -> np.ndarray:
    """
    Step 2:
      QFT on X,
      apply PhaseProduct,
      inverse QFT on X.

    This implements (approximately):
      |x⟩|w_int⟩  ->  |x + floor(N * w_int / 2^m)⟩|w_int⟩
      

    """
    Xdim = 1 << (n + 1)
    Wdim = 1 << m
    Bdim = 2

    Fx = qft_qubits(n + 1)
    Fx_dag = Fx.conj().T

    Iw = np.eye(Wdim, dtype=complex)
    Ib = np.eye(Bdim, dtype=complex)

    phi = 2.0 * np.pi * (N / float(1 << (m + n + 1)))

    PP = phase_product_unitary(Nx=Xdim, Nz=Wdim, phi=phi)
    PP_lift = kron(PP, Ib)

    return kron(Fx_dag, Iw, Ib) @ PP_lift @ kron(Fx, Iw, Ib)

# ----------------------------------------------------------------------
# Step 3: Using an ancilla qubit, compute (x >= N) into b and subtract N if b=1
# ----------------------------------------------------------------------

def step3_flag_and_cond_subN_unitary(*, N: int, n: int, m: int) -> np.ndarray:
    """
    Reversible Step 3 (unitary on the full space):

      flag := [x >= N]
      b2   := b XOR flag
      if b2 == 1 then x := x - N   (mod 2^(n+1))

    This is a permutation of basis states (hence unitary).
    """
    Xdim = 1 << (n + 1)
    Wdim = 1 << m
    Bdim = 2
    dims = (Xdim, Wdim, Bdim)

    def upd(v):
        x, w, b = v
        flag = 1 if x >= N else 0
        b2 = b ^ flag
        x2 = (x - N) % Xdim if b2 == 1 else x
        return (x2, w, b2)

    return permutation_unitary(dims, upd)
# ----------------------------------------------------------------------
# Step 4: Uncompute the ancilla qubit by recomputing a comparison
# Paper: uncompute by checking (cx mod N < Nw) (a comparison operator)
#
#   after Step 3, x is (approximately) cx mod N in [0,N).
#   we can compute Nw_int = floor(N * w_int / 2^m)  (same as Step 2 add)
#   then use condition: [x < Nw_int] to toggle b back.
# ----------------------------------------------------------------------

def step4_uncompute_flag_unitary(*, N: int, n: int, m: int) -> np.ndarray:
    """
    Registers: (X, W, B)
    Action:
      b := b XOR [x < floor(N*w/2^m)]
    """
    Xdim = 1 << (n + 1)
    Wdim = 1 << m
    Bdim = 2
    dims = (Xdim, Wdim, Bdim)

    def upd(v):
        x, w_int, b = v
        Nw_int = N_times_w_from_int(w_int, N, m)
        flag = 1 if x < Nw_int else 0
        return (x, w_int, b ^ flag)

    return permutation_unitary(dims, upd)



def inv_mod(c: int, N: int) -> int:
    """Multiplicative inverse of c mod N (requires gcd(c,N)=1)."""
    return pow(c, -1, N) 

def step5_uncompute_w_unitary(*, N: int, c: int, n: int, m: int) -> np.ndarray:
    """
    Step 5: Uncompute W 

    After Step 3, X holds y = c*x mod N (in the valid subspace).
    We need to subtract the fraction corresponding to:
      a = (1 - c^{-1}) mod N

    """
    Xdim = 1 << (n + 1)
    Wdim = 1 << m
    Bdim = 2

    Hm = hadamard_n(m)  
    Ft = qft_qubits(m)
    Ft_dag = Ft.conj().T

    Ix = np.eye(Xdim, dtype=complex)
    Ib = np.eye(Bdim, dtype=complex)

    c_inv = inv_mod(c % N, N)
    a = (1 - c_inv) % N

    PP = phase_product_modN_unitary(Nx=Xdim, Nz=Wdim, a=a, N=N)

    I_kron_F  = kron(Ix, Hm, Ib)
    I_kron_Fd = kron(Ix, Ft_dag, Ib)
    PP_lift   = kron(PP, Ib)

    U_frac = I_kron_Fd @ PP_lift @ I_kron_F

    return U_frac.conj().T




def algorithm1_unitary(*, N: int, c: int, eta: float) -> Tuple[np.ndarray, Tuple[int, int, int]]:
    if math.gcd(c, N) != 1:
        raise ValueError("Algorithm 1 requires c invertible mod N, i.e. gcd(c,N)=1")

    n = nbits_for_modulus(N)
    m = choose_m(n, eta)

    U1 = step1_compute_w_unitary_hadamard(N=N, c=c, n=n, m=m)
    U2 = step2_add_Nw_into_x_unitary(N=N, n=n, m=m)
    U3 = step3_flag_and_cond_subN_unitary(N=N, n=n, m=m)
    U4 = step4_uncompute_flag_unitary(N=N, n=n, m=m)
    U5 = step5_uncompute_w_unitary(N=N, c=c, n=n, m=m)

    U = U5 @ U4 @ U3 @ U2 @ U1
    dims = ((1 << (n + 1)), (1 << m), 2)
    return U, dims


# --------------------------
# Quick correctness checks
# --------------------------

# def check_ucxq_on_basis(*, nx_qubits: int, mw_qubits: int, a: int, trials: int = 10, seed: int = 0) -> None:
#     Nx = 1 << nx_qubits
#     Nw = 1 << mw_qubits
#     dims = (Nx, Nw)

#     U = ucxq_unitary_via_phaseproduct_and_qft(nx_qubits=nx_qubits, mw_qubits=mw_qubits, a=a)

#     rng = np.random.default_rng(seed)
#     for _ in range(trials):
#         x = int(rng.integers(0, Nx))
#         w = int(rng.integers(0, Nw))

#         # |x>|w>
#         psi = kron(ket(Nx, x), ket(Nw, w))
#         out = apply_unitary(U, psi)

#         # Expected: |x>|(w + a*x) mod Nw>
#         w2 = (w + (a * x)) % Nw
#         exp_state = kron(ket(Nx, x), ket(Nw, w2))

#         # Compare up to global phase (here should actually match exactly for basis inputs)
#         err = np.linalg.norm(out - exp_state)
#         if err > 1e-9:
#             print(f"FAIL for x={x}, w={w}: expected w'={w2}, ||out-exp||={err}")
#             # print the dominant basis state to diagnose
#             print("Most likely:", most_likely_basis_state(out, dims))
#             return

#     print(f"PASS: {trials} random basis tests for nx={nx_qubits}, mw={mw_qubits}, a={a}")



def _fmt_complex(a: complex, digits: int = 4) -> str:
    """Format a complex amplitude in a compact, handwritten-ish way."""
    re = float(np.real(a))
    im = float(np.imag(a))

    # snap tiny parts to 0
    eps = 10 ** (-(digits + 2))
    if abs(re) < eps: re = 0.0
    if abs(im) < eps: im = 0.0

    # purely real / purely imag / general
    if im == 0.0:
        return f"{re:.{digits}f}"
    if re == 0.0:
        # show i, -i nicely when close
        if abs(im - 1.0) < 10**(-digits): return "i"
        if abs(im + 1.0) < 10**(-digits): return "-i"
        return f"{im:.{digits}f}i"
    sign = "+" if im >= 0 else "-"
    return f"{re:.{digits}f}{sign}{abs(im):.{digits}f}i"

def _ket_bits(i: int, nbits: int) -> str:
    return format(i, f"0{nbits}b")

def pretty_state(
    state: np.ndarray,
    *,
    nbits: int,
    cutoff: float = 1e-9,
    digits: int = 4,
    max_terms: Optional[int] = None,
    sort: bool = True,
) -> str:
    """
    Print a state vector of length 2^nbits as:
      (amp)|bitstring> + ...
    """
    state = state.flatten()
    if state.size != (1 << nbits):
        raise ValueError(f"Expected length {1<<nbits}, got {state.size}")

    terms = []
    for idx, amp in enumerate(state):
        p = float(np.abs(amp) ** 2)
        if p >= cutoff:
            terms.append((p, idx, amp))

    if sort:
        terms.sort(reverse=True, key=lambda t: t[0])  # by probability

    if max_terms is not None:
        terms = terms[:max_terms]

    if not terms:
        return "0"

    pieces = []
    for _, idx, amp in terms:
        a_str = _fmt_complex(amp, digits)
        ket = _ket_bits(idx, nbits)
        pieces.append(f"({a_str})|{ket}⟩")

    return " + ".join(pieces)

def pretty_state_tensor(
    state: np.ndarray,
    dims: Tuple[int, ...],
    *,
    cutoff: float = 1e-9,
    digits: int = 4,
    max_terms: Optional[int] = None,
    sort: bool = True,
    ket_style: str = "tuple",  # "tuple" or "bits"
    sep: str = ",",
) -> str:
    """
    Print a state over a tensor product with given dims (like your code uses).

    ket_style:
      - "tuple": |x,w,b⟩ using unflatten_index(dims, idx)
      - "bits" : each register printed in binary with enough bits for its dim (if power-of-2), else decimal
    """
    state = state.flatten()
    D = int(np.prod(dims))
    if state.size != D:
        raise ValueError(f"Expected length {D}, got {state.size}")

    def reg_to_str(v: int, d: int) -> str:
        # if d is power of 2, print binary with log2(d) bits; else decimal
        if d > 0 and (d & (d - 1) == 0):
            bits = (d - 1).bit_length()
            return format(v, f"0{bits}b")
        return str(v)

    terms = []
    for flat_idx, amp in enumerate(state):
        p = float(np.abs(amp) ** 2)
        if p >= cutoff:
            terms.append((p, flat_idx, amp))

    if sort:
        terms.sort(reverse=True, key=lambda t: t[0])

    if max_terms is not None:
        terms = terms[:max_terms]

    if not terms:
        return "0"

    pieces = []
    for _, flat_idx, amp in terms:
        a_str = _fmt_complex(amp, digits)
        vals = unflatten_index(dims, flat_idx)

        if ket_style == "tuple":
            ket = sep.join(str(v) for v in vals)
        elif ket_style == "bits":
            ket = sep.join(reg_to_str(v, d) for v, d in zip(vals, dims))
        else:
            raise ValueError("ket_style must be 'tuple' or 'bits'")

        pieces.append(f"({a_str})|{ket}⟩")

    return " + ".join(pieces)

def isUnitary(U: np.ndarray, atol: float = 1e-10) -> bool:
    """Return True iff U†U ≈ I (within atol)."""
    if U.ndim != 2 or U.shape[0] != U.shape[1]:
        return False
    I = np.eye(U.shape[0], dtype=complex)
    return np.allclose(U.conj().T @ U, I, atol=atol)


def test_step_unitaries_unitary(*, N: int, c: int, n: int, m: int, atol: float = 1e-10) -> None:
    """Build U1..U5 and print whether each is unitary."""
    U1 = step1_compute_w_unitary_hadamard(N=N, c=c, n=n, m=m)
    U2 = step2_add_Nw_into_x_unitary(N=N, n=n, m=m)
    U3 = step3_flag_and_cond_subN_unitary(N=N, n=n, m=m)
    U4 = step4_uncompute_flag_unitary(N=N, n=n, m=m)
    U5 = step5_uncompute_w_unitary(N=N, c=c, n=n, m=m)

    print(f"U1 unitary? {isUnitary(U1, atol=atol)}   shape={U1.shape}")
    print(f"U2 unitary? {isUnitary(U2, atol=atol)}   shape={U2.shape}")
    print(f"U3 unitary? {isUnitary(U3, atol=atol)}   shape={U3.shape}")
    print(f"U4 unitary? {isUnitary(U4, atol=atol)}   shape={U4.shape}")
    print(f"U5 unitary? {isUnitary(U5, atol=atol)}   shape={U5.shape}")


def demo_print_step1_small():
    N = 5
    c = 3
    eta = 0.25
    x = 4
    b = 0

    n = nbits_for_modulus(N)
    m = choose_m(n, eta)

    print("m = ",m)
    Xdim = 1 << (n + 1)
    Wdim = 1 << m
    Bdim = 2
    dims = (Xdim, Wdim, Bdim)

    U1 = step1_compute_w_unitary_hadamard(N=N, c=c, n=n, m=m)
    U2 = step2_add_Nw_into_x_unitary(N=N, n=n, m=m)
    U3 = step3_flag_and_cond_subN_unitary(N=N, n=n, m=m)
    U4 = step4_uncompute_flag_unitary(N=N, n=n, m=m)
    U5 = step5_uncompute_w_unitary(N=N, c=c, n=n, m=m)

    psi0 = basis_state(dims, (x, 0, b))
    psi1 = apply_unitary(U1, psi0)
    psi2 = apply_unitary(U2, psi1)
    psi3 = apply_unitary(U3, psi2)
    psi4 = apply_unitary(U4, psi3)
    psi5 = apply_unitary(U5, psi4)

    def show(label, psi, cutoff=1e-6):
        print(f"\n{label}:")
        print(pretty_state_tensor(psi, dims, cutoff=cutoff, digits=4, max_terms=30, ket_style="tuple"))
        ml, p = most_likely_basis_state(psi, dims)
        print(f"Most likely basis state {label.lower()}: |{ml[0]},{ml[1]},{ml[2]}⟩ with prob {p:.6f}")

    print("BEFORE:")
    print(pretty_state_tensor(psi0, dims, cutoff=1e-12, digits=4, max_terms=30, ket_style="tuple"))

    show("AFTER STEP 1", psi1)
    show("AFTER STEP 2", psi2)
    show("AFTER STEP 3", psi3)
    show("AFTER STEP 4", psi4)
    show("AFTER STEP 5", psi5)


def check_algorithm1_most_likely(
    *,
    N: int,
    c: int,
    eta: float,
    xs: Optional[list[int]] = None,
    b: int = 0,
    cutoff: float = 1e-12,
    atol_unitary: float = 1e-10,
    U_check: bool = True,
) -> dict:
    """
    Runs Algorithm 1 on basis inputs |x>|0>|b| and checks correctness by
    comparing the MOST LIKELY basis state after Step 5.

    We count a trial as success if the argmax output equals:
      (x_out, w_out, b_out) = ( (c*x) mod N, 0, 0 )

    Returns summary dict.
    """
    if math.gcd(c, N) != 1:
        raise ValueError("Need gcd(c,N)=1")

    n = nbits_for_modulus(N)
    m = choose_m(n, eta)

    Xdim = 1 << (n + 1)
    Wdim = 1 << m
    Bdim = 2
    dims = (Xdim, Wdim, Bdim)

    if xs is None:
        xs = list(range(N))

    U1 = step1_compute_w_unitary(N=N, c=c, n=n, m=m)
    U2 = step2_add_Nw_into_x_unitary(N=N, n=n, m=m)
    U3 = step3_flag_and_cond_subN_unitary(N=N, n=n, m=m)
    U4 = step4_uncompute_flag_unitary(N=N, n=n, m=m)
    U5 = step5_uncompute_w_unitary(N=N, c=c, n=n, m=m)

    if U_check:
        print(f"N={N}, c={c}, eta={eta}, n={n}, m={m}, dims={dims}")
        print(f"U1 unitary? {isUnitary(U1, atol=atol_unitary)}")
        print(f"U2 unitary? {isUnitary(U2, atol=atol_unitary)}")
        print(f"U3 unitary? {isUnitary(U3, atol=atol_unitary)}")
        print(f"U4 unitary? {isUnitary(U4, atol=atol_unitary)}")
        print(f"U5 unitary? {isUnitary(U5, atol=atol_unitary)}")

    successes = 0
    details = []

    for x in xs:
        psi0 = basis_state(dims, (x, 0, b))
        psi = U5 @ (U4 @ (U3 @ (U2 @ (U1 @ psi0))))

        (x_hat, w_hat, b_hat), p_hat = most_likely_basis_state(psi, dims)

        x_expected = (c * x) % N
        w_expected = 0
        b_expected = 0

        ok = (x_hat == x_expected) and (w_hat == w_expected) and (b_hat == b_expected)

        successes += int(ok)
        details.append({
            "x_in": x,
            "most_likely": (x_hat, w_hat, b_hat),
            "prob": p_hat,
            "expected": (x_expected, w_expected, b_expected),
            "ok": ok,
        })

        if U_check:
            status = "OK" if ok else "FAIL"
            print(f"x={x:>3}  ->  ML={(x_hat,w_hat,b_hat)}  p={p_hat:.6f}  expected={(x_expected,0,0)}  {status}")

    return {
        "N": N,
        "c": c,
        "eta": eta,
        "n": n,
        "m": m,
        "dims": dims,
        "tested_xs": xs,
        "successes": successes,
        "total": len(xs),
        "success_rate": successes / max(1, len(xs)),
        "details": details,
    }




if __name__ == "__main__":
    demo_print_step1_small()
    res = check_algorithm1_most_likely(N=5, c=3, eta=0.25, xs=list(range(5)), U_check=True)
    print("success_rate =", res["success_rate"])

    res = check_algorithm1_most_likely( N=3,c=2,eta=0.1,xs=list(range(3)),b=0,U_check=True)
    print("success_rate =", res["success_rate"])
    # N = 5
    # c = 3
    # eta = 0.25
    # x = 4
    # b = 0

    # n = nbits_for_modulus(N)
    # m = choose_m(n, eta)
    # test_step_unitaries_unitary(N=N, c=c, n=n, m=m, atol=1e-10)