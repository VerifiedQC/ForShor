import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# QuantumLib, vendored

Transcribed from **inQWIRE/LeanQuantum**, `main` at commit
`44fc4eb1f4ba512e659deacd3468fda0a764d162` (2026-04-24), files

* `Quantumlib/ForMathlib/Data/Matrix/Basic.lean` — `CMatrix`, `CVector`, `CSquare`
* `Quantumlib/ForMathlib/Data/Matrix/Kron.lean` — `Matrix.kron`, the `⊗` notation
* `Quantumlib/Data/Gate/Basic.lean` — `hadamard`, `cnot`, `swap`
* `Quantumlib/Data/Gate/PhaseShift.lean` — `phaseShift`
* `Quantumlib/Data/Basis/Basic.lean` — `ket0`, `ket1`

MIT licensed; see that repository's `LICENSE`.

## Why vendored rather than `require`d

The natural choice would be to depend on QuantumLib as a package. No commit
of it builds on this repository's toolchain: QuantumLib's `lean-toolchain` history runs

```
v4.20.0-rc5  (977f1f04, 2025-05-11)
v4.26.0-rc2  (6f70dcd1, 2025-12-10)
v4.30.0-rc2  (f2af8ad4, 2026-04-24, current main)
```

and this repository is pinned at `v4.36.0-rc1` with Mathlib at `4dc43842`. A
`require` would therefore mean pinning a mismatched toolchain, which is a
development-wide change and out of scope. Vendoring also keeps the work
additive: no `lakefile.lean` and no `lake-manifest.json` edit.

The consequence is honest and worth stating: the theorems in
`Headline.lean` mention *these* definitions, which are transcriptions. They
are character-for-character the upstream ones (only the `import` lines and
the surrounding namespaces differ), so a later `require` is a mechanical
swap of this file for the real package — but until that swap happens, the
guarantee is "equal to QuantumLib's definitions as transcribed here", not
"shares a kernel object with QuantumLib".

Only the declarations this folder uses are transcribed; the
proofs of the `kron` lemmas are re-done here rather than copied, since the
upstream proofs use `Quantumlib.Tactic`.
-/

universe u

/-- `CMatrix m n` — a complex `m × n` matrix. -/
abbrev CMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ

/-- `CVector n` — a complex column vector of length `n`. -/
abbrev CVector (n : ℕ) := CMatrix n 1

/-- `CSquare n` — a complex `n × n` matrix. -/
abbrev CSquare (n : ℕ) := CMatrix n n

namespace Matrix

/-- The Kronecker product, flattened to `Fin`. The **left** factor is the high
digit: `(A ⊗ B) x y = A x.divNat y.divNat * B x.modNat y.modNat`. -/
def kron {a b c d : ℕ} (m₁ : CMatrix a b) (m₂ : CMatrix c d) : CMatrix (a * c) (b * d) :=
  Matrix.of fun x y => m₁ x.divNat y.divNat * m₂ x.modNat y.modNat

@[inherit_doc] scoped[Kron] infixl:100 " ⊗ " => Matrix.kron

open scoped Kron

@[simp] theorem kron_apply {a b c d : ℕ} (A : CMatrix a b) (B : CMatrix c d) (i j) :
    (A ⊗ B) i j = A i.divNat j.divNat * B i.modNat j.modNat := rfl

theorem kron_def {a b c d : ℕ} (A : CMatrix a b) (B : CMatrix c d) :
    A ⊗ B = Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kroneckerMap (· * ·) A B) :=
  rfl

@[simp] theorem one_kron_one {m n : ℕ} :
    (1 : CSquare m) ⊗ (1 : CSquare n) = (1 : CSquare (m * n)) := by
  ext i j
  rw [kron_apply, Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
  have key : i.divNat = j.divNat → i.modNat = j.modNat → i = j := by
    intro h1 h2
    have e1 : i.1 / n = j.1 / n := by simpa [Fin.divNat] using congrArg Fin.val h1
    have e2 : i.1 % n = j.1 % n := by simpa [Fin.modNat] using congrArg Fin.val h2
    refine Fin.ext ?_
    have hi := Nat.div_add_mod i.1 n
    have hj := Nat.div_add_mod j.1 n
    rw [e1, e2] at hi
    omega
  by_cases h : i = j
  · simp [h]
  · rw [ite_eq_right h]
    by_cases h1 : i.divNat = j.divNat
    · have h2 : ¬ (i.modNat = j.modNat) := fun hc => h (key h1 hc)
      simp [h1, h2]
    · simp [h1]

theorem mul_kron_mul {a b c a' b' c' : ℕ} (A : CMatrix a b) (B : CMatrix b c)
    (A' : CMatrix a' b') (B' : CMatrix b' c') :
    (A * B) ⊗ (A' * B') = A ⊗ A' * B ⊗ B' := by
  simp_rw [kron_def, Matrix.mul_kronecker_mul]
  simp

@[simp] theorem conjTranspose_kron {a b c d : ℕ} (A : CMatrix a b) (B : CMatrix c d) :
    (A ⊗ B)ᴴ = Aᴴ ⊗ Bᴴ := by
  ext i j
  simp [kron, Matrix.conjTranspose]

end Matrix

/-! ## Gates -/

open Matrix

/-- The one-qubit Hadamard gate. -/
noncomputable def hadamard : CSquare 2 :=
  Real.sqrt 2⁻¹ • !![1,  1;
                     1, -1]

/-- `CNOT`, control on the **high** (left-kron) qubit. -/
def cnot : CSquare 4 :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- The two-qubit swap. -/
def swap : CSquare 4 :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

open Complex in
/-- The one-qubit phase shift `diag(1, e^{iφ})`. -/
noncomputable def phaseShift (φ : ℝ) : CSquare 2 :=
  !![1, 0          ;
     0, exp (φ * I)]

/-! ## Basis kets -/

/-- `∣0⟩`. -/
abbrev ket0 : CVector 2 := ![1, 0]

/-- `∣1⟩`. -/
abbrev ket1 : CVector 2 := ![0, 1]
