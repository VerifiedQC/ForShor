import ILPEncoding.Affine.Core

/-! # Shared Affine Offsets
Defines the `Label` structure and `offset`, where the only offset variable is the function `a` indexed by arity, and `instantiate` to a `Decoration`. Proves `same_arity_same_offset_variable`, `canonicalChild_affine` and the cleared width step `cleared_width_step`.
-/

namespace Paper.AffineShared

structure Label where
  k : ℤ
  r : ℤ
  d : ℤ
  c : ℤ
  hk : 2 ≤ k
  hr0 : 0 ≤ r
  hrk : r < k
  hd0 : 0 ≤ d
  hdk : d < k

/-- The only offset variable is the function `a` indexed by arity. -/
def offset (a : ℤ → ℤ) (label : Label) : ℤ :=
  a label.k + 1 + max 0 (label.r - label.d)

def instantiate (a : ℤ → ℤ) (label : Label) : Paper.AffineILP.Decoration :=
  ⟨label.k, label.r, offset a label, label.hk, label.hr0, label.hrk⟩

theorem same_arity_same_offset_variable (a : ℤ → ℤ) (u v : Label)
    (hk : u.k = v.k) : a u.k = a v.k := congrArg a hk

def canonicalChild (w : ℤ) (a : ℤ → ℤ) (label : Label) : ℤ :=
  w / label.k + 1 + max (a label.k) (a label.k - label.d + w % label.k)

theorem canonicalChild_affine (w : ℤ) (a : ℤ → ℤ) (label : Label)
    (hr : w % label.k = label.r) :
    canonicalChild w a label = w / label.k + offset a label := by
  simp only [canonicalChild, offset, hr]
  omega

theorem cleared_width_step (P x w : ℤ) (a : ℤ → ℤ) (label : Label)
    (hx : x = P * w) (hr : w % label.k = label.r) :
    P * label.k * canonicalChild w a label =
      Paper.AffineILP.nextWidth P x (instantiate a label) := by
  have hdivision := Int.mul_ediv_add_emod w label.k
  have hmult := congrArg (fun z : ℤ => P * z) hdivision
  rw [canonicalChild_affine w a label hr]
  simp only [Paper.AffineILP.nextWidth, instantiate]
  dsimp [offset]
  rw [hr] at hmult
  nlinarith [hmult]

end Paper.AffineShared
