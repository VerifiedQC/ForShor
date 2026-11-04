import Model.Defs
import Provider.Profiles.SharedReconstruction

/-! # Affine Labels
A bundle of the affine label development, concatenating segments marked by its `BEGIN` comments. It defines the natural-number `Label` and `instantiate`, the predicates `ClearedContractions`, `SemanticContractions` and `PositiveWidths`, and `TableSpec` for tables. Key results include `cleared_iff_semantic`, `plateau_tableAt` and `fixed_word_iff_constraints`.
-/

/- BEGIN Core.lean sha256=436a526ac8f8389acd5736aa4f49d8590ef8e32df45ba631d80a548847af69e5 -/
namespace Paper.AffineILP

structure Decoration where
  k : ℤ
  r : ℤ
  y : ℤ
  hk : 2 ≤ k
  hr0 : 0 ≤ r
  hrk : r < k

def nextWidth (P x : ℤ) (d : Decoration) : ℤ :=
  x + (P * d.k) * d.y - P * d.r

theorem step_divisor_residue (P x : ℤ) (d : Decoration)
    (hP : 0 < P) (hdiv : (P * d.k) ∣ nextWidth P x d) :
    P ∣ x ∧ x / P % d.k = d.r := by
  obtain ⟨z, hz⟩ := hdiv
  have hx : x = P * (d.k * (z - d.y) + d.r) := by
    dsimp [nextWidth] at hz
    nlinarith [hz]
  constructor
  · exact ⟨d.k * (z - d.y) + d.r, hx⟩
  · rw [hx]
    have hP0 : P ≠ 0 := ne_of_gt hP
    rw [Int.mul_ediv_cancel_left _ hP0]
    have hr : d.r % d.k = d.r := Int.emod_eq_of_lt d.hr0 d.hrk
    rw [Int.add_emod, Int.mul_emod, hr]
    simp [hr]

def terminalProduct (P : ℤ) : List Decoration → ℤ
  | [] => P
  | d :: rest => terminalProduct (P * d.k) rest

def terminalWidth (P x : ℤ) : List Decoration → ℤ
  | [] => x
  | d :: rest => terminalWidth (P * d.k) (nextWidth P x d) rest

def AllResidues (P x : ℤ) : List Decoration → Prop
  | [] => P ∣ x
  | d :: rest =>
      P ∣ x ∧ x / P % d.k = d.r ∧
        AllResidues (P * d.k) (nextWidth P x d) rest

theorem terminal_forces_all_residues (P x : ℤ) (ds : List Decoration)
    (hP : 0 < P)
    (hterminal : terminalProduct P ds ∣ terminalWidth P x ds) :
    AllResidues P x ds := by
  induction ds generalizing P x with
  | nil => exact hterminal
  | cons d rest ih =>
      have hk : 0 < d.k := lt_of_lt_of_le (by decide : (0 : ℤ) < 2) d.hk
      have hPk : 0 < P * d.k := mul_pos hP hk
      have hrest := ih (P * d.k) (nextWidth P x d) hPk hterminal
      have hdiv : P * d.k ∣ nextWidth P x d := by
        cases rest with
        | nil => exact hrest
        | cons e tail => exact hrest.1
      have hstep := step_divisor_residue P x d hP hdiv
      exact ⟨hstep.1, hstep.2, hrest⟩

theorem cleared_contraction (P k w w' : ℤ) (hP : 0 < P) (hk : 2 ≤ k) :
    P * k ≤ k * (P * w) - (P * k) * w' ↔ 1 ≤ w - w' := by
  have hPk : 0 < P * k := mul_pos hP (by omega : 0 < k)
  have heq : k * (P * w) - (P * k) * w' = (P * k) * (w - w') := by ring
  rw [heq]
  constructor
  · intro h
    by_contra hn
    have hd : w - w' ≤ 0 := by omega
    have hm : (P * k) * (w - w') ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hPk) hd
    omega
  · intro h
    have hd : 0 ≤ w - w' - 1 := by omega
    have hm : 0 ≤ (P * k) * (w - w' - 1) :=
      mul_nonneg (le_of_lt hPk) hd
    nlinarith

end Paper.AffineILP
/- END Core.lean -/

/- BEGIN Offsets.lean sha256=285f0e0c299a83cd86ea5621797416b1ff8ac88dfcf1ac9630187d9a4e050e82 -/
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
/- END Offsets.lean -/

/- BEGIN Cleared.lean sha256=c80c0a038b06f15b5433ea87f498a63c85c5ae01f2cbb21ec9185eb941563092 -/
namespace Paper.AffineCost

structure Term (D : ℤ) where
  P : ℤ
  N : ℤ
  c : ℤ
  x : ℤ
  hPx : P ∣ x
  hPD : P ∣ D
  hP : 0 < P

def localCost {D : ℤ} (s : Term D) : ℤ :=
  8 * s.N * s.c * (s.x / s.P - 1)

def clearedCost {D : ℤ} (s : Term D) : ℤ :=
  8 * s.N * s.c * ((D / s.P) * s.x - D)

theorem clear_one {D : ℤ} (s : Term D) :
    D * localCost s = clearedCost s := by
  obtain ⟨w, hw⟩ := s.hPx
  obtain ⟨m, hm⟩ := s.hPD
  have hP0 : s.P ≠ 0 := ne_of_gt s.hP
  simp only [localCost, clearedCost, hw, hm]
  rw [Int.mul_ediv_cancel_left _ hP0, Int.mul_ediv_cancel_left _ hP0]
  ring

def totalCost {D : ℤ} (terms : List (Term D)) : ℤ :=
  (terms.map localCost).sum

def totalCleared {D : ℤ} (terms : List (Term D)) : ℤ :=
  (terms.map clearedCost).sum

theorem clear_sum {D : ℤ} (terms : List (Term D)) :
    D * totalCost terms = totalCleared terms := by
  induction terms with
  | nil => simp [totalCost, totalCleared]
  | cons s rest ih =>
      have ih' : D * (rest.map localCost).sum =
          (rest.map clearedCost).sum := by
        simpa [totalCost, totalCleared] using ih
      simp [totalCost, totalCleared, List.map_cons, List.sum_cons,
        mul_add, clear_one s, ih']

theorem cleared_budget_iff (D cost target : ℤ) (hD : 0 < D) :
    D * cost ≤ D * target ↔ cost ≤ target := by
  constructor
  · intro h
    by_contra hn
    have hd : target + 1 ≤ cost := by omega
    have hm : 0 ≤ D * (cost - target - 1) :=
      mul_nonneg (le_of_lt hD) (by omega)
    nlinarith
  · intro h
    exact mul_le_mul_of_nonneg_left h (le_of_lt hD)

theorem cleared_total_budget_iff {D : ℤ} (terms : List (Term D))
    (target : ℤ) (hD : 0 < D) :
    totalCleared terms ≤ D * target ↔ totalCost terms ≤ target := by
  rw [← clear_sum]
  exact cleared_budget_iff D _ _ hD

end Paper.AffineCost
/- END Cleared.lean -/

/- BEGIN Labels.lean sha256=67764d95a7623cd0b028ec17cff561aee8454816956293a683439e803e9894ae -/
namespace Paper.AffineNat

open Paper.F2CatalogTransfer Paper.F4ChargeIntervals
open Paper.F4PaddingReconstructionShared

structure Label where
  k : Nat
  r : Nat
  d : Nat
  c : Nat
  hk : 2 ≤ k
  hr : r < k
  hd : d < k

def aInt (a : Nat → Nat) : ℤ → ℤ := fun k => a k.toNat

def Label.toInt (label : Label) : Paper.AffineShared.Label where
  k := label.k
  r := label.r
  d := label.d
  c := label.c
  hk := by exact_mod_cast label.hk
  hr0 := by exact_mod_cast Nat.zero_le label.r
  hrk := by exact_mod_cast label.hr
  hd0 := by exact_mod_cast Nat.zero_le label.d
  hdk := by exact_mod_cast label.hd

def offset (a : Nat → Nat) (label : Label) : Nat :=
  a label.k + 1 + (label.r - label.d)

theorem offset_toInt (a : Nat → Nat) (label : Label) :
    Paper.AffineShared.offset (aInt a) label.toInt = (offset a label : ℤ) := by
  dsimp [Paper.AffineShared.offset, aInt, Label.toInt, offset]
  simp
  omega

def instantiate (a : Nat → Nat) (label : Label) : Paper.AffineILP.Decoration :=
  Paper.AffineShared.instantiate (aInt a) label.toInt

theorem instantiate_offset (a : Nat → Nat) (label : Label) :
    (instantiate a label).y = (offset a label : ℤ) := by
  exact offset_toInt a label

theorem plateau_reconstruct_one {K : Nat} (a : Nat → Nat) (label : Label)
    (hplateau : minCharge (K := K) label.k label.d (a label.k) =
      (label.c : WithTop Nat)) :
    ∃ t : F2Source K,
      t.arity = label.k ∧ t.charge = label.c ∧
      (rawProfile t).peakA = a label.k ∧
      (rawProfile t).peakB = a label.k - label.d ∧
      ∀ w, F2Source.childWidth t w =
        w / label.k + 1 +
          max (a label.k) ((a label.k - label.d) + w % label.k) := by
  have hfeas : ∃ C, feasible (K := K) label.k label.d (a label.k) C := by
    by_contra hn
    have htop : minCharge (K := K) label.k label.d (a label.k) = ⊤ := by
      simp [minCharge, hn]
    rw [htop] at hplateau
    cases hplateau
  obtain ⟨t, hk, hc, hA, hB, hmin, hw⟩ :=
    minCharge_exactProfile_sharedChildWidth hfeas label.hd
  have hcharge : t.charge = label.c := by
    rw [hplateau] at hmin
    exact WithTop.coe_inj.mp hmin.symm
  exact ⟨t, hk, hcharge, hA, hB, hw⟩

end Paper.AffineNat
/- END Labels.lean -/

/- BEGIN Legal.lean sha256=8127820b1287af1d5aff3766085b7c63c8d291d5c23fe9da91fabb77b9b0ee02 -/
namespace Paper.AffineChain

open Paper.AffineILP

def ClearedContractions (P x : ℤ) : List Decoration → Prop
  | [] => True
  | d :: rest =>
      P * d.k ≤ d.k * x - nextWidth P x d ∧
        ClearedContractions (P * d.k) (nextWidth P x d) rest

def SemanticContractions (P x : ℤ) : List Decoration → Prop
  | [] => True
  | d :: rest =>
      1 ≤ x / P - nextWidth P x d / (P * d.k) ∧
        SemanticContractions (P * d.k) (nextWidth P x d) rest

def PositiveWidths (P x : ℤ) : List Decoration → Prop
  | [] => 1 ≤ x / P
  | d :: rest =>
      1 ≤ x / P ∧ PositiveWidths (P * d.k) (nextWidth P x d) rest

theorem allResidues_divisor (P x : ℤ) (ds : List Decoration)
    (h : AllResidues P x ds) : P ∣ x := by
  cases ds with
  | nil => exact h
  | cons d rest => exact h.1

theorem cleared_iff_semantic (P x : ℤ) (ds : List Decoration)
    (hP : 0 < P) (hres : AllResidues P x ds) :
    ClearedContractions P x ds ↔ SemanticContractions P x ds := by
  induction ds generalizing P x with
  | nil => rfl
  | cons d rest ih =>
      have hk : 0 < d.k := lt_of_lt_of_le (by decide : (0 : ℤ) < 2) d.hk
      have hPk : 0 < P * d.k := mul_pos hP hk
      have hrest : AllResidues (P * d.k) (nextWidth P x d) rest := hres.2.2
      have hx : P ∣ x := hres.1
      have hn : P * d.k ∣ nextWidth P x d :=
        allResidues_divisor _ _ rest hrest
      obtain ⟨w, hw⟩ := hx
      obtain ⟨w', hw'⟩ := hn
      rw [hw] at hw'
      have hfirst :
          (P * d.k ≤ d.k * x - nextWidth P x d) ↔
          1 ≤ x / P - nextWidth P x d / (P * d.k) := by
        rw [hw, hw', Int.mul_ediv_cancel_left _ (ne_of_gt hP),
          Int.mul_ediv_cancel_left _ (ne_of_gt hPk)]
        exact cleared_contraction P d.k w w' hP d.hk
      change (P * d.k ≤ d.k * x - nextWidth P x d ∧
        ClearedContractions (P * d.k) (nextWidth P x d) rest) ↔
        (1 ≤ x / P - nextWidth P x d / (P * d.k) ∧
        SemanticContractions (P * d.k) (nextWidth P x d) rest)
      exact and_congr hfirst (ih (P * d.k) (nextWidth P x d) hPk hrest)

theorem terminal_positive_widths (P x : ℤ) (ds : List Decoration) (z : ℤ)
    (hP : 0 < P) (hz : 1 ≤ z)
    (hterminal : terminalWidth P x ds = terminalProduct P ds * z)
    (hstrict : SemanticContractions P x ds) :
    PositiveWidths P x ds := by
  induction ds generalizing P x with
  | nil =>
      have hP0 : P ≠ 0 := ne_of_gt hP
      change x = P * z at hterminal
      change 1 ≤ x / P
      rw [hterminal, Int.mul_ediv_cancel_left _ hP0]
      exact hz
  | cons d rest ih =>
      have hk : 0 < d.k := lt_of_lt_of_le (by decide : (0 : ℤ) < 2) d.hk
      have hPk : 0 < P * d.k := mul_pos hP hk
      have hnext := ih (P * d.k) (nextWidth P x d) hPk hterminal hstrict.2
      have hn : 1 ≤ nextWidth P x d / (P * d.k) := by
        cases rest with
        | nil => exact hnext
        | cons e tail => exact hnext.1
      have hfirst : 1 ≤ x / P - nextWidth P x d / (P * d.k) := hstrict.1
      have hw : 1 ≤ x / P := by omega
      exact ⟨hw, hnext⟩

theorem terminal_cleared_positive (P x : ℤ) (ds : List Decoration) (z : ℤ)
    (hP : 0 < P) (hz : 1 ≤ z)
    (hterminal : terminalWidth P x ds = terminalProduct P ds * z)
    (hcleared : ClearedContractions P x ds) :
    AllResidues P x ds ∧ PositiveWidths P x ds := by
  have hdiv : terminalProduct P ds ∣ terminalWidth P x ds :=
    ⟨z, hterminal⟩
  have hres := terminal_forces_all_residues P x ds hP hdiv
  have hsemantic := (cleared_iff_semantic P x ds hP hres).1 hcleared
  exact ⟨hres, terminal_positive_widths P x ds z hP hz hterminal hsemantic⟩

end Paper.AffineChain
/- END Legal.lean -/

/- BEGIN Word.lean sha256=91c7acd1169fc1d06ba5c61f1fdb3f14f5735cf2d04f032611fd8191e070cadc -/
namespace Paper.AffineSound

open Paper.AffineILP Paper.AffineShared Paper.AffineChain

def decoded (a : ℤ → ℤ) (P x : ℤ) : List Label → Prop
  | [] => P ∣ x
  | label :: rest =>
      P ∣ x ∧ x / P % label.k = label.r ∧
        nextWidth P x (instantiate a label) / (P * label.k) =
          canonicalChild (x / P) a label ∧
        decoded a (P * label.k) (nextWidth P x (instantiate a label)) rest

theorem residues_imply_decoded (a : ℤ → ℤ) (P x : ℤ)
    (labels : List Label) (hP : 0 < P)
    (hres : AllResidues P x (labels.map (instantiate a))) :
    decoded a P x labels := by
  induction labels generalizing P x with
  | nil => exact hres
  | cons label rest ih =>
      have hk : 0 < label.k :=
        lt_of_lt_of_le (by decide : (0 : ℤ) < 2) label.hk
      have hPk : 0 < P * label.k := mul_pos hP hk
      have hdiv : P ∣ x := hres.1
      have hr : x / P % label.k = label.r := hres.2.1
      obtain ⟨w, hw⟩ := hdiv
      have hP0 : P ≠ 0 := ne_of_gt hP
      have hwdiv : x / P = w := by rw [hw, Int.mul_ediv_cancel_left _ hP0]
      have hstep := cleared_width_step P x w a label hw (by simpa [hwdiv] using hr)
      have hnext : nextWidth P x (instantiate a label) / (P * label.k) =
          canonicalChild (x / P) a label := by
        rw [← hstep, mul_comm P label.k, Int.mul_ediv_cancel_left _ (by
          nlinarith : label.k * P ≠ 0)]
        simp [hwdiv]
      exact ⟨⟨w, hw⟩, hr, hnext,
        ih (P * label.k) (nextWidth P x (instantiate a label)) hPk hres.2.2⟩

theorem terminal_implies_decoded (a : ℤ → ℤ) (P x : ℤ)
    (labels : List Label) (z : ℤ) (hP : 0 < P)
    (hterminal : terminalWidth P x (labels.map (instantiate a)) =
      terminalProduct P (labels.map (instantiate a)) * z) :
    decoded a P x labels := by
  have hdiv : terminalProduct P (labels.map (instantiate a)) ∣
      terminalWidth P x (labels.map (instantiate a)) := ⟨z, hterminal⟩
  exact residues_imply_decoded a P x labels hP
    (terminal_forces_all_residues P x _ hP hdiv)

end Paper.AffineSound
/- END Word.lean -/

/- BEGIN Shared.lean sha256=f3c3237d2a9bb4214b4eab9f463486d9f1ee533ad4842fd5885a9b98c92fa8e9 -/
namespace Paper.AffineTable

open Paper.F2CatalogTransfer Paper.F4ChargeIntervals
open Paper.AffineNat

def TableSpec {K : Nat} (a d c : Nat → Nat) (k : Nat) (t : F2Source K) : Prop :=
  t.arity = k ∧ t.charge = c k ∧
  (rawProfile t).peakA = a k ∧
  (rawProfile t).peakB = a k - d k ∧
  ∀ w, F2Source.childWidth t w =
    w / k + 1 + max (a k) ((a k - d k) + w % k)

theorem plateau_reconstruct_key {K : Nat} (a d c : Nat → Nat) (k : Nat)
    (hk : 2 ≤ k) (hd : d k < k)
    (hplateau : minCharge (K := K) k (d k) (a k) = (c k : WithTop Nat)) :
    ∃ t : F2Source K, TableSpec a d c k t := by
  let label : Paper.AffineNat.Label :=
    { k := k, r := 0, d := d k, c := c k, hk := hk,
      hr := by omega, hd := hd }
  obtain ⟨t, htk, htc, hta, htb, htw⟩ :=
    plateau_reconstruct_one (K := K) a label hplateau
  refine ⟨t, ?_⟩
  exact ⟨htk, htc, hta, htb, htw⟩

noncomputable def tableAt {K : Nat} (a d c : Nat → Nat) (k : Nat) :
    Option (F2Source K) := by
  classical
  exact
  if h : ∃ t : F2Source K, TableSpec a d c k t then
    some (Classical.choose h)
  else none

theorem tableAt_spec {K : Nat} (a d c : Nat → Nat) (k : Nat)
    (h : ∃ t : F2Source K, TableSpec a d c k t) :
    ∃ t, tableAt (K := K) a d c k = some t ∧ TableSpec a d c k t := by
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  simp [tableAt, h]

theorem plateau_tableAt {K : Nat} (a d c : Nat → Nat) (k : Nat)
    (hk : 2 ≤ k) (hd : d k < k)
    (hplateau : minCharge (K := K) k (d k) (a k) = (c k : WithTop Nat)) :
    ∃ t, tableAt (K := K) a d c k = some t ∧ TableSpec a d c k t :=
  tableAt_spec a d c k (plateau_reconstruct_key a d c k hk hd hplateau)

end Paper.AffineTable
/- END Shared.lean -/

/- BEGIN Word.lean sha256=8d60d6f22d22b61f1e2c774bd0b45bb43af8a70c74dd26cc5593f51dab2decc3 -/
namespace Paper.AffineFixed

open Paper.AffineILP Paper.AffineChain Paper.AffineShared
open Paper.AffineNat Paper.AffineTable Paper.F4ChargeIntervals

theorem instantiate_map (a : Nat → Nat) (labels : List Paper.AffineNat.Label) :
    labels.map (Paper.AffineNat.instantiate a) =
      (labels.map Paper.AffineNat.Label.toInt).map
        (Paper.AffineShared.instantiate (Paper.AffineNat.aInt a)) := by
  simp [List.map_map, Paper.AffineNat.instantiate]

theorem fixed_word_sound {K : Nat} (a d c : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x z : ℤ) (hP : 0 < P)
    (hz : 1 ≤ z)
    (hshared : ∀ label ∈ labels,
      label.d = d label.k ∧ label.c = c label.k ∧
      minCharge (K := K) label.k (d label.k) (a label.k) =
        (c label.k : WithTop Nat))
    (hterminal : terminalWidth P x (labels.map (Paper.AffineNat.instantiate a)) =
      terminalProduct P (labels.map (Paper.AffineNat.instantiate a)) * z)
    (hcleared : ClearedContractions P x
      (labels.map (Paper.AffineNat.instantiate a))) :
    Paper.AffineSound.decoded (Paper.AffineNat.aInt a) P x
      (labels.map Paper.AffineNat.Label.toInt) ∧
    PositiveWidths P x (labels.map (Paper.AffineNat.instantiate a)) ∧
    SemanticContractions P x (labels.map (Paper.AffineNat.instantiate a)) ∧
    (∀ label ∈ labels, ∃ t : Paper.F2CatalogTransfer.F2Source K,
      tableAt (K := K) a d c label.k = some t ∧
      TableSpec a d c label.k t) := by
  let ds := labels.map (Paper.AffineNat.instantiate a)
  have hres : AllResidues P x ds :=
    (terminal_cleared_positive P x ds z hP hz hterminal hcleared).1
  have hpos : PositiveWidths P x ds :=
    (terminal_cleared_positive P x ds z hP hz hterminal hcleared).2
  have hsemantic : SemanticContractions P x ds :=
    (cleared_iff_semantic P x ds hP hres).1 hcleared
  have hdecoded : Paper.AffineSound.decoded (Paper.AffineNat.aInt a) P x
      (labels.map Paper.AffineNat.Label.toInt) := by
    apply Paper.AffineSound.terminal_implies_decoded _ _ _ _ z hP
    simpa only [← instantiate_map a labels] using hterminal
  refine ⟨hdecoded, hpos, hsemantic, ?_⟩
  intro label hmem
  obtain ⟨hd, hc, hp⟩ := hshared label hmem
  have hdk : d label.k < label.k := by simpa [← hd] using label.hd
  exact plateau_tableAt a d c label.k label.hk hdk hp

end Paper.AffineFixed
/- END Word.lean -/

/- BEGIN Child.lean sha256=8141e2e3fdc4f9c43f8b3f883ee0f1f1a6fbf8f255182c69fa0d035a7059efd6 -/
namespace Paper.AffineBridge

open Paper.F2CatalogTransfer Paper.F4ChargeIntervals
open Paper.AffineNat Paper.AffineTable Paper.AffineShared

theorem finite_plateau_d_le_a {K : Nat} (a d c : Nat → Nat) (k : Nat)
    (hplateau : minCharge (K := K) k (d k) (a k) = (c k : WithTop Nat)) :
    d k ≤ a k := by
  by_contra hn
  have hnone : ¬ ∃ C, feasible (K := K) k (d k) (a k) C := by
    rintro ⟨C, hC⟩
    exact hn hC.1
  simp [minCharge, hnone] at hplateau

theorem canonicalChild_natCast (a d : Nat → Nat) (k w : Nat)
    (hda : d k ≤ a k) :
    ((w / k + 1 + max (a k) ((a k - d k) + w % k) : Nat) : ℤ) =
      (w : ℤ) / k + 1 +
        max (a k : ℤ) ((a k : ℤ) - d k + (w : ℤ) % k) := by
  norm_cast

theorem table_child_eq_canonical {K : Nat} (a d c : Nat → Nat)
    (label : Paper.AffineNat.Label) (w : Nat) (t : F2Source K)
    (hda : d label.k ≤ a label.k)
    (hd : label.d = d label.k) (hr : w % label.k = label.r)
    (ht : TableSpec a d c label.k t) :
    (F2Source.childWidth t w : ℤ) =
      Paper.AffineShared.canonicalChild w (Paper.AffineNat.aInt a)
        label.toInt := by
  rw [ht.2.2.2.2 w]
  rw [canonicalChild_natCast a d label.k w hda]
  simp [Paper.AffineShared.canonicalChild, Paper.AffineNat.aInt,
    Paper.AffineNat.Label.toInt, ← hd, ← hr]

end Paper.AffineBridge
/- END Child.lean -/

/- BEGIN Actual.lean sha256=99a91306e138f5b0e80c2beb6f0eaa76fbcf300e4a7f7cb3bdfe647be29ab072 -/
namespace Paper.AffineStep

open Paper.AffineNat Paper.AffineTable Paper.AffineBridge
open Paper.AffineShared Paper.AffineILP
open Paper.F2CatalogTransfer Paper.F4ChargeIntervals

theorem actual_child_cleared {K : Nat} (a d c : Nat → Nat)
    (label : Paper.AffineNat.Label) (t : F2Source K)
    (P : ℤ) (w : Nat)
    (hd : label.d = d label.k)
    (hr : w % label.k = label.r)
    (hplateau : minCharge (K := K) label.k (d label.k) (a label.k) =
      (c label.k : WithTop Nat))
    (ht : TableSpec a d c label.k t) :
    nextWidth P (P * w) (Paper.AffineNat.instantiate a label) =
      P * label.k * (F2Source.childWidth t w : ℤ) := by
  have hda : d label.k ≤ a label.k :=
    finite_plateau_d_le_a a d c label.k hplateau
  have hcanon := table_child_eq_canonical a d c label w t hda hd hr ht
  have hri : (w : ℤ) % label.toInt.k = label.toInt.r := by
    have hri0 : (w : ℤ) % (label.k : ℤ) = label.r := by
      exact_mod_cast hr
    simpa [Paper.AffineNat.Label.toInt] using hri0
  have hstep := cleared_width_step P (P * w) w (aInt a) label.toInt rfl hri
  rw [← hcanon] at hstep
  exact hstep.symm

end Paper.AffineStep
/- END Actual.lean -/

/- BEGIN Word.lean sha256=676ef40ac75ffe4a92b51277ecb0c85b405362019eea7f2761b452a8572517d5 -/
namespace Paper.AffineActual

open Paper.AffineNat Paper.AffineTable Paper.AffineStep
open Paper.AffineILP Paper.AffineChain Paper.F2CatalogTransfer
open Paper.F4ChargeIntervals

def ActualWord {K : Nat} (a d c : Nat → Nat) (P x : ℤ) :
    List Paper.AffineNat.Label → Prop
  | [] => ∃ w : Nat, x = P * w ∧ 1 ≤ w
  | label :: rest =>
      ∃ (t : F2Source K) (w : Nat),
        tableAt (K := K) a d c label.k = some t ∧
        TableSpec a d c label.k t ∧
        x = P * w ∧ w % label.k = label.r ∧
        nextWidth P x (Paper.AffineNat.instantiate a label) =
          P * label.k * (F2Source.childWidth t w : ℤ) ∧
        F2Source.childWidth t w < w ∧
        ActualWord (K := K) a d c (P * label.k)
          (nextWidth P x (Paper.AffineNat.instantiate a label)) rest

theorem constraints_to_actual {K : Nat} (a d c : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x : ℤ) (hP : 0 < P)
    (hshared : ∀ label ∈ labels,
      label.d = d label.k ∧ label.c = c label.k ∧
      minCharge (K := K) label.k (d label.k) (a label.k) =
        (c label.k : WithTop Nat))
    (hres : AllResidues P x (labels.map (Paper.AffineNat.instantiate a)))
    (hpos : PositiveWidths P x (labels.map (Paper.AffineNat.instantiate a)))
    (hsem : SemanticContractions P x
      (labels.map (Paper.AffineNat.instantiate a))) :
    ActualWord (K := K) a d c P x labels := by
  induction labels generalizing P x with
  | nil =>
      have hdiv : P ∣ x := hres
      have hpositive : 1 ≤ x / P := hpos
      let w : Nat := (x / P).toNat
      have hw : (w : ℤ) = x / P := by
        exact Int.toNat_of_nonneg (by omega : 0 ≤ x / P)
      have hx : x = P * w := by
        obtain ⟨z, hz⟩ := hdiv
        rw [hz] at hw ⊢
        rw [Int.mul_ediv_cancel_left _ (ne_of_gt hP)] at hw
        simp [hw]
      exact ⟨w, hx, by omega⟩
  | cons label rest ih =>
      have hkpos : 0 < (label.k : ℤ) := by
        have hkn : 0 < label.k :=
          lt_of_lt_of_le (by decide : 0 < 2) label.hk
        exact_mod_cast hkn
      have hPk : 0 < P * label.k := mul_pos hP hkpos
      have hdiv : P ∣ x := hres.1
      have hpositive : 1 ≤ x / P := hpos.1
      let w : Nat := (x / P).toNat
      have hw : (w : ℤ) = x / P := by
        exact Int.toNat_of_nonneg (by omega : 0 ≤ x / P)
      have hx : x = P * w := by
        obtain ⟨z, hz⟩ := hdiv
        rw [hz] at hw ⊢
        rw [Int.mul_ediv_cancel_left _ (ne_of_gt hP)] at hw
        simp [hw]
      obtain ⟨hd, hc, hp⟩ := hshared label (by simp)
      obtain ⟨t, ht, hspec⟩ :=
        plateau_tableAt a d c label.k label.hk (by simpa [← hd] using label.hd) hp
      have hr : w % label.k = label.r := by
        have hri : (w : ℤ) % (label.k : ℤ) = label.r := by
          simpa [hw, Paper.AffineNat.Label.toInt] using hres.2.1
        exact_mod_cast hri
      have hnext : nextWidth P x (Paper.AffineNat.instantiate a label) =
          P * label.k * (F2Source.childWidth t w : ℤ) := by
        rw [hx]
        exact actual_child_cleared a d c label t P w hd hr hp hspec
      have hstrict : F2Source.childWidth t w < w := by
        have hfirst := hsem.1
        change 1 ≤ x / P -
          nextWidth P x (Paper.AffineNat.instantiate a label) /
            (P * label.k) at hfirst
        rw [hnext, hx, Int.mul_ediv_cancel_left _ (ne_of_gt hP),
          Int.mul_ediv_cancel_left _ (ne_of_gt hPk)] at hfirst
        omega
      have hrestShared : ∀ label ∈ rest,
          label.d = d label.k ∧ label.c = c label.k ∧
          minCharge (K := K) label.k (d label.k) (a label.k) =
            (c label.k : WithTop Nat) := by
        intro q hq
        exact hshared q (by simp [hq])
      refine ⟨t, w, ht, hspec, hx, hr, hnext, hstrict, ?_⟩
      exact ih (P * label.k) (nextWidth P x (Paper.AffineNat.instantiate a label))
        hPk hrestShared hres.2.2 hpos.2 hsem.2

end Paper.AffineActual
/- END Word.lean -/

/- BEGIN Word.lean sha256=d492e7a6df3f76027fadbee4b5dcbe1d2209100fb7c1fcb74f480354617c46f2 -/
namespace Paper.AffineConverse

open Paper.AffineNat Paper.AffineActual Paper.AffineILP Paper.AffineChain
open Paper.F4ChargeIntervals

theorem actual_to_constraints {K : Nat} (a d c : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x : ℤ) (hP : 0 < P)
    (hactual : ActualWord (K := K) a d c P x labels) :
    ∃ z : Nat, 1 ≤ z ∧
      terminalWidth P x (labels.map (Paper.AffineNat.instantiate a)) =
        terminalProduct P (labels.map (Paper.AffineNat.instantiate a)) * z ∧
      ClearedContractions P x (labels.map (Paper.AffineNat.instantiate a)) := by
  induction labels generalizing P x with
  | nil =>
      obtain ⟨w, hx, hw⟩ := hactual
      exact ⟨w, hw, hx, trivial⟩
  | cons label rest ih =>
      obtain ⟨t, w, ht, hspec, hx, hr, hnext, hstrict, hrest⟩ := hactual
      have hk : 2 ≤ (label.k : ℤ) := by exact_mod_cast label.hk
      have hkpos : 0 < (label.k : ℤ) := by omega
      have hPk : 0 < P * label.k := mul_pos hP hkpos
      obtain ⟨z, hz, hterm, hcleared⟩ :=
        ih (P * label.k) (nextWidth P x (Paper.AffineNat.instantiate a label))
          hPk hrest
      have hfirst : P * label.k ≤ label.k * x -
          nextWidth P x (Paper.AffineNat.instantiate a label) := by
        rw [hnext, hx]
        apply (cleared_contraction P label.k w (t.childWidth w) hP hk).2
        have hi : (t.childWidth w : ℤ) < w := by exact_mod_cast hstrict
        omega
      exact ⟨z, hz, hterm, ⟨hfirst, hcleared⟩⟩

theorem fixed_word_iff_constraints {K : Nat} (a d c : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x : ℤ) (hP : 0 < P)
    (hshared : ∀ label ∈ labels,
      label.d = d label.k ∧ label.c = c label.k ∧
      minCharge (K := K) label.k (d label.k) (a label.k) =
        (c label.k : WithTop Nat)) :
    ActualWord (K := K) a d c P x labels ↔
      ∃ z : ℤ, 1 ≤ z ∧
        terminalWidth P x (labels.map (Paper.AffineNat.instantiate a)) =
          terminalProduct P (labels.map (Paper.AffineNat.instantiate a)) * z ∧
        ClearedContractions P x
          (labels.map (Paper.AffineNat.instantiate a)) := by
  constructor
  · intro hactual
    obtain ⟨z, hz, hterm, hclear⟩ :=
      actual_to_constraints a d c labels P x hP hactual
    exact ⟨z, by exact_mod_cast hz, hterm, hclear⟩
  · rintro ⟨z, hz, hterm, hclear⟩
    have hboth := terminal_cleared_positive P x
      (labels.map (Paper.AffineNat.instantiate a)) z hP hz hterm hclear
    have hsem := (cleared_iff_semantic P x
      (labels.map (Paper.AffineNat.instantiate a)) hP hboth.1).1 hclear
    exact constraints_to_actual a d c labels P x hP hshared
      hboth.1 hboth.2 hsem

end Paper.AffineConverse
/- END Word.lean -/
