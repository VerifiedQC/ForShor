import FastMultiplication.ShorVerification.Implementation.Reference.Balanced.Defs
import FastMultiplication.ShorVerification.Implementation.Shared.GateLaws
import FastMultiplication.ShorVerification.Implementation.Shared.States

/-!
# Balanced phase products: basis-state correctness

`splitGate_ket`: on every basis state whose two reserves are zero, the balanced
split of `x` against `z` applies exactly the phase `φ · x · z` (signed values)
and returns the basis state, for every plan that passes `fitsB` — so for every
pair of widths the plan rule produces. The controlled form applies it exactly
when the control is one.

The proof is the recombination identity
`extToInt x = toNat (lowBlock x w) + 2^w · extToInt (highPart x w)` (signed top,
unsigned low part; `extToInt_split`) together with the fact that each block's
extension gates restore the basis state.
-/

namespace Shor
namespace Balanced

open Gate

universe u

/-! ## Arithmetic: the recombination identity -/

/-- Two's-complement decoding of a concatenation: unsigned low part, signed high part. -/
theorem tcDecode_split (w m lo hi : ℕ) (hlo : lo < 2 ^ w) (_hhi : hi < 2 ^ (m + 1)) :
    tcDecodeWidth (w + (m + 1)) (lo + 2 ^ w * hi) =
      (lo : ℤ) + 2 ^ w * tcDecodeWidth (m + 1) hi := by
  have hw : w + (m + 1) = (w + m) + 1 := by omega
  rw [hw]
  simp only [tcDecodeWidth]
  have h2 : (2 : ℕ) ^ (w + m) = 2 ^ w * 2 ^ m := pow_add 2 w m
  have h3 : (2 : ℕ) ^ (w + m + 1) = 2 ^ w * 2 ^ (m + 1) := by rw [← pow_add]; ring_nf
  by_cases hh : hi < 2 ^ m
  · have hv : lo + 2 ^ w * hi < 2 ^ (w + m) := by
      rw [h2]
      have : 2 ^ w * hi + 2 ^ w ≤ 2 ^ w * 2 ^ m := by
        have := Nat.mul_le_mul_left (2 ^ w) (Nat.succ_le_of_lt hh)
        linarith [this]
      omega
    simp [hv, hh]
  · have hv : ¬ lo + 2 ^ w * hi < 2 ^ (w + m) := by
      rw [h2]
      have := Nat.mul_le_mul_left (2 ^ w) (Nat.le_of_not_lt hh)
      omega
    simp only [hv, hh, dite_false]
    rw [h3]
    push_cast
    ring

theorem toNat_take_drop {Basis : Type u} [RegEncoding Basis] (r : Reg) (w : ℕ) (hw : w ≤ regSize r)
    (b : Basis) :
    RegEncoding.toNat r b =
      RegEncoding.toNat (r.take w) b + 2 ^ w * RegEncoding.toNat (r.drop w) b := by
  have h := RegEncoding.toNat_split r ⟨w, hw⟩ b
  simp only [splitLeft, splitRight] at h
  have hs : ASize (r.take w) = 2 ^ w := by
    simp [ASize, regSize, Reg.width, Reg.take] at hw ⊢
    omega
  rw [hs] at h
  exact h

/-- **The recombination identity.** For `w < x.width` the signed value of `x` is
the unsigned low block plus `2^w` times the signed high part. -/
theorem extToInt_split {Basis : Type u} [RegEncoding Basis] (x : ExtReg) (w : ℕ)
    (hw : w < x.width) (b : Basis) :
    extToInt x b =
      ((lowBlock x w).toNat b : ℤ) + 2 ^ w * extToInt (highPart x w) b := by
  obtain ⟨m, hm⟩ : ∃ m, x.width = w + (m + 1) := ⟨x.width - w - 1, by omega⟩
  have hsplit := toNat_take_drop x.active w (by unfold ExtReg.width at hw; omega) b
  have hlo : RegEncoding.toNat (x.active.take w) b < 2 ^ w := by
    have := RegEncoding.toNat_lt_ASize (x.active.take w) b
    have hs : ASize (x.active.take w) = 2 ^ w := by
      simp [ASize, regSize, Reg.width, Reg.take, ExtReg.width] at hw ⊢
      omega
    rwa [hs] at this
  have hhw : (highPart x w).width = m + 1 := by rw [highPart_width]; omega
  have hhi : RegEncoding.toNat (x.active.drop w) b < 2 ^ (m + 1) := by
    have := RegEncoding.toNat_lt_ASize (x.active.drop w) b
    have hs : ASize (x.active.drop w) = 2 ^ (m + 1) := by
      have := hhw
      simp [highPart, ExtReg.width] at this
      simp [ASize, this]
    rwa [hs] at this
  unfold extToInt
  rw [hhw, hm]
  simp only [ExtReg.toNat, lowBlock, highPart]
  rw [hsplit]
  exact tcDecode_split w m _ _ hlo hhi

/-! ## Phase factors -/

/-- The phase a signed phase product applies to a basis state with values `X`, `Z`. -/
noncomputable def phaseFactor (φ : Angle) (X Z : ℤ) : ℂ :=
  Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I * (((X : ℤ) : ℂ) * ((Z : ℤ) : ℂ)))

theorem phaseFactor_add (φ : Angle) (w : ℕ) (u h Z : ℤ) :
    phaseFactor φ u Z * phaseFactor (φ * 2 ^ w) h Z = phaseFactor φ (u + 2 ^ w * h) Z := by
  unfold phaseFactor
  rw [← Complex.exp_add]
  congr 1
  rw [show (φ * 2 ^ w : ℚ) = φ * ((2 ^ w : ℕ) : ℚ) by push_cast; ring]
  rw [Angle.toReal_mul_rat]
  push_cast
  ring

theorem phaseFactor_comm (φ : Angle) (X Z : ℤ) : phaseFactor φ X Z = phaseFactor φ Z X := by
  unfold phaseFactor; ring_nf

/-- Whether a product of kind `c` fires on basis state `b`. -/
def Ctl.on {Basis : Type u} [RegEncoding Basis] : Ctl → Basis → Bool
  | .none, _ => true
  | .ctrl q, b => RegEncoding.bit q b

/-- The control (if any) lies outside both operands' owned qubits. -/
def Ctl.Away : Ctl → ExtReg → ExtReg → Prop
  | .none, _, _ => True
  | .ctrl q, x, z => ExtReg.CtrlDisjoint q x z

/-- The scalar a kind-`c` product applies at a basis state. -/
noncomputable def Ctl.factor {Basis : Type u} [RegEncoding Basis] (c : Ctl) (φ : Angle) (X Z : ℤ)
    (b : Basis) : ℂ :=
  if c.on b then phaseFactor φ X Z else 1

theorem Ctl.eval_gate_ket (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (c : Ctl) (φ : Angle) (x z : ExtReg) (b : qs.Basis) :
    qs.eval (c.gate φ x z) (qs.ket b) = c.factor φ (extToInt x b) (extToInt z b) b • qs.ket b := by
  cases c with
  | none =>
      simp only [Ctl.gate, Ctl.factor, Ctl.on, ite_true]
      rw [PhaseSemantics.eval_SignedPhaseProd_ket]
      rfl
  | ctrl q =>
      simp only [Ctl.gate, Ctl.factor, Ctl.on]
      rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
      by_cases hq : RegEncoding.bit q b = true
      · simp only [hq, ite_true]; rfl
      · simp [hq]

/-! ## Cleanliness of the two reserves -/

/-- Both reserves are zero. Lower blocks and the high part share `x`'s reserve. -/
def Clean {Basis : Type u} [RegEncoding Basis] (x z : ExtReg) (b : Basis) : Prop :=
  RegEncoding.toNat x.reserve b = 0 ∧ RegEncoding.toNat z.reserve b = 0

theorem Reg.ext_qubits {r s : Reg} (h : r.qubits = s.qubits) : r = s := by
  cases r; cases s; simp_all

theorem toNat_take_zero {Basis : Type u} [RegEncoding Basis] (r : Reg) (n : ℕ) (b : Basis)
    (h : RegEncoding.toNat r b = 0) : RegEncoding.toNat (r.take n) b = 0 := by
  by_cases hn : n ≤ regSize r
  · have := toNat_take_drop r n hn b
    omega
  · have : r.take n = r := Reg.ext_qubits (by
      simp [Reg.take, regSize, Reg.width] at hn ⊢; omega)
    rw [this]; exact h

theorem toNat_drop_zero {Basis : Type u} [RegEncoding Basis] (r : Reg) (n : ℕ) (b : Basis)
    (h : RegEncoding.toNat r b = 0) : RegEncoding.toNat (r.drop n) b = 0 := by
  by_cases hn : n ≤ regSize r
  · have := toNat_take_drop r n hn b
    have hp : 0 < 2 ^ n := pow_pos (by norm_num) n
    have : 2 ^ n * RegEncoding.toNat (r.drop n) b = 0 := by omega
    rcases Nat.mul_eq_zero.mp this with h1 | h1
    · omega
    · exact h1
  · have hlt := RegEncoding.toNat_lt_ASize (r.drop n) b
    have : ASize (r.drop n) = 1 := by
      simp [ASize, regSize, Reg.width, Reg.drop] at hn ⊢; omega
    omega

/-- Clean reserves give the freshness `extToInt_grow_*` needs. -/
theorem fresh_of_zero {Basis : Type u} [RegEncoding Basis] (e : ExtReg) (n : ℕ) (b : Basis)
    (h : RegEncoding.toNat e.reserve b = 0) : e.FreshFor n b := by
  unfold ExtReg.FreshFor FreshZero ExtReg.newBits
  exact toNat_take_zero _ _ _ h

theorem zero_of_fresh_capacity {Basis : Type u} [RegEncoding Basis] (e : ExtReg) (b : Basis)
    (h : e.FreshFor e.capacity b) : RegEncoding.toNat e.reserve b = 0 := by
  unfold ExtReg.FreshFor FreshZero ExtReg.newBits at h
  have : e.reserve.take e.capacity = e.reserve := Reg.ext_qubits (by
    simp [Reg.take, ExtReg.capacity, regSize, Reg.width])
  rwa [this] at h

/-! ## Owned-qubit bookkeeping -/

theorem lowBlock_owned_sub (x : ExtReg) (w : ℕ) : (lowBlock x w).ownedQubits ⊆ x.ownedQubits := by
  intro q hq
  simp only [ExtReg.ownedQubits, lowBlock, List.mem_append] at hq ⊢
  rcases hq with h | h
  · exact Or.inl (List.take_subset _ _ h)
  · exact Or.inr h

theorem highPart_owned_sub (x : ExtReg) (w : ℕ) : (highPart x w).ownedQubits ⊆ x.ownedQubits := by
  intro q hq
  simp only [ExtReg.ownedQubits, highPart, List.mem_append] at hq ⊢
  rcases hq with h | h
  · exact Or.inl (List.drop_subset _ _ h)
  · exact Or.inr h

theorem active_sub_owned (x : ExtReg) : x.active.qubits ⊆ x.ownedQubits :=
  fun _ h => List.mem_append_left _ h

theorem reserve_sub_owned (x : ExtReg) : x.reserve.qubits ⊆ x.ownedQubits :=
  fun _ h => List.mem_append_right _ h

theorem newBits_sub_owned (x : ExtReg) (n : ℕ) : (x.newBits n).qubits ⊆ x.ownedQubits :=
  fun _ h => reserve_sub_owned x (List.take_subset _ _ h)

theorem grow_active_sub_owned (x : ExtReg) (n : ℕ) : (x.grow n).active.qubits ⊆ x.ownedQubits := by
  rw [← Gate.ExtReg.ownedQubits_grow x n]; exact active_sub_owned _

theorem grow_reserve_sub_reserve (x : ExtReg) (n : ℕ) :
    (x.grow n).reserve.qubits ⊆ x.reserve.qubits :=
  fun _ h => List.drop_subset _ _ h

theorem ownedDisjoint_mono {x x' z z' : ExtReg} (h : ExtReg.OwnedDisjoint x z)
    (hx : x'.ownedQubits ⊆ x.ownedQubits) (hz : z'.ownedQubits ⊆ z.ownedQubits) :
    ExtReg.OwnedDisjoint x' z' :=
  List.disjoint_of_subset_left hx (List.disjoint_of_subset_right hz h)

theorem ctlAway_mono {c : Ctl} {x x' z z' : ExtReg} (h : c.Away x z)
    (hx : x'.ownedQubits ⊆ x.ownedQubits) (hz : z'.ownedQubits ⊆ z.ownedQubits) : c.Away x' z' := by
  cases c with
  | none => trivial
  | ctrl q => exact ⟨fun hq => h.1 (hx hq), fun hq => h.2 (hz hq)⟩

/-! ## What sign extension changes -/

theorem toNat_signExtendBasis_of_disj {Basis : Type u} [RegEncoding Basis] (r : ExtReg) (n : ℕ)
    (R : Reg) (hR : Disjoint R (r.newBits n)) (b : Basis) :
    RegEncoding.toNat R (signExtendBasis r n b) = RegEncoding.toNat R b := by
  unfold signExtendBasis
  exact RegEncoding.toNat_left_write_right R _ hR b _

theorem bit_signExtendBasis_of_not_mem {Basis : Type u} [RegEncoding Basis] (r : ExtReg) (n : ℕ)
    (q : ℕ) (hq : q ∉ r.ownedQubits) (b : Basis) :
    RegEncoding.bit q (signExtendBasis r n b) = RegEncoding.bit q b := by
  unfold signExtendBasis
  exact RegEncoding.bit_writeNat_out _ _ _ _ (fun h => hq (newBits_sub_owned r n h))

theorem extToInt_signExtendBasis_of_disj {Basis : Type u} [RegEncoding Basis] (r : ExtReg) (n : ℕ)
    (e : ExtReg) (he : Disjoint e.active (r.newBits n)) (b : Basis) :
    extToInt e (signExtendBasis r n b) = extToInt e b := by
  unfold extToInt ExtReg.toNat
  rw [toNat_signExtendBasis_of_disj r n e.active he b]

theorem disj_of_owned {x z : ExtReg} (h : ExtReg.OwnedDisjoint x z) {R S : Reg}
    (hR : R.qubits ⊆ x.ownedQubits) (hS : S.qubits ⊆ z.ownedQubits) : Disjoint R S :=
  List.disjoint_of_subset_left hR (List.disjoint_of_subset_right hS h)

theorem disj_of_owned' {x z : ExtReg} (h : ExtReg.OwnedDisjoint x z) {R S : Reg}
    (hR : R.qubits ⊆ z.ownedQubits) (hS : S.qubits ⊆ x.ownedQubits) : Disjoint R S :=
  (disj_of_owned h hS hR).symm

theorem ctl_on_signExtendBasis {Basis : Type u} [RegEncoding Basis] (c : Ctl) (r : ExtReg) (n : ℕ)
    (hc : ∀ q, c = .ctrl q → q ∉ r.ownedQubits) (b : Basis) :
    c.on (signExtendBasis r n b) = c.on b := by
  cases c with
  | none => rfl
  | ctrl q => exact bit_signExtendBasis_of_not_mem r n q (hc q rfl) b

theorem Clean.signExtend_x {Basis : Type u} [RegEncoding Basis] {x z : ExtReg} {b : Basis}
    (hd : ExtReg.OwnedDisjoint x z) (h : Clean x z b) (n : ℕ) :
    RegEncoding.toNat z.reserve (signExtendBasis x n b) = 0 := by
  rw [toNat_signExtendBasis_of_disj x n _ (disj_of_owned' hd (reserve_sub_owned z)
    (newBits_sub_owned x n))]
  exact h.2

/-! ## One lower block -/

theorem lowGate_ket (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (c : Ctl) (φ : Angle) (x z : ExtReg) (w t : ℕ) (b : qs.Basis)
    (_hw : w ≤ x.width) (ht : w + 1 ≤ t) (hxcap : t - w ≤ x.capacity) (hzcap : t - z.width ≤ z.capacity)
    (hd : ExtReg.OwnedDisjoint x z) (hc : c.Away x z) (hb : Clean x z b) :
    qs.eval (lowGate c φ x z w t) (qs.ket b) =
      c.factor φ ((lowBlock x w).toNat b) (extToInt z b) b • qs.ket b := by
  set xb := lowBlock x w with hxb
  set a := t - w
  set d := t - z.width
  set b' := signExtendBasis z d b with hb'
  simp only [lowGate, QSemantics.eval_seq]
  rw [ExtensionSemantics.eval_zeroExtend, ExtensionSemantics.eval_signExtend_ket_total,
    Ctl.eval_gate_ket, QSemantics.eval_smul, ExtensionSemantics.eval_signDealloc_ket_total,
    QSemantics.eval_smul, ExtensionSemantics.eval_zeroDealloc]
  rw [show signDeallocBasis z d (signExtendBasis z d b) = b from signExtendBasis_involutive z d b]
  congr 1
  -- the three readings at `b'`
  have hxbsub : xb.ownedQubits ⊆ x.ownedQubits := lowBlock_owned_sub x w
  have hx : extToInt (xb.grow a) b' = ((xb.toNat b : ℕ) : ℤ) := by
    rw [hb', extToInt_signExtendBasis_of_disj z d _
      (disj_of_owned hd (fun q hq => hxbsub (grow_active_sub_owned xb a hq)) (newBits_sub_owned z d))]
    exact Gate.ExtReg.extToInt_grow_of_fresh xb a b (show xb.CanGrow a by simp only [ExtReg.CanGrow, hxb, lowBlock_capacity]; exact hxcap)
      (fresh_of_zero _ _ _ hb.1) (by omega)
  have hz : extToInt (z.grow d) b' = extToInt z b :=
    extToInt_grow_signExtendBasis z d b (by simpa [ExtReg.CanGrow] using hzcap) (fresh_of_zero _ _ _ hb.2)
  have hon : c.on b' = c.on b :=
    ctl_on_signExtendBasis c z d (fun q hq hmem => by subst hq; exact hc.2 hmem) b
  unfold Ctl.factor
  rw [hx, hz, hon]

/-! ## The top block -/

theorem topGate_ket (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (c : Ctl) (φ : Angle) (x z : ExtReg) (t : ℕ) (b : qs.Basis)
    (hxcap : t - x.width ≤ x.capacity) (hzcap : t - z.width ≤ z.capacity)
    (hd : ExtReg.OwnedDisjoint x z) (hc : c.Away x z) (hb : Clean x z b) :
    qs.eval (topGate c φ x z t) (qs.ket b) =
      c.factor φ (extToInt x b) (extToInt z b) b • qs.ket b := by
  set a := t - x.width
  set d := t - z.width
  set b1 := signExtendBasis x a b with hb1
  set b2 := signExtendBasis z d b1 with hb2
  simp only [topGate, QSemantics.eval_seq]
  rw [ExtensionSemantics.eval_signExtend_ket_total, ExtensionSemantics.eval_signExtend_ket_total,
    Ctl.eval_gate_ket, QSemantics.eval_smul, ExtensionSemantics.eval_signDealloc_ket_total,
    QSemantics.eval_smul, ExtensionSemantics.eval_signDealloc_ket_total]
  rw [show signDeallocBasis z d (signExtendBasis z d b1) = b1 from signExtendBasis_involutive z d b1,
    show signDeallocBasis x a b1 = b from signExtendBasis_involutive x a b]
  congr 1
  have hx : extToInt (x.grow a) b2 = extToInt x b := by
    rw [hb2, extToInt_signExtendBasis_of_disj z d _
      (disj_of_owned hd (grow_active_sub_owned x a) (newBits_sub_owned z d))]
    exact extToInt_grow_signExtendBasis x a b (by simpa [ExtReg.CanGrow] using hxcap)
      (fresh_of_zero _ _ _ hb.1)
  have hz1 : extToInt z b1 = extToInt z b :=
    extToInt_signExtendBasis_of_disj x a z
      (disj_of_owned' hd (active_sub_owned z) (newBits_sub_owned x a)) b
  have hz : extToInt (z.grow d) b2 = extToInt z b := by
    rw [hb2, extToInt_grow_signExtendBasis z d b1 (by simpa [ExtReg.CanGrow] using hzcap)
      (fresh_of_zero _ _ _ (Clean.signExtend_x hd hb a)), hz1]
  have hon : c.on b2 = c.on b := by
    rw [hb2, ctl_on_signExtendBasis c z d (fun q hq hmem => by subst hq; exact hc.2 hmem) b1,
      hb1, ctl_on_signExtendBasis c x a (fun q hq hmem => by subst hq; exact hc.1 hmem) b]
  unfold Ctl.factor
  rw [hx, hz, hon]

/-! ## The whole split -/

/-- **Correctness of the balanced phase product on basis states.** For every plan
passing `fitsB`, on a basis state with clean reserves, the balanced split of
`x` against `z` applies `φ · x · z` (signed) when the kind fires, and returns
the basis state. -/
theorem splitGate_ket (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (P : ShorLoweringPolicy) (c : Ctl) :
    ∀ (bs : List Block) (φ : Angle) (t : ℕ) (x z : ExtReg) (b : qs.Basis),
      fitsB P bs t x z = true → ExtReg.OwnedDisjoint x z → c.Away x z → Clean x z b →
      qs.eval (splitGate c φ bs t x z) (qs.ket b) =
        c.factor φ (extToInt x b) (extToInt z b) b • qs.ket b
  | [], φ, t, x, z, b, hfit, hd, hc, hb => by
      obtain ⟨_, _, hx, hz⟩ := fitsB_nil.mp hfit
      exact topGate_ket qs c φ x z t b (by omega) (by omega) hd hc hb
  | blk :: bs, φ, t, x, z, b, hfit, hd, hc, hb => by
      obtain ⟨hw, ht, _, hx, hz, hrest⟩ := fitsB_cons.mp hfit
      have hd' : ExtReg.OwnedDisjoint (highPart x blk.w) z :=
        ownedDisjoint_mono hd (highPart_owned_sub x blk.w) (fun _ h => h)
      have hc' : c.Away (highPart x blk.w) z := ctlAway_mono hc (highPart_owned_sub x blk.w) (fun _ h => h)
      have hb' : Clean (highPart x blk.w) z b := hb
      simp only [splitGate, QSemantics.eval_seq]
      rw [lowGate_ket qs c φ x z blk.w blk.t b (by omega) ht (by omega) (by omega) hd hc hb,
        QSemantics.eval_smul,
        splitGate_ket qs P c bs (φ * 2 ^ blk.w) t (highPart x blk.w) z b hrest hd' hc' hb', smul_smul]
      congr 1
      rw [extToInt_split x blk.w hw b]
      unfold Ctl.factor
      by_cases hon : c.on b = true
      · simp only [hon, ite_true]
        exact phaseFactor_add φ blk.w _ _ _
      · simp [hon]

end Balanced
end Shor
