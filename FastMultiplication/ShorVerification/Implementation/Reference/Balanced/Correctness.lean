import FastMultiplication.ShorVerification.Implementation.Reference.Balanced.Semantics
import FastMultiplication.ShorVerification.Implementation.Shor.Main

/-!
# Balanced phase products: workspace, cleanliness, and lowering correctness

* `splitGate_ok` (layout/allocation): every block product of a plan that passes
  `fitsB` gets ForShor's static workspace predicate (`Policy.WorkspaceOK`, or
  `Policy.CWorkspaceOK` for a controlled site): the block registers are
  owned-disjoint and the existing reserves cover the extension bits plus
  `Policy.reserveNeed` at the block width. So `balance` never needs more
  static workspace than the source circuit (`balance_ok`).
* `splitGate_clean` (workspace cleanliness): from clean reserves before the
  site, every block product's reserves are clean when it runs under the real
  lowering — ForShor's dynamic precondition `Policy.GateWorkspaceCleanState`.
* `balance_correct`: the pass preserves both preconditions and the semantics on
  every state satisfying the source circuit's preconditions, so
* `Policy.lowerGate_balance_correctness`: lowering the balanced circuit with
  ForShor's own `Policy.lowerGate` implements the *source* circuit, under the
  source circuit's own preconditions.
-/

namespace Shor
namespace Balanced

open Gate

universe u

variable (qs : QSemantics) [RegEncoding qs.Basis]

/-! ## Linear closure helpers -/

theorem closure_map [GateSemanticsCore qs] (U : Gate) {Q Q' : qs.Basis → Prop}
    (hU : ∀ b, Q b → ∃ (s : ℂ) (b' : qs.Basis), qs.eval U (qs.ket b) = s • qs.ket b' ∧ Q' b')
    {ψ : qs.State} (h : CleanClosure Q ψ) : CleanClosure Q' (qs.eval U ψ) := by
  induction h with
  | zero => rw [QSemantics.eval_zero]; exact CleanClosure.zero
  | ket b hb =>
      obtain ⟨s, b', he, hb'⟩ := hU b hb
      rw [he]; exact CleanClosure.smul s (CleanClosure.ket b' hb')
  | add _ _ ih1 ih2 => rw [QSemantics.eval_add]; exact CleanClosure.add ih1 ih2
  | smul a _ ih => rw [QSemantics.eval_smul]; exact CleanClosure.smul a ih

theorem closure_mono {Q Q' : qs.Basis → Prop} (hQ : ∀ b, Q b → Q' b) {ψ : qs.State}
    (h : CleanClosure Q ψ) : CleanClosure Q' ψ := by
  induction h with
  | zero => exact CleanClosure.zero
  | ket b hb => exact CleanClosure.ket b (hQ b hb)
  | add _ _ ih1 ih2 => exact CleanClosure.add ih1 ih2
  | smul a _ ih => exact CleanClosure.smul a ih

theorem eval_eq_on_closure [GateSemanticsCore qs] (U V : Gate) {Q : qs.Basis → Prop}
    (hUV : ∀ b, Q b → qs.eval U (qs.ket b) = qs.eval V (qs.ket b))
    {ψ : qs.State} (h : CleanClosure Q ψ) : qs.eval U ψ = qs.eval V ψ := by
  induction h with
  | zero => rw [QSemantics.eval_zero, QSemantics.eval_zero]
  | ket b hb => exact hUV b hb
  | add _ _ ih1 ih2 => rw [QSemantics.eval_add, QSemantics.eval_add, ih1, ih2]
  | smul a _ ih => rw [QSemantics.eval_smul, QSemantics.eval_smul, ih]

/-! ## Static workspace (layout / allocation) -/

/-- ForShor's static predicate for a product of kind `c`. -/
def Ctl.OK (P : ShorLoweringPolicy) : Ctl → ExtReg → ExtReg → Prop
  | .none, x, z => Policy.WorkspaceOK P x z
  | .ctrl q, x, z => Policy.CWorkspaceOK P q x z

theorem Ctl.gateOK {P : ShorLoweringPolicy} {c : Ctl} {φ : Angle} {x z : ExtReg} (h : c.OK P x z) :
    Policy.GateWorkspaceOK P (c.gate φ x z) := by
  cases c <;> exact h

theorem Ctl.OK.disjoint {P : ShorLoweringPolicy} {c : Ctl} {x z : ExtReg} (h : c.OK P x z) :
    ExtReg.OwnedDisjoint x z := by
  cases c with
  | none => exact h.owned_disjoint
  | ctrl q => exact h.owned_disjoint

theorem Ctl.OK.away {P : ShorLoweringPolicy} {c : Ctl} {x z : ExtReg} (h : c.OK P x z) : c.Away x z := by
  cases c with
  | none => trivial
  | ctrl q => exact h.control_disjoint

theorem Ctl.Away.swap {c : Ctl} {x z : ExtReg} (h : c.Away x z) : c.Away z x := by
  cases c with
  | none => trivial
  | ctrl q => exact ⟨h.2, h.1⟩

theorem ownedDisjoint_swap {x z : ExtReg} (h : ExtReg.OwnedDisjoint x z) : ExtReg.OwnedDisjoint z x :=
  List.Disjoint.symm h

/-- One block product's static workspace, from the fit numbers. -/
theorem blockOK {P : ShorLoweringPolicy} {c : Ctl} {x z X : ExtReg} (a d t : ℕ)
    (hX : X.ownedQubits ⊆ x.ownedQubits)
    (hXw : X.width + a = t) (hzw : z.width + d = t)
    (hxa : a + (Policy.reserveNeed P t t).1 ≤ X.capacity)
    (hzd : d + (Policy.reserveNeed P t t).2 ≤ z.capacity)
    (hd : ExtReg.OwnedDisjoint x z) (hc : c.Away x z) :
    c.OK P (X.grow a) (z.grow d) := by
  have hXa : X.CanGrow a := by unfold ExtReg.CanGrow; omega
  have hzd' : z.CanGrow d := by unfold ExtReg.CanGrow; omega
  have base : Policy.WorkspaceOK P (X.grow a) (z.grow d) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow, Gate.ExtReg.ownedQubits_grow]
      exact ownedDisjoint_mono hd hX (fun _ h => h)
    · rw [ExtReg.width_grow X a hXa, ExtReg.width_grow z d hzd', hXw, hzw,
        ExtReg.capacity_grow X a hXa]
      omega
    · rw [ExtReg.width_grow X a hXa, ExtReg.width_grow z d hzd', hXw, hzw,
        ExtReg.capacity_grow z d hzd']
      omega
  cases c with
  | none => exact base
  | ctrl q =>
      refine ⟨base, ?_, ?_⟩
      · rw [Gate.ExtReg.ownedQubits_grow]; exact fun h => hc.1 (hX h)
      · rw [Gate.ExtReg.ownedQubits_grow]; exact hc.2

theorem lowGate_ok {P : ShorLoweringPolicy} {c : Ctl} {φ : Angle} {x z : ExtReg} {w t : ℕ}
    (hw : w < x.width) (ht : w + 1 ≤ t) (hzt : z.width ≤ t)
    (hx : (t - w) + (Policy.reserveNeed P t t).1 ≤ x.capacity)
    (hz : (t - z.width) + (Policy.reserveNeed P t t).2 ≤ z.capacity)
    (hd : ExtReg.OwnedDisjoint x z) (hc : c.Away x z) :
    Policy.GateWorkspaceOK P (lowGate c φ x z w t) := by
  refine ⟨trivial, trivial, Ctl.gateOK ?_, trivial, trivial⟩
  exact blockOK (t - w) (t - z.width) t (lowBlock_owned_sub x w)
    (by rw [lowBlock_width x w (by omega)]; omega) (by omega) (by simpa using hx) hz hd hc

theorem topGate_ok {P : ShorLoweringPolicy} {c : Ctl} {φ : Angle} {x z : ExtReg} {t : ℕ}
    (hxt : x.width ≤ t) (hzt : z.width ≤ t)
    (hx : (t - x.width) + (Policy.reserveNeed P t t).1 ≤ x.capacity)
    (hz : (t - z.width) + (Policy.reserveNeed P t t).2 ≤ z.capacity)
    (hd : ExtReg.OwnedDisjoint x z) (hc : c.Away x z) :
    Policy.GateWorkspaceOK P (topGate c φ x z t) := by
  refine ⟨trivial, trivial, Ctl.gateOK ?_, trivial, trivial⟩
  exact blockOK (t - x.width) (t - z.width) t (fun _ h => h) (by omega) (by omega) hx hz hd hc

/-- **Layout/allocation of the balanced split.** -/
theorem splitGate_ok (P : ShorLoweringPolicy) (c : Ctl) :
    ∀ (bs : List Block) (φ : Angle) (t : ℕ) (x z : ExtReg),
      fitsB P bs t x z = true → ExtReg.OwnedDisjoint x z → c.Away x z →
      Policy.GateWorkspaceOK P (splitGate c φ bs t x z)
  | [], φ, t, x, z, hfit, hd, hc => by
      obtain ⟨h1, h2, h3, h4⟩ := fitsB_nil.mp hfit
      exact topGate_ok h1 h2 h3 h4 hd hc
  | blk :: bs, φ, t, x, z, hfit, hd, hc => by
      obtain ⟨hw, ht, hzt, hx, hz, hrest⟩ := fitsB_cons.mp hfit
      exact ⟨lowGate_ok hw ht hzt hx hz hd hc,
        splitGate_ok P c bs _ t _ z hrest
          (ownedDisjoint_mono hd (highPart_owned_sub x blk.w) (fun _ h => h))
          (ctlAway_mono hc (highPart_owned_sub x blk.w) (fun _ h => h))⟩

theorem siteGate_ok (P : ShorLoweringPolicy) (R : Rule) (c : Ctl) (φ : Angle) (x z : ExtReg)
    (h : c.OK P x z) : Policy.GateWorkspaceOK P (siteGate P R c φ x z) := by
  unfold siteGate
  split_ifs with h1 h2
  · split
    · split_ifs with hf
      · exact splitGate_ok P c _ φ _ x z hf h.disjoint h.away
      · exact Ctl.gateOK h
    · exact Ctl.gateOK h
  · split
    · split_ifs with hf
      · exact splitGate_ok P c _ φ _ z x hf (ownedDisjoint_swap h.disjoint) h.away.swap
      · exact Ctl.gateOK h
    · exact Ctl.gateOK h
  · exact Ctl.gateOK h

/-- `balance` needs no more static workspace than its source. -/
theorem balance_ok (P : ShorLoweringPolicy) (R : Rule) :
    ∀ (G : Gate), Policy.GateWorkspaceOK P G → Policy.GateWorkspaceOK P (balance P R G)
  | .seq U V, h => ⟨balance_ok P R U h.1, balance_ok P R V h.2⟩
  | .adj U, h => balance_ok P R U h
  | .SignedPhaseProd φ x z, h => siteGate_ok P R .none φ x z h
  | .CSignedPhaseProd q φ x z, h => siteGate_ok P R (.ctrl q) φ x z h
  | .id, h | .H _, h | .X _, h | .CNOT _ _, h | .Toffoli _ _ _, h | .QFT _, h
  | .RadixReverse _ _, h | .CmpGeConst _ _ _ _, h | .CSubConst _ _ _ _, h | .ShiftL _ _, h
  | .ShiftR _ _, h | .Negate _, h | .AddScaled _ _ _ _, h | .zeroExtend _ _, h
  | .signExtend _ _, h | .zeroDealloc _ _, h | .signDealloc _ _, h
  | .idealCtrlModMul _ _ _ _, h => h

/-! ## Dynamic cleanliness under the real lowering -/

theorem recClean_of_clean {X Z : ExtReg} {b : qs.Basis} (h : Clean X Z b) :
    RecursiveWorkspaceCleanBasis X Z b :=
  ⟨fresh_of_zero _ _ _ h.1, fresh_of_zero _ _ _ h.2⟩

theorem clean_of_recClean {X Z : ExtReg} {b : qs.Basis} (h : RecursiveWorkspaceCleanBasis X Z b) :
    Clean X Z b :=
  ⟨zero_of_fresh_capacity _ _ h.1, zero_of_fresh_capacity _ _ h.2⟩

theorem clean_swap {X Z : ExtReg} {b : qs.Basis} (h : Clean X Z b) : Clean Z X b := ⟨h.2, h.1⟩

/-- Growing without touching the state keeps the remaining reserve clean. -/
theorem clean_grow {X Z : ExtReg} {b : qs.Basis} (a : ℕ) (h : Clean X Z b) : Clean (X.grow a) Z b :=
  ⟨toNat_drop_zero _ _ _ h.1, h.2⟩

/-- After sign-extending `Z`, both remaining reserves are still clean. -/
theorem clean_after_signExtend_right {X Z : ExtReg} {b : qs.Basis} (d : ℕ) (h : Clean X Z b)
    (hX : Disjoint X.reserve (Z.newBits d)) :
    Clean X (Z.grow d) (signExtendBasis Z d b) := by
  refine ⟨?_, ?_⟩
  · rw [toNat_signExtendBasis_of_disj Z d _ hX]; exact h.1
  · have hdis : Disjoint (Z.grow d).reserve (Z.newBits d) := by
      unfold Disjoint
      exact (List.disjoint_take_drop Z.reserve.nodup (le_refl d)).symm
    rw [toNat_signExtendBasis_of_disj Z d _ hdis]
    exact toNat_drop_zero _ _ _ h.2

/-- After sign-extending `X`, both remaining reserves are still clean. -/
theorem clean_after_signExtend_left {X Z : ExtReg} {b : qs.Basis} (a : ℕ) (h : Clean X Z b)
    (hZ : Disjoint Z.reserve (X.newBits a)) :
    Clean (X.grow a) Z (signExtendBasis X a b) :=
  clean_swap qs (clean_after_signExtend_right qs a (clean_swap qs h) hZ)

section Clean
variable [GateSemanticsFacts qs] [LowerGateClass qs]

theorem clean_seq {P : ShorLoweringPolicy} (hP : P.Admissible) {U V : Gate}
    (hw : Policy.GateWorkspaceOK P (U ;; V)) {ψ : qs.State}
    (hU : Policy.GateWorkspaceCleanState qs P U hw.1 ψ)
    (hV : Policy.GateWorkspaceCleanState qs P V hw.2 (qs.eval U ψ)) :
    Policy.GateWorkspaceCleanState qs P (U ;; V) hw ψ := by
  refine ⟨hU, ?_⟩
  rw [Policy.lowerGate_correctness qs P hP U hw.1 ψ hU]
  exact hV

theorem Ctl.clean_gate {P : ShorLoweringPolicy} {c : Ctl} {φ : Angle} {x z : ExtReg}
    (hw : Policy.GateWorkspaceOK P (c.gate φ x z)) {ψ : qs.State}
    (h : RecursiveWorkspaceCleanState qs x z ψ) :
    Policy.GateWorkspaceCleanState qs P (c.gate φ x z) hw ψ := by
  cases c <;> exact h

theorem Ctl.clean_gate_iff {P : ShorLoweringPolicy} {c : Ctl} {φ : Angle} {x z : ExtReg}
    (hw : Policy.GateWorkspaceOK P (c.gate φ x z)) {ψ : qs.State} :
    Policy.GateWorkspaceCleanState qs P (c.gate φ x z) hw ψ ↔ RecursiveWorkspaceCleanState qs x z ψ := by
  cases c <;> exact Iff.rfl

theorem lowGate_clean {P : ShorLoweringPolicy} (hP : P.Admissible) {c : Ctl} {φ : Angle}
    {x z : ExtReg} {w t : ℕ} (hd : ExtReg.OwnedDisjoint x z)
    (hw : Policy.GateWorkspaceOK P (lowGate c φ x z w t)) {ψ : qs.State}
    (hψ : CleanClosure (Clean x z) ψ) :
    Policy.GateWorkspaceCleanState qs P (lowGate c φ x z w t) hw ψ := by
  unfold lowGate at hw ⊢
  apply clean_seq qs hP hw trivial
  rw [ExtensionSemantics.eval_zeroExtend]
  apply clean_seq qs hP hw.2 trivial
  apply clean_seq qs hP hw.2.2 _ ⟨trivial, trivial⟩
  rw [Ctl.clean_gate_iff qs]
  refine closure_map qs _ (Q := Clean x z) ?_ hψ
  intro b hb
  refine ⟨1, signExtendBasis z (t - z.width) b, ?_, ?_⟩
  · rw [ExtensionSemantics.eval_signExtend_ket_total, one_smul]
  · apply recClean_of_clean
    apply clean_after_signExtend_right qs _ (clean_grow qs _ hb)
    exact disj_of_owned hd (fun q hq => lowBlock_owned_sub x w
      (reserve_sub_owned _ (grow_reserve_sub_reserve _ _ hq))) (newBits_sub_owned z _)

theorem topGate_clean {P : ShorLoweringPolicy} (hP : P.Admissible) {c : Ctl} {φ : Angle}
    {x z : ExtReg} {t : ℕ} (hd : ExtReg.OwnedDisjoint x z)
    (hw : Policy.GateWorkspaceOK P (topGate c φ x z t)) {ψ : qs.State}
    (hψ : CleanClosure (Clean x z) ψ) :
    Policy.GateWorkspaceCleanState qs P (topGate c φ x z t) hw ψ := by
  unfold topGate at hw ⊢
  apply clean_seq qs hP hw trivial
  apply clean_seq qs hP hw.2 trivial
  apply clean_seq qs hP hw.2.2 _ ⟨trivial, trivial⟩
  rw [Ctl.clean_gate_iff qs]
  have h1 : CleanClosure (Clean (x.grow (t - x.width)) z)
      (qs.eval (Gate.signExtend x (t - x.width)) ψ) := by
    refine closure_map qs _ (Q := Clean x z) ?_ hψ
    intro b hb
    refine ⟨1, signExtendBasis x (t - x.width) b, ?_, ?_⟩
    · rw [ExtensionSemantics.eval_signExtend_ket_total, one_smul]
    · exact clean_after_signExtend_left qs _ hb
        (disj_of_owned' hd (reserve_sub_owned z) (newBits_sub_owned x _))
  refine closure_map qs _ (Q := Clean (x.grow (t - x.width)) z) ?_ h1
  intro b hb
  refine ⟨1, signExtendBasis z (t - z.width) b, ?_, ?_⟩
  · rw [ExtensionSemantics.eval_signExtend_ket_total, one_smul]
  · apply recClean_of_clean
    apply clean_after_signExtend_right qs _ hb
    exact disj_of_owned hd (fun q hq => reserve_sub_owned x (grow_reserve_sub_reserve _ _ hq))
      (newBits_sub_owned z _)

/-- **Workspace cleanliness of the balanced split** under ForShor's lowering. -/
theorem splitGate_clean {P : ShorLoweringPolicy} (hP : P.Admissible) (c : Ctl) :
    ∀ (bs : List Block) (φ : Angle) (t : ℕ) (x z : ExtReg),
      fitsB P bs t x z = true → ExtReg.OwnedDisjoint x z → c.Away x z →
      ∀ (hw : Policy.GateWorkspaceOK P (splitGate c φ bs t x z)) (ψ : qs.State),
        CleanClosure (Clean x z) ψ →
        Policy.GateWorkspaceCleanState qs P (splitGate c φ bs t x z) hw ψ
  | [], φ, t, x, z, _, hd, _, hw, ψ, hψ => topGate_clean qs hP hd hw hψ
  | blk :: bs, φ, t, x, z, hfit, hd, hc, hw, ψ, hψ => by
      obtain ⟨hwid, ht, _, hx, hz, hrest⟩ := fitsB_cons.mp hfit
      have hd' : ExtReg.OwnedDisjoint (highPart x blk.w) z :=
        ownedDisjoint_mono hd (highPart_owned_sub x blk.w) (fun _ h => h)
      have hc' : c.Away (highPart x blk.w) z := ctlAway_mono hc (highPart_owned_sub x blk.w) (fun _ h => h)
      apply clean_seq qs hP hw (lowGate_clean qs hP hd hw.1 hψ)
      apply splitGate_clean hP c bs _ t _ z hrest hd' hc' hw.2
      refine closure_map qs _ (Q := Clean x z) ?_ hψ
      intro b hb
      exact ⟨_, b, lowGate_ket qs c φ x z blk.w blk.t b (by omega) ht (by omega) (by omega) hd hc hb, hb⟩

/-! ## The site and the pass -/

omit [LowerGateClass qs] in
theorem splitGate_eval {P : ShorLoweringPolicy} {c : Ctl} {φ : Angle} {bs : List Block} {t : ℕ}
    {x z : ExtReg} (hfit : fitsB P bs t x z = true) (hd : ExtReg.OwnedDisjoint x z) (hc : c.Away x z)
    {ψ : qs.State} (hψ : CleanClosure (Clean x z) ψ) :
    qs.eval (splitGate c φ bs t x z) ψ = qs.eval (c.gate φ x z) ψ :=
  eval_eq_on_closure qs _ _ (fun b hb => by
    rw [splitGate_ket qs P c bs φ t x z b hfit hd hc hb, Ctl.eval_gate_ket]) hψ

omit [LowerGateClass qs] in
theorem splitGate_eval_swap {P : ShorLoweringPolicy} {c : Ctl} {φ : Angle} {bs : List Block} {t : ℕ}
    {x z : ExtReg} (hfit : fitsB P bs t z x = true) (hd : ExtReg.OwnedDisjoint z x) (hc : c.Away z x)
    {ψ : qs.State} (hψ : CleanClosure (Clean z x) ψ) :
    qs.eval (splitGate c φ bs t z x) ψ = qs.eval (c.gate φ x z) ψ :=
  eval_eq_on_closure qs _ _ (fun b hb => by
    rw [splitGate_ket qs P c bs φ t z x b hfit hd hc hb, Ctl.eval_gate_ket]
    unfold Ctl.factor; rw [phaseFactor_comm]) hψ

/-- One site: the balanced site is clean-ready and equal to the source site. -/
theorem siteGate_correct {P : ShorLoweringPolicy} (hP : P.Admissible) (R : Rule) (c : Ctl)
    (φ : Angle) (x z : ExtReg) (hok : c.OK P x z) (ψ : qs.State)
    (hψ : RecursiveWorkspaceCleanState qs x z ψ) :
    Policy.GateWorkspaceCleanState qs P (siteGate P R c φ x z) (siteGate_ok P R c φ x z hok) ψ ∧
      qs.eval (siteGate P R c φ x z) ψ = qs.eval (c.gate φ x z) ψ := by
  have hcl : CleanClosure (Clean x z) ψ := closure_mono qs (fun b hb => clean_of_recClean qs hb) hψ
  have hcl' : CleanClosure (Clean z x) ψ := closure_mono qs (fun b hb => clean_swap qs hb) hcl
  suffices H : ∀ (G' : Gate), siteGate P R c φ x z = G' → ∀ (hw : Policy.GateWorkspaceOK P G'),
      Policy.GateWorkspaceCleanState qs P G' hw ψ ∧ qs.eval G' ψ = qs.eval (c.gate φ x z) ψ from
    H _ rfl _
  intro G' hG hw
  unfold siteGate at hG
  split_ifs at hG with h1 h2
  · split at hG
    · split_ifs at hG with hf
      · subst hG
        exact ⟨splitGate_clean qs hP c _ φ _ x z hf hok.disjoint hok.away hw ψ hcl,
          splitGate_eval qs hf hok.disjoint hok.away hcl⟩
      · subst hG; exact ⟨Ctl.clean_gate qs hw hψ, rfl⟩
    · subst hG; exact ⟨Ctl.clean_gate qs hw hψ, rfl⟩
  · split at hG
    · split_ifs at hG with hf
      · subst hG
        exact ⟨splitGate_clean qs hP c _ φ _ z x hf (ownedDisjoint_swap hok.disjoint) hok.away.swap hw ψ hcl',
          splitGate_eval_swap qs hf (ownedDisjoint_swap hok.disjoint) hok.away.swap hcl'⟩
      · subst hG; exact ⟨Ctl.clean_gate qs hw hψ, rfl⟩
    · subst hG; exact ⟨Ctl.clean_gate qs hw hψ, rfl⟩
  · subst hG; exact ⟨Ctl.clean_gate qs hw hψ, rfl⟩

/-- **The pass preserves the lowering preconditions and the semantics.** On every
state that satisfies the source circuit's own dynamic precondition, the balanced
circuit satisfies its dynamic precondition and has the same action. -/
theorem balance_correct {P : ShorLoweringPolicy} (hP : P.Admissible) (R : Rule) :
    ∀ (G : Gate) (hw : Policy.GateWorkspaceOK P G) (ψ : qs.State),
      Policy.GateWorkspaceCleanState qs P G hw ψ →
      Policy.GateWorkspaceCleanState qs P (balance P R G) (balance_ok P R G hw) ψ ∧
        qs.eval (balance P R G) ψ = qs.eval G ψ := by
  intro G
  induction G with
  | seq U V ihU ihV =>
      intro hw ψ hclean
      obtain ⟨cU, cV⟩ := hclean
      obtain ⟨cbU, eU⟩ := ihU hw.1 ψ cU
      have hLU : LowerGateClass.evalL (qs := qs) (Policy.lowerGate P U hw.1) ψ = qs.eval U ψ :=
        Policy.lowerGate_correctness qs P hP U hw.1 ψ cU
      have hLbU : LowerGateClass.evalL (qs := qs)
          (Policy.lowerGate P (balance P R U) (balance_ok P R U hw.1)) ψ = qs.eval U ψ := by
        rw [Policy.lowerGate_correctness qs P hP _ _ ψ cbU, eU]
      rw [hLU] at cV
      obtain ⟨cbV, eV⟩ := ihV hw.2 (qs.eval U ψ) cV
      refine ⟨⟨cbU, ?_⟩, ?_⟩
      · change Policy.GateWorkspaceCleanState qs P (balance P R V) (balance_ok P R V hw.2)
          (LowerGateClass.evalL (qs := qs)
            (Policy.lowerGate P (balance P R U) (balance_ok P R U hw.1)) ψ)
        rw [hLbU]; exact cbV
      · change qs.eval (balance P R U ;; balance P R V) ψ = qs.eval (U ;; V) ψ
        rw [QSemantics.eval_seq, QSemantics.eval_seq, eU, eV]
  | adj U ih =>
      intro hw ψ hclean
      obtain ⟨cb, e⟩ := ih hw (qs.eval (Gate.adj U) ψ) hclean
      have hfwd : qs.eval (balance P R U) (qs.eval (Gate.adj U) ψ) = ψ := by
        rw [e, QSemantics.eval_apply_adj]
      have hback : qs.eval (Gate.adj (balance P R U)) ψ = qs.eval (Gate.adj U) ψ := by
        conv_lhs => rw [← hfwd]
        rw [QSemantics.eval_adj_apply]
      refine ⟨?_, hback⟩
      change Policy.GateWorkspaceCleanState qs P (balance P R U) (balance_ok P R U hw)
        (qs.eval (Gate.adj (balance P R U)) ψ)
      rw [hback]; exact cb
  | SignedPhaseProd φ x z =>
      intro hw ψ hclean
      exact siteGate_correct qs hP R .none φ x z hw ψ hclean
  | CSignedPhaseProd q φ x z =>
      intro hw ψ hclean
      exact siteGate_correct qs hP R (.ctrl q) φ x z hw ψ hclean
  | id | H _ | X _ | CNOT _ _ | Toffoli _ _ _ | QFT _ | RadixReverse _ _ | CmpGeConst _ _ _ _
  | CSubConst _ _ _ _ | ShiftL _ _ | ShiftR _ _ | Negate _ | AddScaled _ _ _ _ | zeroExtend _ _
  | signExtend _ _ | zeroDealloc _ _ | signDealloc _ _ | idealCtrlModMul _ _ _ _ =>
      intro hw ψ hclean
      exact ⟨hclean, rfl⟩

/-- **End-to-end lowering with the balanced split.** ForShor's `Policy.lowerGate`,
run on the balanced circuit, implements the source circuit under the source
circuit's own static and dynamic preconditions. -/
theorem Policy.lowerGate_balance_correctness (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule)
    (G : Gate) (hw : Policy.GateWorkspaceOK P G) (ψ : qs.State)
    (hclean : Policy.GateWorkspaceCleanState qs P G hw ψ) :
    LowerGateClass.evalL (qs := qs) (Policy.lowerGate P (balance P R G) (balance_ok P R G hw)) ψ =
      qs.eval G ψ := by
  obtain ⟨cb, e⟩ := balance_correct qs hP R G hw ψ hclean
  rw [Policy.lowerGate_correctness qs P hP _ _ ψ cb, e]

end Clean

end Balanced
end Shor
