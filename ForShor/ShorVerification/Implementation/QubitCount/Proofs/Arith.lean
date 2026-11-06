import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Budgets
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.ExactWidth

/-!
# Qubit count: the budgets by arithmetic

The budgets of `Statement.lean` equal those of `Budgets.lean`. The width map
of a table evaluates to the compiler's width scan, because every table
operation acts on the slot widths by `+ c`, `max`, and `max (· - n) 0`; the
qubits a level activates on one side are `k · W - w`, because the `k` chunks
partition the operand; and the QFT's halving tree holds only `⌊n / 2^j⌋` and
`⌈n / 2^j⌉` at depth `j`.
-/

namespace Shor
namespace QubitCount

open RecursivePhaseWorkspace

/-! ## Suprema over `Fin k` -/

/-- The largest value of `f` over `Fin k`. -/
def supFin : (k : ℕ) → (Fin k → ℕ) → ℕ
  | 0, _ => 0
  | k + 1, f => max (f 0) (supFin k fun i => f i.succ)

lemma le_supFin : ∀ (k : ℕ) (f : Fin k → ℕ) (i : Fin k), f i ≤ supFin k f
  | 0, _, i => i.elim0
  | k + 1, f, i => by
      rw [supFin]
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_max_left _ _
      · exact le_trans (le_supFin k (fun i => f i.succ) j) (le_max_right _ _)

lemma supFin_le : ∀ (k : ℕ) (f : Fin k → ℕ) (b : ℕ), (∀ i, f i ≤ b) → supFin k f ≤ b
  | 0, _, _, _ => Nat.zero_le _
  | k + 1, f, b, h => by
      rw [supFin]
      exact max_le (h 0) (supFin_le k _ b fun j => h j.succ)

lemma supFin_eq_sup (k : ℕ) (f : Fin k → ℕ) : supFin k f = Finset.univ.sup f :=
  le_antisymm (supFin_le k f _ fun i => Finset.le_sup (Finset.mem_univ i))
    (Finset.sup_le fun i _ => le_supFin k f i)

/-- `((n : ℤ) : WithBot ℤ)`. -/
abbrev wb (n : ℕ) : WithBot ℤ := ((n : ℤ) : WithBot ℤ)

lemma wb_sup_add (a b c : WithBot ℤ) : (a ⊔ b) + c = (a + c) ⊔ (b + c) := by
  induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe <;>
    induction c using WithBot.recBotCoe <;> simp [← WithBot.coe_add, ← WithBot.coe_sup]

lemma supBot_add : ∀ (k : ℕ) (f : Fin k → WithBot ℤ) (c : WithBot ℤ),
    supBot k (fun i => f i + c) = supBot k f + c
  | 0, _, c => by simp [supBot]
  | k + 1, f, c => by
      simp only [supBot]
      rw [supBot_add k (fun i => f i.succ) c, wb_sup_add]

lemma supBot_sup : ∀ (k : ℕ) (f g : Fin k → WithBot ℤ),
    supBot k (fun i => f i ⊔ g i) = supBot k f ⊔ supBot k g
  | 0, _, _ => by simp [supBot]
  | k + 1, f, g => by
      simp only [supBot]
      rw [supBot_sup k (fun i => f i.succ) (fun i => g i.succ), sup_sup_sup_comm]

lemma supBot_bot : ∀ (k : ℕ) (f : Fin k → WithBot ℤ), (∀ i, f i = ⊥) → supBot k f = ⊥
  | 0, _, _ => rfl
  | k + 1, f, h => by
      simp only [supBot]
      rw [h 0, supBot_bot k _ (fun i => h i.succ), bot_sup_eq]

lemma supBot_single : ∀ (k : ℕ) (f : Fin k → WithBot ℤ) (s : Fin k),
    (∀ t, t ≠ s → f t = ⊥) → supBot k f = f s
  | 0, _, s, _ => s.elim0
  | k + 1, f, s, h => by
      simp only [supBot]
      cases s using Fin.cases with
      | zero =>
          rw [supBot_bot k _ (fun i => h _ (Fin.succ_ne_zero i)), sup_bot_eq]
      | succ j =>
          rw [h 0 (Fin.succ_ne_zero j).symm, bot_sup_eq]
          exact supBot_single k _ j fun t ht => h _ fun e => ht (Fin.succ_inj.mp e)

lemma botToNat_sup_wb (a : ℕ) (x : WithBot ℤ) : botToNat (wb a ⊔ x) = max a (botToNat x) := by
  induction x using WithBot.recBotCoe with
  | bot => simp [botToNat]
  | coe z =>
      rw [← WithBot.coe_sup]
      simp only [botToNat, WithBot.unbotD_coe]
      omega

lemma supFin_eq_botToNat : ∀ (k : ℕ) (f : Fin k → ℕ),
    supFin k f = botToNat (supBot k fun i => wb (f i))
  | 0, _ => by simp [supFin, supBot, botToNat]
  | k + 1, f => by
      simp only [supFin, supBot]
      rw [supFin_eq_botToNat k (fun i => f i.succ), botToNat_sup_wb]

/-! ## The width map evaluates to the width scan -/

variable {k : ℕ}

lemma evalVar (s : Fin k) (init : Fin k → ℕ) : (WidthTerm.var s).eval init = wb (init s) := by
  unfold WidthTerm.eval WidthTerm.var
  simp only
  rw [supBot_single k _ s]
  · simp
  · intro t ht
    simp [ht]

lemma evalAdd (e : WidthTerm k) (c : ℤ) (init : Fin k → ℕ) :
    (e.add c).eval init = e.eval init + (c : WithBot ℤ) := by
  unfold WidthTerm.eval WidthTerm.add
  simp only
  rw [show (fun s => e.coef s + (c : WithBot ℤ) + wb (init s))
      = fun s => (e.coef s + wb (init s)) + (c : WithBot ℤ) from funext fun s => add_right_comm _ _ _,
    supBot_add, wb_sup_add]

lemma evalSup (e f : WidthTerm k) (init : Fin k → ℕ) :
    (e.sup f).eval init = e.eval init ⊔ f.eval init := by
  unfold WidthTerm.eval WidthTerm.sup
  simp only
  rw [show (fun s => (e.coef s ⊔ f.coef s) + wb (init s))
      = fun s => (e.coef s + wb (init s)) ⊔ (f.coef s + wb (init s)) from
      funext fun s => wb_sup_add _ _ _, supBot_sup, sup_sup_sup_comm]

lemma evalTrunc (e : WidthTerm k) (n : ℕ) (init : Fin k → ℕ) :
    (e.trunc n).eval init = (e.eval init + ((-(n : ℤ) : ℤ) : WithBot ℤ)) ⊔ ((0 : ℤ) : WithBot ℤ) := by
  unfold WidthTerm.eval WidthTerm.trunc
  simp only
  rw [show (fun s => e.coef s + ((-(n : ℤ) : ℤ) : WithBot ℤ) + wb (init s))
      = fun s => (e.coef s + wb (init s)) + ((-(n : ℤ) : ℤ) : WithBot ℤ) from
      funext fun s => add_right_comm _ _ _, supBot_add, ← sup_assoc, wb_sup_add]

lemma wb_add (a n : ℕ) : wb (a + n) = wb a + wb n := by
  simp [wb, WithBot.coe_add]

lemma wb_max (a b : ℕ) : wb (max a b) = wb a ⊔ wb b := by
  simp [wb, Nat.cast_max, WithBot.coe_sup]

lemma wb_sub (a n : ℕ) : wb (a - n) = (wb a + ((-(n : ℤ) : ℤ) : WithBot ℤ)) ⊔ ((0 : ℤ) : WithBot ℤ) := by
  rw [← WithBot.coe_add, ← WithBot.coe_sup, WithBot.coe_inj]
  omega

/-- `cur`'s widths are its terms at `ix` and `iz`. -/
def AgreeW (st : WidthState k) (E : Fin k → WidthTerm k) (ix iz : Fin k → ℕ) : Prop :=
  ∀ i, wb (st.xw i) = (E i).eval ix ∧ wb (st.zw i) = (E i).eval iz

/-- `mx`'s needs are its terms at `ix` and `iz`. -/
def AgreeN (mx : NeededWidths k) (E : Fin k → WidthTerm k) (ix iz : Fin k → ℕ) : Prop :=
  ∀ i, wb (mx.xneed i) = (E i).eval ix ∧ wb (mx.zneed i) = (E i).eval iz

lemma norm_eq (e : WidthTerm k) : e.norm = e := by
  obtain ⟨c, d⟩ := e
  simp only [WidthTerm.norm]
  congr
  funext t
  simp

lemma ofFn_get (E : Fin k → WidthTerm k) : (Slots.ofFn E).get = E := by
  funext i
  simp [Slots.ofFn, norm_eq]

lemma agree_point {st : WidthState k} {E : Fin k → WidthTerm k} {ix iz : Fin k → ℕ}
    (h : AgreeW st E ix iz) (j : Fin k) (vx vz : ℕ) (e : WidthTerm k)
    (hx : wb vx = e.eval ix) (hz : wb vz = e.eval iz) :
    AgreeW ⟨Function.update st.xw j vx, Function.update st.zw j vz⟩ (Function.update E j e) ix iz := by
  intro i
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self]
    exact ⟨hx, hz⟩
  · simp only [Function.update_of_ne hij]
    exact h i

open Operations in
lemma agree_update {st : WidthState k} {E : Fin k → WidthTerm k} {ix iz : Fin k → ℕ}
    (h : AgreeW st E ix iz) (op : valid_ops k) :
    AgreeW (updateWidthState st op) (symUpdate ⟨E⟩ op).get ix iz := by
  cases op <;> simp only [symUpdate, ofFn_get]
  case shiftL j n =>
      refine agree_point h j _ _ _ ?_ ?_
      · rw [evalAdd, ← (h j).1, wb_add]
      · rw [evalAdd, ← (h j).2, wb_add]
  case shiftR j n =>
      refine agree_point h j _ _ _ ?_ ?_
      · rw [evalTrunc, ← (h j).1, wb_sub]
      · rw [evalTrunc, ← (h j).2, wb_sub]
  case negate j =>
      refine agree_point h j _ _ _ ?_ ?_
      · rw [evalAdd, ← (h j).1, wb_add]; rfl
      · rw [evalAdd, ← (h j).2, wb_add]; rfl
  case addScaled dst src negSrc shift =>
      refine agree_point h dst _ _ _ ?_ ?_
      · rw [evalAdd, evalSup, evalAdd, ← (h dst).1, ← (h src).1, wb_add, wb_max, wb_add, add_comm]
        rfl
      · rw [evalAdd, evalSup, evalAdd, ← (h dst).2, ← (h src).2, wb_add, wb_max, wb_add, add_comm]
        rfl
  case phaseProduct j => exact h

lemma agree_merge {mx : NeededWidths k} {cur : WidthState k} {E F : Fin k → WidthTerm k}
    {ix iz : Fin k → ℕ} (hm : AgreeN mx E ix iz) (hc : AgreeW cur F ix iz) :
    AgreeN (mergeNeededWidths mx (widthsOfState cur)) (fun i => (E i).sup (F i)) ix iz := by
  intro i
  simp [mergeNeededWidths, widthsOfState, evalSup, wb_max, (hm i).1, (hm i).2, (hc i).1, (hc i).2]

lemma agree_scan {ix iz : Fin k → ℕ} :
    ∀ (ops : List (Operations.valid_ops k)) (cur : WidthState k) (mx : NeededWidths k)
      (E F : Fin k → WidthTerm k), AgreeW cur F ix iz → AgreeN mx E ix iz →
      AgreeN (scanNeededWidthsAux cur mx ops) (symScanAux ⟨F⟩ ⟨E⟩ ops).get ix iz
  | [], _, _, _, _, _, hm => hm
  | op :: rest, cur, mx, E, F, hc, hm => by
      simp only [scanNeededWidthsAux, symScanAux]
      have hu := agree_update hc op
      rw [show symUpdate ⟨F⟩ op = ⟨(symUpdate ⟨F⟩ op).get⟩ from rfl]
      rw [show Slots.ofFn (fun i => (E i).sup ((symUpdate ⟨F⟩ op).get i))
          = ⟨fun i => (E i).sup ((symUpdate ⟨F⟩ op).get i)⟩ from by
            cases hs : Slots.ofFn _; congr; exact (congrArg Slots.get hs).symm.trans (ofFn_get _)]
      exact agree_scan rest _ _ _ _ hu (agree_merge hm hu)

lemma agree_init (k xw zw : ℕ) :
    AgreeW (initWidths k xw zw) WidthTerm.var (initWidths k xw zw).xw (initWidths k xw zw).zw :=
  fun i => ⟨(evalVar i _).symm, (evalVar i _).symm⟩

lemma agree_init_need (k xw zw : ℕ) :
    AgreeN (widthsOfState (initWidths k xw zw)) WidthTerm.var
      (initWidths k xw zw).xw (initWidths k xw zw).zw :=
  fun i => ⟨(evalVar i _).symm, (evalVar i _).symm⟩

lemma ofReg_interval_width (a n : ℕ) : (ExtReg.ofReg (Reg.interval a n)).width = n := by
  simp [ExtReg.width, ExtReg.ofReg, regSize, Reg.width, Reg.interval]

lemma initWidthState_eq (k wx wz : ℕ) :
    initWidthState (ExtReg.ofReg (Reg.interval 0 wx)) (ExtReg.ofReg (Reg.interval wx wz)) k
      = initWidths k wx wz := by
  simp only [initWidthState, phaseLimbWidth, initWidths, ofReg_interval_width]

@[simp] lemma compile_k (T : ToomCookTable) : T.compile.k = T.k := rfl

theorem levelWidth_compile (T : ToomCookTable) (R : WidthRule) (wx wz : ℕ) :
    T.compile.levelWidth R wx wz = nextWidthBy R T.ops wx wz := by
  cases R
  · show 1 + botToNat (supBot T.k fun i =>
        ((widthMap T.ops).get i).eval (initWidths T.k wx wz).xw
          ⊔ ((widthMap T.ops).get i).eval (initWidths T.k wx wz).zw)
      = commonNeededWidth (neededWidthsBy .scan _ _ T.ops)
    simp only [neededWidthsBy, scanNeededWidths, commonNeededWidth, initWidthState_eq,
      ← supFin_eq_sup, supFin_eq_botToNat]
    congr 2
    congr 1
    funext i
    have h := agree_scan T.ops (initWidths T.k wx wz) (widthsOfState (initWidths T.k wx wz))
      WidthTerm.var WidthTerm.var (agree_init T.k wx wz) (agree_init_need T.k wx wz) i
    rw [wb_max, h.1, h.2]
    rfl
  · show exactSignedWidthOfWidths T.ops wx wz = commonNeededWidth (neededWidthsBy .exact _ _ T.ops)
    simp only [neededWidthsBy, ofReg_interval_width]
    exact (commonNeededWidth_exactNeeded (by have := T.hk; omega) T.ops wx wz).symm

open Operations in
theorem scratch_compile (T : ToomCookTable) (W : ℕ) :
    T.compile.scratch W = Policy.opsScratch T.ops W := by
  have key : ∀ ops : Prog T.k,
      (if ops.any (fun op => match op with | .negate _ => true | _ => false) then 1
        else if ops.any (fun op => match op with | .addScaled _ _ _ _ => true | _ => false) then 1
        else 0)
      = Policy.opsScratch ops W := by
    intro ops
    induction ops with
    | nil => rfl
    | cons op rest ih =>
        rw [Policy.opsScratch, ← ih]
        cases op <;> simp [Policy.opScratch] <;> split_ifs <;> omega
  exact key T.ops

lemma chooseData_map (n : ℕ) : ∀ (l : List PolicyBand),
    chooseData (l.map fun b => (b.threshold, b.table.compile)) n
      = (l.find? fun b => decide (b.threshold ≤ n)).map fun b => b.table.compile
  | [] => rfl
  | b :: l => by
      simp only [chooseData, List.map_cons, List.find?_cons]
      by_cases h : b.threshold ≤ n
      · simp [h]
      · simp only [h, decide_false]
        exact chooseData_map n l

lemma chooseData_compile (P : ShorLoweringPolicy) (n : ℕ) :
    chooseData (Policy.compile P) n = (P.choose n).map ToomCookTable.compile := by
  rw [Policy.compile, chooseData_map, ShorLoweringPolicy.choose, Option.map_map]
  rfl

/-! ## One level's growth is `k · W - w` -/

lemma sum_chunkWidths (m w ℓ : ℕ) (h : m * ℓ ≤ w) :
    ∑ i : Fin (m + 1), phaseSplitLogicalWidth w ℓ (m + 1) i = w := by
  rw [Fin.sum_univ_castSucc]
  have hlow : ∀ i : Fin m, phaseSplitLogicalWidth w ℓ (m + 1) (Fin.castSucc i) = ℓ := by
    intro i
    have hi : ¬ isTopChunk (Fin.castSucc i) := by
      unfold isTopChunk; simp only [Fin.val_castSucc]; have := i.isLt; omega
    simp [phaseSplitLogicalWidth, hi]
  have htop : phaseSplitLogicalWidth w ℓ (m + 1) (Fin.last m) = w - m * ℓ := by
    have hi : isTopChunk (Fin.last m) := by unfold isTopChunk; simp
    simp [phaseSplitLogicalWidth, hi]
  simp only [hlow, htop, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

lemma immediateNeedBy_eq (R : WidthRule) (side : PhaseSide) {k : ℕ} (ops : Prog k) (wx wz : ℕ) :
    immediateNeedBy R side ops wx wz = k * nextWidthBy R ops wx wz - side.width wx wz := by
  have hge : ∀ i : Fin k,
      phaseSplitLogicalWidth (side.width wx wz) (limbWidth k wx wz) k i ≤ nextWidthBy R ops wx wz := by
    intro i
    have h1 := neededWidthsBy_ge_init R (ExtReg.ofReg (Reg.interval 0 wx))
      (ExtReg.ofReg (Reg.interval wx wz)) ops i
    have h2 := commonNeededWidth_gt (neededWidthsBy R (ExtReg.ofReg (Reg.interval 0 wx))
      (ExtReg.ofReg (Reg.interval wx wz)) ops) i
    simp only [initWidthState, ofReg_interval_width] at h1
    cases side
    · exact le_of_lt (lt_of_le_of_lt h1.1 h2.1)
    · exact le_of_lt (lt_of_le_of_lt h1.2 h2.2)
  simp only [immediateNeedBy]
  rw [Finset.sum_tsub_distrib _ (fun i _ => hge i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  cases k with
  | zero => simp
  | succ m =>
    have hℓ : limbWidth (m + 1) wx wz ≤ side.width wx wz / (m + 1) := by
      simp only [limbWidth, phaseLimbWidth, ofReg_interval_width]
      cases side
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hle : m * limbWidth (m + 1) wx wz ≤ side.width wx wz :=
      calc m * limbWidth (m + 1) wx wz ≤ (m + 1) * (side.width wx wz / (m + 1)) :=
            Nat.mul_le_mul (Nat.le_succ m) hℓ
        _ ≤ side.width wx wz := Nat.mul_div_le _ _
    rw [sum_chunkWidths m _ _ hle]

/-! ## The phase-product chain -/

theorem peakReserveF_eq (P : ShorLoweringPolicy) :
    ∀ (f wx wz : ℕ), max wx wz < f →
      peakReserveF P.widthRule (Policy.compile P) f wx wz = Rec.peakReserve P wx wz := by
  intro f
  induction f with
  | zero => intro wx wz h; omega
  | succ f ih =>
    intro wx wz h
    rw [peakReserveF, Rec.peakReserve, chooseData_compile]
    cases hT : P.choose (max wx wz) with
    | none => rfl
    | some T =>
      simp only [Option.map_some, immediateXNeedBy, immediateZNeedBy, immediateNeedBy_eq,
        PhaseSide.width, levelWidth_compile, scratch_compile, compile_k]
      by_cases hrec : nextWidthBy P.widthRule T.ops wx wz < max wx wz
      · simp only [hrec, ↓reduceIte, ↓reduceDIte]
        rw [ih _ _ (by rw [max_self]; omega)]
      · simp only [hrec, ↓reduceIte, ↓reduceDIte]

theorem peakReserveD_eq (P : ShorLoweringPolicy) :
    peakReserveD P.widthRule (Policy.compile P) = Rec.peakReserve P := by
  funext wx wz
  exact peakReserveF_eq P _ wx wz (Nat.lt_succ_self _)

theorem reserveBudgetF_eq (P : ShorLoweringPolicy) :
    ∀ (f wx wz : ℕ), max wx wz < f →
      reserveBudgetF P.widthRule (Policy.compile P) f wx wz = Policy.reserveNeed P wx wz := by
  intro f
  induction f with
  | zero => intro wx wz h; omega
  | succ f ih =>
    intro wx wz h
    rw [reserveBudgetF, Policy.reserveNeed, chooseData_compile]
    cases hT : P.choose (max wx wz) with
    | none => rfl
    | some T =>
      simp only [Option.map_some, immediateXNeedBy, immediateZNeedBy, immediateNeedBy_eq,
        PhaseSide.width, levelWidth_compile, compile_k]
      by_cases hrec : nextWidthBy P.widthRule T.ops wx wz < max wx wz
      · simp only [hrec, ↓reduceIte, ↓reduceDIte]
        rw [ih _ _ (by rw [max_self]; omega)]
      · simp only [hrec, ↓reduceIte, ↓reduceDIte]

theorem reserveBudgetD_eq (P : ShorLoweringPolicy) :
    reserveBudgetD P.widthRule (Policy.compile P) = Policy.reserveNeed P := by
  funext wx wz
  exact reserveBudgetF_eq P _ wx wz (Nat.lt_succ_self _)

/-! ## The QFT's halving tree -/

lemma qftPeakOf_eq (pp : ℕ → ℕ → ℕ) (n : ℕ) :
    Rec.qftPeakOf pp n = max (qftSplitPeak pp n)
      (if 2 ≤ n then max (Rec.qftPeakOf pp (n / 2)) (Rec.qftPeakOf pp (n - n / 2)) else 0) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp [Rec.qftPeakOf, qftSplitPeak]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [Rec.qftPeakOf]
    simp only [qftSplitPeak, ite_eq_left h]

lemma qftPeakOf_lt_two (pp : ℕ → ℕ → ℕ) {n : ℕ} (h : n < 2) : Rec.qftPeakOf pp n = 0 := by
  interval_cases n <;> simp [Rec.qftPeakOf]

/-- The children of two widths at most one apart are the two widths at the next depth. -/
lemma qftStep (pp : ℕ → ℕ → ℕ) {lo hi : ℕ} (hlh : lo ≤ hi) (hhl : hi ≤ lo + 1) :
    max (Rec.qftPeakOf pp lo) (Rec.qftPeakOf pp hi)
      = max (max (qftSplitPeak pp lo) (qftSplitPeak pp hi))
          (if 2 ≤ hi then max (Rec.qftPeakOf pp (lo / 2)) (Rec.qftPeakOf pp ((hi + 1) / 2)) else 0) := by
  rw [qftPeakOf_eq pp lo, qftPeakOf_eq pp hi]
  suffices h : max (if 2 ≤ lo then max (Rec.qftPeakOf pp (lo / 2)) (Rec.qftPeakOf pp (lo - lo / 2)) else 0)
      (if 2 ≤ hi then max (Rec.qftPeakOf pp (hi / 2)) (Rec.qftPeakOf pp (hi - hi / 2)) else 0)
      = if 2 ≤ hi then max (Rec.qftPeakOf pp (lo / 2)) (Rec.qftPeakOf pp ((hi + 1) / 2)) else 0 by
    rw [← h]
    generalize qftSplitPeak pp lo = A
    generalize qftSplitPeak pp hi = B
    generalize (if 2 ≤ lo then max (Rec.qftPeakOf pp (lo / 2)) (Rec.qftPeakOf pp (lo - lo / 2)) else 0) = C
    generalize (if 2 ≤ hi then max (Rec.qftPeakOf pp (hi / 2)) (Rec.qftPeakOf pp (hi - hi / 2)) else 0) = D
    omega
  rcases Nat.lt_or_ge hi 2 with h2 | h2
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    rfl
  · rcases Nat.lt_or_ge lo 2 with hl | hl
    · obtain rfl : lo = 1 := by omega
      obtain rfl : hi = 2 := by omega
      simp [qftPeakOf_lt_two]
    · rw [ite_eq_left hl, ite_eq_left h2, ite_eq_left h2]
      have e1 : hi - hi / 2 = (hi + 1) / 2 := by omega
      rw [e1]
      rcases (show lo - lo / 2 = lo / 2 ∨ lo - lo / 2 = (hi + 1) / 2 by omega) with e2 | e2 <;>
      rcases (show hi / 2 = lo / 2 ∨ hi / 2 = (hi + 1) / 2 by omega) with e3 | e3 <;>
      rw [e2, e3] <;>
      generalize Rec.qftPeakOf pp (lo / 2) = A <;>
      generalize Rec.qftPeakOf pp ((hi + 1) / 2) = B <;>
      omega

theorem qftPeakF_eq (pp : ℕ → ℕ → ℕ) :
    ∀ (f lo hi : ℕ), hi < f → lo ≤ hi → hi ≤ lo + 1 →
      qftPeakF pp f lo hi = max (Rec.qftPeakOf pp lo) (Rec.qftPeakOf pp hi) := by
  intro f
  induction f with
  | zero => intro lo hi h; omega
  | succ f ih =>
    intro lo hi hf hlh hhl
    rw [qftPeakF, qftStep pp hlh hhl]
    by_cases h2 : 2 ≤ hi
    · rw [ite_eq_left h2, ite_eq_left h2, ih _ _ (by omega) (by omega) (by omega)]
    · rw [ite_eq_right h2, ite_eq_right h2]

theorem qftPeakD_eq (P : ShorLoweringPolicy) :
    qftPeakD P.widthRule (Policy.compile P) = Rec.qftPeak P := by
  funext n
  rw [qftPeakD, peakReserveD_eq, qftPeakF_eq _ _ _ _ (Nat.lt_succ_self n) le_rfl (Nat.le_succ n),
    max_self, Rec.qftPeak]

/-! ## The circuit budgets -/

theorem orderFindingPeak_eq (P : ShorLoweringPolicy) (xW dW wW sW : ℕ) :
    Policy.orderFindingPeak P xW dW wW sW = Rec.orderFindingPeak P xW dW wW sW := by
  simp only [Policy.orderFindingPeak, orderFindingPeakD, orderFindingPeakWith, modMulPeakWith,
    modMulPhasePeaksWith, Rec.orderFindingPeak, Rec.orderFindingPeakWith, Rec.modMulPeakWith,
    Rec.modMulPhasePeaksWith, Rec.ppPeak, qftPeakD_eq, peakReserveD_eq]

lemma splitPeakOf_eq (pp : ℕ → ℕ → ℕ) :
    ∀ (bs : List Balanced.Block) (t wx wz : ℕ),
      splitPeakOf pp bs t wx wz = Rec.splitPeakOf pp bs t wx wz
  | [], _, _, _ => rfl
  | b :: bs, t, wx, wz => by rw [splitPeakOf, Rec.splitPeakOf, splitPeakOf_eq pp bs]

lemma planFitsOf_reserveNeed (P : ShorLoweringPolicy) :
    ∀ (bs : List Balanced.Block) (t wx cx wz cz : ℕ),
      planFitsOf (Policy.reserveNeed P) bs t wx cx wz cz = Rec.planFits P bs t wx cx wz cz
  | [], _, _, _, _, _ => rfl
  | b :: bs, t, wx, cx, wz, cz => by
      rw [planFitsOf, Rec.planFits, planFitsOf_reserveNeed P bs]

theorem sitePeakD_eq (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    sitePeakD P.widthRule (Policy.compile P) R = Rec.sitePeak P R := by
  funext wx cx wz cz
  unfold sitePeakD sitePeakOf Rec.sitePeak
  rw [peakReserveD_eq, reserveBudgetD_eq]
  split_ifs
  · rcases R.plan wx wz with _ | p
    · rfl
    · simp only [planFitsOf_reserveNeed, splitPeakOf_eq]
  · rcases R.plan wz wx with _ | p
    · rfl
    · simp only [planFitsOf_reserveNeed, splitPeakOf_eq]
  · rfl

theorem orderFindingPeakBalanced_eq (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (xW dW dC wW wC sW sC : ℕ) :
    Policy.orderFindingPeakBalanced P R xW dW dC wW wC sW sC
      = Rec.orderFindingPeakWith P (Rec.sitePeak P R) xW dW dC wW wC sW sC := by
  simp only [Policy.orderFindingPeakBalanced, orderFindingPeakBalancedD, orderFindingPeakWith,
    modMulPeakWith, modMulPhasePeaksWith, Rec.orderFindingPeakWith, Rec.modMulPeakWith,
    Rec.modMulPhasePeaksWith, qftPeakD_eq, sitePeakD_eq]

end QubitCount
end Shor
