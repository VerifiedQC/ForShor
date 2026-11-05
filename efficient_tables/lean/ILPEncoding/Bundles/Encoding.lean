import ILPEncoding.Labels.ILPChecked
import ILPEncoding.Bounds.Size
import ILPEncoding.Labels.Typed
import ILPEncoding.Bounds.StopBudget
import Mathlib.Data.List.Dedup
import Mathlib.Tactic
import ILPEncoding.Bundles.Profile

/-! # Bundled Encoding Bounds
A single-file bundle of the ILP encoding size development, concatenating the segments marked by its `BEGIN` comments. It contains the row-bound lemmas, `qWord` control, `matrixBits` bounds, `systemRowsC_iff_feasible`, `canonical_matrix_bits_uniform` and `optimizer_canonical_matrix_bits`. It bounds the finite encoding and makes no ILP-solver or uniform polynomial-synthesis claim.
-/

/- BEGIN Bounds.lean source_sha256=1fb2a5d6ab1829c370f7fe2efa9e3060cab447cd812cb2a70227910fbce5a634 body_sha256=f134ad1d348a865beb464271804185fdeadf839a9c341760e209a1bd1a082b5e -/

namespace Paper.F7Size

open Paper.F6ILP Paper.F6ILPRows Paper.AffineNat

def Controlled (U K P : ℤ) : List Label → Prop
  | [] => 0 ≤ P
  | label :: rest =>
      0 ≤ P ∧ P * label.k ≤ U ∧ (label.k : ℤ) ≤ K ∧
        Controlled U K (P * label.k) rest

def interceptGrowth (U K : ℤ) : List Label → ℤ
  | [] => 0
  | _ :: rest => 2 * U * K + interceptGrowth U K rest

def coeffGrowth (U : ℤ) : List Label → ℤ
  | [] => 0
  | _ :: rest => U + coeffGrowth U rest

theorem terminalExpr_bounds {keys : Finset Nat}
    (e : AffineExpr keys) (P U K B C : ℤ)
    (labels : List Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys)
    (hcontrol : Controlled U K P labels)
    (hintercept : -B ≤ e.intercept ∧ e.intercept ≤ B)
    (hcoeff : ∀ key, 0 ≤ e.coeff key ∧ e.coeff key ≤ C) :
    let result := terminalExpr P e labels hkeys;
    -(B + interceptGrowth U K labels) ≤ result.intercept ∧
      result.intercept ≤ B + interceptGrowth U K labels ∧
      (∀ key, 0 ≤ result.coeff key ∧
        result.coeff key ≤ C + coeffGrowth U labels) := by
  induction labels generalizing P e B C with
  | nil =>
      have h : -B ≤ e.intercept ∧ e.intercept ≤ B ∧
          (∀ key, 0 ≤ e.coeff key ∧ e.coeff key ≤ C) :=
        ⟨hintercept.1, hintercept.2, hcoeff⟩
      simpa [terminalExpr, interceptGrowth, coeffGrowth] using h
  | cons label rest ih =>
      have hk : label.k ∈ keys := hkeys label (by simp)
      have htail : ∀ q ∈ rest, q.k ∈ keys := by
        intro q hq
        exact hkeys q (by simp [hq])
      have hsintercept := step_constant_bounds e P U K B label hk
        hcontrol.1 hcontrol.2.1 hcontrol.2.2.1 hintercept
      have hscoeff := step_coeff_nonneg_le e P U C label hk
        hcontrol.1 hcontrol.2.1 hcoeff
      have hresult := ih (stepExpr e P label hk) (P * label.k)
        (B + 2 * U * K) (C + U) htail hcontrol.2.2.2
        hsintercept hscoeff
      simpa only [terminalExpr, interceptGrowth, coeffGrowth,
        add_assoc] using hresult

theorem interceptGrowth_eq_length (U K : ℤ) (labels : List Label) :
    interceptGrowth U K labels =
      2 * U * K * labels.length := by
  induction labels with
  | nil => simp [interceptGrowth]
  | cons label rest ih =>
      simp only [interceptGrowth, List.length_cons, Nat.cast_succ, ih]
      ring

theorem coeffGrowth_eq_length (U : ℤ) (labels : List Label) :
    coeffGrowth U labels = U * labels.length := by
  induction labels with
  | nil => simp [coeffGrowth]
  | cons label rest ih =>
      simp only [coeffGrowth, List.length_cons, Nat.cast_succ, ih]
      ring

end Paper.F7Size
/- END Bounds.lean -/

/- BEGIN Prefix.lean source_sha256=d5e52bf75e3bceca06425cccfe62c522171ef599a9bc90b4610bea07ed345819 body_sha256=6bbccef7d0b1e417cb6afb51c12707c1c3f7dd9b45353495e197637076b47f67 -/

namespace Paper.F7QControl

open Paper.AffineNat Paper.F7Size
open Paper.CountStage.TypedDecorationWords Paper.F6TypedBridge

def qWord : List Label → Nat
  | [] => 1
  | label :: rest => (2 * label.k - 1) * qWord rest

theorem qWord_pos (labels : List Label) : 1 ≤ qWord labels := by
  induction labels with
  | nil => simp [qWord]
  | cons label rest ih =>
      have hq : 1 ≤ 2 * label.k - 1 := by
        have hk := label.hk
        omega
      simpa only [qWord] using Nat.mul_le_mul hq ih

theorem qWord_eq_typed (labels : List Label) :
    qWord labels = qProduct labelQ (labels.map toTyped) := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
      simp only [qWord, List.map_cons, qProduct, List.prod_cons]
      simp only [labelQ, toTyped]
      exact congrArg (fun n => (2 * label.k - 1) * n) ih

theorem controlled_of_qWord (U K P : Nat) (labels : List Label)
    (hbudget : P * qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K) :
    Controlled U K P labels := by
  induction labels generalizing P with
  | nil => simp [Controlled]
  | cons label rest ih =>
      have hq : label.k ≤ 2 * label.k - 1 := by
        have hk := label.hk
        omega
      have hfull : P * (2 * label.k - 1) * qWord rest ≤ U := by
        simpa only [qWord, mul_assoc] using hbudget
      have hfactor : (P * label.k) * qWord rest ≤
          P * (2 * label.k - 1) * qWord rest := by
        have h := Nat.mul_le_mul_left P
          (Nat.mul_le_mul_right (qWord rest) hq)
        simpa only [mul_assoc] using h
      have htailbudget : (P * label.k) * qWord rest ≤ U :=
        le_trans hfactor hfull
      have hprod : P * label.k ≤ U := by
        have h := Nat.mul_le_mul_left (P * label.k) (qWord_pos rest)
        have hh : P * label.k ≤ (P * label.k) * qWord rest := by
          simpa only [mul_one] using h
        exact le_trans hh htailbudget
      have htailK : ∀ q ∈ rest, q.k ≤ K := by
        intro q hqmem
        exact hK q (by simp [hqmem])
      refine ⟨by exact_mod_cast (Nat.zero_le P), ?_, ?_, ?_⟩
      · exact_mod_cast hprod
      · exact_mod_cast hK label (by simp)
      · exact ih (P * label.k) htailbudget htailK

theorem controlled_root_of_typed_budget (U K : Nat)
    (labels : List Label)
    (hbudget : qProduct labelQ (labels.map toTyped) ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K) :
    Controlled U K 1 labels := by
  apply controlled_of_qWord U K 1 labels
  · simpa only [one_mul, qWord_eq_typed] using hbudget
  · exact hK

end Paper.F7QControl
/- END Prefix.lean -/

/- BEGIN Bounds.lean source_sha256=678ac91470ce2b8dc635acd21f3a7154912129b7c7255173ac3ca907b61f31f6 body_sha256=51444f260f807819437024cd8d5bbb6f17071b5c24826012f4812b9fa9494861 -/

namespace Paper.F7Products

open Paper.AffineNat Paper.AffineILP Paper.F6Objective
open Paper.F7QControl

def kWord : List Label → Nat
  | [] => 1
  | label :: rest => label.k * kWord rest

theorem kWord_le_qWord (labels : List Label) :
    kWord labels ≤ qWord labels := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
      have hk := label.hk
      have hfactor : label.k ≤ 2 * label.k - 1 := by omega
      calc
        kWord (label :: rest) = label.k * kWord rest := rfl
        _ ≤ label.k * qWord rest := Nat.mul_le_mul_left _ ih
        _ ≤ (2 * label.k - 1) * qWord rest :=
          Nat.mul_le_mul_right _ hfactor
        _ = qWord (label :: rest) := rfl

theorem terminalProduct_eq_kWord (P : ℤ) (a : Nat → Nat)
    (labels : List Label) :
    terminalProduct P (labels.map (Paper.AffineNat.instantiate a)) =
      P * (kWord labels : ℤ) := by
  induction labels generalizing P with
  | nil => simp [terminalProduct, kWord]
  | cons label rest ih =>
      change terminalProduct (P * label.k)
          (rest.map (Paper.AffineNat.instantiate a)) =
        P * (kWord (label :: rest) : ℤ)
      rw [ih (P * label.k)]
      simp only [kWord, Nat.cast_mul]
      ring

theorem terminalProduct_le_typed_budget (U : Nat) (a : Nat → Nat)
    (labels : List Label)
    (hbudget : qWord labels ≤ U) :
    terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) ≤ U := by
  rw [terminalProduct_eq_kWord]
  norm_num
  exact_mod_cast (le_trans (kWord_le_qWord labels) hbudget)

theorem finalN_eq_qWord (N : Nat) (labels : List Label) :
    finalN N labels = N * qWord labels := by
  induction labels generalizing N with
  | nil => simp [finalN, qWord]
  | cons label rest ih =>
      change finalN (N * (2 * (label.k - 1) + 1)) rest =
        N * qWord (label :: rest)
      rw [ih]
      have hk := label.hk
      have hq : 2 * (label.k - 1) + 1 = 2 * label.k - 1 := by omega
      rw [hq]
      simp [qWord, mul_assoc]

theorem finalN_le_budget (labels : List Label) (U : Nat)
    (hbudget : qWord labels ≤ U) :
    finalN 1 labels ≤ U := by
  simpa only [finalN_eq_qWord, one_mul] using hbudget

end Paper.F7Products
/- END Bounds.lean -/

/- BEGIN Matrix.lean source_sha256=1d2abe876d0cfd1d6e30563f994ffc32140d7753876c28a7808ee9c11743e278 body_sha256=8cae8df261ac5a50e9d543733c61b10144de3ac81a499f8be3544cdaf655cbd8 -/

namespace Paper.F7Encoding

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F6Objective Paper.F6Cleared Paper.AffineNat

def binaryBits (z : ℤ) : Nat := Nat.log2 z.natAbs + 2

theorem binaryBits_le (z : ℤ) (M : Nat) (h : z.natAbs ≤ M) :
    binaryBits z ≤ M + 2 := by
  unfold binaryBits
  exact Nat.add_le_add_right ((Nat.log2_le_self _).trans h) 2

def rowBits {keys : Finset Nat} (row : AffineExpr keys) : Nat :=
  binaryBits row.intercept +
    ∑ key : { k : Nat // k ∈ keys }, binaryBits (row.coeff key)

def matrixBits {keys : Finset Nat} (rows : List (AffineExpr keys)) : Nat :=
  (rows.map rowBits).sum

theorem rowBits_le {keys : Finset Nat} (row : AffineExpr keys)
    (M : Nat) (hintercept : row.intercept.natAbs ≤ M)
    (hcoeff : ∀ key, (row.coeff key).natAbs ≤ M) :
    rowBits row ≤ (Fintype.card { k : Nat // k ∈ keys } + 1) * (M + 2) := by
  have hsum : (∑ key : { k : Nat // k ∈ keys }, binaryBits (row.coeff key)) ≤
      ∑ _key : { k : Nat // k ∈ keys }, (M + 2) := by
    apply Finset.sum_le_sum
    intro key _
    exact binaryBits_le _ M (hcoeff key)
  calc
    rowBits row ≤ (M + 2) +
        ∑ _key : { k : Nat // k ∈ keys }, (M + 2) :=
      Nat.add_le_add (binaryBits_le _ M hintercept) hsum
    _ = (Fintype.card { k : Nat // k ∈ keys } + 1) * (M + 2) := by
      simp [add_mul, Nat.add_comm]

theorem matrixBits_le {keys : Finset Nat}
    (rows : List (AffineExpr keys)) (M : Nat)
    (hrows : ∀ row ∈ rows,
      row.intercept.natAbs ≤ M ∧
      ∀ key, (row.coeff key).natAbs ≤ M) :
    matrixBits rows ≤ rows.length *
      (Fintype.card { k : Nat // k ∈ keys } + 1) * (M + 2) := by
  induction rows with
  | nil => simp [matrixBits]
  | cons row rest ih =>
      have hfirst := hrows row (by simp)
      have htail : ∀ q ∈ rest,
          q.intercept.natAbs ≤ M ∧
          ∀ key, (q.coeff key).natAbs ≤ M := by
        intro q hq
        exact hrows q (by simp [hq])
      have hrest := ih htail
      have hrow := rowBits_le row M hfirst.1 hfirst.2
      calc
        matrixBits (row :: rest) = rowBits row + matrixBits rest := rfl
        _ ≤ (Fintype.card { k : Nat // k ∈ keys } + 1) * (M + 2) +
            rest.length * (Fintype.card { k : Nat // k ∈ keys } + 1) *
              (M + 2) := Nat.add_le_add hrow hrest
        _ = (row :: rest).length *
            (Fintype.card { k : Nat // k ∈ keys } + 1) * (M + 2) := by
          simp only [List.length_cons]
          ring

def lowerRow {keys : Finset Nat} (key : { k : Nat // k ∈ keys })
    (lo : Nat → Nat) : AffineExpr keys where
  intercept := -(lo key.val : ℤ)
  coeff := fun j => if j = key then 1 else 0

def upperRow {keys : Finset Nat} (key : { k : Nat // k ∈ keys })
    (hi : Nat → Nat) : AffineExpr keys where
  intercept := hi key.val
  coeff := fun j => if j = key then -1 else 0

def boundRows {keys : Finset Nat} (lo hi : Nat → Nat) :
    List { k : Nat // k ∈ keys } → List (AffineExpr keys)
  | [] => []
  | key :: rest => lowerRow key lo :: upperRow key hi :: boundRows lo hi rest

theorem boundRows_length {keys : Finset Nat} (lo hi : Nat → Nat)
    (ks : List { k : Nat // k ∈ keys }) :
    (boundRows lo hi ks).length = 2 * ks.length := by
  induction ks with
  | nil => rfl
  | cons key rest ih =>
      simp only [boundRows, List.length_cons, ih]
      omega

noncomputable def systemRows (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat) :
    List (AffineExpr (usedArities labels)) :=
  let terminal := terminalRow labels x z
  [terminal, scaleExpr (-1) terminal] ++
    contractionRoot labels x ++
    [budgetRow labels x z c price N T] ++
    boundRows lo hi (Finset.univ.toList : List (Variable labels))

theorem systemRows_length (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat) :
    (systemRows labels x z c lo hi price N T).length =
      2 * Fintype.card (Variable labels) + labels.length + 3 := by
  have hcon := Paper.F7Size.contractionRoot_length labels x
  simp only [systemRows, List.length_append, List.length_cons,
    List.length_nil, Nat.add_zero, hcon, boundRows_length]
  simp
  omega

end Paper.F7Encoding
/- END Matrix.lean -/

/- BEGIN Rows.lean source_sha256=35486cc691c4087d92afc8091ea549df497a3d30ca3458f46b67de96cb24c76f body_sha256=946bdde1011ed9ce5ebc6aa76d10d36b91742b2a5dd0a0aef29650d3b66fa6fe -/

namespace Paper.F7Computable

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F7Encoding Paper.AffineNat

def usedKeys (labels : List Label) : List (Variable labels) :=
  ((labels.map Label.k).dedup).attach.map fun key =>
    ⟨key.val, by
      have h : key.val ∈ labels.map Label.k := by
        simpa only [List.mem_dedup] using key.property
      simpa only [usedArities, List.mem_toFinset] using h⟩

theorem usedKeys_length (labels : List Label) :
    (usedKeys labels).length = (labels.map Label.k).dedup.length := by
  simp only [usedKeys, List.length_map, List.length_attach]

theorem usedKeys_card (labels : List Label) :
    (usedKeys labels).length = Fintype.card (Variable labels) := by
  rw [usedKeys_length, variable_count]
  have hset : ((labels.map Label.k).dedup).toFinset =
      (labels.map Label.k).toFinset := by
    ext k
    simp only [List.mem_toFinset, List.mem_dedup]
  have hcard := List.toFinset_card_of_nodup
    (List.nodup_dedup (labels.map Label.k))
  rw [hset] at hcard
  simpa only [usedArities] using hcard.symm

def systemRowsC (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat) :
    List (AffineExpr (usedArities labels)) :=
  let terminal := terminalRow labels x z
  [terminal, scaleExpr (-1) terminal] ++
    contractionRoot labels x ++
    [budgetRow labels x z c price N T] ++
    boundRows lo hi (usedKeys labels)

theorem systemRowsC_length (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat) :
    (systemRowsC labels x z c lo hi price N T).length =
      2 * (usedKeys labels).length + labels.length + 3 := by
  have hcon := Paper.F7Size.contractionRoot_length labels x
  simp only [systemRowsC, List.length_append, List.length_cons,
    List.length_nil, hcon, boundRows_length]
  omega

end Paper.F7Computable

/- END Rows.lean -/

/- BEGIN Bounds.lean source_sha256=eb0ebad5e88d28eb35d6e939f35c3431a1d71ab1c56a6858969f15bbfaeb5d9d body_sha256=34507b45f23ddd5dcb584e47755e91cd094a66571359fecd5fe01464874ff524 -/

namespace Paper.F7Terminal

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F7Size Paper.F7QControl Paper.F7Products Paper.AffineNat
open Paper.AffineILP

theorem terminalRow_bounds (labels : List Label) (x z : ℤ)
    (a : Nat → Nat) (U K : Nat) (n : ℤ)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hx : -n ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U) :
    -(n + 2 * (U : ℤ) * K * labels.length + (U : ℤ) * U) ≤ (terminalRow labels x z).intercept ∧
      (terminalRow labels x z).intercept ≤ n + 2 * (U : ℤ) * K * labels.length + (U : ℤ) * U ∧
      (∀ key, 0 ≤ (terminalRow labels x z).coeff key ∧
        (terminalRow labels x z).coeff key ≤ (U : ℤ) * labels.length) := by
  let E := terminalExpr 1 (rootExpr labels x) labels (keyProof labels)
  let D := terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a))
  have hcontrol : Controlled U K 1 labels :=
    controlled_root_of_typed_budget U K labels
      (by simpa only [← qWord_eq_typed] using hbudget) hK
  have hroot : -(n : ℤ) ≤ (rootExpr labels x).intercept ∧
      (rootExpr labels x).intercept ≤ n := by
    simpa only [rootExpr, startExpr] using hx
  have hzero : ∀ key, 0 ≤ (rootExpr labels x).coeff key ∧
      (rootExpr labels x).coeff key ≤ (0 : ℤ) := by
    intro key
    simp [rootExpr, startExpr]
  have hE := terminalExpr_bounds (rootExpr labels x) 1 U K n 0
    labels (keyProof labels) hcontrol hroot hzero
  have hE' :
      -(n + 2 * (U : ℤ) * K * labels.length) ≤ E.intercept ∧
      E.intercept ≤ n + 2 * (U : ℤ) * K * labels.length ∧
      (∀ key, 0 ≤ E.coeff key ∧
        E.coeff key ≤ (U : ℤ) * labels.length) := by
    simpa only [E, interceptGrowth_eq_length,
      coeffGrowth_eq_length, zero_add] using hE
  have hD0 : 0 ≤ D := le_of_lt (Paper.F6Cleared.terminalProduct_pos
    1 _ (by decide))
  have hDU : D ≤ U := terminalProduct_le_typed_budget U a labels hbudget
  have hDfix : D = terminalProduct 1
      (labels.map (Paper.AffineNat.instantiate (fun _ => 0))) := by
    exact Paper.F6ILPCost.terminalProduct_independent 1 labels a (fun _ => 0)
  have hDz : 0 ≤ D * z ∧ D * z ≤ (U : ℤ) * U := by
    constructor
    · exact mul_nonneg hD0 hz.1
    · nlinarith [mul_nonneg (sub_nonneg.mpr hDU) hz.1,
        mul_nonneg (Int.natCast_nonneg U) (sub_nonneg.mpr hz.2)]
  have hrow : (terminalRow labels x z).intercept = E.intercept - D * z := by
    simp [terminalRow, E, subExpr, startExpr, ← hDfix]
  have hcoeff : ∀ key, (terminalRow labels x z).coeff key = E.coeff key := by
    intro key
    simp [terminalRow, E, subExpr, startExpr]
  constructor
  · rw [hrow]
    nlinarith [hE'.1, hDz.2]
  constructor
  · rw [hrow]
    nlinarith [hE'.2.1, hDz.1]
  · intro key
    rw [hcoeff]
    exact hE'.2.2 key

end Paper.F7Terminal

/- END Bounds.lean -/

/- BEGIN Global.lean source_sha256=293f436e72fe38e471208c1789fcf604e0f0036b92708e69f08d5b5afb112226 body_sha256=0fc9fd60e3e756e7b69fc496ec0f28154311d93211e458ec01783d8d3cbfef07 -/

namespace Paper.F7Contraction

open Paper.F6ILP Paper.F6ILPRows Paper.F7Size Paper.AffineNat

theorem contractionExpr_global {keys : Finset Nat}
    (e next : AffineExpr keys) (P U K B C : ℤ) (label : Label)
    (hP : 0 ≤ P) (hprod : P * label.k ≤ U)
    (hK : (label.k : ℤ) ≤ K) (hB : 0 ≤ B)
    (he : -B ≤ e.intercept ∧ e.intercept ≤ B)
    (hn : -B ≤ next.intercept ∧ next.intercept ≤ B)
    (hc : ∀ key, 0 ≤ e.coeff key ∧ e.coeff key ≤ C)
    (hnc : ∀ key, 0 ≤ next.coeff key ∧ next.coeff key ≤ C) :
    -((K + 1) * B + U) ≤ (contractionExpr e next P label).intercept ∧
      (contractionExpr e next P label).intercept ≤ (K + 1) * B + U ∧
      (∀ key, -((K + 1) * C) ≤ (contractionExpr e next P label).coeff key ∧
        (contractionExpr e next P label).coeff key ≤ (K + 1) * C) := by
  have hU : 0 ≤ U := le_trans (mul_nonneg hP (Int.natCast_nonneg _)) hprod
  have hK0 : 0 ≤ K := le_trans (Int.natCast_nonneg _) hK
  have hke : -(K * B) ≤ label.k * e.intercept ∧
      label.k * e.intercept ≤ K * B := by
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hK)
        (sub_nonneg.mpr he.1), mul_nonneg (Int.natCast_nonneg label.k)
        (sub_nonneg.mpr he.1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hK)
        (sub_nonneg.mpr he.2), mul_nonneg (Int.natCast_nonneg label.k)
        (sub_nonneg.mpr he.2)]
  have hcoeff : ∀ key, 0 ≤ label.k * e.coeff key ∧
      label.k * e.coeff key ≤ K * C := by
    intro key
    constructor
    · exact mul_nonneg (Int.natCast_nonneg _) (hc key).1
    · have hC0 : 0 ≤ C := le_trans (hc key).1 (hc key).2
      nlinarith [mul_nonneg (Int.natCast_nonneg label.k)
        (sub_nonneg.mpr (hc key).2),
        mul_nonneg (sub_nonneg.mpr hK) hC0]
  dsimp [contractionExpr, subExpr, scaleExpr, startExpr]
  constructor
  · nlinarith [hke.1, hn.2, hprod]
  constructor
  · nlinarith [hke.2, hn.1, hprod]
  · intro key
    have hec := hcoeff key
    have hnc' := hnc key
    constructor <;> nlinarith

end Paper.F7Contraction

/- END Global.lean -/

/- BEGIN Rows.lean source_sha256=2d53c4ed46a4461d5c40fd6432679491bb88383472e0c278198db6c69bca9ed3 body_sha256=6af16e003d744213447163b30164226ad4586aa717e575a834fbf0859c3e3342 -/

namespace Paper.F7Contraction

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPSystem Paper.F6ILPCost
open Paper.F7Size Paper.F7QControl Paper.AffineNat

theorem contractionRows_bounds_aux {keys : Finset Nat}
    (labels : List Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys)
    (e : AffineExpr keys) (P U K B0 C0 : ℤ)
    (hU : 0 ≤ U) (hK0 : 0 ≤ K) (hB0 : 0 ≤ B0) (hC0 : 0 ≤ C0)
    (hcontrol : Controlled U K P labels)
    (he : -B0 ≤ e.intercept ∧ e.intercept ≤ B0)
    (hc : ∀ key, 0 ≤ e.coeff key ∧ e.coeff key ≤ C0) :
    (contractionRows P e labels hkeys).Forall
      (fun row =>
        -((K + 1) * (B0 + 2 * U * K * labels.length) + U) ≤ row.intercept ∧
        row.intercept ≤ (K + 1) * (B0 + 2 * U * K * labels.length) + U ∧
        (∀ key,
          -((K + 1) * (C0 + U * labels.length)) ≤ row.coeff key ∧
          row.coeff key ≤ (K + 1) * (C0 + U * labels.length))) := by
  induction labels generalizing e P B0 C0 with
  | nil => simp [contractionRows]
  | cons label rest ih =>
      let hk := hkeys label (by simp)
      let next := stepExpr e P label hk
      let hrest : ∀ q ∈ rest, q.k ∈ keys := by
        intro q hq
        exact hkeys q (by simp [hq])
      have hnext := step_constant_bounds e P U K B0 label hk
        hcontrol.1 hcontrol.2.1 hcontrol.2.2.1 he
      have hnextCoeff := step_coeff_nonneg_le e P U C0
        label hk hcontrol.1 hcontrol.2.1 hc
      have hBK : 0 ≤ 2 * U * K := by positivity
      have hBgrow : B0 + 2 * U * K ≤
          B0 + 2 * U * K * (label :: rest).length := by
        simp only [List.length_cons, Nat.cast_succ]
        nlinarith [mul_nonneg hBK (Int.natCast_nonneg rest.length)]
      have hCgrow : C0 + U ≤ C0 + U * (label :: rest).length := by
        simp only [List.length_cons, Nat.cast_succ]
        nlinarith [mul_nonneg hU (Int.natCast_nonneg rest.length)]
      have hBtotal0 : 0 ≤ B0 + 2 * U * K * (label :: rest).length := by
        positivity
      have hCurrent :
          -(B0 + 2 * U * K * (label :: rest).length) ≤ e.intercept ∧
          e.intercept ≤ B0 + 2 * U * K * (label :: rest).length := by
        constructor <;> nlinarith [he.1, he.2, hBgrow]
      have hNext :
          -(B0 + 2 * U * K * (label :: rest).length) ≤ next.intercept ∧
          next.intercept ≤ B0 + 2 * U * K * (label :: rest).length := by
        constructor <;> nlinarith [hnext.1, hnext.2, hBgrow]
      have hcCurrent : ∀ key, 0 ≤ e.coeff key ∧
          e.coeff key ≤ C0 + U * (label :: rest).length := by
        intro key
        have h := hc key
        constructor <;> nlinarith [hCgrow]
      have hcNext : ∀ key, 0 ≤ next.coeff key ∧
          next.coeff key ≤ C0 + U * (label :: rest).length := by
        intro key
        have h := hnextCoeff key
        constructor <;> nlinarith [hCgrow]
      have hhead := contractionExpr_global e next P U K
        (B0 + 2 * U * K * (label :: rest).length)
        (C0 + U * (label :: rest).length) label
        hcontrol.1 hcontrol.2.1 hcontrol.2.2.1 hBtotal0
        hCurrent hNext hcCurrent hcNext
      have htail := ih hrest next (P * label.k)
        (B0 + 2 * U * K) (C0 + U)
        (by positivity) (by positivity)
        hcontrol.2.2.2
        (by simpa only [add_assoc] using hnext)
        (by intro key; exact hnextCoeff key)
      have htail' : (contractionRows (P * label.k) next rest hrest).Forall
          (fun row =>
            -((K + 1) * (B0 + 2 * U * K * (label :: rest).length) + U) ≤
              row.intercept ∧
            row.intercept ≤
              (K + 1) * (B0 + 2 * U * K * (label :: rest).length) + U ∧
            (∀ key,
              -((K + 1) * (C0 + U * (label :: rest).length)) ≤
                row.coeff key ∧
              row.coeff key ≤ (K + 1) *
                (C0 + U * (label :: rest).length))) := by
        convert htail using 1 <;>
          simp only [List.length_cons, Nat.cast_succ] <;> ring
      simpa only [contractionRows, List.forall_cons] using
        And.intro hhead htail'

end Paper.F7Contraction

/- END Rows.lean -/

/- BEGIN Root.lean source_sha256=9153a9a246278c593ea7747beb2e279a028390f351712a2cad5faab834aae403 body_sha256=e36e5e499864aea0bff5ab81061d031c575834a08061b9225b2cf6a248e652a1 -/

namespace Paper.F7Contraction

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPSystem Paper.F6ILPCost
open Paper.F7Size Paper.F7QControl Paper.AffineNat

theorem contractionRoot_bounds (labels : List Label) (x n : ℤ)
    (U K : Nat) (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hn : 0 ≤ n) (hx : -n ≤ x ∧ x ≤ n) :
    (contractionRoot labels x).Forall
      (fun row =>
        -(((K : ℤ) + 1) *
            (n + 2 * (U : ℤ) * K * labels.length) + U) ≤
          row.intercept ∧
        row.intercept ≤
          ((K : ℤ) + 1) *
            (n + 2 * (U : ℤ) * K * labels.length) + U ∧
        (∀ key,
          -(((K : ℤ) + 1) * (U : ℤ) * labels.length) ≤
            row.coeff key ∧
          row.coeff key ≤
            ((K : ℤ) + 1) * (U : ℤ) * labels.length)) := by
  have hcontrol : Controlled U K 1 labels :=
    controlled_of_qWord U K 1 labels (by simpa using hbudget) hK
  have hroot : -n ≤ (rootExpr labels x).intercept ∧
      (rootExpr labels x).intercept ≤ n := by
    simpa only [rootExpr, startExpr] using hx
  have hc : ∀ key, 0 ≤ (rootExpr labels x).coeff key ∧
      (rootExpr labels x).coeff key ≤ (0 : ℤ) := by
    intro key
    simp [rootExpr, startExpr]
  have haux := contractionRows_bounds_aux labels (keyProof labels)
    (rootExpr labels x) 1 U K n 0
    (Int.natCast_nonneg U) (Int.natCast_nonneg K) hn (by decide)
    hcontrol hroot hc
  simpa only [contractionRoot, zero_add, mul_assoc] using haux

end Paper.F7Contraction
/- END Root.lean -/

/- BEGIN Rows.lean source_sha256=57c9fdbed74aa1699e7db55aacfaec3b551751f974f9ff1d0526c22bb41f4f93 body_sha256=0cc845589287c00a838c27b2e14c24ab64074aac88ea419587f6a86a26cf92d4 -/

namespace Paper.F7Semantics

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F6ILPFeasible Paper.F7Encoding Paper.F7Computable
open Paper.AffineNat

theorem usedKeys_complete (labels : List Label) (key : Variable labels) :
    key ∈ usedKeys labels := by
  unfold usedKeys
  simp only [List.mem_map, List.mem_attach, true_and]
  have hm : key.val ∈ (labels.map Label.k).dedup := by
    simpa only [List.mem_dedup, usedArities, List.mem_toFinset] using key.property
  refine ⟨⟨key.val, hm⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem evalInt_lowerRow {keys : Finset Nat}
    (key : { k : Nat // k ∈ keys }) (lo : Nat → Nat)
    (values : { k : Nat // k ∈ keys } → ℤ) :
    evalInt (lowerRow key lo) values = values key - lo key.val := by
  simp [evalInt, lowerRow, Finset.sum_ite_eq']; ring

theorem evalInt_upperRow {keys : Finset Nat}
    (key : { k : Nat // k ∈ keys }) (hi : Nat → Nat)
    (values : { k : Nat // k ∈ keys } → ℤ) :
    evalInt (upperRow key hi) values = hi key.val - values key := by
  simp [evalInt, upperRow, Finset.sum_ite_eq']; ring

theorem boundRows_iff {keys : Finset Nat}
    (lo hi : Nat → Nat) (ks : List { k : Nat // k ∈ keys })
    (values : { k : Nat // k ∈ keys } → ℤ) :
    (boundRows lo hi ks).Forall (fun row => 0 ≤ evalInt row values) ↔
      ∀ key ∈ ks, (lo key.val : ℤ) ≤ values key ∧
        values key ≤ (hi key.val : ℤ) := by
  induction ks with
  | nil => simp [boundRows]
  | cons key rest ih =>
      simp only [boundRows, List.forall_cons, List.mem_cons]
      rw [evalInt_lowerRow, evalInt_upperRow, ih]
      constructor
      · rintro ⟨hl, hu, hrest⟩ q (hq | hq)
        · subst q
          constructor <;> omega
        · exact hrest q hq
      · intro h
        have hk := h key (Or.inl rfl)
        refine ⟨by omega, by omega, ?_⟩
        intro q hq
        exact h q (Or.inr hq)

theorem systemRowsC_iff_feasible (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat)
    (values : Variable labels → ℤ) :
    (systemRowsC labels x z c lo hi price N T).Forall
      (fun row => 0 ≤ evalInt row values) ↔
        Feasible labels x z c lo hi price N T values := by
  have hscale : evalInt (scaleExpr (-1) (terminalRow labels x z)) values =
      -evalInt (terminalRow labels x z) values := by
    simp [evalInt, scaleExpr, Finset.mul_sum]
    ring
  have hb : (∀ key ∈ usedKeys labels,
      (lo key.val : ℤ) ≤ values key ∧ values key ≤ (hi key.val : ℤ)) ↔
      ∀ key : Variable labels,
        (lo key.val : ℤ) ≤ values key ∧ values key ≤ (hi key.val : ℤ) := by
    constructor
    · intro h key
      exact h key (usedKeys_complete labels key)
    · intro h key _
      exact h key
  have heq : (0 ≤ evalInt (terminalRow labels x z) values ∧
      0 ≤ -evalInt (terminalRow labels x z) values) ↔
      evalInt (terminalRow labels x z) values = 0 := by omega
  simp only [systemRowsC, List.forall_append, List.forall_cons,
    and_true, boundRows_iff, hscale, Feasible]
  simp only [← and_assoc]
  rw [heq, hb]
  simp
end Paper.F7Semantics





/- END Rows.lean -/

/- BEGIN Sum.lean source_sha256=9a76b7ec7b2c0e18a5daf6ce5332920b726f50884e65c8c5293b58e73e29ddf5 body_sha256=ce701293b06384875f156559edea4df1e1d550497d89f8f184e602786260b2e1 -/

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.AffineNat

def AbsBound {keys : Finset Nat} (e : AffineExpr keys) (A C : ℤ) : Prop :=
  -A ≤ e.intercept ∧ e.intercept ≤ A ∧
    ∀ key, -C ≤ e.coeff key ∧ e.coeff key ≤ C

theorem absBound_add {keys : Finset Nat} (e f : AffineExpr keys)
    (A B C D : ℤ) (he : AbsBound e A C)
    (hf : AbsBound f B D) :
    AbsBound (addExpr e f) (A + B) (C + D) := by
  unfold AbsBound at *
  simp only [addExpr]
  constructor
  · omega
  constructor
  · omega
  · intro key
    have hec := he.2.2 key
    have hfc := hf.2.2 key
    constructor <;> omega

def TermBounded {keys : Finset Nat}
    (D : ℤ) (c : Nat → Nat) (A C : ℤ)
    (N : Nat) (P : ℤ) (e : AffineExpr keys) :
    (labels : List Label) →
    (∀ label ∈ labels, label.k ∈ keys) → Prop
  | [], _ => True
  | label :: rest, hkeys =>
      let next := stepExpr e P label (hkeys label (by simp))
      let term := scaleExpr (8 * (N : ℤ) * (c label.k : ℤ))
        (subExpr (scaleExpr (D / (P * label.k)) next)
          (startExpr keys D))
      AbsBound term A C ∧
        TermBounded D c A C (N * (2 * (label.k - 1) + 1))
          (P * label.k) next rest
          (by intro q hq; exact hkeys q (by simp [hq]))

theorem clearedExpr_sum_bound {keys : Finset Nat}
    (D : ℤ) (c : Nat → Nat) (A C : ℤ)
    (N : Nat) (P : ℤ) (e : AffineExpr keys)
    (labels : List Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hterms : TermBounded D c A C N P e labels hkeys) :
    AbsBound (clearedExpr D c N P e labels hkeys)
      (labels.length * A) (labels.length * C) := by
  induction labels generalizing N P e with
  | nil =>
      simp [clearedExpr, AbsBound, startExpr, hA, hC]
  | cons label rest ih =>
      let hk := hkeys label (by simp)
      let next := stepExpr e P label hk
      let hrest : ∀ q ∈ rest, q.k ∈ keys := by
        intro q hq
        exact hkeys q (by simp [hq])
      let term := scaleExpr (8 * (N : ℤ) * (c label.k : ℤ))
        (subExpr (scaleExpr (D / (P * label.k)) next)
          (startExpr keys D))
      have hhead : AbsBound term A C := hterms.1
      have htail := ih (N * (2 * (label.k - 1) + 1))
        (P * label.k) next hrest hterms.2
      have hadd := absBound_add term
        (clearedExpr D c (N * (2 * (label.k - 1) + 1))
          (P * label.k) next rest hrest)
        A (rest.length * A) C (rest.length * C) hhead htail
      convert hadd using 1 <;>
        simp only [clearedExpr, List.length_cons, Nat.cast_succ] <;> ring

end Paper.F7Budget
/- END Sum.lean -/

/- BEGIN Step.lean source_sha256=c6bd031ef6f38a7c201981d84f4489bbd77ce0838ddc251fa5221fe9ec2a9336 body_sha256=3a97c811a9b0d36c11e9c5faa9ea0ec7081bb4194b5b9aac02e5ff7ff379dbda -/

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.AffineNat

theorem clearedTerm_bound {keys : Finset Nat}
    (next : AffineExpr keys) (D Q : ℤ)
    (N c U H B C : Nat)
    (hD : 0 ≤ D ∧ D ≤ U)
    (hQ : 0 ≤ Q ∧ Q ≤ U)
    (hN : N ≤ U) (hc : c ≤ H)
    (hB :
      -((B : Nat) : ℤ) ≤ next.intercept ∧ next.intercept ≤ B)
    (hC : ∀ key, 0 ≤ next.coeff key ∧ next.coeff key ≤ C) :
    AbsBound
      (scaleExpr (8 * (N : ℤ) * c)
        (subExpr (scaleExpr Q next) (startExpr keys D)))
      (8 * (U : ℤ) * H * U * (B + 1))
      (8 * (U : ℤ) * H * U * C) := by
  have hU : 0 ≤ (U : ℤ) := Int.natCast_nonneg _
  have hH : 0 ≤ (H : ℤ) := Int.natCast_nonneg _
  have hBn : 0 ≤ (B : ℤ) := Int.natCast_nonneg _
  have hCn : 0 ≤ (C : ℤ) := Int.natCast_nonneg _
  have hN0 : 0 ≤ (N : ℤ) := Int.natCast_nonneg _
  have hc0 : 0 ≤ (c : ℤ) := Int.natCast_nonneg _
  have hNle : (N : ℤ) ≤ U := by exact_mod_cast hN
  have hcle : (c : ℤ) ≤ H := by exact_mod_cast hc
  let S : ℤ := 8 * N * c
  let Smax : ℤ := 8 * U * H
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hSle : S ≤ Smax := by
    have h1 : (N : ℤ) * c ≤ U * c :=
      mul_le_mul_of_nonneg_right hNle hc0
    have h2 : (U : ℤ) * c ≤ U * H :=
      mul_le_mul_of_nonneg_left hcle hU
    dsimp [S, Smax]
    nlinarith
  have hinner : -(U * (B + 1) : ℤ) ≤ Q * next.intercept - D ∧
      Q * next.intercept - D ≤ U * (B + 1) := by
    have hqplus := mul_nonneg hQ.1 (sub_nonneg.mpr hB.2)
    have hqminus := mul_nonneg hQ.1 (sub_nonneg.mpr hB.1)
    have hqU := mul_nonneg (sub_nonneg.mpr hQ.2) hBn
    constructor <;> nlinarith
  have hinnerCoeff : ∀ key, 0 ≤ Q * next.coeff key ∧
      Q * next.coeff key ≤ (U : ℤ) * C := by
    intro key
    constructor
    · exact mul_nonneg hQ.1 (hC key).1
    · nlinarith [mul_nonneg hQ.1 (sub_nonneg.mpr (hC key).2),
        mul_nonneg (sub_nonneg.mpr hQ.2) hCn]
  unfold AbsBound
  dsimp [scaleExpr, subExpr, startExpr]
  constructor
  · nlinarith [mul_nonneg hS0 (sub_nonneg.mpr hinner.1),
      mul_nonneg (sub_nonneg.mpr hSle) (by positivity : 0 ≤ (U : ℤ) * (B + 1))]
  constructor
  · nlinarith [mul_nonneg hS0 (sub_nonneg.mpr hinner.2),
      mul_nonneg (sub_nonneg.mpr hSle) (by positivity : 0 ≤ (U : ℤ) * (B + 1))]
  · intro key
    have hk := hinnerCoeff key
    constructor
    · nlinarith [mul_nonneg hS0 hk.1]
    · nlinarith [mul_nonneg hS0 (sub_nonneg.mpr hk.2),
        mul_nonneg (sub_nonneg.mpr hSle) (by positivity : 0 ≤ (U : ℤ) * C)]

end Paper.F7Budget
/- END Step.lean -/

/- BEGIN Actual.lean source_sha256=cf10d04cb54ad89facd50316de03ac7bd2b1f07e595e860bb7a6f6e02904ffa7 body_sha256=5c9ce586a791c58fa95660dd323a696d2a4bef037e995704c08e0622cf137219 -/

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.AffineNat
open Paper.F6ILPSystem Paper.AffineILP
open Paper.F7Size Paper.F7QControl
open Paper.F7Products

theorem quotient_budget_bound (D P : ℤ) (k U : Nat)
    (hD : 0 ≤ D ∧ D ≤ U) (hP : 0 < P) (hk : 1 ≤ k) :
    0 ≤ D / (P * k) ∧ D / (P * k) ≤ U := by
  have hden : 0 ≤ P * (k : ℤ) := by positivity
  exact ⟨Int.ediv_nonneg hD.1 hden,
    le_trans (Int.ediv_le_self _ hD.1) hD.2⟩

theorem n_le_of_qBudget (U N : Nat) (labels : List Label)
    (hbudget : N * qWord labels ≤ U) : N ≤ U := by
  have h := Nat.mul_le_mul_left N (qWord_pos labels)
  have hh : N ≤ N * qWord labels := by
    simpa only [mul_one] using h
  exact le_trans hh hbudget

theorem termBounded_of_budget_aux {keys : Finset Nat}
    (D : ℤ) (c : Nat → Nat) (N : Nat) (P : ℤ)
    (e : AffineExpr keys) (labels : List Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys)
    (U K H B0 C0 : Nat)
    (hD : 0 ≤ D ∧ D ≤ U) (hP : 0 < P)
    (hcontrol : Controlled U K P labels)
    (hbudget : N * qWord labels ≤ U)
    (hcap : ∀ label ∈ labels, c label.k ≤ H)
    (he : -(B0 : ℤ) ≤ e.intercept ∧ e.intercept ≤ B0)
    (hc : ∀ key, 0 ≤ e.coeff key ∧ e.coeff key ≤ C0) :
    TermBounded D c
      (8 * (U : ℤ) * H * U * (B0 + 2 * U * K * labels.length + 1))
      (8 * (U : ℤ) * H * U * (C0 + U * labels.length))
      N P e labels hkeys := by
  induction labels generalizing N P e B0 C0 with
  | nil =>
      simp [TermBounded]
  | cons label rest ih =>
      let hk := hkeys label (by simp)
      let next := stepExpr e P label hk
      let hrest : ∀ q ∈ rest, q.k ∈ keys := by
        intro q hq
        exact hkeys q (by simp [hq])
      have hnext := step_constant_bounds e P U K B0 label hk
        (le_of_lt hP) hcontrol.2.1 hcontrol.2.2.1 he
      have hnextCoeff := step_coeff_nonneg_le e P U C0 label hk
        (le_of_lt hP) hcontrol.2.1 hc
      have hBrow : (B0 : ℤ) + 2 * U * K ≤
          B0 + 2 * U * K * (label :: rest).length := by
        simp only [List.length_cons, Nat.cast_succ]
        nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℤ) * U * K)
          (Int.natCast_nonneg rest.length)]
      have hCrow : (C0 : ℤ) + U ≤
          C0 + U * (label :: rest).length := by
        simp only [List.length_cons, Nat.cast_succ]
        nlinarith [mul_nonneg (Int.natCast_nonneg U)
          (Int.natCast_nonneg rest.length)]
      have hnextB :
          -((B0 + 2 * U * K * (label :: rest).length : Nat) : ℤ) ≤
              next.intercept ∧
          next.intercept ≤
              ((B0 + 2 * U * K * (label :: rest).length : Nat) : ℤ) := by
        have hbig : ((B0 + 2 * U * K : Nat) : ℤ) ≤
            ((B0 + 2 * U * K * (label :: rest).length : Nat) : ℤ) := by
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
            using hBrow
        have hsmall : -((B0 + 2 * U * K : Nat) : ℤ) ≤
            next.intercept ∧
            next.intercept ≤ ((B0 + 2 * U * K : Nat) : ℤ) := by
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
            using hnext
        exact ⟨le_trans (neg_le_neg hbig) hsmall.1,
          le_trans hsmall.2 hbig⟩
      have hnextC : ∀ key, 0 ≤ next.coeff key ∧
          next.coeff key ≤
            ((C0 + U * (label :: rest).length : Nat) : ℤ) := by
        intro key
        have hbig : ((C0 + U : Nat) : ℤ) ≤
            ((C0 + U * (label :: rest).length : Nat) : ℤ) := by
          simpa only [Nat.cast_add, Nat.cast_mul] using hCrow
        have hsmall : 0 ≤ next.coeff key ∧
            next.coeff key ≤ ((C0 + U : Nat) : ℤ) := by
          simpa only [Nat.cast_add] using hnextCoeff key
        exact ⟨hsmall.1, le_trans hsmall.2 hbig⟩
      have hQ := quotient_budget_bound D P label.k U hD hP
        (Nat.le_trans (by decide : 1 ≤ 2) label.hk)
      have hN : N ≤ U := n_le_of_qBudget U N _ hbudget
      have hhead := clearedTerm_bound next D (D / (P * label.k))
        N (c label.k) U H
        (B0 + 2 * U * K * (label :: rest).length)
        (C0 + U * (label :: rest).length)
        hD hQ hN (hcap label (by simp)) hnextB hnextC
      have hq : 2 * (label.k - 1) + 1 = 2 * label.k - 1 := by
        have hk2 := label.hk
        omega
      have htailBudget :
          (N * (2 * (label.k - 1) + 1)) * qWord rest ≤ U := by
        simpa only [qWord, hq, mul_assoc] using hbudget
      have htailCap : ∀ q ∈ rest, c q.k ≤ H := by
        intro q hqmem
        exact hcap q (by simp [hqmem])
      have hkpos : (0 : ℤ) < label.k := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) label.hk)
      have hPnext : 0 < P * label.k := mul_pos hP hkpos
      have htail := ih (N * (2 * (label.k - 1) + 1))
        (P * label.k) next hrest (B0 + 2 * U * K) (C0 + U)
        hPnext hcontrol.2.2.2 htailBudget htailCap
        (by simpa only [Nat.cast_add, Nat.cast_mul] using hnext)
        (by intro key; simpa only [Nat.cast_add] using hnextCoeff key)
      have htail' : TermBounded D c
          (8 * (U : ℤ) * H * U *
            (B0 + 2 * U * K * (label :: rest).length + 1))
          (8 * (U : ℤ) * H * U *
            (C0 + U * (label :: rest).length))
          (N * (2 * (label.k - 1) + 1)) (P * label.k)
          next rest hrest := by
        convert htail using 1 <;>
          simp only [List.length_cons, Nat.cast_succ, Nat.cast_add,
            Nat.cast_mul] <;> ring
      exact ⟨hhead, htail'⟩

theorem clearedRoot_bound (labels : List Label) (x : ℤ)
    (c : Nat → Nat) (U K H n : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hcap : ∀ label ∈ labels, c label.k ≤ H)
    (hx : -((n : Nat) : ℤ) ≤ x ∧ x ≤ n) :
    AbsBound
      (clearedExpr
        (terminalProduct 1
          (labels.map (instantiate (fun _ => 0))))
        c 1 1 (rootExpr labels x) labels (keyProof labels))
      (labels.length *
        (8 * (U : ℤ) * H * U *
          (n + 2 * U * K * labels.length + 1)))
      (labels.length *
        (8 * (U : ℤ) * H * U *
          (U * labels.length))) := by
  let D := terminalProduct 1
    (labels.map (instantiate (fun _ => 0)))
  have hD : 0 ≤ D ∧ D ≤ U := by
    constructor
    · exact le_of_lt (Paper.F6Cleared.terminalProduct_pos
        1 _ (by decide))
    · exact terminalProduct_le_typed_budget U (fun _ => 0)
        labels hbudget
  have hcontrol : Controlled U K 1 labels :=
    controlled_of_qWord U K 1 labels
      (by simpa using hbudget) hK
  have hroot : -(n : ℤ) ≤ (rootExpr labels x).intercept ∧
      (rootExpr labels x).intercept ≤ n := by
    simpa only [rootExpr, startExpr] using hx
  have hc : ∀ key, 0 ≤ (rootExpr labels x).coeff key ∧
      (rootExpr labels x).coeff key ≤ (0 : ℤ) := by
    intro key
    simp [rootExpr, startExpr]
  have hterms := termBounded_of_budget_aux D c 1 1
    (rootExpr labels x) labels (keyProof labels)
    U K H n 0 hD (by decide) hcontrol
    (by simpa using hbudget) hcap hroot hc
  have hA : 0 ≤ 8 * (U : ℤ) * H * U *
      (n + 2 * U * K * labels.length + 1) := by positivity
  have hC : 0 ≤ 8 * (U : ℤ) * H * U *
      (0 + U * labels.length) := by positivity
  have hsum := clearedExpr_sum_bound D c
    (8 * (U : ℤ) * H * U *
      (n + 2 * U * K * labels.length + 1))
    (8 * (U : ℤ) * H * U *
      (0 + U * labels.length))
    1 1 (rootExpr labels x) labels (keyProof labels)
    hA hC hterms
  simpa only [D, zero_add] using hsum

theorem shared_charge_cap (labels : List Label)
    (c : Nat → Nat) (K : Nat)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hlabelCap : ∀ label ∈ labels, label.c ≤ 27 * label.k ^ 3)
    (hshared : ∀ label ∈ labels, label.c = c label.k) :
    ∀ label ∈ labels, c label.k ≤ 27 * K ^ 3 := by
  intro label hmem
  have hpower := Nat.pow_le_pow_left (hK label hmem) 3
  have hbound := hlabelCap label hmem
  rw [hshared label hmem] at hbound
  exact le_trans hbound (Nat.mul_le_mul_left 27 hpower)

end Paper.F7Budget
/- END Actual.lean -/

/- BEGIN Leaf.lean source_sha256=5a47ce612de835e889b48a0291992e4158c837df2341f636af75f949e7711e51 body_sha256=080426c96e1beb23c2260fb7704d3042c6d9fbd6f78326f86d08def7790e64e2 -/

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F6Objective Paper.AffineNat Paper.AffineILP Paper.PPEndToEnd

theorem budgetRow_bounds_from_cleared
    (labels : List Label) (x z : ℤ) (c : Nat → Nat)
    (price : Nat → Nat) (N T U L S R : Nat)
    (hD : terminalProduct 1
      (labels.map (instantiate (fun _ => 0))) ≤ U)
    (hT : T ≤ U)
    (hLeaf : leafPP price (finalN N labels) z.toNat ≤ L)
    (hCleared :
      -(S : ℤ) ≤
        (clearedExpr (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
          c N 1 (rootExpr labels x) labels (keyProof labels)).intercept ∧
      (clearedExpr (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
        c N 1 (rootExpr labels x) labels (keyProof labels)).intercept ≤ S ∧
      (∀ key, -(R : ℤ) ≤
        (clearedExpr (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
          c N 1 (rootExpr labels x) labels (keyProof labels)).coeff key ∧
        (clearedExpr (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
          c N 1 (rootExpr labels x) labels (keyProof labels)).coeff key ≤ R)) :
    -((U : ℤ) * (U + L) + S) ≤
        (budgetRow labels x z c price N T).intercept ∧
      (budgetRow labels x z c price N T).intercept ≤
        (U : ℤ) * (U + L) + S ∧
      (∀ key, -(R : ℤ) ≤ (budgetRow labels x z c price N T).coeff key ∧
        (budgetRow labels x z c price N T).coeff key ≤ R) := by
  let D := terminalProduct 1 (labels.map (instantiate (fun _ => 0)))
  let leaf := leafPP price (finalN N labels) z.toNat
  let e := clearedExpr D c N 1 (rootExpr labels x)
    labels (keyProof labels)
  have hD0 : 0 ≤ D := le_of_lt (Paper.F6Cleared.terminalProduct_pos
    1 _ (by decide))
  have hDle : D ≤ (U : ℤ) := hD
  have hT0 : 0 ≤ (T : ℤ) := Int.natCast_nonneg _
  have hTle : (T : ℤ) ≤ U := by exact_mod_cast hT
  have hL0 : 0 ≤ (leaf : ℤ) := Int.natCast_nonneg _
  have hLle : (leaf : ℤ) ≤ L := by exact_mod_cast hLeaf
  have hroot : -((U : ℤ) * (U + L)) ≤ D * ((T : ℤ) - leaf) ∧
      D * ((T : ℤ) - leaf) ≤ (U : ℤ) * (U + L) := by
    constructor
    · nlinarith [mul_nonneg hD0 hT0,
        mul_nonneg (sub_nonneg.mpr hDle) hL0,
        mul_nonneg (Int.natCast_nonneg U) (sub_nonneg.mpr hLle)]
    · nlinarith [mul_nonneg hD0 hL0,
        mul_nonneg (sub_nonneg.mpr hDle) hT0,
        mul_nonneg (Int.natCast_nonneg U) (sub_nonneg.mpr hTle)]
  have he : -(S : ℤ) ≤ e.intercept ∧ e.intercept ≤ S ∧
      (∀ key, -(R : ℤ) ≤ e.coeff key ∧ e.coeff key ≤ R) := hCleared
  have hBudgetInt : (budgetRow labels x z c price N T).intercept =
      D * ((T : ℤ) - leaf) - e.intercept := by
    simp only [budgetRow, subExpr, startExpr]
    rfl
  have hBudgetCoeff : ∀ key,
      (budgetRow labels x z c price N T).coeff key = -e.coeff key := by
    intro key
    simp only [budgetRow, subExpr, startExpr, zero_sub]
    rfl
  constructor
  · rw [hBudgetInt]
    omega
  constructor
  · rw [hBudgetInt]
    omega
  · intro key
    have h := he.2.2 key
    rw [hBudgetCoeff]
    constructor <;> omega

end Paper.F7Budget

/- END Leaf.lean -/

/- BEGIN Magnitude.lean source_sha256=cb9778dc1dcb0e9ca4ecf32bb2a60fede968c5f70c8b5b21195b6717d0179c2d body_sha256=dcd7d40315e09931888cb29a4641e3ba19d626ee1a62d0a2b95b9dfd68037165 -/

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F6Objective Paper.AffineNat Paper.AffineILP Paper.F7QControl Paper.F7Products Paper.PPEndToEnd

theorem budgetRoot_bound (labels : List Label) (x z : ℤ)
    (c : Nat → Nat) (price : Nat → Nat)
    (T U K H n L : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hcap : ∀ label ∈ labels, c label.k ≤ H)
    (hx : -(n : ℤ) ≤ x ∧ x ≤ n)
    (hT : T ≤ U)
    (hLeaf : leafPP price (finalN 1 labels) z.toNat ≤ L) :
    let S : Nat := labels.length *
      (8 * U * H * U *
        (n + 2 * U * K * labels.length + 1));
    let R : Nat := labels.length *
      (8 * U * H * U * (U * labels.length));
    -((U : ℤ) * (U + L) + S) ≤
        (budgetRow labels x z c price 1 T).intercept ∧
      (budgetRow labels x z c price 1 T).intercept ≤
        (U : ℤ) * (U + L) + S ∧
      (∀ key, -(R : ℤ) ≤ (budgetRow labels x z c price 1 T).coeff key ∧
        (budgetRow labels x z c price 1 T).coeff key ≤ R) := by
  have hD := terminalProduct_le_typed_budget U (fun _ => 0)
    labels hbudget
  have hCleared := clearedRoot_bound labels x c U K H n
    hbudget hK hcap hx
  have hCleared' :
      -((labels.length *
        (8 * U * H * U * (n + 2 * U * K * labels.length + 1)) : Nat) : ℤ) ≤
          (clearedExpr
            (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
            c 1 1 (rootExpr labels x) labels (keyProof labels)).intercept ∧
      (clearedExpr
        (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
        c 1 1 (rootExpr labels x) labels (keyProof labels)).intercept ≤
          (labels.length *
            (8 * U * H * U * (n + 2 * U * K * labels.length + 1)) : Nat) ∧
      (∀ key,
        -((labels.length * (8 * U * H * U * (U * labels.length)) : Nat) : ℤ) ≤
          (clearedExpr
            (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
            c 1 1 (rootExpr labels x) labels (keyProof labels)).coeff key ∧
        (clearedExpr
          (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
          c 1 1 (rootExpr labels x) labels (keyProof labels)).coeff key ≤
            (labels.length * (8 * U * H * U * (U * labels.length)) : Nat)) := by
    simpa only [AbsBound, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] using hCleared
  exact budgetRow_bounds_from_cleared labels x z c price 1 T U L
    (labels.length *
      (8 * U * H * U * (n + 2 * U * K * labels.length + 1)))
    (labels.length * (8 * U * H * U * (U * labels.length)))
    hD hT hLeaf hCleared'

end Paper.F7Budget
/- END Magnitude.lean -/

/- BEGIN Bound.lean source_sha256=51c234cbe6e1be2059287625246f46b26e8abc854229c9248f1737d6a9467a08 body_sha256=2f87920c7de01e1f9bb21f9985bfdb86302a4443010f76181246cbdf4f36c67e -/

namespace Paper.F7LeafCanon

open Paper.AffineNat Paper.F6Objective Paper.F7Products Paper.F7QControl
open Paper.PPEndToEnd Paper.CountStage.StopBudget

theorem leaf_tauExact_le (N z U : Nat)
    (hN : N ≤ U) (hz : z ≤ U) :
    leafPP tauExact N z ≤ 2004 * (U + 1) ^ 6 := by
  let R := N * z ^ 2
  have hR : R ≤ U ^ 3 := by
    dsimp [R]
    have hz2 : z ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hz 2
    have hm := Nat.mul_le_mul hN hz2
    simpa [pow_succ, pow_zero, mul_assoc] using hm
  have htau := tauExact_le_thousand_mul_succ R
  have hleaf : leafPP tauExact N z ≤ 4 * R + R * (1000 * (R + 1)) := by
    unfold leafPP R
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ htau) _
  have hcube : U ^ 3 ≤ (U + 1) ^ 3 :=
    Nat.pow_le_pow_left (Nat.le_succ U) 3
  have hcube1 : 1 ≤ (U + 1) ^ 3 := by
    have hpos : 0 < (U + 1) ^ 3 := by positivity
    omega
  have hpoly : 4 * R + R * (1000 * (R + 1)) ≤
      2004 * (U + 1) ^ 6 := by
    have hRbig : R ≤ (U + 1) ^ 3 := le_trans hR hcube
    have h1 : 4 * R ≤ 4 * (U + 1) ^ 3 :=
      Nat.mul_le_mul_left 4 hRbig
    have h2 : R * (1000 * (R + 1)) ≤
        (U + 1) ^ 3 * (1000 * ((U + 1) ^ 3 + 1)) := by
      gcongr
    have h3 : (U + 1) ^ 3 * (1000 * ((U + 1) ^ 3 + 1)) ≤
        2000 * (U + 1) ^ 6 := by
      have hCubeSq : (U + 1) ^ 6 = ((U + 1) ^ 3) ^ 2 := by ring
      nlinarith [hCubeSq]
    nlinarith [h1, h2, h3]
  exact hleaf.trans hpoly

theorem canonical_leaf_bound (labels : List Label) (U z : Nat)
    (hbudget : qWord labels ≤ U) (hz : z ≤ U) :
    leafPP tauExact (finalN 1 labels) z ≤ 2004 * (U + 1) ^ 6 := by
  apply leaf_tauExact_le _ _ U
  · exact finalN_le_budget labels U hbudget
  · exact hz

end Paper.F7LeafCanon

/- END Bound.lean -/

/- BEGIN Size4.lean source_sha256=4d2bffa0786afde6174f38451c81500b56b3ca7500b1a882cca2aa21c9a4c0c0 body_sha256=4309a5fe74995e8692c6bdd059d46c7c46b8a55fea2808d4fe614a4d109ac957 -/

namespace Paper.CountStage.StopBudget

open Paper.CountStage.TypedDecorationWords
open Paper.CountStage.TypedWordRuntime

/-- The executable typed alphabet has a fixed-degree size bound in numeric K. -/
theorem decorationLabels_length_le_numeric (K : Nat) :
    (decorationLabels K).length ≤ 28 * (K + 1) ^ 6 := by
  have hlen : (decorationLabels K).length =
      ((List.range (K - 1)).map fun i =>
        (i + 2) ^ 2 * (27 * (i + 2) ^ 3 + 1)).sum := by
    simp [decorationLabels, List.length_flatMap, labelsAt_length,
      Paper.CountStage.Decoration.B]
  have hterm : ∀ i ∈ List.range (K - 1),
      (i + 2) ^ 2 * (27 * (i + 2) ^ 3 + 1) ≤ 28 * (K + 1) ^ 5 := by
    intro i hi
    have hik : i + 2 ≤ K + 1 := by
      simp only [List.mem_range] at hi
      omega
    have h2 : (i + 2) ^ 2 ≤ (K + 1) ^ 2 := by gcongr
    have h3 : (i + 2) ^ 3 ≤ (K + 1) ^ 3 := by gcongr
    have htail : 27 * (i + 2) ^ 3 + 1 ≤ 28 * (K + 1) ^ 3 := by
      have hmul := Nat.mul_le_mul_left 27 h3
      have hone : 1 ≤ (K + 1) ^ 3 := Nat.one_le_pow 3 (K + 1) (by omega)
      omega
    calc
      _ ≤ (K + 1) ^ 2 * (28 * (K + 1) ^ 3) := Nat.mul_le_mul h2 htail
      _ = 28 * (K + 1) ^ 5 := by ring
  have hsum :
      ((List.range (K - 1)).map fun i =>
        (i + 2) ^ 2 * (27 * (i + 2) ^ 3 + 1)).sum ≤
      ((List.range (K - 1)).map fun _ => 28 * (K + 1) ^ 5).sum := by
    apply List.sum_le_sum
    intro i hi
    exact hterm i hi
  have hlenRange : (List.range (K - 1)).length ≤ K + 1 := by
    simp
    omega
  calc
    (decorationLabels K).length ≤ (K - 1) * (28 * (K + 1) ^ 5) := by
      rw [hlen]
      calc
        _ ≤ ((List.range (K - 1)).map fun _ => 28 * (K + 1) ^ 5).sum := hsum
        _ = (K - 1) * (28 * (K + 1) ^ 5) := by simp
    _ ≤ (K + 1) * (28 * (K + 1) ^ 5) := by
      exact Nat.mul_le_mul_right _ (by omega)
    _ = 28 * (K + 1) ^ 6 := by ring

/-- Combining the proved U^40 candidate-count bound with the alphabet bound
controls generator invocation count by an explicit polynomial in numeric K,n. -/
theorem recursive_calls_le_joint_numeric {K n : Nat} (hn : 1 ≤ n) :
    recursiveCalls (decorationLabels K) labelQ
      (fun x => by have hk := x.arity.property; unfold labelQ; omega)
      (rootStopBudget n) ≤
      (28 * (K + 1) ^ 6 + 1) * (3 * 2004 ^ 10 * n ^ 40) + 1 := by
  let C := 3 * 2004 ^ 10 * n ^ 40
  have hbase := recursive_calls_le_numeric_candidate_bound (K := K) hn
  have hcall : recursiveCalls (decorationLabels K) labelQ
      (fun x => by have hk := x.arity.property; unfold labelQ; omega)
      (rootStopBudget n) ≤ ((decorationLabels K).length + 1) * C + 1 := by
    simpa [C, Nat.add_mul, Nat.one_mul] using hbase
  have hlen := decorationLabels_length_le_numeric K
  have hfactor : (decorationLabels K).length + 1 ≤ 28 * (K + 1) ^ 6 + 1 := by omega
  calc
    recursiveCalls (decorationLabels K) labelQ
        (fun x => by have hk := x.arity.property; unfold labelQ; omega)
        (rootStopBudget n) ≤ ((decorationLabels K).length + 1) * C + 1 := hcall
    _ ≤ (28 * (K + 1) ^ 6 + 1) * C + 1 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_right C hfactor) 1
    _ = (28 * (K + 1) ^ 6 + 1) * (3 * 2004 ^ 10 * n ^ 40) + 1 := by rfl

end Paper.CountStage.StopBudget
/- END Size4.lean -/

/- BEGIN Bounds.lean source_sha256=e1e2f9c5ae18b740f8722bc3fa4e5c6204f401cc7751deae3b4d07f77371bed0 body_sha256=f11169f3d2813e3bc374025fbf6cebc17d42813504b1c72d10a5ffb05d65ee0c -/

namespace Paper.F7WordSize

open Paper.AffineNat Paper.F6ILP Paper.F7QControl
open Paper.CountStage.TypedDecorationWords Paper.F6TypedBridge

/-- The typed count budget is exactly the same product as the affine-word
prefix budget, after applying the existing label encoding. -/
theorem qWord_eq_typedProduct (labels : List Label) :
    qWord labels = qProduct labelQ (labels.map toTyped) :=
  Paper.F7QControl.qWord_eq_typed labels

/-- Every label contributes a qWord factor at least three, so the product
strictly dominates the number of labels. -/
theorem length_add_one_le_qWord (labels : List Label) :
    labels.length + 1 ≤ qWord labels := by
  induction labels with
  | nil => simp [qWord]
  | cons label rest ih =>
      have hk := label.hk
      have hfactor : 3 ≤ 2 * label.k - 1 := by omega
      have hsmall : rest.length + 2 ≤ 3 * (rest.length + 1) := by
        nlinarith
      have hlarge : 3 * (rest.length + 1) ≤
          (2 * label.k - 1) * qWord rest :=
        Nat.mul_le_mul hfactor ih
      simpa only [List.length_cons, qWord] using le_trans hsmall hlarge

theorem length_le_qWord (labels : List Label) :
    labels.length ≤ qWord labels := by
  have h := length_add_one_le_qWord labels
  omega

/-- `Variable` indexes the distinct arities in the label list, so its
cardinality cannot exceed the list length. -/
theorem variable_card_le_length (labels : List Label) :
    Fintype.card (Variable labels) ≤ labels.length := by
  rw [Paper.F6ILP.variable_count, usedArities]
  have h := List.toFinset_card_le (labels.map Label.k)
  simpa only [List.length_map] using h

theorem length_and_variable_card_le_of_qWord_bound
    (labels : List Label) (U : Nat)
    (hbudget : qWord labels ≤ U) :
    labels.length ≤ U ∧ Fintype.card (Variable labels) ≤ U := by
  have hlength : labels.length ≤ U :=
    (length_le_qWord labels).trans hbudget
  exact ⟨hlength, (variable_card_le_length labels).trans hlength⟩

end Paper.F7WordSize
/- END Bounds.lean -/

/- BEGIN Common.lean source_sha256=8fdee096eaa59ff43da29463d9036ec7b1dafabcfdaa69d0e70e938d7faf99af body_sha256=58664d8d7ae8dbb7a96cb11d8ff69095ce734164a4f8af5ad7dfa4a3577cc18d -/

namespace Paper.F7System

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F7Encoding Paper.F7Computable Paper.F7Terminal Paper.F7Contraction
open Paper.F7Size Paper.F7QControl Paper.AffineNat

private theorem natAbs_le_of_signed_bounds (z : ℤ) (M : Nat)
    (hlo : -((M : Nat) : ℤ) ≤ z) (hhi : z ≤ M) :
    z.natAbs ≤ M := by
  by_cases hz : 0 ≤ z
  · have hnat : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz
    have hle : (z.natAbs : ℤ) ≤ M := by rw [hnat]; omega
    exact_mod_cast hle
  · have hzn : z ≤ 0 := le_of_not_ge hz
    have hnat : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hzn
    have hle : (z.natAbs : ℤ) ≤ M := by rw [hnat]; omega
    exact_mod_cast hle

def RowAbsBound {keys : Finset Nat} (M : Nat) (row : AffineExpr keys) : Prop :=
  row.intercept.natAbs ≤ M ∧ ∀ key, (row.coeff key).natAbs ≤ M

private theorem forall_append_rowAbsBound {keys : Finset Nat} (M : Nat)
    (xs ys : List (AffineExpr keys))
    (hxs : xs.Forall (RowAbsBound M)) (hys : ys.Forall (RowAbsBound M)) :
    (xs ++ ys).Forall (RowAbsBound M) := by
  apply (List.forall_iff_forall_mem).2
  intro row hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · exact (List.forall_iff_forall_mem).1 hxs row hleft
  · exact (List.forall_iff_forall_mem).1 hys row hright

private theorem boundRows_rowAbsBound {keys : Finset Nat}
    (lo hi : Nat → Nat) (ks : List { k : Nat // k ∈ keys })
    (n M : Nat) (hM1 : 1 ≤ M) (hbound : n ≤ M)
    (hlohi : ∀ key ∈ ks, lo key.val ≤ n ∧ hi key.val ≤ n) :
    (boundRows lo hi ks).Forall (RowAbsBound M) := by
  induction ks with
  | nil => simp [boundRows]
  | cons key rest ih =>
      have hkey := hlohi key (by simp)
      have htail : ∀ q ∈ rest, lo q.val ≤ n ∧ hi q.val ≤ n := by
        intro q hq
        exact hlohi q (by simp [hq])
      have htailRows := ih htail
      have hnM : (n : ℤ) ≤ M := by exact_mod_cast hbound
      have hloM : (lo key.val : ℤ) ≤ M := by
        exact_mod_cast (le_trans hkey.1 hbound)
      have hhiM : (hi key.val : ℤ) ≤ M := by
        exact_mod_cast (le_trans hkey.2 hbound)
      have hloNonneg : 0 ≤ (lo key.val : ℤ) := by positivity
      have hhiNonneg : 0 ≤ (hi key.val : ℤ) := by positivity
      have hrowLo : RowAbsBound M (lowerRow key lo) := by
        constructor
        · have hval := natAbs_le_of_signed_bounds
            (-(lo key.val : ℤ)) M (by omega) (by omega)
          simpa [lowerRow] using hval
        · intro j
          by_cases hj : j = key
          · simpa [lowerRow, hj] using hM1
          · simp [lowerRow, hj]
      have hrowHi : RowAbsBound M (upperRow key hi) := by
        constructor
        · have hval := natAbs_le_of_signed_bounds
            (hi key.val : ℤ) M (by omega) hhiM
          simpa [upperRow] using hval
        · intro j
          by_cases hj : j = key
          · simpa [upperRow, hj] using hM1
          · simp [upperRow, hj]
      simp only [boundRows, List.forall_cons]
      exact ⟨hrowLo, hrowHi, htailRows⟩

theorem systemRowsC_row_bounds
    (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (T U K n M : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hx : -((n : Nat) : ℤ) ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U)
    (hM1 : 1 ≤ M)
    (hterm : (n : ℤ) + 2 * (U : ℤ) * K * labels.length +
      (U : ℤ) * U ≤ M)
    (htermCoeff : (U : ℤ) * labels.length ≤ M)
    (hcontract : ((K : ℤ) + 1) *
      ((n : ℤ) + 2 * (U : ℤ) * K * labels.length) + U ≤ M)
    (hcontractCoeff : ((K : ℤ) + 1) * (U : ℤ) * labels.length ≤ M)
    (hbound : n ≤ M)
    (hlohi : ∀ key ∈ usedKeys labels,
      lo key.val ≤ n ∧ hi key.val ≤ n)
    (hbudgetRow : RowAbsBound M
      (budgetRow labels x z c price 1 T)) :
    ∀ row ∈ systemRowsC labels x z c lo hi price 1 T,
      RowAbsBound M row := by
  let nZ : ℤ := n
  have hnZ : 0 ≤ nZ := by positivity
  have hxZ : -nZ ≤ x ∧ x ≤ nZ := by simpa [nZ] using hx
  have htermRow := terminalRow_bounds labels x z (fun _ => 0) U K nZ
    hbudget hK hxZ hz
  have htermZ : nZ + 2 * (U : ℤ) * K * labels.length +
      (U : ℤ) * U ≤ M := by
    simpa [nZ] using hterm
  have htermCoeffZ : (U : ℤ) * labels.length ≤ M := by
    simpa using htermCoeff
  have hterminal : RowAbsBound M (terminalRow labels x z) := by
    constructor
    · exact natAbs_le_of_signed_bounds _ M
        (by have h := htermRow.1; omega)
        (by have h := htermRow.2.1; omega)
    · intro key
      have hpos := (htermRow.2.2 key).1
      have hupper := (htermRow.2.2 key).2
      have hupperM : (terminalRow labels x z).coeff key ≤ M :=
        le_trans hupper htermCoeffZ
      have hlowerM : -M ≤ (terminalRow labels x z).coeff key := by omega
      exact natAbs_le_of_signed_bounds _ M hlowerM hupperM
  have hterminalNeg : RowAbsBound M (scaleExpr (-1)
      (terminalRow labels x z)) := by
    constructor
    · simpa [scaleExpr] using hterminal.1
    · intro key
      simpa [scaleExpr] using hterminal.2 key
  have hconRows := contractionRoot_bounds labels x nZ U K hbudget hK
    hnZ hxZ
  have hcontractCoeffZ : ((K : ℤ) + 1) * (U : ℤ) * labels.length ≤ M := by
    simpa using hcontractCoeff
  have hcontraction : (contractionRoot labels x).Forall (RowAbsBound M) := by
    apply List.Forall.imp (p := fun row =>
      -( ((K : ℤ) + 1) * ((n : ℤ) + 2 * (U : ℤ) * K * labels.length) + U) ≤
        row.intercept ∧
      row.intercept ≤ ((K : ℤ) + 1) *
        ((n : ℤ) + 2 * (U : ℤ) * K * labels.length) + U ∧
      (∀ key, -(((K : ℤ) + 1) * (U : ℤ) * labels.length) ≤
        row.coeff key ∧ row.coeff key ≤ ((K : ℤ) + 1) *
          (U : ℤ) * labels.length))
    · intro row hrow
      constructor
      · apply natAbs_le_of_signed_bounds
        · omega
        · omega
      · intro key
        apply natAbs_le_of_signed_bounds
        · have hlow := (hrow.2.2 key).1
          omega
        · have hup := (hrow.2.2 key).2
          exact le_trans hup hcontractCoeffZ
    · simpa [nZ] using hconRows
  have hbudgetList : ([budgetRow labels x z c price 1 T] :
      List (AffineExpr (usedArities labels))).Forall (RowAbsBound M) := by
    simpa [hbudgetRow]
  have hboundRows := boundRows_rowAbsBound lo hi (usedKeys labels) n M
    hM1 hbound hlohi
  intro row hrow
  have hall : (systemRowsC labels x z c lo hi price 1 T).Forall
      (RowAbsBound M) := by
    have hfirst : ([terminalRow labels x z,
        scaleExpr (-1) (terminalRow labels x z)] :
        List (AffineExpr (usedArities labels))).Forall (RowAbsBound M) := by
      simp [hterminal, hterminalNeg]
    have hconTail := forall_append_rowAbsBound M
      ((contractionRoot labels x) ++ [budgetRow labels x z c price 1 T])
      (boundRows lo hi (usedKeys labels))
      (forall_append_rowAbsBound M (contractionRoot labels x)
        [budgetRow labels x z c price 1 T] hcontraction hbudgetList)
      hboundRows
    have hwhole := forall_append_rowAbsBound M
      ([terminalRow labels x z, scaleExpr (-1) (terminalRow labels x z)])
      (contractionRoot labels x ++ [budgetRow labels x z c price 1 T] ++
        boundRows lo hi (usedKeys labels)) hfirst hconTail
    simpa [systemRowsC] using hwhole
  exact (List.forall_iff_forall_mem).1 hall row hrow

theorem systemRowsC_matrixBits_le
    (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (T U K n M : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hx : -((n : Nat) : ℤ) ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U)
    (hM1 : 1 ≤ M)
    (hterm : (n : ℤ) + 2 * (U : ℤ) * K * labels.length +
      (U : ℤ) * U ≤ M)
    (htermCoeff : (U : ℤ) * labels.length ≤ M)
    (hcontract : ((K : ℤ) + 1) *
      ((n : ℤ) + 2 * (U : ℤ) * K * labels.length) + U ≤ M)
    (hcontractCoeff : ((K : ℤ) + 1) * (U : ℤ) * labels.length ≤ M)
    (hbound : n ≤ M)
    (hlohi : ∀ key ∈ usedKeys labels,
      lo key.val ≤ n ∧ hi key.val ≤ n)
    (hbudgetRow : RowAbsBound M
      (budgetRow labels x z c price 1 T)) :
    matrixBits (systemRowsC labels x z c lo hi price 1 T) ≤
      (2 * Fintype.card (Variable labels) + labels.length + 3) *
        (Fintype.card (Variable labels) + 1) * (M + 2) := by
  have hrows := systemRowsC_row_bounds labels x z c lo hi price T U K n M
    hbudget hK hx hz hM1 hterm htermCoeff hcontract hcontractCoeff
    hbound hlohi hbudgetRow
  have hmatrix := matrixBits_le
    (systemRowsC labels x z c lo hi price 1 T) M hrows
  rw [systemRowsC_length, usedKeys_card] at hmatrix
  exact hmatrix

end Paper.F7System

/- END Common.lean -/

/- BEGIN Numeric.lean source_sha256=121d1d659f5717762b9e6bf41b137fcf109f066db825ffd5b41f5489e4f7fb16 body_sha256=baa659fea0eee2622a2004703895eade1f4e6f59049dcf56be166c529a343aba -/

namespace Paper.F7System

open Paper.AffineNat Paper.F6ILP Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F7Computable Paper.F7Encoding Paper.F7QControl Paper.F7Size Paper.F7WordSize
open Paper.AffineILP

def budgetS (U K n ell : Nat) : Nat :=
  ell * (8 * U * (27 * K ^ 3) * U * (n + 2 * U * K * ell + 1))

def budgetR (U K ell : Nat) : Nat :=
  ell * (8 * U * (27 * K ^ 3) * U * (U * ell))

def budgetA (U K n ell : Nat) : Nat :=
  U * (U + 2004 * (U + 1) ^ 6) + budgetS U K n ell

/-- One common coefficient envelope for all rows, from the separate terminal,
contraction, box, and budget-row envelopes. -/
def numericMagnitude (U K n ell : Nat) : Nat :=
  1 + n + (n + 2 * U * K * ell + U ^ 2) + (U * ell) +
    ((K + 1) * (n + 2 * U * K * ell) + U) +
    ((K + 1) * U * ell) + budgetA U K n ell + budgetR U K ell

def numericMagnitudeUniform (U K n : Nat) : Nat :=
  numericMagnitude U K n U

private theorem natAbs_le_of_signed_envelope (z : ℤ) (B M : Nat)
    (hB : -((B : Nat) : ℤ) ≤ z ∧ z ≤ B)
    (hBM : B ≤ M) : z.natAbs ≤ M := by
  by_cases hz : 0 ≤ z
  · have hn : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz
    have hM : (z.natAbs : ℤ) ≤ M := by
      rw [hn]
      exact le_trans hB.2 (by exact_mod_cast hBM)
    exact_mod_cast hM
  · have hzn : z ≤ 0 := le_of_not_ge hz
    have hn : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hzn
    have hM : (z.natAbs : ℤ) ≤ M := by
      rw [hn]
      have hBMZ : (B : ℤ) ≤ M := by exact_mod_cast hBM
      omega
    exact_mod_cast hM

/-- Numeric matrix-size closure. The budget row is an explicit signed-envelope
premise; callers discharge it from the canonical leaf/budget theorem. -/
theorem systemRowsC_numericBits_le
    (labels : List Label) (x z : ℤ) (c lo hi price : Nat → Nat)
    (T U K n : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hx : -((n : Nat) : ℤ) ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U)
    (hlohi : ∀ key ∈ usedKeys labels,
      lo key.val ≤ n ∧ hi key.val ≤ n)
    (hbudgetIntercept :
      -((budgetA U K n labels.length : Nat) : ℤ) ≤
        (budgetRow labels x z c price 1 T).intercept ∧
      (budgetRow labels x z c price 1 T).intercept ≤ budgetA U K n labels.length)
    (hbudgetCoeff : ∀ key,
      -((budgetR U K labels.length : Nat) : ℤ) ≤
        (budgetRow labels x z c price 1 T).coeff key ∧
      (budgetRow labels x z c price 1 T).coeff key ≤ budgetR U K labels.length) :
    matrixBits (systemRowsC labels x z c lo hi price 1 T) ≤
      (3 * U + 3) * (U + 1) * (numericMagnitude U K n labels.length + 2) := by
  let ell := labels.length
  let M := numericMagnitude U K n ell
  have hM1 : 1 ≤ M := by
    dsimp [M, numericMagnitude]
    omega
  have htermNat : n + 2 * U * K * ell + U ^ 2 ≤ M := by
    dsimp [M, numericMagnitude, budgetA, budgetS, budgetR]
    omega
  have hterm : (n : ℤ) + 2 * (U : ℤ) * K * labels.length +
      (U : ℤ) * U ≤ M := by
    have hcast : ((n + 2 * U * K * ell + U ^ 2 : Nat) : ℤ) ≤ M := by
      exact_mod_cast htermNat
    simpa [ell, pow_two] using hcast
  have htermCoeffNat : U * ell ≤ M := by
    dsimp [M, numericMagnitude, budgetA, budgetS, budgetR]
    omega
  have htermCoeff : (U : ℤ) * labels.length ≤ M := by
    have hcast : ((U * ell : Nat) : ℤ) ≤ M := by exact_mod_cast htermCoeffNat
    simpa [ell] using hcast
  have hcontractNat : (K + 1) * (n + 2 * U * K * ell) + U ≤ M := by
    dsimp [M, numericMagnitude, budgetA, budgetS, budgetR]
    omega
  have hcontract : ((K : ℤ) + 1) *
      ((n : ℤ) + 2 * (U : ℤ) * K * labels.length) + U ≤ M := by
    have hcast : (((K + 1) * (n + 2 * U * K * ell) + U : Nat) : ℤ) ≤ M := by
      exact_mod_cast hcontractNat
    simpa [ell] using hcast
  have hcontractCoeffNat : (K + 1) * U * ell ≤ M := by
    dsimp [M, numericMagnitude, budgetA, budgetS, budgetR]
    omega
  have hcontractCoeff : ((K : ℤ) + 1) * (U : ℤ) * labels.length ≤ M := by
    have hcast : (((K + 1) * U * ell : Nat) : ℤ) ≤ M := by
      exact_mod_cast hcontractCoeffNat
    simpa [ell] using hcast
  have hbound : n ≤ M := by
    dsimp [M, numericMagnitude, budgetA, budgetS, budgetR]
    omega
  have hbudgetA : budgetA U K n ell ≤ M := by
    dsimp [M, numericMagnitude]
    omega
  have hbudgetR : budgetR U K ell ≤ M := by
    dsimp [M, numericMagnitude]
    omega
  have hbudgetRow : RowAbsBound M (budgetRow labels x z c price 1 T) := by
    constructor
    · exact natAbs_le_of_signed_envelope _ (budgetA U K n ell) M
        hbudgetIntercept hbudgetA
    · intro key
      exact natAbs_le_of_signed_envelope _ (budgetR U K ell) M
        (hbudgetCoeff key) hbudgetR
  have hrows := systemRowsC_matrixBits_le labels x z c lo hi price T U K n M
    hbudget hK hx hz hM1 hterm htermCoeff hcontract hcontractCoeff
    hbound hlohi hbudgetRow
  have hsize := length_and_variable_card_le_of_qWord_bound labels U hbudget
  have hfirst : 2 * Fintype.card (Variable labels) + labels.length + 3 ≤
      3 * U + 3 := by omega
  have hsecond : Fintype.card (Variable labels) + 1 ≤ U + 1 := by omega
  have hproduct := Nat.mul_le_mul hfirst hsecond
  have hscaled := Nat.mul_le_mul_right (M + 2) hproduct
  simpa [M, ell] using hrows.trans hscaled

/-- Replacing the label count by U yields a fixed polynomial envelope in
numeric U,K,n alone. -/
theorem numericMagnitude_le_uniform (U K n ell : Nat) (hell : ell ≤ U) :
    numericMagnitude U K n ell ≤ numericMagnitudeUniform U K n := by
  unfold numericMagnitudeUniform numericMagnitude budgetA budgetS budgetR
  gcongr <;> omega

/-- A system-row bound from `systemRowsC_numericBits_le` becomes a numeric
polynomial bound in U,K,n alone, using qWord to absorb both list and variable
counts. -/
theorem systemRowsC_numericBits_uniform
    (labels : List Label) (x z : ℤ) (c lo hi price : Nat → Nat)
    (T U K n : Nat)
    (hbudget : qWord labels ≤ U)
    (hbits : matrixBits (systemRowsC labels x z c lo hi price 1 T) ≤
      (3 * U + 3) * (U + 1) *
        (numericMagnitude U K n labels.length + 2)) :
    matrixBits (systemRowsC labels x z c lo hi price 1 T) ≤
      (3 * U + 3) * (U + 1) *
        (numericMagnitudeUniform U K n + 2) := by
  have hsize := length_and_variable_card_le_of_qWord_bound labels U hbudget
  have hmag := numericMagnitude_le_uniform U K n labels.length hsize.1
  calc
    matrixBits (systemRowsC labels x z c lo hi price 1 T) ≤
        (3 * U + 3) * (U + 1) *
          (numericMagnitude U K n labels.length + 2) := hbits
    _ ≤ (3 * U + 3) * (U + 1) *
          (numericMagnitudeUniform U K n + 2) := by
      exact Nat.mul_le_mul_left ((3 * U + 3) * (U + 1))
        (Nat.add_le_add_right hmag 2)

end Paper.F7System
/- END Numeric.lean -/

/- BEGIN Canonical.lean source_sha256=0e21d275e116413ddbf3e31a7990c0b3de05e5da5a0ca533d7f0e372a5b9deaa body_sha256=1b2e80c6c3f696575bf8464f6b99de52ecbcbdaaf82a680f2fc42fb4c319ae24 -/

set_option autoImplicit false

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F6Objective Paper.AffineNat Paper.F7QControl
open Paper.PPEndToEnd Paper.CountStage.StopBudget Paper.F7LeafCanon

theorem budgetRoot_canonical_bound (labels : List Label) (x z : ℤ)
    (c : Nat → Nat) (T U K n : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hlabelCap : ∀ label ∈ labels, label.c ≤ 27 * label.k ^ 3)
    (hshared : ∀ label ∈ labels, label.c = c label.k)
    (hx : -(n : ℤ) ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U)
    (hT : T ≤ U) :
    let H : Nat := 27 * K ^ 3;
    let L : Nat := 2004 * (U + 1) ^ 6;
    let S : Nat := labels.length *
      (8 * U * H * U * (n + 2 * U * K * labels.length + 1));
    let R : Nat := labels.length * (8 * U * H * U * (U * labels.length));
    -((U : ℤ) * (U + L) + S) ≤
        (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).intercept ∧
      (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).intercept ≤
        (U : ℤ) * (U + L) + S ∧
      (∀ key, -(R : ℤ) ≤ (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).coeff key ∧
        (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).coeff key ≤ R) := by
  have hzNat : z.toNat ≤ U := by omega
  have hleaf := canonical_leaf_bound labels U z.toNat hbudget hzNat
  have hcap := shared_charge_cap labels c K hK hlabelCap hshared
  exact budgetRoot_bound labels x z c Paper.PPEndToEnd.tauExact T U K
    (27 * K ^ 3) n (2004 * (U + 1) ^ 6)
    hbudget hK hcap hx hT hleaf

end Paper.F7Budget
/- END Canonical.lean -/

/- BEGIN Canonical.lean source_sha256=e4385fccc0e5259edacab0b429a9021351d13a75325b8bb6efa5af53de534bfa body_sha256=25975a7283f91da2af5be5033276aef7c2227a36145d35a01afb8a4b59aa552a -/

set_option autoImplicit false

namespace Paper.F7MatrixFinal

open Paper.AffineNat Paper.F6ILP Paper.F6ILPSystem
open Paper.F7QControl Paper.F7Computable Paper.F7Encoding
open Paper.F7Budget Paper.F7System
open Paper.PPEndToEnd
open Paper.CountStage.StopBudget

/-- Explicit finite binary encoding bound for the canonical leaf price.
The budget-row envelope is derived from the actual q-word budget and
the minimum-charge label cap; no coefficient oracle remains. -/
theorem canonical_matrix_bits_uniform
    (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (T U K n : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hlabelCap : ∀ label ∈ labels, label.c ≤ 27 * label.k ^ 3)
    (hshared : ∀ label ∈ labels, label.c = c label.k)
    (hx : -(n : ℤ) ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U)
    (hT : T ≤ U)
    (hlohi : ∀ key ∈ usedKeys labels,
      lo key.val ≤ n ∧ hi key.val ≤ n) :
    matrixBits (systemRowsC labels x z c lo hi Paper.PPEndToEnd.tauExact 1 T) ≤
      (3 * U + 3) * (U + 1) *
        (numericMagnitudeUniform U K n + 2) := by
  have hb := budgetRoot_canonical_bound labels x z c T U K n
    hbudget hK hlabelCap hshared hx hz hT
  have hbI :
      -((budgetA U K n labels.length : Nat) : ℤ) ≤
        (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).intercept ∧
      (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).intercept ≤
        budgetA U K n labels.length := by
    simpa only [budgetA, budgetS, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat] using And.intro hb.1 hb.2.1
  have hbC : ∀ key,
      -((budgetR U K labels.length : Nat) : ℤ) ≤
        (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).coeff key ∧
      (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).coeff key ≤
        budgetR U K labels.length := by
    intro key
    simpa only [budgetR, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_add, Nat.cast_ofNat] using hb.2.2 key
  have hbits := systemRowsC_numericBits_le labels x z c lo hi
    Paper.PPEndToEnd.tauExact T U K n hbudget hK hx hz hlohi hbI hbC
  exact systemRowsC_numericBits_uniform labels x z c lo hi
    Paper.PPEndToEnd.tauExact T U K n hbudget hbits

end Paper.F7MatrixFinal
/- END Canonical.lean -/

/- BEGIN Optimizer.lean source_sha256=26422319ca1ae6ae2c1fca9e3f6e66b9a212c106479e2ba2fa637ae16b1d51ad body_sha256=4ac3da67d128ca75602fd127370e528667240231df9880cf7d68497b8e6e3f3e -/

set_option autoImplicit false

namespace Paper.F7MatrixFinal

open Coupled.Formal Paper.F2CatalogTransfer Paper.PPEndToEnd
open Paper.A2Feasible Paper.A2ActualForward Paper.ComputableProfileProvider
open Paper.AffineNat Paper.F6ILP Paper.F6ILPSystem Paper.F6ILPFeasible
open Paper.F6TypedBridge Paper.F7System
open Paper.F7QControl Paper.F7WordSize Paper.F7Computable Paper.F7Encoding
open Paper.F7Semantics Paper.CountStage.TypedDecorationWords
open Paper.CountStage.StopBudget

/-- The exact finite raw optimizer yields a feasible canonical-price ILP
encoding at its own optimum threshold, with an explicit numeric bit bound.
This theorem concerns the finite encoding and does not assert an ILP solver
or uniform polynomial synthesis of the minimum-charge profiles. -/
theorem optimizer_canonical_matrix_bits {K W : Nat}
    (hK : 2 ≤ K) (hW : 1 ≤ W) :
    ∃ (reps : List (F2Source K)) (v' : Nat)
      (labels : List Label) (z : ℤ),
      v' = (optimize K W 1).benchmarkCost tauRS 1 ∧
      v' ≤ rootStopBudget W ∧
      ArityInj F2Source.arity reps ∧
      CostL (rawProblem tauRS) reps W 1 v' ∧
      qProduct labelQ (labels.map toTyped) ≤ rootStopBudget W ∧
      labels.map toTyped ∈ consistentBudgetWordsFixed K (rootStopBudget W) ∧
      1 ≤ z ∧ z ≤ v' ∧
      Feasible labels (1 * W) z (profileC reps)
        (fun k => levelLo K W k (profileD reps k) (profileC reps k))
        (fun k => levelHi K W k (profileD reps k) (profileC reps k))
        tauRS 1 v' (fun key => (profileA reps key.val : ℤ)) ∧
      (systemRowsC labels (W : ℤ) z (profileC reps)
        (fun k => levelLo K W k (profileD reps k) (profileC reps k))
        (fun k => levelHi K W k (profileD reps k) (profileC reps k))
        tauRS 1 v').Forall
          (fun row => 0 ≤ evalInt row
            (fun key => (profileA reps key.val : ℤ))) ∧
      matrixBits (systemRowsC labels (W : ℤ) z (profileC reps)
        (fun k => levelLo K W k (profileD reps k) (profileC reps k))
        (fun k => levelHi K W k (profileD reps k) (profileC reps k))
        tauRS 1 v') ≤
        (3 * rootStopBudget W + 3) * (rootStopBudget W + 1) *
          (numericMagnitudeUniform (rootStopBudget W) K W + 2) := by
  obtain ⟨reps,v',labels,z,hopt,hvroot,hinj,hcost,hlabel,hq,hfixed,
      _hcandidate,_hactual,_hcostEq,hz1,hzv,hfeas⟩ :=
    optimizer_candidate_feasible_root hK hW
  have hbudget : qWord labels ≤ rootStopBudget W := by
    rw [qWord_eq_typedProduct]
    exact hq
  have hKlabels : ∀ label ∈ labels, label.k ≤ K := by
    intro label hmem
    obtain ⟨_,_,_,hk,_⟩ := hlabel label hmem
    exact hk
  have hcap : ∀ label ∈ labels,
      label.c ≤ 27 * label.k ^ 3 := by
    intro label hmem
    obtain ⟨_,_,_,_,hcap⟩ := hlabel label hmem
    exact hcap
  have hshared : ∀ label ∈ labels,
      label.c = profileC reps label.k := by
    intro label hmem
    exact (hlabel label hmem).2.1
  have hx : -((W : Nat) : ℤ) ≤ (W : ℤ) ∧ (W : ℤ) ≤ W := by
    omega
  have hvrootZ : (v' : ℤ) ≤ rootStopBudget W := by
    exact_mod_cast hvroot
  have hzroot : 0 ≤ z ∧ z ≤ rootStopBudget W := by
    omega
  have hlohi : ∀ key ∈ usedKeys labels,
      levelLo K W key.val (profileD reps key.val)
          (profileC reps key.val) ≤ W ∧
      levelHi K W key.val (profileD reps key.val)
          (profileC reps key.val) ≤ W := by
    intro key _
    exact level_endpoints_le_root hW
  have hbitsExact := canonical_matrix_bits_uniform labels (W : ℤ) z
    (profileC reps)
    (fun k => levelLo K W k (profileD reps k) (profileC reps k))
    (fun k => levelHi K W k (profileD reps k) (profileC reps k))
    v' (rootStopBudget W) K W hbudget hKlabels hcap hshared
    hx hzroot hvroot hlohi
  have hbits : matrixBits (systemRowsC labels (W : ℤ) z (profileC reps)
      (fun k => levelLo K W k (profileD reps k) (profileC reps k))
      (fun k => levelHi K W k (profileD reps k) (profileC reps k))
      tauRS 1 v') ≤
      (3 * rootStopBudget W + 3) * (rootStopBudget W + 1) *
        (numericMagnitudeUniform (rootStopBudget W) K W + 2) := by
    simpa only [tauRS_eq_tauExact_fun] using hbitsExact
  have hrows := (systemRowsC_iff_feasible labels (W : ℤ) z
    (profileC reps)
    (fun k => levelLo K W k (profileD reps k) (profileC reps k))
    (fun k => levelHi K W k (profileD reps k) (profileC reps k))
    tauRS 1 v' (fun key => (profileA reps key.val : ℤ))).2
    (by simpa only [one_mul] using hfeas)
  exact ⟨reps,v',labels,z,hopt,hvroot,hinj,hcost,hq,hfixed,
    hz1,hzv,hfeas,hrows,hbits⟩

end Paper.F7MatrixFinal
/- END Optimizer.lean -/
