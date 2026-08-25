import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.WellFormed
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage

open Operations

namespace Table_Generation

lemma streamPoint_allowed (n : ℕ) : AllowedPoint (streamPoint n) := by
  rcases n with _ | _ | _ | _ | n
  · simp [streamPoint, AllowedPoint]
  · simp [streamPoint, AllowedPoint]
  · simp [streamPoint, AllowedPoint]
    exact ⟨0, by simp⟩
  · simp [streamPoint, AllowedPoint]
    exact ⟨0, by simp⟩
  · by_cases h0 : n % 4 = 0
    · simp [streamPoint, h0, AllowedPoint]
      exact ⟨1 + n / 4, by simp⟩
    · by_cases h1 : n % 4 = 1
      · simp [streamPoint, h1, AllowedPoint]
        exact ⟨1 + n / 4, by simp⟩
      · by_cases h2 : n % 4 = 2
        · simp [streamPoint, h2, AllowedPoint]
          exact ⟨1 + n / 4, by simp⟩
        · simp [streamPoint, AllowedPoint]
          exact ⟨1 + n / 4, by simp⟩

lemma streamPoint_eq_canonicalPoint (n : ℕ) : streamPoint n = canonicalPoint n := by
  rcases n with _ | _ | _ | _ | n
  · simp [streamPoint, canonicalPoint]
  · simp [streamPoint, canonicalPoint]
  · simp [streamPoint, canonicalPoint]
  · simp [streamPoint, canonicalPoint]
  · by_cases h0 : n % 4 = 0
    · simp [streamPoint, canonicalPoint, h0]
    · by_cases h1 : n % 4 = 1
      · simp [streamPoint, canonicalPoint, h0, h1]
      · by_cases h2 : n % 4 = 2
        · simp [streamPoint, canonicalPoint, h0, h1, h2]
        · simp [streamPoint, canonicalPoint, h0, h1, h2]

def carrierTerm {k : ℕ} (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) (j : Fin k) (σ : State k) (u : Fin k) : ℤ :=
  if parityDegree type k j % 2 = parity then
    if j = dst then 0 else twoPowInt (e * parityDegree type k j) * σ j u
  else
    0

def carrierContribFrom {k : ℕ} (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) (σ : State k) : List (Fin k) → Fin k → ℤ
  | [], _ => 0
  | j :: js, u => carrierTerm type e dst parity j σ u
      + carrierContribFrom type e dst parity σ js u

def carrierAddsList {k : ℕ} (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) : List (Fin k) → Prog k
  | [] => []
  | j :: js =>
      let rest := carrierAddsList type e dst parity js
      let d := parityDegree type k j
      if d % 2 = parity then
        if j = dst then rest else addConstFrom dst j (twoPowInt (e * d)) ++ rest
      else rest

lemma carrierContribFrom_eq_of_preserve_non_dst
    {k : ℕ} (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) (xs : List (Fin k))
    {σ τ : State k}
    (hpres : ∀ t, t ≠ dst → τ t = σ t) :
    ∀ u, carrierContribFrom type e dst parity τ xs u =
      carrierContribFrom type e dst parity σ xs u := by
  intro u
  induction xs with
  | nil =>
      simp [carrierContribFrom]
  | cons j js ih =>
      dsimp [carrierContribFrom, carrierTerm]
      by_cases hp : parityDegree type k j % 2 = parity
      · simp [hp]
        by_cases hj : j = dst
        · simp [hj, ih]
        ·
          rw [hpres j hj]
          rw [ih]
      · simp [hp, ih]

lemma carrierAddsList_effect
    {k : ℕ} (hk : 0 < k) (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) :
    ∀ xs {σ τ : State k},
      run? (carrierAddsList type e dst parity xs) σ = some τ →
      (∀ t, t ≠ dst → τ t = σ t) ∧
      (∀ u, τ dst u =
        σ dst u + carrierContribFrom type e dst parity σ xs u)
  | [], σ, τ, hrun => by
      simp [carrierAddsList] at hrun
      subst τ
      constructor
      · intro t _; rfl
      · intro u; simp [carrierContribFrom]
  | j :: js, σ, τ, hrun => by
      dsimp [carrierAddsList] at hrun
      by_cases hp : parityDegree type k j % 2 = parity
      · simp [hp] at hrun
        by_cases hj : j = dst
        · simp [hj] at hrun
          rcases carrierAddsList_effect hk type e dst parity js hrun with ⟨hpres, hdst⟩
          constructor
          · exact hpres
          · intro u
            rw [hdst u]
            simp [carrierContribFrom, carrierTerm, hj]
        · simp [hj] at hrun
          have hdecomp :
              run? (addConstFrom (k := k) dst j (twoPowInt (e * parityDegree type k j))
                ++ carrierAddsList type e dst parity js) σ = some τ := by
            exact hrun
          rcases run?_append_some
            (p := addConstFrom (k := k) dst j (twoPowInt (e * parityDegree type k j)))
            (q := carrierAddsList type e dst parity js)
            (σ := σ) hdecomp with ⟨μ, hhead, htail⟩
          have heff :=
            addConstFrom_effect_const
              (k := k) hk dst j (twoPowInt (e * parityDegree type k j))
              (by
                intro h
                exact hj h)
              hhead
          rcases heff with ⟨hhead_pres, hhead_dst⟩
          rcases carrierAddsList_effect hk type e dst parity js htail with ⟨htail_pres, htail_dst⟩
          constructor
          · intro t ht
            rw [htail_pres t ht, hhead_pres t ht]
          · intro u
            rw [htail_dst u, hhead_dst u]
            rw [carrierContribFrom_eq_of_preserve_non_dst type e dst parity js hhead_pres u]
            simp [carrierContribFrom, carrierTerm, hp, hj]
            ring
      · simp [hp] at hrun
        rcases carrierAddsList_effect hk type e dst parity js hrun with ⟨hpres, hdst⟩
        constructor
        · exact hpres
        · intro u
          rw [hdst u]
          simp [carrierContribFrom, carrierTerm, hp]

lemma carrierAdds_fold_eq_append
    {k : ℕ} (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) :
    ∀ xs (acc : Prog k),
      List.foldl
        (fun acc j =>
          let d := parityDegree type k j
          if d % 2 = parity then
            if j = dst then acc else acc ++ addConstFrom dst j (twoPowInt (e * d))
          else acc)
        acc xs =
      acc ++ carrierAddsList type e dst parity xs
  | [], acc => by simp [carrierAddsList]
  | j :: js, acc => by
      dsimp [carrierAddsList]
      by_cases hp : parityDegree type k j % 2 = parity
      · simp [hp]
        by_cases hj : j = dst
        · simp [hj, carrierAdds_fold_eq_append type e dst parity js acc]
        ·
          simp [hj]
          rw [carrierAdds_fold_eq_append type e dst parity js
            (acc ++ addConstFrom dst j (twoPowInt (e * parityDegree type k j)))]
          simp [List.append_assoc]
      · simp [hp, carrierAdds_fold_eq_append type e dst parity js acc]

lemma carrierAdds_eq_carrierAddsList
    {k : ℕ} (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) :
    carrierAdds k type e dst parity =
      carrierAddsList type e dst parity (List.finRange k) := by
  unfold carrierAdds
  simpa using carrierAdds_fold_eq_append type e dst parity (List.finRange k) ([] : Prog k)

lemma carrierContribFrom_eq_zero_of_all_ne
    {k : ℕ} (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) (σ : State k) (xs : List (Fin k)) (u : Fin k)
    (hbasis :
      ∀ j, j ≠ dst → parityDegree type k j % 2 = parity →
        ∀ v, σ j v = State.start_state (k := k) j v)
    (hall : ∀ j ∈ xs, j ≠ u) :
    carrierContribFrom type e dst parity σ xs u = 0 := by
  induction xs with
  | nil =>
      simp [carrierContribFrom]
  | cons j js ih =>
      have hju : j ≠ u := hall j (by simp)
      have hall' : ∀ j' ∈ js, j' ≠ u := by
        intro j' hj'
        exact hall j' (by simp [hj'])
      dsimp [carrierContribFrom, carrierTerm]
      by_cases hp : parityDegree type k j % 2 = parity
      · simp [hp]
        by_cases hjd : j = dst
        · simp [hjd, ih hall']
        ·
          have hbasis_j := hbasis j hjd hp u
          have huj : u ≠ j := Ne.symm hju
          simp [hjd, hbasis_j, State.start_state, huj, ih hall']
      · simp [hp, ih hall']

lemma carrierContribFrom_of_unique
    {k : ℕ} (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) (σ : State k) (xs : List (Fin k)) (u : Fin k)
    (hbasis :
      ∀ j, j ≠ dst → parityDegree type k j % 2 = parity →
        ∀ v, σ j v = State.start_state (k := k) j v)
    (hnd : xs.Nodup) (hu : u ∈ xs) :
    carrierContribFrom type e dst parity σ xs u =
      if parityDegree type k u % 2 = parity then
        if u = dst then 0 else twoPowInt (e * parityDegree type k u)
      else 0 := by
  induction xs with
  | nil =>
      cases hu
  | cons j js ih =>
      have hnd' : js.Nodup := (List.nodup_cons.mp hnd).2
      have hnot : j ∉ js := (List.nodup_cons.mp hnd).1
      dsimp [carrierContribFrom]
      cases hu with
      | head =>
        have hall : ∀ j' ∈ js, j' ≠ u := by
          intro j' hj' hEq
          exact hnot (by simpa [hEq] using hj')
        have hzero :=
          carrierContribFrom_eq_zero_of_all_ne type e dst parity σ js u hbasis hall
        by_cases hp : parityDegree type k u % 2 = parity
        · simp [carrierTerm, hp, hzero]
          by_cases hud : u = dst
          · simp [hud]
          ·
            have hbasis_u := hbasis u hud hp u
            simp [hud, hbasis_u, State.start_state]
        · simp [carrierTerm, hp, hzero]
      | tail _ hu_tail =>
          have hju : j ≠ u := by
            intro hEq
            subst hEq
            exact hnot hu_tail
          have hterm_zero : carrierTerm type e dst parity j σ u = 0 := by
            dsimp [carrierTerm]
            by_cases hp : parityDegree type k j % 2 = parity
            · simp [hp]
              by_cases hjd : j = dst
              · simp [hjd]
              ·
                have hbasis_j := hbasis j hjd hp u
                have huj : u ≠ j := Ne.symm hju
                simp [hjd, hbasis_j, State.start_state, huj]
            · simp [hp]
          change carrierTerm type e dst parity j σ u
              + carrierContribFrom type e dst parity σ js u =
            (if parityDegree type k u % 2 = parity then
              if u = dst then 0 else twoPowInt (e * parityDegree type k u)
            else 0)
          rw [hterm_zero]
          simp
          exact ih hnd' hu_tail

lemma carrierContribFrom_finRange
    {k : ℕ} (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) (σ : State k) (u : Fin k)
    (hbasis :
      ∀ j, j ≠ dst → parityDegree type k j % 2 = parity →
        ∀ v, σ j v = State.start_state (k := k) j v) :
    carrierContribFrom type e dst parity σ (List.finRange k) u =
      if parityDegree type k u % 2 = parity then
        if u = dst then 0 else twoPowInt (e * parityDegree type k u)
      else 0 := by
  exact carrierContribFrom_of_unique type e dst parity σ (List.finRange k) u
    hbasis (List.nodup_finRange k) (List.mem_finRange u)

lemma carrierAddsList_run_some
    {k : ℕ} (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) :
    ∀ xs (σ : State k), ∃ τ, run? (carrierAddsList type e dst parity xs) σ = some τ
  | [], σ => by
      exact ⟨σ, by simp [carrierAddsList]⟩
  | j :: js, σ => by
      dsimp [carrierAddsList]
      by_cases hp : parityDegree type k j % 2 = parity
      · simp [hp]
        by_cases hj : j = dst
        · simp [hj]
          exact carrierAddsList_run_some type e dst parity js σ
        · simp [hj]
          rcases run_some_addConstFrom
            (k := k) (dst := dst) (src := j)
            (c := twoPowInt (e * parityDegree type k j)) σ with ⟨μ, hμ⟩
          rcases carrierAddsList_run_some type e dst parity js μ with ⟨τ, hτ⟩
          exact ⟨τ, by simp [run?_append, hμ, hτ]⟩
      · simp [hp]
        exact carrierAddsList_run_some type e dst parity js σ

lemma carrierAdds_run_effect_basis
    {k : ℕ} (hk : 0 < k) (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) (σ : State k)
    (hbasis :
      ∀ j, j ≠ dst → parityDegree type k j % 2 = parity →
        ∀ v, σ j v = State.start_state (k := k) j v) :
    ∃ τ,
      run? (carrierAdds k type e dst parity) σ = some τ ∧
      (∀ t, t ≠ dst → τ t = σ t) ∧
      (∀ u, τ dst u =
        σ dst u +
          if parityDegree type k u % 2 = parity then
            if u = dst then 0 else twoPowInt (e * parityDegree type k u)
          else 0) := by
  rw [carrierAdds_eq_carrierAddsList type e dst parity]
  rcases carrierAddsList_run_some type e dst parity (List.finRange k) σ with ⟨τ, hτ⟩
  rcases carrierAddsList_effect hk type e dst parity (List.finRange k) hτ with ⟨hpres, hdst⟩
  refine ⟨τ, hτ, hpres, ?_⟩
  intro u
  rw [hdst u, carrierContribFrom_finRange type e dst parity σ u hbasis]

def parityCarrierRow {k : ℕ} (type : PointPairType) (e parity : ℕ) : Register k :=
  fun u =>
    if parityDegree type k u % 2 = parity then
      twoPowInt (e * parityDegree type k u)
    else
      0

def positivePointOfPair (type : PointPairType) (e : ℕ) : Point :=
  match type with
  | .integer => .int (twoPowInt e)
  | .fraction => .frac (twoPowInt e)

def negativePointOfPair (type : PointPairType) (e : ℕ) : Point :=
  match type with
  | .integer => .int (-(twoPowInt e))
  | .fraction => .frac (-(twoPowInt e))

lemma parityCarrierRows_positive_expected
    {k : ℕ} (type : PointPairType) (e : ℕ) (u : Fin k) :
    parityCarrierRow type e 1 u + parityCarrierRow type e 0 u =
      expectedRow (k := k) (positivePointOfPair type e) u := by
  cases type with
  | integer =>
      have hmod := Nat.mod_two_eq_zero_or_one u.val
      rcases hmod with hmod | hmod <;>
        simp [positivePointOfPair, parityCarrierRow, parityDegree,
          expectedRow, hmod, twoPowInt, pow_mul]
  | fraction =>
      let d := k - 1 - u.val
      have hmod := Nat.mod_two_eq_zero_or_one d
      rcases hmod with hmod | hmod
      · simp [positivePointOfPair, parityCarrierRow, parityDegree,
          expectedRow, d, hmod, twoPowInt, pow_mul]
      · simp [positivePointOfPair, parityCarrierRow, parityDegree,
          expectedRow, d, hmod, twoPowInt, pow_mul]

lemma parityCarrierRows_negative_expected
    {k : ℕ} (type : PointPairType) (e : ℕ) (u : Fin k) :
    parityCarrierRow type e 0 u - parityCarrierRow type e 1 u =
      expectedRow (k := k) (negativePointOfPair type e) u := by
  cases type with
  | integer =>
      let d := u.val
      have hmod := Nat.mod_two_eq_zero_or_one d
      rcases hmod with hmod | hmod
      · have heven : Even d := Nat.even_iff.mpr hmod
        have hneg := Even.neg_pow heven ((2 : ℤ) ^ e)
        simp [negativePointOfPair, parityCarrierRow, parityDegree,
          expectedRow, d, hmod, twoPowInt, pow_mul, hneg]
      · have hodd : Odd d := Nat.odd_iff.mpr hmod
        have hneg := Odd.neg_pow hodd ((2 : ℤ) ^ e)
        simp [negativePointOfPair, parityCarrierRow, parityDegree,
          expectedRow, d, hmod, twoPowInt, pow_mul, hneg]
  | fraction =>
      let d := k - 1 - u.val
      have hmod := Nat.mod_two_eq_zero_or_one d
      rcases hmod with hmod | hmod
      · have heven : Even d := Nat.even_iff.mpr hmod
        have hneg := Even.neg_pow heven ((2 : ℤ) ^ e)
        simp [negativePointOfPair, parityCarrierRow, parityDegree,
          expectedRow, d, hmod, twoPowInt, pow_mul, hneg]
      · have hodd : Odd d := Nat.odd_iff.mpr hmod
        have hneg := Odd.neg_pow hodd ((2 : ℤ) ^ e)
        simp [negativePointOfPair, parityCarrierRow, parityDegree,
          expectedRow, d, hmod, twoPowInt, pow_mul, hneg]

lemma parityDegree_evenCarrier (k : ℕ) (hk : k ≥ 4) (type : PointPairType) :
    parityDegree type k (evenCarrier k hk type) = 0 := by
  cases type with
  | integer =>
      simp [parityDegree, evenCarrier]
  | fraction =>
      simp [parityDegree, evenCarrier]

lemma parityDegree_oddCarrier (k : ℕ) (hk : k ≥ 4) (type : PointPairType) :
    parityDegree type k (oddCarrier k hk type) = 1 := by
  cases type with
  | integer =>
      simp [parityDegree, oddCarrier]
  | fraction =>
      simp [parityDegree, oddCarrier]
      omega

lemma parityDegree_evenCarrier_mod (k : ℕ) (hk : k ≥ 4) (type : PointPairType) :
    parityDegree type k (evenCarrier k hk type) % 2 = 0 := by
  simp [parityDegree_evenCarrier]

lemma parityDegree_oddCarrier_mod (k : ℕ) (hk : k ≥ 4) (type : PointPairType) :
    parityDegree type k (oddCarrier k hk type) % 2 = 1 := by
  simp [parityDegree_oddCarrier]

lemma carrierAdds_even_from_start
    (k : ℕ) (hk : k ≥ 4) (type : PointPairType) (e : ℕ) :
    ∃ σ,
      run? (carrierAdds k type e (evenCarrier k hk type) 0) State.start_state = some σ ∧
      (∀ t, t ≠ evenCarrier k hk type → σ t = State.start_state t) ∧
      (∀ u, σ (evenCarrier k hk type) u = parityCarrierRow type e 0 u) := by
  let even := evenCarrier k hk type
  have hbasis :
      ∀ j, j ≠ even → parityDegree type k j % 2 = 0 →
        ∀ v, (State.start_state (k := k)) j v = State.start_state j v := by
    intro j hj hp v
    rfl
  rcases carrierAdds_run_effect_basis (k := k) (by omega) type e even 0
      (State.start_state (k := k)) hbasis with ⟨σ, hrun, hpres, hdst⟩
  refine ⟨σ, hrun, hpres, ?_⟩
  intro u
  rw [hdst u]
  dsimp [parityCarrierRow]
  by_cases hsel : parityDegree type k u % 2 = 0
  · simp [hsel]
    by_cases hue : u = even
    · subst hue
      rw [parityDegree_evenCarrier k hk type]
      simp [twoPowInt]
    · simp [hue]
  · simp [hsel]
    by_cases hue : u = even
    · subst hue
      have h0 : parityDegree type k even % 2 = 0 := by
        dsimp [even]
        exact parityDegree_evenCarrier_mod k hk type
      exact False.elim (hsel h0)
    · simp [hue]

lemma shiftL_odd_preserves_basis_sources
    (k : ℕ) (hk : k ≥ 4) (type : PointPairType) (e : ℕ)
    {σE : State k}
    (hpresE : ∀ t, t ≠ evenCarrier k hk type → σE t = State.start_state t) :
    let σS := State.shiftLReg σE (oddCarrier k hk type) e
    ∀ j, j ≠ oddCarrier k hk type → parityDegree type k j % 2 = 1 →
      ∀ v, σS j v = State.start_state j v := by
  intro σS j hjodd hp v
  have hjeven : j ≠ evenCarrier k hk type := by
    intro h
    have hp0 : parityDegree type k j % 2 = 0 := by
      simpa [h] using parityDegree_evenCarrier_mod k hk type
    omega
  simp [σS, State.shiftLReg, hjodd]
  have hreg := hpresE j hjeven
  exact congrFun hreg v

lemma carrierAdds_odd_after_even
    (k : ℕ) (hk : k ≥ 4) (type : PointPairType) (e : ℕ)
    {σE : State k}
    (hpresE : ∀ t, t ≠ evenCarrier k hk type → σE t = State.start_state t) :
    ∃ σ,
      run? ([valid_ops.shiftL (oddCarrier k hk type) e] ++
          carrierAdds k type e (oddCarrier k hk type) 1) σE = some σ ∧
      (∀ t, t ≠ oddCarrier k hk type → σ t =
        (State.shiftLReg σE (oddCarrier k hk type) e) t) ∧
      (∀ u, σ (oddCarrier k hk type) u = parityCarrierRow type e 1 u) := by
  let odd := oddCarrier k hk type
  let σS := State.shiftLReg σE odd e
  have hbasis :
      ∀ j, j ≠ odd → parityDegree type k j % 2 = 1 →
        ∀ v, σS j v = State.start_state j v := by
    dsimp [σS, odd]
    exact shiftL_odd_preserves_basis_sources k hk type e hpresE
  rcases carrierAdds_run_effect_basis (k := k) (by omega) type e odd 1 σS hbasis
    with ⟨σ, hrunAdds, hpres, hdst⟩
  refine ⟨σ, ?_, hpres, ?_⟩
  · simp [σS, odd, applyOp?, hrunAdds]
  · intro u
    rw [hdst u]
    dsimp [parityCarrierRow, σS, odd]
    by_cases hsel : parityDegree type k u % 2 = 1
    · simp [hsel]
      by_cases huo : u = oddCarrier k hk type
      · subst huo
        have hodd_ne_even :
            oddCarrier k hk type ≠ evenCarrier k hk type :=
          Ne.symm (evenCarrier_ne_oddCarrier k hk type)
        have hσEodd := hpresE (oddCarrier k hk type) hodd_ne_even
        have hcoord := congrFun hσEodd (oddCarrier k hk type)
        rw [parityDegree_oddCarrier k hk type]
        simp [State.start_state, hcoord, twoPowInt]
      ·
        have hodd_ne_even :
            oddCarrier k hk type ≠ evenCarrier k hk type :=
          Ne.symm (evenCarrier_ne_oddCarrier k hk type)
        have hσEodd := hpresE (oddCarrier k hk type) hodd_ne_even
        have hcoord := congrFun hσEodd u
        simp [hcoord, State.start_state, huo]
    · simp [hsel]
      by_cases huo : u = oddCarrier k hk type
      · subst huo
        have h1 := parityDegree_oddCarrier_mod k hk type
        omega
      ·
        have hodd_ne_even :
            oddCarrier k hk type ≠ evenCarrier k hk type :=
          Ne.symm (evenCarrier_ne_oddCarrier k hk type)
        have hσEodd := hpresE (oddCarrier k hk type) hodd_ne_even
        have hcoord := congrFun hσEodd u
        simp [hcoord, State.start_state, huo]

lemma combineParityCarriers_run_effect
    {k : ℕ} (even odd : Fin k) (hne : even ≠ odd) (σ : State k) :
    ∃ τ,
      run? (combineParityCarriers even odd) σ = some τ ∧
      (∀ u, τ odd u = σ odd u + σ even u) ∧
      (∀ u, τ even u = σ even u - σ odd u) ∧
      (∀ t, t ≠ even → t ≠ odd → τ t = σ t) := by
  let σ1 := State.addScaledReg σ odd even false 0
  let σ2 := State.shiftLReg σ1 even 1
  let τ := State.addScaledReg σ2 even odd true 0
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · simp [combineParityCarriers, run?, applyOp?, σ1, σ2, τ]
  · intro u
    simp [τ, σ2, σ1, State.addScaledReg, State.shiftLReg, State.setReg,
      Register.addScaled, Register.shiftL, hne, Ne.symm hne]
  · intro u
    simp [τ, σ2, σ1, State.addScaledReg, State.shiftLReg, State.setReg,
      Register.addScaled, Register.shiftL, hne, Ne.symm hne]
    ring
  · intro t hte hto
    ext u
    simp [τ, σ2, σ1, State.addScaledReg, State.shiftLReg, State.setReg,
      Register.addScaled, Register.shiftL, hne, Ne.symm hne, hte, hto]

lemma parityBuildWithCombine_run_effect
    (k : ℕ) (hk : k ≥ 4) (type : PointPairType) (e : ℕ) :
    let even := evenCarrier k hk type
    let odd := oddCarrier k hk type
    let buildEven := carrierAdds k type e even 0
    let buildOdd := [valid_ops.shiftL odd e] ++ carrierAdds k type e odd 1
    let build := buildEven ++ buildOdd ++ combineParityCarriers even odd
    ∃ σ,
      run? build State.start_state = some σ ∧
      (∀ u, σ odd u = expectedRow (k := k) (positivePointOfPair type e) u) ∧
      (∀ u, σ even u = expectedRow (k := k) (negativePointOfPair type e) u) := by
  intro even odd buildEven buildOdd build
  rcases carrierAdds_even_from_start k hk type e with
    ⟨σE, hrunEven, hpresE, hEvenRow⟩
  rcases carrierAdds_odd_after_even k hk type e hpresE with
    ⟨σO, hrunOdd, hpresOdd, hOddRow⟩
  have hEvenAfterOdd : ∀ u, σO even u = parityCarrierRow type e 0 u := by
    intro u
    have heo : even ≠ oddCarrier k hk type := by
      dsimp [even]
      exact evenCarrier_ne_oddCarrier k hk type
    rw [hpresOdd even heo]
    simp [State.shiftLReg, State.setReg, heo]
    exact hEvenRow u
  rcases combineParityCarriers_run_effect even odd
      (evenCarrier_ne_oddCarrier k hk type) σO with
    ⟨σC, hrunCombine, hOddCombine, hEvenCombine, _hCombinePres⟩
  have hrunOdd' : run? buildOdd σE = some σO := by
    simpa [buildOdd, odd] using hrunOdd
  have hrunCombine' : run? (combineParityCarriers even odd) σO = some σC := hrunCombine
  refine ⟨σC, ?_, ?_, ?_⟩
  · simp [build, buildEven, even, run?_append, hrunEven, hrunOdd', hrunCombine']
  · intro u
    rw [hOddCombine u, hOddRow u, hEvenAfterOdd u]
    exact parityCarrierRows_positive_expected type e u
  · intro u
    rw [hEvenCombine u, hEvenAfterOdd u, hOddRow u]
    exact parityCarrierRows_negative_expected type e u

lemma matchesAt_of_row_eq
    {k : ℕ} (hk : 0 < k) {σ : State k} {i : Fin k} {pt : Point}
    (hrow : ∀ u, σ i u = expectedRow (k := k) pt u) :
    matchesAt_pointRow_state (k := k) hk σ i pt = true := by
  unfold matchesAt_pointRow_state regEqExpected
  apply List.all_eq_true.mpr
  intro u _
  exact decide_eq_true_iff.mpr (hrow u)

lemma addConstFrom_NoPhase {k : ℕ} (dst src : Fin k) (c : ℤ) :
    NoPhase (addConstFrom (k := k) dst src c) := by
  exact NoPhase_of_onlyAddScaled (onlyAddScaled_addConstFrom (k := k) dst src c)

lemma carrierAddsList_NoPhase
    {k : ℕ} (type : PointPairType) (e : ℕ)
    (dst : Fin k) (parity : ℕ) :
    ∀ xs, NoPhase (carrierAddsList type e dst parity xs)
  | [] => by
      intro i h
      simp [carrierAddsList] at h
  | j :: js => by
      dsimp [carrierAddsList]
      by_cases hp : parityDegree type k j % 2 = parity
      · simp [hp]
        by_cases hj : j = dst
        · simp [hj]
          exact carrierAddsList_NoPhase type e dst parity js
        · simp [hj]
          exact NoPhase_append
            (addConstFrom_NoPhase dst j (twoPowInt (e * parityDegree type k j)))
            (carrierAddsList_NoPhase type e dst parity js)
      · simp [hp]
        exact carrierAddsList_NoPhase type e dst parity js

lemma carrierAdds_NoPhase
    {k : ℕ} (type : PointPairType) (e : ℕ) (dst : Fin k) (parity : ℕ) :
    NoPhase (carrierAdds k type e dst parity) := by
  rw [carrierAdds_eq_carrierAddsList type e dst parity]
  exact carrierAddsList_NoPhase type e dst parity (List.finRange k)

lemma combineParityCarriers_NoPhase {k : ℕ} (even odd : Fin k) :
    NoPhase (combineParityCarriers even odd) := by
  intro i h
  simp [combineParityCarriers] at h

lemma apply_Op_inverse_NoPhase {k : ℕ} {p : Prog k} (hp : NoPhase p) :
    NoPhase (apply_Op_inverse p) := by
  unfold apply_Op_inverse
  exact NoPhase_map_inv_of_NoPhase (NoPhase_reverse hp)

lemma parityBuild_NoPhase
    (k : ℕ) (hk : k ≥ 4) (type : PointPairType) (e : ℕ) :
    let even := evenCarrier k hk type
    let odd := oddCarrier k hk type
    let buildEven := carrierAdds k type e even 0
    let buildOdd := [valid_ops.shiftL odd e] ++ carrierAdds k type e odd 1
    let build := buildEven ++ buildOdd ++ combineParityCarriers even odd
    NoPhase build := by
  intro even odd buildEven buildOdd build
  have hShift : NoPhase ([valid_ops.shiftL odd e] : Prog k) := by
    intro i h
    simp at h
  have hBuildOdd : NoPhase buildOdd := by
    dsimp [buildOdd]
    exact NoPhase_append hShift (carrierAdds_NoPhase type e odd 1)
  dsimp [build, buildEven]
  exact NoPhase_append
    (NoPhase_append (carrierAdds_NoPhase type e even 0) hBuildOdd)
    (combineParityCarriers_NoPhase even odd)

lemma parityBuild_WellFormed
    (k : ℕ) (hk : k ≥ 4) (type : PointPairType) (e : ℕ) :
    let even := evenCarrier k hk type
    let odd := oddCarrier k hk type
    let buildEven := carrierAdds k type e even 0
    let buildOdd := [valid_ops.shiftL odd e] ++ carrierAdds k type e odd 1
    let build := buildEven ++ buildOdd ++ combineParityCarriers even odd
    Prog.WellFormed build := by
  intro even odd buildEven buildOdd build
  have hEven : Prog.WellFormed buildEven := by
    dsimp [buildEven]
    apply carrierAdds_WellFormed
  have hShift : Prog.WellFormed ([valid_ops.shiftL odd e] : Prog k) := by
    intro op hop
    simp at hop
    subst op
    simp [Prog.OpOK]
  have hOdd : Prog.WellFormed buildOdd := by
    dsimp [buildOdd]
    exact WellFormed_append hShift (carrierAdds_WellFormed k type e odd 1)
  have hCombine : Prog.WellFormed (combineParityCarriers even odd) := by
    apply combineParityCarriers_WellFormed
    dsimp [even, odd]
    exact evenCarrier_ne_oddCarrier k hk type
  dsimp [build]
  exact WellFormed_append (WellFormed_append hEven hOdd) hCombine

lemma generateParityPairBlock_ProgConsumesPts
    (k : ℕ) (hk : k ≥ 4) (type : PointPairType) (e : ℕ) :
    ProgConsumesPts (by omega) State.start_state
      (generateParityPairBlock k hk type e)
      [positivePointOfPair type e, negativePointOfPair type e] := by
  let even := evenCarrier k hk type
  let odd := oddCarrier k hk type
  let buildEven := carrierAdds k type e even 0
  let buildOdd := [valid_ops.shiftL odd e] ++ carrierAdds k type e odd 1
  let build := buildEven ++ buildOdd ++ combineParityCarriers even odd
  rcases parityBuildWithCombine_run_effect k hk type e with
    ⟨σmid, hrunBuild, hposRow, hnegRow⟩
  have hrunBuild' : run? build (State.start_state (k := k)) = some σmid := by
    simpa [build, buildEven, buildOdd, even, odd] using hrunBuild
  have hbuildNP : NoPhase build := by
    dsimp [build, buildEven, buildOdd, even, odd]
    exact parityBuild_NoPhase k hk type e
  have hbuildWF : Prog.WellFormed build := by
    dsimp [build, buildEven, buildOdd, even, odd]
    exact parityBuild_WellFormed k hk type e
  have hbuildC :
      ProgConsumesPts (by omega) (State.start_state (k := k)) build [] :=
    progConsumesPts_of_noPhase_run (k := k) (by omega) hbuildNP hrunBuild'
  have hmatchPos :
      matchesAt_pointRow_state (k := k) (by omega) σmid odd (positivePointOfPair type e) = true :=
    matchesAt_of_row_eq (k := k) (by omega) hposRow
  have hmatchNeg :
      matchesAt_pointRow_state (k := k) (by omega) σmid even (negativePointOfPair type e) = true :=
    matchesAt_of_row_eq (k := k) (by omega) hnegRow
  have hphaseC :
      ProgConsumesPts (by omega) σmid
        ([valid_ops.phaseProduct odd, valid_ops.phaseProduct even] : Prog k)
        [positivePointOfPair type e, negativePointOfPair type e] := by
    simp [ProgConsumesPts, hmatchPos, hmatchNeg]
  have hprefixC :
      ProgConsumesPts (by omega) (State.start_state (k := k))
        (build ++ [valid_ops.phaseProduct odd, valid_ops.phaseProduct even])
        [positivePointOfPair type e, negativePointOfPair type e] := by
    simpa using
      progConsumesPts_append (k := k) (by omega)
        (p := build) (q := [valid_ops.phaseProduct odd, valid_ops.phaseProduct even])
        (σ := State.start_state (k := k)) (σret := σmid)
        (a := []) (b := [positivePointOfPair type e, negativePointOfPair type e])
        hbuildC hrunBuild' hphaseC
  have hprefixRun :
      run? (build ++ [valid_ops.phaseProduct odd, valid_ops.phaseProduct even])
          (State.start_state (k := k)) = some σmid := by
    simp [run?_append, hrunBuild', applyOp?]
  have hcleanupRun :
      run? (apply_Op_inverse build) σmid = some (State.start_state (k := k)) :=
    State.run?_inverse_undoes_WF build hbuildWF (State.start_state (k := k)) σmid hrunBuild'
  have hcleanupNP : NoPhase (apply_Op_inverse build) :=
    apply_Op_inverse_NoPhase hbuildNP
  have hcleanupC :
      ProgConsumesPts (by omega) σmid (apply_Op_inverse build) [] :=
    progConsumesPts_of_noPhase_run (k := k) (by omega) hcleanupNP hcleanupRun
  simpa [generateParityPairBlock, even, odd, buildEven, buildOdd, build, List.append_assoc] using
    progConsumesPts_append (k := k) (by omega)
      (p := build ++ [valid_ops.phaseProduct odd, valid_ops.phaseProduct even])
      (q := apply_Op_inverse build)
      (σ := State.start_state (k := k)) (σret := σmid)
      (a := [positivePointOfPair type e, negativePointOfPair type e]) (b := [])
      hprefixC hprefixRun hcleanupC

lemma generateParityPairBlock_returns_to_start
    (k : ℕ) (hk : k ≥ 4) (type : PointPairType) (e : ℕ) :
    run? (generateParityPairBlock k hk type e) State.start_state =
      some (State.start_state (k := k)) := by
  let even := evenCarrier k hk type
  let odd := oddCarrier k hk type
  let buildEven := carrierAdds k type e even 0
  let buildOdd := [valid_ops.shiftL odd e] ++ carrierAdds k type e odd 1
  let build := buildEven ++ buildOdd ++ combineParityCarriers even odd
  rcases parityBuildWithCombine_run_effect k hk type e with
    ⟨σmid, hrunBuild, _hposRow, _hnegRow⟩
  have hrunBuild' : run? build (State.start_state (k := k)) = some σmid := by
    simpa [build, buildEven, buildOdd, even, odd] using hrunBuild
  have hbuildWF : Prog.WellFormed build := by
    dsimp [build, buildEven, buildOdd, even, odd]
    exact parityBuild_WellFormed k hk type e
  have hcleanupRun :
      run? (apply_Op_inverse build) σmid = some (State.start_state (k := k)) :=
    State.run?_inverse_undoes_WF build hbuildWF (State.start_state (k := k)) σmid hrunBuild'
  change run? ((build ++ [valid_ops.phaseProduct odd, valid_ops.phaseProduct even]) ++
      apply_Op_inverse build) (State.start_state (k := k)) =
    some (State.start_state (k := k))
  simp [run?_append, hrunBuild', hcleanupRun, applyOp?]

lemma start_zero_row_int0
    (k : ℕ) (hk : k ≥ 4) :
    ∀ u : Fin k,
      State.start_state (k := k) ⟨0, by omega⟩ u =
        expectedRow (k := k) (.int 0) u := by
  intro u
  by_cases hu : u = ⟨0, by omega⟩
  · subst hu
    simp [State.start_state, expectedRow]
  · have hval : u.val ≠ 0 := by
      intro h0
      apply hu
      apply Fin.ext
      simpa using h0
    have hpos : 0 < u.val := Nat.pos_of_ne_zero hval
    have hpow : (0 : ℤ) ^ u.val = 0 := by
      exact zero_pow (Nat.ne_of_gt hpos)
    simp [State.start_state, expectedRow, hu, hpow]

lemma start_last_row_frac0
    (k : ℕ) (hk : k ≥ 4) :
    ∀ u : Fin k,
      State.start_state (k := k) ⟨k - 1, by omega⟩ u =
        expectedRow (k := k) (.frac 0) u := by
  intro u
  let last : Fin k := ⟨k - 1, by omega⟩
  by_cases hu : u = last
  · subst hu
    simp [State.start_state, expectedRow, last]
  · have hlt : u.val < k - 1 := by
      have hle : u.val ≤ k - 1 := Nat.le_pred_of_lt u.isLt
      have hne : u.val ≠ k - 1 := by
        intro hv
        apply hu
        apply Fin.ext
        simpa [last] using hv
      omega
    have hpos : 0 < k - 1 - u.val := by omega
    have hpow : (0 : ℤ) ^ (k - 1 - u.val) = 0 :=
      zero_pow (Nat.ne_of_gt hpos)
    have hulast : ¬u = ⟨k - 1, by omega⟩ := by
      intro h
      exact hu (by simpa [last] using h)
    simp [State.start_state, expectedRow, hulast, hpow]

lemma initialBuild_run_effect
    (k : ℕ) (hk : k ≥ 4) :
    let r0 : Fin k := ⟨0, by omega⟩
    let r1 : Fin k := ⟨1, by omega⟩
    let r2 : Fin k := ⟨2, by omega⟩
    let rlast : Fin k := ⟨k - 1, by omega⟩
    let buildEven := carrierAdds k .integer 0 r2 0
    let buildOdd := carrierAdds k .integer 0 r1 1
    let build := buildEven ++ buildOdd ++ combineParityCarriers r2 r1
    ∃ σ,
      run? build State.start_state = some σ ∧
      (∀ u, σ r0 u = expectedRow (k := k) (.int 0) u) ∧
      (∀ u, σ rlast u = expectedRow (k := k) (.frac 0) u) ∧
      (∀ u, σ r1 u = expectedRow (k := k) (.int 1) u) ∧
      (∀ u, σ r2 u = expectedRow (k := k) (.int (-1)) u) := by
  intro r0 r1 r2 rlast buildEven buildOdd build
  have hbasisEven :
      ∀ j, j ≠ r2 → parityDegree .integer k j % 2 = 0 →
        ∀ v, (State.start_state (k := k)) j v = State.start_state j v := by
    intro j _ _ v
    rfl
  rcases carrierAdds_run_effect_basis (k := k) (by omega) .integer 0 r2 0
      (State.start_state (k := k)) hbasisEven with ⟨σE, hrunEven, hpresE, hdstE⟩
  have hEvenRow : ∀ u, σE r2 u = parityCarrierRow .integer 0 0 u := by
    intro u
    rw [hdstE u]
    dsimp [parityCarrierRow, parityDegree]
    by_cases hsel : u.val % 2 = 0
    · simp [hsel, twoPowInt]
      by_cases hur2 : u = r2
      · simp [hur2]
      · simp [hur2]
    · simp [hsel]
      by_cases hur2 : u = r2
      · subst hur2
        norm_num at hsel
      · simp [hur2]
  have hbasisOdd :
      ∀ j, j ≠ r1 → parityDegree .integer k j % 2 = 1 →
        ∀ v, σE j v = State.start_state j v := by
    intro j hj1 hp v
    have hj2 : j ≠ r2 := by
      intro h
      subst h
      norm_num [parityDegree] at hp
    exact congrFun (hpresE j hj2) v
  rcases carrierAdds_run_effect_basis (k := k) (by omega) .integer 0 r1 1 σE hbasisOdd
      with ⟨σO, hrunOdd, hpresOdd, hdstO⟩
  have hOddRow : ∀ u, σO r1 u = parityCarrierRow .integer 0 1 u := by
    intro u
    rw [hdstO u]
    dsimp [parityCarrierRow, parityDegree]
    by_cases hsel : u.val % 2 = 1
    · simp [hsel, twoPowInt]
      by_cases hur1 : u = r1
      ·
        have hσE : σE r1 r1 = State.start_state (k := k) r1 r1 := by
          have hr1_ne_r2 : r1 ≠ r2 := by
            intro h
            have hv := congrArg Fin.val h
            norm_num at hv
          exact congrFun (hpresE r1 hr1_ne_r2) r1
        simp [hur1, hσE, State.start_state]
      ·
        have hσE : σE r1 u = State.start_state (k := k) r1 u := by
          have hr1_ne_r2 : r1 ≠ r2 := by
            intro h
            have hv := congrArg Fin.val h
            norm_num at hv
          exact congrFun (hpresE r1 hr1_ne_r2) u
        simp [hur1, hσE, State.start_state]
    · simp [hsel]
      by_cases hur1 : u = r1
      · subst hur1
        norm_num at hsel
      ·
        have hσE : σE r1 u = State.start_state (k := k) r1 u := by
          have hr1_ne_r2 : r1 ≠ r2 := by
            intro h
            have hv := congrArg Fin.val h
            norm_num at hv
          exact congrFun (hpresE r1 hr1_ne_r2) u
        simp [hur1, hσE, State.start_state]
  have hEvenAfterOdd : ∀ u, σO r2 u = parityCarrierRow .integer 0 0 u := by
    intro u
    have hr2_ne_r1 : r2 ≠ r1 := by
      intro h
      have hv := congrArg Fin.val h
      norm_num at hv
    rw [hpresOdd r2 hr2_ne_r1]
    exact hEvenRow u
  rcases combineParityCarriers_run_effect r2 r1 (by
      intro h
      have hv := congrArg Fin.val h
      norm_num at hv) σO with
    ⟨σC, hrunCombine, hOddCombine, hEvenCombine, hCombinePres⟩
  have hrunOdd' : run? buildOdd σE = some σO := by
    simpa [buildOdd] using hrunOdd
  refine ⟨σC, ?_, ?_, ?_, ?_, ?_⟩
  · simp [build, buildEven, run?_append, hrunEven, hrunOdd', hrunCombine]
  · intro u
    have hr0_ne_r2 : r0 ≠ r2 := by
      intro h
      have hv := congrArg Fin.val h
      norm_num at hv
    have hr0_ne_r1 : r0 ≠ r1 := by
      intro h
      have hv := congrArg Fin.val h
      norm_num at hv
    rw [hCombinePres r0 hr0_ne_r2 hr0_ne_r1]
    rw [hpresOdd r0 hr0_ne_r1, hpresE r0 hr0_ne_r2]
    exact start_zero_row_int0 k hk u
  · intro u
    have hlast_ne_r2 : rlast ≠ r2 := by
      intro h
      have hv := congrArg Fin.val h
      simp [rlast, r2] at hv
      omega
    have hlast_ne_r1 : rlast ≠ r1 := by
      intro h
      have hv := congrArg Fin.val h
      simp [rlast, r1] at hv
      omega
    rw [hCombinePres rlast hlast_ne_r2 hlast_ne_r1]
    rw [hpresOdd rlast hlast_ne_r1, hpresE rlast hlast_ne_r2]
    exact start_last_row_frac0 k hk u
  · intro u
    rw [hOddCombine u, hOddRow u, hEvenAfterOdd u]
    simpa [positivePointOfPair] using
      parityCarrierRows_positive_expected (k := k) .integer 0 u
  · intro u
    rw [hEvenCombine u, hEvenAfterOdd u, hOddRow u]
    simpa [negativePointOfPair] using
      parityCarrierRows_negative_expected (k := k) .integer 0 u

lemma initialBuild_NoPhase (k : ℕ) (hk : k ≥ 4) :
    let r1 : Fin k := ⟨1, by omega⟩
    let r2 : Fin k := ⟨2, by omega⟩
    let buildEven := carrierAdds k .integer 0 r2 0
    let buildOdd := carrierAdds k .integer 0 r1 1
    let build := buildEven ++ buildOdd ++ combineParityCarriers r2 r1
    NoPhase build := by
  intro r1 r2 buildEven buildOdd build
  dsimp [build, buildEven, buildOdd]
  exact NoPhase_append
    (NoPhase_append (carrierAdds_NoPhase .integer 0 r2 0)
      (carrierAdds_NoPhase .integer 0 r1 1))
    (combineParityCarriers_NoPhase r2 r1)

lemma initialBuild_WellFormed (k : ℕ) (hk : k ≥ 4) :
    let r1 : Fin k := ⟨1, by omega⟩
    let r2 : Fin k := ⟨2, by omega⟩
    let buildEven := carrierAdds k .integer 0 r2 0
    let buildOdd := carrierAdds k .integer 0 r1 1
    let build := buildEven ++ buildOdd ++ combineParityCarriers r2 r1
    Prog.WellFormed build := by
  intro r1 r2 buildEven buildOdd build
  dsimp [build, buildEven, buildOdd]
  exact WellFormed_append
    (WellFormed_append
      (carrierAdds_WellFormed k .integer 0 r2 0)
      (carrierAdds_WellFormed k .integer 0 r1 1))
    (combineParityCarriers_WellFormed (by
      intro h
      have hv := congrArg Fin.val h
      norm_num at hv))

lemma generateParityInitialBlock_ProgConsumesPts
    (k : ℕ) (hk : k ≥ 4) :
    ProgConsumesPts (by omega) State.start_state
      (generateParityInitialBlock k hk)
      [.int 0, .frac 0, .int 1, .int (-1)] := by
  let r0 : Fin k := ⟨0, by omega⟩
  let r1 : Fin k := ⟨1, by omega⟩
  let r2 : Fin k := ⟨2, by omega⟩
  let rlast : Fin k := ⟨k - 1, by omega⟩
  let buildEven := carrierAdds k .integer 0 r2 0
  let buildOdd := carrierAdds k .integer 0 r1 1
  let build := buildEven ++ buildOdd ++ combineParityCarriers r2 r1
  rcases initialBuild_run_effect k hk with
    ⟨σmid, hrunBuild, hrow0, hrowLast, hrow1, hrow2⟩
  have hrunBuild' : run? build (State.start_state (k := k)) = some σmid := by
    simpa [build, buildEven, buildOdd, r0, r1, r2, rlast] using hrunBuild
  have hbuildNP : NoPhase build := by
    dsimp [build, buildEven, buildOdd, r1, r2]
    exact initialBuild_NoPhase k hk
  have hbuildWF : Prog.WellFormed build := by
    dsimp [build, buildEven, buildOdd, r1, r2]
    exact initialBuild_WellFormed k hk
  have hbuildC :
      ProgConsumesPts (by omega) (State.start_state (k := k)) build [] :=
    progConsumesPts_of_noPhase_run (k := k) (by omega) hbuildNP hrunBuild'
  have hm0 := matchesAt_of_row_eq (k := k) (by omega) (σ := σmid) (i := r0) (pt := .int 0) hrow0
  have hminf := matchesAt_of_row_eq (k := k) (by omega) (σ := σmid) (i := rlast) (pt := .frac 0) hrowLast
  have hm1 := matchesAt_of_row_eq (k := k) (by omega) (σ := σmid) (i := r1) (pt := .int 1) hrow1
  have hmneg1 := matchesAt_of_row_eq (k := k) (by omega) (σ := σmid) (i := r2) (pt := .int (-1)) hrow2
  have hphaseC :
      ProgConsumesPts (by omega) σmid
        ([valid_ops.phaseProduct r0, valid_ops.phaseProduct rlast,
          valid_ops.phaseProduct r1, valid_ops.phaseProduct r2] : Prog k)
        [.int 0, .frac 0, .int 1, .int (-1)] := by
    simp [ProgConsumesPts, hm0, hminf, hm1, hmneg1]
  have hprefixC :
      ProgConsumesPts (by omega) (State.start_state (k := k))
        (build ++ [valid_ops.phaseProduct r0, valid_ops.phaseProduct rlast,
          valid_ops.phaseProduct r1, valid_ops.phaseProduct r2])
        [.int 0, .frac 0, .int 1, .int (-1)] := by
    simpa using
      progConsumesPts_append (k := k) (by omega)
        (p := build)
        (q := [valid_ops.phaseProduct r0, valid_ops.phaseProduct rlast,
          valid_ops.phaseProduct r1, valid_ops.phaseProduct r2])
        (σ := State.start_state (k := k)) (σret := σmid)
        (a := []) (b := [.int 0, .frac 0, .int 1, .int (-1)])
        hbuildC hrunBuild' hphaseC
  have hprefixRun :
      run? (build ++ [valid_ops.phaseProduct r0, valid_ops.phaseProduct rlast,
          valid_ops.phaseProduct r1, valid_ops.phaseProduct r2])
        (State.start_state (k := k)) = some σmid := by
    simp [run?_append, hrunBuild', applyOp?]
  have hcleanupRun :
      run? (apply_Op_inverse build) σmid = some (State.start_state (k := k)) :=
    State.run?_inverse_undoes_WF build hbuildWF (State.start_state (k := k)) σmid hrunBuild'
  have hcleanupNP : NoPhase (apply_Op_inverse build) :=
    apply_Op_inverse_NoPhase hbuildNP
  have hcleanupC :
      ProgConsumesPts (by omega) σmid (apply_Op_inverse build) [] :=
    progConsumesPts_of_noPhase_run (k := k) (by omega) hcleanupNP hcleanupRun
  simpa [generateParityInitialBlock, r0, r1, r2, rlast, buildEven, buildOdd, build,
    List.append_assoc] using
    progConsumesPts_append (k := k) (by omega)
      (p := build ++ [valid_ops.phaseProduct r0, valid_ops.phaseProduct rlast,
        valid_ops.phaseProduct r1, valid_ops.phaseProduct r2])
      (q := apply_Op_inverse build)
      (σ := State.start_state (k := k)) (σret := σmid)
      (a := [.int 0, .frac 0, .int 1, .int (-1)]) (b := [])
      hprefixC hprefixRun hcleanupC

lemma generateParityInitialBlock_returns_to_start
    (k : ℕ) (hk : k ≥ 4) :
    run? (generateParityInitialBlock k hk) State.start_state =
      some (State.start_state (k := k)) := by
  let r0 : Fin k := ⟨0, by omega⟩
  let r1 : Fin k := ⟨1, by omega⟩
  let r2 : Fin k := ⟨2, by omega⟩
  let rlast : Fin k := ⟨k - 1, by omega⟩
  let buildEven := carrierAdds k .integer 0 r2 0
  let buildOdd := carrierAdds k .integer 0 r1 1
  let build := buildEven ++ buildOdd ++ combineParityCarriers r2 r1
  rcases initialBuild_run_effect k hk with
    ⟨σmid, hrunBuild, _hrow0, _hrowLast, _hrow1, _hrow2⟩
  have hrunBuild' : run? build (State.start_state (k := k)) = some σmid := by
    simpa [build, buildEven, buildOdd, r0, r1, r2, rlast] using hrunBuild
  have hbuildWF : Prog.WellFormed build := by
    dsimp [build, buildEven, buildOdd, r1, r2]
    exact initialBuild_WellFormed k hk
  have hcleanupRun :
      run? (apply_Op_inverse build) σmid = some (State.start_state (k := k)) :=
    State.run?_inverse_undoes_WF build hbuildWF (State.start_state (k := k)) σmid hrunBuild'
  change run? ((build ++ [valid_ops.phaseProduct r0, valid_ops.phaseProduct rlast,
      valid_ops.phaseProduct r1, valid_ops.phaseProduct r2]) ++
      apply_Op_inverse build) (State.start_state (k := k)) =
    some (State.start_state (k := k))
  simp [run?_append, hrunBuild', hcleanupRun, applyOp?]

lemma positivePointOfPair_eq_streamPoint (i : ℕ) :
    positivePointOfPair (pairKindOfIndex i) (pairExponentOfIndex i) =
      streamPoint (4 + 2 * i) := by
  unfold positivePointOfPair pairKindOfIndex pairExponentOfIndex
  rw [show 4 + 2 * i = 2 * i + 4 by omega]
  by_cases hmod : i % 2 = 0
  · have h4mod : (2 * i) % 4 = 0 := by omega
    have hdiv : (2 * i) / 4 = i / 2 := by omega
    simp [streamPoint, hmod, h4mod, hdiv, twoPowInt]
  · have hmod1 : i % 2 = 1 := by omega
    have h4mod : (2 * i) % 4 = 2 := by omega
    have hdiv : (2 * i) / 4 = i / 2 := by omega
    simp [streamPoint, hmod1, h4mod, hdiv, twoPowInt]

lemma negativePointOfPair_eq_streamPoint (i : ℕ) :
    negativePointOfPair (pairKindOfIndex i) (pairExponentOfIndex i) =
      streamPoint (5 + 2 * i) := by
  unfold negativePointOfPair pairKindOfIndex pairExponentOfIndex
  rw [show 5 + 2 * i = (1 + 2 * i) + 4 by omega]
  by_cases hmod : i % 2 = 0
  · have h4mod : (1 + 2 * i) % 4 = 1 := by omega
    have hdiv : (1 + 2 * i) / 4 = i / 2 := by omega
    simp [streamPoint, hmod, h4mod, hdiv, twoPowInt]
  · have hmod1 : i % 2 = 1 := by omega
    have h4mod : (1 + 2 * i) % 4 = 3 := by omega
    have hdiv : (1 + 2 * i) / 4 = i / 2 := by omega
    simp [streamPoint, hmod1, h4mod, hdiv, twoPowInt]

def pairBlockPoints (i : ℕ) : List Point :=
  [positivePointOfPair (pairKindOfIndex i) (pairExponentOfIndex i),
    negativePointOfPair (pairKindOfIndex i) (pairExponentOfIndex i)]

def pairBlocksList (k : ℕ) (hk : k ≥ 4) : List ℕ → Prog k
  | [] => []
  | i :: is =>
      generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i) ++
        pairBlocksList k hk is

lemma generateParityPairBlocks_fold_eq_pairBlocksList
    (k : ℕ) (hk : k ≥ 4) :
    ∀ xs (acc : Prog k),
      List.foldl
        (fun acc i =>
          acc ++ generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i))
        acc xs =
      acc ++ pairBlocksList k hk xs
  | [], acc => by
      simp [pairBlocksList]
  | i :: is, acc => by
      rw [List.foldl]
      rw [foldl_append_hom
        (fun i => generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i))
        (acc ++ generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i))
        is]
      have ih0 := generateParityPairBlocks_fold_eq_pairBlocksList k hk is ([] : Prog k)
      simpa [pairBlocksList, List.append_assoc] using ih0

lemma generateParityPairBlocks_eq_pairBlocksList
    (k : ℕ) (hk : k ≥ 4) (pairCount : ℕ) :
    generateParityPairBlocks k hk pairCount =
      pairBlocksList k hk (List.range pairCount) := by
  unfold generateParityPairBlocks
  simpa using
    generateParityPairBlocks_fold_eq_pairBlocksList k hk (List.range pairCount) ([] : Prog k)

lemma pairBlocksList_ProgConsumesPts
    (k : ℕ) (hk : k ≥ 4) :
    ∀ xs : List ℕ,
      ProgConsumesPts (by omega) State.start_state
        (pairBlocksList k hk xs) (List.flatMap pairBlockPoints xs)
  | [] => by
      simp [pairBlocksList, ProgConsumesPts]
  | i :: is => by
      have hblock :
          ProgConsumesPts (by omega) State.start_state
            (generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i))
            (pairBlockPoints i) := by
        simpa [pairBlockPoints] using
          generateParityPairBlock_ProgConsumesPts k hk
            (pairKindOfIndex i) (pairExponentOfIndex i)
      have hrun :
          run? (generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i))
              (State.start_state (k := k)) =
            some (State.start_state (k := k)) :=
        generateParityPairBlock_returns_to_start k hk
          (pairKindOfIndex i) (pairExponentOfIndex i)
      have htail := pairBlocksList_ProgConsumesPts k hk is
      simpa [pairBlocksList, pairBlockPoints, List.bind_eq_flatMap] using
        progConsumesPts_append (k := k) (by omega)
          (p := generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i))
          (q := pairBlocksList k hk is)
          (σ := State.start_state (k := k)) (σret := State.start_state (k := k))
          (a := pairBlockPoints i) (b := List.flatMap pairBlockPoints is)
          hblock hrun htail

lemma pairBlocksList_returns_to_start
    (k : ℕ) (hk : k ≥ 4) :
    ∀ xs : List ℕ,
      run? (pairBlocksList k hk xs) State.start_state =
        some (State.start_state (k := k))
  | [] => by
      simp [pairBlocksList]
  | i :: is => by
      have hblock :
          run? (generateParityPairBlock k hk (pairKindOfIndex i) (pairExponentOfIndex i))
              (State.start_state (k := k)) =
            some (State.start_state (k := k)) :=
        generateParityPairBlock_returns_to_start k hk
          (pairKindOfIndex i) (pairExponentOfIndex i)
      have htail := pairBlocksList_returns_to_start k hk is
      simp [pairBlocksList, run?_append, hblock, htail]

lemma generateParityPairBlocks_ProgConsumesPts
    (k : ℕ) (hk : k ≥ 4) (pairCount : ℕ) :
    ProgConsumesPts (by omega) State.start_state
      (generateParityPairBlocks k hk pairCount)
      (List.flatMap pairBlockPoints (List.range pairCount)) := by
  simpa [generateParityPairBlocks_eq_pairBlocksList k hk pairCount] using
    pairBlocksList_ProgConsumesPts k hk (List.range pairCount)

lemma generateParityPairBlocks_returns_to_start
    (k : ℕ) (hk : k ≥ 4) (pairCount : ℕ) :
    run? (generateParityPairBlocks k hk pairCount) State.start_state =
      some (State.start_state (k := k)) := by
  simpa [generateParityPairBlocks_eq_pairBlocksList k hk pairCount] using
    pairBlocksList_returns_to_start k hk (List.range pairCount)

lemma generateParitySingletonBlock_ProgConsumesPts
    (k : ℕ) (hk : k ≥ 4) (x : Point) :
    ProgConsumesPts (by omega) State.start_state
      (generateParitySingletonBlock k hk x) [x] := by
  simpa [generateParitySingletonBlock] using
    opsForPointWithProduct_ProgConsumesPts (k := k) (by omega) x

lemma pairBlockPoints_eq_streamPoints (i : ℕ) :
    pairBlockPoints i = [streamPoint (4 + 2 * i), streamPoint (5 + 2 * i)] := by
  simp [pairBlockPoints, positivePointOfPair_eq_streamPoint,
    negativePointOfPair_eq_streamPoint]

lemma streamTail_even (q : ℕ) :
    (List.range (2 * q)).map (fun n => streamPoint (4 + n)) =
      List.flatMap pairBlockPoints (List.range q) := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hrange :
          List.range (2 * (q + 1)) =
            List.range (2 * q) ++ [2 * q, 2 * q + 1] := by
        rw [show 2 * (q + 1) = (2 * q + 1).succ by omega]
        rw [List.range_succ]
        rw [show 2 * q + 1 = (2 * q).succ by omega]
        rw [List.range_succ]
        simp [List.append_assoc]
      rw [hrange, List.map_append, ih]
      rw [show List.range (q + 1) = List.range q ++ [q] by
        rw [show q + 1 = q.succ by omega]
        exact List.range_succ]
      simp [List.flatMap_append, pairBlockPoints_eq_streamPoints]
      congr 1
      omega

lemma streamTail_odd (q : ℕ) :
    (List.range (2 * q + 1)).map (fun n => streamPoint (4 + n)) =
      List.flatMap pairBlockPoints (List.range q) ++ [streamPoint (4 + 2 * q)] := by
  have hrange :
      List.range (2 * q + 1) = List.range (2 * q) ++ [2 * q] := by
    rw [show 2 * q + 1 = (2 * q).succ by omega]
    exact List.range_succ
  simp [hrange, List.map_append, streamTail_even q]

lemma streamTail_split (rem : ℕ) :
    (List.range rem).map (fun n => streamPoint (4 + n)) =
      List.flatMap pairBlockPoints (List.range (rem / 2)) ++
        if rem % 2 = 1 then [streamPoint (4 + 2 * (rem / 2))] else [] := by
  have hmod := Nat.mod_two_eq_zero_or_one rem
  rcases hmod with hmod | hmod
  · have hrem : rem = 2 * (rem / 2) := by
      have h := Nat.div_add_mod rem 2
      omega
    rw [hrem, streamTail_even]
    have hdiv : (2 * (rem / 2)) / 2 = rem / 2 := by omega
    have hmod' : (2 * (rem / 2)) % 2 = 0 := by omega
    simp [hmod', hdiv]
  · have hrem : rem = 2 * (rem / 2) + 1 := by
      have h := Nat.div_add_mod rem 2
      omega
    rw [hrem, streamTail_odd]
    have hdiv : (2 * (rem / 2) + 1) / 2 = rem / 2 := by omega
    have hmod' : (2 * (rem / 2) + 1) % 2 = 1 := by omega
    simp [hmod', hdiv]

lemma range_stream_prefix_tail (rem : ℕ) :
    (List.range (4 + rem)).map streamPoint =
      [.int 0, .frac 0, .int 1, .int (-1)] ++
        (List.range rem).map (fun n => streamPoint (4 + n)) := by
  induction rem with
  | zero =>
      native_decide
  | succ rem ih =>
      rw [show 4 + (rem + 1) = (4 + rem).succ by omega]
      rw [List.range_succ, List.map_append, ih]
      rw [show List.range (rem + 1) =
          List.range rem ++ [rem] by
        rw [show rem + 1 = rem.succ by omega]
        exact List.range_succ]
      simp [List.map_append]

lemma generatedPoints_split_by_rem (rem : ℕ) :
    (List.range (4 + rem)).map streamPoint =
      [.int 0, .frac 0, .int 1, .int (-1)] ++
        List.flatMap pairBlockPoints (List.range (rem / 2)) ++
        if rem % 2 = 1 then [streamPoint (4 + 2 * (rem / 2))] else [] := by
  simp [range_stream_prefix_tail rem, streamTail_split rem]

lemma generatedPoints_split
    (mode : ProductMode) (k : ℕ) (hk : k ≥ 4) :
    generatedPoints mode k =
      [.int 0, .frac 0, .int 1, .int (-1)] ++
        List.flatMap pairBlockPoints (List.range ((mode.pointCount k - 4) / 2)) ++
        if (mode.pointCount k - 4) % 2 = 1 then
          [streamPoint (4 + 2 * ((mode.pointCount k - 4) / 2))]
        else
          [] := by
  have hcount : mode.pointCount k = 4 + (mode.pointCount k - 4) := by
    cases mode <;> simp [ProductMode.pointCount] <;> omega
  have hsub : 4 + (mode.pointCount k - 4) - 4 = mode.pointCount k - 4 := by
    omega
  rw [generatedPoints, hcount]
  simpa [hsub] using generatedPoints_split_by_rem (mode.pointCount k - 4)

/-
  Proves that the parity generation consumes the points in the correct order and
  without violating the safety of the operations (src ≠ dst)
-/

lemma generateParityForMode_ProgConsumesPts
    (mode : ProductMode) (k : ℕ) (hk : k ≥ 4) :
    ProgConsumesPts (by omega) State.start_state
      (generateParityForMode mode k hk) (generatedPoints mode k) := by
  let rem := mode.pointCount k - 4
  let pairCount := rem / 2
  let initPts : List Point := [.int 0, .frac 0, .int 1, .int (-1)]
  let pairsPts : List Point := List.flatMap pairBlockPoints (List.range pairCount)
  let singletonPt : Point := streamPoint (4 + 2 * pairCount)
  have hinitC :
      ProgConsumesPts (by omega) (State.start_state)
        (generateParityInitialBlock k hk) initPts := by
    simpa [initPts] using generateParityInitialBlock_ProgConsumesPts k hk
  have hinitRun :
      run? (generateParityInitialBlock k hk) (State.start_state) =
        some (State.start_state) :=
    generateParityInitialBlock_returns_to_start k hk
  have hpairsC :
      ProgConsumesPts (by omega) (State.start_state)
        (generateParityPairBlocks k hk pairCount) pairsPts := by
    simpa [pairsPts, pairCount] using
      generateParityPairBlocks_ProgConsumesPts k hk pairCount
  have hpairsRun :
      run? (generateParityPairBlocks k hk pairCount) (State.start_state) =
        some (State.start_state) :=
    generateParityPairBlocks_returns_to_start k hk pairCount
  have hprefixC :
      ProgConsumesPts (by omega) (State.start_state)
        (generateParityInitialBlock k hk ++ generateParityPairBlocks k hk pairCount)
        (initPts ++ pairsPts) := by
    simpa using
      progConsumesPts_append (by omega)
        (p := generateParityInitialBlock k hk)
        (q := generateParityPairBlocks k hk pairCount)
        (σ := State.start_state) (σret := State.start_state)
        (a := initPts) (b := pairsPts)
        hinitC hinitRun hpairsC
  have hprefixRun :
      run? (generateParityInitialBlock k hk ++ generateParityPairBlocks k hk pairCount)
          (State.start_state) =
        some (State.start_state) := by
    simp [run?_append, hinitRun, hpairsRun]
  by_cases hodd : rem % 2 = 1
  · have hsingleC :
        ProgConsumesPts (by omega) (State.start_state)
          (generateParitySingletonBlock k hk singletonPt) [singletonPt] := by
      simpa [singletonPt] using
        generateParitySingletonBlock_ProgConsumesPts k hk singletonPt
    have hcombined :
        ProgConsumesPts (by omega) (State.start_state)
          ((generateParityInitialBlock k hk ++ generateParityPairBlocks k hk pairCount) ++
            generateParitySingletonBlock k hk singletonPt)
          ((initPts ++ pairsPts) ++ [singletonPt]) := by
      simpa using
        progConsumesPts_append (by omega)
          (p := generateParityInitialBlock k hk ++ generateParityPairBlocks k hk pairCount)
          (q := generateParitySingletonBlock k hk singletonPt)
          (σ := State.start_state) (σret := State.start_state)
          (a := initPts ++ pairsPts) (b := [singletonPt])
          hprefixC hprefixRun hsingleC
    have hpts :
        generatedPoints mode k = (initPts ++ pairsPts) ++ [singletonPt] := by
      rw [generatedPoints_split mode k hk]
      simp [initPts, pairsPts, singletonPt, rem, pairCount, hodd]
    rw [hpts]
    simpa [generateParityForMode, rem, pairCount, singletonPt, hodd] using hcombined
  · have hpts :
        generatedPoints mode k = initPts ++ pairsPts := by
      rw [generatedPoints_split mode k hk]
      simp [initPts, pairsPts, rem, pairCount, hodd]
    rw [hpts]
    simpa [generateParityForMode, rem, pairCount, hodd] using hprefixC

/- Precomputed table lemmas for point consumption -/

lemma precomputed_k2_product_consumes :
    ProgConsumesPts (by decide) State.start_state
      PrecomputedTables.K2Product.program PrecomputedTables.K2Product.orderedPoints := by
  simp [ProgConsumesPts, PrecomputedTables.K2Product.program,
    PrecomputedTables.K2Product.orderedPoints, PrecomputedTables.K2Product.targetPoints,
    matchesAt_pointRow_state, regEqExpected, expectedRow,
    State.start_state, applyOp?, State.addScaledReg, State.setReg, Register.addScaled]

lemma precomputed_k3_product_consumes :
    ProgConsumesPts (by decide) State.start_state
      PrecomputedTables.K3Product.program PrecomputedTables.K3Product.orderedPoints := by
  simp [ProgConsumesPts, PrecomputedTables.K3Product.program,
    PrecomputedTables.K3Product.orderedPoints,
    matchesAt_pointRow_state, regEqExpected, expectedRow,
    State.start_state, applyOp?, State.addScaledReg, State.setReg, Register.addScaled]
  native_decide

lemma precomputed_k2_triple_consumes :
    ProgConsumesPts (by decide) State.start_state
      PrecomputedTables.K2TripleProduct.program PrecomputedTables.K2TripleProduct.orderedPoints := by
  simp [ProgConsumesPts, PrecomputedTables.K2TripleProduct.program,
    PrecomputedTables.K2TripleProduct.orderedPoints,
    PrecomputedTables.K2TripleProduct.targetPoints,
    matchesAt_pointRow_state, regEqExpected, expectedRow,
    State.start_state, applyOp?, State.addScaledReg, State.setReg, Register.addScaled,
    State.shiftLReg, Register.shiftL, State.shiftRReg?, Register.shiftR?,
    State.negateReg, Register.negate]

lemma precomputed_k3_triple_consumes :
    ProgConsumesPts (by decide) State.start_state
      PrecomputedTables.K3TripleProduct.program PrecomputedTables.K3TripleProduct.orderedPoints := by
  simp [ProgConsumesPts, PrecomputedTables.K3TripleProduct.program,
    PrecomputedTables.K3TripleProduct.orderedPoints,
    matchesAt_pointRow_state, regEqExpected, expectedRow,
    State.start_state, applyOp?, State.addScaledReg, State.setReg, Register.addScaled]
  native_decide

/- Precomputed table lemmas for safe operations (src ≠ dst) -/

lemma precomputed_k2_product_safe :
    SafeProg PrecomputedTables.K2Product.program := by
  apply SafeProg_of_WellFormed
  intro op hop
  simp [PrecomputedTables.K2Product.program, Prog.OpOK] at hop ⊢
  aesop

lemma precomputed_k3_product_safe :
    SafeProg PrecomputedTables.K3Product.program := by
  apply SafeProg_of_WellFormed
  intro op hop
  simp [PrecomputedTables.K3Product.program, Prog.OpOK] at hop ⊢
  aesop

lemma precomputed_k2_triple_safe :
    SafeProg PrecomputedTables.K2TripleProduct.program := by
  apply SafeProg_of_WellFormed
  intro op hop
  simp [PrecomputedTables.K2TripleProduct.program, Prog.OpOK] at hop ⊢
  aesop

lemma precomputed_k3_triple_safe :
    SafeProg PrecomputedTables.K3TripleProduct.program := by
  apply SafeProg_of_WellFormed
  intro op hop
  simp [PrecomputedTables.K3TripleProduct.program, Prog.OpOK] at hop ⊢
  aesop

/- Precomputed table lemmas for for safe operations and point consumption -/

lemma precomputed_k2_product_ProgConsumesPtsSafe :
    ProgConsumesPtsSafe (k := 2) (by decide) State.start_state
      PrecomputedTables.K2Product.program PrecomputedTables.K2Product.orderedPoints where
  consumes := precomputed_k2_product_consumes
  safe_add := precomputed_k2_product_safe

lemma precomputed_k3_product_ProgConsumesPtsSafe :
    ProgConsumesPtsSafe (k := 3) (by decide) State.start_state
      PrecomputedTables.K3Product.program PrecomputedTables.K3Product.orderedPoints where
  consumes := precomputed_k3_product_consumes
  safe_add := precomputed_k3_product_safe

lemma precomputed_k2_triple_ProgConsumesPtsSafe :
    ProgConsumesPtsSafe (k := 2) (by decide) State.start_state
      PrecomputedTables.K2TripleProduct.program PrecomputedTables.K2TripleProduct.orderedPoints where
  consumes := precomputed_k2_triple_consumes
  safe_add := precomputed_k2_triple_safe

lemma precomputed_k3_triple_ProgConsumesPtsSafe :
    ProgConsumesPtsSafe (k := 3) (by decide) State.start_state
      PrecomputedTables.K3TripleProduct.program PrecomputedTables.K3TripleProduct.orderedPoints where
  consumes := precomputed_k3_triple_consumes
  safe_add := precomputed_k3_triple_safe

/- Generalized (k≥4) lemmas for for safe operations and point consumption -/

lemma generateParityProduct_ProgConsumesPtsSafe (k : ℕ) (hk : k ≥ 4) :
    ProgConsumesPtsSafe (by omega) State.start_state
      (generateParityProduct k hk) (generatedPoints .PhaseProduct k) where
  consumes := by
    simpa [generateParityProduct] using
      generateParityForMode_ProgConsumesPts .PhaseProduct k hk
  safe_add := by
    apply SafeProg_of_WellFormed
    simpa [generateParityProduct] using
      generateParityForMode_WellFormed .PhaseProduct k hk

lemma generateParityTripleProduct_ProgConsumesPtsSafe (k : ℕ) (hk : k ≥ 4) :
    ProgConsumesPtsSafe (by omega) State.start_state
      (generateParityTripleProduct k hk) (generatedPoints .PhaseTripleProduct k) where
  consumes := by
    simpa [generateParityTripleProduct] using
      generateParityForMode_ProgConsumesPts .PhaseTripleProduct k hk
  safe_add := by
    apply SafeProg_of_WellFormed
    simpa [generateParityTripleProduct] using
      generateParityForMode_WellFormed .PhaseTripleProduct k hk

/- The generated point list is the protected canonical point list. -/
theorem generatedPoints_valid (mode : ProductMode) (k : ℕ) (_ : k ≥ 2) :
    ValidPointList mode k (generatedPoints mode k) := by
  unfold ValidPointList generatedPoints canonicalPoints
  apply List.map_congr_left
  intro n _hn
  exact streamPoint_eq_canonicalPoint n

lemma generatePointsInOrder_valid (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) :
    ValidPointOrder mode k (generatePointsInOrder mode k hk) := by
  cases mode with
  | PhaseProduct =>
      by_cases h2 : k = 2
      · subst k
        simp [ValidPointOrder, generatePointsInOrder, generatedPoints,
          canonicalPoints, streamPoint]
        decide
      · by_cases h3 : k = 3
        · subst k
          simp [ValidPointOrder, generatePointsInOrder, generatedPoints,
            canonicalPoints, streamPoint]
          decide
        ·
          simp [ValidPointOrder, generatePointsInOrder, generatedPoints,
            canonicalPoints, h2, h3]
          rw [show
            List.map streamPoint (List.range (ProductMode.PhaseProduct.pointCount k)) =
              List.map canonicalPoint (List.range (ProductMode.PhaseProduct.pointCount k)) by
              apply List.map_congr_left
              intro n _hn
              exact streamPoint_eq_canonicalPoint n]
  | PhaseTripleProduct =>
      by_cases h2 : k = 2
      · subst k
        simp [ValidPointOrder, generatePointsInOrder, generatedPoints,
          canonicalPoints, streamPoint]
        decide
      · by_cases h3 : k = 3
        · subst k
          simp [ValidPointOrder, generatePointsInOrder, generatedPoints,
            canonicalPoints, streamPoint]
          decide
        ·
          simp [ValidPointOrder, generatePointsInOrder, generatedPoints,
            canonicalPoints, h2, h3]
          rw [show
            List.map streamPoint (List.range (ProductMode.PhaseTripleProduct.pointCount k)) =
              List.map canonicalPoint (List.range (ProductMode.PhaseTripleProduct.pointCount k)) by
              apply List.map_congr_left
              intro n _hn
              exact streamPoint_eq_canonicalPoint n]

/- The generated program safely consumes a permutation of the canonical points. -/
theorem generate_ProgConsumesPtsSafe (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) :
    ValidPointOrder mode k (generatePointsInOrder mode k hk) ∧
      ProgConsumesPtsSafe (by omega) State.start_state
        (generate mode k hk) (generatePointsInOrder mode k hk) := by
  constructor
  · exact generatePointsInOrder_valid mode k hk
  cases mode with
  | PhaseProduct =>
      by_cases h2 : k = 2
      · subst k
        simp [generate, generatePointsInOrder]
        exact precomputed_k2_product_ProgConsumesPtsSafe
      · by_cases h3 : k = 3
        · subst k
          simp [generate, generatePointsInOrder]
          exact precomputed_k3_product_ProgConsumesPtsSafe
        ·
          have h4 : k ≥ 4 := by omega
          simp [generate, generatePointsInOrder, h2, h3]
          exact generateParityProduct_ProgConsumesPtsSafe k h4
  | PhaseTripleProduct =>
      by_cases h2 : k = 2
      · subst k
        simp [generate, generatePointsInOrder]
        exact precomputed_k2_triple_ProgConsumesPtsSafe
      · by_cases h3 : k = 3
        · subst k
          simp [generate, generatePointsInOrder]
          exact precomputed_k3_triple_ProgConsumesPtsSafe
        ·
          have h4 : k ≥ 4 := by omega
          simp [generate, generatePointsInOrder, h2, h3]
          exact generateParityTripleProduct_ProgConsumesPtsSafe k h4

/-
  Prove that the number of parallel product layers is generated as expected
  k-1 for PhaseProduct, (3k-3)/2 for PhaseTripleProduct
-/
theorem generate_parallelProductLayerCount_eq
  (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) :
  (generateLayerSizes mode k hk).length =
    match mode with
    | .PhaseProduct =>
        if k = 2 then 2 else if k = 3 then 2 else k - 1
    | .PhaseTripleProduct =>
        if k = 2 then 2 else if k = 3 then 3 else (3*k - 3) / 2 := by {
  cases mode <;> simp [generateLayerSizes, PrecomputedTables.K2Product.layerSizes, PrecomputedTables.K3Product.layerSizes, PrecomputedTables.K2TripleProduct.layerSizes, PrecomputedTables.K3TripleProduct.layerSizes]
  {
    split_ifs with hc1 hc2
    { subst hc1 ; simp }
    { subst hc2 ; simp }
    {
      have hq : (2*k - 1 - 4) % 2 = 1 := by omega
      simp [generateParityLayerSizesForMode, ProductMode.pointCount, hq]
      omega
    }
  }
  {
    split_ifs with hc1 hc2
    { subst hc1 ; simp }
    { subst hc2 ; simp }
    {
      simp [generateParityLayerSizesForMode, ProductMode.pointCount]
      split_ifs with hq <;> (simp;omega)
    }
  }
}

end Table_Generation
