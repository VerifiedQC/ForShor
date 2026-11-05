import Provider.Compression.EncodingBounds
import Provider.Profiles.Intervals
import Provider.Compression.Result
import Provider.Ceiling.FinalCeiling

/-! # Bounded Source Enumeration
Defines the finite search over bounded source words: `sourceAlphabet`, `wordsOfLength`, `wordsUpTo`, `searchEntries` and the checks `sourceCheck` and `firstChecked`. Proves soundness and membership statements such as `sourceCheck_iff`, `firstChecked_sound` and `search_sound`. This is an exhaustive finite search with no polynomial claim.
-/

namespace Paper.BoundedThreshold

open TableGeneration TableGeneration.Operations Paper.CompressionEncoding
open Paper.FullDSL Paper.SourceBridge

def sourceAlphabet (k a : Nat) : List (valid_ops k) :=
  (List.finRange k).flatMap fun i =>
    (List.range (a+1)).map (valid_ops.shiftL i) ++
    (List.range (a+1)).map (valid_ops.shiftR i) ++
    [valid_ops.negate i, valid_ops.phaseProduct i] ++
    (List.finRange k).flatMap (fun j =>
      (List.range (a+1)).flatMap (fun n =>
        [valid_ops.addScaled i j false n,
          valid_ops.addScaled i j true n]))

theorem mem_sourceAlphabet_of_exponentWithin {k a : Nat}
    {op : valid_ops k}
    (h : exponentWithin (widthOp (toFull op)) a) :
    op ∈ sourceAlphabet k a := by
  cases op with
  | shiftL i n =>
    simp only [toFull, widthOp, exponentWithin] at h
    simp [sourceAlphabet, h]
  | shiftR i n =>
    simp only [toFull, widthOp, exponentWithin] at h
    simp [sourceAlphabet, h]
  | negate i => simp [sourceAlphabet]
  | phaseProduct i => simp [sourceAlphabet]
  | addScaled i j neg n =>
    simp only [toFull, widthOp, exponentWithin] at h
    cases neg <;> simp [sourceAlphabet] <;> omega

def wordsOfLength {α : Type*} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n+1 => alphabet.flatMap fun op =>
      (wordsOfLength alphabet n).map (op :: ·)

theorem mem_wordsOfLength_of_all {α : Type*} (alphabet : List α)
    (word : List α) (hall : ∀ op ∈ word, op ∈ alphabet) :
    word ∈ wordsOfLength alphabet word.length := by
  induction word with
  | nil => simp [wordsOfLength]
  | cons op rest ih =>
    have hop := hall op (by simp)
    have hrest : ∀ x ∈ rest, x ∈ alphabet := by
      intro x hx
      exact hall x (by simp [hx])
    simp only [List.length_cons, wordsOfLength, List.mem_flatMap]
    exact ⟨op, hop, by simp [ih hrest]⟩

def wordsUpTo {α : Type*} (alphabet : List α) (L : Nat) : List (List α) :=
  (List.range (L+1)).flatMap (wordsOfLength alphabet)

theorem mem_wordsUpTo_of_all {α : Type*} (alphabet : List α)
    (L : Nat) (word : List α) (hlen : word.length ≤ L)
    (hall : ∀ op ∈ word, op ∈ alphabet) :
    word ∈ wordsUpTo alphabet L := by
  simp only [wordsUpTo, List.mem_flatMap]
  exact ⟨word.length, by simp [hlen], mem_wordsOfLength_of_all alphabet word hall⟩

end Paper.BoundedThreshold


namespace Paper.BoundedThreshold

open TableGeneration TableGeneration.Operations Paper.F2CatalogTransfer
open Paper.SourceBridge Paper.F4ChargeIntervals

def sourceCheck {k : Nat} (hk : 2 ≤ k) (a b C : Nat)
    (word : Prog k) (pts : List Point) : Bool :=
  decide (pts.Perm (f2Points k)) &&
  progConsumesPts? (positive_of_ge_two hk) State.start_state word pts &&
  safeProg? word &&
  returnsToStartCheck word State.start_state &&
  decide (Paper.PPEndToEnd.chargedCount word ≤ C) &&
  decide ((sourceProfile (finLast (positive_of_ge_two hk)) word).peakA ≤ a) &&
  decide ((sourceProfile (finLast (positive_of_ge_two hk)) word).peakB ≤ b)

theorem sourceCheck_iff {k : Nat} (hk : 2 ≤ k) (a b C : Nat)
    (word : Prog k) (pts : List Point) :
    sourceCheck hk a b C word pts = true ↔
      pts.Perm (f2Points k) ∧
      ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state word pts ∧
      Paper.PPEndToEnd.chargedCount word ≤ C ∧
      (sourceProfile (finLast (positive_of_ge_two hk)) word).peakA ≤ a ∧
      (sourceProfile (finLast (positive_of_ge_two hk)) word).peakB ≤ b := by
  constructor
  · intro h
    simp only [sourceCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨hperm, hcons⟩, hsafe⟩, hret⟩, hcharge⟩, hA⟩, hB⟩
    exact ⟨hperm, progConsumesPtsSafe_of_checks hcons hsafe hret,
      hcharge, hA, hB⟩
  · rintro ⟨hperm, hsafe, hcharge, hA, hB⟩
    simp only [sourceCheck, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨hperm, hsafe.consumes⟩, hsafe.safe_add⟩,
      hsafe.returns_start⟩, hcharge⟩, hA⟩, hB⟩

theorem ofFn_get_cast {α : Type*} (l : List α) {n : Nat}
    (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.get (Fin.cast h.symm i)) = l := by
  subst n
  exact List.ofFn_get l

def checkedSource {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b C : Nat) (word : Prog k) (pts : List Point)
    (hcheck : sourceCheck hk a b C word pts = true) : F2Source K :=
  let hperm := ((sourceCheck_iff hk a b C word pts).mp hcheck).1
  let hsafe := ((sourceCheck_iff hk a b C word pts).mp hcheck).2.1
  let hlen : pts.length = 2*(k-1)+1 := by
    have hh := hperm.length_eq
    simp [f2Points] at hh
    omega
  {
    source := { policyId := "bounded search", k := k, hk := hk, program := word }
    cap := hK
    points := fun i => pts.get (Fin.cast hlen.symm i)
    safe := by simpa only [ofFn_get_cast pts hlen] using hsafe
    literalF2 := by simpa only [ofFn_get_cast pts hlen] using hperm
  }

theorem checkedSource_spec {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b C : Nat) (word : Prog k) (pts : List Point)
    (hcheck : sourceCheck hk a b C word pts = true) :
    let t := checkedSource hk hK a b C word pts hcheck
    t.arity = k ∧ t.charge ≤ C ∧
      (rawProfile t).peakA ≤ a ∧
      (rawProfile t).peakB ≤ b := by
  obtain ⟨_, _, hc, hA, hB⟩ := (sourceCheck_iff hk a b C word pts).mp hcheck
  exact ⟨rfl, hc, hA, hB⟩

end Paper.BoundedThreshold


namespace Paper.BoundedThreshold

open TableGeneration TableGeneration.Operations Paper.F2CatalogTransfer
open Paper.F4ChargeIntervals

def searchEntries (k a L : Nat) : List (Prog k × List Point) :=
  (wordsUpTo (sourceAlphabet k a) L).flatMap fun word =>
    (f2Points k).permutations.map (fun pts => (word, pts))

theorem mem_searchEntries {k a L : Nat} (word : Prog k) (pts : List Point)
    (hlen : word.length ≤ L)
    (hexp : ∀ op ∈ word,
      Paper.CompressionEncoding.exponentWithin
        (Paper.FullDSL.widthOp (Paper.SourceBridge.toFull op)) a)
    (hperm : pts.Perm (f2Points k)) :
    (word, pts) ∈ searchEntries k a L := by
  have hword : word ∈ wordsUpTo (sourceAlphabet k a) L :=
    mem_wordsUpTo_of_all _ _ _ hlen
      (fun op hop => mem_sourceAlphabet_of_exponentWithin (hexp op hop))
  simp only [searchEntries, List.mem_flatMap]
  refine ⟨word, hword, ?_⟩
  exact List.mem_map.mpr ⟨pts, List.mem_permutations.mpr hperm, rfl⟩

def firstChecked {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b C : Nat) : List (Prog k × List Point) → Option (F2Source K)
  | [] => none
  | (word, pts) :: rest =>
      if h : sourceCheck hk a b C word pts = true then
        some (checkedSource hk hK a b C word pts h)
      else firstChecked hk hK a b C rest

theorem firstChecked_sound {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b C : Nat) (entries : List (Prog k × List Point))
    (t : F2Source K) (h : firstChecked hk hK a b C entries = some t) :
    t.arity = k ∧ t.charge ≤ C ∧
      (rawProfile t).peakA ≤ a ∧ (rawProfile t).peakB ≤ b := by
  induction entries with
  | nil => simp [firstChecked] at h
  | cons pair rest ih =>
    rcases pair with ⟨word, pts⟩
    by_cases hc : sourceCheck hk a b C word pts = true
    · simp only [firstChecked, dif_pos hc, Option.some.injEq] at h
      subst t
      exact checkedSource_spec hk hK a b C word pts hc
    · have htail : firstChecked hk hK a b C rest = some t := by
        simpa only [firstChecked, dif_neg hc] using h
      exact ih htail

theorem firstChecked_exists_of_mem {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b C : Nat) (entries : List (Prog k × List Point))
    (word : Prog k) (pts : List Point)
    (hmem : (word, pts) ∈ entries)
    (hcheck : sourceCheck hk a b C word pts = true) :
    ∃ t, firstChecked hk hK a b C entries = some t := by
  induction entries with
  | nil => simp at hmem
  | cons pair rest ih =>
    rcases pair with ⟨w, p⟩
    by_cases hc : sourceCheck hk a b C w p = true
    · exact ⟨checkedSource hk hK a b C w p hc, by simp [firstChecked, hc]⟩
    · have hrest : (word, pts) ∈ rest := by
        simp only [List.mem_cons] at hmem
        rcases hmem with heq | hrest
        · cases heq
          exact False.elim (hc hcheck)
        · exact hrest
      obtain ⟨t, ht⟩ := ih hrest
      exact ⟨t, by simpa only [firstChecked, dif_neg hc] using ht⟩

def search {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b C L : Nat) : Option (F2Source K) :=
  firstChecked hk hK a b C (searchEntries k a L)

theorem search_sound {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b C L : Nat) (t : F2Source K)
    (h : search hk hK a b C L = some t) :
    t.arity = k ∧ t.charge ≤ C ∧
      (rawProfile t).peakA ≤ a ∧ (rawProfile t).peakB ≤ b :=
  firstChecked_sound hk hK a b C (searchEntries k a L) t h

theorem search_complete_bounded {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b C L : Nat) (word : Prog k) (pts : List Point)
    (hlen : word.length ≤ L)
    (hexp : ∀ op ∈ word,
      Paper.CompressionEncoding.exponentWithin
        (Paper.FullDSL.widthOp (Paper.SourceBridge.toFull op)) a)
    (hcheck : sourceCheck hk a b C word pts = true) :
    ∃ t, search hk hK a b C L = some t := by
  have hperm := ((sourceCheck_iff hk a b C word pts).mp hcheck).1
  exact firstChecked_exists_of_mem hk hK a b C _ word pts
    (mem_searchEntries word pts hlen hexp hperm) hcheck

end Paper.BoundedThreshold


namespace Paper.BoundedThreshold

open TableGeneration Paper.F2CatalogTransfer Paper.F4ChargeIntervals
open Paper.CompressionComplete Paper.CompressionF2 Paper.CompressionEncoding
open Paper.ScannerPotential Paper.SourceBridge Paper.PrefixPaddingStage

def lengthCap (k C : Nat) : Nat :=
  (k+1)*(C+(2*k-1))+k+4

theorem paid_le_charge_op {k : Nat} (op : TableGeneration.Operations.valid_ops k) :
    paidOps (toFull op) ≤ Paper.PPEndToEnd.chargedOp op := by
  cases op <;> simp [paidOps, toFull, Paper.PPEndToEnd.chargedOp]
  split <;> omega

theorem paid_le_source_charge {k : Nat} (word : Prog k) :
    totalPaid (mapToFull word) ≤ Paper.PPEndToEnd.chargedCount word := by
  induction word with
  | nil => simp [totalPaid, Paper.PPEndToEnd.chargedCount, mapToFull]
  | cons op rest ih =>
    have hop := paid_le_charge_op op
    simp only [totalPaid, Paper.PPEndToEnd.chargedCount, mapToFull,
      List.map_cons, List.sum_cons] at *
    omega

theorem compressed_length_le_cap {K : Nat} (t : F2Source K) (C : Nat)
    (hC : t.charge ≤ C) :
    (complete t).source.program.length ≤ lengthCap t.arity C := by
  have hlen := paddedCompressedF2_lengthF2 t (originalA t) (originalB t)
  have hpaid := paid_le_source_charge t.source.program
  have hpaidC : totalPaid (mapToFull t.source.program) ≤ C :=
    hpaid.trans hC
  change (complete t).source.program.length =
    (t.source.k+1)*(totalPaid (mapToFull t.source.program)+(2*t.source.k-1))+
      t.source.k+4 at hlen
  simp only [F2Source.arity, lengthCap]
  nlinarith [Nat.mul_le_mul_left (t.source.k+1)
    (Nat.add_le_add_right hpaidC (2*t.source.k-1))]

theorem search_complete_of_source {K : Nat} (t : F2Source K)
    (a b C : Nat) (hC : t.charge ≤ C)
    (hA : (rawProfile t).peakA ≤ a)
    (hB : (rawProfile t).peakB ≤ b) :
    ∃ u, search t.source.hk t.cap a b C (lengthCap t.arity C) = some u := by
  let v := complete t
  have hlen : v.source.program.length ≤ lengthCap t.arity C :=
    compressed_length_le_cap t C hC
  have hAorig : originalA t ≤ a := by
    simpa [originalA, sourceProfileRaw, rawProfile] using hA
  have hexp : ∀ op ∈ v.source.program,
      exponentWithin (Paper.FullDSL.widthOp (toFull op)) a := by
    intro op hop
    exact exponentWithin_mono _ hAorig (complete_exponents t op hop)
  have hcheck : sourceCheck t.source.hk a b C v.source.program
      (List.ofFn v.points) = true := by
    apply (sourceCheck_iff t.source.hk a b C v.source.program
      (List.ofFn v.points)).2
    have hprof := complete_exact_profile t
    refine ⟨v.literalF2, v.safe, ?_, ?_, ?_⟩
    · have hc : v.charge ≤ C := by
        simpa [v, complete_charge] using hC
      simpa [F2Source.charge] using hc
    · have heq : rawProfile v = rawProfile t := by
        simpa [rawProfile, sourceProfileRaw, v] using hprof
      have ha : (rawProfile v).peakA ≤ a := by rw [heq]; exact hA
      simpa [rawProfile] using ha
    · have heq : rawProfile v = rawProfile t := by
        simpa [rawProfile, sourceProfileRaw, v] using hprof
      have hb : (rawProfile v).peakB ≤ b := by rw [heq]; exact hB
      simpa [rawProfile] using hb
  exact search_complete_bounded t.source.hk t.cap a b C _ v.source.program
    (List.ofFn v.points) hlen hexp hcheck

theorem search_decides_feasible {K k d a C : Nat}
    (hk : 2 ≤ k) (hK : k ≤ K) (hda : d ≤ a) :
    feasible (K := K) k d a C ↔
      ∃ t, search hk hK a (a-d) C (lengthCap k C) = some t := by
  constructor
  · rintro ⟨_, t, htarity, hA, hB, hC⟩
    have h := search_complete_of_source t a (a-d) C hC hA hB
    rcases h with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    unfold F2Source.arity at htarity
    subst k
    exact hu
  · rintro ⟨t, ht⟩
    obtain ⟨htarity, hcharge, hA, hB⟩ :=
      search_sound hk hK a (a-d) C (lengthCap k C) t ht
    exact ⟨hda, t, htarity, hA, hB, hcharge⟩

theorem search_decides_any_feasibility {K k d a : Nat}
    (hk : 2 ≤ k) (hK : k ≤ K) (hda : d ≤ a) :
    (∃ C, feasible (K := K) k d a C) ↔
      ∃ t, search hk hK a (a-d) (27*k^3)
        (lengthCap k (27*k^3)) = some t := by
  constructor
  · rintro ⟨C, hfeasible⟩
    exact (search_decides_feasible hk hK hda).mp
      (Paper.F3ChargeCeiling.feasible_has_ceiling_grouped hk hfeasible)
  · rintro ⟨t, ht⟩
    exact ⟨27*k^3, (search_decides_feasible hk hK hda).mpr ⟨t, ht⟩⟩

end Paper.BoundedThreshold


namespace Paper.BoundedThreshold

open Paper.F2CatalogTransfer Paper.F4ChargeIntervals

def budgetSearch {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b C : Nat) : Option (F2Source K) :=
  search hk hK a b C (lengthCap k C)

def firstBudget {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b : Nat) : Nat → Option (Nat × F2Source K)
  | 0 => (budgetSearch hk hK a b 0).map (fun t => (0,t))
  | C+1 =>
      match firstBudget hk hK a b C with
      | some answer => some answer
      | none => (budgetSearch hk hK a b (C+1)).map (fun t => (C+1,t))

theorem firstBudget_none_all {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b M : Nat) (h : firstBudget hk hK a b M = none) :
    ∀ C ≤ M, budgetSearch hk hK a b C = none := by
  induction M with
  | zero =>
    intro C hC
    have : C = 0 := by omega
    subst C
    cases hs : budgetSearch hk hK a b 0 with
    | none => rfl
    | some t => simp [firstBudget, hs] at h
  | succ M ih =>
    have hp : firstBudget hk hK a b M = none := by
      cases hp : firstBudget hk hK a b M with
      | none => rfl
      | some answer => simp [firstBudget, hp] at h
    have hs : budgetSearch hk hK a b (M+1) = none := by
      cases hs : budgetSearch hk hK a b (M+1) with
      | none => rfl
      | some t => simp [firstBudget, hp, hs] at h
    intro C hC
    by_cases hsmall : C ≤ M
    · exact ih hp C hsmall
    · have heq : C = M+1 := by omega
      simpa [heq] using hs

theorem firstBudget_sound {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b M C : Nat) (t : F2Source K)
    (h : firstBudget hk hK a b M = some (C,t)) :
    C ≤ M ∧ budgetSearch hk hK a b C = some t := by
  induction M with
  | zero =>
    cases hs : budgetSearch hk hK a b 0 with
    | none => simp [firstBudget, hs] at h
    | some u =>
      simp [firstBudget, hs] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨by omega, hs⟩
  | succ M ih =>
    cases hp : firstBudget hk hK a b M with
    | some answer =>
      have hh : answer = (C,t) := by simpa [firstBudget, hp] using h
      subst answer
      obtain ⟨hcm, hs⟩ := ih hp
      exact ⟨by omega, hs⟩
    | none =>
      cases hs : budgetSearch hk hK a b (M+1) with
      | none => simp [firstBudget, hp, hs] at h
      | some u =>
        simp [firstBudget, hp, hs] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨by omega, hs⟩

theorem firstBudget_least {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b M C : Nat) (t : F2Source K)
    (h : firstBudget hk hK a b M = some (C,t)) :
    ∀ D < C, budgetSearch hk hK a b D = none := by
  induction M with
  | zero =>
    have hc := (firstBudget_sound hk hK a b 0 C t h).1
    intro D hD
    omega
  | succ M ih =>
    cases hp : firstBudget hk hK a b M with
    | some answer =>
      have hh : answer = (C,t) := by simpa [firstBudget, hp] using h
      subst answer
      exact ih hp
    | none =>
      cases hs : budgetSearch hk hK a b (M+1) with
      | none => simp [firstBudget, hp, hs] at h
      | some u =>
        simp [firstBudget, hp, hs] at h
        rcases h with ⟨rfl, rfl⟩
        intro D hD
        exact firstBudget_none_all hk hK a b M hp D (by omega)

theorem firstBudget_complete {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K)
    (a b M C : Nat) (t : F2Source K)
    (hC : C ≤ M) (hs : budgetSearch hk hK a b C = some t) :
    ∃ D u, firstBudget hk hK a b M = some (D,u) := by
  cases hf : firstBudget hk hK a b M with
  | none =>
    have hn := firstBudget_none_all hk hK a b M hf C hC
    simp [hs] at hn
  | some pair =>
    exact ⟨pair.1, pair.2, by simpa using hf⟩

theorem firstBudget_attains_raw_minimum {K k d a : Nat}
    (hk : 2 ≤ k) (hK : k ≤ K) (hda : d ≤ a)
    (M C : Nat) (t : F2Source K)
    (h : firstBudget hk hK a (a-d) M = some (C,t)) :
    t.arity = k ∧ t.charge = C ∧
      (rawProfile t).peakA ≤ a ∧ (rawProfile t).peakB ≤ a-d ∧
      ∀ s : F2Source K, s.arity = k →
        (rawProfile s).peakA ≤ a → (rawProfile s).peakB ≤ a-d →
        C ≤ s.charge := by
  have hbudget := (firstBudget_sound hk hK a (a-d) M C t h).2
  obtain ⟨htarity, htcharge, htA, htB⟩ :=
    search_sound hk hK a (a-d) C (lengthCap k C) t hbudget
  have hleast := firstBudget_least hk hK a (a-d) M C t h
  have hceq : t.charge = C := by
    by_contra hneq
    have hlt : t.charge < C := by omega
    have hfeas : feasible (K := K) k d a t.charge :=
      ⟨hda, t, htarity, htA, htB, le_rfl⟩
    obtain ⟨u, hu⟩ := (search_decides_feasible hk hK hda).mp hfeas
    have hn := hleast t.charge hlt
    simp only [budgetSearch, hu] at hn
    contradiction
  refine ⟨htarity, hceq, htA, htB, ?_⟩
  intro s hsarity hsA hsB
  by_contra hnot
  have hlt : s.charge < C := by omega
  have hfeas : feasible (K := K) k d a s.charge :=
    ⟨hda, s, hsarity, hsA, hsB, le_rfl⟩
  obtain ⟨u, hu⟩ := (search_decides_feasible hk hK hda).mp hfeas
  have hn := hleast s.charge hlt
  simp only [budgetSearch, hu] at hn
  contradiction

theorem firstBudget_exists_of_feasible {K k d a C : Nat}
    (hk : 2 ≤ k) (hK : k ≤ K) (hda : d ≤ a)
    (hfeasible : feasible (K := K) k d a C) :
    ∃ D t, firstBudget hk hK a (a-d) (27*k^3) = some (D,t) ∧
      t.arity = k ∧ t.charge = D ∧
      (rawProfile t).peakA ≤ a ∧ (rawProfile t).peakB ≤ a-d ∧
      ∀ s : F2Source K, s.arity = k →
        (rawProfile s).peakA ≤ a → (rawProfile s).peakB ≤ a-d →
        D ≤ s.charge := by
  obtain ⟨u, hu⟩ := (search_decides_any_feasibility hk hK hda).mp
    ⟨C, hfeasible⟩
  obtain ⟨D, t, ht⟩ := firstBudget_complete hk hK a (a-d)
    (27*k^3) (27*k^3) u le_rfl hu
  exact ⟨D, t, ht, firstBudget_attains_raw_minimum hk hK hda _ _ t ht⟩

end Paper.BoundedThreshold
