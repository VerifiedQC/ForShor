import Points.SatYes

/-!
# SAT → DHC₂ on complexitylib's CNF formulas

For a nonempty CNF `φ`, the token stream `CNF.tokens φ` (whose bits are `φ.encode`) gives the
digraph `(ofList φ.tokens).dig`, and

`sat_iff_dhc : φ.Satisfiable ↔ DHC (ofList φ.tokens).dig`.

The token-level statements (`TS.sat_of_dhc`, `TS.dhc_of_sat`) speak of clause ends `b` and literal
starts `s`; here they are matched with the clauses and literals of `φ` by splitting token lists
(`ClauseOK` over clauses, `LitOK` over literals).
-/

namespace Pts

open Complexity SAT

namespace TS

/-- The token stream of a list of tokens. -/
def ofList (L : List EncToken) : TS := ⟨L.length, fun t => L[t]?⟩

/-- Every clause has a true literal (token level). -/
def ClauseOK (G : TS) (α : ℕ → Bool) : Prop :=
  ∀ b, G.cs b → ∃ s x, s ≤ b ∧ G.same s b ∧ G.lit x s ∧ (G.pos s ↔ α x = true)

/-- Some literal is true (token level). -/
def LitOK (G : TS) (α : ℕ → Bool) : Prop := ∃ s x, G.lit x s ∧ (G.pos s ↔ α x = true)

/-- The list is empty or ends with a separator. -/
def EndsSep (P : List EncToken) : Prop :=
  P = [] ∨ P[P.length - 1]? = some .litSep ∨ P[P.length - 1]? = some .clauseSep

section shift

variable {P Q : List EncToken}

@[simp] lemma ofList_tok (L : List EncToken) (t : ℕ) : (ofList L).tok t = L[t]? := rfl
@[simp] lemma ofList_T (L : List EncToken) : (ofList L).T = L.length := rfl

lemma tok_shift (i : ℕ) : (ofList (P ++ Q)).tok (P.length + i) = (ofList Q).tok i := by
  simp [List.getElem?_append_right]

lemma tok_pre {s : ℕ} (h : s < P.length) : (ofList (P ++ Q)).tok s = (ofList P).tok s := by
  simp [List.getElem?_append_left h]

lemma lt_of_tok_ofList {L : List EncToken} {t : ℕ} {e : EncToken} (h : (ofList L).tok t = some e) :
    t < L.length := by
  by_contra hc; simp [List.getElem?_eq_none (by omega : L.length ≤ t)] at h

lemma bnd_shift (hP : EndsSep P) (i : ℕ) :
    (ofList (P ++ Q)).bnd (P.length + i) ↔ (ofList Q).bnd i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [bnd, true_or, iff_true, Nat.add_zero]
    rcases hP with rfl | h | h
    · left; rfl
    · right; unfold isSep
      rw [tok_pre (Q := Q) (lt_of_tok_ofList (L := P) h)]; exact Or.inl h
    · right; unfold isSep
      rw [tok_pre (Q := Q) (lt_of_tok_ofList (L := P) h)]; exact Or.inr h
  · unfold bnd isSep
    rw [show P.length + i - 1 = P.length + (i - 1) by omega, tok_shift]
    constructor
    · rintro (h | h)
      · omega
      · exact Or.inr h
    · rintro (h | h)
      · omega
      · exact Or.inr h

lemma lit_shift (hP : EndsSep P) (x i : ℕ) :
    (ofList (P ++ Q)).lit x (P.length + i) ↔ (ofList Q).lit x i := by
  unfold lit sgn isBit
  rw [bnd_shift hP, tok_shift, show P.length + i + 1 + x = P.length + (i + 1 + x) by omega,
    tok_shift]
  have : ∀ j, (ofList (P ++ Q)).tok (P.length + i + 1 + j) = (ofList Q).tok (i + 1 + j) :=
    fun j => by rw [show P.length + i + 1 + j = P.length + (i + 1 + j) by omega, tok_shift]
  simp only [this]

lemma pos_shift (i : ℕ) : (ofList (P ++ Q)).pos (P.length + i) ↔ (ofList Q).pos i := by
  unfold pos; rw [tok_shift]

lemma cs_shift (i : ℕ) : (ofList (P ++ Q)).cs (P.length + i) ↔ (ofList Q).cs i := by
  unfold cs; rw [tok_shift]

lemma cs_pre {s : ℕ} (h : s < P.length) : (ofList (P ++ Q)).cs s ↔ (ofList P).cs s := by
  unfold cs; rw [tok_pre h]

lemma pos_pre {s : ℕ} (h : s < P.length) : (ofList (P ++ Q)).pos s ↔ (ofList P).pos s := by
  unfold pos; rw [tok_pre h]

lemma bnd_pre {s : ℕ} (h : s < P.length) : (ofList (P ++ Q)).bnd s ↔ (ofList P).bnd s := by
  unfold bnd isSep
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · rw [tok_pre (by omega : s - 1 < P.length)]

/-- Literals starting inside a prefix that ends with a separator stay inside it. -/
lemma lit_pre (hP : EndsSep P) (hne : P ≠ []) {x s : ℕ} (h : s < P.length) :
    (ofList (P ++ Q)).lit x s ↔ (ofList P).lit x s := by
  have hlast : (ofList P).isSep (P.length - 1) := by
    rcases hP with h' | h' | h'
    · exact absurd h' hne
    · exact Or.inl h'
    · exact Or.inr h'
  have hlast' : (ofList (P ++ Q)).isSep (P.length - 1) := by
    unfold isSep; rw [tok_pre (by omega)]; exact hlast
  constructor
  · rintro ⟨⟨hb, hd⟩, hall, hend⟩
    have hin : s + 1 + x < P.length := by
      by_contra hc
      rcases Nat.lt_or_ge s (P.length - 1) with h1 | h1
      · have := hall (P.length - 1 - (s + 1)) (by omega)
        rw [show s + 1 + (P.length - 1 - (s + 1)) = P.length - 1 by omega] at this
        rcases hlast' with h2 | h2 <;> rw [h2] at this <;> cases this
      · have h3 : s = P.length - 1 := by omega
        subst h3
        rcases hb with h2 | h2 <;> rcases hlast' with h4 | h4 <;> rw [h2] at h4 <;> cases h4
    refine ⟨⟨?_, (bnd_pre h).mp hd⟩, fun i hi => ?_, ?_⟩
    · unfold isBit at hb ⊢; rwa [tok_pre h] at hb
    · rw [← tok_pre (by omega)]; exact hall i hi
    · rw [← tok_pre hin]; exact hend
  · rintro ⟨⟨hb, hd⟩, hall, hend⟩
    have hin : s + 1 + x < P.length := lt_of_tok_ofList hend
    refine ⟨⟨?_, (bnd_pre h).mpr hd⟩, fun i hi => ?_, ?_⟩
    · unfold isBit at hb ⊢; rwa [tok_pre h]
    · rw [tok_pre (by omega)]; exact hall i hi
    · rw [tok_pre hin]; exact hend

lemma lit_lt_len {L : List EncToken} {x s : ℕ} (h : (ofList L).lit x s) : s + 1 + x < L.length :=
  lt_of_tok_ofList h.2.2

end shift

section split

variable {α : ℕ → Bool}

lemma same_shift (P : List EncToken) {Q : List EncToken} (i j : ℕ) :
    (ofList (P ++ Q)).same (P.length + i) (P.length + j) ↔ (ofList Q).same i j := by
  unfold same
  constructor
  · intro h t h1 h2 hc
    exact h (P.length + t) (by omega) (by omega) ((cs_shift t).mpr hc)
  · intro h t h1 h2 hc
    exact h (t - P.length) (by omega) (by omega)
      ((cs_shift (P := P) (Q := Q) (t - P.length)).mp (by rwa [Nat.add_sub_cancel' (by omega)]))

lemma same_pre {P Q : List EncToken} {s b : ℕ} (h : b < P.length) :
    (ofList (P ++ Q)).same s b ↔ (ofList P).same s b := by
  unfold same
  exact forall_congr' fun t => imp_congr_right fun _ => imp_congr_right fun ht =>
    not_congr (cs_pre (by omega))

/-- Splitting after a clause end. -/
lemma clauseOK_append {P Q : List EncToken} (hP : P ≠ [])
    (hl : P[P.length - 1]? = some .clauseSep) :
    ClauseOK (ofList (P ++ Q)) α ↔ ClauseOK (ofList P) α ∧ ClauseOK (ofList Q) α := by
  have hE : EndsSep P := Or.inr (Or.inr hl)
  have hPlen : P.length - 1 < P.length := lt_of_tok_ofList (L := P) hl
  have hcsP : (ofList (P ++ Q)).cs (P.length - 1) := by
    unfold cs; rw [tok_pre hPlen]; exact hl
  constructor
  · intro h
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · have hbP : b < P.length := lt_of_tok_ofList hb
      obtain ⟨s, x, h1, h2, h3, h4⟩ := h b ((cs_pre hbP).mpr hb)
      exact ⟨s, x, h1, (same_pre hbP).mp h2, (lit_pre hE hP (by omega)).mp h3,
        by rwa [← pos_pre (by omega)]⟩
    · obtain ⟨s, x, h1, h2, h3, h4⟩ := h (P.length + b) ((cs_shift b).mpr hb)
      have hs : P.length ≤ s := by
        by_contra hc
        exact h2 (P.length - 1) (by omega) (by omega) hcsP
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hs
      exact ⟨i, x, by omega, (same_shift P i b).mp h2, (lit_shift hE x i).mp h3,
        by rwa [← pos_shift]⟩
  · rintro ⟨hA, hB⟩ b hb
    rcases Nat.lt_or_ge b P.length with hbP | hbP
    · obtain ⟨s, x, h1, h2, h3, h4⟩ := hA b ((cs_pre hbP).mp hb)
      exact ⟨s, x, h1, (same_pre hbP).mpr h2, (lit_pre hE hP (by omega)).mpr h3,
        by rwa [pos_pre (by omega)]⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hbP
      obtain ⟨i, x, h1, h2, h3, h4⟩ := hB j ((cs_shift j).mp hb)
      exact ⟨P.length + i, x, by omega, (same_shift P i j).mpr h2, (lit_shift hE x i).mpr h3,
        by rwa [pos_shift]⟩

/-- Splitting after a literal end. -/
lemma litOK_append {P Q : List EncToken} (hP : P ≠ []) (hl : P[P.length - 1]? = some .litSep) :
    LitOK (ofList (P ++ Q)) α ↔ LitOK (ofList P) α ∨ LitOK (ofList Q) α := by
  have hE : EndsSep P := Or.inr (Or.inl hl)
  constructor
  · rintro ⟨s, x, h1, h2⟩
    rcases Nat.lt_or_ge s P.length with hs | hs
    · exact Or.inl ⟨s, x, (lit_pre hE hP hs).mp h1, by rwa [← pos_pre hs]⟩
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hs
      exact Or.inr ⟨i, x, (lit_shift hE x i).mp h1, by rwa [← pos_shift]⟩
  · rintro (⟨s, x, h1, h2⟩ | ⟨i, x, h1, h2⟩)
    · have hs : s < P.length := by have := lit_lt_len h1; omega
      exact ⟨s, x, (lit_pre hE hP hs).mpr h1, by rwa [pos_pre hs]⟩
    · exact ⟨P.length + i, x, (lit_shift hE x i).mpr h1, by rwa [pos_shift]⟩

lemma rawTokens_eq (ℓ : Lit) :
    ℓ.rawTokens = EncToken.bit ℓ.sign :: List.replicate ℓ.var (EncToken.bit true) := by
  simp [Lit.rawTokens, Lit.encodeRaw, Unary.encode, List.map_replicate]

/-- The tokens of one literal. -/
def litTok (ℓ : Lit) (i : ℕ) : Option EncToken :=
  if i = 0 then some (.bit ℓ.sign) else if i ≤ ℓ.var then some (.bit true)
  else if i = ℓ.var + 1 then some .litSep else none

lemma litTok_get (ℓ : Lit) (i : ℕ) :
    (EncToken.bit ℓ.sign :: List.replicate ℓ.var (EncToken.bit true) ++ [EncToken.litSep])[i]? =
      litTok ℓ i := by
  unfold litTok
  rcases i with _ | i
  · simp
  · simp only [List.cons_append, List.getElem?_cons_succ, Nat.add_one_ne_zero, if_false]
    rcases Nat.lt_or_ge i ℓ.var with h | h
    · rw [List.getElem?_append_left (by simpa using h), if_pos (by omega)]
      simp [h]
    · rw [List.getElem?_append_right (by simpa using h), if_neg (by omega)]
      simp only [List.length_replicate]
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · subst h'; simp
      · rw [List.getElem?_eq_none (by simp; omega), if_neg (by omega)]

lemma litTok_bit {ℓ : Lit} {i : ℕ} {b : Bool} (h : litTok ℓ i = some (.bit b)) : i ≤ ℓ.var := by
  unfold litTok at h
  by_contra hc
  rw [if_neg (by omega), if_neg (by omega)] at h
  split_ifs at h <;> cases h

lemma litTok_sep {ℓ : Lit} {i : ℕ} {e : EncToken} (h : litTok ℓ i = some e)
    (he : e = .litSep ∨ e = .clauseSep) : i = ℓ.var + 1 := by
  unfold litTok at h
  by_contra hc
  rw [if_neg hc] at h
  split_ifs at h <;> (cases h; rcases he with he | he <;> cases he)

lemma litTok_one {ℓ : Lit} {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ ℓ.var) :
    litTok ℓ i = some (.bit true) := by
  unfold litTok; rw [if_neg (by omega), if_pos h2]

lemma litTok_end (ℓ : Lit) : litTok ℓ (ℓ.var + 1) = some .litSep := by
  unfold litTok; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- One literal. -/
lemma litOK_lit (ℓ : Lit) :
    LitOK (ofList (ℓ.rawTokens ++ [.litSep])) α ↔ α ℓ.var = ℓ.sign := by
  rw [rawTokens_eq]
  unfold LitOK lit sgn isBit bnd isSep pos
  simp only [ofList_tok, litTok_get]
  constructor
  · rintro ⟨s, x, ⟨⟨hb, hd⟩, hall, hend⟩, hp⟩
    have hs0 : s = 0 := by
      rcases hd with hd | hd
      · exact hd
      · have h1 : s ≤ ℓ.var := by rcases hb with hb | hb <;> exact litTok_bit hb
        have h2 : s - 1 = ℓ.var + 1 := by
          rcases hd with hd | hd
          · exact litTok_sep hd (Or.inl rfl)
          · exact litTok_sep hd (Or.inr rfl)
        omega
    subst hs0
    have hx : x = ℓ.var := by
      rcases lt_trichotomy x ℓ.var with h | h | h
      · rw [show 0 + 1 + x = x + 1 by omega, litTok_one (by omega) (by omega)] at hend; cases hend
      · exact h
      · have := hall ℓ.var h
        rw [show 0 + 1 + ℓ.var = ℓ.var + 1 by omega, litTok_end] at this; cases this
    subst hx
    unfold litTok at hp; simp only [if_true, Option.some.injEq, EncToken.bit.injEq] at hp
    cases h : ℓ.sign <;> cases h' : α ℓ.var <;> simp_all
  · intro h
    refine ⟨0, ℓ.var, ⟨⟨?_, Or.inl rfl⟩, fun i hi => ?_, ?_⟩, ?_⟩
    · unfold litTok; cases ℓ.sign <;> simp
    · exact litTok_one (by omega) (by omega)
    · rw [show 0 + 1 + ℓ.var = ℓ.var + 1 by omega]; exact litTok_end ℓ
    · unfold litTok; simp only [if_true, Option.some.injEq, EncToken.bit.injEq]
      rw [h]

lemma litOK_sep : ¬ LitOK (ofList [.clauseSep]) α := by
  rintro ⟨s, x, ⟨⟨hb, -⟩, -⟩, -⟩
  unfold isBit at hb
  rcases s with _ | s <;> simp at hb

lemma clause_tokens_ne (c : Clause) : ∀ t : ℕ, (c.tokens)[t]? ≠ some EncToken.clauseSep := by
  induction c with
  | nil => simp [Clause.tokens]
  | cons ℓ ℓs ih =>
    intro t h
    simp only [Clause.tokens] at h
    rw [rawTokens_eq] at h
    rcases Nat.lt_or_ge t (ℓ.var + 2) with h1 | h1
    · rw [List.getElem?_append_left (by simp; omega)] at h
      rcases t with _ | t
      · simp at h
      · simp only [List.cons_append, List.getElem?_cons_succ] at h
        rcases Nat.lt_or_ge t ℓ.var with h2 | h2
        · rw [List.getElem?_append_left (by simpa using h2)] at h; simp [h2] at h
        · rw [List.getElem?_append_right (by simpa using h2)] at h
          simp only [List.length_replicate] at h
          rw [show t - ℓ.var = 0 by omega] at h; simp at h
    · rw [List.getElem?_append_right (by simp; omega)] at h
      simp only [List.length_append, List.length_cons, List.length_replicate, List.length_singleton] at h
      exact ih _ h

/-- One clause. -/
lemma clauseOK_clause (c : Clause) :
    ClauseOK (ofList (c.tokens ++ [.clauseSep])) α ↔ ∃ ℓ ∈ c, α ℓ.var = ℓ.sign := by
  have hno := clause_tokens_ne c
  have hcs : ∀ b, (ofList (c.tokens ++ [.clauseSep])).cs b ↔ b = c.tokens.length := by
    intro b
    unfold cs
    rcases Nat.lt_or_ge b c.tokens.length with h | h
    · rw [ofList_tok, List.getElem?_append_left h]; simp [hno b, Nat.ne_of_lt h]
    · rw [ofList_tok, List.getElem?_append_right h]
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · subst h'; simp
      · rw [List.getElem?_eq_none (by simp; omega)]; simp; omega
  have hlit : ClauseOK (ofList (c.tokens ++ [.clauseSep])) α ↔
      LitOK (ofList (c.tokens ++ [.clauseSep])) α := by
    constructor
    · intro h
      obtain ⟨s, x, -, -, h3, h4⟩ := h _ ((hcs _).mpr rfl)
      exact ⟨s, x, h3, h4⟩
    · rintro ⟨s, x, h3, h4⟩ b hb
      rw [hcs] at hb; subst hb
      have := lit_lt_len h3
      simp only [List.length_append, List.length_singleton] at this
      refine ⟨s, x, by omega, fun t _ ht hc => ?_, h3, h4⟩
      rw [hcs] at hc; omega
  rw [hlit]
  clear hlit hcs hno
  induction c with
  | nil => simp only [Clause.tokens, List.nil_append, List.not_mem_nil, false_and, exists_false,
      iff_false]; exact litOK_sep
  | cons ℓ ℓs ih =>
    have e : Clause.tokens (ℓ :: ℓs) ++ [EncToken.clauseSep] =
        (ℓ.rawTokens ++ [.litSep]) ++ (Clause.tokens ℓs ++ [.clauseSep]) := by
      simp [Clause.tokens, List.append_assoc]
    rw [e, litOK_append (by simp) (by simp), litOK_lit]
    constructor
    · rintro (h | h)
      · exact ⟨ℓ, List.mem_cons_self, h⟩
      · obtain ⟨m, hm, h'⟩ := ih.mp h; exact ⟨m, List.mem_cons_of_mem _ hm, h'⟩
    · rintro ⟨m, hm, h'⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Or.inl h'
      · exact Or.inr (ih.mpr ⟨m, hm, h'⟩)

/-- A formula's tokens: every clause has a true literal. -/
lemma clauseOK_cnf (φ : CNF) :
    ClauseOK (ofList φ.tokens) α ↔ ∀ c ∈ φ, ∃ ℓ ∈ c, α ℓ.var = ℓ.sign := by
  induction φ with
  | nil => simp only [CNF.tokens, List.not_mem_nil, false_imp_iff, imp_true_iff, iff_true]
           intro b hb; simp [cs] at hb
  | cons c φ ih =>
    rw [CNF.tokens, List.append_assoc, ← List.append_assoc c.tokens,
      clauseOK_append (by simp) (by simp), clauseOK_clause, ih]
    simp

end split

/-! ### The headline of 3b -/

lemma tokens_ne_nil {φ : CNF} (h : φ ≠ []) : φ.tokens ≠ [] := by
  rcases φ with _ | ⟨c, φ⟩
  · exact absurd rfl h
  · simp [CNF.tokens]

lemma tokens_last {φ : CNF} (h : φ ≠ []) :
    φ.tokens[φ.tokens.length - 1]? = some .clauseSep := by
  induction φ with
  | nil => exact absurd rfl h
  | cons c φ ih =>
    rcases φ with _ | ⟨c', φ'⟩
    · simp [CNF.tokens]
    · have ih' := ih (by simp)
      have hne := tokens_ne_nil (φ := c' :: φ') (by simp)
      rw [CNF.tokens, List.getElem?_append_right (by simp; exact List.length_pos_iff.mpr hne)]
      convert ih' using 2
      simp only [List.length_append, List.length_singleton]
      have := List.length_pos_iff.mpr hne
      omega

lemma wf_tokens {φ : CNF} (h : φ ≠ []) : (ofList φ.tokens).WF := by
  refine ⟨fun t => ?_, List.length_pos_iff.mpr (tokens_ne_nil h), tokens_last h⟩
  simp only [ofList_tok, ofList_T]
  constructor
  · intro ht; simp [List.getElem?_eq_getElem ht]
  · intro hs; by_contra hc; simp [List.getElem?_eq_none (by omega : φ.tokens.length ≤ t)] at hs

/-- **SAT → DHC₂.** A nonempty CNF is satisfiable iff the digraph of its tokens has a directed
Hamiltonian cycle. -/
theorem sat_iff_dhc {φ : CNF} (h : φ ≠ []) : φ.Satisfiable ↔ DHC (ofList φ.tokens).dig := by
  have hw := wf_tokens h
  have hcl : ∀ α : ℕ → Bool, ClauseOK (ofList φ.tokens) α ↔ ∀ c ∈ φ, ∃ ℓ ∈ c, α ℓ.var = ℓ.sign :=
    fun α => clauseOK_cnf φ
  constructor
  · rintro ⟨α, hα⟩
    have hc := (hcl α.get).mpr fun c hc => by
      have := List.all_eq_true.mp hα c hc
      obtain ⟨ℓ, hℓ, he⟩ := List.any_eq_true.mp this
      exact ⟨ℓ, hℓ, by simpa [Lit.eval] using he⟩
    exact dhc_of_sat hw hc
  · intro hd
    obtain ⟨α, hα⟩ := sat_of_dhc hw hd
    have hc := (hcl α).mp hα
    refine ⟨(List.range (φ.maxVar + 1)).map α, List.all_eq_true.mpr fun c hc' => ?_⟩
    obtain ⟨ℓ, hℓ, he⟩ := hc c hc'
    refine List.any_eq_true.mpr ⟨ℓ, hℓ, ?_⟩
    have hv : ℓ.var < φ.maxVar + 1 :=
      Nat.lt_succ_of_le ((Clause.var_le_maxVar hℓ).trans (CNF.clause_maxVar_le_maxVar hc'))
    simp [Lit.eval, Assignment.get, List.getElem?_map, List.getElem?_range hv, he]

end TS

end Pts

namespace Pts

open Complexity SAT

/-- **SAT → the points-as-input table problem** (correctness of the composite map, before
encodings): a nonempty CNF is satisfiable iff the table instance of its token digraph has value
at most `7 (3 n + |arcs|)`. -/
theorem sat_iff_table {φ : CNF} (h : φ ≠ []) :
    φ.Satisfiable ↔ GenTableOpt 2 (tableOf (TS.ofList φ.tokens).dig)
      (7 * (3 * (TS.ofList φ.tokens).dig.n + (TS.ofList φ.tokens).dig.arcs.length)) := by
  have hw := TS.wf_tokens h
  rw [TS.sat_iff_dhc h]
  refine dhc_iff_table (TS.dig_ok hw) TS.dig_out2 ?_
  show 2 ≤ TS.n _
  have := hw.2.1
  unfold TS.n TS.N6; nlinarith

end Pts
