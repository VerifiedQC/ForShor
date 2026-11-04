import Points.SatCnf
import Points.Encode
import Complexitylib.Classes.P.Verdict
import Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner

/-!
# Recognising CNF encodings in polynomial time

`Valid z ↔ ∃ φ, z = φ.encode` (`valid_iff`), where `Valid` is accepted by a finite-state
scanner over the bits (state `C`: between clauses, `L`: after a literal, `I`: inside a literal),
hence `Valid ∈ P` by complexitylib's `scannerTM`. Also `ofBits`, the token stream read off a
bit string, agrees with `ofList` on encodings (`ofBits_encodeTokens`).
-/

namespace Pts

open Complexity SAT

namespace TS

inductive PS | C | L | I | bad
  deriving DecidableEq

instance : Fintype PS := ⟨{.C, .L, .I, .bad}, fun x => by cases x <;> simp⟩

def pStep : PS → EncToken → PS
  | .C, .bit _ => .I
  | .C, .clauseSep => .C
  | .C, .litSep => .bad
  | .L, .bit _ => .I
  | .L, .clauseSep => .C
  | .L, .litSep => .bad
  | .I, .bit true => .I
  | .I, .bit false => .bad
  | .I, .litSep => .L
  | .I, .clauseSep => .bad
  | .bad, _ => .bad

/-- The token of two bits. -/
def tokB : Bool → Bool → EncToken
  | false, false => .bit false
  | true, true => .bit true
  | false, true => .litSep
  | true, false => .clauseSep

lemma tokB_encode (e : EncToken) : tokB (e.encode.getD 0 false) (e.encode.getD 1 false) = e := by
  rcases e with ⟨_ | _⟩ | _ | _ <;> rfl

lemma encode_tokB (b c : Bool) : (tokB b c).encode = [b, c] := by
  cases b <;> cases c <;> rfl

/-- Scanner states: a token state, and the pending first bit of a token (if any). -/
abbrev BS := PS × Option Bool

abbrev BS.ready (s : PS) : BS := (s, none)

def bStep : BS → Bool → BS
  | (s, none), b => (s, some b)
  | (s, some b), c => (pStep s (tokB b c), none)

/-- The CNF encodings. -/
def Valid : Language := {z | z.foldl bStep (BS.ready .C) = BS.ready .C}

lemma foldl_bits (tk : List EncToken) (s : PS) :
    (encodeTokens tk).foldl bStep (BS.ready s) = BS.ready (tk.foldl pStep s) := by
  induction tk generalizing s with
  | nil => rfl
  | cons e tk ih =>
    rw [encodeTokens_cons, List.foldl_append, List.foldl_cons]
    have : e.encode.foldl bStep (BS.ready s) = BS.ready (pStep s e) := by
      rcases e with ⟨_ | _⟩ | _ | _ <;> rfl
    rw [this, ih]

lemma foldl_bits_inv : ∀ (z : List Bool) (s s' : PS), z.foldl bStep (BS.ready s) = BS.ready s' →
    ∃ tk, z = encodeTokens tk ∧ tk.foldl pStep s = s'
  | [], s, s', h => ⟨[], rfl, by simpa using h⟩
  | [b], s, s', h => by simp [bStep, BS.ready] at h
  | b :: c :: z, s, s', h => by
    simp only [List.foldl_cons, bStep] at h
    obtain ⟨tk, rfl, htk⟩ := foldl_bits_inv z _ s' h
    exact ⟨tokB b c :: tk, by rw [encodeTokens_cons, encode_tokB]; rfl, htk⟩

lemma tokens_snoc_clause (φ : CNF) (c : Clause) :
    CNF.tokens φ ++ Clause.tokens c ++ [EncToken.clauseSep] = CNF.tokens (φ ++ [c]) := by
  simp [CNF.tokens_append, CNF.tokens]

lemma raw_mk (b : Bool) (k : ℕ) :
    Lit.rawTokens ⟨b, k⟩ = EncToken.bit b :: List.replicate k (EncToken.bit true) := rawTokens_eq _

/-- What a prefix looks like in each state. -/
def Inv (tk : List EncToken) : PS → Prop
  | .C => ∃ φ : CNF, tk = φ.tokens
  | .L => ∃ (φ : CNF) (c : Clause), tk = φ.tokens ++ Clause.tokens c
  | .I => ∃ (φ : CNF) (c : Clause) (b : Bool) (k : ℕ),
      tk = φ.tokens ++ Clause.tokens c ++ (EncToken.bit b :: List.replicate k (EncToken.bit true))
  | .bad => True

lemma inv_step {tk : List EncToken} {s : PS} (h : Inv tk s) (e : EncToken) :
    Inv (tk ++ [e]) (pStep s e) := by
  cases s with
  | C =>
    obtain ⟨φ, rfl⟩ := h
    cases e with
    | bit b => exact ⟨φ, [], b, 0, by simp [Clause.tokens]⟩
    | litSep => trivial
    | clauseSep => exact ⟨φ ++ [[]], by rw [← tokens_snoc_clause]; simp [Clause.tokens]⟩
  | L =>
    obtain ⟨φ, c, rfl⟩ := h
    cases e with
    | bit b => exact ⟨φ, c, b, 0, by simp⟩
    | litSep => trivial
    | clauseSep => exact ⟨φ ++ [c], tokens_snoc_clause φ c⟩
  | I =>
    obtain ⟨φ, c, b, k, rfl⟩ := h
    cases e with
    | bit b' =>
      cases b'
      · trivial
      · exact ⟨φ, c, b, k + 1, by simp [List.replicate_succ', List.append_assoc]⟩
    | litSep =>
      refine ⟨φ, c ++ [⟨b, k⟩], ?_⟩
      simp [Clause.tokens_append, Clause.tokens, raw_mk, List.append_assoc]
    | clauseSep => trivial
  | bad => cases e <;> trivial

lemma inv_fold (tk : List EncToken) : Inv tk (tk.foldl pStep .C) := by
  induction tk using List.reverseRecOn with
  | nil => exact ⟨[], rfl⟩
  | append_singleton tk e ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact inv_step ih e

/-- **Soundness of the token automaton.** -/
lemma pfold_sound {tk : List EncToken} (h : tk.foldl pStep .C = .C) : ∃ φ : CNF, tk = φ.tokens := by
  have := inv_fold tk; rw [h] at this; exact this

lemma pfold_lit (ℓ : Lit) (s : PS) (hs : s = .C ∨ s = .L) :
    (ℓ.rawTokens ++ [EncToken.litSep]).foldl pStep s = .L := by
  have h2 : ∀ k, (List.replicate k (EncToken.bit true)).foldl pStep .I = .I := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, List.foldl_cons]; exact ih
  have h1 : pStep s (.bit ℓ.sign) = .I := by rcases hs with rfl | rfl <;> rfl
  rw [rawTokens_eq]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, h1, h2]
  rfl

lemma pfold_clause (c : Clause) (s : PS) (hs : s = .C ∨ s = .L) :
    (Clause.tokens c ++ [EncToken.clauseSep]).foldl pStep s = .C := by
  induction c generalizing s with
  | nil => rcases hs with rfl | rfl <;> rfl
  | cons ℓ c ih =>
    have e : Clause.tokens (ℓ :: c) ++ [EncToken.clauseSep] =
        (ℓ.rawTokens ++ [EncToken.litSep]) ++ (Clause.tokens c ++ [EncToken.clauseSep]) := by
      simp [Clause.tokens, List.append_assoc]
    rw [e, List.foldl_append, pfold_lit ℓ s hs]
    exact ih .L (Or.inr rfl)

lemma pfold_cnf (φ : CNF) : φ.tokens.foldl pStep .C = .C := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    rw [CNF.tokens, List.foldl_append, pfold_clause c .C (Or.inl rfl), ih]

/-- **The scanner recognises exactly the CNF encodings.** -/
theorem valid_iff (z : List Bool) : z ∈ Valid ↔ ∃ φ : CNF, z = φ.encode := by
  constructor
  · intro h
    obtain ⟨tk, rfl, htk⟩ := foldl_bits_inv z .C .C h
    obtain ⟨φ, rfl⟩ := pfold_sound htk
    exact ⟨φ, CNF.encodeTokens_tokens φ⟩
  · rintro ⟨φ, rfl⟩
    show φ.encode.foldl bStep (BS.ready .C) = BS.ready .C
    rw [← CNF.encodeTokens_tokens, foldl_bits, pfold_cnf]

theorem valid_mem_P : Valid ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, 0, TM.scannerTM (BS.ready .C) bStep
    (fun s => if decide (s = BS.ready .C) then .one else .zero), fun n => n + 2,
    TM.scannerTM_decidesInTime (BS.ready .C) bStep (fun s => decide (s = BS.ready .C))
      (fun x => by simp [Valid]), ?_⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

theorem valid_FPPred : FPPred fun z => z ∈ Valid := by
  obtain ⟨g, hg, hgL⟩ := mem_P_iff_exists_decisionFn.mp valid_mem_P
  exact (FPPred.of_flag hg).of_iff fun z => (hgL z).symm

/-! ### Token streams read off bits -/

/-- The token stream of a bit string (pairs of bits). -/
def ofBits (z : List Bool) : TS :=
  ⟨z.length / 2, fun t => if 2 * t + 1 < z.length then
    some (tokB (z.getD (2 * t) false) (z.getD (2 * t + 1) false)) else none⟩

lemma ofBits_encodeTokens (tk : List EncToken) : ofBits (encodeTokens tk) = ofList tk := by
  have hlen : ∀ tk : List EncToken, (encodeTokens tk).length = 2 * tk.length := by
    intro tk; induction tk with
    | nil => rfl
    | cons e tk ih =>
      rw [encodeTokens_cons, List.length_append, ih]
      rcases e with ⟨_ | _⟩ | _ | _ <;> simp [EncToken.encode] <;> omega
  have hget : ∀ (tk : List EncToken) (t : ℕ) (ht : t < tk.length),
      tokB ((encodeTokens tk).getD (2 * t) false) ((encodeTokens tk).getD (2 * t + 1) false) =
        tk[t]'ht := by
    intro tk; induction tk with
    | nil => intro t ht; simp at ht
    | cons e tk ih =>
      intro t ht
      rw [encodeTokens_cons]
      have he : e.encode.length = 2 := by rcases e with ⟨_ | _⟩ | _ | _ <;> rfl
      rcases t with _ | t
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : 0 < e.encode.length),
          List.getElem?_append_left (by omega : 0 * 2 + 1 < e.encode.length)]
        simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
        have := tokB_encode e
        simp only [List.getD_eq_getElem?_getD] at this
        exact this
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), he,
          show 2 * (t + 1) - 2 = 2 * t by omega, show 2 * (t + 1) + 1 - 2 = 2 * t + 1 by omega]
        have := ih t (by simp at ht; omega)
        simp only [List.getD_eq_getElem?_getD] at this
        rw [this]; simp
  unfold ofBits ofList
  congr 1
  · rw [hlen]; omega
  · funext t
    rw [hlen]
    split_ifs with h
    · rw [hget tk t (by omega), List.getElem?_eq_getElem (by omega)]
    · rw [List.getElem?_eq_none (by omega)]

lemma ofBits_encode (φ : CNF) : ofBits φ.encode = ofList φ.tokens := by
  rw [← CNF.encodeTokens_tokens, ofBits_encodeTokens]

end TS

end Pts
