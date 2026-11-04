import Points.SatOuts

/-!
# The SAT → table map in polynomial time

Token predicates on `ofBits z` at polynomial-time positions are polynomial-time tests
(`fp_lit`, …), the closed-form out-neighbours are polynomial-time numbers (`fp_o1`, `fp_o2`,
`fp_two`), and the encoded table instance is a concatenation over vertex ranges.
-/

namespace Pts

open Complexity SAT

namespace TS

variable {Z : List Bool → List Bool} {t x s : List Bool → ℕ}

lemma fp_T (hZ : Z ∈ FP) : UnaryFn fun y => (ofBits (Z y)).T :=
  (UnaryFn.length hZ).div (UnaryFn.const 2)

lemma fp_bit (hZ : Z ∈ FP) (ht : UnaryFn t) : FPPred fun y => (Z y).getD (t y) false = true :=
  (FPPred.getBit hZ ht).of_iff fun y => by rw [List.getD_eq_getElem?_getD]

lemma tok_ofBits (z : List Bool) (t : ℕ) (e : EncToken) :
    (ofBits z).tok t = some e ↔ 2 * t + 1 < z.length ∧
      tokB (z.getD (2 * t) false) (z.getD (2 * t + 1) false) = e := by
  unfold ofBits; dsimp only; split_ifs with h <;> simp [h]

lemma tokB_eq (b c : Bool) (e : EncToken) :
    tokB b c = e ↔ (b = (e.encode.getD 0 false) ∧ c = (e.encode.getD 1 false)) := by
  constructor
  · rintro rfl; cases b <;> cases c <;> simp [tokB, EncToken.encode]
  · rintro ⟨rfl, rfl⟩; exact tokB_encode e

lemma fp_tok (hZ : Z ∈ FP) (ht : UnaryFn t) (e : EncToken) :
    FPPred fun y => (ofBits (Z y)).tok (t y) = some e := by
  have h2t : UnaryFn fun y => 2 * t y := (UnaryFn.const 2).mul ht
  have h2t1 : UnaryFn fun y => 2 * t y + 1 := h2t.add (UnaryFn.const 1)
  have hb1 := fp_bit hZ h2t
  have hb2 := fp_bit hZ h2t1
  have hlt := FPPred.lt h2t1 (UnaryFn.length hZ)
  have key : ∀ (P : List Bool → Prop) (v : Bool), FPPred P → FPPred fun y => (P y ↔ v = true) :=
    fun P v hP => by
      cases v
      · exact hP.not.of_iff fun y => by simp
      · exact hP.of_iff fun y => by simp
  refine (hlt.and ((key _ (e.encode.getD 0 false) hb1).and (key _ (e.encode.getD 1 false) hb2))).of_iff
    fun y => ?_
  rw [tok_ofBits, tokB_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · cases h : (Z y).getD (2 * t y) false <;> cases h' : e.encode.getD 0 false <;> simp_all
    · cases h : (Z y).getD (2 * t y + 1) false <;> cases h' : e.encode.getD 1 false <;> simp_all
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · cases h : (Z y).getD (2 * t y) false <;> cases h' : e.encode.getD 0 false <;> simp_all
    · cases h : (Z y).getD (2 * t y + 1) false <;> cases h' : e.encode.getD 1 false <;> simp_all

lemma fp_cs (hZ : Z ∈ FP) (ht : UnaryFn t) : FPPred fun y => (ofBits (Z y)).cs (t y) :=
  fp_tok hZ ht _

lemma fp_pos (hZ : Z ∈ FP) (ht : UnaryFn t) : FPPred fun y => (ofBits (Z y)).pos (t y) :=
  fp_tok hZ ht _

lemma fp_isSep (hZ : Z ∈ FP) (ht : UnaryFn t) : FPPred fun y => (ofBits (Z y)).isSep (t y) :=
  (fp_tok hZ ht _).or (fp_tok hZ ht _)

lemma fp_isBit (hZ : Z ∈ FP) (ht : UnaryFn t) : FPPred fun y => (ofBits (Z y)).isBit (t y) :=
  (fp_tok hZ ht _).or (fp_tok hZ ht _)

lemma fp_bnd (hZ : Z ∈ FP) (ht : UnaryFn t) : FPPred fun y => (ofBits (Z y)).bnd (t y) :=
  (FPPred.eq ht (UnaryFn.const 0)).or (fp_isSep hZ (ht.sub (UnaryFn.const 1)))

lemma fp_clStart (hZ : Z ∈ FP) (ht : UnaryFn t) : FPPred fun y => (ofBits (Z y)).clStart (t y) :=
  (FPPred.eq ht (UnaryFn.const 0)).or (fp_cs hZ (ht.sub (UnaryFn.const 1)))

lemma fp_lit (hZ : Z ∈ FP) (hx : UnaryFn x) (hs : UnaryFn s) :
    FPPred fun y => (ofBits (Z y)).lit (x y) (s y) := by
  have hsgn := (fp_isBit hZ hs).and (fp_bnd hZ hs)
  have hZ' : (fun w => Z (pairFst w)) ∈ FP := mem_FP_comp pairFst_mem_FP hZ
  have hin := fp_tok (e := .bit true) hZ'
    ((hs.lift.add (UnaryFn.const 1)).add UnaryFn.index)
  have hall := FPPred.forall_lt hx hin
  have hend := fp_tok (e := .litSep) hZ ((hs.add (UnaryFn.const 1)).add hx)
  refine (hsgn.and (hall.and hend)).of_iff fun y => ?_
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  rfl

lemma fp_mir (hZ : Z ∈ FP) (hx : UnaryFn x) (hs : UnaryFn s) :
    FPPred fun y => (ofBits (Z y)).mir (x y) (s y) :=
  (fp_lit hZ hx hs).and (fp_pos hZ hs).not

/-- The literal test read from `pair y 1^x`. -/
lemma fp_lit_idx (hZ : Z ∈ FP) (hs : UnaryFn s) :
    FPPred fun w => (ofBits (Z (pairFst w))).lit (pairSnd w).length (s (pairFst w)) :=
  fp_lit (mem_FP_comp pairFst_mem_FP hZ) UnaryFn.index hs.lift

lemma fp_exLit (hZ : Z ∈ FP) (hs : UnaryFn s) : FPPred fun y => (ofBits (Z y)).exLit (s y) :=
  (FPPred.exists_lt (fp_T hZ) (fp_lit_idx hZ hs)).of_iff fun y => by
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]; rfl

lemma fp_vf (hZ : Z ∈ FP) (hs : UnaryFn s) : UnaryFn fun y => (ofBits (Z y)).vf (s y) :=
  (UnaryFn.find (fp_T hZ) (fp_lit_idx hZ hs)).of_eq fun y => by
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]; rfl

section closed

variable {u q : List Bool → ℕ}

local notation "Gy" y => ofBits (Z y)

lemma fp_N6 (hZ : Z ∈ FP) : UnaryFn fun y => (Gy y).N6 :=
  (UnaryFn.const 6).mul ((fp_T hZ).mul (fp_T hZ))

lemma fp_cE (hZ : Z ∈ FP) (hx : UnaryFn x) (hs : UnaryFn s) (hq : UnaryFn q) :
    UnaryFn fun y => (Gy y).cE (x y) (s y) (q y) :=
  ((UnaryFn.const 6).mul ((hx.mul (fp_T hZ)).add hs)).add hq

lemma fp_eLn (hZ : Z ∈ FP) (hx : UnaryFn x) (hs : UnaryFn s) :
    UnaryFn fun y => (Gy y).eLn (x y) (s y) :=
  fp_cE hZ hx hs (UnaryFn.ite (fp_mir hZ hx hs) (UnaryFn.const 4) (UnaryFn.const 0))

lemma fp_eRn (hZ : Z ∈ FP) (hx : UnaryFn x) (hs : UnaryFn s) :
    UnaryFn fun y => (Gy y).eRn (x y) (s y) :=
  fp_cE hZ hx hs (UnaryFn.ite (fp_mir hZ hx hs) (UnaryFn.const 0) (UnaryFn.const 4))

lemma fp_topN (hZ : Z ∈ FP) (hx : UnaryFn x) : UnaryFn fun y => (Gy y).topN (x y) :=
  (fp_N6 hZ).add hx
lemma fp_botN (hZ : Z ∈ FP) (hx : UnaryFn x) : UnaryFn fun y => (Gy y).botN (x y) :=
  ((fp_N6 hZ).add (fp_T hZ)).add hx
lemma fp_rN (hZ : Z ∈ FP) (hx : UnaryFn x) : UnaryFn fun y => (Gy y).rN (x y) :=
  ((fp_N6 hZ).add ((UnaryFn.const 2).mul (fp_T hZ))).add hx
lemma fp_qN (hZ : Z ∈ FP) (hx : UnaryFn x) : UnaryFn fun y => (Gy y).qN (x y) :=
  ((fp_N6 hZ).add ((UnaryFn.const 3).mul (fp_T hZ))).add hx

lemma fp_LpN (hZ : Z ∈ FP) (hx : UnaryFn x) (hs : UnaryFn s) :
    UnaryFn fun y => (Gy y).LpN (x y) (s y) :=
  UnaryFn.ite (FPPred.eq hs (UnaryFn.const 0)) (fp_botN hZ hx)
    (fp_eRn hZ hx (hs.sub (UnaryFn.const 1)))

lemma fp_RpN (hZ : Z ∈ FP) (hx : UnaryFn x) (hs : UnaryFn s) :
    UnaryFn fun y => (Gy y).RpN (x y) (s y) :=
  UnaryFn.ite (FPPred.lt (hs.add (UnaryFn.const 1)) (fp_T hZ))
    (fp_eLn hZ hx (hs.add (UnaryFn.const 1))) (fp_botN hZ hx)

lemma fp_p1N (hZ : Z ∈ FP) (hx : UnaryFn x) (hs : UnaryFn s) :
    UnaryFn fun y => (Gy y).p1N (x y) (s y) :=
  UnaryFn.ite (fp_mir hZ hx hs) (fp_RpN hZ hx hs) (fp_LpN hZ hx hs)

lemma fp_p5N (hZ : Z ∈ FP) (hx : UnaryFn x) (hs : UnaryFn s) :
    UnaryFn fun y => (Gy y).p5N (x y) (s y) :=
  UnaryFn.ite (fp_mir hZ hx hs) (fp_LpN hZ hx hs) (fp_RpN hZ hx hs)

lemma fp_cx (hZ : Z ∈ FP) (hu : UnaryFn u) : UnaryFn fun y => (Gy y).cx (u y) :=
  (hu.div (UnaryFn.const 6)).div (fp_T hZ)
lemma fp_ct (hZ : Z ∈ FP) (hu : UnaryFn u) : UnaryFn fun y => (Gy y).ct (u y) :=
  (hu.div (UnaryFn.const 6)).mod (fp_T hZ)

theorem fp_o1 (hZ : Z ∈ FP) (hu : UnaryFn u) : UnaryFn fun y => (Gy y).o1 (u y) := by
  have hT := fp_T hZ; have hN := fp_N6 hZ
  have hx := fp_cx hZ hu; have ht := fp_ct hZ hu
  have hm := hu.mod (UnaryFn.const 6)
  have c := fun k => fp_cE (q := fun _ => k) hZ hx ht (UnaryFn.const k)
  have hm6 := fun k => FPPred.eq hm (UnaryFn.const k)
  have w1 := hu.sub hN
  have w2 := (hu.sub hN).sub ((UnaryFn.const 2).mul hT)
  have w3 := (hu.sub hN).sub ((UnaryFn.const 3).mul hT)
  have hcell := UnaryFn.ite (hm6 0) (c 1) (UnaryFn.ite (hm6 1) (c 2) (UnaryFn.ite (hm6 2) (c 3)
    (UnaryFn.ite (hm6 3) (c 0) (UnaryFn.ite (hm6 4) (c 5) (c 2)))))
  have htop := fp_eLn hZ w1 (UnaryFn.const 0)
  have hbot := fp_topN hZ ((((hu.sub hN).sub hT).add (UnaryFn.const 1)).mod hT)
  have hr := UnaryFn.ite (fp_cs hZ w2) (fp_qN hZ w2) (fp_rN hZ (w2.add (UnaryFn.const 1)))
  have hq := UnaryFn.ite (fp_clStart hZ w3) (fp_rN hZ w3) (fp_qN hZ (w3.sub (UnaryFn.const 1)))
  refine (UnaryFn.ite (FPPred.lt hu hN) hcell (UnaryFn.ite (FPPred.lt hu (hN.add hT)) htop
    (UnaryFn.ite (FPPred.lt hu (hN.add ((UnaryFn.const 2).mul hT))) hbot
    (UnaryFn.ite (FPPred.lt hu (hN.add ((UnaryFn.const 3).mul hT))) hr hq)))).of_eq fun y => ?_
  simp only [o1, Nat.sub_sub]

theorem fp_o2 (hZ : Z ∈ FP) (hu : UnaryFn u) : UnaryFn fun y => (Gy y).o2 (u y) := by
  have hT := fp_T hZ; have hN := fp_N6 hZ
  have hx := fp_cx hZ hu; have ht := fp_ct hZ hu
  have hm := hu.mod (UnaryFn.const 6)
  have c := fun k => fp_cE (q := fun _ => k) hZ hx ht (UnaryFn.const k)
  have hm6 := fun k => FPPred.eq hm (UnaryFn.const k)
  have w1 := hu.sub hN
  have w2 := (hu.sub hN).sub ((UnaryFn.const 2).mul hT)
  have w3 := (hu.sub hN).sub ((UnaryFn.const 3).mul hT)
  have hcell := UnaryFn.ite (hm6 0) (c 3) (UnaryFn.ite (hm6 1) (fp_p1N hZ hx ht)
    (UnaryFn.ite (hm6 2) (c 5) (UnaryFn.ite (hm6 3) (c 4)
    (UnaryFn.ite (hm6 4) (fp_rN hZ ht) (fp_p5N hZ hx ht)))))
  have htop := fp_eRn hZ w1 (hT.sub (UnaryFn.const 1))
  have w2' := w2.add (UnaryFn.const 1)
  have hr := fp_cE hZ (fp_vf hZ w2') w2' (UnaryFn.const 1)
  have hq := fp_cE hZ (fp_vf hZ w3) w3 (UnaryFn.const 1)
  refine (UnaryFn.ite (FPPred.lt hu hN) hcell (UnaryFn.ite (FPPred.lt hu (hN.add hT)) htop
    (UnaryFn.ite (FPPred.lt hu (hN.add ((UnaryFn.const 2).mul hT))) (UnaryFn.const 0)
    (UnaryFn.ite (FPPred.lt hu (hN.add ((UnaryFn.const 3).mul hT))) hr hq)))).of_eq fun y => ?_
  simp only [o2, Nat.sub_sub]

theorem fp_two (hZ : Z ∈ FP) (hu : UnaryFn u) : FPPred fun y => (Gy y).two (u y) := by
  have hT := fp_T hZ; have hN := fp_N6 hZ
  have hx := fp_cx hZ hu; have ht := fp_ct hZ hu
  have hm := hu.mod (UnaryFn.const 6)
  have w2 := (hu.sub hN).sub ((UnaryFn.const 2).mul hT)
  have w3 := (hu.sub hN).sub ((UnaryFn.const 3).mul hT)
  have c1 := FPPred.lt hu hN
  have c2 := FPPred.lt hu (hN.add hT)
  have c3 := FPPred.lt hu (hN.add ((UnaryFn.const 2).mul hT))
  have c4 := FPPred.lt hu (hN.add ((UnaryFn.const 3).mul hT))
  have pc := (FPPred.eq hm (UnaryFn.const 4)).not.or (fp_lit hZ hx ht)
  have pr := (fp_cs hZ w2).not.and (fp_exLit hZ (w2.add (UnaryFn.const 1)))
  have pq := (fp_clStart hZ w3).and (fp_exLit hZ w3)
  refine ((c1.and pc).or (c1.not.and (c2.or (c3.not.and ((c4.and pr).or (c4.not.and pq)))))).of_iff
    fun y => ?_
  simp only [two, Nat.sub_sub]
  by_cases h1 : u y < (Gy y).N6
  · simp only [h1, if_true, true_and, not_true_eq_false, false_and, or_false]
    constructor
    · rintro (h | h)
      · exact fun e => absurd e h
      · exact fun _ => h
    · intro h
      by_cases e : u y % 6 = 4
      · exact Or.inr (h e)
      · exact Or.inl e
  · simp only [h1, if_false, false_and, false_or, not_false_eq_true, true_and]
    by_cases h2 : u y < (Gy y).N6 + (Gy y).T
    · simp [h2]
    · by_cases h3 : u y < (Gy y).N6 + 2 * (Gy y).T
      · simp [h2, h3]
      · by_cases h4 : u y < (Gy y).N6 + 3 * (Gy y).T
        · simp [h2, h3, h4]
        · simp [h2, h3, h4]

end closed

end TS

end Pts
