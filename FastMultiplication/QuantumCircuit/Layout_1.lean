import FastMultiplication.QuantumCircuit.Basic

/-- Constant-width, contiguous packing. -/
def constWidth (k w : ℕ) (hk:k>0) (hw:w>0): Layout k :=
{ width  := fun _ => w,
  N      := k * w,
  pack   := fun i b => ⟨i.1 * w + b.1, by
    have : i.1 * w + b.1 < k * w := by
      sorry
    simpa using this⟩,
  unpack := fun q =>
    let i : Fin k := ⟨q.1 / w, by
      -- q < k*w ⇒ q/w < k
      have : q.1 < w*k := by have:=q.2;linarith
      exact Nat.div_lt_of_lt_mul this⟩
    let b : Fin w := ⟨q.1 % w, (by apply Nat.mod_lt;apply hw)⟩
    ⟨i, b⟩,
  pack_unpacked := by
    intro q; cases q with
    | mk q hq =>
      simp;rw[Nat.div_mul_self_eq_mod_sub_self];rw[Nat.sub_add_cancel];apply Nat.mod_le
  ,
  unpack_packed := by
    intro i b; cases i with | mk i hi =>
    cases b with | mk b hb =>
    ext <;> simp [Nat.mul_comm, Nat.add_comm]
    rw[Nat.add_div]
    split_ifs with h
    have l1: b%w=b:=by rw[Nat.mod_eq_of_lt];apply hb
    have l2:w * i % w=0:= by simp
    simp[l1] at h
    apply Nat.not_lt_of_le at h
    aesop
    aesop
    apply hw
    rw[Nat.mod_eq_of_lt];apply hb
    }

/-- Build a heterogeneous layout from an arbitrary width function. -/
noncomputable def Layout.ofWidths {k : ℕ} (width : Fin k → ℕ) : Layout k :=
by
  classical
  -- The "sum-of-blocks" index type
  let α := Σ i : Fin k, Fin (width i)
  -- Equivalence: Fin N ≃ α, and its inverse α ≃ Fin N
  let e  : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let e' : α ≃ Fin (Fintype.card α) := e.symm
  exact
  { width  := width,
    N      := Fintype.card α,
    pack   := fun i b => e' ⟨i, b⟩,
    unpack := fun q   => e  q,
    pack_unpacked := by intro q; simp [e, e'],
    unpack_packed := by intro i b; simp [e, e'] }

/-! ## k = 2 Karatsuba (heterogeneous) -/



/-- Heterogeneous widths that match the diagram:
    x0,x1,z0,z1 are `n2` bits; cx,cz are 1-bit carries. -/
def k2Widths (n2 : ℕ) : Fin 6 → ℕ
| i =>
  match i.val with
  | 0 => n2   -- x0
  | 1 => n2   -- x1
  | 2 => 1
  | 3 => n2   -- z0
  | 4 => n2   -- z1
  | _ => 1

/-- The heterogeneous layout for the k=2 Karatsuba circuit. -/
noncomputable def K2Layout (n2 : ℕ) : Layout 6 :=
  Layout.ofWidths (k := 6) (k2Widths n2)
