import FastMultiplication.Emit.Table.Source

/-!
# `Decidable` instances for a user-supplied table's `ShorLoweringSetup` proofs

`Emit/PLAN.md` §11.2 point 5 (R5): a user packaging their own `Prog k` as a
`Shor.ShorLoweringSetup` must prove `consumes : ProgConsumesPtsSafe hk
State.start_state ops (genInterpolationPoints k)` and `returns : run? ops
State.start_state = some State.start_state`. `returns` is already decidable
(`DecidableEq (State k)` via `Fintype.decidablePiFintype`, `State k = Fin k
→ Fin k → ℤ`). `consumes` bundles `ProgConsumesPts` and `SafeProg`, neither
of which had a `Decidable` instance anywhere in the repo: both are stated as
`Prop`s whose shape (an existential fixed by the data, and a `∀` over list
decompositions respectively) hides decidability that only becomes visible
after unfolding. This file supplies both, so a user's `by decide`/`by
native_decide` on a concrete `k`/`ops` just works.
-/

namespace Shor

open Operations

/-- Every non-`phaseProduct` op shares the same shape,
`∃ σ', applyOp? σ op = some σ' ∧ ProgConsumesPts hk σ' ops pts` — this
builds `Decidable` for that shape given the recursive result at whatever
`σ'` `applyOp?` produces. Factored out so `decideProgConsumesPts` below can
call it once per concrete constructor (`shiftL`/`shiftR`/`negate`/
`addScaled`) instead of repeating the same `applyOp?`-case-split four times;
`hEq` lets each call site supply the (defeq-`rfl`) proof that
`ProgConsumesPts` really does unfold to this shape at *that* concrete `op`
— which only holds once `op` is a literal constructor, not a bound
variable (an abstract `op` leaves `ProgConsumesPts`'s own internal `match
op with …` stuck, so this cannot be proven once and reused generically
over `op`). -/
def decideProgConsumesPtsOther {k : ℕ} (hk : k > 0) (σ : State k) (op : valid_ops k) (ops : Prog k)
    (pts : List Point)
    (hEq : ProgConsumesPts hk σ (op :: ops) pts ↔
      ∃ σ', applyOp? (k := k) σ op = some σ' ∧ ProgConsumesPts hk σ' ops pts)
    (rec : (σ' : State k) → Decidable (ProgConsumesPts hk σ' ops pts)) :
    Decidable (ProgConsumesPts hk σ (op :: ops) pts) :=
  match h : applyOp? (k := k) σ op with
  | none => isFalse (fun hp => by obtain ⟨σ', heq, _⟩ := hEq.mp hp; rw [h] at heq; cases heq)
  | some σ' =>
      match rec σ' with
      | isTrue hrec => isTrue (hEq.mpr ⟨σ', h, hrec⟩)
      | isFalse hrec =>
          isFalse (fun hp => by
            obtain ⟨σ'', heq, hrec'⟩ := hEq.mp hp; rw [h] at heq; cases heq; exact hrec hrec')

/-- Term-mode `Decidable` construction for `ProgConsumesPts`, mirroring its
own recursion on `ops` exactly (`Emit/PLAN.md` §11.2 point 5): at
`phaseProduct i`, the existential's witness is `pts`'s own head (nothing to
search for); at any other op, `decideProgConsumesPtsOther` handles it (via
whatever `applyOp?` already computes). Built directly against
`ProgConsumesPts`'s definitional unfolding (no `simp` needed — the
anonymous-constructor proofs below typecheck by the same `match`-reduction
the original `def` itself reduces by), rather than via an `Iff` with a
separately-proven Boolean mirror, since `ProgConsumesPts` itself is not an
`inductive` a mirror-and-transport proof would need to fight the shape of. -/
def decideProgConsumesPts {k : ℕ} (hk : k > 0) :
    (σ : State k) → (ops : Prog k) → (pts : List Point) →
      Decidable (ProgConsumesPts hk σ ops pts)
  | _σ, [], pts => decidable_of_iff (pts = []) Iff.rfl
  | σ, .phaseProduct i :: ops, pts =>
      match pts with
      | [] => isFalse (by rintro ⟨_, _, h, _⟩; cases h)
      | pt :: ptsTail =>
          if h : matchesAt_pointRow_state (k := k) hk σ i pt = true then
            match decideProgConsumesPts hk σ ops ptsTail with
            | isTrue hrec => isTrue ⟨pt, ptsTail, rfl, h, hrec⟩
            | isFalse hrec =>
                isFalse (by rintro ⟨pt', ptsTail', heq, _, hrec'⟩; cases heq; exact hrec hrec')
          else
            isFalse (by rintro ⟨pt', ptsTail', heq, hmatch, _⟩; cases heq; exact h hmatch)
  | σ, (.shiftL a b) :: ops, pts =>
      decideProgConsumesPtsOther hk σ (.shiftL a b) ops pts Iff.rfl
        (fun σ' => decideProgConsumesPts hk σ' ops pts)
  | σ, (.shiftR a b) :: ops, pts =>
      decideProgConsumesPtsOther hk σ (.shiftR a b) ops pts Iff.rfl
        (fun σ' => decideProgConsumesPts hk σ' ops pts)
  | σ, (.negate a) :: ops, pts =>
      decideProgConsumesPtsOther hk σ (.negate a) ops pts Iff.rfl
        (fun σ' => decideProgConsumesPts hk σ' ops pts)
  | σ, (.addScaled a b c d) :: ops, pts =>
      decideProgConsumesPtsOther hk σ (.addScaled a b c d) ops pts Iff.rfl
        (fun σ' => decideProgConsumesPts hk σ' ops pts)

instance decidableProgConsumesPts {k : ℕ} (hk : k > 0) (σ : State k) (ops : Prog k)
    (pts : List Point) : Decidable (ProgConsumesPts hk σ ops pts) :=
  decideProgConsumesPts hk σ ops pts

/-- `SafeProg ops` says every `addScaled d s _ _` occurring anywhere in
`ops` has `d ≠ s`; equivalently, every element of `ops` passes this
Boolean scan. -/
def safeProgCheck {k : ℕ} (ops : Prog k) : Bool :=
  ops.all fun op =>
    match op with
    | valid_ops.addScaled d s _ _ => decide (d ≠ s)
    | _ => true

theorem safeProg_iff_check {k : ℕ} (ops : Prog k) : SafeProg ops ↔ safeProgCheck ops = true := by
  simp only [safeProgCheck, List.all_eq_true]
  constructor
  · intro h op hop
    match op, hop with
    | valid_ops.addScaled d s negSrc sh, hop =>
        obtain ⟨pre, rest, heq⟩ := List.mem_iff_append.mp hop
        exact decide_eq_true (h heq)
    | valid_ops.shiftL .., _ => rfl
    | valid_ops.shiftR .., _ => rfl
    | valid_ops.negate _, _ => rfl
    | valid_ops.phaseProduct _, _ => rfl
  · intro h pre rest d s negSrc sh heq
    have hmem : valid_ops.addScaled d s negSrc sh ∈ ops := heq ▸ List.mem_append_right pre List.mem_cons_self
    simpa using h _ hmem

instance decidableSafeProg {k : ℕ} (ops : Prog k) : Decidable (SafeProg ops) :=
  decidable_of_iff _ (safeProg_iff_check ops).symm

instance decidableProgConsumesPtsSafe {k : ℕ} (hk : k > 0) (σ : State k) (ops : Prog k)
    (pts : List Point) : Decidable (ProgConsumesPtsSafe hk σ ops pts) :=
  decidable_of_iff (ProgConsumesPts hk σ ops pts ∧ SafeProg ops)
    ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.consumes, h.safe_add⟩⟩

end Shor
