import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Workspace

/-!
# Decidability of workspace preconditions

`SignedRecursiveWorkspaceOK`, `CSignedRecursiveWorkspaceOK`, and `QFTReserveOK`
are `Prop`-valued structures whose fields are all `≤` on `ℕ` (already
decidable) or `ExtReg.OwnedDisjoint`/`ExtReg.CtrlDisjoint` (disjointness of
concrete `List ℕ` qubit lists). This file holds the only `Decidable`
instances for the latter two in the repo — every other construction of
these structures is an abstract tactic proof from assumed hypotheses, never
a decidability check against concrete registers. The two instances below
use the same `unfold; infer_instance` idiom `Compiler/Layout.lean:104-107`
uses for `isTopChunk` — `List.Disjoint`'s `∀ ⦃a⦄, a ∈ l₁
→ a ∈ l₂ → False` shape is exactly the bounded-forall form
`List.decidableBAll` already covers for `DecidableEq α`.

Downstream code (`Lower/PhaseProduct.lean`, `Lower/Qft.lean`) discharges
`SignedRecursiveWorkspaceOK`/`CSignedRecursiveWorkspaceOK`/`QFTReserveOK` (and
plain `Disjoint active reserve`, needed to build an `ExtReg` at all) with
`if h : … then … else refuse` against a *concrete* `n` supplied on the
command line — there is no need to prove any of this for all `n`.
-/

namespace Shor

instance decidableRegDisjoint (a b : Reg) : Decidable (Disjoint a b) := by
  unfold Disjoint List.Disjoint
  infer_instance

instance decidableExtRegOwnedDisjoint (x z : ExtReg) : Decidable (ExtReg.OwnedDisjoint x z) := by
  unfold ExtReg.OwnedDisjoint List.Disjoint
  infer_instance

instance decidableExtRegCtrlDisjoint (ctrl : ℕ) (x z : ExtReg) :
    Decidable (ExtReg.CtrlDisjoint ctrl x z) := by
  unfold ExtReg.CtrlDisjoint
  infer_instance

/-- `SignedRecursiveWorkspaceOK` is exactly its three fields conjoined. -/
instance decidableSignedRecursiveWorkspaceOK {k : ℕ} (ops : Prog k) (x z : ExtReg) :
    Decidable (SignedRecursiveWorkspaceOK ops x z) :=
  decidable_of_iff
    (ExtReg.OwnedDisjoint x z ∧
      (RecursivePhaseWorkspace.reserveNeed ops x.width z.width).1 ≤ x.capacity ∧
      (RecursivePhaseWorkspace.reserveNeed ops x.width z.width).2 ≤ z.capacity)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun h => ⟨h.owned_disjoint, h.x_reserve_sufficient, h.z_reserve_sufficient⟩⟩

/-- `CSignedRecursiveWorkspaceOK` is `SignedRecursiveWorkspaceOK` plus one
extra disjointness field. -/
instance decidableCSignedRecursiveWorkspaceOK {k : ℕ} (ops : Prog k) (ctrl : ℕ) (x z : ExtReg) :
    Decidable (CSignedRecursiveWorkspaceOK ops ctrl x z) :=
  decidable_of_iff
    (SignedRecursiveWorkspaceOK ops x z ∧ ExtReg.CtrlDisjoint ctrl x z)
    ⟨fun ⟨a, b⟩ => { a with control_disjoint := b },
     fun h => ⟨h.toSignedRecursiveWorkspaceOK, h.control_disjoint⟩⟩

/-- `QFTReserveOK` is its one field. -/
instance decidableQFTReserveOK {k : ℕ} (ops : Prog k) (r : ExtReg) : Decidable (QFTReserveOK ops r) :=
  decidable_of_iff ((qftWorkspaceNeed ops r.width).1 + (qftWorkspaceNeed ops r.width).2 ≤ r.capacity)
    ⟨fun h => ⟨h⟩, fun h => h.reserve_large_enough⟩

/-! ## The policy spellings

Field for field the same predicates with `Policy.reserveNeed P` /
`Policy.qftWorkspaceNeed P` in place of the fixed-table models, so the
instances are the same `decidable_of_iff`. They are what lets the policy
evaluation tier (`Reflect/PolicyVerify.lean`) write
`if hws : Policy.WorkspaceOK … then` at a concrete width. -/

instance decidablePolicyWorkspaceOK (P : ShorLoweringPolicy) (x z : ExtReg) :
    Decidable (Policy.WorkspaceOK P x z) :=
  decidable_of_iff
    (ExtReg.OwnedDisjoint x z ∧
      (Policy.reserveNeed P x.width z.width).1 ≤ x.capacity ∧
      (Policy.reserveNeed P x.width z.width).2 ≤ z.capacity)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩,
     fun h => ⟨h.owned_disjoint, h.x_reserve_sufficient, h.z_reserve_sufficient⟩⟩

instance decidablePolicyCWorkspaceOK (P : ShorLoweringPolicy) (ctrl : ℕ) (x z : ExtReg) :
    Decidable (Policy.CWorkspaceOK P ctrl x z) :=
  decidable_of_iff
    (Policy.WorkspaceOK P x z ∧ ExtReg.CtrlDisjoint ctrl x z)
    ⟨fun ⟨a, b⟩ => { a with control_disjoint := b },
     fun h => ⟨h.toWorkspaceOK, h.control_disjoint⟩⟩

instance decidablePolicyQFTReserveOK (P : ShorLoweringPolicy) (r : ExtReg) :
    Decidable (Policy.QFTReserveOK P r) :=
  decidable_of_iff
    ((Policy.qftWorkspaceNeed P r.width).1 + (Policy.qftWorkspaceNeed P r.width).2 ≤ r.capacity)
    ⟨fun h => ⟨h⟩, fun h => h.reserve_large_enough⟩

end Shor
