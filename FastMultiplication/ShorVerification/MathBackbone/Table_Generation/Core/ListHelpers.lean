import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.Builders.Fragments
import Mathlib.Data.List.Infix

/-!
# Prelude list helpers

Generic list lemmas used by the table-generation proofs. Quarried verbatim
from the former `One_register_synthesis_combined.lean` (Section 1); no
statements changed.
-/

open Operations

/-! =========================================================
    Section 1: Prelude list helpers
========================================================= -/

infix:50 " <+ " => List.Sublist

theorem mem_cons {α : Type _} {a y : α} {l : List α} :
    a ∈ y :: l ↔ a = y ∨ a ∈ l :=
  List.mem_cons

theorem nodup_cons {α : Type _} {a : α} {l : List α} :
    (a :: l).Nodup ↔ a ∉ l ∧ l.Nodup :=
  List.nodup_cons

theorem mem_finRange {n : ℕ} (i : Fin n) :
    i ∈ List.finRange n :=
  List.mem_finRange i

