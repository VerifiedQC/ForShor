import Foundations.PairedCharge.Defs

namespace PairedCharge

theorem charge_classes :
    Instr.charge Instr.posAdd = 1 ∧ Instr.charge Instr.negAdd = 3 ∧
    Instr.charge Instr.negation = 1 ∧ Instr.charge Instr.shift = 0 ∧
    Instr.charge Instr.checkpoint = 0 ∧
    ∀ l : List Instr, listCharge l = (l.map Instr.charge).sum := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun l => rfl⟩

end PairedCharge
