import Foundations.PairedCharge.Defs

namespace PairedCharge

open Classical in
theorem skeleton_unfold (k : ℕ) (hk : 2 ≤ k) :
    skeleton k =
      [Instr.checkpoint, Instr.checkpoint] ++
      (List.replicate (k - 2)
        (List.replicate (k - 2) Instr.posAdd ++
          [Instr.posAdd, Instr.negAdd, Instr.posAdd] ++
          List.replicate (k - 2) Instr.negAdd)).flatten ++
      (List.replicate (k - 1) Instr.posAdd ++
        List.replicate (k - 1) Instr.negAdd) ++
      List.replicate
        (if Even k then
          2 * ((Finset.Ico 2 (2 * k - 1)).filter (fun i => IsNegFrac (pointAt i))).card
         else 0) Instr.negation := by
  unfold skeleton singletonBlock pairBlock
  congr

end PairedCharge
