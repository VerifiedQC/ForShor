import Provider.Effective.ProfileAllK
import Provider.Effective.ExactPP
import Provider.Effective.Complete
import Provider.Effective.Existence
import Provider.Ceiling.FinalCeiling
import Provider.Ceiling.GroupedPeak
import Model.Scanner.Planner
import PhaseProduct.Catalog.EndToEnd
import Planner.TauPrice
import Provider.Ceiling.GroupedCharge

/-! Axiom audit for the declarations named in `LEAN_MAP.md`. Run after `lake build` with
`lake env lean scripts/AxiomAudit.lean`. Expected: every declaration depends only on
`propext`, `Classical.choice`, `Quot.sound` (the three `Paper.Planner` theorems only on `propext`).
This file is not a library root. -/

#print axioms Paper.ComputableProfileProvider.optimal_raw_F2_exact
#print axioms Paper.ComputableProfileProvider.optimal_raw_F2_allK
#print axioms Paper.EffectiveProvider.effective_optimal_raw_F2_exact
#print axioms Paper.EffectiveProvider.effective_optimal_raw_F2_policy
#print axioms Paper.F2CatalogTransfer.optimal_raw_F2_policy_exists
#print axioms Paper.PPEndToEnd.pp_through_arity_K
#print axioms Paper.PPEndToEnd.optimized_pp_end_to_end
#print axioms Paper.PPEndToEnd.tauRS_eq_tauExact
#print axioms Paper.F3ChargeCeiling.feasible_has_ceiling_grouped
#print axioms Paper.F3ChargeCeiling.minCharge_le_27_cube
#print axioms Paper.F3ChargeCeiling.groupedLiteralBaseline_peaks
#print axioms Paper.F3ChargeCeiling.grouped_bounded_baseline
#print axioms Paper.Planner.childWidth_eq_of_peaks
#print axioms Paper.Planner.widthTrace_eq_of_used_peaks
#print axioms Paper.Planner.planCost_le_of_used_peaks_and_charges
#print axioms Paper.F3ChargeCeiling.groupedLiteralBaseline_charge
#print axioms Paper.F3ChargeCeiling.groupedLiteralBaseline_charge_le
