namespace Shor

/-- A typed full-run selection, separate from the table policy and standalone synthesis.
    The verifier attests the choice; a separate circuit checker must qualify its implementation. -/
inductive FullRunDesign where
  | reference
  | quotientExact
  | quotientCatalytic
  | quotientBandedDataCatalyticWork
  | quotientFallbackDataCatalyticWork
  | quotientStep2Fallback
  | splitStep4Kicks
  | splitStep2FallbackStep4Kicks
  deriving BEq, DecidableEq

def FullRunDesign.label : FullRunDesign → String
  | .reference => "reference"
  | .quotientExact => "quotient-exact"
  | .quotientCatalytic => "quotient-catalytic"
  | .quotientBandedDataCatalyticWork => "quotient-banded-data-catalytic-work"
  | .quotientFallbackDataCatalyticWork => "quotient-fallback-data-catalytic-work"
  | .quotientStep2Fallback => "quotient-step2-fallback"
  | .splitStep4Kicks => "split-step4-kicks"
  | .splitStep2FallbackStep4Kicks => "split-step2-fallback-step4-kicks"

end Shor
