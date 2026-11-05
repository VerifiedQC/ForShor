import Source.P6Parity

/-!
# Accepted policy P6

Defines the accepted generator policy P6 as `implementation : TableGeneration.GeneratorPolicy`, built from the parity construction in `Source.P6Parity`.
-/

namespace TableGeneration.Policies.Accepted.P6f7d25984ff8

def implementation : TableGeneration.GeneratorPolicy :=
  GeneralParity.implementation

end TableGeneration.Policies.Accepted.P6f7d25984ff8
