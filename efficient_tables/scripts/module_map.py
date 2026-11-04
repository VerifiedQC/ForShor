"""Old flat module name -> new layered module name (one-shot restructure record)."""
import re

M = {}

def add(prefix, pairs):
    for old, new in pairs:
        M[old] = f"{prefix}.{new}"

# ---- Foundations: pure counting / word / budget arithmetic, no Paper dependency
add("Foundations.Counting", [
    ("WeightedWords.Count", "WeightedWords"),
    ("TypedWords.Enumeration", "TypedWords"),
    ("WordRuntime.Calls", "RecursiveCalls"),
    ("TypedConsistency.Fixed", "TypedConsistency"),
    ("CountStage.Bounds", "BranchCount"),
    ("DimensionBound.Elementary", "DimensionBound"),
    ("OuterComplexity.Composition", "OuterComposition"),
])
add("Foundations", [("MachineResource.Bounds", "MachineResource")])

# ---- Source: the source-level program model and its best-known-table contracts
src = ["Language", "Metrics", "Spec", "Model", "Baseline", "Policy", "P52", "P6Parity", "P6",
       "Pf4Fixed", "Pf4Parity", "Pf4", "BestKnown", "Catalog", "RecursivePlanner", "RecursiveCorrectness"]
for s in src: M[f"Paper.Source{s}"] = f"Source.{s}"
M["Paper.SourceBasic"] = "Source.Basic"

# ---- Model: the exact model (Defs), width scanner, instruction DSL, interpreter
M["Paper.Defs"] = "Model.Defs"
add("Model.Scanner", [("Paper.Scanner", "Scanner"), ("Paper.ArrayScanner", "ArrayScanner"),
    ("Paper.ArrayPrefixTrajectory", "ArrayPrefixTrajectory"), ("Paper.LimbReconstruction", "LimbReconstruction"),
    ("Paper.SplitHelper", "SplitHelper"), ("Paper.Profile", "Profile"),
    ("Paper.Planner", "Planner"), ("Paper.C11", "C11")])
add("Model.Interpreter", [("Paper.FullDSL", "FullDSL"), ("Paper.Mass", "Mass"), ("Paper.Interpreter", "Interpreter"),
    ("Paper.RawInterpreter", "RawInterpreter"), ("Paper.Values", "Values"), ("Paper.Consumption", "Consumption"),
    ("Paper.ValueTrace", "ValueTrace"), ("Paper.ValueBounds", "ValueBounds"),
    ("Paper.ValueBoundsPrefixes", "ValueBoundsPrefixes"), ("Paper.BasisReflection", "BasisReflection"),
    ("Paper.Costs", "Costs"), ("Paper.Connection", "Connection"), ("Paper.SourceConnection", "SourceConnection")])

# ---- Planner: recursive objective, planner optimality, exact integer price
add("Planner", [("Paper.PlannerReachability", "Reachability"),
    ("Paper.RecursivePlannerLocal", "RecursiveLocal"), ("Paper.PlannerDenseSparse", "DenseSparse"),
    ("Paper.PlannerOptimality", "Optimality"), ("Paper.PolicyOptimality", "PolicyOptimality"),
    ("Price.Tau", "TauPrice")])

# ---- PhaseProduct: the phase identity and the finite-catalogue end-to-end optimum
add("PhaseProduct.Identity", [("Paper.PhaseIdentity", "PhaseIdentity"), ("Paper.Normalization", "Normalization"),
    ("Paper.Interpolation", "Interpolation"), ("Paper.GenericPhase", "GenericPhase"),
    ("Paper.GeneralConstruction", "GeneralConstruction"), ("Paper.PointNodes", "PointNodes"),
    ("Paper.ListPhase", "ListPhase"), ("Paper.CanonicalNodes", "CanonicalNodes"),
    ("Paper.CanonicalValidity", "CanonicalValidity"), ("Paper.PhaseTables", "PhaseTables")])
add("PhaseProduct.Baseline", [("Paper.BaselineArithmetic", "BaselineArithmetic"), ("Paper.BuilderRows", "BuilderRows"),
    ("Paper.BaselineContract", "BaselineContract"), ("Paper.BaselinePhase", "BaselinePhase")])
add("PhaseProduct.Encoding", [("Paper.SignedEncoding", "SignedEncoding"), ("Paper.BitStep", "BitStep"),
    ("Paper.BitTrace", "BitTrace")])
add("PhaseProduct.Catalog", [("Paper.BestKnownContract", "BestKnownContract"), ("Paper.BestKnownPhase", "BestKnownPhase"),
    ("Paper.CatalogSemantics", "CatalogSemantics"), ("Paper.ChoiceSoundness", "ChoiceSoundness"), ("Paper.ValuePhase", "ValuePhase"),
    ("Paper.FinitePhase", "FinitePhase"), ("Paper.Schoolbook", "Schoolbook"), ("Paper.IntegerInputPhase", "IntegerInputPhase"),
    ("Paper.PPTableSemantics", "TableSemantics"), ("Paper.PPCount", "Count"),
    ("Paper.PPRecursiveSemantics", "RecursiveSemantics"), ("Paper.PPEndToEnd", "EndToEnd")])

# ---- Compression: shift-block compression preserving profiles
add("Provider.Compression", [("Potential.Bounds", "Potential"), ("PaddingStage.Prefix", "Padding"),
    ("Compression.Block", "Block"), ("CompressionProgram.Whole", "Program"), ("CompressionTrace.Values", "Trace"),
    ("CompressionSource.Bridge", "SourceBridge"), ("CompressionF2.Witness", "F2Witness"),
    ("CompressionEncoding.Bounds", "EncodingBounds"), ("CompressionCertificate.Transfer", "CertificateTransfer"),
    ("CompressionComplete.Result", "Result")])

# ---- Provider: raw F2 ladders, profile intervals, ceilings, weights, effective provider, A2 optimizer
add("Provider.Ladders", [("F2Stage.F2CatalogTransfer_20261016T170100", "CatalogTransfer"),
    ("F2Stage.F2Certificate_20261016T213100", "Certificate"),
    ("F2Stage.F2CertificateExists_20261016T213500", "CertificateExists")])
add("Provider.Profiles", [("F4.Intervals", "Intervals"), ("Reconstruction.Exact", "Reconstruction"),
    ("ReconstructionShared.Shared", "SharedReconstruction"), ("ActualPolicy.Bound", "ActualPolicyBound")])
add("Provider.Ceiling", [("F3.Ceiling", "Ceiling"), ("F3Witness.Source", "Witness"), ("F3Grouped.Source", "Grouped"),
    ("F3Dyadic.Power", "DyadicPower"), ("F3Scanner.Fixed", "FixedScanner"), ("F3SourceFixed.Word", "SourceFixedWord"),
    ("F3Points.Dyadic", "DyadicPoints"), ("F3Coeff.Basic", "Coefficients"), ("F3Block.Local", "LocalBlock"),
    ("F3PointBlock.Bound", "PointBlock"), ("F3Groups.Words", "GroupWords"), ("F3GroupScan.Peak", "GroupScanPeak"),
    ("F3GroupedPeak.Profile", "GroupedPeak"), ("F3Final.Ceiling", "FinalCeiling")])
add("Provider.Weights", [("A4Bundle.All", "Projective"), ("A4Rational.Weights", "Rational"), ("RationalBundle.All", "Reduced")])
add("Provider.Effective", [("ProviderStage.Bridge6", "Bridge"), ("ProviderStage.Keys2", "Keys"),
    ("ProviderStage.FiniteProvider3", "FiniteProvider"), ("ProviderStage.Existence3", "Existence"),
    ("EffectiveProvider.Complete", "Complete"), ("A2Bundle.All", "Enumeration"), ("A2Size.Bounds", "Size"),
    ("A2Card.Catalog", "Cardinality"), ("A2Profile.Provider", "ProfileProvider"), ("A2Profile.Exact", "ProfileExact"),
    ("A2Profile.AllK", "ProfileAllK"), ("A2Exact.PP", "ExactPP"), ("A2Runner.Optimize", "Optimize"),
    ("A2Attain.Raw", "Attain")])

# ---- ILPEncoding: affine cost / ILP encoding of the shared-ladder objective and its bit-size bounds
add("ILPEncoding.Affine", [("AffineILP.Core", "Core"), ("AffineShared.Offsets", "Offsets"), ("AffineCost.Cleared", "Cleared")])
add("ILPEncoding.Labels", [("F6Bundle.All", "Labels"), ("F6Typed.Bridge", "Typed"), ("F6Final.All", "Final"),
    ("F6ILPChecked.All", "ILPChecked"), ("F6Positive.Actual", "Positive"), ("F6SharedCost.Actual", "SharedCost")])
add("ILPEncoding.Bounds", [("StopBudget.Polynomial", "StopBudget"), ("F7Size.Prefix", "Size"), ("F7Global.Bounds", "Global"),
    ("F7QControl.Prefix", "QControl"), ("F7Products.Bounds", "Products"), ("F7Terminal.Bounds", "Terminal"),
    ("F7LeafCanon.Bound", "LeafCanon"), ("F7WordSize.Bounds", "WordSize"), ("F7Budget.Sum", "BudgetSum"),
    ("F7Budget.Leaf", "BudgetLeaf"), ("F7Budget.Step", "BudgetStep"), ("F7Budget.Actual", "BudgetActual"),
    ("F7Budget.Magnitude", "BudgetMagnitude"), ("F7Budget.Canonical", "BudgetCanonical"),
    ("F7Encoding.Matrix", "Matrix"), ("F7Computable.Rows", "ComputableRows"),
    ("F7Semantics.Rows", "SemanticRows"), ("F7Contraction.Global", "ContractionGlobal"),
    ("F7Contraction.Rows", "ContractionRows"), ("F7Contraction.Root", "ContractionRoot"),
    ("F7System.Common", "SystemCommon"), ("F7System.Numeric", "SystemNumeric"),
    ("F7MatrixFinal.Canonical", "CanonicalMatrix")])
add("ILPEncoding.Bundles", [("ProfileBundle.All", "Profile"), ("EncodingBundle.All", "Encoding"),
    ("F7MatrixFinal.Optimizer", "MatrixOptimizer")])

# ---- Alignment: Fortran-solver alignment and the sparse-threshold census
add("Alignment", [("AlignmentBundle.All", "FortranSolver"), ("ExecutionAlignment.SparseThreshold", "SparseThreshold")])

# ---- Helpers: standalone Mathlib-only lemma files (separate library)
HELPERS = {}
for old in ["CanonicalProfile20261015T140900", "CanonicalProfileMinimal20261015T141600",
            "ChangingHelpers20261016T014500", "CompleteRepresentation20261016T024500",
            "CrossingExchange20261015T223000", "DualCap20261016T005600", "DyadicFlow20261016T092900",
            "GapAlgebraRepair20261015", "GlobalScanner20261015T204800", "HelperIdentities20261015T213100",
            "ObservedCaps20261015T224600", "RootLoadBoundsV1", "RootLoadBoundsV2",
            "RunQuotaExchange20261015T201400", "RunQuotaExchangeRepair20261015T202100",
            "StateBudget20261016T011900", "SymbolicBoundary20261016T014500", "SymbolicSolver20261016T001800",
            "ThresholdAlgebraRepair20261015", "UniformPolicy20261015T231700"]:
    HELPERS[old] = re.sub(r"\d{8}(T\d{6})?$", "", old)
