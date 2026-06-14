const graphData = {
  overview: {
    title: "ShorVerification",
    subtitle: "Top-level correctness architecture",
    description:
      "The repository splits Shor verification into a shared semantic core, classical/source-program mathematics, high-level circuit correctness, low-level lowering, approximation bounds, and the final order-finding/factoring statements.",
    nodes: [
      {
        id: "basic",
        label: "Basic semantics",
        subtitle: "Reg, ExtReg, Gate, QSemantics",
        kind: "core",
        view: "basic",
        file: "FastMultiplication/ShorVerification/Basic.lean",
        declarations: ["Reg", "ExtReg", "Gate", "QSemantics", "eval_PhaseProd_ket", "eval_norm_preserved"],
        summary:
          "Defines the register model, abstract gate language, quantum semantics interfaces, and reusable semantic facts used by every later proof layer."
      },
      {
        id: "table",
        label: "Table generation",
        subtitle: "source programs and coverage",
        kind: "math",
        view: "table",
        file: "FastMultiplication/ShorVerification/MathBackBone/Table_Generation",
        declarations: ["Prog", "run?", "PhaseProductCoverage", "genOpsWithProduct_PhaseProductCoverage"],
        summary:
          "Builds symbolic arithmetic programs and proves that generated operations consume the interpolation phase points needed by the phase-product compiler."
      },
      {
        id: "toom",
        label: "Toom-Cook algebra",
        subtitle: "interpolation matrix facts",
        kind: "math",
        view: "toom",
        file: "FastMultiplication/ShorVerification/MathBackBone/Toom_Cook_formula.lean",
        declarations: ["GoodInterpolationPoints", "evalAtRadix", "interpCoeff"],
        summary:
          "Supplies the interpolation algebra that turns phase contributions at points into the intended signed multiplication phase scalar."
      },
      {
        id: "phase",
        label: "Phase-product correctness",
        subtitle: "compileOpsToSignedGate",
        kind: "algorithm",
        view: "phase",
        file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/PhaseProduct",
        declarations: ["allocated_widths_sound", "toom_cook_interpolation", "eval_compileOpsToSignedGate_correct"],
        summary:
          "Assembles width soundness, allocation correctness, compiled operation semantics, and interpolation correctness into the main phase-product compiler theorem."
      },
      {
        id: "qft",
        label: "QFT decomposition",
        subtitle: "split identity",
        kind: "algorithm",
        view: "qft",
        file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/QFT/Decomposition.lean",
        declarations: ["eval_QFT_split"],
        summary:
          "Proves that a QFT over a register decomposes into smaller QFTs, phase product, and radix reversal."
      },
      {
        id: "machine",
        label: "Abstract machine",
        subtitle: "Gate to LowGate lowering",
        kind: "machine",
        view: "machine",
        file: "FastMultiplication/ShorVerification/AbstractMachine",
        declarations: ["LowGate", "eval_lowerQFT", "lowerGate_correctness"],
        summary:
          "Defines the target low-level gate language and proves recursive lowering correctness for QFT, phase products, and whole programs."
      },
      {
        id: "modexp",
        label: "ModExp bounds",
        subtitle: "approximation control",
        kind: "algorithm",
        view: "modexp",
        file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/ModExpBounds.lean",
        declarations: ["modExpSteps_dist_bound", "modExp_dist_bound", "modExp_overlap_bound_sqrt"],
        summary:
          "Packages quantitative norm-distance and overlap bounds for approximate modular exponentiation."
      },
      {
        id: "classical",
        label: "Classical reduction",
        subtitle: "order finding to factoring",
        kind: "math",
        view: "classical",
        file: "FastMultiplication/ShorVerification/MathBackBone/Factoring_Reduction",
        declarations: ["shors_classical_reduction", "shors_probability_bound"],
        summary:
          "Contains the number-theoretic reduction and probability arguments that connect successful order finding to nontrivial factors."
      },
      {
        id: "shor",
        label: "Shor correctness",
        subtitle: "end-to-end theorem",
        kind: "final",
        view: "shor",
        file: "FastMultiplication/ShorVerification/ShorCorrectness.lean",
        declarations: ["Shor_correct", "Shor_correct_approx", "Shor_end_to_end_factoring"],
        summary:
          "Combines ideal/approximate order-finding circuits, measurement probabilities, approximation control, and classical reduction into the top-level statements."
      }
    ],
    links: [
      { source: "table", target: "phase", label: "coverage theorem" },
      { source: "toom", target: "phase", label: "interpolation proof" },
      { source: "basic", target: "phase", label: "gate semantics" },
      { source: "basic", target: "qft", label: "QFT semantics" },
      { source: "phase", target: "qft", label: "phase product identity" },
      { source: "phase", target: "machine", label: "lower phase products" },
      { source: "qft", target: "machine", label: "lower QFT" },
      { source: "machine", target: "shor", label: "exact lowering" },
      { source: "modexp", target: "shor", label: "approx bounds" },
      { source: "classical", target: "shor", label: "factor recovery" },
      { source: "basic", target: "modexp", label: "norm facts" }
    ]
  },

  basic: {
    title: "Basic semantics",
    subtitle: "The common proof substrate",
    description:
      "This layer defines the abstract objects later proofs manipulate: registers, extended registers, gates, semantic interfaces, and reusable evaluation lemmas.",
    parent: "overview",
    nodes: [
      { id: "reg", label: "Reg", subtitle: "ordinary intervals", kind: "core", file: "FastMultiplication/ShorVerification/Basic.lean", declarations: ["Reg", "regSize", "ASize", "splitLeft", "splitRight"], summary: "Ordinary finite registers and interval/splitting facts." },
      { id: "regenc", label: "RegEncoding", subtitle: "basis read/write", kind: "core", file: "FastMultiplication/ShorVerification/Basic.lean", declarations: ["RegEncoding", "writeNat_comm_of_disjoint"], summary: "Basis-level interface for reading, writing, and proving register locality." },
      { id: "extreg", label: "ExtReg", subtitle: "signed widths", kind: "core", file: "FastMultiplication/ShorVerification/Basic.lean", declarations: ["ExtReg", "ExtRegEncoding", "tcDecodeWidth", "FitsSignedWidth"], summary: "Extended-register interpretation and two's-complement support." },
      { id: "gate", label: "Gate", subtitle: "high-level syntax", kind: "core", file: "FastMultiplication/ShorVerification/Basic.lean", declarations: ["Gate", "PhaseProd", "CPhaseProd"], summary: "High-level gate syntax and derived gate macros." },
      { id: "sem", label: "QSemantics", subtitle: "evaluation model", kind: "core", file: "FastMultiplication/ShorVerification/Basic.lean", declarations: ["QSemantics", "QFTSemantics", "PhaseSemantics", "ArithmeticSemantics"], summary: "Abstract semantic interfaces for evaluating gates on quantum states." },
      { id: "facts", label: "Semantic facts", subtitle: "ket and norm lemmas", kind: "core", file: "FastMultiplication/ShorVerification/Basic.lean", declarations: ["eval_RadixReverse_split_ket", "eval_PhaseProd_ket", "eval_isometry", "eval_norm_preserved"], summary: "Reusable facts that later correctness proofs invoke instead of reopening semantics." }
    ],
    links: [
      { source: "reg", target: "regenc", label: "read/write laws" },
      { source: "reg", target: "extreg", label: "signed views" },
      { source: "reg", target: "gate", label: "gate operands" },
      { source: "gate", target: "sem", label: "eval interface" },
      { source: "regenc", target: "sem", label: "basis laws" },
      { source: "extreg", target: "facts", label: "phase semantics" },
      { source: "sem", target: "facts", label: "proof lemmas" }
    ]
  },

  table: {
    title: "Table generation",
    subtitle: "Symbolic programs to phase coverage",
    description:
      "This subgraph follows the source-program side of the project: define a symbolic language, synthesize operations, prove execution properties, then package phase-point coverage.",
    parent: "overview",
    nodes: [
      { id: "tg-basic", label: "Basic", subtitle: "symbolic states", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Basic.lean", declarations: ["Register", "State", "shiftL", "shiftR", "addScaledReg"], summary: "Core symbolic register operations." },
      { id: "language", label: "Language", subtitle: "Prog and run?", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Language.lean", declarations: ["Prog", "applyOp?", "run?", "PhaseProductCoverage"], summary: "Turns symbolic operations into executable source programs and coverage predicates." },
      { id: "basic-lemmas", label: "Basic lemmas", subtitle: "execution algebra", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Basic_lemmas.lean", declarations: ["run?_append", "run?_inverse_undoes_WF"], summary: "Reusable program execution and inverse lemmas." },
      { id: "synthesis", label: "Synthesis", subtitle: "generated programs", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Synthesis_programs.lean", declarations: ["opsForPointWithProduct", "genOpsWithProduct", "run_some_computeLocalAux"], summary: "Defines source programs that generate the required phase-point behavior." },
      { id: "combined", label: "Combined proof", subtitle: "coverage endpoint", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Table_Generation/One_register_synthesis_combined.lean", declarations: ["opsForPointWithProduct_returns_to_original", "genOpsWithProduct_returns_to_original", "genOpsWithProduct_PhaseProductCoverage"], summary: "Proves the generated programs return state and satisfy phase-product coverage." },
      { id: "blocks", label: "Table blocks", subtitle: "block decomposition", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Table_Blocks.lean", declarations: ["progConsumesPts_has_blockDecomposition", "progConsumesPts_implies_phaseProductCoverage", "phaseProductCoverage_peel_block"], summary: "Repackages coverage into phase blocks for the compiler proof." }
    ],
    links: [
      { source: "tg-basic", target: "language", label: "ops become Prog" },
      { source: "language", target: "basic-lemmas", label: "run? facts" },
      { source: "basic-lemmas", target: "synthesis", label: "execution support" },
      { source: "synthesis", target: "combined", label: "generated ops" },
      { source: "combined", target: "blocks", label: "coverage proof" }
    ]
  },

  phase: {
    title: "Phase-product correctness",
    subtitle: "Compiler proof assembly",
    description:
      "The phase-product proof turns source-level coverage and Toom-Cook interpolation into a semantic correctness theorem for compiled signed phase-product gates.",
    parent: "overview",
    nodes: [
      { id: "core", label: "Core", subtitle: "layouts and annotations", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/PhaseProduct/Core.lean", declarations: ["SignedLayout", "EncodedState", "compileOpsToSignedGate"], summary: "Defines compiler bookkeeping, layouts, annotations, and encoded states." },
      { id: "support", label: "Support lemmas", subtitle: "row and layout facts", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/PhaseProduct/SupportLemmas.lean", declarations: ["splitExtReg_reconstruct_int", "annotatePhaseTermsAux_append"], summary: "Collects facts used by width, allocation, body, and interpolation proofs." },
      { id: "width", label: "Width soundness", subtitle: "allocated widths", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/PhaseProduct/WidthSoundness.lean", declarations: ["allocated_widths_sound"], summary: "Shows extracted width bookkeeping remains sound across symbolic execution." },
      { id: "alloc", label: "Allocation", subtitle: "basis into layout", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/PhaseProduct/AllocationCorrectness.lean", declarations: ["eval_compileSignedAllocations_ket", "eval_compileSignedAllocations_ket_fits"], summary: "Proves allocation puts basis states into the intended widened encoded form." },
      { id: "body", label: "Body/deallocation", subtitle: "compiled ops", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/PhaseProduct/BodyCorrectness.lean", declarations: ["eval_compileAnnotatedOpsToSignedGateAux_of_blocks", "eval_compileSignedDeallocations_ket", "eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc"], summary: "Proves the semantic behavior of compiled annotated operations and deallocation." },
      { id: "interp", label: "Interpolation", subtitle: "phase scalar equality", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/PhaseProduct/InterpolationCorrectness.lean", declarations: ["toom_cook_interpolation"], summary: "Converts accumulated point phases into the target signed phase-product scalar." },
      { id: "compile", label: "Compilation", subtitle: "main theorem", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/PhaseProduct/CompilationCorrectness.lean", declarations: ["eval_compileOpsToSignedGate_correct"], summary: "Assembles allocation, body/deallocation, and interpolation into the compiler correctness theorem." }
    ],
    links: [
      { source: "core", target: "support", label: "definitions" },
      { source: "support", target: "width", label: "layout facts" },
      { source: "width", target: "alloc", label: "fits widths" },
      { source: "alloc", target: "body", label: "encoded start" },
      { source: "support", target: "interp", label: "row facts" },
      { source: "body", target: "compile", label: "compiled semantics" },
      { source: "interp", target: "compile", label: "phase equality" }
    ]
  },

  toom: {
    title: "Toom-Cook algebra",
    subtitle: "Interpolation support",
    description:
      "This layer is mostly independent algebra. The compiler correctness proof consumes it through `toom_cook_interpolation`.",
    parent: "overview",
    nodes: [
      { id: "points", label: "Good points", subtitle: "interpolation hypotheses", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Toom_Cook_formula.lean", declarations: ["GoodInterpolationPoints", "GoodToomCookPoints"], summary: "Packages the assumptions required for nonsingular interpolation." },
      { id: "matrix", label: "Matrix facts", subtitle: "coefficients", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Toom_Cook_formula.lean", declarations: ["interpCoeff", "interpEntry"], summary: "Defines the interpolation matrix and coefficient accessors." },
      { id: "radix", label: "Radix evaluation", subtitle: "chunk reconstruction", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Toom_Cook_formula.lean", declarations: ["evalAtRadix"], summary: "Relates coefficient lists and radix/chunk evaluation." },
      { id: "tc-proof", label: "Compiler bridge", subtitle: "toom_cook_interpolation", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/PhaseProduct/InterpolationCorrectness.lean", declarations: ["toom_cook_interpolation"], summary: "The algorithm layer's theorem that applies Toom-Cook algebra to phase scalars." }
    ],
    links: [
      { source: "points", target: "matrix", label: "nonsingularity" },
      { source: "matrix", target: "radix", label: "coefficients" },
      { source: "radix", target: "tc-proof", label: "reconstruction" },
      { source: "points", target: "tc-proof", label: "good point class" }
    ]
  },

  qft: {
    title: "QFT decomposition",
    subtitle: "High-level split identity",
    description:
      "The QFT branch proves a semantic identity at the high-level gate layer, then the abstract machine lowering proof uses that identity recursively.",
    parent: "overview",
    nodes: [
      { id: "qft-sem", label: "QFT semantics", subtitle: "Basic.lean classes", kind: "core", file: "FastMultiplication/ShorVerification/Basic.lean", declarations: ["QFTSemantics", "RadixReverseSemantics", "PhaseSemantics"], summary: "Semantic interfaces required to reason about QFT and phase-product gates." },
      { id: "split", label: "Split registers", subtitle: "left/right decomposition", kind: "core", file: "FastMultiplication/ShorVerification/Basic.lean", declarations: ["splitLeft", "splitRight", "eval_RadixReverse_split_ket"], summary: "Register decomposition and radix-reversal facts." },
      { id: "phase-id", label: "Phase product", subtitle: "cross terms", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/QFT/Decomposition.lean", declarations: ["eval_QFT_split"], summary: "The split QFT identity uses a phase product to represent cross terms." },
      { id: "eval", label: "eval_QFT_split", subtitle: "decomposition theorem", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/QFT/Decomposition.lean", declarations: ["eval_QFT_split"], summary: "Main high-level QFT decomposition theorem." }
    ],
    links: [
      { source: "qft-sem", target: "split", label: "semantic facts" },
      { source: "split", target: "phase-id", label: "register halves" },
      { source: "phase-id", target: "eval", label: "cross-term proof" }
    ]
  },

  machine: {
    title: "Abstract machine",
    subtitle: "Lowering high-level gates",
    description:
      "The lowering branch defines a low-level gate language and proves that lowering preserves the high-level semantics under geometry side conditions.",
    parent: "overview",
    nodes: [
      { id: "lowgate", label: "LowGate", subtitle: "target language", kind: "machine", file: "FastMultiplication/ShorVerification/AbstractMachine/LowGate.lean", declarations: ["LowGate"], summary: "Defines the low-level target gate syntax." },
      { id: "phase-lower", label: "Phase lowering", subtitle: "phase products", kind: "machine", file: "FastMultiplication/ShorVerification/AbstractMachine/PhaseProductLoweringCorrectness.lean", declarations: ["eval_lowerPhaseProd"], summary: "Correctness theorem for lowered phase-product operations." },
      { id: "qft-lower", label: "QFT lowering", subtitle: "recursive QFT", kind: "machine", file: "FastMultiplication/ShorVerification/AbstractMachine/QFTLoweringCorrectness.lean", declarations: ["lowerQFTAux", "eval_lowerQFT", "evalL_lowerPhaseProd"], summary: "Uses the high-level QFT split identity and the phase-product lowering theorem for the middle phase-product in the recursive QFT decomposition." },
      { id: "whole", label: "Whole program", subtitle: "lowerGate_correctness", kind: "machine", file: "FastMultiplication/ShorVerification/AbstractMachine/WholeProgramCorrectness.lean", declarations: ["GateGeomOK", "lowerGate_correctness"], summary: "Proves lowering correctness for full high-level Gate programs." }
    ],
    links: [
      { source: "lowgate", target: "phase-lower", label: "target semantics" },
      { source: "lowgate", target: "qft-lower", label: "target semantics" },
      { source: "phase-lower", target: "qft-lower", label: "lowers split phase product" },
      { source: "phase-lower", target: "whole", label: "recursive case" },
      { source: "qft-lower", target: "whole", label: "recursive case" }
    ]
  },

  modexp: {
    title: "ModExp bounds",
    subtitle: "Approximate modular exponentiation",
    description:
      "This branch controls the distance between approximate and ideal modular exponentiation, then packages that as an overlap bound for Shor correctness.",
    parent: "overview",
    nodes: [
      { id: "spec", label: "Spec and gates", subtitle: "ideal/approx interface", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/ModExpBounds.lean", declarations: ["Spec", "ModMul", "modExpIdealSteps", "modExpIdeal'"], summary: "Defines the specification classes and ideal/approximate modular exponentiation gates." },
      { id: "local", label: "Step bound", subtitle: "single multiply", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/ModExpBounds.lean", declarations: ["ctrlMul_step_dist_bound"], summary: "Controls the error for one controlled multiplication step." },
      { id: "steps", label: "Steps bound", subtitle: "iterated distance", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/ModExpBounds.lean", declarations: ["modExpSteps_dist_bound"], summary: "Lifts local step error to the iterated modular exponentiation loop." },
      { id: "dist", label: "Circuit distance", subtitle: "modExp_dist_bound", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/ModExpBounds.lean", declarations: ["modExp_dist_bound"], summary: "Packages the full approximate-vs-ideal distance bound." },
      { id: "overlap", label: "Overlap", subtitle: "success transfer", kind: "algorithm", file: "FastMultiplication/ShorVerification/AlgorithmCorrectness/ModExpBounds.lean", declarations: ["modExp_overlap_bound_sqrt"], summary: "Converts norm-distance control into an overlap-style bound for the final theorem." }
    ],
    links: [
      { source: "spec", target: "local", label: "error model" },
      { source: "local", target: "steps", label: "iteration" },
      { source: "steps", target: "dist", label: "whole gate" },
      { source: "dist", target: "overlap", label: "overlap lemma" }
    ]
  },

  classical: {
    title: "Classical reduction",
    subtitle: "Order finding to factoring",
    description:
      "The classical branch models successful choices of `a`, order recovery, and the reduction from a good order to a nontrivial factor.",
    parent: "overview",
    nodes: [
      { id: "defs", label: "Definitions", subtitle: "success predicates", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Factoring_Reduction/Defs.lean", declarations: ["valid_choices", "successful_choices", "is_successful_choice"], summary: "Defines the classical sets and predicates used by the factoring theorem." },
      { id: "prob", label: "Probability bound", subtitle: "successful choices", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Factoring_Reduction/ProbabilityBound.lean", declarations: ["valid_choices_card_general", "general_unsuccessful_bound"], summary: "Counts successful choices among coprime residues." },
      { id: "reduction", label: "Reduction", subtitle: "gcd factors", kind: "math", file: "FastMultiplication/ShorVerification/MathBackBone/Factoring_Reduction/Reduction.lean", declarations: ["shors_classical_reduction"], summary: "Shows good order information yields a nontrivial factor." },
      { id: "bound", label: "Shor probability", subtitle: "repo theorem", kind: "final", file: "FastMultiplication/ShorVerification/ShorCorrectness.lean", declarations: ["shors_probability_bound"], summary: "Top-level use of the classical counting theorem." }
    ],
    links: [
      { source: "defs", target: "prob", label: "finite sets" },
      { source: "defs", target: "reduction", label: "success conditions" },
      { source: "prob", target: "bound", label: "counting theorem" },
      { source: "reduction", target: "bound", label: "factor theorem" }
    ]
  },

  shor: {
    title: "Shor correctness",
    subtitle: "Final assembly",
    description:
      "`ShorCorrectness.lean` defines order-finding circuits and measurement probabilities, then states ideal, approximate, and end-to-end factoring theorems.",
    parent: "overview",
    nodes: [
      { id: "circuits", label: "Order-finding circuits", subtitle: "ideal and approximate", kind: "final", file: "FastMultiplication/ShorVerification/ShorCorrectness.lean", declarations: ["initY1", "orderFindingApprox", "orderFindingIdeal"], summary: "Assembles H, initialization, modular exponentiation, and QFT into order-finding gates." },
      { id: "measure", label: "Measurement model", subtitle: "success probability", kind: "final", file: "FastMultiplication/ShorVerification/ShorCorrectness.lean", declarations: ["MeasureClass", "measProbAfter", "successProbAfterFinset", "probability_of_success"], summary: "Abstracts measurement and packages success probabilities." },
      { id: "ideal", label: "Ideal theorem", subtitle: "Shor_correct", kind: "final", file: "FastMultiplication/ShorVerification/ShorCorrectness.lean", declarations: ["Shor_correct"], summary: "States the ideal order-finding correctness lower bound." },
      { id: "approx", label: "Approx theorem", subtitle: "Shor_correct_approx", kind: "final", file: "FastMultiplication/ShorVerification/ShorCorrectness.lean", declarations: ["Shor_correct_approx"], summary: "States the approximation-aware order-finding lower bound." },
      { id: "factoring", label: "End-to-end factoring", subtitle: "Shor_end_to_end_factoring", kind: "final", file: "FastMultiplication/ShorVerification/ShorCorrectness.lean", declarations: ["Shor_end_to_end_factoring"], summary: "Combines classical choice probability and quantum order finding into a factoring statement." }
    ],
    links: [
      { source: "circuits", target: "measure", label: "run and measure" },
      { source: "measure", target: "ideal", label: "success expression" },
      { source: "ideal", target: "approx", label: "ideal baseline" },
      { source: "ideal", target: "factoring", label: "order finding" },
      { source: "measure", target: "factoring", label: "probability API" }
    ]
  }
};

const state = {
  viewId: "overview",
  selectedId: null,
  selectedEdge: null,
  focusMode: true,
  query: "",
  transform: { x: 0, y: 0, scale: 1 },
  dragging: null,
  panning: null,
  positions: new Map(),
  positionsViewId: null
};

const svg = document.getElementById("graph");
const viewList = document.getElementById("viewList");
const detailsContent = document.getElementById("detailsContent");
const breadcrumb = document.getElementById("breadcrumb");
const searchInput = document.getElementById("searchInput");
const fitButton = document.getElementById("fitButton");
const resetButton = document.getElementById("resetButton");
const focusToggleButton = document.getElementById("focusToggleButton");
const zoomInButton = document.getElementById("zoomInButton");
const zoomOutButton = document.getElementById("zoomOutButton");
const viewSubtitle = document.getElementById("viewSubtitle");
const viewDescription = document.getElementById("viewDescription");
const graphStats = document.getElementById("graphStats");
const legend = document.getElementById("legend");
const emptyState = document.getElementById("emptyState");

const ns = "http://www.w3.org/2000/svg";
const nodeWidth = 214;
const nodeHeight = 98;
const githubRepoUrl = "https://github.com/VerifiedQC/ForShor";
const githubBranch = "main";
const kindLabels = {
  core: "Semantic core",
  math: "Math backbone",
  algorithm: "Algorithm proof",
  machine: "Lowering",
  final: "Final assembly"
};
const kindColors = {
  core: "#2368b8",
  math: "#218263",
  algorithm: "#b46519",
  machine: "#6d55b8",
  final: "#be3f50"
};

const edgeCatalog = {
  "coverage theorem": {
    theorem: "genOpsWithProduct_PhaseProductCoverage",
    description: "Shows that the generated symbolic source program consumes exactly the interpolation phase points required by the later phase-product compiler.",
    proof: "The proof comes from the table-generation synthesis chain: generated operations are shown to return the symbolic state to its original form while preserving the phase-point coverage invariant."
  },
  "interpolation proof": {
    theorem: "toom_cook_interpolation",
    description: "Turns the accumulated phase contributions at Toom-Cook interpolation points into the intended signed phase-product scalar.",
    proof: "The proof uses the interpolation matrix and radix-evaluation lemmas from the Toom-Cook algebra layer, then specializes them to the compiler's phase-scalar bookkeeping."
  },
  "gate semantics": {
    theorem: "eval_PhaseProd_ket",
    description: "Connects the abstract gate semantics to the ket-level behavior that phase-product correctness statements reason about.",
    proof: "The core semantic facts in Basic.lean expose phase-product evaluation as a reusable theorem, so the compiler proof can use semantics without reopening the model."
  },
  "QFT semantics": {
    theorem: "QFTSemantics.eval_QFT_size0/1",
    description: "Provides the semantic base cases and interfaces needed by the QFT decomposition and lowering proofs.",
    proof: "The QFT proofs depend on the abstract QFT semantic class and its small-register facts before applying the recursive split theorem."
  },
  "phase product identity": {
    theorem: "eval_QFT_split",
    description: "Identifies the phase product that appears between the two recursive QFT calls in the split QFT circuit.",
    proof: "The theorem rewrites QFT over a register into right-QFT, phase product, left-QFT, and radix reversal."
  },
  "lower phase products": {
    theorem: "evalL_lowerPhaseProd",
    description: "Proves that the low-level lowering of a high-level phase product preserves the high-level semantics.",
    proof: "The proof invokes the phase-product compiler correctness theorem and the recursive low-level lowering semantics."
  },
  "lower QFT": {
    theorem: "eval_lowerQFT",
    description: "Proves that the recursive low-level QFT lowering has the same semantics as high-level Gate.QFT.",
    proof: "The proof uses eval_QFT_split and, for the middle split phase product, calls evalL_lowerPhaseProd."
  },
  "exact lowering": {
    theorem: "lowerGate_correctness",
    description: "Lifts phase-product and QFT lowering correctness to arbitrary geometrically well-formed high-level Gate programs.",
    proof: "The proof is by induction over Gate syntax, dispatching QFT and signed phase-product cases to their specialized lowering theorems."
  },
  "approx bounds": {
    theorem: "modExp_overlap_bound_sqrt",
    description: "Transfers approximate modular-exponentiation error into an overlap-style bound usable by the final Shor statement.",
    proof: "The proof packages per-step distance bounds into a whole-circuit distance theorem and then converts distance control into overlap control."
  },
  "factor recovery": {
    theorem: "shors_classical_reduction",
    description: "Connects successful order recovery to extracting a nontrivial factor with a gcd computation.",
    proof: "The proof uses the classical Shor success conditions to show one of the standard gcd candidates yields a nontrivial divisor."
  },
  "norm facts": {
    theorem: "eval_norm_preserved",
    description: "Supplies the norm-preservation facts needed when modular-exponentiation approximation bounds are composed.",
    proof: "The semantic core proves evaluation is isometric, allowing later distance and overlap arguments to control circuit errors."
  },
  "read/write laws": {
    theorem: "writeNat_comm_of_disjoint",
    description: "Shows that writes to disjoint registers commute, which is a basic locality fact for register reasoning.",
    proof: "The proof uses the RegEncoding bit-level locality axioms and basis extensionality."
  },
  "signed views": {
    theorem: "zeroExtend_extToInt",
    description: "Relates ordinary register data to extended signed-register interpretation.",
    proof: "The proof unfolds the two's-complement decoding interface and records how extension operations preserve integer meaning."
  },
  "gate operands": {
    theorem: "Gate.PhaseProd",
    description: "Builds phase-product gate syntax from register operands and extended unsigned views.",
    proof: "This is a definitional bridge from register structures to high-level gate constructors."
  },
  "eval interface": {
    theorem: "QSemantics.eval",
    description: "Moves from syntactic Gate values to their abstract action on quantum states.",
    proof: "The semantic interface supplies evaluation and composition laws used by every later circuit proof."
  },
  "basis laws": {
    theorem: "toNat_left_write_right",
    description: "States that writing one side of a disjoint split preserves the other side's numeric interpretation.",
    proof: "The proof instantiates RegEncoding locality on the split-register geometry."
  },
  "phase semantics": {
    theorem: "eval_PhaseProd_ket",
    description: "Gives the ket-level behavior of phase-product gates.",
    proof: "This theorem packages the PhaseSemantics class into a form suitable for downstream compiler proofs."
  },
  "proof lemmas": {
    theorem: "eval_norm_preserved",
    description: "Records that gate evaluation preserves norm.",
    proof: "The proof follows from the semantic isometry theorem."
  },
  "ops become Prog": {
    theorem: "run?",
    description: "Defines whole-program execution for symbolic operations.",
    proof: "The language layer folds single-step operation semantics into the executable program interpreter."
  },
  "run? facts": {
    theorem: "run?_append",
    description: "Shows how execution distributes over appended symbolic programs.",
    proof: "The proof follows the list structure of Prog execution and is used to reason compositionally about generated programs."
  },
  "execution support": {
    theorem: "run_some_computeLocalAux",
    description: "Shows that key synthesized local computations execute successfully.",
    proof: "The synthesis proofs use the execution lemmas to establish successful runs for generated helper programs."
  },
  "generated ops": {
    theorem: "opsForPointWithProduct_returns_to_original",
    description: "Shows generated operations for an interpolation point restore the symbolic state after doing the needed work.",
    proof: "The proof follows the generated operation sequence and tracks how each symbolic register is restored."
  },
  "coverage proof": {
    theorem: "progConsumesPts_has_blockDecomposition",
    description: "Packages phase-point consumption into a block decomposition for the compiler proof.",
    proof: "The proof converts coverage of the generated program into block-level structure with clean phase interfaces."
  },
  "definitions": {
    theorem: "compileOpsToSignedGate",
    description: "Introduces the compiler object whose correctness is proved by the later phase-product modules.",
    proof: "This is a definitional edge: later proofs consume the layout and annotated-operation definitions introduced here."
  },
  "layout facts": {
    theorem: "allocated_widths_sound",
    description: "Proves width bookkeeping remains sound throughout symbolic execution.",
    proof: "The proof uses support lemmas about layouts, split extended registers, and generated rows."
  },
  "fits widths": {
    theorem: "eval_compileSignedAllocations_ket_fits",
    description: "Shows allocation creates an encoded state that fits the computed signed widths.",
    proof: "The allocation proof combines width soundness with ket-level allocation semantics."
  },
  "encoded start": {
    theorem: "eval_compileAnnotatedOpsToSignedGateAux_of_blocks",
    description: "Runs the compiled operation body from the allocated encoded state.",
    proof: "The proof walks through block-structured annotated operations while preserving the encoded-state invariant."
  },
  "row facts": {
    theorem: "expectedRow_mul_expectedRow_eq_interpEntry",
    description: "Relates compiler row bookkeeping to interpolation matrix entries.",
    proof: "The proof is one of the algebraic bridges used before the final Toom-Cook phase-scalar equality."
  },
  "compiled semantics": {
    theorem: "eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc",
    description: "Combines the compiled body with deallocation to return to the intended output layout.",
    proof: "The proof composes body correctness with deallocation cancellation lemmas."
  },
  "phase equality": {
    theorem: "eval_compileOpsToSignedGate_correct",
    description: "Assembles interpolation equality with compiled circuit semantics into the main compiler theorem.",
    proof: "Compilation correctness combines allocation, body/deallocation, and toom_cook_interpolation."
  },
  "nonsingularity": {
    theorem: "GoodToomCookPoints.to_GoodInterpolationPoints",
    description: "Converts good Toom-Cook point assumptions into the interpolation hypotheses needed downstream.",
    proof: "The proof packages the point assumptions into the generic good-interpolation interface."
  },
  "coefficients": {
    theorem: "phaseCoeffFromPtsWidth_eq_interpCoeff",
    description: "Relates phase-coefficient extraction to interpolation coefficients.",
    proof: "The proof unfolds the coefficient definitions and aligns compiler indexing with interpolation indexing."
  },
  "reconstruction": {
    theorem: "evalAtRadix_tcProductCoeff_eq_ext_product",
    description: "Reconstructs the product value from Toom-Cook coefficient evaluation.",
    proof: "The proof combines chunk reconstruction lemmas for the source operands."
  },
  "good point class": {
    theorem: "GoodToomCookPoints.to_GoodInterpolationPoints",
    description: "Supplies the good-point hypothesis used by the compiler bridge theorem.",
    proof: "The proof is a typeclass/interface conversion between the Toom-Cook and interpolation layers."
  },
  "semantic facts": {
    theorem: "eval_RadixReverse_split_ket",
    description: "Provides register-split semantic facts used inside the QFT split proof.",
    proof: "The proof comes from the core semantics of radix reversal on split registers."
  },
  "register halves": {
    theorem: "splitLeft_splitRight_disjoint",
    description: "Proves the left and right halves of a split register are disjoint.",
    proof: "The proof is arithmetic over register intervals."
  },
  "cross-term proof": {
    theorem: "eval_QFT_split",
    description: "Proves the cross terms in the QFT split are exactly represented by a phase product.",
    proof: "The proof expands the QFT split structure and matches the phase contribution."
  },
  "target semantics": {
    theorem: "LowerGateClass.evalL",
    description: "Provides the semantic interface for evaluating LowGate programs.",
    proof: "The low-level correctness theorems are stated by comparing evalL of lowered LowGate programs with high-level Gate evaluation."
  },
  "lowers split phase product": {
    theorem: "evalL_lowerPhaseProd",
    description: "Supplies the phase-product lowering theorem used inside recursive QFT lowering.",
    proof: "In eval_lowerQFTAux_strong, the proof rewrites the lowered middle phase product using evalL_lowerPhaseProd."
  },
  "recursive case": {
    theorem: "lowerGate_correctness",
    description: "Uses the specialized lowering theorem as one recursive case of whole-program lowering.",
    proof: "The whole-program theorem inducts over Gate syntax and dispatches each constructor to its matching semantic lemma."
  },
  "error model": {
    theorem: "ctrlMul_step_dist_bound",
    description: "Introduces the local controlled-multiplication error bound.",
    proof: "The proof applies the ModMul specification to a single modular multiplication step."
  },
  "iteration": {
    theorem: "modExpSteps_dist_bound",
    description: "Lifts the local step error over the modular-exponentiation loop.",
    proof: "The proof accumulates stepwise norm-distance errors across the iteration."
  },
  "whole gate": {
    theorem: "modExp_dist_bound",
    description: "Packages the iterated step bound as a statement about the whole modular-exponentiation gate.",
    proof: "The proof specializes the step theorem to the full circuit wrapper."
  },
  "overlap lemma": {
    theorem: "modExp_overlap_bound_sqrt",
    description: "Converts modular-exponentiation distance control into overlap control.",
    proof: "The proof applies the distance-to-overlap lemmas from the same file."
  },
  "finite sets": {
    theorem: "valid_choices_card_general",
    description: "Counts the valid choices of bases used in the classical reduction.",
    proof: "The proof unfolds the finite set of coprime residues and relates it to Euler's totient."
  },
  "success conditions": {
    theorem: "shors_classical_reduction",
    description: "Uses the success predicate to derive a nontrivial factor from the recovered order.",
    proof: "The proof applies the standard Shor gcd identities under the success-condition hypotheses."
  },
  "counting theorem": {
    theorem: "shors_probability_bound",
    description: "Shows that at least half of the valid choices are successful under the classical assumptions.",
    proof: "The proof combines the unsuccessful-choice bound with the partition of valid choices."
  },
  "factor theorem": {
    theorem: "Shor_end_to_end_factoring",
    description: "Feeds the classical factor-recovery theorem into the end-to-end factoring statement.",
    proof: "The final theorem combines the classical reduction with the quantum order-finding success theorem."
  },
  "run and measure": {
    theorem: "measProbAfter",
    description: "Defines the probability of a measurement outcome after running an order-finding circuit.",
    proof: "This is the definitional bridge from circuits to measurement probabilities."
  },
  "success expression": {
    theorem: "probability_of_success",
    description: "Packages measurement probabilities into the success expression used by Shor correctness.",
    proof: "The definition sums over measurement outcomes weighted by the continued-fraction verifier."
  },
  "ideal baseline": {
    theorem: "Shor_correct_approx",
    description: "Uses the ideal theorem as the baseline for the approximation-aware statement.",
    proof: "The approximate theorem subtracts an explicit modular-exponentiation error term from the ideal success lower bound."
  },
  "order finding": {
    theorem: "Shor_end_to_end_factoring",
    description: "Feeds ideal order-finding correctness into the end-to-end factoring theorem.",
    proof: "The end-to-end theorem invokes Shor_correct for every successful choice of base."
  },
  "probability API": {
    theorem: "successProbAfterFinset_mono",
    description: "Provides basic monotonicity and range facts for success probabilities.",
    proof: "The proof uses nonnegativity of measurement probabilities and finite-set summation facts."
  }
};

let viewport = { width: 900, height: 640 };
let scene;
let didDrag = false;
let pendingNodeClick = null;

function make(tag, attrs = {}, parent = null) {
  const el = document.createElementNS(ns, tag);
  Object.entries(attrs).forEach(([key, value]) => el.setAttribute(key, value));
  if (parent) parent.appendChild(el);
  return el;
}

function fileHref(file) {
  if (!file || file.includes("://")) return file;
  const githubView = file.includes(".") ? "blob" : "tree";
  return `${githubRepoUrl}/${githubView}/${githubBranch}/${file.split("/").map(encodeURIComponent).join("/")}`;
}

function nodeMatches(node, query) {
  if (!query) return true;
  const haystack = [node.label, node.subtitle, node.summary, node.file, ...(node.declarations || [])]
    .join(" ")
    .toLowerCase();
  return haystack.includes(query.toLowerCase());
}

function linkTouches(link, selectedId) {
  return link.source === selectedId || link.target === selectedId;
}

function edgeKey(link) {
  return `${link.source}->${link.target}:${link.label}`;
}

function getViewKinds(view) {
  return [...new Set(view.nodes.map((node) => node.kind || "core"))];
}

function getDominantKind(view) {
  const counts = new Map();
  view.nodes.forEach((node) => counts.set(node.kind, (counts.get(node.kind) || 0) + 1));
  return [...counts.entries()].sort((a, b) => b[1] - a[1])[0]?.[0] || "core";
}

function getNode(id) {
  return graphData[state.viewId].nodes.find((node) => node.id === id);
}

function getRelatedEdges(id) {
  const view = graphData[state.viewId];
  return {
    incoming: view.links.filter((link) => link.target === id),
    outgoing: view.links.filter((link) => link.source === id)
  };
}

function getEdgeInfo(link) {
  const catalogEntry = edgeCatalog[link.label] || {};
  return {
    theorem: link.theorem || catalogEntry.theorem || link.label,
    description: link.description || catalogEntry.description || `This proof edge connects ${link.source} to ${link.target}.`,
    proof: link.proof || catalogEntry.proof || "This edge is a curated dependency bridge in the proof architecture.",
    relation: link.label
  };
}

function getNodeProfile(node, view) {
  const related = getRelatedEdges(node.id);
  const endpoints = node.declarations?.slice(-2).join(", ") || "the module declarations";
  const incoming = related.incoming.length
    ? `It consumes ${related.incoming.length} upstream proof bridge${related.incoming.length === 1 ? "" : "s"}.`
    : "It is an entry point for this graph layer.";
  const outgoing = related.outgoing.length
    ? `It feeds ${related.outgoing.length} downstream proof bridge${related.outgoing.length === 1 ? "" : "s"}.`
    : "It is an endpoint of this graph layer.";

  return {
    role: node.summary || view.description,
    why:
      `${incoming} ${outgoing} The main things to look for here are ${endpoints}.`
  };
}

function topologicalLevels(view) {
  const indegree = new Map(view.nodes.map((node) => [node.id, 0]));
  view.links.forEach((link) => indegree.set(link.target, (indegree.get(link.target) || 0) + 1));
  const queue = [...indegree.entries()].filter(([, degree]) => degree === 0).map(([id]) => id);
  const level = new Map(queue.map((id) => [id, 0]));

  while (queue.length) {
    const id = queue.shift();
    const current = level.get(id) || 0;
    view.links.filter((link) => link.source === id).forEach((link) => {
      level.set(link.target, Math.max(level.get(link.target) || 0, current + 1));
      indegree.set(link.target, indegree.get(link.target) - 1);
      if (indegree.get(link.target) === 0) queue.push(link.target);
    });
  }

  view.nodes.forEach((node) => {
    if (!level.has(node.id)) level.set(node.id, 0);
  });
  return level;
}

function layout(view) {
  const levels = topologicalLevels(view);
  const groups = new Map();
  view.nodes.forEach((node) => {
    const level = levels.get(node.id) || 0;
    if (!groups.has(level)) groups.set(level, []);
    groups.get(level).push(node);
  });

  const levelCount = Math.max(1, groups.size);
  const minGap = viewport.width < 760 ? 330 : 420;
  const xGap = Math.max(minGap, (viewport.width - 160) / Math.max(1, levelCount - 1));
  const nextPositions = new Map();

  [...groups.entries()].sort((a, b) => a[0] - b[0]).forEach(([level, nodes]) => {
    const minVerticalGap = viewport.width < 760 ? 250 : 285;
    const yGap = Math.max(minVerticalGap, (viewport.height - 130) / Math.max(1, nodes.length));
    nodes.forEach((node, index) => {
      const x = 90 + level * xGap;
      const y = Math.max(90, (viewport.height - yGap * (nodes.length - 1)) / 2 + index * yGap);
      nextPositions.set(node.id, { x, y });
    });
  });

  state.positions = nextPositions;
  state.positionsViewId = state.viewId;
}

function applyTransform() {
  scene.setAttribute("transform", `translate(${state.transform.x} ${state.transform.y}) scale(${state.transform.scale})`);
}

function setScale(nextScale, center = null) {
  const oldScale = state.transform.scale;
  const scale = Math.min(1.9, Math.max(0.38, nextScale));
  const cx = center?.x ?? viewport.width / 2;
  const cy = center?.y ?? viewport.height / 2;
  state.transform.x = cx - (cx - state.transform.x) * (scale / oldScale);
  state.transform.y = cy - (cy - state.transform.y) * (scale / oldScale);
  state.transform.scale = scale;
  applyTransform();
  renderStats();
}

function fitGraph() {
  const view = graphData[state.viewId];
  if (!view || !view.nodes.length) return;
  const points = view.nodes.map((node) => state.positions.get(node.id)).filter(Boolean);
  const minX = Math.min(...points.map((point) => point.x));
  const maxX = Math.max(...points.map((point) => point.x + nodeWidth));
  const minY = Math.min(...points.map((point) => point.y));
  const maxY = Math.max(...points.map((point) => point.y + nodeHeight));
  const graphWidth = maxX - minX;
  const graphHeight = maxY - minY;
  const minReadableScale = viewport.width < 760 ? 0.46 : 0.54;
  const scale = Math.max(
    minReadableScale,
    Math.min(1.08, (viewport.width - 84) / graphWidth, (viewport.height - 110) / graphHeight)
  );
  const scaledWidth = graphWidth * scale;
  const scaledHeight = graphHeight * scale;
  state.transform = {
    scale,
    x: scaledWidth > viewport.width - 84
      ? 42 - minX * scale
      : (viewport.width - scaledWidth) / 2 - minX * scale,
    y: scaledHeight > viewport.height - 110
      ? 120 - minY * scale
      : (viewport.height - scaledHeight) / 2 - minY * scale + 18
  };
  applyTransform();
  renderStats();
}

function renderViews() {
  viewList.innerHTML = "";
  Object.entries(graphData).forEach(([id, view]) => {
    const button = document.createElement("button");
    button.className = `view-button${id === state.viewId ? " active" : ""}`;
    button.type = "button";
    button.style.setProperty("--view-color", kindColors[getDominantKind(view)]);
    button.innerHTML = `<span class="view-name">${view.title}</span><span class="view-count">${view.nodes.length}</span>`;
    button.addEventListener("click", () => setView(id));
    viewList.appendChild(button);
  });
}

function renderLegend() {
  legend.innerHTML = Object.entries(kindLabels).map(([kind, label]) => `
    <div class="legend-item">
      <span class="legend-dot" style="--legend-color: ${kindColors[kind]}"></span>
      <span>${label}</span>
    </div>
  `).join("");
}

function renderBreadcrumb() {
  const view = graphData[state.viewId];
  const crumbs = [];
  if (state.viewId !== "overview") crumbs.push(graphData.overview.title);
  crumbs.push(view.title);
  breadcrumb.innerHTML = crumbs.map((item) => `<span class="crumb">${item}</span>`).join("");
}

function renderMeta() {
  const view = graphData[state.viewId];
  viewSubtitle.textContent = view.subtitle || "";
  viewDescription.textContent = view.description || "";
  renderStats();
}

function renderStats() {
  const view = graphData[state.viewId];
  const matches = view.nodes.filter((node) => nodeMatches(node, state.query)).length;
  graphStats.innerHTML = `
    <div class="stat"><strong>${view.nodes.length}</strong><span>nodes</span></div>
    <div class="stat"><strong>${view.links.length}</strong><span>proofs</span></div>
    <div class="stat"><strong>${Math.round(state.transform.scale * 100)}%</strong><span>zoom</span></div>
    <div class="stat"><strong>${state.query ? matches : getViewKinds(view).length}</strong><span>${state.query ? "matches" : "layers"}</span></div>
  `;
}

function renderFocusToggle() {
  focusToggleButton.textContent = state.focusMode ? "Focus on" : "Show all";
  focusToggleButton.setAttribute("aria-pressed", String(state.focusMode));
  focusToggleButton.classList.toggle("active", state.focusMode);
}

function renderEdgeList(title, edges, direction) {
  if (!edges.length) return "";
  const rows = edges.map((link) => {
    const otherId = direction === "incoming" ? link.source : link.target;
    const other = getNode(otherId);
    const label = direction === "incoming"
      ? `${other?.label || otherId} proves into this`
      : `feeds ${other?.label || otherId}`;
    return `
      <button class="edge-chip" type="button" data-edge-key="${edgeKey(link)}">
        <strong>${link.label}</strong>
        <span>${label}</span>
      </button>
    `;
  }).join("");
  return `
    <div class="detail-section">
      <h3>${title}</h3>
      <div class="edge-list">${rows}</div>
    </div>
  `;
}

function renderDetails(item = null, link = null) {
  const view = graphData[state.viewId];
  if (link) {
    const info = getEdgeInfo(link);
    const source = view.nodes.find((node) => node.id === link.source);
    const target = view.nodes.find((node) => node.id === link.target);
    detailsContent.innerHTML = `
      <div class="details-card">
        <div class="detail-kicker">
          <span class="detail-type">proof edge</span>
          <span class="detail-type">${info.relation}</span>
        </div>
        <h2>${source?.label || link.source} to ${target?.label || link.target}</h2>
        <p>${info.description}</p>
        <div class="detail-section">
          <h3>Relation</h3>
          <p>${link.label}</p>
        </div>
        <div class="detail-section">
          <h3>Main theorem or declaration</h3>
          <div class="pill-list"><span class="pill">${info.theorem}</span></div>
        </div>
        <div class="detail-section">
          <h3>Why the arrow exists</h3>
          <p>${info.proof}</p>
        </div>
        <div class="detail-section">
          <h3>Source</h3>
          <button class="edge-chip" type="button" data-node-id="${source?.id || link.source}">
            <strong>${source?.label || link.source}</strong>
            <span>${source?.summary || ""}</span>
          </button>
        </div>
        <div class="detail-section">
          <h3>Target</h3>
          <button class="edge-chip" type="button" data-node-id="${target?.id || link.target}">
            <strong>${target?.label || link.target}</strong>
            <span>${target?.summary || ""}</span>
          </button>
        </div>
      </div>`;
    detailsContent.querySelectorAll("[data-node-id]").forEach((button) => {
      button.addEventListener("click", () => selectNode(button.dataset.nodeId));
    });
    return;
  }

  const selected = item || view.nodes.find((node) => node.id === state.selectedId);
  state.selectedId = selected?.id || null;

  if (!selected) {
    const kinds = getViewKinds(view).map((kind) => kindLabels[kind] || kind).join(", ");
    detailsContent.innerHTML = `
      <div class="details-card">
        <div class="detail-kicker">
          <span class="detail-type">graph view</span>
          <span class="detail-type">${view.nodes.length} nodes / ${view.links.length} proofs</span>
        </div>
        <h2>${view.title}</h2>
        <p>${view.description}</p>
        <div class="detail-section">
          <h3>Layers</h3>
          <p>${kinds}</p>
        </div>
        <div class="detail-section">
          <h3>Proof bridges</h3>
          <div class="edge-list">
            ${view.links.map((edge) => {
              const source = view.nodes.find((node) => node.id === edge.source);
              const target = view.nodes.find((node) => node.id === edge.target);
              return `
                <button class="edge-chip" type="button" data-edge-key="${edgeKey(edge)}">
                  <strong>${edge.label}</strong>
                  <span>${source?.label || edge.source} to ${target?.label || edge.target}</span>
                </button>
              `;
            }).join("")}
          </div>
        </div>
      </div>
    `;
    detailsContent.querySelectorAll("[data-edge-key]").forEach((button) => {
      button.addEventListener("click", () => {
        const edge = view.links.find((candidate) => edgeKey(candidate) === button.dataset.edgeKey);
        if (edge) selectEdge(edge);
      });
    });
    return;
  }

  const declarations = (selected.declarations || []).map((decl) => `<span class="pill">${decl}</span>`).join("");
  const drillDown = selected.view && graphData[selected.view]
    ? `<button class="detail-action" type="button" data-open-view="${selected.view}">Open ${graphData[selected.view].title}</button>`
    : "";
  const file = selected.file
    ? `<a class="file-link" href="${fileHref(selected.file)}" target="_blank" rel="noopener noreferrer">${selected.file}</a>`
    : "";
  const related = getRelatedEdges(selected.id);
  const profile = getNodeProfile(selected, view);

  detailsContent.innerHTML = `
    <div class="details-card">
      <div class="detail-kicker">
        <span class="detail-type">${kindLabels[selected.kind] || selected.kind || "node"}</span>
        <span class="detail-type">${related.incoming.length} in / ${related.outgoing.length} out</span>
      </div>
      <h2>${selected.label}</h2>
      <p>${profile.role}</p>
      ${drillDown}
      <div class="detail-section">
        <h3>Why this node matters</h3>
        <p>${profile.why}</p>
      </div>
      <div class="detail-section">
        <h3>Lean declarations</h3>
        <div class="pill-list">${declarations || '<span class="pill">module</span>'}</div>
      </div>
      ${renderEdgeList("Inputs", related.incoming, "incoming")}
      ${renderEdgeList("Outputs", related.outgoing, "outgoing")}
      <div class="detail-section">
        <h3>Location</h3>
        ${file}
      </div>
    </div>
    `;

  const openButton = detailsContent.querySelector("[data-open-view]");
  if (openButton) {
    openButton.addEventListener("click", () => setView(openButton.dataset.openView));
  }
  detailsContent.querySelectorAll("[data-edge-key]").forEach((button) => {
    button.addEventListener("click", () => {
      const edge = view.links.find((candidate) => edgeKey(candidate) === button.dataset.edgeKey);
      if (edge) selectEdge(edge);
    });
  });
}

function edgeLaneOffset(view, link) {
  const incoming = view.links.filter((candidate) => candidate.target === link.target);
  const outgoing = view.links.filter((candidate) => candidate.source === link.source);
  const incomingIndex = incoming.findIndex((candidate) => edgeKey(candidate) === edgeKey(link));
  const outgoingIndex = outgoing.findIndex((candidate) => edgeKey(candidate) === edgeKey(link));
  const targetOffset = incoming.length > 1 ? (incomingIndex - (incoming.length - 1) / 2) * 150 : 0;
  const sourceOffset = outgoing.length > 1 ? (outgoingIndex - (outgoing.length - 1) / 2) * 88 : 0;
  return targetOffset + sourceOffset;
}

function cubicPoint(p0, p1, p2, p3, t) {
  const mt = 1 - t;
  return {
    x: mt ** 3 * p0.x + 3 * mt ** 2 * t * p1.x + 3 * mt * t ** 2 * p2.x + t ** 3 * p3.x,
    y: mt ** 3 * p0.y + 3 * mt ** 2 * t * p1.y + 3 * mt * t ** 2 * p2.y + t ** 3 * p3.y
  };
}

function cubicTangent(p0, p1, p2, p3, t) {
  const mt = 1 - t;
  return {
    x: 3 * mt ** 2 * (p1.x - p0.x) + 6 * mt * t * (p2.x - p1.x) + 3 * t ** 2 * (p3.x - p2.x),
    y: 3 * mt ** 2 * (p1.y - p0.y) + 6 * mt * t * (p2.y - p1.y) + 3 * t ** 2 * (p3.y - p2.y)
  };
}

function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

function rectsOverlap(a, b, padding = 0) {
  return (
    a.x < b.x + b.width + padding &&
    a.x + a.width > b.x - padding &&
    a.y < b.y + b.height + padding &&
    a.y + a.height > b.y - padding
  );
}

function labelOverlapCount(view, point, labelWidth, labelHeight) {
  const labelRect = {
    x: point.x - labelWidth / 2,
    y: point.y - labelHeight + 4,
    width: labelWidth,
    height: labelHeight
  };
  return view.nodes.reduce((count, node) => {
    const nodePoint = state.positions.get(node.id);
    if (!nodePoint) return count;
    const nodeRect = { x: nodePoint.x, y: nodePoint.y, width: nodeWidth, height: nodeHeight };
    return count + (rectsOverlap(labelRect, nodeRect, 24) ? 1 : 0);
  }, 0);
}

function clearLabelPoint(view, route, labelWidth, labelHeight) {
  const laneSign = Math.sign(route.lane);
  const candidates = laneSign >= 0
    ? [0, 110, -110, 175, -175, 245, -245, 320, -320]
    : [0, -110, 110, -175, 175, -245, 245, -320, 320];
  let best = route.label;
  let bestCount = Infinity;

  for (const dy of candidates) {
    const candidate = { x: route.label.x, y: route.label.y + dy };
    const overlapCount = labelOverlapCount(view, candidate, labelWidth, labelHeight);
    if (overlapCount === 0) return candidate;
    if (overlapCount < bestCount) {
      best = candidate;
      bestCount = overlapCount;
    }
  }

  return best;
}

function edgeRoute(view, link, a, b) {
  const x1 = a.x + nodeWidth;
  const y1 = a.y + nodeHeight / 2;
  const x2 = b.x;
  const y2 = b.y + nodeHeight / 2;
  const dx = Math.max(96, Math.abs(x2 - x1) * 0.46);
  const lane = edgeLaneOffset(view, link);
  const p0 = { x: x1, y: y1 };
  const p1 = { x: x1 + dx, y: y1 + lane };
  const p2 = { x: x2 - dx, y: y2 + lane };
  const p3 = { x: x2, y: y2 };
  const label = cubicPoint(p0, p1, p2, p3, 0.5);
  const tangent = cubicTangent(p0, p1, p2, p3, 0.5);
  const angle = clamp(Math.atan2(tangent.y, tangent.x) * 180 / Math.PI, -12, 12);
  return {
    d: `M ${p0.x} ${p0.y} C ${p1.x} ${p1.y}, ${p2.x} ${p2.y}, ${p3.x} ${p3.y}`,
    label,
    angle,
    lane
  };
}

function renderGraph() {
  const view = graphData[state.viewId];
  viewport = svg.getBoundingClientRect();
  renderStats();
  svg.innerHTML = "";

  const defs = make("defs", {}, svg);
  const marker = make("marker", {
    id: "arrow",
    markerWidth: "10",
    markerHeight: "10",
    refX: "9",
    refY: "3",
    orient: "auto",
    markerUnits: "strokeWidth"
  }, defs);
  make("path", { d: "M 0 0 L 9 3 L 0 6 z", fill: "#8b98aa" }, marker);

  scene = make("g", { class: "scene" }, svg);
  if (state.positionsViewId !== state.viewId || state.positions.size === 0) {
    layout(view);
  }

  const selectedId = state.selectedId;
  const selectedEdgeKey = state.selectedEdge ? edgeKey(state.selectedEdge) : null;
  const matches = new Set(view.nodes.filter((node) => nodeMatches(node, state.query)).map((node) => node.id));
  emptyState.hidden = !state.query || matches.size > 0;

  const edgesLayer = make("g", { class: "edges" }, scene);
  view.links.forEach((link) => {
    const source = state.positions.get(link.source);
    const target = state.positions.get(link.target);
    if (!source || !target) return;
    const isSelectedEdge = selectedEdgeKey === edgeKey(link);
    const isNeighbor = selectedId && linkTouches(link, selectedId);
    const focusDim = state.focusMode && ((selectedEdgeKey && !isSelectedEdge) || (selectedId && !isNeighbor));
    const dim = focusDim || state.query && !(matches.has(link.source) || matches.has(link.target));
    const route = edgeRoute(view, link, source, target);
    const path = make("path", {
      class: `edge${isSelectedEdge ? " selected" : ""}${isNeighbor ? " neighbor" : ""}${dim ? " dimmed" : ""}`,
      d: route.d
    }, edgesLayer);
    const hitPath = make("path", {
      class: "edge-hit",
      d: route.d
    }, edgesLayer);
    hitPath.addEventListener("click", (event) => {
      event.stopPropagation();
      selectEdge(link);
    });
    path.addEventListener("click", (event) => {
      event.stopPropagation();
      selectEdge(link);
    });
  });

  const labelsLayer = make("g", { class: "edge-labels" }, scene);
  view.links.forEach((link) => {
    const source = state.positions.get(link.source);
    const target = state.positions.get(link.target);
    if (!source || !target) return;
    const route = edgeRoute(view, link, source, target);
    const isSelectedEdge = selectedEdgeKey === edgeKey(link);
    const isNeighbor = selectedId && linkTouches(link, selectedId);
    const focusDim = state.focusMode && ((selectedEdgeKey && !isSelectedEdge) || (selectedId && !isNeighbor));
    const dim = focusDim || state.query && !(matches.has(link.source) || matches.has(link.target));
    const lines = splitTextLines(link.label, 22, 2);
    const labelWidth = Math.min(170, Math.max(92, Math.max(...lines.map((line) => line.length)) * 7.1 + 22));
    const labelHeight = 12 + lines.length * 14;
    const point = clearLabelPoint(view, route, labelWidth, labelHeight);
    const labelGroup = make("g", {
      class: `edge-label-group${dim ? " dimmed" : ""}`,
      tabindex: "0",
      role: "button",
      "aria-label": link.label
    }, labelsLayer);
    labelGroup.addEventListener("click", (event) => {
      event.stopPropagation();
      selectEdge(link);
    });
    labelGroup.addEventListener("keydown", (event) => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        selectEdge(link);
      }
    });
    const labelBg = make("rect", {
      class: "edge-label-bg",
      x: point.x - labelWidth / 2,
      y: point.y - labelHeight + 4,
      width: labelWidth,
      height: labelHeight,
      rx: 6,
      ry: 6
    }, labelGroup);
    const text = make("text", {
      class: "edge-label",
      x: point.x,
      "text-anchor": "middle"
    }, labelGroup);
    lines.forEach((line, index) => {
      const tspan = make("tspan", { x: point.x, y: point.y - (lines.length - 1) * 7 + index * 14 }, text);
      tspan.textContent = line;
    });
  });

  const nodesLayer = make("g", { class: "nodes" }, scene);
  view.nodes.forEach((node) => {
    const point = state.positions.get(node.id);
    const edgeSelectedAndUnrelated = state.selectedEdge && ![state.selectedEdge.source, state.selectedEdge.target].includes(node.id);
    const focusDim = state.focusMode && (edgeSelectedAndUnrelated || (selectedId && selectedId !== node.id && !view.links.some((link) => linkTouches(link, selectedId) && linkTouches(link, node.id))));
    const dim = (state.query && !matches.has(node.id)) || focusDim;
    const group = make("g", {
      class: `node${node.id === selectedId ? " selected" : ""}${dim ? " dimmed" : ""}`,
      "data-kind": node.kind || "node",
      transform: `translate(${point.x} ${point.y})`,
      tabindex: "0",
      role: "button",
      "aria-label": node.label
    }, nodesLayer);
    make("rect", { class: "node-card", width: nodeWidth, height: nodeHeight, rx: "8", ry: "8" }, group);
    make("rect", { class: "node-top-accent", x: "6", width: nodeWidth - 6, height: "22", rx: "8", ry: "8" }, group);
    make("rect", { class: "node-accent", width: "6", height: nodeHeight, rx: "4", ry: "4" }, group);
    const kindText = make("text", { x: 17, y: 18, class: "node-kind" }, group);
    kindText.textContent = node.kind || "node";
    makeText(group, node.label, 17, 42, 17, "node-title", 24, 2);
    makeText(group, node.subtitle || "", 17, 76, 13, "node-subtitle", 29, 2);

    group.addEventListener("pointerdown", (event) => {
      event.stopPropagation();
      didDrag = false;
      svg.classList.add("dragging");
      state.dragging = {
        id: node.id,
        startX: event.clientX,
        startY: event.clientY,
        origin: { ...state.positions.get(node.id) }
      };
      group.setPointerCapture(event.pointerId);
    });
    group.addEventListener("pointerup", () => {
      if (state.dragging && state.dragging.id === node.id) {
        state.dragging = null;
        svg.classList.remove("dragging");
      }
    });
    group.addEventListener("click", (event) => {
      event.stopPropagation();
      if (didDrag) return;
      scheduleNodeSelect(node.id);
    });
    group.addEventListener("dblclick", (event) => {
      event.stopPropagation();
      if (pendingNodeClick) {
        clearTimeout(pendingNodeClick);
        pendingNodeClick = null;
      }
      if (node.view) setView(node.view);
    });
    group.addEventListener("keydown", (event) => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        selectNode(node.id);
      }
      if (event.key === "d" || event.key === "D") {
        if (node.view && graphData[node.view]) {
          setView(node.view);
        }
      }
    });
  });

  applyTransform();
}

function splitTextLines(text, lineLimit = 24, maxLines = 2) {
  const words = String(text).split(/\s+/);
  const lines = [];
  let current = "";
  words.forEach((word) => {
    if (current && (current + " " + word).trim().length > lineLimit) {
      lines.push(current.trim());
      current = word;
    } else {
      current = `${current} ${word}`.trim();
    }
  });
  if (current) lines.push(current);
  return lines.slice(0, maxLines);
}

function makeText(parent, text, x, y, size, className, lineLimit = 24, maxLines = 2) {
  const lines = splitTextLines(text, lineLimit, maxLines);
  lines.forEach((line, index) => {
    const el = make("text", { x, y: y + index * (size + 2), "font-size": size, class: className }, parent);
    el.textContent = line;
  });
}

function selectNode(id) {
  state.selectedId = id;
  state.selectedEdge = null;
  renderDetails();
  renderGraph();
}

function scheduleNodeSelect(id) {
  if (pendingNodeClick) clearTimeout(pendingNodeClick);
  pendingNodeClick = setTimeout(() => {
    pendingNodeClick = null;
    selectNode(id);
  }, 140);
}

function selectEdge(link) {
  state.selectedId = null;
  state.selectedEdge = link;
  renderGraph();
  renderDetails(null, link);
}

function setView(id) {
  if (!graphData[id]) return;
  state.viewId = id;
  state.selectedId = null;
  state.selectedEdge = null;
  state.query = "";
  searchInput.value = "";
  state.transform = { x: 0, y: 0, scale: 1 };
  state.positions = new Map();
  state.positionsViewId = null;
  renderViews();
  renderLegend();
  renderFocusToggle();
  renderBreadcrumb();
  renderMeta();
  renderDetails();
  renderGraph();
  fitGraph();
}

svg.addEventListener("pointerdown", (event) => {
  if (event.target !== svg) return;
  svg.classList.add("panning");
  state.panning = {
    startX: event.clientX,
    startY: event.clientY,
    origin: { ...state.transform }
  };
  svg.setPointerCapture(event.pointerId);
});

svg.addEventListener("pointermove", (event) => {
  if (state.dragging) {
    didDrag = didDrag || Math.abs(event.clientX - state.dragging.startX) + Math.abs(event.clientY - state.dragging.startY) > 4;
    const point = state.positions.get(state.dragging.id);
    point.x = state.dragging.origin.x + (event.clientX - state.dragging.startX) / state.transform.scale;
    point.y = state.dragging.origin.y + (event.clientY - state.dragging.startY) / state.transform.scale;
    renderGraph();
    return;
  }

  if (state.panning) {
    state.transform.x = state.panning.origin.x + event.clientX - state.panning.startX;
    state.transform.y = state.panning.origin.y + event.clientY - state.panning.startY;
    applyTransform();
  }
});

svg.addEventListener("pointerup", () => {
  state.dragging = null;
  state.panning = null;
  svg.classList.remove("dragging", "panning");
});

svg.addEventListener("wheel", (event) => {
  event.preventDefault();
  const oldScale = state.transform.scale;
  const delta = Math.sign(event.deltaY) * -0.08;
  const rect = svg.getBoundingClientRect();
  const cx = event.clientX - rect.left;
  const cy = event.clientY - rect.top;
  setScale(oldScale + delta, { x: cx, y: cy });
}, { passive: false });

searchInput.addEventListener("input", () => {
  state.query = searchInput.value.trim();
  state.selectedEdge = null;
  renderGraph();
});

fitButton.addEventListener("click", fitGraph);
resetButton.addEventListener("click", () => setView("overview"));
focusToggleButton.addEventListener("click", () => {
  state.focusMode = !state.focusMode;
  renderFocusToggle();
  renderGraph();
});
zoomInButton.addEventListener("click", () => setScale(state.transform.scale + 0.16));
zoomOutButton.addEventListener("click", () => setScale(state.transform.scale - 0.16));

window.addEventListener("keydown", (event) => {
  if (event.target === searchInput) return;
  if (event.key === "f") fitGraph();
  if (event.key === "Escape") {
    state.query = "";
    searchInput.value = "";
    state.selectedEdge = null;
    renderGraph();
    renderDetails();
  }
});

window.addEventListener("resize", () => {
  state.positionsViewId = null;
  renderGraph();
  fitGraph();
});

setView("overview");
