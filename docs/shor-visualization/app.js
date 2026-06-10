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

let viewport = { width: 900, height: 640 };
let scene;
let didDrag = false;

function make(tag, attrs = {}, parent = null) {
  const el = document.createElementNS(ns, tag);
  Object.entries(attrs).forEach(([key, value]) => el.setAttribute(key, value));
  if (parent) parent.appendChild(el);
  return el;
}

function fileHref(file) {
  if (!file || file.includes("://")) return file;
  return `../../${file}`;
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
  const minGap = viewport.width < 760 ? 270 : 320;
  const xGap = Math.max(minGap, (viewport.width - 160) / Math.max(1, levelCount - 1));
  const nextPositions = new Map();

  [...groups.entries()].sort((a, b) => a[0] - b[0]).forEach(([level, nodes]) => {
    const yGap = Math.max(154, (viewport.height - 130) / Math.max(1, nodes.length));
    nodes.forEach((node, index) => {
      const x = 90 + level * xGap;
      const y = Math.max(70, (viewport.height - yGap * (nodes.length - 1)) / 2 + index * yGap);
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
  const scale = Math.min(1.08, (viewport.width - 84) / graphWidth, (viewport.height - 110) / graphHeight);
  state.transform = {
    scale,
    x: (viewport.width - graphWidth * scale) / 2 - minX * scale,
    y: (viewport.height - graphHeight * scale) / 2 - minY * scale + 18
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
    const source = view.nodes.find((node) => node.id === link.source);
    const target = view.nodes.find((node) => node.id === link.target);
    detailsContent.innerHTML = `
      <div class="details-card">
        <div class="detail-kicker"><span class="detail-type">proof edge</span></div>
        <h2>${link.label}</h2>
        <p>${source?.label || link.source} feeds ${target?.label || link.target}.</p>
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

  const selected = item || view.nodes.find((node) => node.id === state.selectedId) || view.nodes[0];
  state.selectedId = selected?.id || null;

  if (!selected) {
    detailsContent.innerHTML = "";
    return;
  }

  const declarations = (selected.declarations || []).map((decl) => `<span class="pill">${decl}</span>`).join("");
  const drillDown = selected.view && graphData[selected.view]
    ? `<button class="detail-action" type="button" data-open-view="${selected.view}">Open ${graphData[selected.view].title}</button>`
    : "";
  const file = selected.file
    ? `<a class="file-link" href="${fileHref(selected.file)}">${selected.file}</a>`
    : "";
  const related = getRelatedEdges(selected.id);

  detailsContent.innerHTML = `
    <div class="details-card">
      <div class="detail-kicker">
        <span class="detail-type">${kindLabels[selected.kind] || selected.kind || "node"}</span>
        <span class="detail-type">${related.incoming.length} in / ${related.outgoing.length} out</span>
      </div>
      <h2>${selected.label}</h2>
      <p>${selected.summary || view.description}</p>
      ${drillDown}
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

function pathBetween(a, b) {
  const x1 = a.x + nodeWidth;
  const y1 = a.y + nodeHeight / 2;
  const x2 = b.x;
  const y2 = b.y + nodeHeight / 2;
  const dx = Math.max(58, (x2 - x1) * 0.48);
  return `M ${x1} ${y1} C ${x1 + dx} ${y1}, ${x2 - dx} ${y2}, ${x2} ${y2}`;
}

function labelPoint(a, b) {
  return {
    x: (a.x + nodeWidth + b.x) / 2,
    y: (a.y + b.y) / 2 + nodeHeight / 2 - 8
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
    const path = make("path", {
      class: `edge${isSelectedEdge ? " selected" : ""}${isNeighbor ? " neighbor" : ""}${dim ? " dimmed" : ""}`,
      d: pathBetween(source, target)
    }, edgesLayer);
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
    const point = labelPoint(source, target);
    const isSelectedEdge = selectedEdgeKey === edgeKey(link);
    const isNeighbor = selectedId && linkTouches(link, selectedId);
    const focusDim = state.focusMode && ((selectedEdgeKey && !isSelectedEdge) || (selectedId && !isNeighbor));
    const dim = focusDim || state.query && !(matches.has(link.source) || matches.has(link.target));
    const labelWidth = Math.min(190, Math.max(74, link.label.length * 7.1 + 20));
    make("rect", {
      class: `edge-label-bg${dim ? " dimmed" : ""}`,
      x: point.x - labelWidth / 2,
      y: point.y - 17,
      width: labelWidth,
      height: 22,
      rx: 6,
      ry: 6
    }, labelsLayer);
    const text = make("text", {
      class: `edge-label${dim ? " dimmed" : ""}`,
      x: point.x,
      y: point.y,
      "text-anchor": "middle"
    }, labelsLayer);
    text.textContent = link.label;
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
      selectNode(node.id);
    });
    group.addEventListener("dblclick", (event) => {
      event.stopPropagation();
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

function makeText(parent, text, x, y, size, className, lineLimit = 24, maxLines = 2) {
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
  lines.slice(0, maxLines).forEach((line, index) => {
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

function selectEdge(link) {
  state.selectedId = null;
  state.selectedEdge = link;
  renderGraph();
  renderDetails(null, link);
}

function setView(id) {
  if (!graphData[id]) return;
  state.viewId = id;
  state.selectedId = graphData[id].nodes[0]?.id || null;
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
