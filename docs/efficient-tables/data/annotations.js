// Curated skin on top of the generated graph.js skeleton (see scripts/gen_docs_graph.py --check).
// A single strict-JSON object literal assigned to window.ANNOTATIONS.
window.ANNOTATIONS = {
 "repo": {
  "owner": "VerifiedQC",
  "repo": "ForShor",
  "branch": "main"
 },
 "intro": {
  "title": "Exact table optimization",
  "summary": "A classical, theoretical companion to ForShor. It characterizes and solves the table-optimization problem behind ForShor's PhaseProduct benchmark. It is not part of ForShor's verified order-finding circuit, and ForShor does not import it. Two Lake projects: a layered proof library and a separate hardness project.",
  "spine": [
   "Library",
   "Hardness"
  ]
 },
 "roles": {
  "library": {
   "color": "#2368b8",
   "label": "Proof library"
  },
  "hardness": {
   "color": "#1b8c97",
   "label": "Hardness project"
  },
  "model": {
   "color": "#2368b8",
   "label": "Source & exact model"
  },
  "planner": {
   "color": "#b46519",
   "label": "Planner"
  },
  "phase": {
   "color": "#be3f50",
   "label": "Phase identity & catalogue"
  },
  "provider": {
   "color": "#7d6a13",
   "label": "Provider & optimizer"
  },
  "encoding": {
   "color": "#218263",
   "label": "Encoding & bounds"
  },
  "alignment": {
   "color": "#6d55b8",
   "label": "Solver alignment"
  },
  "support": {
   "color": "#8793a6",
   "label": "Support"
  },
  "contract": {
   "color": "#8793a6",
   "label": "Vendored contract"
  },
  "barrier": {
   "color": "#1b8c97",
   "label": "Mahaney & sparsity barrier"
  },
  "reduction": {
   "color": "#be3f50",
   "label": "NP-hardness reduction"
  }
 },
 "layers": {},
 "nodes": {
  "Library": {
   "role": "library",
   "subtitle": "Lean 4.28 · Mathlib · exact optimality",
   "summary": "The machine-checked part of the table-optimization work: a model of table programs and their recursive cost, a planner, and a finite-search optimizer, proved optimal over all source-legal tables at fixed (K, W, N). It proves no running-time bound and no polynomial-time synthesis."
  },
  "Hardness": {
   "role": "hardness",
   "subtitle": "Lean 4.35 · complexitylib · separate Lake project",
   "summary": "The complexity statements. Mahaney's theorem and the conditional sparsity barriers for the paper's problem, and NP-hardness of the structural score A + 5L when the interpolation points are supplied as input. It does not show that T-count optimization is NP-hard."
  },
  "Library/Foundations": {
   "role": "support",
   "subtitle": "counting & four side developments",
   "summary": "Weighted-word counting and budget arithmetic that do not mention the table model, plus four self-contained developments: small integer points in a polyhedron, composition of stage costs, separation of signed sums of powers of two, and charge counting of the paired constructor."
  },
  "Library/Source": {
   "role": "model",
   "subtitle": "the program language and contracts",
   "summary": "The source-level model: the program language and its metrics, the baseline and best-known policies (the P52, P6 and Pf4 tables), and the recursive planner with its correctness statement."
  },
  "Library/Model": {
   "role": "model",
   "subtitle": "the exact model",
   "summary": "The exact model: instruction language, the historical width scanner, the interpreter and value traces, and the profile algebra. A table matters to the cost only through its profile and charge."
  },
  "Library/Planner": {
   "role": "planner",
   "subtitle": "recursive planner and exact price",
   "summary": "The recursive planner: reachability, local recursion, dense versus sparse search, optimality for planners and for shared-table policies, and the exact integer form of the rotation price."
  },
  "Library/PhaseProduct": {
   "role": "phase",
   "subtitle": "the phase identity and the catalogue optimum",
   "summary": "The phase identity and its construction from interpolation tables, then the finite-catalogue optimum pp_through_arity_K. This is the optimization problem's model of a phase product, not ForShor's verified circuit of the same name."
  },
  "Library/Provider": {
   "role": "provider",
   "subtitle": "candidates, pricing, exhaustive optimizer",
   "summary": "Everything that feeds the optimizer: raw ladders and certificates, profile intervals, the baseline charge ceiling, shift-block compression, interpolation weights, and the finite effective provider whose exhaustive Optimize is the executable optimizer. Finite-search statements only."
  },
  "Library/ILPEncoding": {
   "role": "encoding",
   "subtitle": "affine cost encoding and its size",
   "summary": "The affine/ILP encoding of the shared-ladder objective and explicit bounds on its bit size. These bound the encoding; they do not assert an ILP solver or uniform polynomial-time synthesis."
  },
  "Library/Alignment": {
   "role": "alignment",
   "subtitle": "Fortran solver vs. the Lean model",
   "summary": "FortranSolver aligns the search windows and loops of the Fortran solver with the Lean model. SparseThreshold holds counting and encoding lemmas used in the sparseness discussion; it is not a sparseness theorem."
  },
  "Library/Helpers": {
   "role": "support",
   "subtitle": "standalone lemma files",
   "summary": "Small Mathlib-only lemma files kept as a separate library (EfficientTablesHelpers). Nothing in the main library imports them."
  },
  "Hardness/TableGeneration": {
   "role": "contract",
   "subtitle": "benchmark contract, vendored",
   "summary": "Byte-identical copies of the ShorTableOptimization contract files (Basic, Language, Spec, Metrics, ContractSoundness). The table problem is stated against this contract; it is not original to this package."
  },
  "Hardness/Mahaney": {
   "role": "barrier",
   "subtitle": "a sparse NP-hard set collapses P and NP",
   "summary": "Mahaney's theorem on complexitylib's Turing machines, and the two conditional barriers built from it: for the paper's problem (k in unary) and for a unary-n policy language whose optimum is polynomially bounded. They say an NP-hardness proof would imply P = NP; they are not hardness results."
  },
  "Hardness/Points": {
   "role": "reduction",
   "subtitle": "SAT → DHC₂ → EHC → table",
   "summary": "NP-hardness of the structural-score table problem when the points are part of the input, already at arity 2, by SAT → directed Hamiltonian cycle (out-degree ≤ 2) → edge-Hamiltonian cycle → table. The paper's fixed-points problem stays barrier-blocked."
  }
 },
 "views": {
  "": {
   "columns": [
    [
     "Library"
    ],
    [
     "Hardness"
    ]
   ],
   "edges": []
  },
  "Library": {
   "edges": [
    {
     "from": "Library/Source",
     "to": "Library/Model",
     "emphasis": "primary",
     "label": "source language, metrics, baselines",
     "why": "Model/Defs.lean imports Source/Baseline, Source/Model and Source/RecursivePlanner, so the exact instruction-level model is defined over the source-level language."
    },
    {
     "from": "Library/Model",
     "to": "Library/Planner",
     "emphasis": "primary",
     "theorem": "ppProblem",
     "label": "ppProblem, the recursive objective",
     "why": "Planner/Optimality and Planner/PolicyOptimality import Model/Defs.lean, where the recursive objective ppProblem is defined."
    },
    {
     "from": "Library/Planner",
     "to": "Library/PhaseProduct",
     "emphasis": "primary",
     "label": "planner optimality",
     "why": "PhaseProduct/Catalog/ChoiceSoundness imports Planner/Optimality, and PhaseProduct/Catalog/Count imports Planner/PolicyOptimality."
    },
    {
     "from": "Library/PhaseProduct",
     "to": "Library/Provider",
     "emphasis": "primary",
     "theorem": "pp_through_arity_K",
     "label": "the finite-catalogue optimum",
     "why": "Provider/Ladders/CatalogTransfer imports PhaseProduct/Catalog/EndToEnd, where pp_through_arity_K is proved: optimal over a finite certified catalogue. Provider extends this beyond the catalogue; its strongest form is optimal_raw_F2_exact."
    },
    {
     "from": "Library/Planner",
     "to": "Library/Provider",
     "emphasis": "primary",
     "theorem": "tauRS_eq_tauExact",
     "label": "exact integer rotation price",
     "why": "Provider/Effective/ExactPP and ProfileExact import Planner/TauPrice, which proves that the rounded rotation price equals its exact integer form."
    },
    {
     "from": "Library/Provider",
     "to": "Library/ILPEncoding",
     "emphasis": "primary",
     "label": "profiles into the affine encoding",
     "why": "ILPEncoding/Bundles/Profile imports Provider/Effective/Attain, and the label bounds import Provider/Profiles and Provider/Weights."
    },
    {
     "from": "Library/Foundations",
     "to": "Library/ILPEncoding",
     "emphasis": "primary",
     "label": "counting and budget arithmetic",
     "why": "ILPEncoding's budget and label bounds import Foundations/Counting (branch counts, dimension bound, recursive calls, typed words)."
    },
    {
     "from": "Library/ILPEncoding",
     "to": "Library/Alignment",
     "emphasis": "primary",
     "label": "bit-size bounds the solver relies on",
     "why": "Alignment/FortranSolver and Alignment/SparseThreshold import ILPEncoding's StopBudget, Encoding and MatrixOptimizer modules."
    },
    {
     "from": "Library/Model",
     "to": "Library/PhaseProduct",
     "emphasis": "secondary"
    },
    {
     "from": "Library/Model",
     "to": "Library/Provider",
     "emphasis": "secondary"
    },
    {
     "from": "Library/Model",
     "to": "Library/ILPEncoding",
     "emphasis": "secondary"
    },
    {
     "from": "Library/Source",
     "to": "Library/Planner",
     "emphasis": "secondary"
    },
    {
     "from": "Library/Source",
     "to": "Library/PhaseProduct",
     "emphasis": "secondary"
    },
    {
     "from": "Library/Planner",
     "to": "Library/ILPEncoding",
     "emphasis": "secondary"
    },
    {
     "from": "Library/PhaseProduct",
     "to": "Library/Alignment",
     "emphasis": "secondary"
    }
   ]
  },
  "Hardness": {
   "edges": [
    {
     "from": "Hardness/TableGeneration",
     "to": "Hardness/Mahaney",
     "emphasis": "primary",
     "label": "the problem the barrier is about",
     "why": "Mahaney/SparsityBarrier imports TableGeneration's Spec, Metrics and ContractSoundness: the sparsity barrier is stated for the benchmark's own contract."
    },
    {
     "from": "Hardness/TableGeneration",
     "to": "Hardness/Points",
     "emphasis": "primary",
     "theorem": "reduction_correct",
     "label": "the contract the reduction targets",
     "why": "Points/Reduction imports TableGeneration/ContractSoundness, Points/Gap imports Language and Points/LowerBound imports Metrics."
    },
    {
     "from": "Hardness/Mahaney",
     "to": "Hardness/Points",
     "emphasis": "primary",
     "label": "instance encoding and string toolkit",
     "why": "Points/Encode imports Mahaney/TableLang and Points/Split imports Mahaney/Blocks: the hardness proof builds on the barrier's bit-string encoding of table instances."
    }
   ]
  },
  "Hardness/Mahaney": {
   "edges": [
    {
     "from": "Hardness/Mahaney/Bits.lean",
     "to": "Hardness/Mahaney/Strings.lean",
     "emphasis": "primary"
    },
    {
     "from": "Hardness/Mahaney/Bits.lean",
     "to": "Hardness/Mahaney/Blocks.lean",
     "emphasis": "secondary"
    },
    {
     "from": "Hardness/Mahaney/Strings.lean",
     "to": "Hardness/Mahaney/Left.lean",
     "emphasis": "primary",
     "theorem": "LeftSAT_mem_NP",
     "label": "the left set of SAT is in NP"
    },
    {
     "from": "Hardness/Mahaney/Core.lean",
     "to": "Hardness/Mahaney/ListAlg.lean",
     "emphasis": "primary",
     "label": "pruning core, as a list algorithm"
    },
    {
     "from": "Hardness/Mahaney/ListAlg.lean",
     "to": "Hardness/Mahaney/Blocks.lean",
     "emphasis": "primary"
    },
    {
     "from": "Hardness/Mahaney/Blocks.lean",
     "to": "Hardness/Mahaney/Machine.lean",
     "emphasis": "primary"
    },
    {
     "from": "Hardness/Mahaney/Left.lean",
     "to": "Hardness/Mahaney/Machine.lean",
     "emphasis": "primary"
    },
    {
     "from": "Hardness/Mahaney/Machine.lean",
     "to": "Hardness/Mahaney/Step.lean",
     "emphasis": "primary",
     "theorem": "stepS_mem_FP",
     "label": "one pruning level in FP"
    },
    {
     "from": "Hardness/Mahaney/Step.lean",
     "to": "Hardness/Mahaney/Theorem.lean",
     "emphasis": "primary",
     "theorem": "iterS_mem_FP",
     "label": "the loop is in FP"
    },
    {
     "from": "Hardness/Mahaney/Theorem.lean",
     "to": "Hardness/Mahaney/TableLang.lean",
     "emphasis": "primary",
     "theorem": "mahaney",
     "label": "Sparse S → NPHard S → P = NP"
    },
    {
     "from": "Hardness/Mahaney/SparsityBarrier.lean",
     "to": "Hardness/Mahaney/TableLang.lean",
     "emphasis": "primary",
     "label": "the table problem and its sparse core"
    },
    {
     "from": "Hardness/Mahaney/TableLang.lean",
     "to": "Hardness/Mahaney/PolicyLang.lean",
     "emphasis": "primary",
     "theorem": "tableOpt_barrier",
     "label": "NPHard TableOptLang → P = NP"
    }
   ]
  },
  "Hardness/Points": {
   "edges": [
    {
     "from": "Hardness/Points/Weight.lean",
     "to": "Hardness/Points/Gap.lean",
     "emphasis": "primary",
     "label": "signed-binary weight arithmetic"
    },
    {
     "from": "Hardness/Points/Gap.lean",
     "to": "Hardness/Points/LowerBound.lean",
     "emphasis": "primary",
     "label": "gap lemma → k = 2 lower bound"
    },
    {
     "from": "Hardness/Points/LowerBound.lean",
     "to": "Hardness/Points/Reduction.lean",
     "emphasis": "primary",
     "theorem": "reduction_correct",
     "label": "EHP ↔ table instance"
    },
    {
     "from": "Hardness/Points/Reduction.lean",
     "to": "Hardness/Points/Encode.lean",
     "emphasis": "primary",
     "theorem": "ehp_le_gen",
     "label": "reduction on bit strings in P"
    },
    {
     "from": "Hardness/Points/Reduction.lean",
     "to": "Hardness/Points/CycleTable.lean",
     "emphasis": "primary",
     "theorem": "cycle_reduction",
     "label": "cycle version"
    },
    {
     "from": "Hardness/Points/CycleTable.lean",
     "to": "Hardness/Points/Split.lean",
     "emphasis": "primary",
     "label": "split + pendant line graph"
    },
    {
     "from": "Hardness/Points/Split.lean",
     "to": "Hardness/Points/Cyclic.lean",
     "emphasis": "primary"
    },
    {
     "from": "Hardness/Points/Cyclic.lean",
     "to": "Hardness/Points/SplitBack.lean",
     "emphasis": "primary",
     "theorem": "dhc_iff_ehc",
     "label": "DHC₂ ↔ edge-Hamiltonian cycle"
    },
    {
     "from": "Hardness/Points/SplitBack.lean",
     "to": "Hardness/Points/DhcTable.lean",
     "emphasis": "primary",
     "label": "DHC₂ ↔ table"
    },
    {
     "from": "Hardness/Points/DhcTable.lean",
     "to": "Hardness/Points/SatGraph.lean",
     "emphasis": "primary",
     "label": "clause cells and rotating cycles"
    },
    {
     "from": "Hardness/Points/SatGraph.lean",
     "to": "Hardness/Points/SatNo.lean",
     "emphasis": "primary",
     "label": "cycle ⇒ satisfying assignment"
    },
    {
     "from": "Hardness/Points/SatNo.lean",
     "to": "Hardness/Points/SatYes.lean",
     "emphasis": "primary",
     "label": "assignment ⇒ cycle"
    },
    {
     "from": "Hardness/Points/SatYes.lean",
     "to": "Hardness/Points/SatCnf.lean",
     "emphasis": "primary",
     "theorem": "sat_iff_table",
     "label": "SAT ↔ table"
    },
    {
     "from": "Hardness/Points/SatCnf.lean",
     "to": "Hardness/Points/SatParse.lean",
     "emphasis": "primary",
     "label": "CNF encodings recognised in P"
    },
    {
     "from": "Hardness/Points/SatParse.lean",
     "to": "Hardness/Points/SatLab.lean",
     "emphasis": "primary"
    },
    {
     "from": "Hardness/Points/SatLab.lean",
     "to": "Hardness/Points/SatOuts.lean",
     "emphasis": "primary"
    },
    {
     "from": "Hardness/Points/SatOuts.lean",
     "to": "Hardness/Points/SatFP.lean",
     "emphasis": "primary",
     "label": "the SAT → table map in P"
    },
    {
     "from": "Hardness/Points/SatFP.lean",
     "to": "Hardness/Points/SatRed.lean",
     "emphasis": "primary",
     "theorem": "genLang_NPHard",
     "label": "NPHard GenLang"
    }
   ]
  }
 }
};
