// Curated skin on top of the generated docs/data/graph.js skeleton.
//
// This file must be a single strict-JSON object literal assigned to
// window.ANNOTATIONS (no comments or trailing commas *inside* the object;
// scripts/gen_docs_graph.py --check parses it as JSON).
//
// `views[path]` curates what a view draws: `columns` (optional) pins the
// left-to-right grid explicitly, one array per column, top to bottom; every
// child of the view must appear exactly once, or --check fails. `edges` is
// the hand-picked list of import edges to draw — each must be a real import
// edge in that view (checked), each `theorem` must resolve to a real
// declaration (checked). Edges not listed still exist in the data (a
// selected node's "also imports / also imported by" section shows them);
// they are just not drawn by default. `emphasis` is "primary" (full role
// colour, thick, labelled if `label` is set), "secondary" (grey, thin,
// unlabelled — real structure that is not the story), or "dim" (light grey
// dashed — real but incidental edges). A view with no `views[path]` entry (or an empty
// `edges` list) falls back to an automatic transitive reduction of its full
// import DAG, drawn as primary with no labels.
window.ANNOTATIONS = {
 "repo": {
  "owner": "VerifiedQC",
  "repo": "ForShor",
  "branch": "main"
 },
 "intro": {
  "title": "ShorVerification",
  "summary": "Framework/ is the specification vocabulary: registers, the Gate/LowGate languages, the semantic classes and cost model every proof is stated in, and Framework/ToomCookTable.lean's ShorSubmission, the Toom-Cook table (an arithmetic program plus the interpolation points it evaluates at) an entrant actually hands in. The correctness contract itself, Reference/Contract.lean's ShorImplementation structure, is stated over that vocabulary. Everything else is the construction: three independently-verified subroutines (PhaseProduct, QFT, ModularExponentiation) are lowered to LowGate by Compiler and feed the Shor assembly, which proves correctness and the gate-count bound; Reference turns it into a concrete ShorImplementation, and QubitCount counts the qubits that implementation needs.",
  "spine": [
   "Reference",
   "Shor",
   "ModularExponentiation",
   "QFT",
   "PhaseProduct"
  ]
 },
 "roles": {
  "framework": {
   "color": "#2368b8",
   "label": "Framework"
  },
  "subroutine": {
   "color": "#b46519",
   "label": "Subroutine"
  },
  "assembly": {
   "color": "#be3f50",
   "label": "Assembly"
  },
  "resource": {
   "color": "#7d6a13",
   "label": "Resource estimate"
  },
  "submission": {
   "color": "#218263",
   "label": "Submission"
  },
  "support": {
   "color": "#8793a6",
   "label": "Support library"
  }
 },
 "layers": {
  "math": {
   "color": "#218263",
   "label": "Math"
  },
  "definitions": {
   "color": "#6d55b8",
   "label": "Definitions"
  },
  "lowering": {
   "color": "#6d55b8",
   "label": "Lowering"
  },
  "spec": {
   "color": "#b46519",
   "label": "Spec"
  },
  "proofs": {
   "color": "#2368b8",
   "label": "Proofs"
  },
  "main": {
   "color": "#be3f50",
   "label": "Main"
  }
 },
 "nodes": {
  "Framework": {
   "role": "framework",
   "subtitle": "the vocabulary",
   "summary": "Defines the vocabulary a Shor order-finding submission is stated in: registers and the Gate/LowGate languages, the QSemantics/MeasureClass semantic interfaces, the LowGate cost model, and Framework/ToomCookTable.lean's ShorSubmission, the Toom-Cook table a submission consists of. The ShorImplementation structure every Implementation/ folder exists to build one value of lives in Reference/Contract.lean, over this vocabulary."
  },
  "PhaseProduct": {
   "role": "subroutine",
   "subtitle": "recursive Toom-Cook phase-product compiler",
   "summary": "Computes exp(i*phi*x*z) on two registers with a circuit that scales better than the naive O(n^2) construction: a Toom-Cook-style interpolation compiler recursively splits operands into k-way chunks, reconstructs the product phase from 2k-1 smaller phase-product calls plus classical interpolation arithmetic, and lowers the result to primitive LowGates."
  },
  "QFT": {
   "role": "subroutine",
   "subtitle": "recursive Quantum Fourier Transform",
   "summary": "Splits a register's QFT into two half-size recursive QFTs joined by an unsigned phase-product macro (built from PhaseProduct) and a radix reversal, plus the workspace budget model letting both recursive halves safely reuse the same reserve pools."
  },
  "ModularExponentiation": {
   "role": "subroutine",
   "subtitle": "Algorithm 1: in-place modular multiplication/exponentiation",
   "summary": "Approximates |x><c*x mod N>|0> and, by recursing over the exponent register, modular exponentiation, via a fractional-load-and-cleanup circuit built from QFT-based phase products and an inverse-QFT comparator, with a quantitative error bound uniform in the precision parameter eta."
  },
  "Compiler": {
   "role": "subroutine",
   "subtitle": "Gate to LowGate lowering",
   "summary": "Policy.lowerGate lowers a Gate circuit to a LowGate program by sending each QFT, phase-product and modular-arithmetic block to its subroutine's lowerer, given a proof that every block has the workspace it needs. Policy.lowerGate_correct: for an admissible policy, the lowered program acts on a clean state exactly as the gate does."
  },
  "Shor": {
   "role": "assembly",
   "subtitle": "order-finding assembly and correctness",
   "summary": "Builds the concrete approximate order-finding circuit from the three subroutines above, proves workspace readiness for the whole lowered circuit, and proves the two results that make it Shor's algorithm: the ideal circuit's success-probability lower bound and the transfer of that bound across the modular-exponentiation implementation's approximation error. That transfer costs a loss term in the per-step precision eta, so the lowered result is stated twice — once with eta free, and once at a precision tied to N, where half the ideal bound provably survives."
  },
  "Reference": {
   "role": "submission",
   "subtitle": "the concrete submission",
   "summary": "Makes every choice the folders above leave abstract (interpolation-point program, physical register layout, precision schedule) into one deterministic, fully computable construction, and packages the result as the framework's ShorImplementation value — including the 2048-bit-benchmark trial count and gate count the leaderboard scores on."
  },
  "Shor/Main.lean": {
   "role": "assembly",
   "subtitle": "the two final theorems",
   "summary": "Shor_correct_approx_lowered_uniform (the fully lowered circuit, per-step precision eta left free, constant K ≤ 1600 — what Reference/ consumes) and Shor_correct_approx_lowered (at any eta below shorPrecision N x — a closed form with no hidden constant, concluding kappa / (2 log(log2 N + 1))). The last is the one to cite for the bound itself: the uniform form subtracts a loss that does not shrink as N grows, so it says something only once eta is tied to N. This file is the only way into Shor/Proofs from outside Shor/."
  },
  "Framework/Quantum": {
   "role": "framework",
   "subtitle": "registers and measurement"
  },
  "Framework/AbstractMachine": {
   "role": "framework",
   "subtitle": "Gate and LowGate languages"
  },
  "Framework/Semantics": {
   "role": "framework",
   "subtitle": "abstract evaluation classes"
  },
  "Framework/ToomCookTable.lean": {
   "role": "framework",
   "subtitle": "what a submission is",
   "summary": "ShorSubmission: an arithmetic program over k limb registers plus the interpolation points its phaseProduct checkpoints evaluate at, with four decidable side conditions that make the pair admissible. Imports Mathlib and nothing else, so the acceptance test can be read without the construction that satisfies it."
  },
  "Framework/Gatecount": {
   "role": "framework",
   "subtitle": "the cost-model interface"
  },
  "Framework/Policy.lean": {
   "role": "framework",
   "subtitle": "what a policy submission is",
   "summary": "ShorPolicySubmission: a list of Toom-Cook tables indexed by operand width, each band carrying the same four side conditions a single table does, plus one decidable field saying the thresholds strictly decrease. choose picks the first band at or below a width and none is the schoolbook leaf; constPolicy makes a table submission the one-band policy at threshold 0. Imports Framework/ToomCookTable.lean and nothing else."
  },
  "QubitCount": {
   "role": "resource",
   "subtitle": "the peak qubit count",
   "summary": "Walks the lowered order-finding circuit keeping the set of live qubits and proves an exact formula for its peak, for any admissible policy and for the two balanced circuits of Reference/Balanced. The count is not LowGate.qubitCount (every qubit ever touched): a phase-product recursion's children each own a reserve but run one after another. At 2048 bits the peak is 19,319 for the plain circuit and 17,291 for the balanced one."
  }
 },
 "views": {
  "": {
   "columns": [
    [
     "Framework"
    ],
    [
     "PhaseProduct"
    ],
    [
     "QFT",
     "PhaseTripleProduct"
    ],
    [
     "ModularExponentiation"
    ],
    [
     "Compiler"
    ],
    [
     "Shor"
    ],
    [
     "Reference"
    ],
    [
     "QubitCount"
    ]
   ],
   "edges": [
    {
     "from": "Framework",
     "to": "PhaseTripleProduct",
     "emphasis": "secondary"
    },
    {
     "from": "PhaseProduct",
     "to": "PhaseTripleProduct",
     "emphasis": "secondary"
    },
    {
     "from": "Framework",
     "to": "PhaseProduct",
     "emphasis": "primary",
     "label": "vocabulary: Reg, Gate, LowGate, QSemantics",
     "why": "Every subroutine is built over Framework's register, gate, and semantic vocabulary; PhaseProduct is where the site draws that arrow once rather than fanning it to all four subsystems."
    },
    {
     "from": "PhaseProduct",
     "to": "QFT",
     "emphasis": "primary",
     "theorem": "lowerSignedPhaseProduct_correct",
     "label": "phase product for the QFT split",
     "why": "QFT's recursive split needs an unsigned phase-product macro between the two half-size QFTs; that macro's lowered correctness comes from PhaseProduct/Main.lean."
    },
    {
     "from": "PhaseProduct",
     "to": "ModularExponentiation",
     "emphasis": "secondary"
    },
    {
     "from": "QFT",
     "to": "ModularExponentiation",
     "emphasis": "primary",
     "label": "QFT-based phase products, IQFT comparator",
     "why": "ModularExponentiation's approximate circuit is built from QFT-based phase products and an inverse-QFT comparator."
    },
    {
     "from": "ModularExponentiation",
     "to": "Shor",
     "emphasis": "primary",
     "theorem": "modExpApprox_correct",
     "label": "modExpApprox_correct",
     "why": "Shor's approximate correctness theorem transfers this eta-independent distance bound into a success-probability lower bound for the full lowered circuit."
    },
    {
     "from": "QFT",
     "to": "Shor",
     "emphasis": "secondary"
    },
    {
     "from": "QFT",
     "to": "Compiler",
     "emphasis": "secondary"
    },
    {
     "from": "PhaseProduct",
     "to": "Compiler",
     "emphasis": "secondary"
    },
    {
     "from": "Compiler",
     "to": "Shor",
     "emphasis": "primary",
     "theorem": "lowerGate_correct",
     "label": "Policy.lowerGate",
     "why": "Shor's lowered circuit is Policy.lowerGate applied to the order-finding circuit, and its success bound transfers to the lowered program through Policy.lowerGate_correct."
    },
    {
     "from": "Shor",
     "to": "Reference",
     "emphasis": "primary",
     "theorem": "Shor_correct_approx_lowered_uniform",
     "label": "Shor_correct_approx_lowered_uniform",
     "why": "Reference discharges this theorem's hypotheses concretely (layout, precision, readiness), and the workspace proof LoweredShorReady.workspace, and takes its constant up to K = 1600 by monotonicity to get one honest success probability for referenceShorImplementation, a value of the ShorImplementation structure Reference/Contract.lean defines. It consumes Shor/Main.lean and Shor/Statement.lean, not Shor/Proofs directly."
    },
    {
     "from": "Reference",
     "to": "QubitCount",
     "emphasis": "primary",
     "label": "the circuits it counts"
    },
    {
     "from": "Compiler",
     "to": "QubitCount",
     "emphasis": "secondary"
    }
   ]
  },
  "Framework": {
   "columns": [
    [
     "Framework/Quantum"
    ],
    [
     "Framework/AbstractMachine"
    ],
    [
     "Framework/Semantics",
     "Framework/Gatecount"
    ],
    [
     "Framework/ToomCookTable.lean"
    ],
    [
     "Framework/Policy.lean"
    ]
   ],
   "edges": [
    {
     "from": "Framework/Quantum",
     "to": "Framework/AbstractMachine",
     "emphasis": "primary",
     "theorem": "Reg",
     "label": "Reg as gate operand",
     "why": "Gate and LowGate syntax (Framework/AbstractMachine) is built over the Reg register type Quantum defines."
    },
    {
     "from": "Framework/AbstractMachine",
     "to": "Framework/Semantics",
     "emphasis": "primary",
     "theorem": "LowGate",
     "label": "LowerGateClass over LowGate",
     "why": "LowerGateClass and GateSemanticsCore (Framework/Semantics) give evaluation meaning to the LowGate/Gate syntax AbstractMachine defines."
    },
    {
     "from": "Framework/AbstractMachine",
     "to": "Framework/Gatecount",
     "emphasis": "primary",
     "theorem": "gateCount",
     "label": "gateCount over LowGate",
     "why": "The cost model in Framework/Gatecount is a fold over exactly the LowGate syntax AbstractMachine defines."
    },
    {
     "from": "Framework/ToomCookTable.lean",
     "to": "Framework/Policy.lean",
     "emphasis": "primary",
     "theorem": "ShorLoweringSetup",
     "label": "a policy is a list of tables",
     "why": "A policy band is one Toom-Cook table, so Policy.lean is stated over ToomCookTable.lean's vocabulary and records. The import runs one way only: a reader of the single-table specification never has to read the policy."
    }
   ]
  },
  "PhaseProduct": {
   "columns": [
    [
     "PhaseProduct/Statement.lean"
    ],
    [
     "PhaseProduct/Proofs"
    ],
    [
     "PhaseProduct/Main.lean"
    ]
   ],
   "edges": [
    {
     "from": "PhaseProduct/Statement.lean",
     "to": "PhaseProduct/Proofs",
     "emphasis": "primary",
     "label": "definitions and what is claimed"
    },
    {
     "from": "PhaseProduct/Proofs",
     "to": "PhaseProduct/Main.lean",
     "emphasis": "primary",
     "theorem": "lowerSignedPhaseProduct_correct",
     "label": "compiler + lowering assembled"
    },
    {
     "from": "PhaseProduct/Statement.lean",
     "to": "PhaseProduct/Main.lean",
     "emphasis": "secondary"
    }
   ]
  },
  "QFT": {
   "columns": [
    [
     "QFT/Statement.lean"
    ],
    [
     "QFT/Proofs"
    ],
    [
     "QFT/Main.lean"
    ]
   ],
   "edges": [
    {
     "from": "QFT/Statement.lean",
     "to": "QFT/Proofs",
     "emphasis": "primary",
     "label": "the lowering and its workspace model",
     "why": "Statement.lean defines the workspace budget, the plans and the lowered QFT; Proofs/ proves the split identity and that the lowering is correct."
    },
    {
     "from": "QFT/Proofs",
     "to": "QFT/Main.lean",
     "emphasis": "primary",
     "theorem": "lowerQFT_correct",
     "label": "recursive lowering assembled",
     "why": "Main.lean packages the plan-semantics and readiness proofs from Proofs/ into the single lowering-correctness theorem."
    },
    {
     "from": "QFT/Statement.lean",
     "to": "QFT/Main.lean",
     "emphasis": "primary",
     "label": "what is claimed",
     "why": "Statement.lean states LowerQFTCorrect and Policy.LowerQFTCorrect and imports nothing else from QFT/; Main.lean proves them."
    }
   ]
  },
  "ModularExponentiation": {
   "columns": [
    [
     "ModularExponentiation/Statement.lean"
    ],
    [
     "ModularExponentiation/Proofs"
    ],
    [
     "ModularExponentiation/Main.lean"
    ]
   ],
   "edges": [
    {
     "from": "ModularExponentiation/Statement.lean",
     "to": "ModularExponentiation/Proofs",
     "emphasis": "primary",
     "label": "circuit and claims",
     "why": "Proofs/ proves the distance bound Statement.lean states, for the circuit Statement.lean defines."
    },
    {
     "from": "ModularExponentiation/Proofs",
     "to": "ModularExponentiation/Main.lean",
     "emphasis": "primary",
     "theorem": "modExpApprox_correct",
     "label": "modExpApprox_correct",
     "why": "Main.lean combines the staged Algorithm-1 approximation proofs in Proofs/ into one eta-independent distance bound; Proofs/ is proof-only, so Main.lean is the only route out of ModularExponentiation/."
    },
    {
     "from": "ModularExponentiation/Statement.lean",
     "to": "ModularExponentiation/Main.lean",
     "emphasis": "secondary"
    }
   ]
  },
  "Compiler": {
   "columns": [
    [
     "Compiler/Statement.lean"
    ],
    [
     "Compiler/Proofs"
    ],
    [
     "Compiler/Main.lean"
    ]
   ],
   "edges": [
    {
     "from": "Compiler/Statement.lean",
     "to": "Compiler/Proofs",
     "emphasis": "primary",
     "why": "Proofs/ proves the correctness claim Statement.lean states, by induction over the gate, and gives the single-table forms used by Emit/, the gate-count proofs and Reference/."
    },
    {
     "from": "Compiler/Proofs",
     "to": "Compiler/Main.lean",
     "emphasis": "primary",
     "theorem": "lowerGate_correct",
     "label": "Policy.lowerGate_correct",
     "why": "Main.lean packages the proof as the claim Policy.LowerGateCorrect; Proofs/ is proof-only, so Main.lean is the only route out of Compiler/."
    },
    {
     "from": "Compiler/Statement.lean",
     "to": "Compiler/Main.lean",
     "emphasis": "secondary"
    }
   ]
  },
  "Shor": {
   "columns": [
    [
     "Shor/Statement.lean"
    ],
    [
     "Shor/Proofs"
    ],
    [
     "Shor/Main.lean"
    ]
   ],
   "edges": [
    {
     "from": "Shor/Statement.lean",
     "to": "Shor/Proofs",
     "emphasis": "primary",
     "why": "Proofs/ proves the lemmas behind the propositions Statement.lean states."
    },
    {
     "from": "Shor/Proofs",
     "to": "Shor/Main.lean",
     "emphasis": "primary",
     "theorem": "Shor_correct_approx_lowered",
     "label": "Shor_correct_approx_lowered",
     "why": "Main.lean combines the ideal correctness, approximation transfer, and classical reduction proofs from Proofs/ into the propositions Statement.lean states — Proofs/ is proof-only, so Main.lean is the only route out of Shor/."
    },
    {
     "from": "Shor/Statement.lean",
     "to": "Shor/Main.lean",
     "emphasis": "secondary"
    }
   ]
  },
  "Reference": {
   "columns": [
    [
     "Reference/Contract.lean"
    ],
    [
     "Reference/Balanced"
    ],
    [
     "Reference/Standard"
    ]
   ],
   "edges": [
    {
     "from": "Reference/Contract.lean",
     "to": "Reference/Standard",
     "emphasis": "primary",
     "theorem": "referenceShorImplementation",
     "label": "the contract it fills"
    },
    {
     "from": "Reference/Balanced",
     "to": "Reference/Standard",
     "emphasis": "primary",
     "label": "the balancing pass"
    }
   ]
  }
 }
}
