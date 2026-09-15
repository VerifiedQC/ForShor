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
// dashed — Shared's edges). A view with no `views[path]` entry (or an empty
// `edges` list) falls back to an automatic transitive reduction of its full
// import DAG, drawn as primary with no labels.
window.ANNOTATIONS = {
 "repo": { "owner": "VerifiedQC", "repo": "ForShor", "branch": "main" },
 "intro": {
  "title": "ShorVerification",
  "summary": "Framework/ is the specification: it defines what a Shor order-finding submission is (Framework/Submission.lean's ShorImplementation structure) and the vocabulary every proof is stated in. Everything else is the submission: three independently-verified subroutines (PhaseProduct, QFT, ModularExponentiation) feed the Shor assembly, which is scored by GateCount and packaged as the concrete Reference implementation. Shared is a lemma library used by all three subroutines, not a step in the story.",
  "spine": ["Reference", "Shor", "ModularExponentiation", "QFT", "PhaseProduct"]
 },
 "roles": {
  "framework": { "color": "#2368b8", "label": "Framework" },
  "subroutine": { "color": "#b46519", "label": "Subroutine" },
  "assembly": { "color": "#be3f50", "label": "Assembly" },
  "resource": { "color": "#7d6a13", "label": "Resource estimate" },
  "submission": { "color": "#218263", "label": "Submission" },
  "support": { "color": "#8793a6", "label": "Support library" }
 },
 "layers": {
  "math": { "color": "#218263", "label": "Math" },
  "definitions": { "color": "#6d55b8", "label": "Definitions" },
  "lowering": { "color": "#6d55b8", "label": "Lowering" },
  "spec": { "color": "#b46519", "label": "Spec" },
  "proofs": { "color": "#2368b8", "label": "Proofs" },
  "main": { "color": "#be3f50", "label": "Main" }
 },
 "nodes": {
  "Framework": {
   "role": "framework",
   "subtitle": "the contract",
   "summary": "Defines what a Shor order-finding submission is: registers and the Gate/LowGate languages, the QSemantics/MeasureClass semantic interfaces, the LowGate cost model, and Framework/Submission.lean's ShorImplementation structure that every Implementation/ folder exists to build one value of."
  },
  "Shared": {
   "role": "support",
   "subtitle": "lemma library",
   "summary": "Derived register/encoding laws, QSemantics/evaluator algebra, Hadamard-superposition facts, per-gate semantic-class lemmas, and lowered-gate evaluation rewrites used by PhaseProduct, QFT, ModularExponentiation, and Shor. Imports nothing from any of them, and proves no correctness theorem of its own."
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
  "Shor": {
   "role": "assembly",
   "subtitle": "order-finding assembly and correctness",
   "summary": "Builds the concrete approximate order-finding circuit from the three subroutines above, proves workspace readiness for the whole lowered circuit, and proves the two results that make it Shor's algorithm: the ideal circuit's success-probability lower bound and the transfer of that bound across the modular-exponentiation implementation's approximation error."
  },
  "GateCount": {
   "role": "resource",
   "subtitle": "O(n^(2+eps)) resource estimate",
   "summary": "Gives LowGate a concrete cost model, bounds PhaseProduct's and QFT's lowered gate counts at a shared comparison rate, sums one modular-multiplication core's bound over the whole exponentiation, and chooses the recursion arity k large enough that the rate collapses to 2+epsilon."
  },
  "Reference": {
   "role": "submission",
   "subtitle": "the concrete submission",
   "summary": "Makes every choice the folders above leave abstract (interpolation-point program, physical register layout, precision schedule) into one deterministic, fully computable construction, and packages the result as the framework's ShorImplementation value — including the 2048-bit-benchmark trial count and gate count the leaderboard scores on."
  },
  "Framework/Quantum": { "role": "framework", "subtitle": "registers and measurement" },
  "Framework/AbstractMachine": { "role": "framework", "subtitle": "Gate and LowGate languages" },
  "Framework/Semantics": { "role": "framework", "subtitle": "abstract evaluation classes" },
  "Framework/Instantiation": { "role": "framework", "subtitle": "one concrete QSemantics instance" },
  "Framework/Gatecount": { "role": "framework", "subtitle": "the cost-model interface" },
  "Framework/Math": { "role": "framework", "subtitle": "classical order/factoring definitions" },
  "Framework/Submission.lean": {
   "role": "framework",
   "subtitle": "the public boundary",
   "summary": "ShorImplementation asks for one LowGate circuit per valid order-finding instance, a declared success probability, a trial count amplifying that probability to 99% on 2048-bit moduli, and proofs that both are honest."
  }
 },
 "views": {
  "": {
   "columns": [["Framework", "Shared"], ["PhaseProduct"], ["QFT"], ["ModularExponentiation"], ["Shor"], ["GateCount"], ["Reference"]],
   "edges": [
    { "from": "Framework", "to": "PhaseProduct", "emphasis": "primary", "label": "vocabulary: Reg, Gate, LowGate, QSemantics", "why": "Every subroutine is built over Framework's register, gate, and semantic vocabulary; PhaseProduct is where the site draws that arrow once rather than fanning it to all four subsystems." },
    { "from": "Framework", "to": "Reference", "emphasis": "primary", "theorem": "ShorImplementation", "label": "ShorImplementation, the submission structure", "why": "Everything under Implementation/ exists to build one concrete value of Framework/Submission.lean's ShorImplementation structure and hand it to the framework; Reference is where that value is actually assembled." },
    { "from": "Framework", "to": "Shared", "emphasis": "dim" },
    { "from": "PhaseProduct", "to": "QFT", "emphasis": "primary", "theorem": "lowerSignedPhaseProduct_correct", "label": "phase product for the QFT split", "why": "QFT's recursive split needs an unsigned phase-product macro between the two half-size QFTs; that macro's lowered correctness comes from PhaseProduct/Main.lean." },
    { "from": "PhaseProduct", "to": "ModularExponentiation", "emphasis": "secondary" },
    { "from": "QFT", "to": "ModularExponentiation", "emphasis": "primary", "label": "QFT-based phase products, IQFT comparator", "why": "ModularExponentiation's approximate circuit is built from QFT-based phase products and an inverse-QFT comparator." },
    { "from": "ModularExponentiation", "to": "Shor", "emphasis": "primary", "theorem": "modExpApprox_correct", "label": "modExpApprox_correct", "why": "Shor's approximate correctness theorem transfers this eta-independent distance bound into a success-probability lower bound for the full lowered circuit." },
    { "from": "QFT", "to": "Shor", "emphasis": "secondary" },
    { "from": "Shor", "to": "GateCount", "emphasis": "primary", "theorem": "lowerGate_correctness", "label": "the LowGate program being counted", "why": "GateCount counts gates in the same lowered circuit (orderFindingApproxLow, built via Shor/Lowering's lowerGate) whose semantics lowerGate_correctness verifies; correctness and resource estimation share the circuit but not the proof." },
    { "from": "Shor", "to": "Reference", "emphasis": "primary", "theorem": "Shor_correct_approx_lowered_uniform", "label": "Shor_correct_approx_lowered_uniform", "why": "Reference discharges this theorem's hypotheses concretely (layout, precision, readiness) to get one honest success probability for referenceShorImplementation." },
    { "from": "GateCount", "to": "Reference", "emphasis": "primary", "theorem": "exists_shorGateCountBound", "label": "exists_shorGateCountBound", "why": "Reference2048Headline.lean instantiates this existential at the 2048-bit benchmark to compute the headline gate count the leaderboard scores on." },
    { "from": "PhaseProduct", "to": "GateCount", "emphasis": "secondary" }
   ]
  },
  "Framework": {
   "columns": [["Framework/Quantum", "Framework/Math"], ["Framework/AbstractMachine"], ["Framework/Semantics", "Framework/Gatecount"], ["Framework/Submission.lean", "Framework/Instantiation"]],
   "edges": [
    { "from": "Framework/Quantum", "to": "Framework/AbstractMachine", "emphasis": "primary", "theorem": "Reg", "label": "Reg as gate operand", "why": "Gate and LowGate syntax (Framework/AbstractMachine) is built over the Reg register type Quantum defines." },
    { "from": "Framework/AbstractMachine", "to": "Framework/Semantics", "emphasis": "primary", "theorem": "LowGate", "label": "LowerGateClass over LowGate", "why": "LowerGateClass and GateSemanticsCore (Framework/Semantics) give evaluation meaning to the LowGate/Gate syntax AbstractMachine defines." },
    { "from": "Framework/Semantics", "to": "Framework/Submission.lean", "emphasis": "primary", "theorem": "LowerGateClass", "label": "evaluating the submitted circuit", "why": "ShorImplementation's correct field states that evaluating the submitted LowGate program (via LowerGateClass) matches the framework's order-finding specification." },
    { "from": "Framework/AbstractMachine", "to": "Framework/Gatecount", "emphasis": "primary", "theorem": "gateCount", "label": "gateCount over LowGate", "why": "The cost model in Framework/Gatecount is a fold over exactly the LowGate syntax AbstractMachine defines." },
    { "from": "Framework/Gatecount", "to": "Framework/Submission.lean", "emphasis": "secondary" },
    { "from": "Framework/Math", "to": "Framework/Submission.lean", "emphasis": "primary", "label": "order-finding spec", "why": "ShorImplementation's correctness statement is phrased in terms of the classical order/factoring definitions Framework/Math supplies." },
    { "from": "Framework/Quantum", "to": "Framework/Instantiation", "emphasis": "secondary" },
    { "from": "Framework/Semantics", "to": "Framework/Instantiation", "emphasis": "secondary" }
   ]
  },
  "PhaseProduct": {
   "columns": [["PhaseProduct/Math"], ["PhaseProduct/Compiler", "PhaseProduct/Gates"], ["PhaseProduct/Lowering"], ["PhaseProduct/Spec"], ["PhaseProduct/Proofs"], ["PhaseProduct/Main.lean"]],
   "edges": [
    { "from": "PhaseProduct/Math", "to": "PhaseProduct/Compiler", "emphasis": "primary", "label": "Toom-Cook points and interpolation", "why": "The compiler's layout and coefficient bookkeeping is built directly over the Toom-Cook interpolation algebra and table-generation coverage facts in Math/." },
    { "from": "PhaseProduct/Compiler", "to": "PhaseProduct/Lowering", "emphasis": "primary", "label": "compiled gates → plans", "why": "The recursive lowering plans are built to lower exactly the compiled signed/controlled-signed phase-product gates Compiler/ defines." },
    { "from": "PhaseProduct/Gates", "to": "PhaseProduct/Lowering", "emphasis": "secondary" },
    { "from": "PhaseProduct/Lowering", "to": "PhaseProduct/Spec", "emphasis": "primary", "label": "PhaseLoweringReady", "why": "Spec/Readiness.lean states the readiness precondition the recursive lowering plans in Lowering/ must satisfy." },
    { "from": "PhaseProduct/Spec", "to": "PhaseProduct/Proofs", "emphasis": "primary", "label": "what is claimed", "why": "Proofs/ discharges exactly the readiness and cleanliness assertions Spec/ states." },
    { "from": "PhaseProduct/Proofs", "to": "PhaseProduct/Main.lean", "emphasis": "primary", "theorem": "lowerSignedPhaseProduct_correct", "label": "compiler + lowering assembled", "why": "Main.lean states the final theorem by combining the compiler correctness and lowering-readiness proofs developed in Proofs/." },
    { "from": "PhaseProduct/Spec", "to": "PhaseProduct/Main.lean", "emphasis": "secondary" }
   ]
  },
  "QFT": {
   "columns": [["QFT/Split.lean"], ["QFT/Lowering"], ["QFT/Spec"], ["QFT/Proofs"], ["QFT/Main.lean"]],
   "edges": [
    { "from": "QFT/Split.lean", "to": "QFT/Lowering", "emphasis": "primary", "label": "split convention", "why": "The recursive lowering plan follows the left/right split and radix-reversal convention Split.lean states." },
    { "from": "QFT/Lowering", "to": "QFT/Spec", "emphasis": "primary", "label": "QFTLoweringReady", "why": "Spec/Readiness.lean states the readiness precondition the recursive QFT lowering plan in Lowering/ must satisfy." },
    { "from": "QFT/Spec", "to": "QFT/Proofs", "emphasis": "primary", "why": "Proofs/ discharges exactly the readiness and cleanliness assertions Spec/ states." },
    { "from": "QFT/Proofs", "to": "QFT/Main.lean", "emphasis": "primary", "theorem": "lowerQFT_correct", "label": "recursive lowering assembled", "why": "Main.lean packages the plan-semantics and readiness proofs from Proofs/ into the single lowering-correctness theorem." },
    { "from": "QFT/Spec", "to": "QFT/Main.lean", "emphasis": "secondary" }
   ]
  },
  "ModularExponentiation": {
   "columns": [["ModularExponentiation/Circuit", "ModularExponentiation/Math"], ["ModularExponentiation/Lowering", "ModularExponentiation/Spec"], ["ModularExponentiation/Proofs"], ["ModularExponentiation/Main.lean"]],
   "edges": [
    { "from": "ModularExponentiation/Circuit", "to": "ModularExponentiation/Lowering", "emphasis": "primary", "label": "Step 3 constant arithmetic", "why": "The constant-arithmetic subtraction stage Lowering/ProvesCorrect targets is exactly the circuit Circuit/ defines." },
    { "from": "ModularExponentiation/Circuit", "to": "ModularExponentiation/Spec", "emphasis": "primary", "label": "validity and config records", "why": "Spec/'s validity predicates and configuration records are stated over the circuit and workspace Circuit/ defines." },
    { "from": "ModularExponentiation/Lowering", "to": "ModularExponentiation/Proofs", "emphasis": "secondary" },
    { "from": "ModularExponentiation/Spec", "to": "ModularExponentiation/Proofs", "emphasis": "primary", "why": "Proofs/ discharges exactly the validity and precision assertions Spec/ states." },
    { "from": "ModularExponentiation/Math", "to": "ModularExponentiation/Proofs", "emphasis": "secondary" },
    { "from": "ModularExponentiation/Proofs", "to": "ModularExponentiation/Main.lean", "emphasis": "primary", "theorem": "modExpApprox_correct", "label": "modExpApprox_correct", "why": "Main.lean combines the staged Algorithm-1 approximation proofs in Proofs/ into one eta-independent distance bound." },
    { "from": "ModularExponentiation/Spec", "to": "ModularExponentiation/Main.lean", "emphasis": "secondary" }
   ]
  },
  "Shor": {
   "columns": [["Shor/Lowering", "Shor/Math"], ["Shor/Circuit"], ["Shor/Spec"], ["Shor/Proofs"], ["Shor/Main.lean"]],
   "edges": [
    { "from": "Shor/Lowering", "to": "Shor/Circuit", "emphasis": "primary", "theorem": "lowerGate", "label": "lowerGate", "why": "The order-finding circuit is assembled from the same lowered gates Shor/Lowering's lowerGate produces." },
    { "from": "Shor/Circuit", "to": "Shor/Spec", "emphasis": "primary", "label": "orderFindingApprox", "why": "Spec/'s setup and cleanliness assertions are stated over the concrete order-finding circuit orderFindingApprox Circuit/ defines." },
    { "from": "Shor/Spec", "to": "Shor/Proofs", "emphasis": "primary", "why": "Proofs/ discharges exactly the setup and readiness assertions Spec/ states." },
    { "from": "Shor/Math", "to": "Shor/Proofs", "emphasis": "secondary" },
    { "from": "Shor/Proofs", "to": "Shor/Main.lean", "emphasis": "primary", "theorem": "Shor_end_to_end_factoring", "label": "Shor_end_to_end_factoring", "why": "Main.lean combines the ideal correctness, approximation transfer, and classical reduction proofs from Proofs/ into the complete factoring statement, and the fully-lowered Shor_correct_approx_lowered_uniform that Reference/ actually discharges." },
    { "from": "Shor/Spec", "to": "Shor/Main.lean", "emphasis": "secondary" }
   ]
  },
  "GateCount": {
   "columns": [["GateCount/Definitions.lean"], ["GateCount/PhaseProduct", "GateCount/Lemmas"], ["GateCount/QFT_GateCount.lean"], ["GateCount/Shor_GateCount.lean"]],
   "edges": [
    { "from": "GateCount/Definitions.lean", "to": "GateCount/Lemmas", "emphasis": "secondary" },
    { "from": "GateCount/Definitions.lean", "to": "GateCount/PhaseProduct", "emphasis": "primary", "label": "the cost model", "why": "PhaseProduct/'s recurrence bounds are proved directly over the LowGateCostModel fold Definitions.lean defines." },
    { "from": "GateCount/Lemmas", "to": "GateCount/QFT_GateCount.lean", "emphasis": "secondary" },
    { "from": "GateCount/PhaseProduct", "to": "GateCount/QFT_GateCount.lean", "emphasis": "primary", "label": "phase-product recurrence bound", "why": "The QFT gate-count recurrence is solved by applying PhaseProduct/'s component bound to the cross-term phase product." },
    { "from": "GateCount/QFT_GateCount.lean", "to": "GateCount/Shor_GateCount.lean", "emphasis": "primary", "theorem": "exists_shorGateCountBound", "label": "exists_shorGateCountBound", "why": "The final theorem combines the QFT and phase-product component bounds with the modular-exponentiation count, then picks k so the rate collapses to n^(2+epsilon)." }
   ]
  },
  "Shared": {
   "columns": [["Shared/Registers.lean", "Shared/States.lean"], ["Shared/GateLaws.lean", "Shared/Hadamard.lean"], ["Shared/LowGateEval.lean"], ["Shared/QftPhase.lean", "Shared/Measurement.lean"]],
   "edges": [
    { "from": "Shared/Registers.lean", "to": "Shared/GateLaws.lean", "emphasis": "secondary" },
    { "from": "Shared/Registers.lean", "to": "Shared/Hadamard.lean", "emphasis": "secondary" },
    { "from": "Shared/Registers.lean", "to": "Shared/LowGateEval.lean", "emphasis": "secondary" },
    { "from": "Shared/States.lean", "to": "Shared/GateLaws.lean", "emphasis": "secondary" },
    { "from": "Shared/States.lean", "to": "Shared/Hadamard.lean", "emphasis": "secondary" },
    { "from": "Shared/States.lean", "to": "Shared/LowGateEval.lean", "emphasis": "secondary" },
    { "from": "Shared/GateLaws.lean", "to": "Shared/LowGateEval.lean", "emphasis": "secondary" }
   ]
  },
  "Reference": {
   "columns": [["Reference/ReferencePrecision.lean"], ["Reference/ReferenceLayout.lean"], ["Reference/ReferenceReadiness.lean"], ["Reference/ShorProgram.lean"], ["Reference/ReferenceShorImplementation.lean"], ["Reference/Reference2048Headline.lean", "Reference/StandardLoweringSetup.lean"]],
   "edges": [
    { "from": "Reference/ReferencePrecision.lean", "to": "Reference/ReferenceLayout.lean", "emphasis": "secondary" },
    { "from": "Reference/ReferenceLayout.lean", "to": "Reference/ReferenceReadiness.lean", "emphasis": "primary", "label": "concrete layout", "why": "Readiness discharges the implementation-specific readiness obligations against the concrete register layout ReferenceLayout.lean builds." },
    { "from": "Reference/ReferenceReadiness.lean", "to": "Reference/ShorProgram.lean", "emphasis": "primary", "label": "readiness discharged", "why": "ShorProgram.lean's circuit family relies on the readiness proofs ReferenceReadiness.lean establishes for the concrete layout and precision schedule." },
    { "from": "Reference/ShorProgram.lean", "to": "Reference/ReferenceShorImplementation.lean", "emphasis": "primary", "theorem": "referenceShorImplementation", "label": "referenceShorImplementation", "why": "referenceShorImplementation packages ShorProgram's concrete, computable circuit family together with the layout/readiness/precision proofs into the actual ShorImplementation value." },
    { "from": "Reference/ReferenceShorImplementation.lean", "to": "Reference/Reference2048Headline.lean", "emphasis": "primary", "label": "headline 2048-bit numbers", "why": "Reference2048Headline.lean instantiates referenceShorImplementation's fields at the 2048-bit benchmark modulus family to compute the headline trial count and gate count." }
   ]
  }
 }
}
