// Curated skin on top of the generated docs/data/graph.js skeleton.
//
// This file must be a single strict-JSON object literal assigned to
// window.ANNOTATIONS (no comments or trailing commas *inside* the object;
// scripts/gen_docs_graph.py --check parses it as JSON). Every bridge names a
// real declaration and must line up with a real import edge in graph.js, or
// --check fails the build.
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
 "bridges": [
  {
   "from": "Framework", "to": "Reference",
   "theorem": "ShorImplementation",
   "label": "submission structure",
   "why": "Everything under Implementation/ exists to build one concrete value of Framework/Submission.lean's ShorImplementation structure and hand it to the framework; Reference is where that value is actually assembled."
  },
  {
   "from": "PhaseProduct", "to": "QFT",
   "theorem": "lowerSignedPhaseProduct_correct",
   "label": "phase-product circuit for the QFT split",
   "why": "QFT's recursive split needs an unsigned phase-product macro between the two half-size QFTs; that macro's lowered correctness comes from PhaseProduct/Main.lean."
  },
  {
   "from": "PhaseProduct", "to": "Shor",
   "theorem": "lowerSignedPhaseProduct_correct",
   "label": "signed phase product for modular arithmetic",
   "why": "Shor's assembled circuit uses signed and controlled-signed phase products directly (via ModularExponentiation and QFT), so its readiness/correctness proofs ultimately invoke PhaseProduct's lowering theorem."
  },
  {
   "from": "QFT", "to": "Shor",
   "theorem": "lowerQFT_correct",
   "label": "QFT stage of order finding",
   "why": "The order-finding circuit's inverse-QFT stage is exactly the lowered QFT this theorem verifies."
  },
  {
   "from": "ModularExponentiation", "to": "Shor",
   "theorem": "modExpApprox_correct",
   "label": "modular exponentiation error bound",
   "why": "Shor's approximate correctness theorem transfers this eta-independent distance bound into a success-probability lower bound for the full lowered circuit."
  },
  {
   "from": "Shor", "to": "Reference",
   "theorem": "Shor_correct_approx_lowered_uniform",
   "label": "lowered order-finding correctness",
   "why": "Reference discharges this theorem's hypotheses concretely (layout, precision, readiness) to get one honest success probability for referenceShorImplementation."
  },
  {
   "from": "GateCount", "to": "Reference",
   "theorem": "exists_shorGateCountBound",
   "label": "leaderboard gate-count bound",
   "why": "Reference2048Headline.lean instantiates this existential at the 2048-bit benchmark to compute the headline gate count the leaderboard scores on."
  },
  {
   "from": "Shor", "to": "GateCount",
   "theorem": "lowerGate_correctness",
   "label": "the exact LowGate program being counted",
   "why": "GateCount counts gates in the same lowered circuit (orderFindingApproxLow, built via Shor/Lowering's lowerGate) whose semantics lowerGate_correctness verifies; correctness and resource estimation share the circuit but not the proof."
  },
  {
   "from": "Framework/Quantum", "to": "Framework/AbstractMachine",
   "theorem": "Reg",
   "label": "register operands for gate syntax",
   "why": "Gate and LowGate syntax (Framework/AbstractMachine) is built over the Reg register type Quantum defines."
  },
  {
   "from": "Framework/Quantum", "to": "Framework/Instantiation",
   "theorem": "QSemantics",
   "label": "the interface Instantiation implements",
   "why": "Framework/Instantiation's ConcreteQSemantics is the one concrete instance of Quantum's abstract QSemantics class that every proof ultimately runs against."
  },
  {
   "from": "Framework/Quantum", "to": "Framework/Submission.lean",
   "theorem": "MeasureClass",
   "label": "success-probability interface",
   "why": "ShorImplementation's declared successProbability field is stated in terms of the generalized measurement interface MeasureClass defines."
  },
  {
   "from": "Framework/AbstractMachine", "to": "Framework/Semantics",
   "theorem": "LowGate",
   "label": "the language semantics attaches to",
   "why": "LowerGateClass and GateSemanticsCore (Framework/Semantics) give evaluation meaning to the LowGate/Gate syntax AbstractMachine defines."
  },
  {
   "from": "Framework/AbstractMachine", "to": "Framework/Gatecount",
   "theorem": "gateCount",
   "label": "counting the target language",
   "why": "The cost model in Framework/Gatecount is a fold over exactly the LowGate syntax AbstractMachine defines."
  },
  {
   "from": "Framework/Semantics", "to": "Framework/Submission.lean",
   "theorem": "LowerGateClass",
   "label": "evaluating the submitted circuit",
   "why": "ShorImplementation's correct field states that evaluating the submitted LowGate program (via LowerGateClass) matches the framework's order-finding specification."
  },
  {
   "from": "PhaseProduct/Compiler", "to": "PhaseProduct/Proofs",
   "theorem": "allocated_widths_sound",
   "label": "width bookkeeping is sound",
   "why": "The compiler's width-tracking bookkeeping (Compiler/Widths.lean) is proved sound in Proofs/Compiler/WidthSoundness.lean before any allocation/body correctness proof can rely on it."
  },
  {
   "from": "PhaseProduct/Proofs", "to": "PhaseProduct/Main.lean",
   "theorem": "lowerSignedPhaseProduct_correct",
   "label": "compiler + lowering assembled",
   "why": "Main.lean states the final theorem by combining the compiler correctness and lowering-readiness proofs developed in Proofs/."
  },
  {
   "from": "QFT/Split.lean", "to": "QFT/Proofs",
   "theorem": "eval_QFT_split",
   "label": "the split identity being lowered",
   "why": "Every proof under QFT/Proofs about the recursive lowering ultimately rewrites through the high-level split identity Split.lean states."
  },
  {
   "from": "QFT/Proofs", "to": "QFT/Main.lean",
   "theorem": "lowerQFT_correct",
   "label": "recursive lowering assembled",
   "why": "Main.lean packages the plan-semantics and readiness proofs from Proofs/ into the single lowering-correctness theorem."
  },
  {
   "from": "ModularExponentiation/Proofs", "to": "ModularExponentiation/Main.lean",
   "theorem": "modExpApprox_correct",
   "label": "staged error bound assembled",
   "why": "Main.lean combines the staged Algorithm-1 approximation proofs in Proofs/ into one eta-independent distance bound."
  },
  {
   "from": "Shor/Circuit", "to": "Shor/Proofs",
   "theorem": "Shor_correct",
   "label": "ideal circuit correctness",
   "why": "The ideal order-finding circuit Circuit/OrderFinding.lean defines (orderFindingIdeal) is what Proofs/NaiveShor/Correctness.lean proves succeeds with the standard probability."
  },
  {
   "from": "Shor/Proofs", "to": "Shor/Main.lean",
   "theorem": "Shor_end_to_end_factoring",
   "label": "correctness assembled into the payoff",
   "why": "Main.lean combines the ideal correctness, approximation transfer, and classical reduction proofs from Proofs/ into the complete factoring statement."
  },
  {
   "from": "Shor/Proofs", "to": "Shor/Main.lean",
   "theorem": "Shor_correct_approx_lowered_uniform",
   "label": "the theorem the submission needs",
   "why": "This is the version of correctness stated at the fully lowered circuit level, the one Reference/ actually discharges."
  },
  {
   "from": "GateCount/QFT_GateCount.lean", "to": "GateCount/Shor_GateCount.lean",
   "theorem": "exists_shorGateCountBound",
   "label": "component bounds combined",
   "why": "The final theorem combines the QFT and phase-product component bounds with the modular-exponentiation count, then picks k so the rate collapses to n^(2+epsilon)."
  },
  {
   "from": "Reference/ShorProgram.lean", "to": "Reference/ReferenceShorImplementation.lean",
   "theorem": "referenceShorImplementation",
   "label": "the submission value",
   "why": "referenceShorImplementation packages ShorProgram's concrete, computable circuit family together with the layout/readiness/precision proofs into the actual ShorImplementation value."
  },
  {
   "from": "Shared/Registers.lean", "to": "Shared/GateLaws.lean",
   "theorem": "writeNat_comm_of_disjoint",
   "label": "locality laws under per-gate semantics",
   "why": "GateLaws.lean's per-gate-class semantic lemmas are built on the disjoint-write commutation laws Registers.lean proves."
  }
 ]
}
