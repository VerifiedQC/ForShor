#!/usr/bin/env python3
"""Layer discipline for Implementation/.

Replaces the five check_*_layers.sh scripts. Each folder's layer order is a
table below; a file may import another file in the same folder only if that
file's rank is strictly lower. Equal ranks are siblings and may not import
each other, which is how genuine independence (Step2 vs Step5) is enforced
rather than papered over with a total order.

Run with no arguments to check every folder, or name one:
    scripts/check_layers.py            # all
    scripts/check_layers.py Shor       # one
"""

import os
import re
import sys

IMPL = "FastMultiplication/ShorVerification/Implementation"
PREFIX = "FastMultiplication.ShorVerification.Implementation."

# A declaration, for the umbrella detector. `private`/`protected`/`opaque`/
# `example` count: a file of only private lemmas is not an umbrella.
DECL = re.compile(
    r"^(private\s+|protected\s+|scoped\s+|local\s+|noncomputable\s+|unsafe\s+|partial\s+)*"
    r"(def|abbrev|structure|inductive|class|instance|theorem|lemma|opaque|example|axiom)\b"
    r"|^@\[|^(macro|elab|syntax|notation|infix|infixl|infixr|prefix|postfix)\b"
)

# Layer tables: (regex on the module path inside the folder) -> rank.
# First match wins, so order matters. Rank 99 means "unclassified": a new
# top-level directory fails loudly instead of silently passing.
LAYERS = {
    "ModularExponentiation": [
        (r"^Math", 1), (r"^Circuit", 2), (r"^Lowering", 3),
        (r"^Spec", 4), (r"^Proofs", 5), (r"^Main$", 6),
    ],
    "PhaseProduct": [
        (r"^Math", 1), (r"^Compiler", 2), (r"^Gates", 3),
        (r"^Lowering", 4), (r"^Spec", 5), (r"^Proofs", 6), (r"^Main$", 7),
    ],
    "QFT": [
        (r"^Split$", 1), (r"^Lowering", 2),
        (r"^Spec", 3), (r"^Proofs", 4), (r"^Main$", 5),
    ],
    "Shared": [
        (r"^(QftPhase|Registers|Measurement)$", 1), (r"^States$", 2),
        (r"^(Hadamard|GateLaws)$", 3), (r"^LowGateEval$", 4),
    ],
    "Shor": [
        (r"^Math", 10), (r"^Lowering", 15), (r"^Circuit", 20),
        (r"^Spec\.Assertions$", 31), (r"^Spec", 30),
        (r"^Proofs\.(Budgets|Setup|Lowering)$", 40),
        # Readiness/: the real partial order, not a total one. Equal ranks are
        # independent and may not import each other -- Step2/Step5,
        # Init/Step1 and IQFT/ModMul each genuinely are.
        (r"^Proofs\.Readiness\.Static$", 41),
        (r"^Proofs\.Readiness\.Sequencing$", 42),
        (r"^Proofs\.Readiness\.Primitives$", 43),
        (r"^Proofs\.Readiness\.(Init|Step1)$", 44),
        (r"^Proofs\.Readiness\.(Step2|Step5)$", 45),
        (r"^Proofs\.Readiness\.(IQFT|ModMul)$", 46),
        (r"^Proofs\.Readiness\.ModExp$", 47),
        (r"^Proofs\.Readiness\.Dynamic$", 48),
        (r"^Proofs\.NaiveShor", 52), (r"^Proofs\.Correctness$", 53),
        (r"^Main$", 60),
    ],
}

# Ranks whose members are genuinely independent: a file may not import a
# sibling at the same rank. Everywhere else same-layer imports are the normal
# case (a `Spec/` file importing another `Spec/` file), so only ordering across
# layers is checked.
STRICT_SIBLINGS = {"Shor": {44, 45, 46}}

# Umbrella files that are deliberately nothing but imports.
UMBRELLA_OK = {
    ("PhaseProduct", "Math.Table_Generation"),
    ("PhaseProduct", "Math.Table_Generation.Generator"),
}

# Modules not inspected. `Generator*` is the unbuilt table-generation subtree
# that nothing on the headline path roots; narrowed from the old blanket
# `Math.Table_Generation*` skip, which is how real inversions escaped.
SKIP = {
    "PhaseProduct": [r"^Math\.Table_Generation\.Generator($|\.)"],
}

# (module, dependency) pairs allowed to break the layer order, with a reason.
ALLOWED = {
    ("Shor", "Spec.Assertions", "Proofs.Readiness.Static"):
        "the assertion inlines a GateWorkspaceOK proof term; proof-irrelevant "
        "in meaning, but a real file dependency",
}

# Folders that may not import another subroutine/assembly folder sideways.
NO_SIDEWAYS = {"Shared"}
SIDEWAYS_RE = re.compile(
    r"^import FastMultiplication\.ShorVerification\.Implementation\."
    r"(PhaseProduct|QFT|ModularExponentiation|Shor|GateCount|Reference)\.")

# Shor/Proofs is proof-only: nothing outside Implementation/Shor may import it.
# Two provider files are documented in Shor/README.md as deliberate exports.
PROOFS_ONLY_PREFIX = PREFIX + "Shor.Proofs"
PROOFS_ONLY_ALLOWED = {
    (f"{IMPL}/GateCount/Shor_GateCount.lean", "Shor.Proofs.Lowering"),
    (f"{IMPL}/Reference/ShorProgram.lean", "Shor.Proofs.Readiness.Static"),
}


def imports(path):
    """Module names imported by `path`, one per `import` line."""
    out = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            if not line.startswith("import "):
                continue
            # `import A B` is not Lean 4 syntax, but split anyway so a stray
            # second name is seen rather than silently dropped.
            for name in line[len("import "):].split():
                out.append(name)
    return out


def rank(folder, module):
    for pattern, value in LAYERS[folder]:
        if re.search(pattern, module):
            return value
    return 99


def lean_files(root):
    found = []
    for dirpath, _dirnames, filenames in os.walk(root):
        for name in filenames:
            if name.endswith(".lean"):
                found.append(os.path.join(dirpath, name))
    return sorted(found)  # sorted: failure output must not vary run to run


def check_folder(folder):
    root = f"{IMPL}/{folder}"
    prefix = PREFIX + folder + "."
    skips = [re.compile(p) for p in SKIP.get(folder, [])]
    problems = []

    for path in lean_files(root):
        module = path[len(root) + 1:-len(".lean")].replace("/", ".")
        if any(s.search(module) for s in skips):
            continue

        text = open(path, encoding="utf-8").read()
        lines = text.splitlines()
        if (any(l.startswith("import ") for l in lines)
                and not any(DECL.match(l) for l in lines)
                and (folder, module) not in UMBRELLA_OK):
            problems.append(f"UMBRELLA FILE: {folder}.{module}")

        mine = rank(folder, module)
        if mine == 99:
            problems.append(f"UNCLASSIFIED: {folder}.{module} matches no layer rule")

        for name in imports(path):
            if name.startswith(prefix):
                dep = name[len(prefix):]
                if any(s.search(dep) for s in skips):
                    continue
                theirs = rank(folder, dep)
                strict = mine in STRICT_SIBLINGS.get(folder, set())
                bad = theirs > mine or (strict and theirs == mine)
                if bad:
                    if (folder, module, dep) in ALLOWED:
                        continue
                    rel = ("independent siblings" if theirs == mine
                           else "higher layer")
                    problems.append(
                        f"LAYER VIOLATION: {folder}.{module} imports {folder}.{dep} ({rel})")
            if folder in NO_SIDEWAYS and SIDEWAYS_RE.match("import " + name):
                problems.append(
                    f"FORBIDDEN SIDEWAYS IMPORT: {folder}.{module} imports {name}")
    return problems


def check_proofs_only():
    """Shor/Proofs may not be imported from outside Implementation/Shor."""
    problems = []
    for path in lean_files("FastMultiplication"):
        if path.startswith(f"{IMPL}/Shor/"):
            continue
        for name in imports(path):
            if name.startswith(PROOFS_ONLY_PREFIX):
                dep = name[len(PREFIX):]
                if (path, dep) in PROOFS_ONLY_ALLOWED:
                    continue
                problems.append(
                    f"FORBIDDEN PROOFS IMPORT: {path} imports {dep} "
                    "(Shor/Proofs is proof-only; route through Shor/Main.lean)")
    return problems


def shared_waiting():
    """Rule (b) of Shared/README.md, informational only."""
    root = f"{IMPL}/Shared"
    notes = []
    for path in lean_files(root):
        module = path[len(root) + 1:-len(".lean")].replace("/", ".")
        needle = f"import {PREFIX}Shared.{module}"
        folders = set()
        for other in lean_files(IMPL):
            if other.startswith(root + "/"):
                continue
            if any(n == f"{PREFIX}Shared.{module}" for n in imports(other)):
                folders.add(other[len(IMPL) + 1:].split("/")[0])
        if len(folders) < 2:
            notes.append(
                f"WARNING: Shared.{module} is imported from only {len(folders)} "
                "top-level folder(s) (shared-in-waiting)")
    return notes


def main():
    wanted = sys.argv[1:] or sorted(LAYERS)
    unknown = [w for w in wanted if w not in LAYERS]
    if unknown:
        print(f"unknown folder(s): {', '.join(unknown)}", file=sys.stderr)
        return 2

    problems = []
    for folder in wanted:
        problems += check_folder(folder)
    if "Shor" in wanted:
        problems += check_proofs_only()
    for note in (shared_waiting() if "Shared" in wanted else []):
        print(note)

    for p in problems:
        print(p)
    if problems:
        print(f"\n{len(problems)} problem(s)", file=sys.stderr)
        return 1
    print(f"layer check passed: {', '.join(wanted)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
