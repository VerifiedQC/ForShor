#!/usr/bin/env python3
"""Verify a table-generation submission and emit CI artifacts."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any


CHALLENGE = "table-generation"
TARGET_MODULE = (
    "FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math."
    "Table_Generation.Generator"
)
GENERATOR_DIR = Path(
    "FastMultiplication/ShorVerification/Implementation/PhaseProduct/Math/"
    "Table_Generation/Generator"
)
DEFS_FILE = GENERATOR_DIR / "Defs.lean"
CORRECTNESS_FILE = GENERATOR_DIR / "Correctness.lean"
SPEC_FILE = GENERATOR_DIR / "Spec.lean"
WELLFORMED_FILE = GENERATOR_DIR / "WellFormed.lean"
GENERATOR_IMPORT_FILE = Path(
    "FastMultiplication/ShorVerification/Implementation/PhaseProduct/Math/"
    "Table_Generation/Generator.lean"
)

SUBMISSION_FILES = {str(DEFS_FILE), str(CORRECTNESS_FILE)}
PROTECTED_FILES = {
    str(SPEC_FILE),
    str(WELLFORMED_FILE),
    str(GENERATOR_IMPORT_FILE),
}
ALLOWED_CHANGED_FILES = SUBMISSION_FILES

NAT = "\u2115"
GE = "\u2265"
EXPECTED_THEOREMS = {
    "generatedPoints_valid": (
        f"theorem generatedPoints_valid (mode : ProductMode) (k : {NAT}) "
        f"(_ : k {GE} 2) : ValidPointList mode k "
        "(generatedPoints mode k) := by"
    ),
    "generate_ProgConsumesPtsSafe": (
        f"theorem generate_ProgConsumesPtsSafe (mode : ProductMode) "
        f"(k : {NAT}) (hk : k {GE} 2) : ProgConsumesPtsSafe "
        "(by omega) State.start_state (generate mode k hk) "
        "(generatePointsInOrder mode k hk) := by"
    ),
}

BANNED_PATTERNS = {
    "sorry/admit": re.compile(r"\bsorry\b|\bsorryAx\b|\badmit\b"),
    "axiom/constant": re.compile(r"\baxiom\b|\bconstant\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
}

ALLOWED_AXIOMS = {
    "Classical.choice",
    "propext",
    "Quot.sound",
}


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def run_cmd(
    args: list[str],
    cwd: Path,
    timeout: int = 1200,
    env: dict[str, str] | None = None,
) -> dict[str, Any]:
    try:
        completed = subprocess.run(
            args,
            cwd=cwd,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
        return {
            "args": args,
            "returncode": completed.returncode,
            "output": completed.stdout,
        }
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return {
            "args": args,
            "returncode": 124,
            "output": output + f"\nTimed out after {timeout} seconds.\n",
        }


def check_result(name: str, ok: bool, details: str) -> dict[str, str]:
    return {
        "name": name,
        "status": "success" if ok else "failure",
        "details": details,
    }


def skipped_result(name: str, details: str) -> dict[str, str]:
    return {"name": name, "status": "skipped", "details": details}


def normalize_decl(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def strip_lean_comments(text: str) -> str:
    output: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
            if i < len(text):
                output.append("\n")
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            output.append(text[i])
        elif text[i] == "\n":
            output.append("\n")
        i += 1
    return "".join(output)


def extract_theorem_decl(text: str, theorem_name: str) -> tuple[int, str | None]:
    count = len(re.findall(rf"\btheorem\s+{re.escape(theorem_name)}\b", text))
    match = re.search(
        rf"\btheorem\s+{re.escape(theorem_name)}\b.*?:=\s*by",
        text,
        flags=re.DOTALL,
    )
    return count, match.group(0) if match else None


def get_changed_files(repo: Path) -> tuple[bool, list[str], str]:
    base = os.getenv("TABLE_GEN_BASE_SHA", "").strip()
    head = os.getenv("TABLE_GEN_HEAD_SHA", "").strip() or "HEAD"
    base_repo = os.getenv("TABLE_GEN_BASE_REPOSITORY", "").strip()
    event_name = os.getenv("GITHUB_EVENT_NAME", "").strip()

    if not base:
        if event_name == "pull_request":
            return False, [], "TABLE_GEN_BASE_SHA is missing for pull_request."
        return True, [], "No PR base SHA was provided; changed-file check skipped."

    has_base = run_cmd(["git", "cat-file", "-e", f"{base}^{{commit}}"], repo, 60)
    if has_base["returncode"] != 0:
        fetch_origin = run_cmd(["git", "fetch", "--no-tags", "--depth=1", "origin", base], repo, 300)
        if fetch_origin["returncode"] != 0 and base_repo:
            run_cmd(
                [
                    "git",
                    "fetch",
                    "--no-tags",
                    "--depth=1",
                    f"https://github.com/{base_repo}.git",
                    base,
                ],
                repo,
                300,
            )

    has_base = run_cmd(["git", "cat-file", "-e", f"{base}^{{commit}}"], repo, 60)
    if has_base["returncode"] != 0:
        return False, [], f"Could not fetch PR base commit {base}."

    diff = run_cmd(["git", "diff", "--name-only", f"{base}...{head}"], repo, 300)
    if diff["returncode"] != 0:
        return False, [], diff["output"].strip()

    files = [line.strip() for line in diff["output"].splitlines() if line.strip()]
    return True, files, f"Compared {base}...{head}."


def verify_required_files(repo: Path) -> dict[str, str]:
    required = sorted(SUBMISSION_FILES | PROTECTED_FILES)
    missing = [path for path in required if not (repo / path).is_file()]
    return check_result(
        "required files exist",
        not missing,
        "All required files are present." if not missing else "Missing: " + ", ".join(missing),
    )


def verify_changed_files(repo: Path) -> dict[str, str]:
    ok, changed, details = get_changed_files(repo)
    if not ok:
        return check_result("changed files are allowed", False, details)
    if not changed:
        return skipped_result("changed files are allowed", details)
    disallowed = sorted(path for path in changed if path not in ALLOWED_CHANGED_FILES)
    if disallowed:
        return check_result(
            "changed files are allowed",
            False,
            "Only Defs.lean and Correctness.lean may change. Disallowed: "
            + ", ".join(disallowed),
        )
    return check_result(
        "changed files are allowed",
        True,
        "Changed files: " + ", ".join(sorted(changed)),
    )


def verify_theorem_statements(repo: Path) -> dict[str, str]:
    text = (repo / CORRECTNESS_FILE).read_text(encoding="utf-8")
    failures: list[str] = []
    for theorem_name, expected in EXPECTED_THEOREMS.items():
        count, actual = extract_theorem_decl(text, theorem_name)
        if count != 1:
            failures.append(f"{theorem_name} appears {count} times")
            continue
        if actual is None:
            failures.append(f"{theorem_name} declaration could not be parsed")
            continue
        if normalize_decl(actual) != normalize_decl(expected):
            failures.append(f"{theorem_name} statement differs from the template")

    return check_result(
        "theorem statements are preserved",
        not failures,
        "The two theorem statements match the template."
        if not failures
        else "; ".join(failures),
    )


def verify_no_banned_tokens(repo: Path) -> dict[str, str]:
    lean_files = sorted((repo / GENERATOR_DIR).glob("*.lean"))
    failures: list[str] = []
    for path in lean_files:
        stripped = strip_lean_comments(path.read_text(encoding="utf-8"))
        for label, pattern in BANNED_PATTERNS.items():
            for match in pattern.finditer(stripped):
                line = stripped.count("\n", 0, match.start()) + 1
                rel = path.relative_to(repo)
                failures.append(f"{rel}:{line}: banned {label}")

    return check_result(
        "no banned proof shortcuts",
        not failures,
        "No sorry, admit, axiom, constant, or unsafe declarations were found."
        if not failures
        else "; ".join(failures[:20]),
    )


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def verify_build(repo: Path, out_dir: Path) -> dict[str, str]:
    build = run_cmd(["lake", "build", TARGET_MODULE], repo)
    write_text(out_dir / "table-generation-build.log", build["output"])
    return check_result(
        "lean build",
        build["returncode"] == 0,
        "Build completed successfully."
        if build["returncode"] == 0
        else f"Build failed with exit code {build['returncode']}. See build log.",
    )


def parse_axiom_names(output: str) -> set[str]:
    names: set[str] = set()
    for match in re.finditer(r"depends on axioms:\s*\[([^\]]*)\]", output):
        for raw in match.group(1).split(","):
            name = raw.strip().strip("'\"")
            if name:
                names.add(name)
    return names


def verify_axiom_dependencies(repo: Path, out_dir: Path) -> dict[str, str]:
    source = "\n".join(
        [
            f"import {TARGET_MODULE}.Correctness",
            "",
            "#print axioms Table_Generation.generatedPoints_valid",
            "#print axioms Table_Generation.generate_ProgConsumesPtsSafe",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as tmp:
        check_file = Path(tmp) / "CheckAxioms.lean"
        check_file.write_text(source, encoding="utf-8")
        result = run_cmd(["lake", "env", "lean", str(check_file)], repo, 600)

    write_text(out_dir / "table-generation-axioms.log", result["output"])
    if result["returncode"] != 0:
        return check_result(
            "axiom dependencies",
            False,
            f"Could not inspect theorem axioms; lean exited {result['returncode']}.",
        )

    output = result["output"]
    if "sorryAx" in output:
        return check_result("axiom dependencies", False, "A theorem depends on sorryAx.")

    found = parse_axiom_names(output)
    unexpected = sorted(found - ALLOWED_AXIOMS)
    if unexpected:
        return check_result(
            "axiom dependencies",
            False,
            "Unexpected theorem axioms: " + ", ".join(unexpected),
        )

    detail = (
        "No axioms were reported."
        if not found
        else "Only allowed axioms were reported: " + ", ".join(sorted(found))
    )
    return check_result("axiom dependencies", True, detail)


def parse_metric_output(output: str) -> dict[str, str]:
    metrics: dict[str, str] = {}
    in_block = False
    for line in output.splitlines():
        if line.strip() == "TABLE_GENERATION_METRICS_BEGIN":
            in_block = True
            continue
        if line.strip() == "TABLE_GENERATION_METRICS_END":
            break
        if in_block and "=" in line:
            key, value = line.split("=", 1)
            metrics[key.strip()] = value.strip()
    return metrics


def collect_metrics(repo: Path, out_dir: Path) -> tuple[dict[str, Any], dict[str, str]]:
    source = "\n".join(
        [
            f"import {TARGET_MODULE}.Defs",
            "import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Builders.Fragments",
            "",
            "open Operations",
            "open Table_Generation",
            "",
            "def targetProgram : Prog 4 := generate .PhaseTripleProduct 4 (by decide)",
            "def targetPoints : List Point := generatePointsInOrder .PhaseTripleProduct 4 (by decide)",
            "",
            '#eval IO.println "TABLE_GENERATION_METRICS_BEGIN"',
            '#eval IO.println ("mode=PhaseTripleProduct")',
            '#eval IO.println ("k=4")',
            '#eval IO.println ("score=" ++ toString targetProgram.length)',
            '#eval IO.println ("operation_count=" ++ toString targetProgram.length)',
            '#eval IO.println ("point_count=" ++ toString targetPoints.length)',
            '#eval IO.println ("points=" ++ joinComma (targetPoints.map pointToString))',
            '#eval IO.println ("program=" ++ progToString targetProgram)',
            '#eval IO.println "TABLE_GENERATION_METRICS_END"',
            "",
        ]
    )

    with tempfile.TemporaryDirectory() as tmp:
        metrics_file = Path(tmp) / "CollectMetrics.lean"
        metrics_file.write_text(source, encoding="utf-8")
        result = run_cmd(["lake", "env", "lean", str(metrics_file)], repo, 600)

    write_text(out_dir / "table-generation-metrics.log", result["output"])
    if result["returncode"] != 0:
        return {}, check_result(
            "target metrics",
            False,
            f"Could not evaluate k=4 PhaseTripleProduct metrics; lean exited {result['returncode']}.",
        )

    raw = parse_metric_output(result["output"])
    required = {"mode", "k", "score", "operation_count", "point_count", "points", "program"}
    missing = sorted(required - set(raw))
    if missing:
        return raw, check_result(
            "target metrics",
            False,
            "Missing metric fields: " + ", ".join(missing),
        )

    metrics: dict[str, Any] = dict(raw)
    for key in ("k", "score", "operation_count", "point_count"):
        try:
            metrics[key] = int(str(metrics[key]))
        except ValueError:
            return raw, check_result("target metrics", False, f"{key} is not an integer.")

    if metrics["k"] != 4 or metrics["mode"] != "PhaseTripleProduct":
        return metrics, check_result("target metrics", False, "Metrics target changed.")
    if metrics["point_count"] != 10:
        return metrics, check_result(
            "target metrics",
            False,
            f"Expected 10 points for k=4 triple product, got {metrics['point_count']}.",
        )
    if metrics["score"] != metrics["operation_count"]:
        return metrics, check_result("target metrics", False, "Score must equal operation count.")

    return metrics, check_result(
        "target metrics",
        True,
        f"k=4 PhaseTripleProduct score is {metrics['score']} operations.",
    )


def build_summary(result: dict[str, Any]) -> str:
    status = result["status"].upper()
    lines = [
        "<!-- table-generation-submission-result -->",
        "### Table generation submission",
        "",
        f"Status: **{status}**",
        "",
        "| Check | Status | Details |",
        "| --- | --- | --- |",
    ]
    for check in result["checks"]:
        details = str(check["details"]).replace("\n", " ").replace("|", "\\|")
        lines.append(f"| {check['name']} | {check['status']} | {details} |")

    metrics = result.get("metrics") or {}
    if result["status"] == "success" and metrics:
        lines.extend(
            [
                "",
                f"Score: `{metrics.get('score')}` operations for `k=4`, `PhaseTripleProduct`.",
                "",
                "The full JSON result, build log, axiom log, and metric log are attached as workflow artifacts.",
            ]
        )
    else:
        lines.extend(
            [
                "",
                "The JSON failure result and logs are attached as workflow artifacts.",
            ]
        )
    return "\n".join(lines) + "\n"


def collect_metadata() -> dict[str, Any]:
    return {
        "repository": os.getenv("GITHUB_REPOSITORY", ""),
        "workflow": os.getenv("GITHUB_WORKFLOW", ""),
        "run_id": os.getenv("GITHUB_RUN_ID", ""),
        "run_attempt": os.getenv("GITHUB_RUN_ATTEMPT", ""),
        "event_name": os.getenv("GITHUB_EVENT_NAME", ""),
        "pr_number": os.getenv("TABLE_GEN_PR_NUMBER", ""),
        "base_ref": os.getenv("GITHUB_BASE_REF", ""),
        "head_ref": os.getenv("GITHUB_HEAD_REF", ""),
        "base_sha": os.getenv("TABLE_GEN_BASE_SHA", ""),
        "head_sha": os.getenv("TABLE_GEN_HEAD_SHA", ""),
        "created_at": utc_now(),
    }


def verify(repo: Path, out_dir: Path) -> dict[str, Any]:
    checks: list[dict[str, str]] = []
    metrics: dict[str, Any] = {}

    checks.append(verify_required_files(repo))
    checks.append(verify_changed_files(repo))
    checks.append(verify_theorem_statements(repo))
    checks.append(verify_no_banned_tokens(repo))

    build_check = verify_build(repo, out_dir)
    checks.append(build_check)

    if build_check["status"] == "success":
        checks.append(verify_axiom_dependencies(repo, out_dir))
        metrics, metric_check = collect_metrics(repo, out_dir)
        checks.append(metric_check)
    else:
        checks.append(skipped_result("axiom dependencies", "Skipped because Lean build failed."))
        checks.append(skipped_result("target metrics", "Skipped because Lean build failed."))

    required_checks = [check for check in checks if check["status"] != "skipped"]
    success = all(check["status"] == "success" for check in required_checks)
    result = {
        "schema_version": 1,
        "challenge": CHALLENGE,
        "status": "success" if success else "failure",
        "target": {"mode": "PhaseTripleProduct", "k": 4, "score": "operation_count"},
        "metadata": collect_metadata(),
        "checks": checks,
        "metrics": metrics,
    }
    return result


def write_artifacts(result: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    write_text(
        out_dir / "table-generation-submission-result.json",
        json.dumps(result, indent=2, sort_keys=True) + "\n",
    )
    write_text(out_dir / "table-generation-summary.md", build_summary(result))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", default=".", help="Repository root to verify.")
    parser.add_argument("--out-dir", default="artifacts", help="Artifact output directory.")
    args = parser.parse_args()

    repo = Path(args.repo).resolve()
    out_dir = (repo / args.out_dir).resolve()
    try:
        result = verify(repo, out_dir)
    except Exception as exc:  # noqa: BLE001
        result = {
            "schema_version": 1,
            "challenge": CHALLENGE,
            "status": "failure",
            "target": {"mode": "PhaseTripleProduct", "k": 4, "score": "operation_count"},
            "metadata": collect_metadata(),
            "checks": [
                check_result("verifier exception", False, f"{type(exc).__name__}: {exc}")
            ],
            "metrics": {},
        }

    write_artifacts(result, out_dir)
    return 0 if result["status"] == "success" else 1


if __name__ == "__main__":
    sys.exit(main())
