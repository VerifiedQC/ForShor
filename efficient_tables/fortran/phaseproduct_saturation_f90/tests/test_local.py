"""Independent literal replay and constructor correspondence, no model calls."""
from pathlib import Path
import importlib.util
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
GFORTRAN = Path(os.environ.get('FC') or shutil.which('gfortran') or 'gfortran')
REFERENCE = ROOT / "tests" / "f2_bridge_witness.py"
spec = importlib.util.spec_from_file_location("bridge_reference", REFERENCE)
bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bridge)
env = dict(os.environ)
env["PATH"] = str(GFORTRAN.parent) + os.pathsep + env["PATH"]
cmd = [str(GFORTRAN), "-std=f95", "-Wall", "-Wextra", "-fcheck=all", "-fbacktrace",
       "-I", "tests", "-J", "tests", "src/sp_oracle.f90", "src/sp_threshold.f90",
       "tests/test_local.f90", "-o", "tests/test_local.exe"]
subprocess.run(cmd, cwd=ROOT, env=env, check=True)
run = subprocess.run([str(ROOT / "tests/test_local.exe")], cwd=ROOT, env=env,
                     check=True, capture_output=True, text=True)
(ROOT / "tests/local_test_output.txt").write_text(run.stdout)
constructors = []
for line in run.stdout.splitlines():
    tokens = line.split()
    if not tokens:
        continue
    if tokens[0] == "CTOR":
        k, nop, charge, a, b = map(int, tokens[1:])
        constructors.append((k, nop, charge, a, b, []))
    elif tokens[0] == "OP":
        constructors[-1][-1].append(tuple(map(int, tokens[1:])))

for k, nop, charge, a, b, ops in constructors:
    # Compare against the byte-preserved theory constructor after erasing markers.
    expected = []
    for op in bridge.paired(k, bridge.points("PP", k)):
        if op[0] == "mark":
            continue
        if op[0] == "add":
            expected.append((1, op[1] + 1, op[2] + 1, op[3], op[4]))
        elif op[0] in ("L", "R"):
            expected.append((2 if op[0] == "L" else 3, op[1] + 1, 0, 0, op[2]))
        elif op[0] == "neg":
            expected.append((4, op[1] + 1, 0, 0, 0))
    assert ops == expected, ("constructor correspondence", k)
    rows = [[int(i == j) for j in range(k)] for i in range(k)]
    identity = [row[:] for row in rows]
    targets = [bridge.target(k, p) for p in bridge.points("PP", k)]
    seen = {i for i, t in enumerate(targets) if t in rows}
    s0 = [0] * k
    sr = [0] * (k - 1) + [k - 1]
    peak0, peakr, actual_charge = 0, k - 1, 0
    for kind, dst, source, sign, shift in ops:
        dst -= 1
        source -= 1
        if kind == 1:
            rows[dst] = [x + sign * (y << shift) for x, y in zip(rows[dst], rows[source])]
            s0[dst] = 1 + max(s0[dst], s0[source] + shift)
            sr[dst] = 1 + max(sr[dst], sr[source] + shift)
            actual_charge += 1 if sign > 0 else 3
        elif kind == 2:
            rows[dst] = [x << shift for x in rows[dst]]
            s0[dst] += shift
            sr[dst] += shift
        elif kind == 3:
            assert all(x % (1 << shift) == 0 for x in rows[dst])
            rows[dst] = [x >> shift for x in rows[dst]]
            s0[dst] -= shift
            sr[dst] -= shift
        elif kind == 4:
            rows[dst] = [-x for x in rows[dst]]
            s0[dst] += 1
            sr[dst] += 1
            actual_charge += 1
        assert min(s0 + sr) >= 0
        peak0 = max(peak0, max(s0))
        peakr = max(peakr, max(sr))
        seen.update(i for i, t in enumerate(targets) if t in rows)
    assert rows == identity and len(seen) == 2 * k - 1
    assert (actual_charge, peak0, peakr - k + 1) == (charge, a, b)
    assert len(ops) == nop
    print(f"independent constructor/replay k={k}: charge={charge} profile=({a},{b}) PASS")
assert "LOCAL_TESTS_PASS" in run.stdout
# F90 source audit: reject later-standard features used in common ports.
for filename in ["sp_oracle.f90", "sp_threshold.f90"]:
    text = (ROOT / "src" / filename).read_text().lower()
    lines = [line for line in text.splitlines() if not line.lstrip().startswith("!")]
    assert max(map(len, lines)) <= 120
    for forbidden in ["pure ", "elemental ", "iso_fortran_env", "move_alloc", "allocatable ::"]:
        if forbidden == "allocatable ::":
            continue  # Local allocatable arrays are F90.
        assert forbidden not in "\n".join(lines), (filename, forbidden)
print("LOCAL_DIFFERENTIAL_AND_SOURCE_AUDIT_PASS")
