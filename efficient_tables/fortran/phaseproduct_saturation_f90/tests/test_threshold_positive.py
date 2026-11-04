"""Uncapped independent positive threshold regression; no model or timeout."""
from datetime import datetime
from pathlib import Path
import os
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
GFORTRAN = Path(os.environ.get('FC') or shutil.which('gfortran') or 'gfortran')
BUILD = ROOT / "build" / "threshold_positive"
BUILD.mkdir(parents=True, exist_ok=True)
ENV = dict(os.environ)
ENV["PATH"] = str(GFORTRAN.parent) + os.pathsep + ENV["PATH"]
C11 = [(1, 3, 2, 1, 0), (4, 2, 0, 0, 0), (1, 3, 1, 1, 0),
       (1, 3, 2, 1, 1), (1, 2, 1, 1, 1), (1, 1, 2, 1, 0),
       (4, 2, 0, 0, 0), (1, 3, 1, 1, 0), (1, 1, 2, 1, 0),
       (1, 3, 2, 1, 1), (1, 2, 1, 1, 1)]


def replay(k, a, b, budget, ops):
    identity = [[int(i == j) for j in range(k)] for i in range(k)]
    rows = [row[:] for row in identity]
    targets = {tuple(int(j == 0) for j in range(k)),
               tuple(int(j == k - 1) for j in range(k))}
    points = []
    exponent = 0
    while len(points) < 2 * k - 3:
        for reciprocal in ([False] if exponent == 0 else [True, False]):
            for sign in [-1, 1]:
                powers = range(k - 1, -1, -1) if reciprocal else range(k)
                points.append(tuple((sign * 2**exponent)**power for power in powers))
        exponent += 1
    targets.update(points[:2 * k - 3])
    seen = {tuple(row) for row in rows}
    scans = [[0] * k, [0] * (k - 1) + [k - 1]]
    peaks = [0, k - 1]
    charge = 0
    for kind, destination, source, sign, shift in ops:
        destination -= 1
        source -= 1
        assert 0 <= destination < k and shift >= 0
        if kind == 1:
            assert 0 <= source < k and source != destination and sign in (-1, 1)
            rows[destination] = [x + sign * (y << shift)
                                 for x, y in zip(rows[destination], rows[source])]
            for scan in scans:
                scan[destination] = 1 + max(scan[destination], scan[source] + shift)
            charge += 1 if sign > 0 else 3
        else:
            assert source == -1 and sign == 0
            if kind == 2:
                rows[destination] = [x << shift for x in rows[destination]]
                for scan in scans:
                    scan[destination] += shift
            elif kind == 3:
                assert all(x % (1 << shift) == 0 for x in rows[destination])
                rows[destination] = [x // (1 << shift) for x in rows[destination]]
                for scan in scans:
                    scan[destination] -= shift
            else:
                assert kind == 4 and shift == 0
                rows[destination] = [-x for x in rows[destination]]
                for scan in scans:
                    scan[destination] += 1
                charge += 1
        assert all(min(scan) >= 0 for scan in scans)
        peaks = [max(peak, max(scan)) for peak, scan in zip(peaks, scans)]
        assert peaks[0] <= a and peaks[1] <= b + k - 1
        seen.update(tuple(row) for row in rows)
    assert rows == identity and targets <= seen and charge <= budget
    return charge, peaks[0], peaks[1] - k + 1


assert replay(3, 6, 5, 11, C11) == (11, 6, 5)
# Existing constructor and generic differential cases compile with runtime checks.
subprocess.run([sys.executable, "tests/test_local.py"],
               cwd=ROOT, env=ENV, check=True)
exe = BUILD / "threshold_positive.exe"
subprocess.run([str(GFORTRAN), "-std=f95", "-pedantic-errors",
                "-Wall", "-Wextra", "-O3", "-J", str(BUILD), "-I", str(BUILD),
                "src/sp_oracle.f90", "src/sp_threshold.f90",
                "tests/test_threshold_positive.f90", "-o", str(exe)],
               cwd=ROOT, env=ENV, check=True)
start = time.perf_counter()
result = subprocess.run([str(exe)], cwd=ROOT, env=ENV, capture_output=True, text=True)
elapsed = time.perf_counter() - start
raw = result.stdout + result.stderr + f"\nELAPSED_SECONDS {elapsed:.6f}\n"
log = ROOT / "tests" / ("threshold_positive_output." + datetime.now().strftime("%Y-%m-%dT%H%M%S") + ".txt")
log.write_text(raw)
print(raw, end="", flush=True)
print("RAW_OUTPUT", log, flush=True)
assert result.returncode == 0, result.returncode
ops = [tuple(map(int, line.split()[1:])) for line in result.stdout.splitlines()
       if line.split() and line.split()[0] == "OP"]
threshold = next(line.split()[1:] for line in result.stdout.splitlines()
                 if line.split() and line.split()[0] == "THRESHOLD")
status, theta, nops, calls, states = map(int, threshold)
assert status == 0 and theta == 6 and nops == len(ops) and calls > 1 and states > 0
profile = replay(3, 6, 5, 11, ops)
assert max(profile[1], profile[2] + 1) == theta
assert "THRESHOLD_POSITIVE_PASS" in result.stdout
print("INDEPENDENT_THRESHOLD_REPLAY_PASS", profile, "CALLS", calls, "STATES", states)
