#!/usr/bin/env python3
"""Check the shipped templates' exact stdout against the pre-refactor coherent baseline.

Captured at a31848a with `lake exe forshor_policy_submission` (plain and
`--balanced`) and `lake exe forshor_ptp_policy_submission`. The hashes include
the newline, the submission envelope and all of its IR; don't rebaseline for
semiclassical-only changes.
"""
import hashlib
import sys

EXPECTED = {
    "policy": "dcac12605eaa7d711c02b18006529be6579b2384fe2a9733fcf6bdba868f4e47",
    "balanced": "24e3e3c5c6f1aca793ec61ed942244302604f462110bf9cf023b0348e11ca5b2",
    "ptp": "becc52e7d28c94cbb914970e4d3d9807687183c5dc9ebe69519192aeae463653",
}

if len(sys.argv) != 2 or sys.argv[1] not in EXPECTED:
    sys.exit("usage: check_coherent_policy_output.py {policy|balanced|ptp} < output.json")

mode = sys.argv[1]
actual = hashlib.sha256(sys.stdin.buffer.read()).hexdigest()
if actual != EXPECTED[mode]:
    sys.exit(f"{mode} output changed: expected SHA-256 {EXPECTED[mode]}, got {actual}")
print(f"{mode} output matches the coherent baseline")
