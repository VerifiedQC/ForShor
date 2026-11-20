#!/usr/bin/env python3
"""Smoke check the measured policy emitter on ForShor's shipped two-band template."""
import json
import sys

data = sys.stdin.buffer.read()
assert len(data) < 1024 * 1024, "the shipped measured policy document must stay compact"
doc = json.loads(data)
assert doc["schema"] == "forshor.policy-submission-semiclassical/v1"
assert [(b["threshold"], b["k"]) for b in doc["bands"]] == [(40, 3), (14, 2)]
assert doc["benchmark"]["bits"] == 2048 and doc["benchmark"]["trial_count"] == "386"
assert doc["precision"]["m"] == str(2**150 - 3) and doc["negation"] == "oneQubit"
assert doc["readout"] == {
    "schema": "forshor.readout-loop/v1",
    "mode": "semiclassical",
    "initialization": "initY1",
    "control": "referenceControl",
    "rounds": "referenceXWidth",
    "steps": ["H", "multiply", "ffPhase", "H", "measureReset"],
    "bit_order": "lsb_first",
    "angle_unit": "pi",
    "record": "rec[i] = outcome (0 or 1) of the i-th measureReset node executed (absolute slot, "
    "oldest first, 0-based); each measureReset appends one slot",
    "ff_angle_rule": "ffPhase(q, j) applies Phase(q, theta) with theta = -(sum_{i=0}^{j-1} rec[i] / 2^(j-i)) "
    "in units of pi (a dyadic rational; a missing slot counts as 0)",
}
ir = doc["ir"]
assert ir["schema"] == "forshor.ir/v1" and ir["entry"] == "readout_round"
names = [t["name"] for t in ir["templates"]]
assert names.count("readout_round") == 1 and "qft" in names
assert "shor" not in names and "shor_gate" not in names
assert {"balanced_phase_product", "balanced_cphase_product"} <= set(names)
round_template = next(t for t in ir["templates"] if t["name"] == "readout_round")
assert round_template["rParams"] == ["ctrl", "y", "work", "scratch", "flag"]
assert "modpow(a, ((rounds - 1) - j), N)" in json.dumps(round_template["body"])
print("compact measured policy output matches the readout contract")
