#!/usr/bin/env python3
"""One-shot: build the layered lean/ tree from the flat one and rewrite imports + lakefile."""
import os, re, sys, shutil
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import module_map as mm

SRC, DST = sys.argv[1], sys.argv[2]   # flat lean/ dir, new lean/ dir
def path(root, mod): return os.path.join(root, *mod.split(".")) + ".lean"
imp_re = re.compile(r"^import\s+(\S+)\s*$", re.M)

def convert(text, table):
    return imp_re.sub(lambda g: "import " + table.get(g.group(1), g.group(1)), text)

for old, new in mm.M.items():
    os.makedirs(os.path.dirname(path(DST, new)), exist_ok=True)
    open(path(DST, new), "w").write(convert(open(path(SRC, old)).read(), mm.M))
for old, new in mm.HELPERS.items():
    out = os.path.join(DST, "Helpers", new + ".lean")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    shutil.copy(os.path.join(SRC, "helpers", old + ".lean"), out)
print("moved", len(mm.M), "modules and", len(mm.HELPERS), "helpers")
