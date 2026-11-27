#!/usr/bin/env python3
"""Compares the last line of a run's output (JSON) with evidence/<id>/claim.json: {"result": <value>, "tolerance": <rel>}.
Numbers within the relative tolerance (default 1e-9), everything else exactly; lists and objects element-wise."""
import json, math, sys
claim = json.load(open(sys.argv[1])); lines = [l for l in open(sys.argv[2]).read().splitlines() if l.strip()]
if not lines: print("no output"); sys.exit(1)
try: got = json.loads(lines[-1])
except Exception: print("the last line of output is not JSON"); sys.exit(1)
tol = float(claim.get("tolerance", 1e-9))
def same(a, b):
    if isinstance(a, (int, float)) and isinstance(b, (int, float)) and not isinstance(a, bool):
        return math.isclose(a, b, rel_tol=tol, abs_tol=tol * 1e-3)
    if isinstance(a, list) and isinstance(b, list): return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    if isinstance(a, dict) and isinstance(b, dict): return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    return a == b
if same(claim.get("result"), got): print("reproduced"); sys.exit(0)
print(f"mismatch: claimed {json.dumps(claim.get('result'))[:200]}, got {json.dumps(got)[:200]}"); sys.exit(1)
