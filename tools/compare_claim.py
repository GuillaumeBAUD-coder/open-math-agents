#!/usr/bin/env python3
"""Compares the last line of a run's output (JSON) with evidence/<id>/claim.json. Two kinds of claim:

1. {"result": <value>, "tolerance": <rel>}: reproduction. Numbers within the relative tolerance (default 1e-9),
   everything else exactly; lists and objects element-wise. Prints "reproduced". This shows the run is reproducible,
   not that its result is correct.
2. {"interval": [lo, hi]}: certified enclosure. The run's last line must be {"interval": [lo, hi]} (or [lo, hi]) and its
   interval must lie inside the claimed one. Every endpoint is a JSON string, "p/q" or a decimal such as "0.3183",
   parsed exactly with fractions.Fraction and compared in exact rational arithmetic; JSON numbers (floats) are refused,
   so no floating-point value is trusted anywhere in the comparison. Prints "certified: ...".
Exit status 0 when the claim holds, 1 otherwise."""
import json, math, re, sys
from fractions import Fraction

def fail(msg):
    print(msg); sys.exit(1)

claim = json.load(open(sys.argv[1]))
lines = [l for l in open(sys.argv[2]).read().splitlines() if l.strip()]
if not lines: fail("no output")
try: got = json.loads(lines[-1])
except Exception: fail("the last line of output is not JSON")

EXACT = re.compile(r"[+-]?(\d+(\.\d*)?|\.\d+)([eE][+-]?\d+)?(/\d+)?")
def exact(x, where):
    if not isinstance(x, str):
        fail(f"refused: {where} endpoint {json.dumps(x)} is not a string; give exact endpoints as \"p/q\" or decimal strings (floats are not trusted)")
    s = x.strip()
    if not EXACT.fullmatch(s): fail(f"refused: {where} endpoint {json.dumps(x)} is not an exact rational (\"p/q\" or a decimal)")
    try: return Fraction(s)
    except (ValueError, ZeroDivisionError): fail(f"refused: {where} endpoint {json.dumps(x)} is not an exact rational")

def interval(v, where):
    if isinstance(v, dict): v = v.get("interval")
    if not (isinstance(v, list) and len(v) == 2): fail(f"refused: {where} must be an interval [lo, hi]")
    lo, hi = exact(v[0], where), exact(v[1], where)
    if lo > hi: fail(f"refused: {where} interval has lo > hi")
    return lo, hi

if "interval" in claim:
    clo, chi = interval(claim["interval"], "claimed")
    glo, ghi = interval(got, "output")
    show = lambda a, b: f"[{a}, {b}]"
    if clo <= glo and ghi <= chi:
        print(f"certified: the run's interval {show(glo, ghi)} lies inside the claimed {show(clo, chi)} (exact rational comparison)"); sys.exit(0)
    fail(f"not contained: the run's interval {show(glo, ghi)} is not inside the claimed {show(clo, chi)}")

tol = float(claim.get("tolerance", 1e-9))
def same(a, b):
    if isinstance(a, (int, float)) and isinstance(b, (int, float)) and not isinstance(a, bool):
        return math.isclose(a, b, rel_tol=tol, abs_tol=tol * 1e-3)
    if isinstance(a, list) and isinstance(b, list): return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    if isinstance(a, dict) and isinstance(b, dict): return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    return a == b
if same(claim.get("result"), got): print("reproduced"); sys.exit(0)
fail(f"mismatch: claimed {json.dumps(claim.get('result'))[:200]}, got {json.dumps(got)[:200]}")
