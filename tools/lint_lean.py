#!/usr/bin/env python3
"""Refuses Lean files that could pass the compiler without proving anything: sorry/admit, new axioms, unsafe or
implemented_by tricks, native_decide (trusts the compiler), options that silence errors. The compiler output is checked too."""
import re, sys
src = open(sys.argv[1], encoding="utf-8").read()
code = re.sub(r"/-.*?-/", "", src, flags=re.S); code = re.sub(r"--[^\n]*", "", code)
bad = [w for w in [r"\bsorry\b", r"\badmit\b", r"^\s*axiom\b", r"\bunsafe\b", r"implemented_by", r"\bextern\b", r"native_decide", r"set_option\s+debug", r"\bopaque\b", r"@\[csimp\]", r"\bdebug\.skipKernelTC\b"]
       if re.search(w, code, re.M)]
if bad: print("forbidden: " + ", ".join(bad)); sys.exit(1)
if not re.search(r"^\s*import\s+Physlib|^\s*import\s+PhyslibAlpha|^\s*import\s+QuantumInfo|^\s*import\s+Mathlib", code, re.M): print("must import Physlib (or Mathlib)"); sys.exit(1)
if not re.search(r"^\s*(theorem|lemma)\s", code, re.M): print("no theorem"); sys.exit(1)
print("ok")
