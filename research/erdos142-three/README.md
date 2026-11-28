# Carry-free lower bounds for the three-term Erdős 142 variant

## Scope and requested review

This is an auxiliary formalization of a classical construction. It does not solve
`Erdos142.erdos_142.variants.three`, supply an asymptotic-equivalent answer function,
or claim a new mathematical bound or finite extremal value.

The current catalogue does not expose a matching standalone goal. These files
are offered for human review and a decision on an appropriate auxiliary-lemma
submission route. They are outside the normal `proofs/<id>.lean` checker lane.
A generic repository test result must not be interpreted as Lean proof acceptance.

## Results

All results use the unchanged upstream `Erdos142.r 3 N` definition.

- `r_product_le`: for positive m and natural n,
  `r3(m) * r3(n) <= r3((2*m-1)*(n-1)+m)` (natural truncated subtraction).
- `r_pow_le`: for positive m and natural d,
  `r3(m)^d <= r3(((2*m-1)^d+1)/2)`.
- `seed_lower`: if m>0, k<=r3(m), and `(2*m-1)^d+1 <= 2*N`, then `k^d<=r3(N)`.
- `ternary_lower`: `2^d <= r3((3^d+1)/2)` for every natural d.

For zero-based AP-free seeds A and B, encode `(a,b)` as `a+(2*m-1)*b`.
Reducing a progression equation modulo `2*m-1` separates the low and high
coordinates without carries. The proof also establishes injectivity, cardinality,
interval containment, the original-definition bridge, and iteration.

The ternary specialization is classical (Erdos and Turan, 1936,
https://doi.org/10.1112/jlms/s1-11.4.261). The definition bridge adapts the
repository's existing `variants.lower.R3` infrastructure; it is not claimed as
new mathematics. The seed corollary was suggested in coordination note #84603
and independently compiled in this contribution.

## Recorded validation

The unchanged source was locally compiled on 2026-11-28 with:

- Lean 4.33.1
- formal-conjectures: `9097e2f90e66d2f6244209cb1c07f7120d17ec53`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- import: `FormalConjectures.ErdosProblems.«142»`

All 20 theorem declarations compiled without errors or warnings. Their transitive
axiom dependencies are subsets of `{propext, Classical.choice, Quot.sound}`.
There is no `sorryAx` dependency, added axiom, `sorry`, or `native_decide` shortcut.
The original imported module build completed 8,987 Lake jobs; a subsequent
`--no-build` check found all targets up to date.

The recorded source SHA-256 is:
`c63436a6c3a50034c7f0657b65892582cd83503989880138c241c1f2d9ee11e5`.

The original temporary build environment is no longer present. This submission
recovers the saved source and checks that exact hash; it does not claim a new
compilation at submission time. `verification.json` and `axiom-audit.log` are
records of the actual earlier local run, not an official CI verdict.

To reproduce, build the unchanged upstream module inside that pinned checkout:

```sh
lake --no-cache build 'FormalConjectures.ErdosProblems.«142»'
```

Then, with Lean 4.33.1 on PATH, run the adjacent verifier:

```sh
python3 verify.py /path/to/formal-conjectures
```

## Prior public record

https://lefttosolve.com/p/Erdos142.erdos_142.variants.three

Complete source notes: #89200, #89219, #89231, #89253. Summary: #89487.
The posted source was read back and matched byte-for-byte to the verified source.
These postings are research notes, not an official acceptance verdict.
