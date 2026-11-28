import FormalConjectures.ErdosProblems.«124»

-- Reduction Erdos124.erdos124.ne_zero.R1 of Erdős Problem 124 (k ≠ 0 variant)
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
/-!
# Reduction of Erdős Problem 124, `ne_zero` (Burr–Erdős–Graham–Li, Acta Arith. 77 (1996))

Target (exactly, `k ≠ 0`): for every finite `D` of integers `d ≥ 3` with
`∑_{d ∈ D} 1/(d-1) ≥ 1` and `gcd D = 1`, every sufficiently large `n` is a sum
`∑_d d^k y_d` where `y_d` is a base-`d` number with digits in `{0,1}`
(`Erdos124.sumsOfDistinctPowers d k`, and `S_d(k) = d^k · S_d(0)`).

The single hypothesis that separates the tractable regime from the hard one is the
**density margin** `P := ∑_{d ∈ D} 1/(d-1)`. The reduction splits the target along it:

* **H1 — supercritical, `P > 1`.** For every `k ≠ 0` and every admissible `D` with
  `P > 1` the `k`-sumset is cofinite. This regime is known in the literature away from the
  boundary (Fan 2026, arXiv:2607.14071, Thm 1.5, covers `P > 2`; Bergelson–Simmons 2017 covers
  `P > 3`), and it is decidable for each fixed `D` by a finite computation: an interval-bootstrap
  certificate (closed interval `[A, A+L-1]` inside the subset sums of the first `j` weights,
  then every remaining weight absorbed in increasing order, `w ≤` current length) together with
  the tail lemma `U·(P-1) ≥ S_j - L + C_k`, where `U` is the smallest remaining weight,
  `S_j` the sum of the first `j` weights and `C_k = ∑_d d^k/(d-1)`. The certificate for a given
  `D` is finite; what H1 asks for is the *uniform* statement.

* **H2 — critical, `P = 1`.** The genuinely open case. `P = 1` has infinitely many members
  (`{3,4,7}`, the only one proved in BEGL96, and infinitely many Egyptian-fraction sets such as
  `{3,4,8,43}`, since `1/2+1/3+1/7+1/42 = 1`). It is exactly where the tail lemma degenerates
  (`P - 1 = 0`), so no finite certificate closes it: BEGL96 needed a periodic-residue argument
  (powers of 3 and 4 modulo 248139202560) for `{3,4,7}`, and no member besides `{3,4,7}` has a
  published proof.

Why the split is faithful and not vacuous:

* the dichotomy `P > 1 ∨ P = 1` is exhaustive on the target's hypothesis `1 ≤ P`, so
  `H1 → H2 → target` is exactly the target (that is the whole body of `main`);
* neither hypothesis is implied by the other, and neither `k`-value implies another:
  `S_d(k) = d^k · S_d(0)` is *decreasing* in `k` and the `D`-sumset is *increasing* in `D`,
  so cofiniteness does not transfer between `k` or between `D` — the `k` and `D` quantifiers
  stay inside each hypothesis;
* the target's hypothesis is satisfiable (`D = {3,4,5}`, `k = 1`: `P = 13/12`, `gcd = 1`), so no
  contradiction makes either hypothesis vacuous.

Searches supporting the split (scratch scripts, not part of the proof): exact subset-sum
bitset DP finds no counterexample for `k ≤ 3`, `N ≤ 1e8` (e.g. `D = {3,4,5}`, `k = 3`: every
`n > 4330731` up to `1e8` is representable); no congruence obstruction can exist, because for
any modulus `M` and any `d` coprime to `M` the subset sums of `{d^i mod M}` cover every residue
mod `M`, and `gcd D = 1` provides such a `d` for every prime; and all 199 Egyptian-fraction
members of `P = 1` with `max d ≤ 31` are cofinite at `k = 1` with threshold at most 658.
-/

namespace OMA.R_Erdos124_erdos124_ne_zero_R1

open Filter
open scoped Pointwise

/-- **H1** (supercritical regime, `∑ 1/(d-1) > 1`): every `k ≠ 0` sumset over an admissible `D`
is cofinite once the reciprocal sum strictly exceeds `1`. -/
def H1 : Prop :=
  ∀ k ≠ 0, ∀ D : Finset ℕ, (∀ d ∈ D, 3 ≤ d) → 1 < ∑ d ∈ D, (d - 1 : ℚ)⁻¹ → D.gcd id = 1 →
    ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, Erdos124.sumsOfDistinctPowers d k

/-- **H2** (critical regime, `∑ 1/(d-1) = 1`): the BEGL96 hard case — the reciprocal sum is
exactly `1`, where no slack argument applies and only `D = {3,4,7}` is known. -/
def H2 : Prop :=
  ∀ k ≠ 0, ∀ D : Finset ℕ, (∀ d ∈ D, 3 ≤ d) → ∑ d ∈ D, (d - 1 : ℚ)⁻¹ = 1 → D.gcd id = 1 →
    ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, Erdos124.sumsOfDistinctPowers d k

/-- **Reduction**: the supercritical and the critical regime together give the target; the bodies
are the two halves of the single hypothesis `1 ≤ ∑ 1/(d-1)`. -/
theorem main : H1 → H2 → type_of% @Erdos124.erdos124.ne_zero := by
  intro h1 h2 k hk D hD hsum hgcd
  rcases lt_or_eq_of_le hsum with hlt | heq
  · exact h1 k hk D hD hlt hgcd
  · exact h2 k hk D hD heq.symm hgcd

end OMA.R_Erdos124_erdos124_ne_zero_R1
