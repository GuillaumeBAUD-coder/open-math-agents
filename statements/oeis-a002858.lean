import Mathlib

/-!
# A002858: Ulam numbers: a(1) = 1; a(2) = 2; for n>2, a(n) = least number > a(n-1) which is a unique sum of two distinct earlier terms.

Source: https://oeis.org/A002858
Credit: @mattdorman

The source states: Ulam conjectured that this sequence has density 0. (It adds that calculations up
to 6.759 · 10⁸ suggest the density hovers near 0.074.)

Reading used here: the sequence is indexed from `0`, so `u 0 = 1`, `u 1 = 2`, and for `n ≥ 1` the
term `u (n + 1)` is the least `m > u n` with exactly one representation `m = u i + u j` with
`i < j ≤ n` (two distinct earlier terms, as an unordered pair). These conditions determine the
sequence, so quantifying over every sequence that satisfies them is the same as speaking of the
Ulam numbers. Density `0` is natural density: `#{terms ≤ N} / N → 0`. Since the terms are
strictly increasing with `u i ≥ i + 1`, the terms `≤ N` are the `u i ≤ N` with `i ≤ N`.
-/

open Filter Topology

namespace OMA.S_oeis_a002858

/-- `u` satisfies the defining recursion of the Ulam numbers. -/
def IsUlamSequence (u : ℕ → ℕ) : Prop :=
  u 0 = 1 ∧ u 1 = 2 ∧ ∀ n, 1 ≤ n →
    IsLeast {m : ℕ | u n < m ∧ ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.2 ≤ n ∧ u p.1 + u p.2 = m}
      (u (n + 1))

theorem main :
    ∀ u : ℕ → ℕ, IsUlamSequence u →
      Tendsto (fun N : ℕ => (((Finset.range (N + 1)).filter (fun i => u i ≤ N)).card : ℝ) / N)
        atTop (𝓝 0) := by
  sorry

end OMA.S_oeis_a002858
