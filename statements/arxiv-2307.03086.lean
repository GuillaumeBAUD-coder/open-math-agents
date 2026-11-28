import Mathlib

/-!
# Sun's conjectural series for $\frac56\pi^3$

Source: Z.-W. Sun, *New series involving binomial coefficients (II)*,
https://arxiv.org/abs/2307.03086 (conjecture quoted in the abstract, v10)
Credit: @SulkBash

## The problem (as the source states it)

We conjecture that
$$\sum_{k=0}^\infty\frac{\binom{2k}k^3}{4096^k}\left(9(42k+5)\sum_{0\le j<k}\frac1{(2j+1)^4}
  +\frac{25}{(2k+1)^3}\right)=\frac 56\pi^3.$$

This refines Ramanujan's classical series
$\sum_{k\ge0}(42k+5)\binom{2k}k^3/4096^k = 16/\pi$.

## Formalization notes

* `term k` is the $k$-th summand. The inner sum over $0 \le j < k$ is
  `∑ j ∈ Finset.range k, 1 / (2j+1)^4`, which is empty for $k = 0$.
* All quantities are real, with every natural number cast to `ℝ`.
* `HasSum term (5/6 * π^3)` asserts unconditional convergence to $\frac56\pi^3$. Every term is
  nonnegative, so this is equivalent to convergence of the partial sums. Moreover
  $\binom{2k}{k}^3/4096^k \le 64^{-k}$, so the series converges absolutely, at a geometric rate.
-/

namespace OMA.S_arxiv_2307_03086

open Real

/-- The `k`-th summand of Sun's series. -/
noncomputable def term (k : ℕ) : ℝ :=
  ((Nat.choose (2 * k) k : ℝ) ^ 3 / 4096 ^ k) *
    (9 * (42 * (k : ℝ) + 5) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * (j : ℝ) + 1) ^ 4 +
      25 / (2 * (k : ℝ) + 1) ^ 3)

/-- Sun's conjecture: the series sums to `5π³/6`. -/
theorem main : HasSum term (5 / 6 * π ^ 3) := by
  sorry

end OMA.S_arxiv_2307_03086
