import Mathlib

/-!
# Can this sum be majorized?

Source: https://mathoverflow.net/questions/300152
Credit: @ivillar

Status: false as stated. For `m = 2` and `r = (1, 1/2)` the sum with the `r_i` is
`2 * 1 - 1/2 = 3/2`, while the sum with the `r_i ^ 2` is `2 * 1 - 1/4 = 7/4` (the counterexample
`m = 2, r_1 = 1, r_2 = 0.5` is given in the comments to the question). The statement is kept as
the target of a disproof.

Suppose that we have real numbers $r_1, r_2, \dots, r_m \in [0,1]$ and we study the sum
$$ S_1 = \sum_{i=1}^m \binom{m}{i}(-1)^{i-1} f(r_i) $$
for $f : [0,1] \to [0,1]$ a concave bijection. Take another sequence $z_1, \dots, z_m \in [0,1]$
with $r_i \geq z_i$. Can we prove or disprove
$$ S_1 \geq S_2 = \sum_{i=1}^m \binom{m}{i}(-1)^{i-1} f(z_i)? $$
The asker then reduces the question to the case that is actually needed: $f(x) = x$,
$z_i = r_i^2$ for all $i$, with $1 \geq r_1 \geq r_2 \geq \cdots \geq r_m \geq 0$.

Formalization notes:
* `main` is the reduced claim: for a non-increasing sequence `r` with values in `[0, 1]`,
  `∑_{i=1}^m C(m,i) (-1)^(i-1) r_i ^ 2 ≤ ∑_{i=1}^m C(m,i) (-1)^(i-1) r_i`.
* The sequence is given as a function `r : ℕ → ℝ`, non-increasing with values in `[0, 1]`
  everywhere; only `r 1, …, r m` enter the sums.
-/

namespace OMA.S_mo_300152

theorem main : ∀ (m : ℕ) (r : ℕ → ℝ), (∀ i, 0 ≤ r i ∧ r i ≤ 1) → Antitone r →
    ∑ i ∈ Finset.Icc 1 m, (m.choose i : ℝ) * (-1) ^ (i - 1) * r i ^ 2 ≤
      ∑ i ∈ Finset.Icc 1 m, (m.choose i : ℝ) * (-1) ^ (i - 1) * r i := by
  sorry

end OMA.S_mo_300152
