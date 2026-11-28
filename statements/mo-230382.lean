import Mathlib

/-!
# Optimization on Binomial coefficients

Source: https://mathoverflow.net/questions/230382
Credit: @ivillar

Status: false as stated. As pointed out in the comments to the question, `C(N-1, r-1)` is bigger
than the guessed value `C(N-1, r)` when `r ≥ N/2`: for `N = 5000`, `r = 4999` the choice
`m₀ = 1`, `m₁ = 4999`, `j = 1` gives `C(1,1) * C(4999,4998) = 4999`, while `C(4999,4999) = 1`.
The statement is kept as the target of a disproof.

Suppose we are given integers $1\leq r\leq N$, we want to study the following
$$ \max_{m_0+m_1=N,\ m_0,m_1\geq 1}\ \max_j \tbinom {m_0}{j}\tbinom {m_1}{r-j}. $$
$N$ is very large, for instance $N\geq 5000$. I guess it is $\tbinom {N-1}{r}$.

Formalization notes:
* `main` is the guess: for `N ≥ 5000` and `1 ≤ r ≤ N`, the number `C(N-1, r)` is the greatest
  element of the set of values `C(m₀, j) * C(m₁, r - j)` with `m₀ + m₁ = N`, `m₀, m₁ ≥ 1` and
  `0 ≤ j ≤ r`.
-/

namespace OMA.S_mo_230382

theorem main : ∀ N r : ℕ, 5000 ≤ N → 1 ≤ r → r ≤ N →
    IsGreatest {x : ℕ | ∃ m₀ m₁ j : ℕ, 1 ≤ m₀ ∧ 1 ≤ m₁ ∧ m₀ + m₁ = N ∧ j ≤ r ∧
      x = m₀.choose j * m₁.choose (r - j)} ((N - 1).choose r) := by
  sorry

end OMA.S_mo_230382
