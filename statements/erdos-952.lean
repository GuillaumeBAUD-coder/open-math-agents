import Mathlib

/-!
# Erdős Problem 952 (Gaussian moat problem)

Source: https://www.erdosproblems.com/952
Credit: @joshuadc11

Is there an infinite sequence of distinct Gaussian primes `x₁, x₂, ...` such that
`|x_{n+1} - x_n| ≪ 1`?
The source notes that the answer is almost certainly negative (the Gaussian moat conjecture).

Formalization notes:
- Gaussian integers are `GaussianInt` (`ℤ[i]`), and Gaussian primes are `Prime x` in
  `GaussianInt`.
- Since `(z : GaussianInt).norm = |z|^2`, bounded Euclidean step size `|x_{n+1} - x_n| ≤ M`
  is equivalent to `(x (n + 1) - x n).norm ≤ C` for a constant `C : ℤ`.
- Stated in the conjectured negative form (no such sequence exists).
-/

namespace OMA.S_erdos_952

theorem main :
    ¬ ∃ (x : ℕ → GaussianInt) (C : ℤ),
      Function.Injective x ∧
      (∀ n, Prime (x n)) ∧
      (∀ n, (x (n + 1) - x n).norm ≤ C) := by
  sorry

end OMA.S_erdos_952
