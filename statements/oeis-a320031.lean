import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a320031

/-- OEIS A320031: square array `A(n, k) = ∑_{j=0}^{n} C(n, j) * j! * k^j`,
whose column `k` has exponential generating function `exp(x) / (1 - k * x)`. -/
def a320031 (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), Nat.choose n j * j.factorial * k ^ j

/-- OEIS A371898: lower triangular matrix `L(n, k)` defined by `L(n, 0) = 1`,
`L(0, k + 1) = 0`, and `L(n + 1, k + 1) = (n + 1) * (k + 1) * (L(n, k) + L(n, k + 1))`. -/
def a371898 : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => (n + 1) * (k + 1) * (a371898 n k + a371898 n (k + 1))

/-- OEIS A320031 conjecture (Werner Schulte, Apr 14 2024):
For every `n : ℕ`, the exponential generating function of row `n` of `A320031` is
`exp(x) * (∑_{i=0}^{n} A371898(n, i) * x^i / i!)`; equivalently, for every `k : ℕ`,
the `k`-th exponential coefficient satisfies
`A(n, k) / k! = ∑_{i=0}^{min(k, n)} (1 / (k - i)!) * (A371898(n, i) / i!)`. -/
theorem main :
    ∀ n k : ℕ,
      (a320031 n k : ℚ) / (k.factorial : ℚ) =
        ∑ i ∈ Finset.range (min k n + 1),
          (1 / ((k - i).factorial : ℚ)) * ((a371898 n i : ℚ) / (i.factorial : ℚ)) := by
  sorry

end OMA.S_oeis_a320031
