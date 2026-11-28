import Mathlib

/-!
# A006351: Number of series-parallel networks with n labeled edges.

Source: https://oeis.org/A006351
Credit: @MartinFoxy

The entry carries the formula (Mikhail Kurkov):
`Conjecture: a(n) = A379459(n-2,0) = A379460(n-1,0) for n > 1 with a(1) = 1.`
The same two claims appear in the entries of the arrays, as `A(n,0) = A006351(n+2)` in A379459
and `A(n,0) = A006351(n+1)` in A379460.

Formalization notes:
* A006351 has offset 1 (data: 1, 2, 8, 52, 472, 5504, 78416, ...). Its entry records that the
  exponential generating function `B(x) = Sum_{n>=1} a(n) x^n/n!` satisfies
  `B'(x) = (1 + B(x))/(1 - B(x))` with `B(0) = 0` (Vladimir Kruchinin, Jan 18 2011; Peter Bala,
  Sep 05 2011). Clearing the denominator gives `B' = 1 + B + B*B'`, and comparing coefficients
  of `x^n/n!` gives the recurrence used here: `a(0) = 0` and
  `a(n+1) = [n = 0] + a(n) + Sum_{k=1..n} binomial(n,k) * a(k) * a(n+1-k)`.
* A379459 is defined by its name: `A(0,k) = 2*(k+1)!` and
  `A(n,k) = A(n-1,k+1) + 2*(k+1)! * Sum_{j=0..k} A(n-1,j)/j!`, for `n, k >= 0`. Because of the
  division by `j!` it is computed in `ℚ`.
* A379460 is defined by its name: `A(0,k) = 1`, `A(n,0) = A(n-1,0) + A(n-1,1)` and
  `A(n,k) = A(n,k-1) + (k+1)*(A(n-1,k) + A(n-1,k+1))`, for `n, k >= 0`.
* The conjecture is stated for every `n > 1`; the clause `a(1) = 1` is part of the definition.
-/

namespace OMA.S_oeis_a006351

/-- A006351 (offset 1), from `B' = 1 + B + B*B'` for its exponential generating function. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if n = 0 then 1 else 0) + a n +
      ∑ k : Fin n, Nat.choose n (k + 1) * a (k + 1) * a (n - k)
decreasing_by all_goals omega

/-- The array A379459. -/
def A379459 : ℕ → ℕ → ℚ
  | 0, k => 2 * (k + 1).factorial
  | n + 1, k => A379459 n (k + 1) +
      2 * (k + 1).factorial * ∑ j ∈ Finset.range (k + 1), A379459 n j / j.factorial

/-- The array A379460. -/
def A379460 : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, 0 => A379460 n 0 + A379460 n 1
  | n + 1, k + 1 => A379460 (n + 1) k + (k + 2) * (A379460 n (k + 1) + A379460 n (k + 2))

/-- Kurkov's conjecture: `a(n) = A379459(n-2,0) = A379460(n-1,0)` for `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n →
    (a n : ℚ) = A379459 (n - 2) 0 ∧ a n = A379460 (n - 1) 0 := by
  sorry

end OMA.S_oeis_a006351
