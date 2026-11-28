import Mathlib

/-!
# A010048: polynomials with Fibonomial coefficients

Source: https://oeis.org/A010048
Credit: @Moti1125

A010048 is the triangle of Fibonomial coefficients
`T(n, k) = F(1) ⋯ F(n) / ((F(1) ⋯ F(k)) · (F(1) ⋯ F(n - k)))`, `0 ≤ k ≤ n`, where `F` is the
Fibonacci sequence with `F(1) = F(2) = 1`.

Conjecture (from the entry): the polynomials with (positive) Fibonomial coefficients are reducible
iff `n` is odd and `n > 1`.

Conventions:
- The `n`-th polynomial is row `n` of the triangle, `P n = ∑_{k=0}^{n} T(n, k) X^k`, with rational
  coefficients. Its leading and constant coefficients are `1`, so by Gauss's lemma it is
  irreducible over `ℚ` iff it is irreducible over `ℤ`.
- `P 0 = 1` is a unit, which is neither reducible nor irreducible, so the statement is for
  `n ≥ 1`. There `P n` has degree `n ≥ 1`, and "reducible" means "not irreducible".
- `T(n, k)` is computed with natural-number division of the Fibonacci products, which is exact.
-/

namespace OMA.S_oeis_a010048

open Polynomial

/-- The product `F(1) ⋯ F(n)` of the first `n` Fibonacci numbers. -/
def fibProd (n : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 n, Nat.fib i

/-- The Fibonomial coefficient `T(n, k)`, for `k ≤ n`. -/
def fibonomial (n k : ℕ) : ℕ := fibProd n / (fibProd k * fibProd (n - k))

/-- The polynomial `∑_{k=0}^{n} T(n, k) X^k`. -/
noncomputable def fibonomialPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (fibonomial n k : ℚ) * X ^ k

theorem main :
    ∀ n : ℕ, 1 ≤ n → (¬ Irreducible (fibonomialPoly n) ↔ (Odd n ∧ 1 < n)) := by
  sorry

end OMA.S_oeis_a010048
