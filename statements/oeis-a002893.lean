import Mathlib

/-!
# A002893: a(n) = Sum_{k=0..n} binomial(n,k)^2 * binomial(2*k,k)

Source: https://oeis.org/A002893
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A002893): For each n = 1, 2, 3, ... the polynomial
g_n(x) = Sum_{k=0..n} binomial(n,k)^2 * binomial(2k,k) * x^k is irreducible over the field of
rational numbers.

Conventions:
* g_n is a polynomial in `ℚ[X]`, and irreducible is Mathlib's `Irreducible` in `ℚ[X]`.
-/

namespace OMA.S_oeis_a002893

open Polynomial

/-- Sun's polynomial `g_n(x) = Sum_{k=0..n} binomial(n,k)^2 * binomial(2k,k) * x^k` over `ℚ`. -/
noncomputable def g (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℚ) ^ 2 * ((2 * k).choose k : ℚ)) * X ^ k

/-- Sun's conjecture on A002893: `g_n` is irreducible over `ℚ` for every `n >= 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Irreducible (g n) := by
  sorry

end OMA.S_oeis_a002893
