import Mathlib

/-!
# A002893: irreducibility of Zhi-Wei Sun's binomial polynomials

Source: https://oeis.org/A002893
Credit: @Bondyboy2001

Zhi-Wei Sun conjectured that for each positive integer `n`, the polynomial
`g_n(x) = ∑_{k=0}^n binom(n,k)^2 * binom(2k,k) * x^k` is irreducible over the rational numbers.
-/

namespace OMA.S_oeis_a002893

open Polynomial

/-- Sun's polynomial `g_n` over `ℚ`. -/
noncomputable def sunPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℚ) ^ 2 * ((2 * k).choose k : ℚ)) * X ^ k

/-- For every positive integer `n`, Sun's polynomial `g_n` is irreducible over `ℚ`. -/
theorem main : ∀ n : ℕ, 0 < n → Irreducible (sunPoly n) := by
  sorry

end OMA.S_oeis_a002893
