import Mathlib

/-!
# OEIS A059304: a(n) = Σ_{j,k} C(n,j) C(n,k) C(j+k,n)

Source: https://oeis.org/A059304
Credit: @SudharsanAnimations

`A059304(n) = 2^n (2n)!/(n!)^2`. Peter Bala conjectured (Jul 2024) that
`a(n) = Σ_{0 ≤ j, k ≤ n} binomial(n, j) binomial(n, k) binomial(j + k, n)` for all `n ≥ 0`; the entry
records this as a theorem, with a proof by coefficient extraction. We state the proved identity.

Conventions: offset `0`; `/` is natural-number division (exact here).
-/

namespace OMA.S_oeis_a059304

open Nat

/-- A059304: `a(n) = 2^n (2n)! / (n!)^2`. -/
def a (n : ℕ) : ℕ := 2 ^ n * (2 * n)! / (n ! ^ 2)

theorem main : ∀ n : ℕ,
    a n = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
      n.choose j * n.choose k * (j + k).choose n := by
  sorry

end OMA.S_oeis_a059304
