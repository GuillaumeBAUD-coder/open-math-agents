import Mathlib

/-!
# A058188: Number of primes between prime(n) and prime(n) + sqrt(prime(n)), where prime(n) is the n-th prime.

Source: https://oeis.org/A058188
Credit: @divmxnd0x

Conjecture (stated in A058188): if `prime(n) ≥ 127`, there is always at least one prime between
`prime(n)` and `prime(n) + sqrt(prime(n))`.

Formalization notes:
* Stated for every prime `p ≥ 127`: there is a prime `q` with `p < q < p + sqrt p` (real square
  root). For smaller primes it fails at `p = 3, 7, 13, 23, 31, 113`.
-/

namespace OMA.S_oeis_a058188

/-- For every prime `p ≥ 127` there is a prime strictly between `p` and `p + sqrt p`. -/
theorem main : ∀ p : ℕ, p.Prime → 127 ≤ p →
    ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) < p + Real.sqrt p := by
  sorry

end OMA.S_oeis_a058188
