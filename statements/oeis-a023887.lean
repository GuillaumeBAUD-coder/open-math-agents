import Mathlib

/-!
# A023887: a(n) = sigma_n(n): sum of n-th powers of divisors of n.

Source: https://oeis.org/A023887
Credit: @divmxnd0x

Conjecture (Rayhan Ahmed, Jun 19 2026, stated in A023887): 5 is the only prime in this sequence.

Formalization notes:
* Offset 1: `a 1, a 2, ... = 1, 5, 28, 273, 3126, ...`; `a 2 = 1 + 2^2 = 5` is prime.
* "5 is the only prime" is stated as: for every `n ≥ 1`, if `a n` is prime then `a n = 5`.
-/

namespace OMA.S_oeis_a023887

/-- A023887(n) = ∑_{d ∣ n} d^n. -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d ^ n

/-- The only prime value of `sigma_n(n)` is `5`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n).Prime → a n = 5 := by
  sorry

end OMA.S_oeis_a023887
