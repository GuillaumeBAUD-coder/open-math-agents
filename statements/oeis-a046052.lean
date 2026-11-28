import Mathlib

/-!
# A046052: Number of prime factors of Fermat number F(n).

Source: https://oeis.org/A046052
Credit: @tczyzycki

Here `a(n) = Ω(2^(2^n) + 1)` is the number of prime factors of the `n`-th Fermat number
`F(n) = 2^(2^n) + 1`, counted with multiplicity (offset 0: `a(0) = 1, ..., a(5) = 2, ...`).

Conjecture (John Selfridge): the sequence `a` is not monotonically nondecreasing, i.e.,
there exists `n : ℕ` such that `a(n + 1) < a(n)`.
-/

namespace OMA.S_oeis_a046052

/-- `A046052(n)`: the number of prime factors of the `n`-th Fermat number `2^(2^n) + 1`,
    counted with multiplicity (`Ω(F(n))`). -/
def a (n : ℕ) : ℕ :=
  ArithmeticFunction.cardFactors (2 ^ (2 ^ n) + 1)

/-- Selfridge's conjecture on Fermat numbers: `a` is not monotonic, so `a(n + 1) < a(n)`
    for some `n : ℕ`. -/
theorem main : ∃ n : ℕ, a (n + 1) < a n := by
  sorry

end OMA.S_oeis_a046052
