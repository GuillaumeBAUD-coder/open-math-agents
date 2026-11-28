import FormalConjectures.OEIS.«7013»

-- Reduction OeisA7013.conjecture.R1 of the Catalan-Mersenne conjecture (A007013)
-- Credit: @marcusbuffett

/-!
# Catalan-Mersenne numbers: the five known primes, and the open rest

The sequence is `a 0 = 2`, `a (n + 1) = 2 ^ a n - 1`: `2, 3, 7, 127, 2^127 - 1, ...`. The
conjecture says every term is prime.

* `H1` (known): `a 0, ..., a 4` are prime. The only substantial case is
  `a 4 = 2^127 - 1 = 170141183460469231731687303715884105727`, proved prime by Lucas in 1876; it
  is certified by the Lucas-Lehmer test.
* `H2`: `a n` is prime for every `n ≥ 5`. This is open: `a 5 = 2^(2^127 - 1) - 1` is far beyond
  any known primality test, and no factor is known.
-/

namespace OMA.R_OeisA7013_conjecture_R1

/-- The first five Catalan-Mersenne numbers are prime. -/
def H1 : Prop :=
  ∀ n : ℕ, n ≤ 4 → (OeisA7013.a n).Prime

/-- The open part: the terms from `a 5` on. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 ≤ n → (OeisA7013.a n).Prime

theorem main : H1 → H2 → type_of% @OeisA7013.conjecture := by
  intro h1 h2 n
  by_cases hn : n ≤ 4
  · exact h1 n hn
  · exact h2 n (by omega)

end OMA.R_OeisA7013_conjecture_R1
