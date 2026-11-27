import FormalConjectures.OEIS.«1599»

-- Reduction OeisA1599.eq_one_of_odd_of_a.R1 of Ore's conjecture on odd harmonic numbers
-- Credit: @marcusbuffett

/-!
# Ore's harmonic numbers: prime powers, and the open rest

Ore's conjecture says that `1` is the only odd harmonic number (a number `n` for which
`σ(n) ∣ n * τ(n)`, that is, the harmonic mean of the divisors is an integer).

* `H1` (Ore, On the averages of the divisors of a number, Amer. Math. Monthly 55 (1948)): no
  prime power is harmonic. For `n = p^k` the divisor sum `1 + p + ⋯ + p^k` is coprime to `p^k`,
  so it would have to divide `k + 1`, and it is larger.
* `H2`: an odd harmonic number that is not a prime power equals `1`. This is the open problem
  and stays open.
-/

namespace OMA.R_OeisA1599_eq_one_of_odd_of_a_R1

/-- No prime power is a harmonic number. -/
def H1 : Prop :=
  ∀ n : ℕ, IsPrimePow n → ¬ OeisA1599.A n

/-- The open part: odd harmonic numbers that are not prime powers. -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA1599.A n → Odd n → ¬ IsPrimePow n → n = 1

theorem main : H1 → H2 → type_of% @OeisA1599.eq_one_of_odd_of_a := by
  intro h1 h2 n hn hodd
  by_cases hpp : IsPrimePow n
  · exact absurd hn (h1 n hpp)
  · exact h2 n hn hodd hpp

end OMA.R_OeisA1599_eq_one_of_odd_of_a_R1
