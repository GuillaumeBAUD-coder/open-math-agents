import FormalConjectures.OEIS.«108866»

-- Reduction OeisA108866.conjecture.R1 of OEIS A108866 — conjecture
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target characterises the primes `n > 3` by a congruence for the numerator of a rational
-- expression. The two directions are independent.

namespace OMA.R_OeisA108866_conjecture_R1

open OeisA108866

/-- Excluding composites: if the numerator is divisible by `n ^ 2` then `n` is prime. -/
def H1 : Prop :=
  ∀ n : ℕ, n > 3 → (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] → n.Prime

/-- Verifying the primes: for a prime `n > 3` the numerator is divisible by `n ^ 2`. -/
def H2 : Prop :=
  ∀ n : ℕ, n > 3 → n.Prime → (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)]

theorem main : H1 → H2 → type_of% @OeisA108866.conjecture := by
  intro h1 h2 n hn
  exact ⟨h1 n hn, h2 n hn⟩

end OMA.R_OeisA108866_conjecture_R1
