import FormalConjectures.OEIS.«224»

-- Reduction OeisA224.conjecture.R1 of OEIS A000224 — conjecture
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target characterises the primes `n != 2` by the congruence `n ^ 2 = 1` modulo
-- `a n * (a n - 1)`. The two directions are independent.

namespace OMA.R_OeisA224_conjecture_R1

open OeisA224

/-- Forward direction: for a prime `n != 2` the congruence holds. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n.Prime ∧ n ≠ 2 → n ^ 2 ≡ 1 [MOD a n * (a n - 1)]

/-- Backward direction: if the congruence holds then `n` is a prime different from `2`. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → n ^ 2 ≡ 1 [MOD a n * (a n - 1)] → n.Prime ∧ n ≠ 2

theorem main : H1 → H2 → type_of% @OeisA224.conjecture := by
  intro h1 h2 n hn
  exact ⟨h1 n hn, h2 n hn⟩

end OMA.R_OeisA224_conjecture_R1
