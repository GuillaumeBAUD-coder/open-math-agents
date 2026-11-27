import FormalConjectures.OEIS.«5258»

-- Reduction OeisA5258.conjecture.R1 of Apéry numbers
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Split on whether n + 1 is prime. When p = n + 1 is prime, every coefficient of x^k with
-- 1 ≤ k ≤ n has p-adic valuation exactly 1, so the reversed polynomial is p-Eisenstein.

namespace OMA.R_OeisA5258_conjecture_R1

/-- The case where n + 1 is prime (Eisenstein at p = n + 1 after reversal). -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → (n + 1).Prime → Irreducible (OeisA5258.aperyPoly n)

/-- The case where n + 1 is not prime (open). -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ¬ (n + 1).Prime → Irreducible (OeisA5258.aperyPoly n)

theorem main : H1 → H2 → type_of% @OeisA5258.conjecture := by
  intro h1 h2 n hn
  by_cases hp : (n + 1).Prime
  · exact h1 n hn hp
  · exact h2 n hn hp

end OMA.R_OeisA5258_conjecture_R1
