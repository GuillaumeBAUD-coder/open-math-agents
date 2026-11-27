import FormalConjectures.OEIS.«7406»

-- Reduction OeisA7406.conjecture.R1 of Wolstenholme numbers
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1: the prime case (a Wolstenholme-type congruence). H2: the composite case (gcd is 1).

namespace OMA.R_OeisA7406_conjecture_R1

def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n.Prime → Nat.gcd n (OeisA7406.a (n - 1)) = OeisA89026.a n

def H2 : Prop :=
  ∀ n : ℕ, 3 < n → ¬ n.Prime → Nat.gcd n (OeisA7406.a (n - 1)) = OeisA89026.a n

theorem main : H1 → H2 → type_of% @OeisA7406.conjecture := by
  intro h1 h2 n hn
  by_cases hp : n.Prime
  · exact h1 n hn hp
  · exact h2 n hn hp

end OMA.R_OeisA7406_conjecture_R1
