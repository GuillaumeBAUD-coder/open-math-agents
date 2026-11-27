import FormalConjectures.OEIS.«2426»

-- Reduction OeisA2426.conjecture.R1 of Central trinomial coefficients
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1 is the known half (Z.-W. Sun): every prime p > 3 satisfies a(p) = 1 mod p^2.
-- H2 is the open half: no composite n > 3 satisfies a(n) = 1 mod n^2.

/-! Split of OeisA2426.conjecture into the known prime half and the open composite half. -/

namespace OMA.R_OeisA2426_conjecture_R1

def H1 : Prop := ∀ p : ℕ, 3 < p → p.Prime → OeisA2426.a p ≡ 1 [MOD p ^ 2]

def H2 : Prop := ∀ n : ℕ, 3 < n → ¬ n.Prime → ¬ OeisA2426.a n ≡ 1 [MOD n ^ 2]

theorem main : H1 → H2 → type_of% @OeisA2426.conjecture := by
  intro h1 h2 n hn
  constructor
  · exact h1 n hn
  · intro h
    by_contra hp
    exact h2 n hn hp h

end OMA.R_OeisA2426_conjecture_R1
