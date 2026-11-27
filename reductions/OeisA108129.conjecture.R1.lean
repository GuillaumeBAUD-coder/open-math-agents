import FormalConjectures.OEIS.«108129»

-- Reduction OeisA108129.conjecture.R1 of Riesel Problem
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1: 509203 is a Riesel number (covering set 3, 5, 7, 13, 17, 241 with period 24).
-- H2: no smaller odd k = 2n - 1 is a Riesel number (the open part of the Riesel problem).

namespace OMA.R_OeisA108129_conjecture_R1

def H1 : Prop := OeisA108129.a 254602 = -1

def H2 : Prop := ∀ n : ℕ, 1 ≤ n ∧ n < 254602 → OeisA108129.a n ≠ -1

theorem main : H1 → H2 → type_of% @OeisA108129.conjecture := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_OeisA108129_conjecture_R1
