import FormalConjectures.OEIS.«234246»

-- Reduction OeisA234246.conjecture_2.R1 of OEIS A234246 — conjecture 2
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target says that `a n = 1` exactly at the nine listed indices. The two directions of the
-- iff are independent: excluding the other indices, and verifying the listed ones.

namespace OMA.R_OeisA234246_conjecture_2_R1

open OeisA234246

/-- Forward direction: if `a n = 1` then `n` is one of the nine listed indices. -/
def H1 : Prop :=
  ∀ n : ℕ, a n = 1 → n ∈ ({4, 5, 8, 9, 12, 13, 24, 33, 49} : Finset ℕ)

/-- Backward direction: at each of the nine listed indices the value is `1`. -/
def H2 : Prop :=
  ∀ n : ℕ, n ∈ ({4, 5, 8, 9, 12, 13, 24, 33, 49} : Finset ℕ) → a n = 1

theorem main : H1 → H2 → type_of% @OeisA234246.conjecture_2 := by
  intro h1 h2 n
  exact ⟨h1 n, h2 n⟩

end OMA.R_OeisA234246_conjecture_2_R1
