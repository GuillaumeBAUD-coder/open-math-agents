import FormalConjectures.OEIS.«217785»

-- Reduction OeisA217785.conjecture_3.R1 of Smallest integer $s > n$ such that $1 + 2s + 3s^2 + \dots + n s^{n-1}$ is prime — conjecture 3
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1: the case n + 2 prime. Then s_n(X + 1) is Eisenstein at p = n + 2, since its X^j coefficient is (j + 1) * C(n + 2, j + 2).
-- H2: the case n + 2 composite (the open part).

namespace OMA.R_OeisA217785_conjecture_3_R1

def H1 : Prop := ∀ n : ℕ, 1 ≤ n → (n + 2).Prime →
  Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217785.polyS n))

def H2 : Prop := ∀ n : ℕ, 1 ≤ n → ¬ (n + 2).Prime →
  Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217785.polyS n))

theorem main : H1 → H2 → type_of% @OeisA217785.conjecture_3 := by
  intro h1 h2 n hn
  by_cases hp : (n + 2).Prime
  · exact h1 n hn hp
  · exact h2 n hn hp

end OMA.R_OeisA217785_conjecture_3_R1
