import FormalConjectures.Wikipedia.ErdosMoser

-- Reduction ErdosMoser.erdos_moser_conjecture.R1 of The Erdős–Moser equation
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1: the odd-exponent case (classical, Moser: pair i with m-1-i, so m-1 divides 2).
-- H2: the even-exponent case (the open part): no solution at all.

namespace OMA.R_ErdosMoser_erdos_moser_conjecture_R1

def H1 : Prop :=
  ∀ k m : ℕ, 0 < k → 0 < m → Odd k → ErdosMoser.powerSum k m = m ^ k → k = 1 ∧ m = 3

def H2 : Prop :=
  ∀ k m : ℕ, 0 < k → 0 < m → Even k → ErdosMoser.powerSum k m ≠ m ^ k

theorem main : H1 → H2 → type_of% @ErdosMoser.erdos_moser_conjecture := by
  intro h1 h2 k m hk hm h
  rcases Nat.even_or_odd k with he | ho
  · exact absurd h (h2 k m hk hm he)
  · exact h1 k m hk hm ho h

end OMA.R_ErdosMoser_erdos_moser_conjecture_R1
