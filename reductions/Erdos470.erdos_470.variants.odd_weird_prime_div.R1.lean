import FormalConjectures.ErdosProblems.«470»

/-!
# Reduction of the Liddy–Riedl bound on odd weird numbers

An odd weird number must have at least six distinct prime divisors. The proof splits by the
number of prime divisors of `n`: rule out at most three, then rule out exactly four, then rule out
exactly five; the conclusion follows by arithmetic on the count.
-/

-- Reduction Erdos470.erdos_470.variants.odd_weird_prime_div.R1
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1

/-- An odd weird number has more than three distinct prime divisors. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Weird → 4 ≤ {m | m ∈ n.divisors ∧ m.Prime}.ncard

/-- An odd weird number does not have exactly four distinct prime divisors. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.Weird → {m | m ∈ n.divisors ∧ m.Prime}.ncard ≠ 4

/-- An odd weird number does not have exactly five distinct prime divisors. -/
def H3 : Prop :=
  ∀ n : ℕ, Odd n → n.Weird → {m | m ∈ n.divisors ∧ m.Prime}.ncard ≠ 5

theorem main : H1 → H2 → H3 →
    type_of% @Erdos470.erdos_470.variants.odd_weird_prime_div := by
  intro h1 h2 h3 n hn hw
  have a := h1 n hn hw
  have b := h2 n hn hw
  have c := h3 n hn hw
  omega

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1
