import FormalConjectures.Wikipedia.FeitThompsonPrimeConjecture

-- Reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1 of Feit-Thompson conjecture on primes
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Write N = (q ^ p - 1) / (q - 1) = sum of q ^ i for i < p and M = (p ^ q - 1) / (p - 1).
-- H1: if q % p = 1 then p divides N but M % p = 1 (this includes p = 2).
-- H2: if q % p is not 1, p % 4 = 3 and q % 4 = 1, then N % p = 1 and N % 4 = 3.
--     A division N | M gives p ^ q = 1 mod N, so the Jacobi symbol (p | N) is 1 (q is odd),
--     but quadratic reciprocity gives (p | N) = -(N | p) = -(1 | p) = -1.
-- H3: all remaining pairs (the open part).

namespace OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1

/-- The case q % p = 1: then p divides the first quotient but not the second. -/
def H1 : Prop :=
  ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p = 1 →
    ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)

/-- The case q % p ≠ 1, p % 4 = 3, q % 4 = 1: excluded by Jacobi reciprocity. -/
def H2 : Prop :=
  ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p ≠ 1 → p % 4 = 3 → q % 4 = 1 →
    ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)

/-- All remaining pairs of primes p < q. -/
def H3 : Prop :=
  ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p ≠ 1 → ¬ (p % 4 = 3 ∧ q % 4 = 1) →
    ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)

theorem main : H1 → H2 → H3 → type_of% @FeitThompsonPrimeConjecture.feit_thompson_primes := by
  intro h1 h2 h3 p q hp hq h
  by_cases hm : q % p = 1
  · exact h1 p q hp hq h hm
  by_cases hc : p % 4 = 3 ∧ q % 4 = 1
  · exact h2 p q hp hq h hm hc.1 hc.2
  · exact h3 p q hp hq h hm hc

end OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1
