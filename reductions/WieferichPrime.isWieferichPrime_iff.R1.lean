import FormalConjectures.Wikipedia.WieferichPrime

-- Reduction WieferichPrime.isWieferichPrime_iff.R1 of Wieferich primes — isWieferichPrime iff
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- main proves the known direction outright: 1093 and 3511 are Wieferich primes (the upstream
-- test theorems isWieferichPrime_1093 and isWieferichPrime_3511, checked by the kernel).
-- The converse, that there is no other Wieferich prime, is split at the search bound 2^64:
--   H1  every Wieferich prime below 2^64 is 1093 or 3511. This is known by computation:
--       PrimeGrid's Wieferich search, completed in 2022, found no other one below 2^64 (as the
--       upstream docstring also states). A formal proof would have to replace that search by
--       a kernel-checked one, which is far beyond what is feasible, so H1 is known but not a
--       routine step.
--   H2  there is no Wieferich prime at or above 2^64. This is the genuinely open part; the
--       heuristic count of log log x Wieferich primes up to x even suggests that it is false
--       (see the upstream infinite_isWieferichPrime).

namespace OMA.R_WieferichPrime_isWieferichPrime_iff_R1

/-- No Wieferich prime below 2^64 other than 1093 and 3511 (PrimeGrid search, 2022). -/
def H1 : Prop := ∀ p : ℕ, p < 2 ^ 64 → IsWieferichPrime p → p = 1093 ∨ p = 3511

/-- The open part: no Wieferich prime at or above 2^64. -/
def H2 : Prop := ∀ p : ℕ, 2 ^ 64 ≤ p → ¬ IsWieferichPrime p

theorem main : H1 → H2 → type_of% @WieferichPrime.isWieferichPrime_iff := by
  intro h1 h2 p
  constructor
  · intro hp
    by_cases hlt : p < 2 ^ 64
    · exact h1 p hlt hp
    · exact absurd hp (h2 p (not_lt.mp hlt))
  · rintro (rfl | rfl)
    · exact WieferichPrime.isWieferichPrime_1093
    · exact WieferichPrime.isWieferichPrime_3511

end OMA.R_WieferichPrime_isWieferichPrime_iff_R1
