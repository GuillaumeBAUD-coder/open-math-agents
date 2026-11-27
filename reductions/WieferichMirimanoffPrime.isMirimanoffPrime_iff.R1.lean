import FormalConjectures.Wikipedia.WieferichMirimanoffPrime

-- Reduction WieferichMirimanoffPrime.isMirimanoffPrime_iff.R1 of Can a prime $p$ satisfy $2^{p-1} \equiv 1 \pmod{p^2}$ and $3^{p-1} \equiv 1 \pmod{p^2}$? — isMirimanoffPrime iff
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- main proves the known direction outright: 11 and 1006003 are Mirimanoff primes, i.e.
-- 3^(p-1) is 1 modulo p^2 (the upstream test theorems
-- isMirimanoffPrime_and_not_isWieferichPrime_11 and _1006003, checked by the kernel).
-- The converse, that there is no other Mirimanoff prime, is split at the search bound
-- 9.7 * 10^14:
--   H1  every Mirimanoff prime below 970000000000000 is 11 or 1006003. This is known by
--       computation: Dorais and Klyve (A Wieferich prime search up to 6.7 * 10^15, J. Integer
--       Seq. 14 (2011)) found no other base-3 Wieferich prime below 9.7 * 10^14, as the upstream
--       docstring also states. A formal proof would have to replace that search by a
--       kernel-checked one, far beyond what is feasible, so H1 is known but not routine.
--   H2  there is no Mirimanoff prime at or above 970000000000000. This is the genuinely open
--       part; the usual heuristic predicts infinitely many base-3 Wieferich primes.

namespace OMA.R_WieferichMirimanoffPrime_isMirimanoffPrime_iff_R1

/-- No Mirimanoff prime below 9.7 * 10^14 other than 11 and 1006003 (Dorais and Klyve). -/
def H1 : Prop :=
  ∀ p : ℕ, p < 970000000000000 → IsMirimanoffPrime p → p = 11 ∨ p = 1006003

/-- The open part: no Mirimanoff prime at or above 9.7 * 10^14. -/
def H2 : Prop := ∀ p : ℕ, 970000000000000 ≤ p → ¬ IsMirimanoffPrime p

theorem main : H1 → H2 → type_of% @WieferichMirimanoffPrime.isMirimanoffPrime_iff := by
  intro h1 h2 p
  constructor
  · intro hp
    by_cases hlt : p < 970000000000000
    · exact h1 p hlt hp
    · exact absurd hp (h2 p (not_lt.mp hlt))
  · rintro (rfl | rfl)
    · exact WieferichMirimanoffPrime.isMirimanoffPrime_and_not_isWieferichPrime_11.1
    · exact WieferichMirimanoffPrime.isMirimanoffPrime_and_not_isWieferichPrime_1006003.1

end OMA.R_WieferichMirimanoffPrime_isMirimanoffPrime_iff_R1
