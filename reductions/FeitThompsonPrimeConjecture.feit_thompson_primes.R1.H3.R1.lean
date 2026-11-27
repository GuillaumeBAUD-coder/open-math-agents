import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1

-- Reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H3.R1 of step FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H3
-- Credit: @jagong-cmu
-- Write N = (q ^ p - 1) / (q - 1) and M = (p ^ q - 1) / (p - 1).
-- H1 (class S): if N has a prime factor r with q not dividing r - 1, then N does not divide M.
--   Proof idea: r divides M, so p ^ q = 1 in ZMod r. The order of p is 1 or q. Order 1 gives
--   M = q mod r, so r = q, but N = 1 mod q. Order q gives q | r - 1.
-- H2: the rest, where every prime factor r of N has q | r - 1 (so 2pq | r - 1). Open.
--   For p = 3 this is the case q = 11 mod 12 with q ^ 2 + q + 1 prime.

namespace OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1

/-- Class S: N has a prime factor r with q not dividing r - 1. -/
def H1 : Prop :=
  ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p ≠ 1 → ¬ (p % 4 = 3 ∧ q % 4 = 1) →
    (∃ r : ℕ, r.Prime ∧ r ∣ (q ^ p - 1) / (q - 1) ∧ ¬ q ∣ r - 1) →
    ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)

/-- The rest: every prime factor r of N has q | r - 1. -/
def H2 : Prop :=
  ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p ≠ 1 → ¬ (p % 4 = 3 ∧ q % 4 = 1) →
    (∀ r : ℕ, r.Prime → r ∣ (q ^ p - 1) / (q - 1) → q ∣ r - 1) →
    ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)

theorem main : H1 → H2 → OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H3 := by
  intro h1 h2 p q hp hq h hm hc
  by_cases hs : ∃ r : ℕ, r.Prime ∧ r ∣ (q ^ p - 1) / (q - 1) ∧ ¬ q ∣ r - 1
  · exact h1 p q hp hq h hm hc hs
  · refine h2 p q hp hq h hm hc ?_
    intro r hr hrN
    by_contra hqr
    exact hs ⟨r, hr, hrN, hqr⟩

end OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1
