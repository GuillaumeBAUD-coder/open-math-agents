import OMAStatements.S_oeis_a173614
import Mathlib

-- Proof of Velin Yanev's conjecture in OEIS A173614 (statement by @ivillar).
-- Idea: rad(n) is the product of the distinct primes p | n, which are pairwise coprime, so
-- λ(rad n) = lcm_p λ(p) (Mathlib's `carmichael_finsetProd`), and λ(p) = p - 1 for a prime p.

namespace OMAA173614Helpers

theorem carm_prime (p : ℕ) (hp : p.Prime) : ArithmeticFunction.carmichael p = p - 1 := by
  rcases eq_or_ne p 2 with rfl | h2
  · have := ArithmeticFunction.carmichael_two_pow_of_le_two (n := 1) (by norm_num)
    simpa using this
  · have := ArithmeticFunction.carmichael_pow_of_prime_ne_two 1 hp h2
    rw [pow_one] at this
    rw [this, Nat.totient_prime hp]

end OMAA173614Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a173614.main := by
  intro n _
  rw [Nat.radical_eq_prod_primeFactors]
  have hcop : Set.Pairwise (n.primeFactors : Set ℕ) (Nat.Coprime.onFun fun p => p) := by
    intro p hp q hq hpq
    show Nat.Coprime p q
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  have := ArithmeticFunction.carmichael_finsetProd (s := n.primeFactors) (f := fun p => p) hcop
  rw [this, OMA.S_oeis_a173614.a]
  apply Finset.lcm_congr rfl
  intro p hp
  simp [OMAA173614Helpers.carm_prime p (Nat.prime_of_mem_primeFactors hp)]
