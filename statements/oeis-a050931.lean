import Mathlib

/-!
OEIS A050931: Numbers having a prime factor congruent to 1 mod 6.

Conjecture (OEIS): the terms are exactly the numbers m such that
abs(Sum_{k=1..m} [k|m]*A008683(k)*(-1)^(2*k/3)) = 0,
where A008683 is the Moebius function and (-1)^(2k/3) is the principal complex power,
i.e. exp(2*Pi*i*k/3).
-/

namespace OMA.S_oeis_a050931

theorem main :
    ∀ m : ℕ, 1 ≤ m →
      ((∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 6 = 1) ↔
        ‖∑ k ∈ Finset.Icc 1 m,
            (if k ∣ m then ((ArithmeticFunction.moebius k : ℤ) : ℂ) * (-1 : ℂ) ^ ((2 * (k : ℂ)) / 3) else 0)‖ = 0) := by
  sorry

end OMA.S_oeis_a050931
