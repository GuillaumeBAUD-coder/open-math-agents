import Mathlib

/-!
# Nonzero terms of OEIS A096069

Source: https://oeis.org/A096069, Amarnath Murthy (2004).
Credit: @MMexicann

A term is zero exactly when no qualifying prime exists. The two known zero
terms correspond to the first and third primes, 2 and 5. The conjecture says
that every other prime occurs as a decimal suffix of a prime that is 1 modulo
the suffix. Congruence modulo ten to the number of digits expresses that suffix.
-/

namespace OMA.S_oeis_a096069

theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 →
    ∃ q : ℕ, q.Prime ∧ q ≡ p [MOD 10 ^ (Nat.digits 10 p).length] ∧ q ≡ 1 [MOD p] := by
  sorry

end OMA.S_oeis_a096069
