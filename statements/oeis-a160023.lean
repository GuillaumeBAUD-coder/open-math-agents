import Mathlib

/-!
# A160023: Primes whose fourth power plus the fourth powers of 7 and 3 is prime

Source: https://oeis.org/A160023
Credit: @gblacher2
-/

namespace OMA.S_oeis_a160023

theorem main : {p : ℕ | p.Prime ∧ (p ^ 4 + 7 ^ 4 + 3 ^ 4).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a160023
