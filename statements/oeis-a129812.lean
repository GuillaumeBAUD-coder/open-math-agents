import Mathlib

/-!
# A129812: lesser of consecutive prime pairs whose last digits differ by 6.

Source: https://oeis.org/A129812
Credit: @cjchaffin

Conjecture (on the OEIS page): the number of terms is infinite. Example: the last
digits of the consecutive primes 7 and 11 differ by 6, so 7 is a term.

Conventions: last digits are residues modulo 10; “differ by 6” means the natural
distance between those residues is 6. The infinitude statement does not depend on
the official offset.
-/

namespace OMA.S_oeis_a129812

def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬ r.Prime

def LastDigitsDifferBy (d p q : ℕ) : Prop :=
  Int.natAbs ((p % 10 : ℤ) - (q % 10)) = d

theorem main : {p : ℕ | ∃ q : ℕ, ConsecutivePrimes p q ∧ LastDigitsDifferBy 6 p q}.Infinite := by
  sorry

end OMA.S_oeis_a129812
