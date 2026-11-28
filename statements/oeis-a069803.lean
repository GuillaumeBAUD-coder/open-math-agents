import Mathlib

/-!
# A069803: Smaller of two consecutive palindromic primes.

Source: https://oeis.org/A069803
Credit: @keiichisince1986-bot

A069803 lists the smaller member of each pair of consecutive primes that are both palindromes:
`2, 3, 5, 7, 181, 787, 919` (the pairs are `(2, 3), (3, 5), (5, 7), (7, 11), (181, 191),`
`(787, 797), (919, 929)`; the larger members form A069804).
The entry states: Conjectured to be complete.

Conventions:
- Two consecutive palindromic primes means two consecutive primes `p < q` (no prime strictly
  between them) that are both palindromes. This is the reading the data follow: `11` and `101`
  are consecutive among palindromic primes but are not consecutive primes, and `11` is not a term.
- `IsPalindrome n`: the decimal digit list of `n` equals its reverse.
- `IsNextPrime p q`: `q` is the least prime greater than `p`.
- Complete means that the data list every term, so the conjecture says that the set of such
  smaller members is exactly `{2, 3, 5, 7, 181, 787, 919}`.
-/

namespace OMA.S_oeis_a069803

/-- `n` is a palindrome in base 10. -/
def IsPalindrome (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- `q` is the least prime greater than `p`. -/
def IsNextPrime (p q : ℕ) : Prop :=
  q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬ r.Prime

theorem main :
    {p : ℕ | p.Prime ∧ IsPalindrome p ∧ ∃ q : ℕ, IsNextPrime p q ∧ IsPalindrome q} =
      {2, 3, 5, 7, 181, 787, 919} := by
  sorry

end OMA.S_oeis_a069803
