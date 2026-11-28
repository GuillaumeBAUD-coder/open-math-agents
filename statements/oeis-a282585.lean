import Mathlib

/-!
# A282585: number of ordered sums of 3 squarefree palindromes (A071251).

Source: https://oeis.org/A282585
Credit: @cjchaffin

Additional conjecture (on the OEIS page): every number `> 3` can be written as the sum of
4 squarefree palindromes.

Conventions:
- Offset 0; a squarefree palindrome is a positive integer which is `Squarefree` and whose
  base-10 digits (via `Nat.digits 10`) form a palindrome, matching A071251 (the generating
  function of the page starts at `k ≥ 1`, so 0 is excluded).
- The conjecture is an existence statement, so unordered sums and repeated summands are
  allowed, consistent with the ordinary generating function used for the 3-summand count.
- The page’s first conjecture (`a(n) > 0` for sufficiently large `n`) is not formalized,
  because it gives no explicit bound.
-/

namespace OMA.S_oeis_a282585

def IsSquarefreePalindrome (k : ℕ) : Prop :=
  0 < k ∧ Squarefree k ∧ (Nat.digits 10 k).reverse = Nat.digits 10 k

theorem main : ∀ n : ℕ, 3 < n →
    ∃ a b c d : ℕ,
      IsSquarefreePalindrome a ∧ IsSquarefreePalindrome b ∧
        IsSquarefreePalindrome c ∧ IsSquarefreePalindrome d ∧
        a + b + c + d = n := by
  sorry

end OMA.S_oeis_a282585
