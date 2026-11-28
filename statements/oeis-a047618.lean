import Mathlib

/-!
# A047618: Numbers that are congruent to {0, 2, 5} mod 8.

Source: https://oeis.org/A047618
Credit: @vivanpoddar

The sequence (offset 1) begins 0, 2, 5, 8, 10, 13, 16, 18, 21, 24, ...
It is defined as in the name of the entry: a(n) is the n-th nonnegative integer that is congruent
to 0, 2 or 5 mod 8 (Nat.nth counts from 0, so a(n) is Nat.nth at n - 1).

Conjecture (L. Edson Jeffery, Sep 02 2014): a(n)+a(n+1)+a(n+2) = 8*n-1; or
a(n) = 8*(n-2)-a(n-1)-a(n-2)-1, n>3, with a(1)=0, a(2)=2, a(3)=5.
Both forms are stated, the first for n >= 1 (the offset), the second for n > 3 together with the
three initial values.
-/

namespace OMA.S_oeis_a047618

/-- A047618 (offset 1): the n-th nonnegative integer congruent to 0, 2 or 5 mod 8. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => m % 8 = 0 ∨ m % 8 = 2 ∨ m % 8 = 5) (n - 1)

/-- The conjectured relations for A047618. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) + a (n + 1) + a (n + 2) = 8 * n - 1) ∧
    ((∀ n : ℕ, 3 < n → (a n : ℤ) = 8 * (n - 2) - a (n - 1) - a (n - 2) - 1) ∧
      a 1 = 0 ∧ a 2 = 2 ∧ a 3 = 5) := by
  sorry

end OMA.S_oeis_a047618
