import Mathlib

/-!
# A248568: Least positive integer m such that phi(m+n) divides m, where phi(.) is Euler's totient function.

Source: https://oeis.org/A248568
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) exists for any n > 0. Moreover, a(n) <= n*(n-1) for all n > 1.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m,
  and "a(n) ≤ B" is the existence of such an m with m ≤ B.
* Controls (computed): a(1..12) = 1, 2, 6, 2, 20, 4, 8, 4, 12, 40, 24, 6, as in the entry; both parts
  hold for n ≤ 60.
-/

namespace OMA.S_oeis_a248568



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ Nat.totient (m + n) ∣ m) ∧
      ∀ n : ℕ, 1 < n → ∃ m : ℕ, 0 < m ∧ m ≤ n * (n - 1) ∧ Nat.totient (m + n) ∣ m := by
  sorry

end OMA.S_oeis_a248568
