import Mathlib

/-!
# A248354: Least positive integer m such that m + n divides prime(m^2) + prime(n^2).

Source: https://oeis.org/A248354
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) exists for any n > 0. Moreover, a(n) <= n*(n-1)/2 for all n > 1.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m,
  and "a(n) ≤ B" is the existence of such an m with m ≤ B.
* prime(k) = `Nat.nth Nat.Prime (k - 1)`.
* Controls (computed): a(1..12) = 1, 1, 2, 1, 3, 8, 2, 6, 6, 45, 9, 4, as in the entry; both parts
  hold for n ≤ 60.
-/

namespace OMA.S_oeis_a248354

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ prime (m ^ 2) + prime (n ^ 2)) ∧
      ∀ n : ℕ, 1 < n → ∃ m : ℕ, 0 < m ∧ m ≤ n * (n - 1) / 2 ∧ m + n ∣ prime (m ^ 2) + prime (n ^ 2) := by
  sorry

end OMA.S_oeis_a248354
