import Mathlib

/-!
# A001223: Prime gaps: differences between consecutive primes.

Source: https://oeis.org/A001223
Credit: @MartinFoxy

The entry carries two conjectures of Zhi-Wei Sun in its Comments section:
* Conjecture: For any positive numbers x and y, there is an index k such that
  `x/y = a(k)/a(k+1)`.
* Conjecture: For any three positive numbers x, y and j, there is an index k such that
  `x/y = a(k)/a(k+j)`.

Formalization notes:
* The sequence has offset 1: `a(n) = prime(n+1) - prime(n)` with `prime(1) = 2`
  (data from n = 1: 1, 2, 2, 4, 2, 4, 2, 4, 6, ...). Mathlib's `Nat.nth Nat.Prime` counts from 0,
  so `a(n) = Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)` for `n ≥ 1`.
* The quotients `a(k)/a(k+1)` are rational, so the positive numbers `x`, `y` are positive
  integers, as is the shift `j`. The equality of quotients is stated in `ℚ`, and an index is
  an integer `k ≥ 1`.
* The entry also has a comment relating Cramér's conjecture to a bound on
  `(log prime(n+1)/log prime(n))^n`. It asserts an equivalence without fixing its quantifiers
  and is not one of the two conjectures above; it is not formalized here.
-/

namespace OMA.S_oeis_a001223

/-- A001223 (offset 1): `a(n) = prime(n+1) - prime(n)`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

/-- Zhi-Wei Sun's two conjectures on quotients of prime gaps. -/
theorem main :
    (∀ x y : ℕ, 0 < x → 0 < y →
      ∃ k : ℕ, 1 ≤ k ∧ (x : ℚ) / (y : ℚ) = (a k : ℚ) / (a (k + 1) : ℚ)) ∧
    (∀ x y j : ℕ, 0 < x → 0 < y → 0 < j →
      ∃ k : ℕ, 1 ≤ k ∧ (x : ℚ) / (y : ℚ) = (a k : ℚ) / (a (k + j) : ℚ)) := by
  sorry

end OMA.S_oeis_a001223
