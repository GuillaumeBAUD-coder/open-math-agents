import Mathlib

/-!
# A055023: a(n) = n/A055032(n).

Source: https://oeis.org/A055023
Credit: @azmiozgen

Conjecture (from the entry; Giuga's conjecture): this is n iff n is 1 or a prime.

Formalization notes:
* A055032(n) is the denominator (in lowest terms) of (Sum_{m=1..n-1} m^(n-1) + 1)/n; it divides
  n, so a(n) = n / A055032(n) is exact division in ℕ.
* The conjecture is stated for every n ≥ 1 (offset 1).
* Controls: a(1..12) = 1, 2, 3, 1, 5, 2, 7, 1, 1, 2, 11, 1, as in the entry.
-/

namespace OMA.S_oeis_a055023

/-- A055032(n): the denominator of `(∑_{m=1}^{n-1} m^(n-1) + 1) / n`. -/
def den (n : ℕ) : ℕ := ((∑ m ∈ Finset.Icc 1 (n - 1), (m : ℚ) ^ (n - 1) + 1) / n).den

/-- A055023(n) = n / A055032(n). -/
def a (n : ℕ) : ℕ := n / den n

/-- Giuga's conjecture in the form of the entry: `a(n) = n` iff `n` is `1` or a prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = n ↔ n = 1 ∨ n.Prime) := by
  sorry

end OMA.S_oeis_a055023
