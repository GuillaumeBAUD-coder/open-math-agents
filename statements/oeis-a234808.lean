import Mathlib

/-!
# A234808: a(n) = |{0 < k < n: p = k + phi(n-k) and 2*n - p are both prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234808
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 except for n = 1, 8.

Formalization notes:
* phi = `Nat.totient`, sigma = `ArithmeticFunction.sigma 1`, prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2). "x is a square" is `IsSquare x`.
* 2n - p ≥ n since phi(n-k) ≤ n-k, so the subtraction in ℕ does not truncate.
* Stated for every n ≥ 1: a(n) = 0 iff n = 1 or n = 8.
* Controls (computed): a(1..30) = 0, 1, 1, 2, 2, 3, 2, 0, 3, 1, 2, 5, 2, 1, 5, 1, 2, 7, 2, 1, 4, 1, 2,
  1, 4, 1, 4, 2, 4, 11, as in the entry; a(n) = 0 for n < 300 only at n = 1, 8.
-/

namespace OMA.S_oeis_a234808


/-- A234808(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k =>
    (k + Nat.totient (n - k)).Prime ∧ (2 * n - (k + Nat.totient (n - k))).Prime).card

/-- The conjecture of the entry (all parts listed above). -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n = 1 ∨ n = 8) := by
  sorry

end OMA.S_oeis_a234808
