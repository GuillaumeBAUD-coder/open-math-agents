import Mathlib

/-!
# A219782: Number of ways to write n=x+y (0<x<=y) with n^2-xy and n^2+xy both prime.

Source: https://oeis.org/A219782
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
1. a(n) > 0 if n is not among 1, 8, 10, 18, 20, 41, 46, 58, 78, 116, 440.
2. For any k = 0, 1, 2, 4, 5, 6, ... (k ≠ 3) and positive odd integer m, each sufficiently large
   integer n can be written as x + y (0 < x <= y) with |m*n^k - xy| and |m*n^k + xy| all prime.

Formalization notes:
* With y = n - x, "0 < x <= y" is 0 < x and 2x ≤ n. n^2 - xy ≥ 0 here, so ℕ subtraction is exact.
* In conjecture 2 the absolute value is taken in ℤ (`Int.natAbs`); "sufficiently large" is
  "there is N such that for all n ≥ N".
* Controls (computed): for n < 1500, a(n) = 0 exactly at the 11 listed n.
-/

namespace OMA.S_oeis_a219782

/-- A219782(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n / 2)).filter fun x => (n ^ 2 - x * (n - x)).Prime ∧ (n ^ 2 + x * (n - x)).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → n ∉ ({1, 8, 10, 18, 20, 41, 46, 58, 78, 116, 440} : Finset ℕ) → 0 < a n) ∧
      ∀ k m : ℕ, k ≠ 3 → Odd m → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ x : ℕ, 0 < x ∧ 2 * x ≤ n ∧
        (Int.natAbs ((m : ℤ) * n ^ k - x * (n - x))).Prime ∧ (m * n ^ k + x * (n - x)).Prime := by
  sorry

end OMA.S_oeis_a219782
