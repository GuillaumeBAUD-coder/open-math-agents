import Mathlib

/-!
# A068012: Number of subsets of {1,2,3,...,n} that sum to 0 mod 6.

Source: https://oeis.org/A068012
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 1, 2, 3, 6, 12, 22, 44, 88, 172, 344, ...
It is defined as in the name of the entry: the number of subsets of {1, ..., n} whose sum of
elements is divisible by 6 (the empty set, with sum 0, is counted).

From David A. Corneth, Sep 13 2025:
Conjecture: a(n) = 2*a(n-1) for n > 2 and 3 does not divide n-1.
a(3*k+1) = 2*a(3*k) - 2^(k-1), k >= 1, 3*k + 1 = n.
If this conjecture is true then a(3*k + 1 + r) = ((2*4^k - 2)/3 + 1)*2^(k-1+r)
where k >= 1 and r in {0, 1, 2}.
All three assertions are stated (the division by 3 in the last one is exact).
-/

namespace OMA.S_oeis_a068012

/-- A068012: the number of subsets of {1, ..., n} whose sum is 0 mod 6. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).powerset.filter (fun s => (∑ i ∈ s, i) % 6 = 0)).card

/-- Corneth's conjecture for A068012 and the closed form it implies. -/
theorem main :
    (∀ n : ℕ, 2 < n → ¬ 3 ∣ (n - 1) → a n = 2 * a (n - 1)) ∧
    (∀ k : ℕ, 1 ≤ k → (a (3 * k + 1) : ℤ) = 2 * (a (3 * k) : ℤ) - 2 ^ (k - 1)) ∧
    (∀ k r : ℕ, 1 ≤ k → r ≤ 2 →
      a (3 * k + 1 + r) = ((2 * 4 ^ k - 2) / 3 + 1) * 2 ^ (k - 1 + r)) := by
  sorry

end OMA.S_oeis_a068012
