import Mathlib

/-!
# A029576: two conjectured recurrences

Source: https://oeis.org/A029576
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. Both statements
follow from the closed form of the entry, which is used as the definition here.

A029576 (offset 0): number of permutations of an n-set containing a 9-cycle;
data 0, 0, 0, 0, 0, 0, 0, 0, 0, 40320, 403200, 4435200, 53222400, ...

Conjectures from Stéphane Rézel, Nov 24 2019:
(1) a(n) = n*a(n-1), for n > 9 and n !== 0 (mod 9);
(2) for k > 1, a(9*k) = a(9*k-1)*S(k)/S(k-1) where S(k) = 9*k*S(k-1) - (-1)^k with S(1) = 1.

Formalization: the entry records the closed form a(n) = n! * (1 - Sum_{k=0..floor(n/9)} (-1)^k/(9^k * k!)),
and this formula (with values in ℚ) is the definition of a(n) used here. S is defined by the stated
recurrence; S(0) = 0 is the value for which the recurrence at k = 1 gives S(1) = 1, and only S(k) with
k ≥ 1 occurs in `main`. `main` is the conjunction of (1) and (2). Checked on the data, for example
a(10) = 403200 = 10 * 40320, and a(18) = 671854030848000 = a(17)*S(2)/S(1) = 39520825344000 * 17 / 1.
-/

namespace OMA.S_oeis_a029576

/-- a(n) = n! * (1 - Sum_{k=0..floor(n/9)} (-1)^k / (9^k * k!)), the closed form recorded in the entry. -/
def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) *
    (1 - ∑ k ∈ Finset.range (n / 9 + 1), (-1 : ℚ) ^ k / (9 ^ k * (k.factorial : ℚ)))

/-- S(k) = 9*k*S(k-1) - (-1)^k with S(1) = 1 (and S(0) = 0). -/
def S : ℕ → ℚ
  | 0 => 0
  | (k + 1) => 9 * ((k : ℚ) + 1) * S k - (-1) ^ (k + 1)

/-- The two conjectured recurrences of A029576. -/
theorem main : (∀ n : ℕ, 9 < n → n % 9 ≠ 0 → a n = (n : ℚ) * a (n - 1)) ∧
    (∀ k : ℕ, 1 < k → a (9 * k) = a (9 * k - 1) * S k / S (k - 1)) := by
  sorry

end OMA.S_oeis_a029576
