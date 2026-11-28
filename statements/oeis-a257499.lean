import Mathlib

/-!
# A257499: Array A read by upward antidiagonals in which the entry in row n and column k is defined by A(n,k) = (1 + 2^n*(6*k-3+2*(-1)^n))/3, n,k >= 1.

Source: https://oeis.org/A257499
Credit: @xor2k

Comment section of A257499 (the comment is not signed in the text available to us; it is
presumably by the author of the entry):
  Conjecture (now Lemma 1): The sequence is a permutation of the odd natural numbers.
  Reformulating the conjecture, we need to prove that for any integer m >= 0, the equation
  (1 + 2^n*(6*k - 3 + 2*(-1)^n))/3 = 2*m + 1 has a unique solution in integers n,k >= 1.

Only this conjecture (Lemma 1) of the entry is formalized here.

Conventions:
* `A n k` is the array entry of the title for row n ≥ 1 and column k ≥ 1, as an integer, with
  integer division by 3. The division is exact for all n, k ≥ 1; this exactness is the first
  conjunct of the statement, so that the integer division cannot hide anything.
* The sequence lists every entry A(n,k), n, k ≥ 1, exactly once (upward antidiagonals:
  A(1,1), A(2,1), A(1,2), A(3,1), A(2,2), A(1,3), ...), so the sequence is a permutation of the odd
  natural numbers iff (n,k) ↦ A(n,k) is a bijection from the pairs n, k ≥ 1 onto the odd natural
  numbers. This is stated as: every entry is of the form 2*m + 1 with m a natural number (second
  conjunct), and for every natural number m there is exactly one pair (n,k) with n, k ≥ 1 and
  A(n,k) = 2*m + 1 (third conjunct, which is literally the reformulation given in the entry).
  The antidiagonal enumeration itself is not formalized.

Numerical check: a Python copy of the definition, read by upward antidiagonals, gives
1, 7, 5, 3, 15, 9, 27, 19, 23, 13, 11, 59, 35, 31, 17, 107, 75, 91, 51, 39, 21, ...; the DATA
field of the entry is not available offline for comparison. Exactness of the division, oddness,
injectivity for n < 40, k < 20000, and attainment of every odd number below 20000 were checked.
-/

namespace OMA.S_oeis_a257499

/-- The array entry A(n,k) = (1 + 2^n*(6*k-3+2*(-1)^n))/3 (integer division; exact for n, k ≥ 1). -/
def A (n k : ℕ) : ℤ := (1 + 2 ^ n * (6 * (k : ℤ) - 3 + 2 * (-1) ^ n)) / 3

/-- Lemma 1 of the entry: the array is a permutation of the odd natural numbers. -/
theorem main :
    (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → (3 : ℤ) ∣ 1 + 2 ^ n * (6 * (k : ℤ) - 3 + 2 * (-1) ^ n)) ∧
    (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∃ m : ℕ, A n k = 2 * (m : ℤ) + 1) ∧
    (∀ m : ℕ, ∃! p : ℕ × ℕ, 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ A p.1 p.2 = 2 * (m : ℤ) + 1) := by
  sorry

end OMA.S_oeis_a257499
