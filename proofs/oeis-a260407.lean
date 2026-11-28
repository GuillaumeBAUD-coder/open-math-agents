import OMAStatements.S_oeis_a260407
import Mathlib

/-!
# A260407: (n-1)^2+1 divides 2^(n-1)-1 iff it divides (2^k)^(n-1)-1 for all k >= 1 (claim is true)

Statement. For every integer n >= 1, let M = (n-1)^2 + 1. The claim is that
M divides 2^(n-1) - 1 if and only if M divides (2^k)^(n-1) - 1 for every k >= 1.

Proof. Fix n >= 1 and put x = 2^(n-1). For every k, (2^k)^(n-1) = 2^(k(n-1)) = x^k.

1. Geometric-sum fact: for natural numbers a and k, a - 1 divides a^k - 1, because
   a^k - 1 = (a - 1)(a^(k-1) + ... + a + 1).
2. Forward direction. Assume M divides x - 1. Let k >= 1. By step 1 with a = x, x - 1 divides
   x^k - 1 = (2^k)^(n-1) - 1. Since M divides x - 1, transitivity gives M divides (2^k)^(n-1) - 1.
3. Backward direction. Assume M divides (2^k)^(n-1) - 1 for all k >= 1. Take k = 1: the number
   (2^1)^(n-1) - 1 is 2^(n-1) - 1, so M divides 2^(n-1) - 1.
-/

namespace OMA.S_oeis_a260407

/-- Step 0: (2^k)^(n-1) = (2^(n-1))^k, since both sides are 2 to the power k (n-1). -/
lemma two_pow_pow_comm (n k : ℕ) : (2 ^ k) ^ (n - 1) = (2 ^ (n - 1)) ^ k := by
  -- Rewrite both sides as 2 to the power of a product, then commute the factors.
  rw [← pow_mul, Nat.mul_comm k, pow_mul]

/-- Step 1 applied to a divisor: if d divides a - 1, then d divides a^k - 1 for every k. -/
lemma dvd_pow_sub_one_of_dvd {a d : ℕ} (h : d ∣ a - 1) (k : ℕ) : d ∣ a ^ k - 1 :=
  -- Chain d | a - 1 with the geometric-sum fact a - 1 | a^k - 1.
  h.trans (Nat.sub_one_dvd_pow_sub_one _ _)

end OMA.S_oeis_a260407

open OMA.S_oeis_a260407 in
/-- Steps 2 and 3: both directions of the equivalence for every n >= 1. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a260407.main := by
  intro n _
  constructor
  · -- Forward direction: rewrite (2^k)^(n-1) as x^k with x = 2^(n-1), then apply step 1.
    intro h k _
    rw [two_pow_pow_comm]
    exact dvd_pow_sub_one_of_dvd h k
  · -- Backward direction: the hypothesis at k = 1 is the statement for 2^(n-1) - 1.
    intro h
    simpa using h 1 (by decide)
