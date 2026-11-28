import OMAStatements.S_oeis_a078616
import Mathlib

/-!
# A078616: a(n) = Sum_{k=0..n} A010815(k) against ones in distinct partitions (false at n = 0)

Statement. Let A010815(k) be the coefficient of q^k in Product_{m>=1} (1 - q^m), and let
a(n) = Sum_{k=0..n} A010815(k). Let onesOdd(n) be the number of parts equal to 1, summed over
the distinct partitions of n with an odd number of parts, and let onesEven(n) be the same sum
over the distinct partitions of n with an even number of parts. The claim is that
a(n) = onesOdd(n) - onesEven(n) for every n >= 0.

The claim is false. Counterexample at n = 0:

1. A010815(0) is the coefficient of q^0 in the empty product, which is 1. Hence a(0) = 1.
2. The only partition of 0 is the empty partition. It has no parts, so it has no part equal to 1.
   Hence onesOdd(0) = 0 and onesEven(0) = 0.
3. So the right-hand side at n = 0 is 0 - 0 = 0.
4. Therefore a(0) = 1 is not equal to 0, and the identity fails at n = 0.
-/

namespace OMA.S_oeis_a078616

/-- Step 2: a partition of 0 has no part equal to 1, since every part is positive and the parts sum to 0. -/
lemma count_one_zero (p : Nat.Partition 0) : p.parts.count 1 = 0 := by
  have h := p.parts_sum
  -- Suppose the count of 1 is nonzero, so 1 is a part of p.
  by_contra hn
  have hm : 1 ∈ p.parts := Multiset.count_pos.mp (Nat.pos_of_ne_zero hn)
  -- A part is at most the sum of all parts, so 1 <= 0, which is false.
  have := Multiset.le_sum_of_mem hm
  omega

/-- Step 2 in total: the number of ones in distinct partitions of 0 with an odd number of parts is 0. -/
lemma onesOdd_zero : onesOdd 0 = 0 := by
  simp [onesOdd, count_one_zero]

/-- Step 2 in total: the number of ones in distinct partitions of 0 with an even number of parts is 0. -/
lemma onesEven_zero : onesEven 0 = 0 := by
  simp [onesEven, count_one_zero]

/-- Step 1: a(0) = A010815(0) = 1, the constant coefficient of the empty product. -/
lemma a_zero : a 0 = 1 := by
  simp [a, A010815]

end OMA.S_oeis_a078616

open OMA.S_oeis_a078616 in
/-- Steps 3 and 4: the identity at n = 0 would say 1 = 0 - 0, which is false. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a078616.main) := by
  intro h
  have h0 := h 0
  -- Rewrite a(0), onesOdd(0) and onesEven(0) to their values 1, 0 and 0.
  rw [a_zero, onesOdd_zero, onesEven_zero] at h0
  -- h0 : 1 = 0 - 0 in the integers, which is a contradiction.
  norm_num at h0
