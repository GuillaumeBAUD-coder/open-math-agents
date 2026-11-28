import OMAStatements.S_oeis_a207642
import Mathlib

/-!
# A207642: the claimed equality a(n) = b(n) fails at n = 2

Statement. Let a(n) be the coefficient of x^n in the series Sum_{k>=0} x^k Prod_{j=0..k-1} (1 + x^(k+j)).
Let b(n) be the number of partitions of n into distinct parts p such that max(p) <= 1 + 2 min(p).
The claim is that a(n) = b(n) for every n >= 1.

The claim is false. Counterexample at n = 2:

1. Compute a(2), the coefficient of x^2. A summand with index k has the factor x^k times a
   polynomial with constant term 1, so it contributes to x^2 only when k <= 2.
   - k = 0: the summand is 1, whose x^2 coefficient is 0.
   - k = 1: the summand is x (1 + x) = x + x^2, whose x^2 coefficient is 1.
   - k = 2: the summand is x^2 (1 + x^2)(1 + x^3), whose x^2 coefficient is 1.
   Hence a(2) = 0 + 1 + 1 = 2.
2. Compute b(2). The partitions of 2 are {2} and {1, 1}. Only {2} has distinct parts, and it satisfies
   max = 2 <= 1 + 2 * 2 = 5. Hence b(2) = 1.
3. So a(2) = 2 and b(2) = 1 differ, and the claimed equality fails at n = 2.
-/

namespace OMA.S_oeis_a207642

/-- Step 1: the coefficient of x^2 in the defining series is 2. Only the summands with index 0, 1, 2
contribute, with coefficients 0, 1, 1 (see the header). -/
lemma a_two : a 2 = 2 := by
  norm_num [a, Finset.sum_range_succ, Finset.prod_range_succ, mul_add,
    add_mul, ← pow_add, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]

/-- Step 2, the key fact: a partition of 2 with distinct parts is the single part 2. Its parts form a
subset of {1, 2} with sum 2, and the only such subset is {2}. -/
lemma distinct_partition_two_eq (p : Nat.Partition 2) (hp : p.parts.Nodup) :
    p = Nat.Partition.indiscrete 2 := by
  -- View the parts of p as a finset S; distinctness makes this faithful.
  let S : Finset ℕ := ⟨p.parts, hp⟩
  -- Every part is positive and at most 2, so S lies in the powerset of {1, 2}.
  have hS : S ∈ ({1,2} : Finset ℕ).powerset := by
    apply Finset.mem_powerset.mpr
    intro x hx
    change x ∈ p.parts at hx
    have := p.parts_pos hx
    have := Nat.Partition.le_of_mem_parts hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  -- The parts sum to 2.
  have sumS : S.sum id = 2 := by simpa [Finset.sum, S] using p.parts_sum
  -- Finite check: the only subset of {1, 2} with sum 2 is {2}.
  have small : ∀ T ∈ ({1,2} : Finset ℕ).powerset, T.sum id = 2 → T = {2} := by decide
  have he := congrArg Finset.val (small S hS sumS)
  apply Nat.Partition.ext
  simpa [S] using he

/-- Step 2: b(2) = 1. The only distinct-part partition of 2 is {2}, and it satisfies the bound. -/
lemma b_two : b 2 = 1 := by
  unfold b
  -- Rewrite 1 as the cardinality of the one-element set {indiscrete 2}, which is the partition {2}.
  rw [show (1 : ℕ) = ({Nat.Partition.indiscrete 2} : Finset _).card by simp]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · -- Distinct parts force p = {2}, by the lemma above.
    intro hp
    exact distinct_partition_two_eq p hp.1
  · -- The partition {2} has distinct parts and satisfies max <= 1 + 2 min, so it is counted.
    rintro rfl
    simp

end OMA.S_oeis_a207642

open OMA.S_oeis_a207642 in
/-- Step 3: a(2) = 2 and b(2) = 1 contradict the claimed equality at n = 2. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a207642.main) := by
  intro h
  -- Instantiate the claim at n = 2 (1 <= 2 holds), giving a(2) = b(2).
  have := h 2 (by decide)
  -- Combine with a(2) = 2 and b(2) = 1 to get 2 = 1.
  rw [a_two, b_two] at this
  omega
