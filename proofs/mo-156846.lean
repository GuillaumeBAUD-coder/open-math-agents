import OMAStatements.S_mo_156846
import Mathlib

/-!
# MO 156846: the linear system has no solution for n = 1 (the claim is false)

Statement. Let H_n = Sum_{j=0..n-1} 1/(j+1) and C(n) = 2 (n + 1 - H_n) / (n (n + 1)).
Let the forcing term be f(n, i) = 1/(i+2) - C(n). The claim is that for every n >= 1 there is a
real sequence w(0), w(1), ... such that

(a) for every i < n:  w(i) - (1/(i+1)) * Sum_{j=0..i} w(n - (i+1) + j) = f(n, i), and
(b) Sum_{i=0..n-1} (i+1) w(i) = 0.

The claim is false. Counterexample at n = 1, using only condition (a) for row i = 0:

1. H_1 = 1, so C(1) = 2 (1 + 1 - 1) / (1 * 2) = 1.
2. The forcing term for n = 1, i = 0 is f(1, 0) = 1/2 - C(1) = -1/2.
3. In row i = 0 the inner sum runs over j = 0 only, and the index n - (i+1) + j = 1 - 1 + 0 = 0.
   So the left-hand side is w(0) - (1/1) w(0) = 0.
4. Thus any solution would satisfy 0 = -1/2, which is impossible. No solution exists for n = 1.
-/

namespace OMA.S_mo_156846

/-- Step 1: the constant C(1) equals 1, because H_1 = 1 and C(1) = 2 (1 + 1 - 1) / (1 * 2). -/
lemma constant_one : constant 1 = 1 := by
  norm_num [constant]

/-- Step 2: the forcing term at n = 1, i = 0 is 1/2 - C(1) = -1/2. -/
lemma forcing_one_zero : forcing 1 0 = -1 / 2 := by
  norm_num [forcing, constant_one]

end OMA.S_mo_156846

open OMA.S_mo_156846 in
/-- Steps 3 and 4: row 0 of the system with n = 1 reads 0 = -1/2, which is a contradiction. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_156846.main) := by
  intro h
  -- Use the claim at n = 1 (0 < 1 holds) to get a candidate sequence w with its system.
  obtain ⟨w, hw⟩ := h 1 (by decide)
  -- Row i = 0 of condition (a).
  have row := hw.1 0 (by decide)
  -- Step 2: replace the right-hand side by -1/2.
  rw [forcing_one_zero] at row
  -- Step 3: the left-hand side simplifies to w 0 - w 0 = 0, so row says 0 = -1/2, which is false.
  norm_num at row
