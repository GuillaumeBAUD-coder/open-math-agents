import Mathlib

/-!
# A297292: the sequence b of a system of three complementary equations

Source: https://oeis.org/A297292 (OEIS Foundation, CC BY-SA 4.0).

Entry A297292 (Clark Kimberling, 2018), offset 0: Solution (b(n)) of the system of 3
complementary equations in Comments.
Data 3, 6, 7, 11, 14, 15, 19, 20, 23, 25, 29, 30, 34, 36, 39, 40, 43, 46, 49, 50, ...

Comments: Define sequences a(n), b(n), c(n) recursively:
a(n) = least new;
b(n) = least new > = a(n) + 2;
c(n) = a(n) + b(n) - 2;
where least new k means the least positive integer not yet placed.
The sequences a,b,c partition the positive integers.
Conjectures: for n >= 0,
0 <= 5*n + 4 - 2*a(n) <= 5,
0 <= 5*n + 8 - 2*b(n) <= 4,
0 <= c(n) - 5n <= 4.

Example: n = 0, 1, 2, 3, 4, 5, ... gives a = 1, 4, 5, 9, 12, 13, ..., b = 3, 6, 7, 11, 14, 15, ...
and c = 2, 8, 10, 18, 24, 26, ...

Formalization notes.
* `leastNewFrom s t` is the least integer k >= t that is not in the finite set `s` of the numbers
  placed so far. The least new number is `leastNewFrom s 1` (the least positive integer not yet
  placed), and the least new number >= a(n) + 2 is `leastNewFrom s (a(n) + 2)`, where `s` now
  contains a(n).
* `step U` performs step n from the set `U` of the numbers placed in the steps before n: it places
  a(n), then b(n), then c(n) = a(n) + b(n) - 2, and returns (a(n), b(n), c(n), new placed set).
* `state n` is the result of step n; step 0 starts from the empty set. This gives
  (a(0), b(0), c(0)) = (1, 3, 2), then (4, 6, 8) and (5, 7, 10), as in the example.
* `main` is the conjunction of the three conjectured two-sided bounds for every n >= 0, written
  in the integers.
-/

namespace OMA.S_oeis_a297292

/-- The least integer k >= t that is not in `s`. -/
noncomputable def leastNewFrom (s : Finset ℕ) (t : ℕ) : ℕ := sInf {k : ℕ | t ≤ k ∧ k ∉ s}

/-- One step from the set `U` of placed numbers: (a, b, c, new set of placed numbers). -/
noncomputable def step (U : Finset ℕ) : ℕ × ℕ × ℕ × Finset ℕ :=
  let A := leastNewFrom U 1
  let B := leastNewFrom (insert A U) (A + 2)
  (A, B, A + B - 2, insert (A + B - 2) (insert B (insert A U)))

/-- The result of step n: (a(n), b(n), c(n), set of the numbers placed in steps 0, ..., n). -/
noncomputable def state : ℕ → ℕ × ℕ × ℕ × Finset ℕ
  | 0 => step ∅
  | n + 1 => step (state n).2.2.2

noncomputable def a (n : ℕ) : ℕ := (state n).1
/-- A297292. -/
noncomputable def b (n : ℕ) : ℕ := (state n).2.1
noncomputable def c (n : ℕ) : ℕ := (state n).2.2.1

/-- Conjectures of Kimberling. -/
theorem main : ∀ n : ℕ,
    (0 ≤ 5 * (n : ℤ) + 4 - 2 * (a n : ℤ) ∧ 5 * (n : ℤ) + 4 - 2 * (a n : ℤ) ≤ 5) ∧
    (0 ≤ 5 * (n : ℤ) + 8 - 2 * (b n : ℤ) ∧ 5 * (n : ℤ) + 8 - 2 * (b n : ℤ) ≤ 4) ∧
    (0 ≤ (c n : ℤ) - 5 * (n : ℤ) ∧ (c n : ℤ) - 5 * (n : ℤ) ≤ 4) := by
  sorry

end OMA.S_oeis_a297292
