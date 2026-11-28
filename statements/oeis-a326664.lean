import Mathlib

/-!
# A326664: the column c of the solution of c(n) = a(n) + b(3n)

Source: https://oeis.org/A326664 (OEIS Foundation, CC BY-SA 4.0).

Entry A326664 (Clark Kimberling), offset 1: Column 3 of the array at A326661; see Comments.
Data 7, 16, 25, 35, 43, 52, 61, 71, 79, 88, 97, 107, 115, 124, 133, 142, 151, 160, 169, ...

Comments: This is the sequence (c(n)) defined by the complementary equation
c(n) = a(n) + b(3n), with initial value a(1) = 1. See A326661.
Conjecture: 9n-c(n) is in {1,2} for all n.

Related entry A326661: Rectangular array in 3 columns that solve the complementary equation
c(n) = a(n) + b(3n), where a(1) = 1. Let A = (a(n)), B = (b(n)), and C = (c(n)). A unique
solution (A,B,C) exists for the following conditions: (1) A,B,C must partition the positive
integers, and (2) A and B are defined by mex (minimal excludant); that is, a(n) is the least
"new" positive integer, and likewise for b(n). Rows (a(n), b(n), c(n)): (1, 2, 7), (3, 4, 16),
(5, 6, 25), (8, 9, 35), (10, 11, 43), (12, 13, 52), (14, 15, 61), ...
The program in A326661 (Peter J. C. Moses) builds the solution in rounds: round n places
a(3n-2), b(3n-2), a(3n-1), b(3n-1), a(3n), b(3n) in this order, each as the least new
number at its turn, and then places c(n) = a(n) + b(3n).

Formalization notes.
* `leastNew s` is the least positive integer that is not in the finite set `s` of the numbers
  already placed (the mex over the positive integers).
* `pair U` places a term of A and then a term of B, each as the least new number. It returns
  the two numbers and the new set of placed numbers.
* `state n` is the tuple (the function a on the indices placed so far, the function b on the
  indices placed so far, c(n), set of the numbers placed up to round n). The functions have the
  value 0 at the indices that are not yet placed, and `state 0` is the empty start. Round n + 1
  places a(3n+1), b(3n+1), a(3n+2), b(3n+2), a(3n+3), b(3n+3) and then
  c(n+1) = a(n+1) + b(3n+3) (the value a(n+1) is known at this time, because n+1 <= 3n+3).
  Round 1 places 1, 2, 3, 4, 5, 6 and c(1) = 1 + 6 = 7; round 2 places 8, 9, 10, 11, 12, 13
  and c(2) = 3 + 13 = 16, as in the rows above.
* `main` is the conjecture: for each n >= 1, 9n - c(n) is 1 or 2.
-/

namespace OMA.S_oeis_a326664

/-- The least positive integer that is not yet placed. -/
noncomputable def leastNew (s : Finset ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ k ∉ s}

/-- Place a term of A and then a term of B, each as the least new number. -/
noncomputable def pair (U : Finset ℕ) : ℕ × ℕ × Finset ℕ :=
  let A := leastNew U
  let B := leastNew (insert A U)
  (A, B, insert B (insert A U))

/-- The state after round n: (a on the indices up to 3n, b on the indices up to 3n, c(n),
placed numbers). -/
noncomputable def state : ℕ → (ℕ → ℕ) × (ℕ → ℕ) × ℕ × Finset ℕ
  | 0 => (fun _ => 0, fun _ => 0, 0, ∅)
  | n + 1 =>
    let p1 := pair (state n).2.2.2
    let p2 := pair p1.2.2
    let p3 := pair p2.2.2
    let α := Function.update (Function.update (Function.update (state n).1
      (3 * n + 1) p1.1) (3 * n + 2) p2.1) (3 * n + 3) p3.1
    let β := Function.update (Function.update (Function.update (state n).2.1
      (3 * n + 1) p1.2.1) (3 * n + 2) p2.2.1) (3 * n + 3) p3.2.1
    (α, β, α (n + 1) + β (3 * n + 3), insert (α (n + 1) + β (3 * n + 3)) p3.2.2)

/-- A326664. -/
noncomputable def c (n : ℕ) : ℕ := (state n).2.2.1

/-- Conjecture of Kimberling: 9n - c(n) is in {1, 2}. -/
theorem main : ∀ n : ℕ, 1 ≤ n → c n + 1 = 9 * n ∨ c n + 2 = 9 * n := by
  sorry

end OMA.S_oeis_a326664
