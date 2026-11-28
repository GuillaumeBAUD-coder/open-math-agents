import Mathlib

/-!
# OEIS A284654: the n-th 0 of the 0-limiting word of 0 -> 1, 1 -> 0110 stays near n * r

Source: https://oeis.org/A284654 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code, submitted by @SSmurf.

Entry (Clark Kimberling, Apr 07 2017), offset 1: Positions of 0 in A284653; complement of A284655.
Comment: Conjecture: -1 < n*r - a(n) < 3 for n >= 1, where r = (3+sqrt(3))/2.
A284653 is the 0-limiting word of the morphism 0 -> 1, 1 -> 0110.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` is the k-th iterate of the morphism applied to the word 0:
  0 -> 1 -> 0110 -> 1011001101 -> ...
  The iterates with an even number of steps start with 0 and each extends the previous even one;
  those with an odd number of steps start with 1 and each extends the previous odd one. As in the
  comment of A284653, the 0-limiting word is the limit of the iterates with an even number of
  steps (it starts 0, 1, 1, 0, 1, 0, 1, 1, as the data of A284653).
* `A284653 i` is the i-th letter (i >= 1) of that word, read off `iter (2 * i)`, which has more
  than i letters; any later iterate of the same parity gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A284653(i) = 0, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1. The first terms are
  a(1..8) = 1, 4, 6, 9, 10, 13, 16, 19, the entry's data.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1, with
  r = (3+sqrt(3))/2 as in the entry.
-/

namespace OMA.S_oeis_a284654

/-- The morphism 0 -> 1, 1 -> 0110 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1]
  | _ => [0, 1, 1, 0]

/-- The k-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [0]

/-- A284653(i) for i >= 1: the i-th letter of the 0-limiting word, read off `iter (2 * i)`. -/
def A284653 (i : ℕ) : ℕ := (iter (2 * i)).getD (i - 1) 0

/-- A284654(n) for n >= 1: the position of the n-th 0 in A284653. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A284653 i = 0) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -1 < (n : ℝ) * ((3 + Real.sqrt 3) / 2) - a n ∧
      (n : ℝ) * ((3 + Real.sqrt 3) / 2) - a n < 3 := by
  sorry

end OMA.S_oeis_a284654
