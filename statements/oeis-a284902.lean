import Mathlib

/-!
# OEIS A284902: the n-th 0 of the fixed point of 0 -> 01, 1 -> 1000 stays near n * r

Source: https://oeis.org/A284902 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code, submitted by @SSmurf.

Entry (Clark Kimberling, Apr 16 2017), offset 1: Positions of 0 in A284901; complement of A284903.
Comment: Conjecture: -3 < n*r - a(n) < 3 for n >= 1, where r = (3+sqrt(3))/3.
A284901 is the fixed point of the morphism 0 -> 01, 1 -> 1000.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` is the k-th iterate of the morphism applied to the word 0. The image of 0 starts
  with 0, so each iterate extends the one before, and their limit is the fixed point (it starts
  0, 1, 1, 0, 0, 0, 1, 0, as the data of A284901).
* `A284901 i` is the i-th letter (i >= 1) of the fixed point, read off `iter i`, which has more than
  i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A284901(i) = 0, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1. The first terms are
  a(1..8) = 1, 4, 5, 6, 8, 9, 10, 11, the entry's data.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1, with
  r = (3+sqrt(3))/3 as in the entry.
-/

namespace OMA.S_oeis_a284902

/-- The morphism 0 -> 01, 1 -> 1000 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [0, 1]
  | _ => [1, 0, 0, 0]

/-- The k-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [0]

/-- A284901(i) for i >= 1: the i-th letter of the fixed point, read off `iter i`. -/
def A284901 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A284902(n) for n >= 1: the position of the n-th 0 in A284901. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A284901 i = 0) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -3 < (n : ℝ) * ((3 + Real.sqrt 3) / 3) - a n ∧
      (n : ℝ) * ((3 + Real.sqrt 3) / 3) - a n < 3 := by
  sorry

end OMA.S_oeis_a284902
