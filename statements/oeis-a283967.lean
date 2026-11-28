import Mathlib

/-!
# OEIS A283967: the n-th 0 of the fixed point of 0 -> 1, 1 -> 10101 stays near n * r

Source: https://oeis.org/A283967 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code, submitted by @SSmurf.

Entry (Clark Kimberling, Mar 26 2017), offset 1: Positions of 0 in A283966; complement of A284015.
Comment: Conjecture: -1 < n*r - a(n) < 3 for n >= 1, where r = (7+sqrt(17))/4.
A283966 is the fixed point of the morphism 0 -> 1, 1 -> 10101.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` is the k-th iterate of the morphism applied to the word 1. The image of 1 starts
  with 1, so each iterate extends the one before, and their limit is the fixed point (it starts
  1, 0, 1, 0, 1, 1, 1, 0, as the data of A283966).
* `A283966 i` is the i-th letter (i >= 1) of the fixed point, read off `iter i`, which has more than
  i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A283966(i) = 0, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1. The first terms are
  a(1..8) = 2, 4, 8, 10, 14, 16, 19, 21, the entry's data.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1, with
  r = (7+sqrt(17))/4 as in the entry.
-/

namespace OMA.S_oeis_a283967

/-- The morphism 0 -> 1, 1 -> 10101 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1]
  | _ => [1, 0, 1, 0, 1]

/-- The k-th iterate of the morphism applied to the word 1. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [1]

/-- A283966(i) for i >= 1: the i-th letter of the fixed point, read off `iter i`. -/
def A283966 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A283967(n) for n >= 1: the position of the n-th 0 in A283966. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A283966 i = 0) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -1 < (n : ℝ) * ((7 + Real.sqrt 17) / 4) - a n ∧
      (n : ℝ) * ((7 + Real.sqrt 17) / 4) - a n < 3 := by
  sorry

end OMA.S_oeis_a283967
