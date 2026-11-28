import Mathlib

/-!
# OEIS A284946: the n-th 1 of the fixed point of 0 -> 01, 1 -> 1110: the conjectured bounds on n * r - a(n)

Source: https://oeis.org/A284946 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code, submitted by @SSmurf.

Entry (Clark Kimberling, Apr 18 2017), offset 1: Positions of 1 in A284944; complement of A284945.
Comment: Conjecture:  -1 < n*r - a(n) < 3 for n >= 1, where r = 2 + sqrt(2).
A284944 is the fixed point of the morphism 0 -> 01, 1 -> 1110.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` is the k-th iterate of the morphism applied to the word 0. The image of 0 starts
  with 0, so each iterate extends the one before, and their limit is the fixed point (it starts
  0, 1, 1, 1, 1, 0, 1, 1, as the data of A284944).
* `A284944 i` is the i-th letter (i >= 1) of the fixed point, read off `iter i`, which has more than
  i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A284944(i) = 1, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1. The first terms are
  a(1..8) = 2, 3, 4, 5, 7, 8, 9, 11, the entry's data.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1, with
  r = 2 + sqrt(2) as in the entry.
* As written, the inequality already fails at n = 2: a(2) = 3 and
  2*r - a(2) = 3.8284, above the upper bound 3. `main` is the entry's literal text, so it
  is expected to be refuted, not proved.
-/

namespace OMA.S_oeis_a284946

/-- The morphism 0 -> 01, 1 -> 1110 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [0, 1]
  | _ => [1, 1, 1, 0]

/-- The k-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [0]

/-- A284944(i) for i >= 1: the i-th letter of the fixed point, read off `iter i`. -/
def A284944 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A284946(n) for n >= 1: the position of the n-th 1 in A284944. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A284944 i = 1) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -1 < (n : ℝ) * (2 + Real.sqrt 2) - a n ∧
      (n : ℝ) * (2 + Real.sqrt 2) - a n < 3 := by
  sorry

end OMA.S_oeis_a284946
