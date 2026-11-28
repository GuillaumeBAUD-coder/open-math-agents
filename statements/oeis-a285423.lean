import Mathlib

/-!
# OEIS A285423: the n-th 1 of the 1-limiting word of 0 -> 11, 1 -> 011 stays near n * r

Source: https://oeis.org/A285423 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code, submitted by @SSmurf.

Entry (Clark Kimberling, Apr 28 2017), offset 1: Positions of 1 in A285421; complement of A285422.
Comment: Conjecture: -2 < n*r - a(n) < 2 for n>=1, where r = (1 + sqrt(3))2.
A285421 is the 1-limiting word of the morphism 0 -> 11, 1 -> 011.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` is the k-th iterate of the morphism applied to the word 0:
  0 -> 11 -> 011011 -> 1101101111011011 -> ...
  The iterates with an even number of steps start with 0 and each extends the previous even one;
  those with an odd number of steps start with 1 and each extends the previous odd one. As in the
  comment of A285421, the 1-limiting word is the limit of the iterates with an odd number of
  steps (it starts 1, 1, 0, 1, 1, 0, 1, 1, as the data of A285421).
* `A285421 i` is the i-th letter (i >= 1) of that word, read off `iter (2 * i + 1)`, which has more
  than i letters; any later iterate of the same parity gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A285421(i) = 1, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1. The first terms are
  a(1..8) = 1, 2, 4, 5, 7, 8, 9, 10, the entry's data.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1, with
  r = (1 + sqrt(3))/2 as in the entry.
* The entry prints r as "(1 + sqrt(3))2"; the division sign is missing. It is read as
  (1 + sqrt(3))/2, the value in the twin entry A285420 (the 0-limiting word of the same morphism,
  with the same conjecture). That is the limit of a(n)/n here, the only value of r for which
  n*r - a(n) can stay bounded.
-/

namespace OMA.S_oeis_a285423

/-- The morphism 0 -> 11, 1 -> 011 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1, 1]
  | _ => [0, 1, 1]

/-- The k-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [0]

/-- A285421(i) for i >= 1: the i-th letter of the 1-limiting word, read off `iter (2 * i + 1)`. -/
def A285421 (i : ℕ) : ℕ := (iter (2 * i + 1)).getD (i - 1) 0

/-- A285423(n) for n >= 1: the position of the n-th 1 in A285421. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A285421 i = 1) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -2 < (n : ℝ) * ((1 + Real.sqrt 3) / 2) - a n ∧
      (n : ℝ) * ((1 + Real.sqrt 3) / 2) - a n < 2 := by
  sorry

end OMA.S_oeis_a285423
