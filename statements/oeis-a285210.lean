import Mathlib

/-!
# OEIS A285210: the n-th 1 of the 1-limiting word of 0 -> 10, 1 -> 0100 stays near n * r

Source: https://oeis.org/A285210 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code, submitted by @SSmurf.

Entry (Clark Kimberling, Apr 23 2017), offset 1: Positions of 1 in A285208; complement of A285209.
Comment: Conjecture: 0 < n*r - a(n) < 3, where r = 1 + sqrt(3).
A285208 is the 1-limiting word of the morphism 0 -> 10, 1 -> 0100.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` is the k-th iterate of the morphism applied to the word 0:
  0 -> 10 -> 010010 -> 1001001010010010 -> ...
  The iterates with an even number of steps start with 0 and each extends the previous even one;
  those with an odd number of steps start with 1 and each extends the previous odd one. As in the
  comment of A285208, the 1-limiting word is the limit of the iterates with an odd number of
  steps (it starts 1, 0, 0, 1, 0, 0, 1, 0, as the data of A285208).
* `A285208 i` is the i-th letter (i >= 1) of that word, read off `iter (2 * i + 1)`, which has more
  than i letters; any later iterate of the same parity gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A285208(i) = 1, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1. The first terms are
  a(1..8) = 1, 4, 7, 9, 12, 15, 18, 21, the entry's data.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1, with
  r = 1 + sqrt(3) as in the entry.
* The entry's comment does not give the range of n; `main` takes every n >= 1, the range of the
  sequence (offset 1).
-/

namespace OMA.S_oeis_a285210

/-- The morphism 0 -> 10, 1 -> 0100 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1, 0]
  | _ => [0, 1, 0, 0]

/-- The k-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [0]

/-- A285208(i) for i >= 1: the i-th letter of the 1-limiting word, read off `iter (2 * i + 1)`. -/
def A285208 (i : ℕ) : ℕ := (iter (2 * i + 1)).getD (i - 1) 0

/-- A285210(n) for n >= 1: the position of the n-th 1 in A285208. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A285208 i = 1) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    0 < (n : ℝ) * (1 + Real.sqrt 3) - a n ∧
      (n : ℝ) * (1 + Real.sqrt 3) - a n < 3 := by
  sorry

end OMA.S_oeis_a285210
